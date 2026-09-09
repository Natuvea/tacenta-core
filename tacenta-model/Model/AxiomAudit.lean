import Lean

/-!
# AxiomAudit: the declaration kinds `#print axioms` cannot see

`#print axioms` under `#guard_msgs` pins what a *pinned* theorem rests on,
and `no-sorry.sh` asks the compiler for incomplete declarations. Neither sees a
declaration that is itself the new thing: an `axiom` nobody pins a theorem
against, an `opaque` or `partial def` that opts out of termination checking,
an `unsafe` declaration that opts out of everything, or an `@[implemented_by]`
or `@[extern]` attribute, under which the program `native_decide` runs is a
different definition from the one the kernel reasons about (the textbook route
to a proof of `False`).

`scripts/check-lean-constructs.sh` greps the source for these. A grep sees
text, and the review of that script found the text it did not see: `private
axiom`, an axiom behind an attribute, `opaque`, and `set_option
debug.skipKernelTC`. This module asks the elaborated environment instead. It
walks every constant, keeps those whose module is first-party and hand-written,
and refuses the build if any is an axiom, opaque, unsafe or partial, or carries
an `implemented_by` or `extern` attribute. The generated translation
(`Translation.Tacenta*`) is exempt from the axiom rule only: Aeneas emits every
opaque external as an `axiom`, and `scripts/attest.py` holds those files to a
recorded per-file axiom set instead.

One allowance, deliberate and narrow: the compiler-trust axioms `native_decide`
and `bv_decide` introduce (`<decl>._native.native_decide.ax_*`,
`<decl>._native.bv_decide.ax_*`). Those are visible to `#print axioms`, are
pinned where they are load-bearing, and are recorded in `LIMITATIONS.md`; a
declaration-level audit that refused them would refuse the field proofs.

What this cannot see: a declaration added under `set_option
debug.skipKernelTC true` is an ordinary theorem in the environment, checked by
the elaborator and not by the kernel. The defence against that is
`lean4checker`, which replays a module's declarations through the kernel from
its olean; `REPRODUCING.md` says how to run it. The grep script is kept as a
textual second line and now refuses that option by name.

This module lives in the model package because both the proofs package and
the translation package depend on it, so one definition serves all three.
Each package carries a small module that imports what it builds and calls
`Model.AxiomAudit.run`; a module outside its package's build glob would be an
audit nothing runs, which `scripts/check-translation-coverage.sh` guards
against for the translation package.
-/

namespace Model.AxiomAudit

open Lean

/-- One refused declaration: what it is, where it was declared, and why it is
refused. -/
structure Offence where
  decl : Name
  module : Name
  kind : String
  deriving Repr

/-- The compiler-trust axioms `native_decide` and `bv_decide` generate carry a
`_native` component. They are the one axiom shape a hand-written module may
declare, because `#print axioms` reports them and the pins hold them. -/
def compilerTrust (n : Name) : Bool :=
  n.components.any (· == `_native)

/-- The generated translation: `Translation.Tacenta<Crate>`. Its axioms are the
opaque externals the translator declares, held to a recorded set by
`attest.py` rather than refused here. Everything else about it is still
audited (an `unsafe` or an `implemented_by` in a generated file would be
refused). -/
def isGenerated (m : Name) : Bool :=
  match m with
  | .str `Translation s => s.startsWith "Tacenta"
  | _ => false

/-- A module is ours if one of the given prefixes is a prefix of its name. -/
def isFirstParty (prefixes : Array Name) (m : Name) : Bool :=
  prefixes.any fun p => p.isPrefixOf m

/-- The module a constant was declared in: an imported module by index, or the
module being elaborated. -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- Lean compiles every recursive definition, structural or well-founded,
through an auxiliary `<f>._unsafe_rec` it marks `partial`; the kernel-checked
`<f>` is what the proofs reason about, and the auxiliary is the compiler's
own. A user-written `partial def g` is different: it elaborates to an
*opaque* `g` with an `implemented_by g._unsafe_rec`, and the opaque is what
this audit refuses. So the auxiliary's `partial`/`unsafe` flags are exempt
and nothing a user can write is. -/
def compilerAuxiliary (n : Name) : Bool :=
  match n with
  | .str _ "_unsafe_rec" => true
  | _ => false

/-- The reasons a constant is refused, if any. Several can apply at once, and
all are reported. -/
def reasons (env : Environment) (m : Name) (n : Name) (c : ConstantInfo) :
    List String := Id.run do
  let mut out : List String := []
  match c with
  | .axiomInfo _ =>
    if !compilerTrust n && !isGenerated m then out := out ++ ["axiom"]
  | .opaqueInfo _ => out := out ++ ["opaque"]
  | _ => pure ()
  if c.isUnsafe && !compilerAuxiliary n then out := out ++ ["unsafe"]
  if c.isPartial && !compilerAuxiliary n then out := out ++ ["partial"]
  if (Compiler.implementedByAttr.getParam? env n).isSome then
    out := out ++ ["implemented_by"]
  if isExtern env n then out := out ++ ["extern"]
  return out

/-- Walk the environment. Returns the offences, the number of first-party
constants seen, and the axioms each generated module declares (reported for the
log; `attest.py` is what holds them to a recorded set). -/
def audit (env : Environment) (prefixes : Array Name) :
    Array Offence × Nat × Array (Name × Name) := Id.run do
  let mut offences : Array Offence := #[]
  let mut seen := 0
  let mut generated : Array (Name × Name) := #[]
  for (n, c) in env.constants.toList do
    let m := moduleOf env n
    if !isFirstParty prefixes m then continue
    seen := seen + 1
    if isGenerated m then
      if let .axiomInfo _ := c then generated := generated.push (m, n)
    for k in reasons env m n c do
      offences := offences.push { decl := n, module := m, kind := k }
  return (offences.qsort (fun a b => a.decl.toString < b.decl.toString), seen,
    generated.qsort (fun a b => a.2.toString < b.2.toString))

/-- Run the audit over everything imported into the current module and refuse
the build on any offence. `prefixes` names the first-party module roots to
hold to the rule. -/
def run (prefixes : Array Name) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  let (offences, seen, generated) := audit env prefixes
  if seen == 0 then
    throwError "axiom audit: no first-party declaration found under {prefixes}; \
      the audit module imports nothing it should"
  if !offences.isEmpty then
    let lines := offences.map fun o => s!"  {o.decl} ({o.module}): {o.kind}"
    throwError "axiom audit: {offences.size} first-party declaration(s) widen the \
      trust base without a compiler warning:\n{String.intercalate "\n" lines.toList}\n\
      An axiom, an opaque or partial definition, an unsafe declaration, or an \
      implemented_by/extern attribute in hand-written Lean is refused. If one is \
      genuinely needed, record it in LIMITATIONS.md and extend `Model.AxiomAudit` \
      with the reason."
  let generatedNote :=
    if generated.isEmpty then ""
    else s!"; {generated.size} opaque externals declared by the generated translation, \
      held to manifests/translation-attestation.json by attest.py"
  logInfo m!"axiom audit: {seen} first-party declarations under {prefixes}; none is an \
    axiom, opaque, unsafe or partial, or carries implemented_by/extern, outside the \
    native_decide/bv_decide allowance{generatedNote}"

end Model.AxiomAudit
