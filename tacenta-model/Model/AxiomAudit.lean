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
recorded per-file axiom set instead. This module prints the axioms it finds
in each generated module, one `audit-axiom: <module> <name>` line each, and
`scripts/no-sorry.sh` compares that list against the recorded set, so the
manifest is checked against the environment and not only against the text.
The compiler-trust axioms a generated module carries are not opaque externals
and are printed apart, as `audit-native:` lines.

Two allowances, deliberate and narrow, and each held to the exact shape the
compiler produces rather than to a name:

- The compiler-trust axioms `native_decide` (and its spelling `decide
  +native`) and `bv_decide` introduce. Each is named
  `<decl>._native.<tactic>.ax_<n>` and states that a compiled Boolean
  evaluation returned `true`: `Decidable.decide p = true` for the first two,
  `Std.Tactic.BVDecide.Reflect.verifyBVExpr e c = true` for `bv_decide` (the
  older `Lean.reduceBool _ = true` form is accepted too). The audit accepts
  an axiom only if its name has that shape, the `<decl>` it hangs off is a
  theorem or definition declared in the same module (a definition, because
  the tactic can discharge a proof obligation inside a term: Aeneas's `toStr`
  takes its length bound `by decide +native`, so every generated `Debug`
  `fmt` body carries some), and its statement has the matching shape. An
  `axiom Evil._native.ax : False` has the component and none of the rest,
  and is refused; so is one with the right name and the wrong statement, or
  hung off a declaration in another module. Those axioms are visible to
  `#print axioms`, are pinned where they are load-bearing, and are recorded
  in `LIMITATIONS.md`; a declaration-level audit that refused them would
  refuse the field proofs.
- The `<f>._unsafe_rec` auxiliary the compiler makes for every recursive
  definition (see `compilerAuxiliary`). The name alone is not enough there
  either: the code generator calls `<f>._unsafe_rec` in place of `<f>` if a
  constant of that name exists, so a hand-written `def bar._unsafe_rec` is an
  `implemented_by` in disguise, and `native_decide` will evaluate it instead
  of `bar`. It is neither partial nor unsafe, so a flag-based rule does not
  see it. The audit accepts the name only in the one shape the compiler
  produces, and refuses it in every other.

What this cannot see: a declaration added under `set_option
debug.skipKernelTC true` is an ordinary theorem in the environment, checked by
the elaborator and not by the kernel. The defence against that is
`leanchecker`, which replays a module's declarations through the kernel from
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

/-- The module a constant was declared in: an imported module by index, or the
module being elaborated. -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- The functions whose compiled evaluation a compiler-trust axiom asserts
returned `true`, by the tactic named in the axiom's second-to-last component.
`Decidable.decide` is what `native_decide` and `decide +native` state on this
toolchain (the component is `native_decide` or `decide` accordingly), the
`Reflect` verifiers are what `bv_decide` states, and `Lean.reduceBool` is the
form both took on earlier toolchains. Anything else is not a compiler-trust
axiom whatever it is called. -/
def compilerTrustHeads : String → List Name
  | "native_decide" => [`Decidable.decide, `Lean.reduceBool]
  | "decide" => [`Decidable.decide, `Lean.reduceBool]
  | "bv_decide" =>
    [`Std.Tactic.BVDecide.Reflect.verifyBVExpr, `Std.Tactic.BVDecide.Reflect.verifyCert,
     `Lean.reduceBool]
  | _ => []

/-- `ty` is `@Eq Bool (h ...) Bool.true` for some `h` in `heads`. -/
def isBoolEvalTrue (heads : List Name) (ty : Expr) : Bool :=
  match ty with
  | .app (.app (.app (.const ``Eq _) (.const ``Bool _)) lhs) (.const ``Bool.true _) =>
    match lhs.getAppFn with
    | .const h _ => heads.contains h
    | _ => false
  | _ => false

/-- The compiler-trust axioms `native_decide`, `decide +native` and `bv_decide`
generate, held to their exact shape: named `<decl>._native.<tactic>.ax_<n>`,
hanging off a theorem or definition declared in the same module, and stating
that a compiled Boolean evaluation returned `true`. They are the one axiom
shape a hand-written module may declare, because `#print axioms` reports them
and the pins hold them. -/
def compilerTrust (env : Environment) (m : Name) (n : Name) (c : ConstantInfo) : Bool :=
  match n, c with
  | .str (.str (.str decl "_native") tactic) ax, .axiomInfo _ =>
    ax.startsWith "ax_" &&
    (match env.find? decl with
      | some (.thmInfo _) | some (.defnInfo _) => moduleOf env decl == m
      | _ => false) &&
    isBoolEvalTrue (compilerTrustHeads tactic) c.type
  | _, _ => false

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

/-- Lean compiles every recursive definition, structural or well-founded,
through an auxiliary `<f>._unsafe_rec` it marks `partial`; the kernel-checked
`<f>` is what the proofs reason about, and the auxiliary is the compiler's
own. A user-written `partial def g` is different: it elaborates to an
*opaque* `g` with an `implemented_by g._unsafe_rec`, and the opaque is what
this audit refuses.

The exemption is by shape, not by name, because the name is load-bearing for
the code generator: it compiles a call to `<f>` as a call to `<f>._unsafe_rec`
whenever that constant exists, so a hand-written `def bar._unsafe_rec` with a
different body is what `native_decide` evaluates in place of `bar`. What the
compiler produces, and nothing a user can write, is a *definition* whose safety
is `partial` (a user's `partial def` becomes an opaque; a user's `def` is safe;
a user's `unsafe def` is unsafe), not unsafe, with the same type as a plain,
safe definition `<f>` declared in the same module. -/
def compilerAuxiliary (env : Environment) (m : Name) (n : Name) (c : ConstantInfo) : Bool :=
  match n, c with
  | .str f "_unsafe_rec", .defnInfo d =>
    d.safety == .partial &&
    (match env.find? f with
      | some (.defnInfo p) =>
        p.safety == .safe && moduleOf env f == m && p.type == c.type &&
        p.levelParams == d.levelParams
      | _ => false)
  | _, _ => false

/-- A constant named into the compiler's own namespace: `_unsafe_rec` or
`_native` as a component. Such a name is never something a user has reason to
write, and the two exemptions above accept it only in the compiler's shape. -/
def compilerNamed (n : Name) : Bool :=
  n.components.any fun c => c.toString == "_unsafe_rec" || c.toString == "_native"

/-- The reasons a constant is refused, if any. Several can apply at once, and
all are reported. -/
def reasons (env : Environment) (m : Name) (n : Name) (c : ConstantInfo) :
    List String := Id.run do
  let mut out : List String := []
  let trusted := compilerTrust env m n c
  let auxiliary := compilerAuxiliary env m n c
  match c with
  | .axiomInfo _ =>
    if !trusted && !isGenerated m then out := out ++ ["axiom"]
  | .opaqueInfo _ => out := out ++ ["opaque"]
  | _ => pure ()
  if c.isUnsafe && !auxiliary then out := out ++ ["unsafe"]
  if c.isPartial && !auxiliary then out := out ++ ["partial"]
  if (Compiler.implementedByAttr.getParam? env n).isSome then
    out := out ++ ["implemented_by"]
  if isExtern env n then out := out ++ ["extern"]
  -- A name in the compiler's namespace that is not one of the two shapes the
  -- compiler produces: a planted `_unsafe_rec` the code generator would call,
  -- or an axiom dressed as compiler trust.
  if compilerNamed n && !trusted && !auxiliary then
    out := out ++ ["compiler-namespace"]
  return out

/-- What the walk found. -/
structure Result where
  offences : Array Offence
  /-- First-party constants seen. -/
  seen : Nat
  /-- The opaque externals each generated module declares: its axioms that are
  not compiler trust. Printed by `run` as `audit-axiom:` lines;
  `scripts/no-sorry.sh` compares them with the set `attest.py` recorded. -/
  generated : Array (Name × Name)
  /-- The compiler-trust axioms in generated modules (Aeneas's `toStr` bound,
  `by decide +native`). Printed as `audit-native:` lines for the count. -/
  generatedNative : Array (Name × Name)

/-- Walk the environment. -/
def audit (env : Environment) (prefixes : Array Name) : Result := Id.run do
  let mut offences : Array Offence := #[]
  let mut seen := 0
  let mut generated : Array (Name × Name) := #[]
  let mut generatedNative : Array (Name × Name) := #[]
  for (n, c) in env.constants.toList do
    let m := moduleOf env n
    if !isFirstParty prefixes m then continue
    seen := seen + 1
    if isGenerated m then
      if let .axiomInfo _ := c then
        if compilerTrust env m n c then generatedNative := generatedNative.push (m, n)
        else generated := generated.push (m, n)
    for k in reasons env m n c do
      offences := offences.push { decl := n, module := m, kind := k }
  let byName (a b : Name × Name) : Bool := a.2.toString < b.2.toString
  return { offences := offences.qsort (fun a b => a.decl.toString < b.decl.toString),
           seen, generated := generated.qsort byName,
           generatedNative := generatedNative.qsort byName }

/-- Run the audit over everything imported into the current module and refuse
the build on any offence. `prefixes` names the first-party module roots to
hold to the rule. -/
def run (prefixes : Array Name) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  let { offences, seen, generated, generatedNative } := audit env prefixes
  if seen == 0 then
    throwError "axiom audit: no first-party declaration found under {prefixes}; \
      the audit module imports nothing it should"
  if !offences.isEmpty then
    let lines := offences.map fun o => s!"  {o.decl} ({o.module}): {o.kind}"
    throwError "axiom audit: {offences.size} first-party declaration(s) widen the \
      trust base without a compiler warning:\n{String.intercalate "\n" lines.toList}\n\
      An axiom, an opaque or partial definition, an unsafe declaration, an \
      implemented_by/extern attribute, or a declaration named into the compiler's \
      `_native`/`_unsafe_rec` namespace outside the shape the compiler produces, in \
      hand-written Lean is refused. If one is genuinely needed, record it in \
      LIMITATIONS.md and extend `Model.AxiomAudit` with the reason."
  -- One line per generated axiom, fully qualified, as plain text so the build
  -- log carries it verbatim for `scripts/no-sorry.sh` to compare against
  -- `manifests/translation-attestation.json`; the compiler-trust ones apart.
  let perModule (tag : String) (found : Array (Name × Name)) : Elab.Command.CommandElabM Unit := do
    for m in (found.map (·.1)).toList.eraseDups do
      let lines := found.filter (·.1 == m) |>.map fun (_, n) => s!"{tag}: {m} {n}"
      logInfo (String.intercalate "\n" lines.toList)
  perModule "audit-axiom" generated
  perModule "audit-native" generatedNative
  let generatedNote :=
    if generated.isEmpty && generatedNative.isEmpty then ""
    else s!"; {generated.size} opaque externals declared by the generated translation, \
      listed above and held to manifests/translation-attestation.json by attest.py, and \
      {generatedNative.size} compiler-trust axioms in it (Aeneas's `toStr` bound, \
      `by decide +native`)"
  logInfo m!"axiom audit: {seen} first-party declarations under {prefixes}; none is an \
    axiom, opaque, unsafe or partial, or carries implemented_by/extern, outside the \
    native_decide/bv_decide allowance{generatedNote}"

end Model.AxiomAudit
