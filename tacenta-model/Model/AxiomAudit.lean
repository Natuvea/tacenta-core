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

Two allowances, deliberate and narrow, and each held to the shape the
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
  `fmt` body carries some), its statement has the matching shape, and the
  `<decl>`'s own value applies it -- directly, as a theorem proved `by
  native_decide` does, or through one of the `<decl>._proof_n` auxiliaries
  the elaborator splits out of a definition, as the generated `fmt` bodies
  do. An `axiom Evil._native.ax : False` has the component and none of the
  rest, and is refused; so is one with the right name and the wrong
  statement, one hung off a declaration in another module, or one that
  nothing under its parent's name applies *while something first-party
  applies it somewhere* (see `compilerNamesApplied` for that qualification,
  which is what an orphan axiom turns on). Those axioms are visible to
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
  produces -- a partial-safety definition that calls itself, beside a safe,
  recursive `<f>` of the same type in the same module -- and refuses it in
  every other.

What the shape cannot settle: the shape is what the compiler produces, and
elaboration-time code produces it just as well. A `run_cmd` (or `#eval`, an
`elab`, a `macro`, an `initialize`) that calls `addDecl` can add an axiom
named `<t>._native.native_decide.ax_1_1` of type `decide False = true` and a
theorem whose proof term applies it, with the name assembled from string
literals so that no `axiom` token and no `_native` token appears in the
source; `addAndCompile` can add a partial `<f>._unsafe_rec` with a different
body beside a recursive `<f>`, after which `native_decide` proves things of
`<f>` that are false of it. Both satisfy every check in this module, and
`leanchecker` accepts both, since an axiom is a kernel-valid declaration.
**This audit cannot distinguish a planted compiler-trust axiom or auxiliary
from a real one on shape alone.** What excludes them is textual:
`scripts/check-lean-constructs.sh` refuses every elaboration-time construct
in hand-written first-party Lean -- `run_cmd`, `#eval`, `elab`, `macro`,
`syntax`, `initialize`, `addDecl` and its kin, and any reference to the
`Lean` namespace at all -- outside this module's own implementation and the
five `run_cmd Model.AxiomAudit.run` lines, which it allow-lists by file path
and exact line content; and `scripts/check-audit-reach.sh` fails if any
first-party module is outside the five audit modules' import closure, so no
module escapes the walk. The division of labour: this module recognises the
declaration kinds a grep cannot, and the grep refuses the code that could
forge what this module accepts.

What this cannot see either: a declaration added under `set_option
debug.skipKernelTC true` is an ordinary theorem in the environment, checked by
the elaborator and not by the kernel. The defence against that is
`leanchecker`, which replays a module's declarations through the kernel from
its olean; `REPRODUCING.md` says how to run it. The grep script refuses that
option by name, and every other `debug.*` option with it.

This module lives in the model package because both the proofs package and
the translation package depend on it, so one definition serves all three.
Each package carries a small module that imports what it builds and calls
`Model.AxiomAudit.run`; a module outside its package's build glob would be an
audit nothing runs, which `scripts/check-translation-coverage.sh` guards
against for the translation package, and a module outside every audit's
imports would be a module nothing walks, which `check-audit-reach.sh` guards
against for all three.
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

/-- Does the value of `root`, or of an auxiliary the elaborator split out of
it, mention `target`? A theorem proved `by native_decide` applies its axiom
in its own proof term; a definition that discharged an obligation `by decide
+native` applies it in a `<root>._proof_n` theorem the elaborator abstracted
out, and `<root>`'s value applies that. The walk starts at `root` and follows
only constants declared under `root`'s name in module `m` (`_proof_n`,
`match_n`, and the like), so it is bounded by the declaration's own
auxiliaries; the fuel is a guard, not a limit anything reaches. -/
def mentionsVia (env : Environment) (m root target : Name) : Bool :=
  go [root] {} 256
where
  go : List Name → NameSet → Nat → Bool
    | [], _, _ => false
    | _, _, 0 => false
    | c :: rest, seen, fuel + 1 =>
      if seen.contains c then go rest seen fuel
      else
        -- `allowOpaque`: on this toolchain `value?` withholds a theorem's
        -- proof term without it, and a theorem is the usual parent.
        match (env.find? c).bind (·.value? (allowOpaque := true)) with
        | none => go rest (seen.insert c) fuel
        | some v =>
          let used := v.getUsedConstants
          if used.contains target then true
          else
            let next := used.toList.filter fun u =>
              root.isPrefixOf u && u != root && moduleOf env u == m && !seen.contains u
            go (next ++ rest) (seen.insert c) fuel

/-- The compiler-trust axioms `native_decide`, `decide +native` and `bv_decide`
generate, held to their shape: named `<decl>._native.<tactic>.ax_<n>`,
hanging off a theorem or definition declared in the same module, stating
that a compiled Boolean evaluation returned `true`, and applied by that
declaration's own value (see `mentionsVia`) unless no first-party declaration
mentions it at all, in a value or in a statement (see `compilerNamesApplied`).
`check-audit-negatives.sh` plants each of these conditions, and each other
kind the audit refuses, and checks that the rule refuses what it says it
refuses. They are the one axiom shape a
hand-written module may declare, because `#print axioms` reports them and
the pins hold them. The shape is what the tactic produces, and what
elaboration-time code could produce too; see the module docstring for what
excludes that. -/
def compilerTrust (env : Environment) (applied : NameSet)
    (m : Name) (n : Name) (c : ConstantInfo) : Bool :=
  match n, c with
  | .str (.str (.str decl "_native") tactic) ax, .axiomInfo _ =>
    ax.startsWith "ax_" &&
    (match env.find? decl with
      | some (.thmInfo _) | some (.defnInfo _) => moduleOf env decl == m
      | _ => false) &&
    isBoolEvalTrue (compilerTrustHeads tactic) c.type &&
    (mentionsVia env m decl n || !applied.contains n)
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

/-- The recursion a `<f>._unsafe_rec`'s parent must show in its value.
Structural recursion elaborates through the inductive type's `brecOn` (or
`binductionOn`, for a `Prop`-valued one); well-founded recursion through
`WellFounded.fix`, packed behind a `<f>._unary` companion when `<f>` takes
more than one argument. A non-recursive `<f>` has none of these, and the
compiler makes no auxiliary for it. -/
def recursiveValue (f : Name) (v : Expr) : Bool :=
  v.getUsedConstants.any fun u =>
    u == ``WellFounded.fix || u == ``WellFounded.fixF || u == f ++ `_unary ||
    (match u with
      | .str _ "brecOn" | .str _ "binductionOn" => true
      | _ => false)

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
compiler produces is a *definition* whose safety is `partial` (a user's
`partial def` becomes an opaque; a user's `def` is safe; a user's `unsafe
def` is unsafe), not unsafe, whose body calls itself (it is `<f>`'s body with
the recursive calls redirected), with the same type and universe parameters
as a plain, safe definition `<f>` declared in the same module whose own value
is recursive (`recursiveValue`). A `def barC := 0` with a planted
`barC._unsafe_rec := 1` beside it fails the last two: `barC` recurses on
nothing, and the auxiliary calls nothing. The shape is still one that
`addAndCompile` at elaboration time can produce beside a genuinely recursive
`<f>`; the module docstring says what excludes that. -/
def compilerAuxiliary (env : Environment) (m : Name) (n : Name) (c : ConstantInfo) : Bool :=
  match n, c with
  | .str f "_unsafe_rec", .defnInfo d =>
    d.safety == .partial &&
    d.value.getUsedConstants.contains n &&
    (match env.find? f with
      | some (.defnInfo p) =>
        p.safety == .safe && moduleOf env f == m && p.type == c.type &&
        p.levelParams == d.levelParams && recursiveValue f p.value
      | _ => false)
  | _, _ => false

/-- A constant named into the compiler's own namespace: `_unsafe_rec` or
`_native` as a component. Such a name is never something a user has reason to
write, and the two exemptions above accept it only in the compiler's shape. -/
def compilerNamed (n : Name) : Bool :=
  n.components.any fun c => c.toString == "_unsafe_rec" || c.toString == "_native"

/-- Every constant named into the compiler's namespace (`compilerNamed`) that
some first-party declaration mentions, in its value or in its statement.

Why the audit needs it: `decide +native` names the axiom it adds after the
declaration being elaborated, but the proof term it builds may not use that
axiom. Lean caches these by statement, so when two declarations in one module
discharge the *same* obligation, the second reuses the first's axiom and the
axiom named after the second is left declared and mentioned by nothing. That
is not hypothetical here: the three-leaf translation unit
(`Translation.TacentaTripleUnit`) puts all three leaves' types in one module,
and seven string literals occur in more than one leaf's `Debug` body --
`ChainExhausted`, `SkippedStoreFull`, `TooManySkipped`, `Malformed`,
`TooShort`, `UnknownVersion` and `Header`. Aeneas's `toStr` takes a length
bound `by decide +native` for each occurrence, and every occurrence after the
first reuses the cached proof, so ten such orphans exist there. None exists in
any module that holds one crate, where each literal occurs once.

An orphan is inert: no declaration reaches it, so it is in no theorem's
`#print axioms` and can widen no trust base. The rule below therefore waives
the "its parent applies it" requirement exactly for an axiom nothing
first-party mentions, and keeps it for every axiom that is actually used.
Waiving it for an unused axiom costs nothing: to become load-bearing it must
be mentioned, and then this set contains it and the requirement is back.

Statements are walked as well as values, and the difference is not cosmetic.
`#print axioms` traverses both, so a declaration whose *type* names an axiom
depends on it even if its proof term does not. Reading values alone would call
such an axiom unmentioned and waive it while a theorem genuinely rests on it,
which is exactly the inertness this waiver claims. Walking both closes that
gap; it waives none of the orphans this rule exists for, because no first-party
statement here names a compiler-trust axiom.

First-party is the right scope and not a shortcut: a third-party module cannot
mention a first-party axiom, since the dependency runs the other way, so a use
that could ever reach one of our theorems is a use by a first-party
declaration and is seen here.

The set is built from the environment the audit runs in, so it sees a use only
if the using module is in that environment. Every audit is therefore given the
same `prefixes`, covering all four first-party namespaces, so that a declaring
module and a using module are never split across audits in a way that lets each
call the axiom someone else's problem. `check-audit-reach.sh` holds the other
half of that: every first-party module is in some audit's environment.

The same waiver is deliberately *not* extended to `<f>._unsafe_rec` (see
`compilerAuxiliary`). An unused axiom is inert; an unused `_unsafe_rec` is
not, because the code generator calls it by name whether or not anything
mentions it. -/
def compilerNamesApplied (env : Environment) (prefixes : Array Name) : NameSet :=
  Id.run do
    let mut out : NameSet := {}
    for (n, c) in env.constants.toList do
      if !isFirstParty prefixes (moduleOf env n) then continue
      for u in c.type.getUsedConstants do
        if compilerNamed u then out := out.insert u
      if let some v := c.value? (allowOpaque := true) then
        for u in v.getUsedConstants do
          if compilerNamed u then out := out.insert u
    return out

/-- The reasons a constant is refused, if any. Several can apply at once, and
all are reported. -/
def reasons (env : Environment) (applied : NameSet)
    (m : Name) (n : Name) (c : ConstantInfo) : List String := Id.run do
  let mut out : List String := []
  let trusted := compilerTrust env applied m n c
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
  -- One pass for the whole walk: which compiler-named constants anything
  -- first-party applies. See `compilerNamesApplied`.
  let applied := compilerNamesApplied env prefixes
  for (n, c) in env.constants.toList do
    let m := moduleOf env n
    if !isFirstParty prefixes m then continue
    seen := seen + 1
    if isGenerated m then
      if let .axiomInfo _ := c then
        if compilerTrust env applied m n c then
          generatedNative := generatedNative.push (m, n)
        else generated := generated.push (m, n)
    for k in reasons env applied m n c do
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
