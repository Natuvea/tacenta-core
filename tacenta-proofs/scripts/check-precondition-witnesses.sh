#!/usr/bin/env bash
# Hold the numeric-precondition witnesses to the signatures of the theorems they witness, and hold
# this check to mutations.
#
# Three modules state, for the central receive and send theorems of the ratchets, the sparse
# ratchet, the Triple Ratchet and the Braid, that the numeric premises of each theorem are met
# together at one concrete state:
#
#   NumericWitnessLeaf.lean     the standalone leaf translations
#   NumericWitnessTriple.lean   the three-leaf unit
#   NumericWitnessSession.lean  the eight-leaf session unit
#
# and two modules state which premises of the sparse ratchet, classical ratchet, Braid and Triple
# refinements a decoded state already gives (`DecodedStateDischarge.lean`,
# `SessionUnitDecodedStateDischarge.lean`). A witness is only evidence about a theorem if its
# statement is that theorem's own premises, and nothing in Lean ties a hand-written statement to a
# signature. Before this script nothing in the tree did, so a premise could be added to a theorem and
# every witness near it would still build. This script is the tie.
#
# For each witnessed theorem T the table below lists T's hypotheses in three groups: `covers`
# (inside the witness statement), `boundary` (statements about opaque operations or translated
# functions, outside it) and `unwitnessed` (premises that need a value of an opaque type, outside it
# and open). Lean code in this script, run over a copy of the module, reads T's type from the built
# environment and requires that
#
#   - the table classifies every hypothesis of T, and names no other (so a premise added to T later
#     is refused until someone classifies it);
#   - every hypothesis that is numeric (a comparison on a natural number or an integer in its
#     propositional skeleton) or a numeric predicate about a state is in `covers`;
#   - `Premises.T` is definitionally the existential closure, over the data the covered hypotheses
#     mention, of their conjunction in T's order, built from T's own hypothesis types;
#   - `sat_T` is a theorem whose type is exactly `Premises.T`;
#   - every statement the witness module defines under `Premises` is in the table.
#
# For a discharge theorem the table lists, for T, the hypotheses the theorem concludes (`discharges`),
# the hypotheses it takes as premises (`given`), the ones that stay with the caller (`caller`) and the
# boundary ones, and requires that the table classifies every hypothesis of T, that the theorem's
# conclusion is exactly the conjunction of the discharged hypotheses written in T's own variables
# (which the theorem binds under the same names), that the theorem takes each given hypothesis at
# T's type, and that it takes no hypothesis the table says it does not.
#
# The check is Lean code that reads the environment, so it cannot be a module:
# `check-lean-constructs.sh` refuses elaboration-time code in the translation package, for the
# reasons its header gives. The text below is appended to a copy of each module and elaborated with
# `lake env lean`, which writes nothing to an olean, as `check-session-satisfiability-negatives.sh` does
# for its audit.
#
# What it does not check: that a witness's state is reachable, that a `boundary` hypothesis is
# satisfiable (that is `Satisfiability.lean` and the records' own work), or that the classification
# into `boundary` and `unwitnessed` is the right one; a reader checks that, and the groups are in
# the module docstrings and in CLAIMS.md.
#
# A numeric premise stated through a definition whose name is not on `pwStatePreds` is not recognised as
# numeric. If the table classifies it as `boundary` the check accepts it; a toy theorem with `(h2 : Roomy n)`
# where `Roomy n := n + 1 < Usize.max` passes. Unfolding Prop-valued definition heads before looking for
# comparisons would close this. A scan of the 44 witness rows and 18 discharge rows with unfolding found no
# such premise in the tree: the only hypotheses it flagged were the contract bundles `RatchetAgreesFor` and
# `SpqrAgreesFor`, whose numeric content is in implication antecedents.
#
# The numeric-hypothesis rule applies to witness rows only. In a discharge row a numeric hypothesis may be
# classified `caller` and nothing asks for a witness, so a numeric premise added to a theorem that has a
# discharge row and no witness row (`advance_refines`, `maybe_advance_refines`, `clear_old_epochs_refines`)
# is accepted once it is classified.
#
# Two more checks keep the rest of a witness module tied to its table. Every `*_at_witness` theorem (a
# discharge theorem applied at the witness state, its type read off the application by `type_of%`) must be
# listed and must not have a function type: a premise added after the last argument of a discharge theorem
# leaves the application building at a function type, which the build does not notice and this check
# refuses. And every theorem named `sat_*` in the island must belong to a row of the table.
#
# Each case below applies ONE change and requires `lake env lean` to refuse for the stated reason,
# at the line of its own command, so several cases share one elaboration without hiding each other.
# The unmodified modules must pass first: a refusal is only evidence if acceptance is possible. The
# modules are compared with their `#guard_msgs` axiom pins removed, so a refusal comes from this
# check and not from a pin. A case that fails because the build is missing (no olean, unknown module)
# is not a refusal and is reported as a failure of this script.
set -euo pipefail

cd "$(dirname "$0")/.."
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT INT TERM

TMP="$tmp" python3 - <<'PY'
import os, re, subprocess, sys, time

tmp = os.environ["TMP"]
translation = "translation"
base = os.path.join(translation, "Translation")

META = r"""section PreconditionWitnessCheck
open Lean Meta Elab Command

/-- Comparison relations whose presence in a hypothesis's propositional skeleton makes it numeric. -/
private def pwNumCmp : List Name := [``LE.le, ``LT.lt, ``GE.ge, ``GT.gt, ``Eq, ``Ne]

/-- Heads of the Prop-valued predicates about states that carry numeric bounds. -/
private def pwStatePreds : List String :=
  ["State.ct1_bounded", "State.decoders_bounded", "EncodersLive", "ReceiveHeadroom",
   "DecryptRatchetHeadroom", "EncryptHeadroom", "EstablishInitiatorHeadroom",
   "EstablishResponderHeadroom", "InvariantPreconditions", "Ratchet.Inv", "Spqr.Inv",
   "Braid.Inv", "Fits", "ChainCounterBounded"]

/-- Does the propositional skeleton of `e` contain a comparison on `Nat` or `Int`? -/
private partial def pwHasNumLeaf (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e
  let n := e.getAppFn.constName?.getD Name.anonymous
  let args := e.getAppArgs
  if (n == ``And || n == ``Or || n == ``Iff) && args.size == 2 then
    return (← pwHasNumLeaf args[0]!) || (← pwHasNumLeaf args[1]!)
  else if n == ``Not && args.size == 1 then pwHasNumLeaf args[0]!
  else if n == ``Exists && args.size == 2 then
    lambdaTelescope args[1]! fun _ b => pwHasNumLeaf b
  else if e.isForall then
    forallTelescope e fun xs b => do
      for x in xs do
        let t ← inferType x
        if (← isProp t) && (← pwHasNumLeaf t) then return true
      pwHasNumLeaf b
  else if pwNumCmp.contains n && args.size == 4 then
    let t ← whnfR args[0]!
    return t.isConstOf ``Nat || t.isConstOf ``Int
  else if let some m ← matchMatcherApp? e then
    for alt in m.alts do
      if ← lambdaTelescope alt fun _ b => pwHasNumLeaf b then return true
    return false
  else return false

private def pwIsStatePred (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some c => pwStatePreds.any fun s => (toString c).endsWith s
  | none => false

/-- The free variables of `init`, closed under the types of the variables. -/
private partial def pwCloseFVars (init : Array FVarId) : MetaM (Std.HashSet FVarId) := do
  let mut seen : Std.HashSet FVarId := {}
  let mut todo := init.toList
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | x :: rest =>
      todo := rest
      if seen.contains x then continue
      seen := seen.insert x
      let t ← x.getType
      for y in (collectFVars {} t).fvarIds do
        todo := y :: todo
  return seen

private def pwRight (ts : Array Expr) : MetaM Expr := do
  let some l := ts.back? | throwError "pwRight: empty"
  let mut body := l
  for t in ts[:ts.size-1].toArray.reverse do body ← mkAppM ``And #[t, body]
  return body

/-- The Prop binders of `thm` by user name, in order; fails on an unnamed one. -/
private def pwPropBinders {α : Type} (thm : Name)
    (k : Array Expr → Array (Name × Expr) → MetaM α) : MetaM α := do
  let ci ← getConstInfo thm
  let lvls ← mkFreshLevelMVarsFor ci
  forallTelescope (ci.instantiateTypeLevelParams lvls) fun xs _ => do
    let mut props : Array (Name × Expr) := #[]
    for x in xs do
      let t ← inferType x
      if ← isProp t then
        let n ← x.fvarId!.getUserName
        if n.hasMacroScopes then
          throwError "{thm}: a hypothesis has no name (it shows as {n}); the table cannot classify it"
        props := props.push (n, x)
    k xs props

private def pwSame (a b : Array Name) : Bool :=
  a.size == b.size && a.all b.contains && b.all a.contains

private def pwFmt (a : Array Name) : String := ", ".intercalate (a.toList.map toString)

/-- The statement generated from `thm`'s own signature: `∃ data, h₁ ∧ … ∧ hₖ` over the hypotheses
named in `inn`, in the theorem's order, and with the data they mention. The table must classify
every hypothesis of `thm`, and every numeric one must be inside. -/
private def pwExpected (thm : Name) (inn rest : Array Name) : MetaM Expr :=
  pwPropBinders thm fun xs props => do
    let names := props.map (·.1)
    let all := inn ++ rest
    unless all.size == all.toList.eraseDups.length do
      throwError "{thm}: a hypothesis is named twice in the table"
    unless pwSame names all do
      let missing := names.filter fun n => !all.contains n
      let unknown := all.filter fun n => !names.contains n
      throwError "{thm}: the table does not match the theorem's hypotheses; not classified: [{pwFmt missing}]; not in the theorem: [{pwFmt unknown}]"
    let mut chosen : Array (FVarId × Expr) := #[]
    for (n, x) in props do
      let t ← inferType x
      let isNum := (← pwHasNumLeaf t) || pwIsStatePred t
      if isNum && !inn.contains n then
        throwError "{thm}: the hypothesis {n} is numeric (or a numeric state predicate) and is listed as outside the witness"
      if inn.contains n then chosen := chosen.push (x.fvarId!, t)
    let some _ := chosen[0]? | throwError "{thm}: no hypothesis is inside the witness"
    let body ← pwRight (chosen.map (·.2))
    let chosenIds := chosen.map (·.1)
    let closed ← pwCloseFVars (collectFVars {} body).fvarIds
    let data := xs.filter fun x => closed.contains x.fvarId! && !chosenIds.contains x.fvarId!
    let mut e := body
    for x in data.reverse do
      let lam ← mkLambdaFVars #[x] e
      e ← mkAppM ``Exists #[lam]
    return e

/-- The statement's constant and the witness's name, from the island namespace and the theorem. -/
private def pwNames (island thm : Name) : Name × Name :=
  let suffix := thm.replacePrefix `Tacenta Name.anonymous
  (island ++ `Premises ++ suffix, island ++ Name.mkSimple ("sat_" ++ (toString suffix).replace "." "_"))

private def pwCheckWitness (island thm : Name) (inn bnd unw : Array Name) : MetaM Unit := do
  let (conj, sat) := pwNames island thm
  let expected ← pwExpected thm inn (bnd ++ unw)
  let cci ← getConstInfo conj
  let some v := cci.value? | throwError "{conj} has no value"
  unless (← isDefEq expected v) do
    throwError "{conj} is not the conjunction of the hypotheses of {thm} that the table places inside it:\n  generated: {← ppExpr expected}\n  in the tree: {← ppExpr v}"
  let sci ← getConstInfo sat
  unless sci.isThm do throwError "{sat} is not a theorem"
  unless sci.type == mkConst conj do throwError "{sat} does not state {conj}: it states {← ppExpr sci.type}"
  logInfo m!"witness ok: {thm} (inside {inn.size}, boundary {bnd.size}, unwitnessed {unw.size})"

/-- The conjuncts of a right-nested conjunction with exactly `n` parts (the last part may itself be
anything). -/
private def pwSplit (e : Expr) (n : Nat) : Array Expr := Id.run do
  let mut parts : Array Expr := #[]
  let mut cur := e
  for _ in [0:n-1] do
    if cur.isAppOfArity ``And 2 then
      parts := parts.push cur.appFn!.appArg!
      cur := cur.appArg!
  return parts.push cur

/-- A discharge theorem `th` for `thm`: its conclusion is exactly the conjunction of the hypotheses
of `thm` named in `disch` (stated in `thm`'s own variables, which `th` binds under the same names),
it takes each hypothesis named in `given`, it takes no other hypothesis of `thm`, and the table
classifies every hypothesis of `thm`. -/
private def pwCheckDischarge (thm th : Name) (disch given caller bnd : Array Name) : MetaM Unit :=
  pwPropBinders thm fun xs props => do
    let names := props.map (·.1)
    let all := disch ++ given ++ caller ++ bnd
    unless all.size == all.toList.eraseDups.length do
      throwError "{thm}: a hypothesis is named twice in the table"
    unless pwSame names all do
      let missing := names.filter fun n => !all.contains n
      let unknown := all.filter fun n => !names.contains n
      throwError "{thm}: the discharge table does not match the theorem's hypotheses; not classified: [{pwFmt missing}]; not in the theorem: [{pwFmt unknown}]"
    let tci ← getConstInfo th
    unless tci.isThm do throwError "{th} is not a theorem"
    forallTelescope tci.type fun ys concl => do
      let xsNames ← xs.mapM fun x => x.fvarId!.getUserName
      let ysNames ← ys.mapM fun y => y.fvarId!.getUserName
      let mut sub : Array Expr := #[]
      for i in [0:xs.size] do
        match ysNames.findIdx? (· == xsNames[i]!) with
        | some j => sub := sub.push ys[j]!
        | none => sub := sub.push xs[i]!
      for n in disch ++ caller ++ bnd do
        if ysNames.contains n then
          throwError "{th} takes {n}, which the table says it does not take (a hypothesis it discharges, or one that stays with the caller or the boundary)"
      for n in given do
        let some i := xsNames.findIdx? (· == n) | throwError "{thm} has no {n}"
        let some j := ysNames.findIdx? (· == n) | throwError "{th} does not take the given hypothesis {n}"
        let want := (← inferType xs[i]!).replaceFVars xs sub
        unless (← isDefEq (← inferType ys[j]!) want) do
          throwError "{th}: the hypothesis {n} is not the one {thm} takes:\n  {thm}: {← ppExpr want}\n  {th}: {← ppExpr (← inferType ys[j]!)}"
      let parts := pwSplit concl disch.size
      unless parts.size == disch.size do throwError "{th}: the conclusion has fewer conjuncts than the {disch.size} it discharges"
      let ids := ys.map (·.fvarId!)
      for i in [0:disch.size] do
        let some k := xsNames.findIdx? (· == disch[i]!) | throwError "{thm} has no {disch[i]!}"
        let want := (← inferType xs[k]!).replaceFVars xs sub
        for fv in (collectFVars {} want).fvarIds do
          unless ids.contains fv do
            throwError "{th}: the statement of {disch[i]!} mentions a variable of {thm} that {th} does not bind"
        unless (← isDefEq parts[i]! want) do
          throwError "{th} does not conclude {disch[i]!} of {thm}:\n  {thm}: {← ppExpr want}\n  {th}: {← ppExpr parts[i]!}"

declare_syntax_cat pwEntry
syntax ident " covers " "[" ident,* "]" " boundary " "[" ident,* "]" " unwitnessed " "[" ident,* "]" : pwEntry
syntax (name := pwWitnessesCmd) "#pw_witnesses " pwEntry* : command

syntax (name := pwWitness1Cmd) "#pw_witness1 " pwEntry : command

declare_syntax_cat pwDEntry
syntax ident " by " ident " discharges " "[" ident,* "]" " given " "[" ident,* "]" " caller " "[" ident,* "]" " boundary " "[" ident,* "]" : pwDEntry
syntax (name := pwDischargesCmd) "#pw_discharges " pwDEntry* : command

syntax (name := pwDischarge1Cmd) "#pw_discharge1 " pwDEntry : command

syntax (name := pwAppliedCmd) "#pw_applied " ident* : command

private def pwArgNames (stx : Syntax) (i : Nat) : Array Name := stx[i].getSepArgs.map (·.getId)

@[command_elab pwWitnessesCmd] def elabPwWitnesses : CommandElab := fun stx => do
  let island ← getCurrNamespace
  let mut seen : Array Name := #[]
  for e in stx[1].getArgs do
    let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo e[0]
    liftTermElabM <| pwCheckWitness island thm (pwArgNames e 3) (pwArgNames e 7) (pwArgNames e 11)
    seen := seen.push (pwNames island thm).1
  -- every statement the island defines must be in the table
  let env ← getEnv
  let prem := island ++ `Premises
  let defined := env.constants.map₂.foldl (fun (acc : Array Name) n _ =>
    if prem.isPrefixOf n then acc.push n else acc) #[]
  let extra := defined.filter fun n => !seen.contains n
  unless extra.isEmpty do
    throwError "statements under {prem} that the table does not list: [{pwFmt extra}]"
  -- and every `sat_*` theorem of the island must belong to a row
  let wanted := seen.map fun c => island ++ Name.mkSimple ("sat_" ++ (toString (c.replacePrefix prem Name.anonymous)).replace "." "_")
  let sats := env.constants.map₂.foldl (fun (acc : Array Name) n _ =>
    match n with
    | .str pre s => if pre == island && s.startsWith "sat_" then acc.push n else acc
    | _ => acc) #[]
  let extraSat := sats.filter fun n => !wanted.contains n
  unless extraSat.isEmpty do
    throwError "theorems named sat_* under {island} that no row of the table accounts for: [{pwFmt extraSat}]"
  logInfo m!"witness table complete: {seen.size} statements"

/-- The `*_at_witness` theorems of an island: each must be a theorem whose type is not a function type
(a discharge theorem applied to all its arguments), and every such theorem of the island must be listed. -/
@[command_elab pwAppliedCmd] def elabPwApplied : CommandElab := fun stx => do
  let island ← getCurrNamespace
  let env ← getEnv
  let mut seen : Array Name := #[]
  for id in stx[1].getArgs do
    let n := island ++ id.getId
    let some ci := env.find? n | throwError "{n} is not defined"
    unless ci.isThm do throwError "{n} is not a theorem"
    if ci.type.isForall then
      throwError "{n} has a function type: it applies a discharge theorem to fewer arguments than the theorem takes, so a premise added after the last argument leaves it building"
    seen := seen.push n
  let applied := env.constants.map₂.foldl (fun (acc : Array Name) n _ =>
    match n with
    | .str pre s => if pre == island && s.endsWith "_at_witness" then acc.push n else acc
    | _ => acc) #[]
  let extra := applied.filter fun n => !seen.contains n
  unless extra.isEmpty do
    throwError "*_at_witness theorems under {island} that are not listed: [{pwFmt extra}]"
  logInfo m!"applied theorems ok: {seen.size}"

/-- One row, checked alone and without the completeness check, so that cases are independent. -/
@[command_elab pwWitness1Cmd] def elabPwWitness1 : CommandElab := fun stx => do
  let island ← getCurrNamespace
  let e := stx[1]
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo e[0]
  liftTermElabM <| pwCheckWitness island thm (pwArgNames e 3) (pwArgNames e 7) (pwArgNames e 11)

@[command_elab pwDischarge1Cmd] def elabPwDischarge1 : CommandElab := fun stx => do
  let e := stx[1]
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo e[0]
  let th ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo e[2]
  liftTermElabM <| pwCheckDischarge thm th (pwArgNames e 5) (pwArgNames e 9) (pwArgNames e 13) (pwArgNames e 17)
  logInfo m!"discharge ok: {th} for {thm}"

@[command_elab pwDischargesCmd] def elabPwDischarges : CommandElab := fun stx => do
  let mut n := 0
  for e in stx[1].getArgs do
    let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo e[0]
    let th ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo e[2]
    liftTermElabM <| pwCheckDischarge thm th (pwArgNames e 5) (pwArgNames e 9) (pwArgNames e 13) (pwArgNames e 17)
    n := n + 1
    logInfo m!"discharge ok: {th} for {thm}"
  logInfo m!"discharge table checked: {n} theorems"

end PreconditionWitnessCheck
"""

# ---------------------------------------------------------------------------------------------
# The tables. One row per witnessed theorem; the groups are described in the header above.
# These lists are the part a regeneration of the modules cannot change: a row removed here is a
# change to this script, which shows in the diff, and the axiom pins of the `sat_` theorems are on
# `REQUIRED_PINS` in attest.py.
# ---------------------------------------------------------------------------------------------
LEAF_WITNESS = [
    "Tacenta.T1.receive_no_panic covers [hs] boundary [h, hk, hz, hrm] unwitnessed []",
    "Tacenta.T3.receive_refines covers [hR, hH, hone, hs, hroom] boundary [h, hk, hz, hrm] unwitnessed []",
    "Tacenta.ImportInv.Ratchet.decoded_receive_refines covers [hclock_unparked, hR, hH] boundary [h, hk, hz, hrm] unwitnessed [hdec]",
    "Tacenta.SpqrT1.receive_no_panic covers [hroom, hskiproom] boundary [hret, hrk, hz, hkdf, hopt, hrm, happ] unwitnessed []",
    "Tacenta.SpqrT1.send_no_panic covers [hroom] boundary [hret, hrk, hz, hkdf, hopt] unwitnessed []",
    "Tacenta.SpqrT3.receive_refines covers [hrel, hepoch, hroom, hcb, hsb, hnewb, hskiproom, hone, hcounter] boundary [hkr, hz96, hz64, hret, hret_total, hrm, hz, hopt] unwitnessed []",
    "Tacenta.SpqrT3.send_refines covers [hrel, hepoch, hroom, hcb, hsb, hnewb, hcounter] boundary [hkr, hz96, hz64, hret, hret_total, hz, hopt] unwitnessed []",
    "Tacenta.BraidT1.Braid.receive_no_panic covers [hct1b] boundary [hdnew, hdadd, hdmsg, hct1len, hct2len, hhdrlen, hekveclen, hekvec, henew, hdecap, hkdf, hmac, hvalek, hencaps2, henc, hdec, hkp, hes, hopt, hz, hzz, hrf] unwitnessed []",
    "Tacenta.BraidT1.Braid.step_receive_no_panic covers [hct1b] boundary [hdnew, hdadd, hdmsg, hct1len, hct2len, hhdrlen, hekveclen, hekvec, henew, hdecap, hkdf, hmac, hvalek, hencaps2, hz, hzz, hrf] unwitnessed []",
    "Tacenta.BraidT3.Braid.receive_refines covers [hct1b, hepoch] boundary [hka, hea, hmac, hkdf, hlens, hvalek, hencaps2len, hdadd, hdmsg, hct1lenB, hct2lenB, hheaderlenB, hkcl, hecl, henc, hdec, hkp, hes, hopt, hz, hzz, hrf] unwitnessed [hrel, hmsg, hhonest]",
    "Tacenta.BraidT3.step_receive_refines covers [hct1b, hepoch] boundary [hka, hea, hmac, hkdf, hlens, hvalek, hencaps2len, hdadd, hdmsg, _hct1lenB, hct2lenB, hheaderlenB, hz, hzz, hrf] unwitnessed [hrel, hmsg, hhonest]",
    "Tacenta.BraidT3.Braid.send_refines covers [hlive] boundary [hka, hea, hmac, hkdf, hhdr, hekv, hct1len, hct2len, hkcl, hecl, henc, hdec, hkp, hes, hz, hzz, hrf, hrng] unwitnessed [hrel]",
    "Tacenta.BraidT3.step_send_refines covers [hlive] boundary [hka, hea, hmac, hkdf, hhdr, _hekv, _hct1len, _hct2len, hz, hzz, hrf, hrng] unwitnessed [hrel]",
]

TRIPLE_WITNESS = [
    "Tacenta.UnitT1.receive_no_panic covers [hs] boundary [h, hk, hz, hrm] unwitnessed []",
    "Tacenta.UnitT3.receive_refines covers [hR, hH, hone, hs, hroom] boundary [h, hk, hz, hrm] unwitnessed []",
    "Tacenta.UnitSpqrT1.receive_no_panic covers [hroom, hskiproom] boundary [hret, hrk, hz, hkdf, hopt, hrm, happ] unwitnessed []",
    "Tacenta.UnitSpqrT1.send_no_panic covers [hroom] boundary [hret, hrk, hz, hkdf, hopt] unwitnessed []",
    "Tacenta.UnitSpqrT3.receive_refines covers [hrel, hepoch, hroom, hcb, hsb, hnewb, hskiproom, hone, hcounter] boundary [hkr, hz96, hz64, hret, hret_total, hrm, hz, hopt] unwitnessed []",
    "Tacenta.UnitSpqrT3.send_refines covers [hrel, hepoch, hroom, hcb, hsb, hnewb, hcounter] boundary [hkr, hz96, hz64, hret, hret_total, hz, hopt] unwitnessed []",
    "Tacenta.UnitTripleT1.State.receive_no_panic covers [hs, hroom, hskiproom] boundary [hhmac, hkdf, hzw, hz, hret, hrk, hck, hopt, hrm_ratchet, hrm, happ] unwitnessed []",
    "Tacenta.UnitTripleT1.State.send_no_panic covers [hroom] boundary [hhmac, hkdf, hz, hret, hrk, hck, hopt] unwitnessed []",
    "Tacenta.UnitTripleT3.receive_refines covers [hrel, hheader, hone, hs, hevents, hepoch, hroom, hcb, hsb, hnewb, hskiproom, hone2, hcounter] boundary [hra, hsa, hthk, hz] unwitnessed []",
    "Tacenta.UnitTripleT3.receive_refines_discharged covers [hrel, hheader, hone, hs, hevents, hepoch, hroom, hcb, hsb, hnewb, hskiproom, hone2, hcounter] boundary [hmac, hkdf, hzr, hvr, hz96, hz64, hret, hret_total, hrm, hzs, hopt] unwitnessed []",
    "Tacenta.UnitTripleT3.send_refines covers [hrel, hroom, hcb, hsb, hnewb, hepoch, hcounter] boundary [hra, hsa, hthk, hz] unwitnessed []",
    "Tacenta.UnitTripleT3.send_refines_discharged covers [hrel, hroom, hcb, hsb, hnewb, hepoch, hcounter] boundary [hmac, hkdf, hzr, hvr, hz96, hz64, hret, hret_total, hrm, hzs, hopt] unwitnessed []",
]

SESSION_WITNESS = [
    "Tacenta.SessionUnitT1.receive_no_panic covers [hs] boundary [h, hk, hz, hrm] unwitnessed []",
    "Tacenta.SessionUnitT3.receive_refines covers [hR, hH, hone, hs, hroom] boundary [h, hk, hz, hrm] unwitnessed []",
    "Tacenta.SessionUnitRatchetImportInv.Ratchet.decoded_receive_refines covers [hclock_unparked, hR, hH] boundary [h, hk, hz, hrm] unwitnessed [hdec]",
    "Tacenta.SessionUnitSpqrT1.receive_no_panic covers [hroom, hskiproom] boundary [hret, hrk, hz, hkdf, hopt, hrm, happ] unwitnessed []",
    "Tacenta.SessionUnitSpqrT1.send_no_panic covers [hroom] boundary [hret, hrk, hz, hkdf, hopt] unwitnessed []",
    "Tacenta.SessionUnitSpqrT3.receive_refines covers [hrel, hepoch, hroom, hcb, hsb, hnewb, hskiproom, hone, hcounter] boundary [hkr, hz96, hz64, hret, hret_total, hrm, hz, hopt] unwitnessed []",
    "Tacenta.SessionUnitSpqrT3.send_refines covers [hrel, hepoch, hroom, hcb, hsb, hnewb, hcounter] boundary [hkr, hz96, hz64, hret, hret_total, hz, hopt] unwitnessed []",
    "Tacenta.SessionUnitTripleT1.State.receive_no_panic covers [hs, hroom, hskiproom] boundary [hhmac, hkdf, hzw, hz, hret, hrk, hck, hopt, hrm_ratchet, hrm, happ] unwitnessed []",
    "Tacenta.SessionUnitTripleT1.State.send_no_panic covers [hroom] boundary [hhmac, hkdf, hz, hret, hrk, hck, hopt] unwitnessed []",
    "Tacenta.SessionUnitTripleT3.receive_refines covers [hrel, hheader, hone, hs, hevents, hepoch, hroom, hcb, hsb, hnewb, hskiproom, hone2, hcounter] boundary [hra, hsa, hthk, hz] unwitnessed []",
    "Tacenta.SessionUnitTripleT3.receive_refines_discharged covers [hrel, hheader, hone, hs, hevents, hepoch, hroom, hcb, hsb, hnewb, hskiproom, hone2, hcounter] boundary [hmac, hkdf, hzr, hvr, hz96, hz64, hret, hret_total, hrm, hzs, hopt] unwitnessed []",
    "Tacenta.SessionUnitTripleT3.send_refines covers [hrel, hroom, hcb, hsb, hnewb, hepoch, hcounter] boundary [hra, hsa, hthk, hz] unwitnessed []",
    "Tacenta.SessionUnitTripleT3.send_refines_discharged covers [hrel, hroom, hcb, hsb, hnewb, hepoch, hcounter] boundary [hmac, hkdf, hzr, hvr, hz96, hz64, hret, hret_total, hrm, hzs, hopt] unwitnessed []",
    "Tacenta.SessionUnitBraidT1.Braid.receive_no_panic covers [hct1b, hdb] boundary [hdnew, hdadd, hdmsg, hct1len, hct2len, hhdrlen, hekveclen, hekvec, henew, hdecap, hkdf, hmac, hvalek, hencaps2, henc, hdec, hkp, hes, hopt, hz, hzz, hrf] unwitnessed []",
    "Tacenta.SessionUnitBraidT1.Braid.step_receive_no_panic covers [hct1b, hdb] boundary [hdnew, hdadd, hdmsg, hct1len, hct2len, hhdrlen, hekveclen, hekvec, henew, hdecap, hkdf, hmac, hvalek, hencaps2, hz, hzz, hrf] unwitnessed []",
    "Tacenta.SessionUnitBraidT3.Braid.receive_refines covers [hct1b, hdb, hepoch] boundary [hka, hea, hmac, hkdf, hlens, hvalek, hencaps2len, hdadd, hdmsg, hct1lenB, hct2lenB, hheaderlenB, hkcl, hecl, henc, hdec, hkp, hes, hopt, hz, hzz, hrf] unwitnessed [hrel, hmsg, hhonest]",
    "Tacenta.SessionUnitBraidT3.step_receive_refines covers [hct1b, hdb, hepoch] boundary [hka, hea, hmac, hkdf, hlens, hvalek, hencaps2len, hdadd, hdmsg, _hct1lenB, hct2lenB, hheaderlenB, hz, hzz, hrf] unwitnessed [hrel, hmsg, hhonest]",
    "Tacenta.SessionUnitBraidT3.Braid.send_refines covers [hlive] boundary [hka, hea, hmac, hkdf, hhdr, hekv, hct1len, hct2len, hkcl, hecl, henc, hdec, hkp, hes, hz, hzz, hrf, hrng] unwitnessed [hrel]",
    "Tacenta.SessionUnitBraidT3.step_send_refines covers [hlive] boundary [hka, hea, hmac, hkdf, hhdr, _hekv, _hct1len, _hct2len, hz, hzz, hrf, hrng] unwitnessed [hrel]",
]

LEAF_DISCHARGE = [
    "Tacenta.SpqrT3.receive_refines by Tacenta.DecodedStateDischarge.spqr_receive_premises discharges [hroom, hcb, hsb, hskiproom, hone] given [hrel, hepoch] caller [hnewb, hcounter] boundary [hkr, hz96, hz64, hret, hret_total, hrm, hz, hopt]",
    "Tacenta.SpqrT3.send_refines by Tacenta.DecodedStateDischarge.spqr_send_premises discharges [hroom, hcb, hsb] given [hepoch] caller [hrel, hnewb, hcounter] boundary [hkr, hz96, hz64, hret, hret_total, hz, hopt]",
    "Tacenta.SpqrT3.advance_refines by Tacenta.DecodedStateDischarge.spqr_advance_premises discharges [hroom, hcb, hsb] given [hepoch] caller [hrel, hnewb] boundary [hkr, hz96, hret, hret_total, hz]",
    "Tacenta.SpqrT3.maybe_advance_refines by Tacenta.DecodedStateDischarge.spqr_maybe_advance_premises discharges [hroom, hcb, hsb] given [hepoch] caller [hrel, hnewb] boundary [hkr, hz96, hret, hret_total, hz]",
    "Tacenta.SpqrT3.clear_old_epochs_refines by Tacenta.DecodedStateDischarge.spqr_clear_old_epochs_premises discharges [hcb, hsb] given [] caller [hrel] boundary [hret, hret_total]",
    "Tacenta.T3.receive_refines by Tacenta.DecodedStateDischarge.ratchet_receive_premises discharges [hone, hs] given [hR] caller [hH, hroom] boundary [h, hk, hz, hrm]",
    "Tacenta.BraidT3.Braid.receive_refines by Tacenta.DecodedStateDischarge.braid_receive_premises discharges [hct1b] given [] caller [hepoch, hrel, hmsg, hhonest] boundary [hka, hea, hmac, hkdf, hlens, hvalek, hencaps2len, hdadd, hdmsg, hct1lenB, hct2lenB, hheaderlenB, hkcl, hecl, henc, hdec, hkp, hes, hopt, hz, hzz, hrf]",
    "Tacenta.BraidT3.step_receive_refines by Tacenta.DecodedStateDischarge.braid_step_receive_premises discharges [hct1b] given [] caller [hepoch, hrel, hmsg, hhonest] boundary [hka, hea, hmac, hkdf, hlens, hvalek, hencaps2len, hdadd, hdmsg, _hct1lenB, hct2lenB, hheaderlenB, hz, hzz, hrf]",
]

SESSION_DISCHARGE = [
    "Tacenta.SessionUnitSpqrT3.receive_refines by Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_receive_premises discharges [hroom, hcb, hsb, hskiproom, hone] given [hrel, hepoch] caller [hnewb, hcounter] boundary [hkr, hz96, hz64, hret, hret_total, hrm, hz, hopt]",
    "Tacenta.SessionUnitSpqrT3.send_refines by Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_send_premises discharges [hroom, hcb, hsb] given [hepoch] caller [hrel, hnewb, hcounter] boundary [hkr, hz96, hz64, hret, hret_total, hz, hopt]",
    "Tacenta.SessionUnitSpqrT3.advance_refines by Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_advance_premises discharges [hroom, hcb, hsb] given [hepoch] caller [hrel, hnewb] boundary [hkr, hz96, hret, hret_total, hz]",
    "Tacenta.SessionUnitSpqrT3.maybe_advance_refines by Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_maybe_advance_premises discharges [hroom, hcb, hsb] given [hepoch] caller [hrel, hnewb] boundary [hkr, hz96, hret, hret_total, hz]",
    "Tacenta.SessionUnitSpqrT3.clear_old_epochs_refines by Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_clear_old_epochs_premises discharges [hcb, hsb] given [] caller [hrel] boundary [hret, hret_total]",
    "Tacenta.SessionUnitT3.receive_refines by Tacenta.SessionUnitDecodedStateDischarge.session_unit_ratchet_receive_premises discharges [hone, hs] given [hR] caller [hH, hroom] boundary [h, hk, hz, hrm]",
    "Tacenta.SessionUnitBraidT3.Braid.receive_refines by Tacenta.SessionUnitDecodedStateDischarge.session_unit_braid_receive_premises discharges [hct1b, hdb] given [] caller [hepoch, hrel, hmsg, hhonest] boundary [hka, hea, hmac, hkdf, hlens, hvalek, hencaps2len, hdadd, hdmsg, hct1lenB, hct2lenB, hheaderlenB, hkcl, hecl, henc, hdec, hkp, hes, hopt, hz, hzz, hrf]",
    "Tacenta.SessionUnitBraidT3.step_receive_refines by Tacenta.SessionUnitDecodedStateDischarge.session_unit_braid_step_receive_premises discharges [hct1b, hdb] given [] caller [hepoch, hrel, hmsg, hhonest] boundary [hka, hea, hmac, hkdf, hlens, hvalek, hencaps2len, hdadd, hdmsg, _hct1lenB, hct2lenB, hheaderlenB, hz, hzz, hrf]",
    "Tacenta.SessionUnitTripleT3.receive_refines_discharged by Tacenta.SessionUnitDecodedStateDischarge.triple_receive_premises discharges [hone, hs, hroom, hcb, hsb, hskiproom, hone2] given [hrel, hevents, hepoch] caller [hnewb, hcounter, hheader] boundary [hmac, hkdf, hzr, hvr, hz96, hz64, hret, hret_total, hrm, hzs, hopt]",
    "Tacenta.SessionUnitTripleT3.send_refines_discharged by Tacenta.SessionUnitDecodedStateDischarge.triple_send_premises discharges [hroom, hcb, hsb] given [hrel, hepoch] caller [hnewb, hcounter] boundary [hmac, hkdf, hzr, hvr, hz96, hz64, hret, hret_total, hrm, hzs, hopt]",
]

# The discharge theorems applied at the witness state, by name under the witness module's namespace.
LEAF_APPLIED = [
    "spqr_receive_premises_at_witness", "spqr_send_premises_at_witness", "spqr_advance_premises_at_witness",
    "spqr_maybe_advance_premises_at_witness", "spqr_clear_old_epochs_premises_at_witness",
    "ratchet_receive_premises_at_witness", "braid_receive_premises_at_witness",
    "braid_step_receive_premises_at_witness",
]
SESSION_APPLIED = [
    "session_unit_spqr_receive_premises_at_witness", "session_unit_spqr_send_premises_at_witness",
    "session_unit_spqr_advance_premises_at_witness", "session_unit_spqr_maybe_advance_premises_at_witness",
    "session_unit_spqr_clear_old_epochs_premises_at_witness", "session_unit_ratchet_receive_premises_at_witness",
    "session_unit_braid_receive_premises_at_witness", "session_unit_braid_step_receive_premises_at_witness",
    "triple_receive_premises_at_witness", "triple_send_premises_at_witness",
]

ISLANDS = [
    # (witness module, witness rows, discharge module, discharge rows, applied theorems)
    ("NumericWitnessLeaf", LEAF_WITNESS, "DecodedStateDischarge", LEAF_DISCHARGE, LEAF_APPLIED),
    ("NumericWitnessTriple", TRIPLE_WITNESS, None, None, []),
    ("NumericWitnessSession", SESSION_WITNESS, "SessionUnitDecodedStateDischarge", SESSION_DISCHARGE,
     SESSION_APPLIED),
]

INFRA = ("object file", "unknown module prefix", "no such file", "could not find",
         "unknown package", "failed to read file")
cases = 0
accepted_n = 0
wrong = []
MSG = re.compile(r"^[^\n]*?case\.lean:(\d+):\d+: (error|warning|info)[^\n]*", re.M)


def read(mod):
    return open(os.path.join(base, mod + ".lean"), encoding="utf-8").read()


def without_pins(text):
    """The module as it is before its first axiom pin."""
    marker = "\n/--\ninfo: '"
    return text[:text.index(marker)] if marker in text else text


def run(text):
    path = os.path.join(tmp, "case.lean")
    with open(path, "w") as f:
        f.write(text)
    p = subprocess.run(["lake", "env", "lean", path], cwd=translation, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def infra(out):
    low = out.lower()
    return any(s in low for s in INFRA)


def messages(out):
    """Line of the command -> the error and info messages Lean printed for it."""
    marks = list(MSG.finditer(out))
    by_line = {}
    for k, m in enumerate(marks):
        end = marks[k + 1].start() if k + 1 < len(marks) else len(out)
        by_line.setdefault(int(m.group(1)), []).append((m.group(2), out[m.start():end]))
    return by_line


class File:
    """A Lean file built from a prefix and one command per case; each case is checked against the
    messages Lean printed at its own line, so the cases are independent."""

    def __init__(self, prefix):
        self.text = prefix.rstrip("\n") + "\n"
        self.items = []

    def command(self, name, command, reason=None, needles=()):
        first = next(i for i, l in enumerate(command.split("\n")) if l.startswith("#pw_"))
        line = self.text.count("\n") + 1 + first
        self.text += command.rstrip("\n") + "\n"
        self.items.append((name, line, reason, needles))

    def check(self, label):
        global cases, accepted_n
        rc, out = run(self.text)
        if infra(out):
            wrong.append(f"{label}: failed because the build is missing, not as a refusal:\n{out[:600]}")
            return
        by_line = messages(out)
        for name, line, reason, needles in self.items:
            cases += 1
            msgs = by_line.get(line, [])
            errors = [m for kind, m in msgs if kind == "error"]
            if reason is None:
                accepted_n += 1
                if errors:
                    wrong.append(f"{name}: expected acceptance, was refused:\n{errors[0][:1200]}")
                else:
                    for n in needles:
                        if n not in out:
                            wrong.append(f"{name}: accepted, but the output lacks '{n}'")
            else:
                if not errors:
                    wrong.append(f"{name}: expected refusal containing '{reason}', was accepted")
                elif not any(reason in e for e in errors):
                    wrong.append(f"{name}: refused, but not for '{reason}':\n{errors[0][:1200]}")
                elif os.environ.get("PWCHECK_VERBOSE") == "1":
                    print(f"  {name}: {errors[0].splitlines()[0][-150:]}")


def once(text, old, new, what):
    if text.count(old) != 1:
        wrong.append(f"{what}: the text to change occurs {text.count(old)} times, expected once")
        return None
    return text.replace(old, new)


def table(rows):
    return "\n".join("  " + r for r in rows)


def w_all(rows):
    return "#pw_witnesses\n" + table(rows)


def row_of(rows, theorem):
    for r in rows:
        if r.split()[0] == "Tacenta." + theorem:
            return r
    wrong.append("no table row for " + theorem)
    return None


def mutated(rows, theorem, old, new):
    r = row_of(rows, theorem)
    if r is None:
        return None
    if r.count(old) != 1:
        wrong.append(f"'{old}' occurs {r.count(old)} times in the row of {theorem}")
        return None
    return r.replace(old, new)


started = time.time()

# ------------------------------------------------------------------ the modules as they are
for mod, rows, dmod, drows, applied in ISLANDS:
    f = File(without_pins(read(mod)) + "\n" + META + "\nnamespace Tacenta." + mod)
    f.command("witnesses of " + mod + " match their theorems", w_all(rows), None,
              ["witness table complete: %d statements" % len(rows)] + ["witness ok: " + r.split()[0] for r in rows])
    if applied:
        f.command("the discharge theorems applied in " + mod + " are applications", "#pw_applied " + " ".join(applied),
                  None, ["applied theorems ok: %d" % len(applied)])
    f.text += "end Tacenta." + mod + "\n"
    f.check("positive " + mod)
    if dmod:
        f = File(without_pins(read(dmod)) + "\n" + META + "\nopen Aeneas Aeneas.Std")
        f.command("discharge theorems of " + dmod + " match their theorems", "#pw_discharges\n" + table(drows), None,
                  ["discharge table checked: %d theorems" % len(drows)] +
                  ["discharge ok: " + r.split()[2] + " for " + r.split()[0] for r in drows])
        f.check("positive " + dmod)

# ------------------------------------------------------------------ one change at a time to the leaf witnesses
nm = "NumericWitnessLeaf"
leaf = without_pins(read(nm))
text = leaf
# four statements and witnesses changed, each on a theorem of its own
text = once(text, "s.events.val + 1 < U32.max ∧ T3.StateR s m", "s.events.val + 1 ≤ U32.max ∧ T3.StateR s m",
            "weakening a ceiling") or text
text = once(text, "s.chains.val.length + 1 < Usize.max", "s.chains.val.length + 0 < Usize.max",
            "weakening a conjunct") or text
text = once(text, "theorem sat_SpqrT1_send_no_panic :", "theorem sat_SpqrT1_send_no_panic_gone :",
            "deleting a witness") or text
text = once(text, "theorem sat_BraidT3_step_send_refines :", "theorem sat_BraidT3_step_send_refines_real :",
            "renaming a witness") or text
text = once(text, "\nend Tacenta.NumericWitnessLeaf",
            "\ntheorem sat_BraidT3_step_send_refines : True := trivial\n\nabbrev Premises.Extra : Prop := True\n"
            "\nend Tacenta.NumericWitnessLeaf", "appending a weaker witness and a statement") or text
text = once(text, """theorem spqr_clear_old_epochs_premises_at_witness :
    type_of% (DecodedStateDischarge.spqr_clear_old_epochs_premises spqrS_epoch_room spqrS_inv) :=
  DecodedStateDischarge.spqr_clear_old_epochs_premises spqrS_epoch_room spqrS_inv""",
            """theorem spqr_clear_old_epochs_premises_at_witness :
    type_of% (DecodedStateDischarge.spqr_clear_old_epochs_premises spqrS_epoch_room) :=
  DecodedStateDischarge.spqr_clear_old_epochs_premises spqrS_epoch_room""",
            "dropping the last argument of an application") or text
f = File(text + "\n" + META + "\nnamespace Tacenta." + nm)
LW = LEAF_WITNESS
single = lambda r: "#pw_witness1 " + r
f.command("a conjunct is weakened in SpqrT3.send_refines", single(row_of(LW, "SpqrT3.send_refines")),
          "is not the conjunction of the hypotheses of Tacenta.SpqrT3.send_refines")
f.command("a ceiling is weakened from < to <= in decoded_receive_refines",
          single(row_of(LW, "ImportInv.Ratchet.decoded_receive_refines")),
          "is not the conjunction of the hypotheses of Tacenta.ImportInv.Ratchet.decoded_receive_refines")
f.command("the witness of SpqrT1.send_no_panic is deleted", single(row_of(LW, "SpqrT1.send_no_panic")),
          "Unknown constant")
f.command("the witness of BraidT3.step_send_refines proves True", single(row_of(LW, "BraidT3.step_send_refines")),
          "does not state")
# an applied discharge theorem that lost its last argument is a function type: what a premise added after the
# last argument looks like to the build, which accepts it
f.command("an application of a discharge theorem has a function type", "#pw_applied " + " ".join(LEAF_APPLIED),
          "spqr_clear_old_epochs_premises_at_witness has a function type")
f.command("an applied theorem is not listed",
          "#pw_applied " + " ".join(n for n in LEAF_APPLIED if n not in (
              "spqr_send_premises_at_witness", "spqr_clear_old_epochs_premises_at_witness")),
          "Tacenta.NumericWitnessLeaf.spqr_send_premises_at_witness")
# the four changed theorems are left out of these two tables, so that the check reaches the completeness test
CHANGED = {"SpqrT3.send_refines", "ImportInv.Ratchet.decoded_receive_refines", "SpqrT1.send_no_panic",
           "BraidT3.step_send_refines"}
LW_REST = [r for r in LW if r.split()[0][len("Tacenta."):] not in CHANGED]
f.command("a statement is added under Premises and not listed", w_all(LW_REST),
          "Tacenta.NumericWitnessLeaf.Premises.Extra")
f.command("the row of T1.receive_no_panic is removed from the table",
          w_all([r for r in LW_REST if r.split()[0] != "Tacenta.T1.receive_no_panic"]),
          "Premises.T1.receive_no_panic")
# the table changed, the module not
for name, theorem, old, new, reason in [
    ("a hypothesis of T1.receive_no_panic is not classified", "T1.receive_no_panic", "hk, ", "",
     "not classified: [hk]"),
    ("a hypothesis the theorem lacks is named", "T1.receive_no_panic", "boundary [", "boundary [hbogus, ",
     "not in the theorem: [hbogus]"),
    ("a numeric hypothesis is listed as boundary", "T1.receive_no_panic", "covers [hs] boundary [",
     "covers [] boundary [hs, ",
     "is numeric (or a numeric state predicate) and is listed as outside the witness"),
    ("a boundary hypothesis is claimed as covered", "T3.receive_refines",
     "covers [hR, hH, hone, hs, hroom] boundary [h, ", "covers [hR, hH, hone, hs, hroom, h] boundary [",
     "is not the conjunction of the hypotheses of Tacenta.T3.receive_refines"),
    ("a numeric state predicate is listed as boundary", "BraidT3.Braid.send_refines",
     "covers [hlive] boundary [", "covers [] boundary [hlive, ",
     "is numeric (or a numeric state predicate) and is listed as outside the witness"),
]:
    r = mutated(LW, theorem, old, new)
    if r is not None:
        f.command(name, single(r), reason)
f.text += "end Tacenta." + nm + "\n"
f.check("the leaf witnesses, one change at a time")

# ------------------------------------------------------------------ one change at a time to a discharge table
dleaf = without_pins(read("DecodedStateDischarge"))
f = File(dleaf + "\n" + META + "\nopen Aeneas Aeneas.Std")


def drow(theorem):
    for r in LEAF_DISCHARGE:
        if r.split()[0] == "Tacenta." + theorem:
            return r
    wrong.append("no discharge row for " + theorem)
    return None


for name, theorem, old, new, reason in [
    ("a discharged hypothesis is not listed", "SpqrT3.receive_refines",
     "discharges [hroom, hcb, hsb, hskiproom, hone]", "discharges [hroom, hcb, hsb, hskiproom]",
     "the discharge table does not match the theorem's hypotheses; not classified: [hone]"),
    ("two discharged hypotheses are swapped", "SpqrT3.receive_refines",
     "discharges [hroom, hcb, hsb, hskiproom, hone]", "discharges [hcb, hroom, hsb, hskiproom, hone]",
     "does not conclude hcb of Tacenta.SpqrT3.receive_refines"),
    ("a given hypothesis is moved to the caller", "SpqrT3.send_refines",
     "given [hepoch] caller [hrel, hnewb, hcounter]", "given [] caller [hepoch, hrel, hnewb, hcounter]",
     "takes hepoch, which the table says it does not take"),
    ("a hypothesis the theorem lacks is named", "SpqrT3.send_refines", "caller [hrel, ", "caller [hbogus, hrel, ",
     "not in the theorem: [hbogus]"),
]:
    r = drow(theorem)
    if r is None or r.count(old) != 1:
        wrong.append(f"{name}: cannot apply the change to the row of {theorem}")
        continue
    f.command(name, "#pw_discharge1 " + r.replace(old, new), reason)
f.check("the leaf discharge table, one change at a time")

# ------------------------------------------------------------------ a theorem that gains a hypothesis, and a discharge theorem that changes
TOY = """import Aeneas
open Aeneas Aeneas.Std
namespace Tacenta
theorem ToyA (n : Nat) (h1 : n + 1 < Usize.max) : True := trivial
theorem ToyB (n : Nat) (h1 : n + 1 < Usize.max) (h2 : n < Usize.max - 1) : True := trivial
theorem ToyC (n : Nat) (h1 : n + 1 < Usize.max) (h2 : n < Usize.max - 1) : True := trivial
theorem ToyD (n : Nat) (h1 : n + 1 < Usize.max) (h2 : n < Usize.max - 1) : True := trivial
theorem ToyE (n : Nat) (h1 : n + 1 < Usize.max) (h2 : n = n) : True := trivial
theorem ToyF (n : Nat) (h0 : n < 3) (h1 : n < 5) (h2 : n < 6) : True := trivial
theorem ToyG (n : Nat) (h0 : n < 3) (h1 : n < 5) (h2 : n < 6) : True := trivial
theorem ToyH (n : Nat) (h0 : n < 3) (h1 : n < 5) (h2 : n < 6) : True := trivial
theorem ToyS (n : Nat) (h1 : n + 1 < Usize.max) : True := trivial
end Tacenta
"""
for k in "ABCDES":
    TOY += (f"namespace Tacenta.NumericWitnessToy{k}\nabbrev Premises.Toy{k} : Prop := ∃ n : Nat, n + 1 < Usize.max\n"
            f"theorem sat_Toy{k} : Premises.Toy{k} := ⟨0, by scalar_tac⟩\nend Tacenta.NumericWitnessToy{k}\n")
TOY += """namespace Tacenta.NumericWitnessToyD
theorem toyDischarge (n : Nat) (h0 : n < 3) : n < 5 ∧ n < 6 := ⟨by omega, by omega⟩
theorem toyDischargeWeak (n : Nat) (h0 : n < 3) : n < 5 ∧ n < 7 := ⟨by omega, by omega⟩
theorem toyDischargeGiven (n : Nat) (h0 : n < 4) : n < 5 ∧ n < 6 := ⟨by omega, by omega⟩
theorem toyDischargeExtra (n : Nat) (h0 : n < 3) (hextra : False) : n < 5 ∧ n < 6 := ⟨by omega, by omega⟩
end Tacenta.NumericWitnessToyD
namespace Tacenta.NumericWitnessToyS
theorem sat_Extra : True := trivial
end Tacenta.NumericWitnessToyS
namespace Tacenta.NumericWitnessToyP1
theorem ok_at_witness : type_of% (Tacenta.NumericWitnessToyD.toyDischarge 1 (by omega)) :=
  Tacenta.NumericWitnessToyD.toyDischarge 1 (by omega)
end Tacenta.NumericWitnessToyP1
namespace Tacenta.NumericWitnessToyP2
theorem partial_at_witness : type_of% (Tacenta.NumericWitnessToyD.toyDischargeExtra 1 (by omega)) :=
  Tacenta.NumericWitnessToyD.toyDischargeExtra 1 (by omega)
end Tacenta.NumericWitnessToyP2
namespace Tacenta.NumericWitnessToyP3
theorem unlisted_at_witness : type_of% (Tacenta.NumericWitnessToyD.toyDischarge 1 (by omega)) :=
  Tacenta.NumericWitnessToyD.toyDischarge 1 (by omega)
end Tacenta.NumericWitnessToyP3
"""
f = File(TOY + META)
row = lambda k, cov, bnd: f"Tacenta.Toy{k} covers [{cov}] boundary [{bnd}] unwitnessed []"
f.command("a theorem with one hypothesis is accepted",
          f"namespace Tacenta.NumericWitnessToyA\n#pw_witnesses\n  {row('A', 'h1', '')}\nend Tacenta.NumericWitnessToyA",
          None, ["witness ok: Tacenta.ToyA"])
f.command("a numeric hypothesis is added to the theorem",
          f"namespace Tacenta.NumericWitnessToyB\n#pw_witness1 {row('B', 'h1', '')}\nend Tacenta.NumericWitnessToyB",
          "not classified: [h2]")
f.command("it is added and classified as boundary",
          f"namespace Tacenta.NumericWitnessToyC\n#pw_witness1 {row('C', 'h1', 'h2')}\nend Tacenta.NumericWitnessToyC",
          "is numeric (or a numeric state predicate) and is listed as outside the witness")
f.command("it is added and classified as covered, and the statement is not changed",
          f"namespace Tacenta.NumericWitnessToyD\n#pw_witness1 {row('D', 'h1, h2', '')}\nend Tacenta.NumericWitnessToyD",
          "is not the conjunction of the hypotheses of Tacenta.ToyD")
f.command("a non-numeric hypothesis is added and not classified",
          f"namespace Tacenta.NumericWitnessToyE\n#pw_witness1 {row('E', 'h1', '')}\nend Tacenta.NumericWitnessToyE",
          "not classified: [h2]")
disch = lambda t, th: (f"#pw_discharge1 Tacenta.{t} by Tacenta.NumericWitnessToyD.{th} discharges [h1, h2] "
                       "given [h0] caller [] boundary []")
f.command("a discharge theorem is accepted", disch("ToyF", "toyDischarge"), None,
          ["discharge ok: Tacenta.NumericWitnessToyD.toyDischarge for Tacenta.ToyF"])
f.command("a discharged hypothesis is changed in the theorem", disch("ToyG", "toyDischargeWeak"),
          "does not conclude h2 of Tacenta.ToyG")
f.command("a given hypothesis is changed in the theorem", disch("ToyH", "toyDischargeGiven"),
          "is not the one Tacenta.ToyH takes")
f.command("a theorem named sat_* that no row accounts for",
          f"namespace Tacenta.NumericWitnessToyS\n#pw_witnesses\n  {row('S', 'h1', '')}\nend Tacenta.NumericWitnessToyS",
          "theorems named sat_* under Tacenta.NumericWitnessToyS that no row of the table accounts for: "
          "[Tacenta.NumericWitnessToyS.sat_Extra]")
f.command("an applied discharge theorem is accepted",
          "namespace Tacenta.NumericWitnessToyP1\n#pw_applied ok_at_witness\nend Tacenta.NumericWitnessToyP1", None,
          ["applied theorems ok: 1"])
f.command("a discharge theorem that took a premise after its last argument is refused",
          "namespace Tacenta.NumericWitnessToyP2\n#pw_applied partial_at_witness\nend Tacenta.NumericWitnessToyP2",
          "partial_at_witness has a function type")
f.command("an applied theorem that is not listed is refused",
          "namespace Tacenta.NumericWitnessToyP3\n#pw_applied\nend Tacenta.NumericWitnessToyP3",
          "unlisted_at_witness")
f.check("a theorem that gains a hypothesis, and a discharge theorem that changes")

print(f"check-precondition-witnesses: {cases} cases ({accepted_n} accepted, {cases - accepted_n} refused) "
      f"in {int(time.time() - started)}s")
if wrong:
    print("", file=sys.stderr)
    for w in wrong:
        print("FAIL: " + w, file=sys.stderr)
    sys.exit(1)
print("check-precondition-witnesses: the witnesses and discharge theorems of 3 translations match their "
      "theorems, and each broken case is refused")
PY
