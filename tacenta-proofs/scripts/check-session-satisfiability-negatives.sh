#!/usr/bin/env bash
# Hold the Session contract satisfiability evidence to mutations, and run the
# classification audit of the joint model.
#
# Nine modules carry that evidence: the three below, and the six of the joint decision of OracleOf
# (UnitOracleShape.lean to UnitOracleJoint.lean, the oracle group):
#
#   UnitSatisfiabilitySession.lean  thirteen separate witnesses, one per boundary
#                                   contract of the first Session proof layer, and one
#                                   theorem that names them all.
#   UnitSatisfiabilityJoint.lean    one interpretation of the unit's opaque constants
#                                   that satisfies every axiom-level field of the four
#                                   contract records, each shape bound to the real
#                                   predicate by `Iff.rfl`, except that `VecRetainTotal`
#                                   is bound by regrouping its conjuncts.
#   UnitSatisfiabilityRecords.lean  the four records proved from that base.
#
# Each case below applies ONE change to a copy of a module and requires `lake
# env lean` to fail with the stated message. The unmodified copy must pass first:
# a refusal is only evidence if acceptance is possible. A copy that fails
# because the build is missing (no olean, unknown module) is not a refusal and
# is reported as a failure of this script.
#
# The groups:
#   witnesses     every witness of the Session module, removed in turn. The list is
#                 read from the coverage theorem, and the script fails if a
#                 `*_satisfiable` theorem of the module is not on it. The `Vec::pop`
#                 witness's proof replaced by one for the function that does not shorten the
#                 vector, which the law `w.val = v.val.dropLast` refuses.
#   model         the joint model changed so that one faithful field breaks.
#   bridges       a shape changed by one constant or one premise, so that its `Iff.rfl` bridge to
#                 the real predicate is rejected; a field dropped from a record's parts. The
#                 aggregate `all_shapes_are_predicates` must name every `_is` bridge.
#   records       a field dropped from a structure the record proofs build.
#   oracle        the clauses of `OracleOf` decided jointly (UnitOracle*.lean): each witness removed
#                 in turn, nine primitives and the private-key view of the joint model changed one at
#                 a time, each refused by the result, the lemma or the law of the model that needs
#                 it, and a bridge or a record changed by one field, each refused.
#   audit         the classification audit (the Lean text in AUDIT below), appended to a
#                 copy of the joint module. It must pass on the module and print the
#                 field counts, and must fail on five mutations of the module and on the two
#                 commands that take a structure given the wrong kind of structure.
#
# The audit is text in this script and not a Lean module because
# `check-lean-constructs.sh` refuses elaboration-time code in the translation
# package, and not a `.lean` file of this directory because
# `tooling/check-precondition-shapes.py` expects every Lean file of a package
# directory to be one it scans. See the header comment of the text.
set -euo pipefail

cd "$(dirname "$0")/.."
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT INT TERM

TMP="$tmp" python3 - <<'PY'
import os, re, subprocess, sys

tmp = os.environ["TMP"]
translation = "translation"
base = os.path.join(translation, "Translation")
session = open(os.path.join(base, "UnitSatisfiabilitySession.lean")).read()
joint = open(os.path.join(base, "UnitSatisfiabilityJoint.lean")).read()
records = open(os.path.join(base, "UnitSatisfiabilityRecords.lean")).read()
AUDIT = r"""/-
The classification audit of `Translation/UnitSatisfiabilityJoint.lean`.

This text is not part of the Lean package.  `check-lean-constructs.sh` refuses elaboration-time
code (`elab`, `syntax`, any reference to the `Lean` namespace) in hand-written Translation modules,
and its allow-list is the audit invocations of `Model.AxiomAudit`; the checks below need that kind
of code, so they cannot be a module.  `check-session-satisfiability-negatives.sh` appends this file
to a copy of the module (an unmodified copy, and copies with one mutation each) and runs
`lake env lean` on the result.  Nothing is written to an olean, so nothing here enters an
environment a theorem is checked in.

What the four commands check, by walking the elaborated environment:

* `#audit_interp_exact`: no field type of `Interp` mentions an opaque unit axiom (other than the
  error type inside `RngCore`).
* `#audit_interp_complete`: the unit axioms `Interp.real` interprets are exactly those the four
  records and the class `DerivedKeysModel` reach.
* `#audit_axiom_part`: no field of an axiom part (or of `StdLaws`, `FaithfulShape`) mentions an opaque
  unit axiom or a translated function except through an `Interp` field.
* `#audit_defined_part`: every field of a defined part mentions a translated function.

They do not check that a shape is the right statement (the `Iff.rfl` bridges do, in the build), that a
model fact is true (the build), or that a defined field is proved (the build).
-/

section Audit

open Lean Meta Elab Command

private def auditConsts (e : Expr) : NameSet := e.foldConsts {} fun n s => s.insert n

private def auditIsUnit (n : Name) : Bool := n.getRoot == `tacenta_session_unit

private partial def auditReach (env : Environment) (start : NameSet) :
    NameSet × NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut axs : NameSet := {}
  let mut defs : NameSet := {}
  let mut todo := start.toList
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        if auditIsUnit n then
          match ci with
          | .axiomInfo _ => axs := axs.insert n
          | .opaqueInfo _ => axs := axs.insert n
          | _ =>
            defs := defs.insert n
            if let some v := ci.value? then
              for c in (auditConsts v).toList do todo := c :: todo
          for c in (auditConsts ci.type).toList do todo := c :: todo
  return (axs, defs)

/-- Unit constants mentioned by an expression, following our own definitions. -/
private partial def auditMentioned (env : Environment) (e : Expr) : NameSet := Id.run do
  let mut out : NameSet := {}
  let mut seen : NameSet := {}
  let mut todo := (auditConsts e).toList
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | m :: rest =>
      todo := rest
      if seen.contains m then continue
      seen := seen.insert m
      if auditIsUnit m then
        out := out.insert m
      else if m.getRoot == `Tacenta then
        match env.find? m with
        | none => pure ()
        | some ci =>
          for c in (auditConsts ci.type).toList do todo := c :: todo
          if let some v := ci.value? then
            for c in (auditConsts v).toList do todo := c :: todo
          if let .inductInfo iv := ci then
            for c in iv.ctors do todo := c :: todo
  return out

private def auditIsTypeFormer (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | none => false
  | some ci =>
    let rec go : Expr → Bool
      | .forallE _ _ b _ => go b
      | .sort _ => true
      | _ => false
    go ci.type

/-- A translated function: a definition with a body, of function type, that is
not a type former.  Constructors and axioms are not counted. -/
private def auditIsFunction (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo ci) => ci.type.isForall && !auditIsTypeFormer env n
  | _ => false

/-- The binder types of the last `k` binders of a constructor type. -/
private def auditFieldTypes (ctorType : Expr) (k : Nat) : List Expr :=
  let rec binders : Expr → List Expr
    | .forallE _ d b _ => d :: binders b
    | _ => []
  let bs := binders ctorType
  bs.drop (bs.length - k)

private def auditNumFields (env : Environment) (s : Name) : Nat :=
  (getStructureFields env s).size

private def errorAxiom : Name := `tacenta_session_unit.rand_core_1.error.Error

private def allowedProjection (n : Name) : Bool :=
  n == `tacenta_session_unit.rand_core_1.RngCore.fill_bytes

elab "#audit_interp_exact " i:ident : command => do
  let env ← getEnv
  let iname ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
  let some ci := env.find? (iname ++ `mk) | throwError "no constructor"
  let us := auditMentioned env ci.type
  let (axs, _) := auditReach env us
  let bad := axs.toList.filter (· != errorAxiom)
  unless bad.isEmpty do
    throwError "Interp mentions uninterpreted unit axioms: {bad}"
  logInfo m!"Interp: no uninterpreted unit axiom in any field type (mentions {us.size} unit constants)"

elab "#audit_axiom_part " ss:ident* : command => do
  let env ← getEnv
  for s in ss do
    let sname ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
    let some ci := env.find? (sname ++ `mk) | throwError "no constructor for {sname}"
    let ftys := auditFieldTypes ci.type (auditNumFields env sname)
    let mut total : Nat := 0
    for t in ftys do
      let us := auditMentioned env t
      let (axs, _) := auditReach env us
      let badAx := axs.toList.filter (· != errorAxiom)
      let badFn := us.toList.filter fun c =>
        auditIsFunction env c && !allowedProjection c
      unless badAx.isEmpty && badFn.isEmpty do
        throwError "{sname}: a field mentions unit axioms {badAx} or translated functions {badFn}"
      total := total + 1
    logInfo m!"{sname}: {total} fields, none mentions a unit axiom or translated function outside an Interp field"

elab "#audit_defined_part " ss:ident* : command => do
  let env ← getEnv
  for s in ss do
    let sname ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
    let some ci := env.find? (sname ++ `mk) | throwError "no constructor for {sname}"
    let ftys := auditFieldTypes ci.type (auditNumFields env sname)
    let mut total : Nat := 0
    for t in ftys do
      let us := auditMentioned env t
      let fns := us.toList.filter fun c =>
        auditIsFunction env c && !allowedProjection c
      if fns.isEmpty then
        throwError "{sname}: a field mentions no translated function"
      total := total + 1
    logInfo m!"{sname}: {total} fields, each mentions a translated function"

/-- The interpreted axioms are exactly the axioms the four records depend on:
every unit axiom reached by any field of the four records and the two model
classes is a field of `Interp.real` (or the error type inside `RngCore`), and
every field of `Interp.real` is reached. -/
elab "#audit_interp_complete " real:ident " from " rs:ident* : command => do
  let env ← getEnv
  let realName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo real
  let some rci := env.find? realName | throwError "no {realName}"
  let some rv := rci.value? | throwError "no body"
  let mut interpreted : NameSet := {}
  for c in (auditConsts rv).toList do
    if auditIsUnit c then interpreted := interpreted.insert c
  let mut start : NameSet := {}
  for r in rs do
    let rn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo r
    start := start.insert rn
  let mut us : NameSet := {}
  for n in start.toList do
    let mentioned := auditMentioned env (mkConst n)
    for c in mentioned.toList do us := us.insert c
  let (axs, _) := auditReach env us
  let reached := axs.toList.filter (· != errorAxiom)
  let missing := reached.filter fun a => !interpreted.contains a
  let extra := interpreted.toList.filter fun a => !(axs.contains a)
  unless missing.isEmpty do
    throwError "axioms reached by the records but not interpreted: {missing}"
  unless extra.isEmpty do
    throwError "axioms interpreted but not reached by the records: {extra}"
  logInfo m!"Interp.real interprets exactly the {interpreted.size} unit axioms reached by the records"

#audit_interp_exact Tacenta.UnitSatisfiabilityJoint.Interp
#audit_interp_complete Tacenta.UnitSatisfiabilityJoint.Interp.real from
  Tacenta.UnitLifecycleT1.EncryptContracts Tacenta.UnitLifecycleT1.DecryptRatchetContracts
  Tacenta.UnitLifecycleT1.EstablishInitiatorContracts
  Tacenta.UnitLifecycleT1.EstablishResponderContracts
  Tacenta.SessionUnitT1.DerivedKeysModel
#audit_axiom_part Tacenta.UnitSatisfiabilityJoint.BraidSendAxiom
  Tacenta.UnitSatisfiabilityJoint.TripleSendAxiom Tacenta.UnitSatisfiabilityJoint.EncryptAxiom
  Tacenta.UnitSatisfiabilityJoint.BraidReceiveAxiom
  Tacenta.UnitSatisfiabilityJoint.TripleReceiveAxiom Tacenta.UnitSatisfiabilityJoint.DecryptAxiom
  Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitSatisfiabilityJoint.ResponderAxiom
  Tacenta.UnitSatisfiabilityJoint.StdLaws Tacenta.UnitSatisfiabilityJoint.FaithfulShape
#audit_defined_part Tacenta.UnitSatisfiabilityJoint.BraidSendDefined
  Tacenta.UnitSatisfiabilityJoint.TripleSendDefined Tacenta.UnitSatisfiabilityJoint.EncryptDefined
  Tacenta.UnitSatisfiabilityJoint.BraidReceiveDefined
  Tacenta.UnitSatisfiabilityJoint.TripleReceiveDefined Tacenta.UnitSatisfiabilityJoint.DecryptDefined
  Tacenta.UnitSatisfiabilityJoint.InitiatorDefined Tacenta.UnitSatisfiabilityJoint.ResponderDefined

end Audit
"""
audit = AUDIT

INFRA = ("object file", "unknown module prefix", "no such file", "could not find",
         "unknown package", "failed to read file")
cases = 0
accepted = 0

wrong = []


def run(text):
    path = os.path.join(tmp, "case.lean")
    with open(path, "w") as f:
        f.write(text)
    p = subprocess.run(["lake", "env", "lean", path], cwd=translation,
                       capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def infra(out):
    low = out.lower()
    return any(s in low for s in INFRA)


def passes(name, text, needles=()):
    global cases, accepted
    cases += 1
    accepted += 1
    rc, out = run(text)
    if rc != 0 or infra(out):
        wrong.append(f"{name}: expected acceptance, was refused:\n{out[:1500]}")
        return
    for n in needles:
        if n not in out:
            wrong.append(f"{name}: accepted, but the output lacks '{n}'")


def refused(name, text, reason):
    global cases
    cases += 1
    rc, out = run(text)
    if rc == 0:
        wrong.append(f"{name}: expected refusal containing '{reason}', was accepted")
    elif infra(out):
        wrong.append(f"{name}: failed because the build is missing, not as a refusal:\n{out[:600]}")
    elif reason not in out:
        wrong.append(f"{name}: refused, but not for '{reason}':\n{out[:1200]}")
    elif os.environ.get("SATNEG_VERBOSE"):
        first = next((l for l in out.splitlines() if "error" in l), "")
        print(f"  {name}: {first[:150]}")


def once(text, old, new, what):
    if text.count(old) != 1:
        wrong.append(f"{what}: the text to change occurs {text.count(old)} times, expected once")
        return None
    return text.replace(old, new)


# ---------------------------------------------------------------- witnesses
passes("session-unmodified", session)

m = re.search(r"theorem all_thirteen_contracts_satisfiable :.*?:=\s*⟨(.*?)⟩\s*\nend ", session, re.S)
listed = re.findall(r"[A-Za-z_][A-Za-z0-9_]*", m.group(1)) if m else []
declared = re.findall(r"^theorem (\w+_satisfiable)\b", session, re.M)
if len(listed) != 13:
    wrong.append(f"the coverage theorem names {len(listed)} witnesses, expected 13: {listed}")
for d in declared:
    if d not in listed and d != "all_thirteen_contracts_satisfiable":
        wrong.append(f"witness {d} is declared but the coverage theorem does not name it")
for w in listed:
    t = once(session, f"theorem {w} :", f"theorem {w}_removed :", f"remove {w}")
    if t is not None:
        refused(f"remove-witness-{w}", t, f"Unknown identifier `{w}`")

# The whole proof is replaced, so that what is refused is the law and not the shape of the proof
# script: a pop that returns and leaves the vector unchanged cannot give `w.val = v.val.dropLast`.
POP_OLD = """  refine ⟨Tacenta.UnitSatisfiabilityJoint.popImpl, ?_, ?_⟩
  · exact fun T v => Tacenta.UnitSatisfiabilityJoint.popImpl_ok v
  · intro T v hv
    simp only [Tacenta.UnitSatisfiabilityJoint.popImpl, dif_neg hv]
    exact ⟨_, _, rfl, rfl⟩
"""
POP_NEW = """  refine ⟨(fun {_} v => ok (none, v)), fun T v => ⟨_, rfl⟩, ?_⟩
  intro T v hv
  exact ⟨_, _, rfl, rfl⟩
"""
t = once(session, POP_OLD, POP_NEW, "pop no-op")
if t is not None:
    refused("pop-witness-is-the-no-op", t, "dropLast")

# -------------------------------------------------------------------- model
passes("joint-unmodified", joint)
# `all_shapes_are_predicates` collects the `_is` bridges; one left out of it is not noticed by the build
bridges = set(re.findall(r"^theorem (\w+_is)\b", joint, re.M)) - {"DecoderNewTotal_is"}
agg = re.search(r"theorem all_shapes_are_predicates :.*?:=\s*⟨(.*?)⟩\s*\n", joint, re.S)
named = set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", agg.group(1))) if agg else set()
for b in sorted(bridges - named):
    wrong.append(f"bridge {b} is declared but all_shapes_are_predicates does not name it")

FLOOR_OLD = """  else ok (Usize.ofNatCore ((a.val + b.val - 1) / b.val) (by
    have ha : a.val < 2 ^ UScalarTy.Usize.numBits := a.hBounds
    have hb : 0 < b.val := Nat.pos_of_ne_zero h
    have : (a.val + b.val - 1) / b.val < a.val + 1 := by
      rw [Nat.div_lt_iff_lt_mul hb]
      have h1 : a.val ≤ a.val * b.val := Nat.le_mul_of_pos_right _ hb
      have h2 : (a.val + 1) * b.val = a.val * b.val + b.val := by ring
      omega
    omega))
"""
FLOOR_NEW = """  else ok (Usize.ofNatCore (a.val / b.val) (by
    have ha : a.val < 2 ^ UScalarTy.Usize.numBits := a.hBounds
    exact lt_of_le_of_lt (Nat.div_le_self _ _) ha))
"""
controls = [
    ("model-delete-range-full-witness",
     "theorem model_RangeFullIndex : RangeFullIndexShape Interp.model := fun _ => rfl\n", "",
     "model_RangeFullIndex"),
    ("model-range-full-forgets-its-slice",
     "rangeFullIndex _ s := ok s\n  divCeil", "rangeFullIndex _ _ := ok (Slice.new _)\n  divCeil",
     "Type mismatch"),
    ("model-zeroizing-deref-fails", "zDeref _ z := ok z", "zDeref _ _ := fail Error.panic", "Application type mismatch"),
    ("model-option-clone-drops-content",
     "optionClone inst o := optionCloneImpl inst o", "optionClone _ _ := ok none", "unsolved goals"),
    # the model's header is fixed at 0 by its witness; the cap itself is held by `badCap_refutes`
    ("model-header-differs-from-its-witness", "HEADER_LEN := ok 0#usize", "HEADER_LEN := ok 5000#usize", "Application type mismatch"),
    ("model-pop-is-the-no-op", "vecPop _ v := popImpl v", "vecPop _ v := ok (none, v)", "Type mismatch"),
    ("model-truncate-fails", "vecTruncate _ v n := truncateImpl v n",
     "vecTruncate _ _ _ := fail Error.panic", "Application type mismatch"),
    ("model-as-mut-fails", "optionAsMut o := ok (o, fun x => x)",
     "optionAsMut _ := fail Error.panic", "Type mismatch"),
    # a floor division whose own bound proof is fine, so the refusal is at `divCeilImpl_value`
    ("model-div-ceil-floors", FLOOR_OLD, FLOOR_NEW, "unsolved goals"),
    # bridges: one constant changed, so the shape is not the predicate
    ("bridge-ct1-cap-4095",
     "def Ct1LenShape (I : Interp) : Prop := ∃ v : Usize, I.CT1_LEN = ok v ∧ v.val ≤ 4096",
     "def Ct1LenShape (I : Interp) : Prop := ∃ v : Usize, I.CT1_LEN = ok v ∧ v.val ≤ 4095",
     "Type mismatch"),
    ("bridge-option-clone-drops-its-premise",
     "    (∀ x, o = some x → inst.clone x ⦃ fun y => y = x ⦄) →\n    I.optionClone inst o ⦃ fun o' => o' = o ⦄",
     "    I.optionClone inst o ⦃ fun o' => o' = o ⦄", "Type mismatch"),
    ("bridge-hkdf-bound-8161",
     "N.val ≤ 8160 → ∃ r, I.hkdfSha256", "N.val ≤ 8161 → ∃ r, I.hkdfSha256", "Type mismatch"),
    ("bridge-div-ceil-value-off-by-one",
     "∀ a : Usize, ∃ r, I.divCeil a 32#usize = ok r ∧ r.val = (a.val + 31) / 32",
     "∀ a : Usize, ∃ r, I.divCeil a 32#usize = ok r ∧ r.val = (a.val + 30) / 32", "Type mismatch"),
    # repacking: a field of a record left out of both parts
    ("parts-drop-range-full-from-the-braid-send-axiom-part",
     "  arrayZeroize : ArrayZeroizeShape I\n  rangeFullIndex : RangeFullIndexShape I\n\nstructure BraidSendDefined",
     "  arrayZeroize : ArrayZeroizeShape I\n\nstructure BraidSendDefined", "Invalid `⟨...⟩` notation"),
    ("parts-drop-div-ceil-value-from-the-responder-axiom-part",
     "  vecPop : VecPopShape I\n  divCeilValue : DivCeilValueShape I\n",
     "  vecPop : VecPopShape I\n", "Invalid `⟨...⟩` notation"),
]
for name, old, new, reason in controls:
    t = once(joint, old, new, name)
    if t is not None:
        refused(name, t, reason)

# ------------------------------------------------------------------ records
passes("records-unmodified", records)
for name, old, new, reason in [
    ("records-ratchet-laws-without-as-mut",
     "  asMut := l.asMut\n  blanketU32 := l.blanketU32\n", "  blanketU32 := l.blanketU32\n",
     "Fields missing: `asMut`"),
    ("records-base-satisfiable-without-the-laws",
     "      derivedKeys := ⟨model_ZeroizingModel DerivedZ⟩\n      laws := model_StdLaws }⟩\n\n/-- The same interpretation",
     "      derivedKeys := ⟨model_ZeroizingModel DerivedZ⟩ }⟩\n\n/-- The same interpretation",
     "Fields missing: `laws`"),
]:
    t = once(records, old, new, name)
    if t is not None:
        refused(name, t, reason)

# -------------------------------------------------------------------- audit
EXPECT = [
    "Interp: no uninterpreted unit axiom in any field type",
    "Interp.real interprets exactly the 48 unit axioms reached by the records",
]
for s, n in [("BraidSendAxiom", 11), ("TripleSendAxiom", 5), ("EncryptAxiom", 5),
             ("BraidReceiveAxiom", 16), ("TripleReceiveAxiom", 7), ("DecryptAxiom", 7),
             ("InitiatorAxiom", 14), ("ResponderAxiom", 7), ("StdLaws", 5), ("FaithfulShape", 6)]:
    EXPECT.append(f"Tacenta.UnitSatisfiabilityJoint.{s}: {n} fields, none mentions a unit axiom or translated function outside an Interp field")
for s, n in [("BraidSendDefined", 4), ("TripleSendDefined", 3), ("EncryptDefined", 2),
             ("BraidReceiveDefined", 6), ("TripleReceiveDefined", 5), ("DecryptDefined", 2),
             ("InitiatorDefined", 1), ("ResponderDefined", 2)]:
    EXPECT.append(f"Tacenta.UnitSatisfiabilityJoint.{s}: {n} fields, each mentions a translated function")

passes("audit-unmodified", joint + "\n" + audit, EXPECT)

# 1. an axiom the interpretation covers but no record reaches
t = joint
for old, new in [
    ("  divCeil : Usize → Usize → Result Usize\n",
     "  divCeil : Usize → Usize → Result Usize\n  saturatingMul : Usize → Usize → Result Usize\n"),
    ("  divCeil := core.num.Usize.div_ceil\n",
     "  divCeil := core.num.Usize.div_ceil\n  saturatingMul := core.num.Usize.saturating_mul\n"),
    ("  divCeil a b := divCeilImpl a b\n",
     "  divCeil a b := divCeilImpl a b\n  saturatingMul a _ := ok a\n"),
]:
    t = once(t, old, new, "extra interpreted axiom") if t else None
if t:
    refused("audit-an-interpreted-axiom-no-record-reaches", t + "\n" + audit,
            "axioms interpreted but not reached by the records")

# 2. an axiom a record reaches that the interpretation leaves out (in the audit's start list)
a = once(audit, "  Tacenta.SessionUnitT1.DerivedKeysModel\n#audit_axiom_part",
         "  Tacenta.SessionUnitT1.DerivedKeysModel Tacenta.UnitLifecycleT1.XeddsaSignTotal\n#audit_axiom_part",
         "audit start list")
if a:
    refused("audit-a-reached-axiom-the-interpretation-omits", joint + "\n" + a,
            "axioms reached by the records but not interpreted")

# 3. a shape that names a real function through a beta-redex
t = once(joint, "def HmacShape (I : Interp) : Prop := ∀ (a b : Slice U8), ∃ r, I.hmacSha256 a b = ok r",
         "def HmacShape (I : Interp) : Prop :=\n  (fun (_ : Result (Array U8 32#usize)) => ∀ (a b : Slice U8), ∃ r, I.hmacSha256 a b = ok r)\n    (tacenta_kdf.hmac_sha256 (Slice.new U8) (Slice.new U8))",
         "beta-redex")
if t:
    refused("audit-a-shape-names-a-real-function", t + "\n" + audit, "a field mentions unit axioms")

# 4. an axiom part that names a translated function
t = once(joint, "structure TripleSendAxiom (I : Interp) : Prop where",
         "def AuditDummy (I : Interp) (_f : tacenta_spqr.Direction → Result tacenta_spqr.Direction) : Prop :=\n  SpqrZeroizeShape I\n\nstructure TripleSendAxiom (I : Interp) : Prop where",
         "translated function (1)")
if t:
    t = once(t, "  zeroize : SpqrZeroizeShape I\n  vecRetain : VecRetainAxiomShape I\n  optionClone : OptionCloneShape I\n\nstructure TripleSendDefined",
             "  zeroize : AuditDummy I tacenta_spqr.Direction.Insts.CoreCloneClone.clone\n  vecRetain : VecRetainAxiomShape I\n  optionClone : OptionCloneShape I\n\nstructure TripleSendDefined",
             "translated function (2)")
if t:
    refused("audit-an-axiom-part-names-a-translated-function", t + "\n" + audit,
            "or translated functions")

# 7. a field of `Interp` whose type names a real opaque type, so `Interp` is not an interpretation of it
t = joint
for old, new in [
    ("  divCeil : Usize → Usize → Result Usize\n\n/-- The real constants",
     "  divCeil : Usize → Usize → Result Usize\n  phantom : List tacenta_kem.IncrementalKeyPair\n\n/-- The real constants"),
    ("  divCeil := core.num.Usize.div_ceil\n", "  divCeil := core.num.Usize.div_ceil\n  phantom := []\n"),
    ("  divCeil a b := divCeilImpl a b\n", "  divCeil a b := divCeilImpl a b\n  phantom := []\n"),
]:
    t = once(t, old, new, "phantom field") if t else None
if t:
    refused("audit-an-interp-field-names-a-real-type", t + "\n" + audit,
            "Interp mentions uninterpreted unit axioms")

# 5 and 6. each command must refuse the wrong kind of structure
a = once(audit, "#audit_defined_part Tacenta.UnitSatisfiabilityJoint.BraidSendDefined",
         "#audit_defined_part Tacenta.UnitSatisfiabilityJoint.BraidSendAxiom\n#audit_defined_part Tacenta.UnitSatisfiabilityJoint.BraidSendDefined",
         "defined command")
if a:
    refused("audit-a-defined-part-with-an-axiom-level-field", joint + "\n" + a,
            "a field mentions no translated function")
a = once(audit, "#audit_axiom_part Tacenta.UnitSatisfiabilityJoint.BraidSendAxiom",
         "#audit_axiom_part Tacenta.UnitSatisfiabilityJoint.BraidSendDefined\n#audit_axiom_part Tacenta.UnitSatisfiabilityJoint.BraidSendAxiom",
         "axiom command")
if a:
    refused("audit-an-axiom-part-with-a-translated-function", joint + "\n" + a,
            "or translated functions")

# ------------------------------------------------------------------- oracle
# The clauses of `OracleOf` decided jointly (`UnitOracleShape.lean` to `UnitOracleJoint.lean`). Each
# witness removed in turn must be refused where it is used; nine primitives and the private-key view of
# the joint model, changed one at a time, must each be refused by the result, the lemma or the law of
# the model that needs it; a bridge or a record changed by one field must be refused. A model mutation is checked on one file made of the
# model module and the cluster module that uses it, with their pin sections removed, so that what
# refuses is the theorem and not a pin.
def module(name):
    return open(os.path.join(base, name + ".lean")).read()


def body_of(text):
    """The module text without its import lines and without its pin section."""
    if "\n/-! ## Pins" in text:
        text = text[: text.index("\n/-! ## Pins")]
    return "\n".join(l for l in text.splitlines() if not l.startswith("import ")) + "\n"


def nopins(text):
    if "\n/-! ## Pins" in text:
        text = text[: text.index("\n/-! ## Pins")]
    return text + "\n"


o_shape, o_model, o_dh = module("UnitOracleShape"), module("UnitOracleModel"), module("UnitOracleDh")
o_aead, o_ks, o_joint = module("UnitOracleAead"), module("UnitOracleKemSig"), module("UnitOracleJoint")
for nm, t in [("shape", o_shape), ("model", o_model), ("dh", o_dh), ("aead", o_aead),
              ("kemsig", o_ks), ("joint", o_joint)]:
    passes(f"oracle-{nm}-unmodified", t)

# witnesses: every model witness is named by `modelO_axiomBase` or `modelO_laws`, and each cluster
# lemma by the cluster theorem; each removed in turn is refused as an unknown identifier.
m_base = re.search(r"theorem modelO_axiomBase : AxiomBase M byteRng where(.*?)\n\n", o_model, re.S)
m_laws = re.search(r"theorem modelO_laws :.*?:=\s*⟨(.*?)⟩", o_model, re.S)
m_std = re.search(r"theorem modelO_StdLaws : StdLaws M :=(.*?)\n\n", o_model, re.S)
named = set(re.findall(r"\b(?:modelO_\w+|byteRng_total)\b", " ".join(
    m.group(1) for m in (m_base, m_laws, m_std) if m)))
declared = set(re.findall(r"^(?:theorem|def) ((?:modelO_\w+|byteRng_total))\b", o_model, re.M))
for d in sorted(declared - named - {"modelO_axiomBase", "modelO_laws"}):
    wrong.append(f"model witness {d} is declared but modelO_axiomBase, modelO_laws and modelO_StdLaws do not name it")
if len(named) < 18:
    wrong.append(f"the model aggregates name {len(named)} witnesses, expected at least 18: {sorted(named)}")
for w in sorted(named):
    kw = "def" if re.search(rf"^def {w}\b", o_model, re.M) else "theorem"
    t = once(o_model, f"{kw} {w} ", f"{kw} {w}_removed ", f"remove {w}")
    if t is not None:
        refused(f"oracle-remove-model-witness-{w}", t, f"Unknown identifier `{w}`")
for text, names in [
    (o_dh, ["model_dhPublicClause", "model_dhAgreeClause", "model_identityValidClause",
            "oracleM_dhPublic", "oracleM_dhAgree", "oracleM_identityValid", "xor32_comm",
            "xor32_self"]),
    (o_aead, ["model_aeadSealClause", "model_aeadOpenClause", "oracleM_aeadSeal",
              "oracleM_aeadOpen", "openModel_zero_cons", "openModel_nil"]),
    (o_ks, ["model_kemDecapsulateClause", "model_sigVerifyClause", "model_kemGuardedClause",
            "kemGuardedClause_of_law", "never_encapsulating_meets_kemClauses",
            "never_encapsulating_fails_guarded", "oracleM_kemDecaps", "oracleM_sigVerify",
            "oracleM_sigSign", "kemModelValid_key1568", "byteTrace_oneDrawState", "map_u8_ofByte",
            "oracleM_kemEncaps", "oracleM_kemValid", "u8_ofByte"]),
    (o_joint, ["modelO_oracleLaws", "oracleOfShape_of_oracleLaws", "oracleOfGuarded_of_laws",
               "oracleOf_joint_model"]),
    (o_shape, ["liftView_spec", "isValidIdentityKeyOf_total", "arrayOf_injective",
               "sliceOf_injective"]),
]:
    # the list is complete: every theorem of the module is on it or carries an axiom pin
    code = re.sub(r"/-.*?-/", "", text, flags=re.S)
    unlisted = sorted(t for t in re.findall(r"^theorem (\w+)", code, re.M)
                      if t not in names and not re.search(rf"#print axioms \S+\.{t}\n", text))
    for t in unlisted:
        wrong.append(f"theorem {t} has neither an axiom pin nor a removal case in the oracle group")
    for w in names:
        t = once(text, f"theorem {w} ", f"theorem {w}_removed ", f"remove {w}")
        if t is not None:
            refused(f"oracle-remove-witness-{w}", t, f"Unknown identifier `{w}`")

# the toy primitives made degenerate, one at a time
ks_body = body_of(o_ks)
dh_body = body_of(o_dh)
aead_body = body_of(o_aead)
for name, old, new, rest, reason in [
    ("oracle-model-verify-accepts-every-signature",
     "  ok (if s.val.take 32 = pk.val then .Ok () else .Err ())", "  ok (.Ok ())",
     dh_body + ks_body, "Could not split"),
    ("oracle-model-sign-forgets-the-secret",
     "  ⟨sk.val ++ List.replicate 32 0#u8, by simp [sk.property]⟩",
     "  ⟨List.replicate 64 0#u8, by simp⟩", dh_body + ks_body, "unsolved goals"),
    ("oracle-model-decapsulation-accepts-every-length",
     "  ok (if h : c.val.length = 32 then .Ok ⟨c.val, by simpa using h⟩ else .Err ())",
     "  ok (.Ok (Array.repeat 32#usize 0#u8))", dh_body + ks_body, "unsolved goals"),
    ("oracle-model-open-accepts-everything",
     "    if x = 0#u8 then .Ok ⟨rest, by have := c.property; rw [h] at this; simp at this; omega⟩\n    else .Err ()\n  | [] => .Err ()",
     "    .Ok ⟨rest, by have := c.property; rw [h] at this; simp at this; omega⟩\n  | [] => .Ok (alloc.vec.Vec.new U8)",
     aead_body, "Tactic `rfl` failed"),
    ("oracle-model-seal-drops-the-tag",
     "  if h : p.val.length + 1 ≤ Usize.max then ⟨0#u8 :: p.val, by simp; omega⟩\n  else ⟨p.val, p.property⟩",
     "  ⟨p.val, p.property⟩", aead_body, "Could not split"),
    ("oracle-model-agreement-never-refuses",
     "  if (xor32 k p).val = zero32.val then none else some (xor32 k p)", "  some (xor32 k p)",
     dh_body, "unsolved goals"),
    ("oracle-model-prime-order-accepts-every-key",
     "dhIsPrimeOrderPublic := fun p => ok (decide (p.val ≠ zero32.val))",
     "dhIsPrimeOrderPublic := fun _ => ok true", dh_body, "unsolved goals"),
    ("oracle-model-encapsulation-never-draws",
     "        ok (core.result.Result.Ok (kemModelE (sliceOf publicKey) (sliceOf m)), rng'))\n  else ok (.Err (), rng)",
     "        ok (core.result.Result.Ok (kemModelE (sliceOf publicKey) (sliceOf m)), rng))\n  else ok (.Err (), rng)",
     "", "Type mismatch"),
    ("oracle-model-generate-draws-nothing",
     "    ikpGenerate := fun rc _ rng => do\n      let (rng', _) ← rc.fill_bytes rng zeros64\n      ok (.Ok (), rng')",
     "    ikpGenerate := fun _ _ rng => ok (.Ok (), rng)", "", "'show' tactic failed"),
    ("oracle-model-private-view-forgets-the-key",
     "def dhM : DhViewOf M := ⟨arrayOf, arrayOf⟩", "def dhM : DhViewOf M := ⟨fun _ => [], arrayOf⟩",
     "", "Application type mismatch"),
]:
    t = once(nopins(o_model), old, new, name)
    if t is not None:
        refused(name, t + rest, reason)

# the bridges and the records, one field changed
for name, text, old, new, reason in [
    ("oracle-bridge-shape-field-views-the-secret-twice", o_shape,
     "      result.map arrayOf = oracle.dhAgree (dh.privateKey secret) (dh.publicKey publicKey)\n  identityValid : ∀ publicKey,\n    ∃ result,\n      isValidIdentityKeyOf",
     "      result.map arrayOf = oracle.dhAgree (dh.privateKey secret) (dh.privateKey secret)\n  identityValid : ∀ publicKey,\n    ∃ result,\n      isValidIdentityKeyOf",
     "Application type mismatch"),
    ("oracle-bridge-identity-body-differs", o_shape,
     "  let b ← isCanonicalKeyOf I pk\n  if b then I.dhIsPrimeOrderPublic pk else ok false",
     "  let b ← isCanonicalKeyOf I pk\n  if b then I.dhIsPrimeOrderPublic pk else ok true",
     "Not a definitional equality"),
    ("oracle-laws-drop-a-view-law", o_joint,
     "  dhView : DhViewInjective dh\n  kemView : KemViewInjective kem",
     "  dhView : DhViewInjective dh", "Invalid field `kemView`"),
    ("oracle-guarded-record-drops-its-guard", o_ks,
     "  kemEncapsulateGuarded : ∀ publicKey rng draw rest,\n    oracle.kemValid (sliceOf publicKey) = true →\n    trace rng = draw :: rest →",
     "  kemEncapsulateGuarded : ∀ publicKey rng draw rest,\n    trace rng = draw :: rest →",
     "Application type mismatch"),
]:
    t = once(text, old, new, name)
    if t is not None:
        refused(name, t, reason)

if wrong:
    sys.stderr.write("session-satisfiability negatives: %d of %d cases gave the wrong result\n" % (len(wrong), cases))
    for w in wrong:
        sys.stderr.write("  WRONG  " + w + "\n")
    sys.exit(1)
print("session-satisfiability negatives: %d cases gave the expected result "
      "(%d unmodified inputs accepted, %d mutations or wrong inputs refused with the stated message)"
      % (cases, accepted, cases - accepted))
PY
