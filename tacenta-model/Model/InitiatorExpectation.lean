/-
Model.InitiatorExpectation: the initiator's expectation, and the order in which
the initiator makes its checks.

Written from tacenta-spec/protocol/session-establishment.md, "Records,
expectations and attribution" (The initiator) and "Sending the initial message",
with `Model.IdentityRecords` for the classification and the lookup it is built on.

**The initiator establishes only with an expectation**, in one of two forms:
- *known*: the record of the contact she means to reach. The record is
  non-empty.
- *first contact*: for a peer she holds no record for. It carries all her
  records.

**The order** (the pages' wording, "after the bundle's presence and
canonical-key checks, and before the identity-key rule, the signature checks,
the KEM prekey's input checks and anything that draws randomness or computes an
agreement"):
1. an expectation that is malformed is refused (`MalformedRecord`), before any
   check of Sending the initial message;
2. the bundle's presence check and its canonical-key checks;
3. the check of the bundle's identity key against the expectation, which
   applies the identity-key rule to the key first;
4. the rest: the identity-key rule, both signatures, the KEM prekey's input
   checks, randomness and the agreements. That is `Model.Lifecycle.establishInitiator`,
   unchanged, which the step calls with the bundle's own identity key as the key
   it expects, so its own comparison cannot fire (`leaf_never_unexpected`) and its
   own rule check cannot fire after step 3 (`rule_never_fires_after_expectation`).

Attribution of the session, which the pages place after all of this, is not
modelled here: it is `Model.IdentityRecords.lookupWith` applied to the session's
peer identity key.

**The leaf is not edited.** `Model.Lifecycle.establishInitiator` is the model's
internal step and is the pinned-first function it has always been: it compares the
bundle's identity key with an expected one before the presence and canonical
checks. It is not the specification's initiator, which is
`establishInitiatorExpecting` below. Editing the leaf would rebuild every module of
the translation that imports it.

**What is and is not established here.** These are definitions to run and
properties of the definitions (the order of the checks, that a refusal draws
nothing, that the leaf's own comparison and rule check are redundant after the
expectation). Whether `tacenta-core` makes these checks in this order is the
vectors' question. The rule is `oracle.identityValid`, as the leaf takes it; its
agreement with `Model.IdentityKey.valid` is the lifecycle model's, pinned by the
identity-key vectors.
-/
import Model.IdentityRecords
import Model.Lifecycle

namespace Model.InitiatorExpectation

open Model.IdentityRecords
open Model.Lifecycle (Oracle Identity Bundle Session absentId establishInitiator)

/-- An initiator's expectation, over contacts of type `C`. -/
inductive Expectation (C : Type) where
  /-- The record of the contact she means to reach, which she selects herself. -/
  | known (record : Record)
  /-- All her records; for a peer she holds no record for. -/
  | firstContact (records : List (C × Record))

/-- She refuses an expectation as a malformed record when it holds a non-canonical
    key, in the record under *known* or in any of her records under *first contact*,
    or when it is *known* with a record whose two sets are both empty. -/
def Expectation.malformed {C : Type} : Expectation C → Bool
  | .known r => !r.wellFormed || !r.holds
  | .firstContact rs => !(rs.all fun cr => cr.2.wellFormed)

/-- What the initiator can refuse before the rest of establishment, and what she
    reports after it. The leaf's refusals are carried as they are. -/
inductive Refusal where
  /-- A malformed expectation: a non-canonical key in a record, or *known* with a
      record that holds nothing. -/
  | malformedRecord
  /-- The bundle's key is not the expectation's (*new* under *known*; a contact's
      or ambiguous under *first contact*). -/
  | unexpectedIdentity
  /-- The bundle's key is *retired* (under *known*), or a retired key (under
      *first contact*). -/
  | retiredIdentity
  /-- The bundle's identity key is not the canonical encoding of a curve public
      key. -/
  | decodeFailure
  /-- The bundle's identity key is canonical but not an identity key. -/
  | invalidIdentityKey
  /-- A refusal of the unchanged lifecycle step, which includes the presence and
      canonical-key refusals that precede the expectation. -/
  | bundle (reason : Model.Lifecycle.Refusal)
  deriving Repr, DecidableEq, Inhabited

def Refusal.ofKey : KeyRefusal → Refusal
  | .decodeFailure => .decodeFailure
  | .invalidIdentityKey => .invalidIdentityKey

/-- The check of the bundle's identity key `ikb` against the expectation, under the
    rule `rule`; `none` when the key goes on.
    - *known*: classify it against the record. *Retired* is a retired identity,
      *new* an unexpected identity, *same* goes on.
    - *first contact*: look it up. A contact's key or an ambiguous one is an
      unexpected identity (even when it is also retired for another contact), a
      retired key (*same* for no contact) a retired identity, an unattributed key
      goes on.
    Either way the identity-key rule is applied to the key first, by the
    classification and by the lookup. -/
def checkWith {C : Type} (rule : Key → Bool) (exp : Expectation C) (ikb : Key) :
    Option Refusal :=
  match exp with
  | .known r =>
    match classifyWith rule ikb r with
    | .error .decodeFailure => some .decodeFailure
    | .error .invalidIdentityKey => some .invalidIdentityKey
    | .error .malformedRecord => some .malformedRecord
    | .ok .retired => some .retiredIdentity
    | .ok .new => some .unexpectedIdentity
    | .ok .same => none
  | .firstContact rs =>
    match lookupWith rule ikb rs with
    | .error e => some (Refusal.ofKey e)
    | .ok res =>
      match res.attribution with
      | .contact _ => some .unexpectedIdentity
      | .ambiguous _ => some .unexpectedIdentity
      | .retiredKey _ => some .retiredIdentity
      | .unattributed => none

/-- The outcome of the initiator's establishment as far as this module goes: the
    result and the oracle that is left, so that "draws nothing" is a statement
    about the oracle. -/
structure Step where
  result : Except Refusal Session
  oracle : Oracle

/-- The refusal a step ended in, if any. -/
def Step.refusal (s : Step) : Option Refusal :=
  match s.result with
  | .error r => some r
  | .ok _ => none

/-- The leaf's result in this module's refusal type. -/
def liftResult : Except Model.Lifecycle.Refusal Session → Except Refusal Session
  | .ok s => .ok s
  | .error r => .error (.bundle r)

/-- The specification's initiator establishment, up to and including the step the
    unchanged lifecycle model takes. The order is the pages': a malformed
    expectation; the presence check; the canonical-key checks; the expectation,
    with the rule first; then `Model.Lifecycle.establishInitiator`, whose own
    comparison is made against the bundle's own key. The presence and canonical
    tests are the leaf's, written out. -/
def establishInitiatorExpecting {C : Type} (oracle : Oracle) (identity : Identity)
    (bundle : Bundle) (exp : Expectation C) : Step :=
  if exp.malformed then { result := .error .malformedRecord, oracle }
  else if bundle.oneTimePrekey.isSome != (bundle.oneTimeId != absentId) then
    { result := .error (.bundle .inconsistentBundle), oracle }
  else if !(Model.Messages.canonicalKey bundle.identityKey)
      || !(Model.Messages.canonicalKey bundle.signedPrekey)
      || !(bundle.oneTimePrekey.all Model.Messages.canonicalKey) then
    { result := .error (.bundle .badEncoding), oracle }
  else
    match checkWith oracle.identityValid exp bundle.identityKey with
    | some r => { result := .error r, oracle }
    | none =>
      let leaf := establishInitiator oracle identity bundle bundle.identityKey
      { result := liftResult leaf.result, oracle := leaf.oracle }

/-! ## The expectation -/

/-- *Known* with a record that holds nothing is malformed: a contact she holds no
    record for is reached under *first contact*. -/
theorem known_empty_malformed {C : Type} :
    (Expectation.known (C := C) ⟨[], []⟩).malformed = true := by
  simp [Expectation.malformed, Record.holds]

/-- A non-canonical key in a record is a malformed expectation, under *known*. -/
theorem known_noncanonical_malformed {C : Type} (r : Record) (h : r.wellFormed = false) :
    (Expectation.known (C := C) r).malformed = true := by
  simp [Expectation.malformed, h]

/-- A non-canonical key in any of her records is a malformed expectation under
    *first contact*. -/
theorem firstContact_noncanonical_malformed {C : Type} (rs : List (C × Record)) (c : C)
    (r : Record) (hm : (c, r) ∈ rs) (h : r.wellFormed = false) :
    (Expectation.firstContact rs).malformed = true := by
  simp only [Expectation.malformed, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_false]
  exact ⟨(c, r), hm, by simp [h]⟩

/-- *First contact* with no records is a well-formed expectation. -/
theorem firstContact_nil_not_malformed {C : Type} :
    (Expectation.firstContact (C := C) []).malformed = false := by
  simp [Expectation.malformed]

/-- A key that is not an identity key is refused as such by the expectation's check,
    whatever the expectation holds, under either form. -/
theorem check_key_refusal {C : Type} (rule : Key → Bool) (exp : Expectation C) (ikb : Key)
    (e : KeyRefusal) (h : keyRefusalWith rule ikb = some e) :
    checkWith rule exp ikb = some (Refusal.ofKey e) := by
  cases exp with
  | known r => cases e <;> simp [checkWith, classify_key_refusal rule ikb r _ h, ClassifyRefusal.ofKey,
      Refusal.ofKey]
  | firstContact rs => simp [checkWith, lookup_key_refusal rule ikb rs e h]

/-- The expectation's check never reports a malformed record for an expectation
    that is not malformed: that refusal belongs to the first step. -/
theorem check_not_malformed {C : Type} (rule : Key → Bool) (exp : Expectation C) (ikb : Key)
    (h : exp.malformed = false) : checkWith rule exp ikb ≠ some .malformedRecord := by
  cases exp with
  | known r =>
    have hwf : r.wellFormed = true := by
      simp only [Expectation.malformed, Bool.or_eq_false_iff, Bool.not_eq_false'] at h
      exact h.1
    have hne := classify_wellFormed_not_malformed rule ikb r hwf
    cases hc : classifyWith rule ikb r with
    | error e => cases e <;> simp_all [checkWith]
    | ok c => cases c <;> simp [checkWith, hc]
  | firstContact rs =>
    cases hl : lookupWith rule ikb rs with
    | error e => cases e <;> simp [checkWith, hl, Refusal.ofKey]
    | ok res =>
      cases ha : res.attribution <;> simp [checkWith, hl, ha]

/-- Under *known*: the key goes on exactly when it is an identity key, the record is
    well formed, and the key is in the current set and not in the retired set. -/
theorem check_known_none_iff {C : Type} (rule : Key → Bool) (r : Record) (ikb : Key) :
    checkWith rule (Expectation.known (C := C) r) ikb = none ↔
      keyRefusalWith rule ikb = none ∧ r.wellFormed = true ∧ ikb ∉ r.retired ∧
        ikb ∈ r.current := by
  unfold checkWith classifyWith
  cases hk : keyRefusalWith rule ikb with
  | some e => cases e <;> simp [ClassifyRefusal.ofKey]
  | none =>
    by_cases hw : r.wellFormed = true
    · by_cases hr : ikb ∈ r.retired <;> by_cases hc : ikb ∈ r.current <;> simp [hw, hr, hc]
    · simp at hw; simp [hw]

/-- Under *known*, *retired* is a retired identity and *new* an unexpected one. -/
theorem check_known_retired {C : Type} (rule : Key → Bool) (r : Record) (ikb : Key)
    (hk : keyRefusalWith rule ikb = none) (hw : r.wellFormed = true) (h : ikb ∈ r.retired) :
    checkWith rule (Expectation.known (C := C) r) ikb = some .retiredIdentity := by
  simp [checkWith, classify_retired rule ikb r hk hw h]

theorem check_known_new {C : Type} (rule : Key → Bool) (r : Record) (ikb : Key)
    (hk : keyRefusalWith rule ikb = none) (hw : r.wellFormed = true) (hr : ikb ∉ r.retired)
    (hc : ikb ∉ r.current) :
    checkWith rule (Expectation.known (C := C) r) ikb = some .unexpectedIdentity := by
  simp [checkWith, classify_new rule ikb r hk hw hr hc]

/-- Under *first contact*, with an identity key: the key goes on exactly when the
    lookup finds it unattributed, i.e. *same* and *retired* for no contact. -/
theorem check_firstContact_none_iff {C : Type} (rule : Key → Bool) (rs : List (C × Record))
    (ikb : Key) :
    checkWith rule (Expectation.firstContact rs) ikb = none ↔
      keyRefusalWith rule ikb = none ∧ sameFor rule ikb rs = [] ∧ retiredFor rule ikb rs = [] := by
  unfold checkWith lookupWith
  cases hk : keyRefusalWith rule ikb with
  | some e => cases e <;> simp [Refusal.ofKey]
  | none =>
    dsimp only
    cases hs : sameFor rule ikb rs with
    | nil =>
      cases hr : retiredFor rule ikb rs with
      | nil => simp [attributionOf]
      | cons a t => simp [attributionOf]
    | cons a t => cases t <;> simp [attributionOf]

/-- Under *first contact*, a key that is *same* for a contact, or for several, is an
    unexpected identity, even when it is also *retired* for another contact. -/
theorem check_firstContact_unexpected {C : Type} (rule : Key → Bool) (rs : List (C × Record))
    (ikb : Key) (hk : keyRefusalWith rule ikb = none) (hs : sameFor rule ikb rs ≠ []) :
    checkWith rule (Expectation.firstContact rs) ikb = some .unexpectedIdentity := by
  unfold checkWith lookupWith
  simp only [hk]
  cases hl : sameFor rule ikb rs with
  | nil => exact absurd hl hs
  | cons a t => cases t <;> simp [attributionOf]

/-- Under *first contact*, a key that is *same* for no contact and *retired* for some
    is a retired identity. -/
theorem check_firstContact_retired {C : Type} (rule : Key → Bool) (rs : List (C × Record))
    (ikb : Key) (hk : keyRefusalWith rule ikb = none) (hs : sameFor rule ikb rs = [])
    (hr : retiredFor rule ikb rs ≠ []) :
    checkWith rule (Expectation.firstContact rs) ikb = some .retiredIdentity := by
  unfold checkWith lookupWith
  simp only [hk, hs]
  cases hl : retiredFor rule ikb rs with
  | nil => exact absurd hl hr
  | cons a t => simp [attributionOf]

/-- *First contact* with no records lets an identity key go on. -/
theorem check_firstContact_nil {C : Type} (rule : Key → Bool) (ikb : Key)
    (hk : keyRefusalWith rule ikb = none) :
    checkWith rule (Expectation.firstContact (C := C) []) ikb = none := by
  simp [checkWith, lookup_nil rule ikb hk]

/-- The expectation's check goes on only for an identity key. -/
theorem check_none_key {C : Type} (rule : Key → Bool) (exp : Expectation C) (ikb : Key)
    (h : checkWith rule exp ikb = none) : keyRefusalWith rule ikb = none := by
  cases hk : keyRefusalWith rule ikb with
  | none => rfl
  | some e => rw [check_key_refusal rule exp ikb e hk] at h; simp at h

/-! ## The order -/

/-- A malformed expectation is refused first, for every bundle, identity and oracle,
    and the oracle is left as it was: no randomness is drawn. -/
theorem malformed_first {C : Type} (oracle : Oracle) (identity : Identity) (bundle : Bundle)
    (exp : Expectation C) (h : exp.malformed = true) :
    establishInitiatorExpecting oracle identity bundle exp =
      { result := .error .malformedRecord, oracle } := by
  simp [establishInitiatorExpecting, h]

/-- A bundle whose one-time prekey and identifier disagree about presence is refused
    for that, ahead of the expectation, whatever the expectation would say of the
    bundle's key. -/
theorem presence_before_expectation {C : Type} (oracle : Oracle) (identity : Identity)
    (bundle : Bundle) (exp : Expectation C) (hm : exp.malformed = false)
    (hp : (bundle.oneTimePrekey.isSome != (bundle.oneTimeId != absentId)) = true) :
    establishInitiatorExpecting oracle identity bundle exp =
      { result := .error (.bundle .inconsistentBundle), oracle } := by
  simp [establishInitiatorExpecting, hm, hp]

/-- A bundle with a non-canonical identity key, signed prekey or one-time prekey is
    refused as a bad encoding, ahead of the expectation. -/
theorem canonical_before_expectation {C : Type} (oracle : Oracle) (identity : Identity)
    (bundle : Bundle) (exp : Expectation C) (hm : exp.malformed = false)
    (hp : bundle.oneTimePrekey.isSome = (bundle.oneTimeId != absentId))
    (hc : (!(Model.Messages.canonicalKey bundle.identityKey)
      || !(Model.Messages.canonicalKey bundle.signedPrekey)
      || !(bundle.oneTimePrekey.all Model.Messages.canonicalKey)) = true) :
    establishInitiatorExpecting oracle identity bundle exp =
      { result := .error (.bundle .badEncoding), oracle } := by
  have hp' : (bundle.oneTimePrekey.isSome != (bundle.oneTimeId != absentId)) = false := by
    simp [hp]
  simp [establishInitiatorExpecting, hm, hp', hc]

/-- A refusal by the expectation is the step's result, with the oracle untouched,
    for a bundle that passed the presence and canonical checks. Nothing is
    verified, drawn or computed for it. -/
theorem expectation_refusal {C : Type} (oracle : Oracle) (identity : Identity)
    (bundle : Bundle) (exp : Expectation C) (r : Refusal) (hm : exp.malformed = false)
    (hp : bundle.oneTimePrekey.isSome = (bundle.oneTimeId != absentId))
    (hc : (!(Model.Messages.canonicalKey bundle.identityKey)
      || !(Model.Messages.canonicalKey bundle.signedPrekey)
      || !(bundle.oneTimePrekey.all Model.Messages.canonicalKey)) = false)
    (hr : checkWith oracle.identityValid exp bundle.identityKey = some r) :
    establishInitiatorExpecting oracle identity bundle exp =
      { result := .error r, oracle } := by
  have hp' : (bundle.oneTimePrekey.isSome != (bundle.oneTimeId != absentId)) = false := by
    simp [hp]
  simp [establishInitiatorExpecting, hm, hp', hc, hr]

/-- A refusal by the expectation holds whatever the signatures, the KEM prekey, the
    agreements or the randomness would have said: two oracles that differ in
    everything but their identity-key rule give the same result. This is what makes
    a bundle with a bad signature, a KEM prekey that fails its input checks, or a
    low-order prekey under a key she refuses a refusal of the key. -/
theorem expectation_refusal_independent {C : Type} (oracle oracle' : Oracle)
    (identity : Identity) (bundle : Bundle) (exp : Expectation C) (r : Refusal)
    (hm : exp.malformed = false)
    (hp : bundle.oneTimePrekey.isSome = (bundle.oneTimeId != absentId))
    (hc : (!(Model.Messages.canonicalKey bundle.identityKey)
      || !(Model.Messages.canonicalKey bundle.signedPrekey)
      || !(bundle.oneTimePrekey.all Model.Messages.canonicalKey)) = false)
    (hv : oracle'.identityValid = oracle.identityValid)
    (hr : checkWith oracle.identityValid exp bundle.identityKey = some r) :
    (establishInitiatorExpecting oracle identity bundle exp).result =
      (establishInitiatorExpecting oracle' identity bundle exp).result := by
  rw [expectation_refusal oracle identity bundle exp r hm hp hc hr,
    expectation_refusal oracle' identity bundle exp r hm hp hc (by rw [hv]; exact hr)]

/-- An expectation refusal, and the rule's refusal that it contains, leave the
    oracle as it was, so the random draws are exactly as before. -/
theorem refusal_keeps_oracle {C : Type} (oracle : Oracle) (identity : Identity)
    (bundle : Bundle) (exp : Expectation C) (r : Refusal) (hm : exp.malformed = false)
    (hp : bundle.oneTimePrekey.isSome = (bundle.oneTimeId != absentId))
    (hc : (!(Model.Messages.canonicalKey bundle.identityKey)
      || !(Model.Messages.canonicalKey bundle.signedPrekey)
      || !(bundle.oneTimePrekey.all Model.Messages.canonicalKey)) = false)
    (hr : checkWith oracle.identityValid exp bundle.identityKey = some r) :
    (establishInitiatorExpecting oracle identity bundle exp).oracle = oracle := by
  rw [expectation_refusal oracle identity bundle exp r hm hp hc hr]

/-- A bundle whose identity key is not an identity key (canonical, but refused by
    the rule) is refused as an invalid identity key, under either form and
    whatever the records hold, provided the expectation is well formed. -/
theorem rule_first {C : Type} (oracle : Oracle) (identity : Identity) (bundle : Bundle)
    (exp : Expectation C) (hm : exp.malformed = false)
    (hp : bundle.oneTimePrekey.isSome = (bundle.oneTimeId != absentId))
    (hc : (!(Model.Messages.canonicalKey bundle.identityKey)
      || !(Model.Messages.canonicalKey bundle.signedPrekey)
      || !(bundle.oneTimePrekey.all Model.Messages.canonicalKey)) = false)
    (hlen : bundle.identityKey.length = 32)
    (hv : oracle.identityValid bundle.identityKey = false) :
    establishInitiatorExpecting oracle identity bundle exp =
      { result := .error .invalidIdentityKey, oracle } := by
  have hcanon : canonicalEncoding bundle.identityKey = true := by
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hc
    simp [canonicalEncoding, hlen, hc.1.1]
  have hk : keyRefusalWith oracle.identityValid bundle.identityKey = some .invalidIdentityKey := by
    simp [keyRefusalWith, hcanon, hv]
  exact expectation_refusal oracle identity bundle exp .invalidIdentityKey hm hp hc
    (by simpa [Refusal.ofKey] using check_key_refusal oracle.identityValid exp _ _ hk)

/-! ## The step the expectation hands to the unchanged lifecycle model -/

/-- The lifecycle model's own comparison cannot fire when the key it expects is the
    bundle's own: the unchanged step never gives `unexpectedIdentity` there. -/
theorem leaf_never_unexpected (oracle : Oracle) (identity : Identity) (bundle : Bundle) :
    (establishInitiator oracle identity bundle bundle.identityKey).result ≠
      .error .unexpectedIdentity := by
  unfold establishInitiator
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  repeat' split
  all_goals (intro h; simp at h)

/-- The lifecycle model's own rule check cannot fire after the expectation: when the
    expectation's check let the key go on, the rule accepted it, and the unchanged
    step, which tests the rule before the signatures, does not refuse the key. The
    check is the rule's own check made earlier, as the pages say. -/
theorem rule_never_fires_after_expectation {C : Type} (oracle : Oracle) (identity : Identity)
    (bundle : Bundle) (exp : Expectation C)
    (hr : checkWith oracle.identityValid exp bundle.identityKey = none) :
    (establishInitiator oracle identity bundle bundle.identityKey).result ≠
      .error (.handshake .invalidIdentityKey) := by
  have hk := (keyRefusalWith_eq_none_iff _ _).mp (check_none_key _ exp _ hr)
  have hv : oracle.identityValid bundle.identityKey = true := hk.2
  unfold establishInitiator
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hv, Bool.not_true]
  repeat' split
  all_goals (intro h; simp at h)

/-- The expectation's own refusals are never the lifecycle step's. -/
theorem checkWith_not_bundle {C : Type} (rule : Key → Bool) (exp : Expectation C) (ikb : Key)
    (r : Refusal) (h : checkWith rule exp ikb = some r) : ∀ x, r ≠ Refusal.bundle x := by
  intro x hx
  subst hx
  cases exp with
  | known rec =>
    cases hc : classifyWith rule ikb rec with
    | error e => cases e <;> simp [checkWith, hc] at h
    | ok c => cases c <;> simp [checkWith, hc] at h
  | firstContact rs =>
    cases hl : lookupWith rule ikb rs with
    | error e => cases e <;> simp [checkWith, hl, Refusal.ofKey] at h
    | ok res => cases ha : res.attribution <;> simp [checkWith, hl, ha] at h

/-- Whatever the expectation holds, a step never ends in the lifecycle step's own
    comparison: `unexpectedIdentity` is only ever the expectation's. -/
theorem step_never_leaf_unexpected {C : Type} (oracle : Oracle) (identity : Identity)
    (bundle : Bundle) (exp : Expectation C) :
    (establishInitiatorExpecting oracle identity bundle exp).refusal ≠
      some (.bundle .unexpectedIdentity) := by
  have hl := leaf_never_unexpected oracle identity bundle
  unfold establishInitiatorExpecting
  repeat' split
  all_goals first
    | (intro h; simp [Step.refusal] at h; done)
    | skip
  · rename_i r hr
    intro h
    simp only [Step.refusal, Option.some.injEq] at h
    exact checkWith_not_bundle _ _ _ r hr _ (by simpa using h)
  · cases hres : (establishInitiator oracle identity bundle bundle.identityKey).result with
    | ok s => simp [Step.refusal, liftResult, hres]
    | error r =>
      intro h
      simp only [hres, Step.refusal, liftResult, Option.some.injEq, Refusal.bundle.injEq] at h
      subst h
      exact hl hres

/-- A step that went past the expectation is the lifecycle step's result and oracle,
    and nothing else. -/
theorem success_is_leaf {C : Type} (oracle : Oracle) (identity : Identity) (bundle : Bundle)
    (exp : Expectation C) (hm : exp.malformed = false)
    (hp : bundle.oneTimePrekey.isSome = (bundle.oneTimeId != absentId))
    (hc : (!(Model.Messages.canonicalKey bundle.identityKey)
      || !(Model.Messages.canonicalKey bundle.signedPrekey)
      || !(bundle.oneTimePrekey.all Model.Messages.canonicalKey)) = false)
    (hr : checkWith oracle.identityValid exp bundle.identityKey = none) :
    establishInitiatorExpecting oracle identity bundle exp =
      { result := liftResult (establishInitiator oracle identity bundle bundle.identityKey).result
        oracle := (establishInitiator oracle identity bundle bundle.identityKey).oracle } := by
  have hp' : (bundle.oneTimePrekey.isSome != (bundle.oneTimeId != absentId)) = false := by
    simp [hp]
  simp [establishInitiatorExpecting, hm, hp', hc, hr]

/-- After the expectation, the lifecycle step's own comparison and rule check are
    redundant: neither ends the step. Together with `rule_first`, the identity-key
    rule is applied to the key once, before anything is spent on the bundle. -/
theorem leaf_key_checks_redundant {C : Type} (oracle : Oracle) (identity : Identity)
    (bundle : Bundle) (exp : Expectation C) (hm : exp.malformed = false)
    (hp : bundle.oneTimePrekey.isSome = (bundle.oneTimeId != absentId))
    (hc : (!(Model.Messages.canonicalKey bundle.identityKey)
      || !(Model.Messages.canonicalKey bundle.signedPrekey)
      || !(bundle.oneTimePrekey.all Model.Messages.canonicalKey)) = false)
    (hr : checkWith oracle.identityValid exp bundle.identityKey = none) :
    (establishInitiatorExpecting oracle identity bundle exp).refusal ≠
        some (.bundle .unexpectedIdentity) ∧
      (establishInitiatorExpecting oracle identity bundle exp).refusal ≠
        some (.bundle (.handshake .invalidIdentityKey)) := by
  refine ⟨step_never_leaf_unexpected oracle identity bundle exp, ?_⟩
  have hv := rule_never_fires_after_expectation oracle identity bundle exp hr
  rw [success_is_leaf oracle identity bundle exp hm hp hc hr]
  cases hres : (establishInitiator oracle identity bundle bundle.identityKey).result with
  | ok s => simp [Step.refusal, liftResult]
  | error r =>
    intro h
    simp only [Step.refusal, liftResult, Option.some.injEq, Refusal.bundle.injEq] at h
    subst h
    exact hv hres

/-! ## Build-time checks

The order, on the model's toy primitives (`Model.Lifecycle.Examples.toyOracle`, which does no
real cryptography) with the real identity-key rule as the oracle's rule and real
identity keys. Each case records the refusal the step ended in, and the draws left,
so "no randomness drawn" is part of the statement. The signatures are a flag: the
toy oracle accepts every signature or none. -/

/-- Decidable equality of results, for the examples only. -/
local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error a, .error b =>
      if h : a = b then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl)
  | .ok a, .ok b =>
      if h : a = b then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl)
  | .error _, .ok _ => isFalse (by intro h; cases h)
  | .ok _, .error _ => isFalse (by intro h; cases h)

/-- The toy oracle with the real rule and a signature verdict. -/
def exOracle (sigOk : Bool) (draws : List Key) : Oracle :=
  { Model.Lifecycle.Examples.toyOracle draws with
    identityValid := Model.IdentityKey.valid
    sigVerify := fun _ _ _ => sigOk }

/-- Three 32-byte draws, enough for a whole establishment. -/
def exDraws : List Key := [List.replicate 32 0x12, List.replicate 32 0x13, List.replicate 32 0x14]

/-- The toy bundle under another identity key. -/
def exBundle (ik : Key) : Bundle := { Model.Lifecycle.Examples.toyBundle with identityKey := ik }

/-- The refusal the step ended in, and the draws it left. -/
def exRun (sigOk : Bool) (ik : Key) (exp : Expectation Nat) : Option Refusal × List Key :=
  let s := establishInitiatorExpecting (exOracle sigOk exDraws)
    Model.Lifecycle.Examples.toyAliceIdentity (exBundle ik) exp
  (s.refusal, s.oracle.draws)

def known (current retired : List Key) : Expectation Nat := .known ⟨current, retired⟩

-- *known* {K}, bundle K: a session, and the draws are used.
example : (exRun true keyAlice (known [keyAlice] [])).1 = none := by decide +kernel
example : (exRun true keyAlice (known [keyAlice] [])).2 ≠ exDraws := by decide +kernel
-- *known* {K}, bundle K': an unexpected identity, nothing drawn.
example : exRun true keyBob (known [keyAlice] []) = (some .unexpectedIdentity, exDraws) := by
  decide +kernel
-- *known* {current K, retired K_old}, bundle K_old.
example : exRun true keyH2 (known [keyAlice] [keyH2]) = (some .retiredIdentity, exDraws) := by
  decide +kernel
-- A bad signature under a key she refuses is the key's refusal.
example : exRun false keyBob (known [keyAlice] []) = (some .unexpectedIdentity, exDraws) := by
  decide +kernel
-- Under the key she expects, the signatures are still checked.
example : (exRun false keyAlice (known [keyAlice] [])).1 =
    some (.bundle (.handshake .badSignedPrekeySignature)) := by decide +kernel
-- Inconsistent presence, under a key she would refuse: the presence refusal.
example : (establishInitiatorExpecting (exOracle true exDraws) Model.Lifecycle.Examples.toyAliceIdentity
      { exBundle keyBob with oneTimePrekey := some (List.replicate 32 0x24) }
      (known [keyAlice] [])).refusal = some (.bundle .inconsistentBundle) := by
  decide +kernel
-- Under the expected key, the KEM and agreement checks follow the
-- expectation (the toy oracle refuses a KEM prekey, or the agreements).
example : (establishInitiatorExpecting
      { exOracle true exDraws with kemValid := fun _ => false }
      Model.Lifecycle.Examples.toyAliceIdentity (exBundle keyAlice) (known [keyAlice] [])).refusal =
    some (.bundle .kem) := by decide +kernel
example : (establishInitiatorExpecting
      { exOracle true exDraws with kemValid := fun _ => false }
      Model.Lifecycle.Examples.toyAliceIdentity (exBundle keyBob) (known [keyAlice] [])).refusal =
    some .unexpectedIdentity := by decide +kernel
example : (establishInitiatorExpecting
      { exOracle true exDraws with dhAgree := fun _ _ => none }
      Model.Lifecycle.Examples.toyAliceIdentity (exBundle keyAlice) (known [keyAlice] [])).refusal =
    some (.bundle (.handshake .nonContributoryAgreement)) := by decide +kernel
example : (establishInitiatorExpecting
      { exOracle true exDraws with dhAgree := fun _ _ => none }
      Model.Lifecycle.Examples.toyAliceIdentity (exBundle keyBob) (known [keyAlice] [])).refusal =
    some .unexpectedIdentity := by decide +kernel
-- A non-canonical member, with a bad signature: a malformed record.
example : exRun false keyAlice (known [keyAlice, keyUp] []) = (some .malformedRecord, exDraws) := by
  decide +kernel
-- A key that is not an identity key: invalid identity key, under *known* and
-- under *first contact* with no records, with nothing drawn.
example : exRun true keyAlicePlusT (known [keyAlice] []) = (some .invalidIdentityKey, exDraws) := by
  decide +kernel
example : exRun true keyAlicePlusT (.firstContact []) = (some .invalidIdentityKey, exDraws) := by
  decide +kernel
-- A bundle key that is not canonical: the canonical-key refusal, not the key's.
example : exRun true keyBit255 (known [keyAlice] []) = (some (.bundle .badEncoding), exDraws) := by
  decide +kernel
-- *first contact*, no records: a session, unattributed.
example : (exRun true keyH1 (.firstContact [])).1 = none := by decide +kernel
-- *known* with a record that holds nothing, with a bad signature.
example : exRun false keyAlice (known [] []) = (some .malformedRecord, exDraws) := by
  decide +kernel
example : exRun true keyAlice (known [] []) = (some .malformedRecord, exDraws) := by
  decide +kernel
-- *first contact*, a key retired for one contact and *same* for none.
example : exRun true keyH2 (.firstContact [(1, ⟨[], [keyH2]⟩)]) = (some .retiredIdentity, exDraws) := by
  decide +kernel
-- A key that is a recorded contact's, however it is recorded.
example : exRun true keyBob (.firstContact [(1, ⟨[keyBob], []⟩)]) =
    (some .unexpectedIdentity, exDraws) := by decide +kernel
example : exRun true keyAlice (.firstContact [(1, ⟨[keyAlice], []⟩), (2, ⟨[], [keyAlice]⟩)]) =
    (some .unexpectedIdentity, exDraws) := by decide +kernel
example : exRun true keyAlice (.firstContact [(1, ⟨[keyAlice], []⟩), (2, ⟨[keyAlice], []⟩)]) =
    (some .unexpectedIdentity, exDraws) := by decide +kernel
-- *known* {K}, with K also current for another contact: a session, and the
-- lookup finds the key ambiguous.
example : (exRun true keyAlice (known [keyAlice] [])).1 = none := by decide +kernel
example : lookupWith (C := Nat) Model.IdentityKey.valid keyAlice
      [(1, ⟨[keyAlice], []⟩), (2, ⟨[keyAlice], []⟩)] = .ok ⟨.ambiguous [1, 2], [], []⟩ := by
  decide +kernel
-- *first contact*, one record with a non-canonical member, bad signature.
example : exRun false keyH1 (.firstContact [(1, ⟨[keyBob, keyBit255], []⟩)]) =
    (some .malformedRecord, exDraws) := by decide +kernel
-- *known* {K}, a key the rule refuses, with bad signatures: invalid identity key.
example : exRun false keyU0 (known [keyAlice] []) = (some .invalidIdentityKey, exDraws) := by
  decide +kernel
example : exRun false keyU2 (known [keyAlice] []) = (some .invalidIdentityKey, exDraws) := by
  decide +kernel
example : exRun false (hexKey "0100000000000000000000000000000000000000000000000000000000000000")
      (known [keyAlice] []) = (some .invalidIdentityKey, exDraws) := by decide +kernel
example : exRun false (hexKey "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f")
      (known [keyAlice] []) = (some .invalidIdentityKey, exDraws) := by decide +kernel
example : exRun false (hexKey "e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800")
      (known [keyAlice] []) = (some .invalidIdentityKey, exDraws) := by decide +kernel
example : exRun false (hexKey "5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157")
      (known [keyAlice] []) = (some .invalidIdentityKey, exDraws) := by decide +kernel
-- *known* {current K, retired K+T}, bundle K+T: invalid identity key, not retired.
example : exRun true keyAlicePlusT (known [keyAlice] [keyAlicePlusT]) =
    (some .invalidIdentityKey, exDraws) := by decide +kernel
-- *first contact*, no records, a key the rule refuses.
example : exRun true keyU2 (.firstContact []) = (some .invalidIdentityKey, exDraws) := by
  decide +kernel
-- A non-canonical member, and a bundle key that is not an identity key: the
-- malformed record comes first.
example : exRun true keyU0 (known [keyAlice, keyUp] []) = (some .malformedRecord, exDraws) := by
  decide +kernel
-- A presence disagreement and a key that is not an identity key: the presence
-- refusal.
example : (establishInitiatorExpecting (exOracle true exDraws) Model.Lifecycle.Examples.toyAliceIdentity
      { exBundle keyU0 with oneTimePrekey := some (List.replicate 32 0x24) }
      (known [keyAlice] [])).refusal = some (.bundle .inconsistentBundle) := by
  decide +kernel
-- A canonical member that is not an identity key is not malformed.
example : (exRun true keyAlice (known [keyAlice, keyU0] [])).1 = none := by decide +kernel
-- *first contact*, a record that holds only such a key: a session.
example : (exRun true keyH1 (.firstContact [(1, ⟨[keyU0], []⟩)])).1 = none := by
  decide +kernel

end Model.InitiatorExpectation
