/-
Model.IdentityRecords: the identity pair digest, the verification number, and a
party's records of identity keys with their classification and lookup.

Written from two pages of tacenta-spec:
- protocol/identities-and-devices.md, "The identity pair digest" and "The
  verification number" (and "Identity keys", for where the identity-key rule
  applies);
- protocol/session-establishment.md, "Records, expectations and attribution":
  the records, the classification, the lookup and attribution.

It is written from the pages, not from `tacenta-core`, so that it can disagree
with it. The initiator's expectation, which is built on the classification and
the lookup, is in `Model.InitiatorExpectation`.

**The rule, and an argument for it.** The identity-key rule is
`Model.IdentityKey.valid`. The classification and the lookup take the rule as an
argument `rule : Key → Bool`, which is applied only to a key that has already
passed the canonical-encoding check, so a refusal is a decode failure or an
invalid identity key, never both. The functions named without `With` fix it at
`Model.IdentityKey.valid`. The argument exists so that the initiator's
expectation, which lives beside the lifecycle model, can use the same rule the
lifecycle model takes from its oracle (`Model.Lifecycle.Oracle.identityValid`),
and so that "the rule never fires on its own after the expectation" can be
stated as a theorem.

**What is and is not established here.** These are definitions to run, and the
theorems below are properties of the definitions (a total characterisation, the
order of the checks, symmetry). Nothing here proves that the definitions compute
what `tacenta-core` computes: that is the vectors' and the runner's job, and a
reading of the page. The digest's SHA-256 is `Model.Sha256.hash`, which is
checked against the FIPS examples and a length theorem, not proved correct.

**A choice the pages leave to the model.** The pages speak of 32-byte keys, and
`tacenta-core` takes `[u8; 32]`. The model's keys are byte lists, so a list that
is not 32 bytes long is not the canonical encoding of a curve public key: it is
refused as a decode failure, by the same test that refuses a key with bit 255
set. No page names that case; it is unreachable for a key the decoders return.
-/
import Model.IdentityKey
import Model.Sha256

namespace Model.IdentityRecords

abbrev Key := List UInt8

open Model.Messages (canonicalKey leValue)

/-! ## Keys: a decode failure or an invalid identity key -/

/-- The two refusals of a key (identities-and-devices.md, Identity keys, "A
    refusal"): not a canonical encoding, which is a decode failure, and canonical
    but not an identity key. -/
inductive KeyRefusal where
  | decodeFailure
  | invalidIdentityKey
  deriving Repr, DecidableEq, Inhabited

/-- Whether `k` is the canonical encoding of a curve public key
    (message-format.md, Curve public keys): 32 bytes, bit 255 clear, value below
    `p`. A member of a record is held to this and no more. -/
def canonicalEncoding (k : Key) : Bool := k.length == 32 && canonicalKey k

/-- The refusal of a key, if any: first the canonical encoding, then the rule.
    The rule is applied only to a canonical key. -/
def keyRefusalWith (rule : Key → Bool) (k : Key) : Option KeyRefusal :=
  if !canonicalEncoding k then some .decodeFailure
  else if !rule k then some .invalidIdentityKey
  else none

/-- `keyRefusalWith` under the model's own statement of the rule. -/
abbrev keyRefusal : Key → Option KeyRefusal := keyRefusalWith Model.IdentityKey.valid

/-- A key is not refused exactly when it is a canonical encoding and the rule
    accepts it. -/
theorem keyRefusalWith_eq_none_iff (rule : Key → Bool) (k : Key) :
    keyRefusalWith rule k = none ↔ canonicalEncoding k = true ∧ rule k = true := by
  unfold keyRefusalWith
  cases h1 : canonicalEncoding k <;> cases h2 : rule k <;> simp

/-- Whether `k` is an identity key: neither refusal applies. -/
def isIdentityKey (k : Key) : Bool := (keyRefusal k).isNone

/-- `Model.IdentityKey.valid` already contains the canonical test and the length,
    so a key it accepts is never refused here. -/
theorem keyRefusal_eq_none_iff (k : Key) :
    keyRefusal k = none ↔ Model.IdentityKey.valid k = true := by
  unfold keyRefusal keyRefusalWith canonicalEncoding Model.IdentityKey.valid
  cases h1 : (k.length == 32) <;> cases h2 : canonicalKey k <;>
    cases h3 : Model.IdentityKey.inPrimeOrderSubgroup (leValue k) <;> simp

/-! ## The identity pair digest -/

/-- `PAIR_DIGEST_LABEL`, `"Tacenta:identity:pair-digest:v1" || 0xFF`
    (CONSTANTS.md): 32 bytes. -/
def pairDigestLabel : Key :=
  [0x54, 0x61, 0x63, 0x65, 0x6e, 0x74, 0x61, 0x3a, 0x69, 0x64, 0x65, 0x6e, 0x74, 0x69,
   0x74, 0x79, 0x3a, 0x70, 0x61, 0x69, 0x72, 0x2d, 0x64, 0x69, 0x67, 0x65, 0x73, 0x74,
   0x3a, 0x76, 0x31, 0xff]

theorem pairDigestLabel_length : pairDigestLabel.length = 32 := by decide

/-- `a <= b` for byte strings, as strings of unsigned bytes: byte 0 first, and
    the first byte that differs decides (identities-and-devices.md, "Order").
    It is not the order of the little-endian values the keys name. -/
def bytesLe : Key → Key → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a.toNat < b.toNat then true
      else if a.toNat = b.toNat then bytesLe as bs
      else false

theorem bytesLe_total (a b : Key) : bytesLe a b = true ∨ bytesLe b a = true := by
  induction a generalizing b with
  | nil => simp [bytesLe]
  | cons x xs ih =>
    cases b with
    | nil => simp [bytesLe]
    | cons y ys =>
      simp only [bytesLe]
      by_cases hxy : x.toNat < y.toNat
      · simp [hxy]
      · by_cases hyx : y.toNat < x.toNat
        · simp [hyx]
        · have heq : x.toNat = y.toNat := by omega
          simpa [hxy, hyx, heq] using ih ys

theorem bytesLe_antisymm (a b : Key) (hab : bytesLe a b = true) (hba : bytesLe b a = true) :
    a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => simp [bytesLe] at hba
  | cons x xs ih =>
    cases b with
    | nil => simp [bytesLe] at hab
    | cons y ys =>
      rcases Nat.lt_trichotomy x.toNat y.toNat with hlt | heq | hgt
      · exfalso
        have h1 : ¬ (y.toNat < x.toNat) := by omega
        have h2 : ¬ (y.toNat = x.toNat) := by omega
        simp [bytesLe, h1, h2] at hba
      · have hxy : x = y := UInt8.toNat_inj.mp heq
        subst hxy
        simp [bytesLe] at hab hba
        rw [ih ys hab hba]
      · exfalso
        have h1 : ¬ (x.toNat < y.toNat) := by omega
        have h2 : ¬ (x.toNat = y.toNat) := by omega
        simp [bytesLe, h1, h2] at hab

/-- The two keys sorted by `bytesLe`: `(lo, hi) = (k1, k2)` if `k1 <= k2`, else
    `(k2, k1)`. -/
def sortPair (k1 k2 : Key) : Key × Key :=
  if bytesLe k1 k2 then (k1, k2) else (k2, k1)

/-- Both parties compute the same pair, whichever of them computes it. -/
theorem sortPair_comm (k1 k2 : Key) : sortPair k1 k2 = sortPair k2 k1 := by
  unfold sortPair
  by_cases h12 : bytesLe k1 k2 = true <;> by_cases h21 : bytesLe k2 k1 = true
  · have := bytesLe_antisymm k1 k2 h12 h21
    subst this; rfl
  · simp [h12, h21]
  · simp [h12, h21]
  · rcases bytesLe_total k1 k2 with h | h <;> simp_all

/-- `SHA-256(PAIR_DIGEST_LABEL || lo || hi)`, with no check on the keys: the
    digest function as the pseudocode gives it after the line "refuse unless k1
    and k2 are identity keys". 96 bytes in, 32 out. Exposed so that the sorting
    and the hash can be checked on pairs that the rule refuses. -/
def digestOf (k1 k2 : Key) : Key :=
  let p := sortPair k1 k2
  Model.Sha256.hash (pairDigestLabel ++ p.1 ++ p.2)

/-- `identity_pair_digest(k1, k2)` (identities-and-devices.md): refuse unless both
    keys are identity keys, then the digest of the sorted pair. The refusal is
    the first key's if it is refused, then the second's. -/
def pairDigest (k1 k2 : Key) : Except KeyRefusal Key :=
  match keyRefusal k1 with
  | some r => .error r
  | none =>
    match keyRefusal k2 with
    | some r => .error r
    | none => .ok (digestOf k1 k2)

/-- The refusals the page allows for a pair: the refusal of each key that is
    refused. "When both keys would be refused, either refusal conforms." -/
def allowedRefusals (k1 k2 : Key) : List KeyRefusal :=
  (keyRefusal k1).toList ++ (keyRefusal k2).toList

theorem digestOf_comm (k1 k2 : Key) : digestOf k1 k2 = digestOf k2 k1 := by
  unfold digestOf
  rw [sortPair_comm]

theorem digestOf_length (k1 k2 : Key) : (digestOf k1 k2).length = 32 := by
  simp [digestOf, Model.Sha256.hash_length]

/-- The digest is symmetric in its arguments: if one order is accepted, the other
    gives the same digest. -/
theorem pairDigest_comm_ok (k1 k2 d : Key) (h : pairDigest k1 k2 = .ok d) :
    pairDigest k2 k1 = .ok d := by
  unfold pairDigest at h ⊢
  cases h1 : keyRefusal k1 <;> cases h2 : keyRefusal k2 <;> simp_all [digestOf_comm]

/-- The refusal-or-accept split: accepted exactly when neither key is refused. -/
theorem pairDigest_ok_iff (k1 k2 d : Key) :
    pairDigest k1 k2 = .ok d ↔
      keyRefusal k1 = none ∧ keyRefusal k2 = none ∧ d = digestOf k1 k2 := by
  unfold pairDigest
  cases h1 : keyRefusal k1 <;> cases h2 : keyRefusal k2 <;> simp [eq_comm]

/-- A refusal is a refusal of one of the two keys: a decode failure or an invalid
    identity key, and nothing else. -/
theorem pairDigest_error_allowed (k1 k2 : Key) (r : KeyRefusal)
    (h : pairDigest k1 k2 = .error r) : r ∈ allowedRefusals k1 k2 := by
  unfold pairDigest at h
  unfold allowedRefusals
  cases h1 : keyRefusal k1 <;> cases h2 : keyRefusal k2 <;> simp_all

/-- The set of allowed refusals is the same for both orders, so a runner may
    accept either refusal for a pair whose keys are both refused. -/
theorem allowedRefusals_comm (k1 k2 : Key) (r : KeyRefusal) :
    r ∈ allowedRefusals k1 k2 ↔ r ∈ allowedRefusals k2 k1 := by
  simp only [allowedRefusals, List.mem_append]
  exact Or.comm

/-- The digest refuses exactly when some key is refused. -/
theorem pairDigest_error_iff (k1 k2 : Key) :
    (∃ r, pairDigest k1 k2 = .error r) ↔ allowedRefusals k1 k2 ≠ [] := by
  unfold pairDigest allowedRefusals
  cases h1 : keyRefusal k1 <;> cases h2 : keyRefusal k2 <;> simp

/-- A key refused alone is refused whatever the other is: the first key's
    refusal is the digest's, and when it is not refused the second's is. This is
    the model's choice among the refusals the page allows. -/
theorem pairDigest_first_refusal (k1 k2 : Key) (r : KeyRefusal)
    (h : keyRefusal k1 = some r) : pairDigest k1 k2 = .error r := by
  simp [pairDigest, h]

/-- Equal keys are allowed. -/
theorem pairDigest_self (k : Key) (h : keyRefusal k = none) :
    pairDigest k k = .ok (digestOf k k) := by
  simp [pairDigest, h]

/-! ## The verification number -/

/-- A byte string read as an unsigned big-endian integer. -/
def beValue (bs : Key) : Nat := bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The decimal digits of `n` in `width` places, most significant first. -/
def decimalDigits (n width : Nat) : List Nat :=
  (List.range width).reverse.map (fun i => n / 10 ^ i % 10)

/-- A digit as its ASCII byte, `0x30` to `0x39`. -/
def asciiDigit (d : Nat) : UInt8 := UInt8.ofNat (0x30 + d)

/-- `verification_number(digest)` (identities-and-devices.md): the digest read as
    an unsigned big-endian integer, `mod 10^60`, as 60 ASCII digits, most
    significant first, left-padded with `'0'`. -/
def verificationNumber (digest : Key) : Key :=
  (decimalDigits (beValue digest % 10 ^ 60) 60).map asciiDigit

/-- The ASCII digits read back as a decimal integer. -/
def decimalValue (bs : Key) : Nat := bs.foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0

theorem verificationNumber_length (digest : Key) : (verificationNumber digest).length = 60 := by
  simp [verificationNumber, decimalDigits]

private theorem foldl_decimalDigits (n acc w : Nat) :
    (decimalDigits n w).foldl (fun a d => a * 10 + d) acc = acc * 10 ^ w + n % 10 ^ w := by
  induction w generalizing acc with
  | zero => simp [decimalDigits, Nat.mod_one]
  | succ w ih =>
    have hd : decimalDigits n (w + 1) = (n / 10 ^ w % 10) :: decimalDigits n w := by
      simp [decimalDigits, List.range_succ]
    rw [hd, List.foldl_cons, ih, Nat.mod_pow_succ]
    grind

private theorem decimalDigits_lt (n w d : Nat) (hd : d ∈ decimalDigits n w) : d < 10 := by
  simp only [decimalDigits, List.mem_map] at hd
  obtain ⟨i, _, rfl⟩ := hd
  exact Nat.mod_lt _ (by omega)

/-- Every byte of the number is an ASCII digit. -/
theorem verificationNumber_digits (digest : Key) :
    ∀ b ∈ verificationNumber digest, 0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 := by
  intro b hb
  simp only [verificationNumber, List.mem_map] at hb
  obtain ⟨d, hd, rfl⟩ := hb
  have := decimalDigits_lt _ _ d hd
  simp only [asciiDigit]
  simp
  omega

/-- The number reads back as the digest's value mod `10^60`, so the digits are the
    big-endian value in decimal, most significant first, and nothing else. -/
theorem decimalValue_verificationNumber (digest : Key) :
    decimalValue (verificationNumber digest) = beValue digest % 10 ^ 60 := by
  have key : ∀ (ds : List Nat), (∀ d ∈ ds, d < 10) → ∀ acc,
      (ds.map asciiDigit).foldl (fun a b => a * 10 + (b.toNat - 0x30)) acc =
        ds.foldl (fun a d => a * 10 + d) acc := by
    intro ds
    induction ds with
    | nil => intros; rfl
    | cons d ds ih =>
      intro hlt acc
      have hd : d < 10 := hlt d (by simp)
      have h48 : (asciiDigit d).toNat - 0x30 = d := by
        simp only [asciiDigit]
        simp
        omega
      simp only [List.map_cons, List.foldl_cons, h48]
      exact ih (fun e he => hlt e (by simp [he])) _
  unfold decimalValue verificationNumber
  rw [key _ (fun d hd => decimalDigits_lt _ _ d hd), foldl_decimalDigits]
  have : beValue digest % 10 ^ 60 % 10 ^ 60 = beValue digest % 10 ^ 60 := Nat.mod_mod _ _
  simp

/-- The digits in groups of five, `n` groups: a layout of the same digits
    ("twelve groups of five"). -/
def groupsOfFive : Nat → Key → List Key
  | 0, _ => []
  | n + 1, bs => bs.take 5 :: groupsOfFive n (bs.drop 5)

theorem groupsOfFive_length (n : Nat) (bs : Key) : (groupsOfFive n bs).length = n := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => simp [groupsOfFive, ih]

theorem groupsOfFive_flatten (n : Nat) (bs : Key) :
    (groupsOfFive n bs).flatten = bs.take (5 * n) := by
  induction n generalizing bs with
  | zero => simp [groupsOfFive]
  | succ n ih =>
    simp only [groupsOfFive, List.flatten_cons, ih]
    have : 5 * (n + 1) = 5 + 5 * n := by omega
    rw [this, List.take_add]

/-- The number in twelve groups of five: the same digits, unchanged. -/
theorem groupsOfFive_verificationNumber (digest : Key) :
    (groupsOfFive 12 (verificationNumber digest)).flatten = verificationNumber digest ∧
      (groupsOfFive 12 (verificationNumber digest)).length = 12 := by
  refine ⟨?_, groupsOfFive_length _ _⟩
  rw [groupsOfFive_flatten]
  exact List.take_of_length_le (by simp [verificationNumber_length])

/-! ## Records -/

/-- A party's record for one contact (session-establishment.md, Records): two
    finite sets of keys, *current* and *retired*. A list denotes the set of its
    members; duplicates are ignored (`classify_congr`). -/
structure Record where
  current : List Key
  retired : List Key
  deriving Repr, DecidableEq, Inhabited

/-- Every member of both sets is the canonical encoding of a curve public key.
    Members are held to this and not to the identity-key rule. -/
def Record.wellFormed (r : Record) : Bool :=
  r.current.all canonicalEncoding && r.retired.all canonicalEncoding

/-- A party *holds a record* for a contact when either set is non-empty. -/
def Record.holds (r : Record) : Bool := !(r.current.isEmpty && r.retired.isEmpty)

/-- How a presented key stands against one record. -/
inductive Class where
  | same
  | new
  | retired
  deriving Repr, DecidableEq, Inhabited

/-- The refusals of a classification: the presented key's two, and a malformed
    record. -/
inductive ClassifyRefusal where
  | decodeFailure
  | invalidIdentityKey
  | malformedRecord
  deriving Repr, DecidableEq, Inhabited

def ClassifyRefusal.ofKey : KeyRefusal → ClassifyRefusal
  | .decodeFailure => .decodeFailure
  | .invalidIdentityKey => .invalidIdentityKey

/-- The classification of a presented key `k` against one record (session-
    establishment.md, Classification):
    1. `k` must be an identity key: not canonical is a decode failure, canonical
       but not an identity key is an invalid identity key;
    2. every member of both sets must be a canonical encoding, else the record is
       malformed, even if `k` matches another member;
    3. *retired* if `k` is in the retired set, otherwise *same* if it is in the
       current set, otherwise *new*. -/
def classifyWith (rule : Key → Bool) (k : Key) (r : Record) : Except ClassifyRefusal Class :=
  match keyRefusalWith rule k with
  | some e => .error (ClassifyRefusal.ofKey e)
  | none =>
    if !r.wellFormed then .error .malformedRecord
    else if r.retired.contains k then .ok .retired
    else if r.current.contains k then .ok .same
    else .ok .new

abbrev classify : Key → Record → Except ClassifyRefusal Class :=
  classifyWith Model.IdentityKey.valid

/-- The presented key's checks come first of all, before any member is looked at:
    whatever the record holds. -/
theorem classify_key_refusal (rule : Key → Bool) (k : Key) (r : Record) (e : KeyRefusal)
    (h : keyRefusalWith rule k = some e) :
    classifyWith rule k r = .error (ClassifyRefusal.ofKey e) := by
  simp [classifyWith, h]

/-- A classification against a well-formed record is never refused as a malformed
    record. -/
theorem classify_wellFormed_not_malformed (rule : Key → Bool) (k : Key) (r : Record)
    (hr : r.wellFormed = true) : classifyWith rule k r ≠ .error .malformedRecord := by
  unfold classifyWith
  cases hk : keyRefusalWith rule k with
  | some e => cases e <;> simp [ClassifyRefusal.ofKey]
  | none =>
    simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split <;> try simp
    split <;> simp

/-- A malformed record refuses the classification of an identity key even when
    the key matches another member. -/
theorem classify_malformed (rule : Key → Bool) (k : Key) (r : Record)
    (hk : keyRefusalWith rule k = none) (hr : r.wellFormed = false) :
    classifyWith rule k r = .error .malformedRecord := by
  simp [classifyWith, hk, hr]

/-- With an identity key and a well-formed record: retired first, then same,
    then new. -/
theorem classify_retired (rule : Key → Bool) (k : Key) (r : Record)
    (hk : keyRefusalWith rule k = none) (hr : r.wellFormed = true)
    (h : k ∈ r.retired) : classifyWith rule k r = .ok .retired := by
  simp [classifyWith, hk, hr, h]

theorem classify_same (rule : Key → Bool) (k : Key) (r : Record)
    (hk : keyRefusalWith rule k = none) (hr : r.wellFormed = true)
    (hret : k ∉ r.retired) (h : k ∈ r.current) :
    classifyWith rule k r = .ok .same := by
  simp [classifyWith, hk, hr, hret, h]

theorem classify_new (rule : Key → Bool) (k : Key) (r : Record)
    (hk : keyRefusalWith rule k = none) (hr : r.wellFormed = true)
    (hret : k ∉ r.retired) (hcur : k ∉ r.current) :
    classifyWith rule k r = .ok .new := by
  simp [classifyWith, hk, hr, hret, hcur]

/-- A key in both sets is *retired*: to accept it again, the party removes it from
    *retired*. -/
theorem classify_both_retired (rule : Key → Bool) (k : Key) (r : Record)
    (hk : keyRefusalWith rule k = none) (hr : r.wellFormed = true)
    (_hc : k ∈ r.current) (ht : k ∈ r.retired) :
    classifyWith rule k r = .ok .retired :=
  classify_retired rule k r hk hr ht

/-- Standalone classification against a record that holds nothing gives *new*
    (an *expectation* with such a record is malformed, but that is
    `Model.InitiatorExpectation`'s). -/
theorem classify_empty (rule : Key → Bool) (k : Key) (hk : keyRefusalWith rule k = none) :
    classifyWith rule k ⟨[], []⟩ = .ok .new := by
  simp [classifyWith, hk, Record.wellFormed]

/-- The classification reads only the two sets' members, so a list and the same
    list with duplicates removed, or in another order, classify alike. -/
theorem classify_congr (rule : Key → Bool) (k : Key) (r r' : Record)
    (hc : ∀ m, m ∈ r.current ↔ m ∈ r'.current)
    (ht : ∀ m, m ∈ r.retired ↔ m ∈ r'.retired) :
    classifyWith rule k r = classifyWith rule k r' := by
  have hcur : r.current.contains k = r'.current.contains k := by
    simpa [List.contains_iff_mem] using hc k
  have hret : r.retired.contains k = r'.retired.contains k := by
    simpa [List.contains_iff_mem] using ht k
  have hwf : r.wellFormed = r'.wellFormed := by
    have h1 : r.current.all canonicalEncoding = r'.current.all canonicalEncoding := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      exact ⟨fun h m hm => h m ((hc m).2 hm), fun h m hm => h m ((hc m).1 hm)⟩
    have h2 : r.retired.all canonicalEncoding = r'.retired.all canonicalEncoding := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      exact ⟨fun h m hm => h m ((ht m).2 hm), fun h m hm => h m ((ht m).1 hm)⟩
    simp [Record.wellFormed, h1, h2]
  simp only [classifyWith, hcur, hret, hwf]

/-- A key that is classified *same* or *retired* is a member of the record, and an
    identity key. A canonical member that is not an identity key therefore never
    matches a presented key (session-establishment.md, Records). -/
theorem classify_member_is_identity_key (rule : Key → Bool) (k : Key) (r : Record) (c : Class)
    (h : classifyWith rule k r = .ok c) (hc : c ≠ .new) :
    keyRefusalWith rule k = none ∧ rule k = true ∧ (k ∈ r.current ∨ k ∈ r.retired) := by
  unfold classifyWith at h
  cases hk : keyRefusalWith rule k with
  | some e => simp [hk] at h
  | none =>
    simp only [hk] at h
    have hrule : rule k = true := by
      unfold keyRefusalWith at hk
      split at hk <;> simp_all
    refine ⟨rfl, hrule, ?_⟩
    split at h
    · simp at h
    · split at h
      · simp_all
      · split at h
        · simp_all
        · simp at h
          exact absurd h.symm hc

/-! ## The lookup -/

/-- What a lookup finds (session-establishment.md, Lookup). -/
inductive Attribution (C : Type) where
  /-- *same* for exactly one contact: the key is that contact's. -/
  | contact (c : C)
  /-- *same* for more than one contact: the key is no contact's. -/
  | ambiguous (cs : List C)
  /-- *same* for none and *retired* for one or more: a retired key of those
      contacts, and no contact's. -/
  | retiredKey (cs : List C)
  /-- *same* for none and *retired* for none. -/
  | unattributed
  deriving Repr, DecidableEq

/-- A lookup's result: the attribution, the contacts the key is *retired* for
    (reported alongside whatever the attribution is), and the contacts whose
    record was skipped as malformed (reported, and attributing nothing). -/
structure LookupResult (C : Type) where
  attribution : Attribution C
  retiredFor : List C
  malformed : List C
  deriving Repr, DecidableEq

section Lookup

variable {C : Type}

/-- The contacts whose record the key is *same* for. -/
def sameFor (rule : Key → Bool) (k : Key) (records : List (C × Record)) : List C :=
  records.filterMap fun cr =>
    match classifyWith rule k cr.2 with
    | .ok .same => some cr.1
    | _ => none

/-- The contacts whose record the key is *retired* for. -/
def retiredFor (rule : Key → Bool) (k : Key) (records : List (C × Record)) : List C :=
  records.filterMap fun cr =>
    match classifyWith rule k cr.2 with
    | .ok .retired => some cr.1
    | _ => none

/-- The contacts whose record is malformed. -/
def malformedFor (rule : Key → Bool) (k : Key) (records : List (C × Record)) : List C :=
  records.filterMap fun cr =>
    match classifyWith rule k cr.2 with
    | .error .malformedRecord => some cr.1
    | _ => none

/-- The four outcomes, from the contacts the key is *same* and *retired* for. -/
def attributionOf (same retired : List C) : Attribution C :=
  match same with
  | [] => if retired.isEmpty then .unattributed else .retiredKey retired
  | [c] => .contact c
  | _ :: _ :: _ => .ambiguous same

/-- A key is looked up by classifying it against every record. A key the
    classification refuses as a decode failure or an invalid identity key refuses
    the lookup in the same way, whether or not any record is held, and no record
    is reported. -/
def lookupWith (rule : Key → Bool) (k : Key) (records : List (C × Record)) :
    Except KeyRefusal (LookupResult C) :=
  match keyRefusalWith rule k with
  | some e => .error e
  | none =>
    let same := sameFor rule k records
    let retired := retiredFor rule k records
    .ok { attribution := attributionOf same retired
          retiredFor := retired
          malformed := malformedFor rule k records }

/-- A refused key refuses the lookup, with no record read. -/
theorem lookup_key_refusal (rule : Key → Bool) (k : Key) (records : List (C × Record))
    (e : KeyRefusal) (h : keyRefusalWith rule k = some e) :
    lookupWith rule k records = .error e := by
  simp [lookupWith, h]

/-- The lookup is total on an identity key: it gives a result. -/
theorem lookup_total (rule : Key → Bool) (k : Key) (records : List (C × Record))
    (h : keyRefusalWith rule k = none) : ∃ r, lookupWith rule k records = .ok r :=
  ⟨{ attribution := attributionOf (sameFor rule k records) (retiredFor rule k records)
     retiredFor := retiredFor rule k records
     malformed := malformedFor rule k records }, by simp [lookupWith, h]⟩

/-- The lookup is total: it refuses the key, or gives a result. -/
theorem lookup_refuses_or_gives (rule : Key → Bool) (k : Key) (records : List (C × Record)) :
    (∃ e, keyRefusalWith rule k = some e ∧ lookupWith rule k records = .error e) ∨
      ∃ r, keyRefusalWith rule k = none ∧ lookupWith rule k records = .ok r := by
  cases h : keyRefusalWith rule k with
  | some e => exact Or.inl ⟨e, rfl, lookup_key_refusal rule k records e h⟩
  | none =>
    obtain ⟨r, hr⟩ := lookup_total rule k records h
    exact Or.inr ⟨r, rfl, hr⟩

/-- Over no records, an identity key is unattributed and nothing is reported. -/
theorem lookup_nil (rule : Key → Bool) (k : Key) (h : keyRefusalWith rule k = none) :
    lookupWith rule k ([] : List (C × Record)) =
      .ok { attribution := .unattributed, retiredFor := [], malformed := [] } := by
  simp [lookupWith, h, sameFor, retiredFor, malformedFor, attributionOf]

/-- The partition into four outcomes, with what each outcome means in terms of
    the contacts the key is *same* and *retired* for. -/
theorem attributionOf_cases (same retired : List C) :
    (∃ c, attributionOf same retired = .contact c ∧ same = [c]) ∨
    (∃ cs, attributionOf same retired = .ambiguous cs ∧ cs = same ∧ 2 ≤ cs.length) ∨
    (attributionOf same retired = .retiredKey retired ∧ same = [] ∧ retired ≠ []) ∨
    (attributionOf same retired = .unattributed ∧ same = [] ∧ retired = []) := by
  match same, retired with
  | [], [] => exact Or.inr (Or.inr (Or.inr ⟨by simp [attributionOf], rfl, rfl⟩))
  | [], r :: rs => exact Or.inr (Or.inr (Or.inl ⟨by simp [attributionOf], rfl, by simp⟩))
  | [c], _ => exact Or.inl ⟨c, by simp [attributionOf], rfl⟩
  | a :: b :: t, _ =>
    exact Or.inr (Or.inl ⟨a :: b :: t, by simp [attributionOf], rfl, by simp⟩)

/-- A lookup's result is exactly the four outcomes of the contacts the key is
    *same* and *retired* for, with the retired contacts reported alongside. -/
theorem lookup_result (rule : Key → Bool) (k : Key) (records : List (C × Record))
    (r : LookupResult C) (h : lookupWith rule k records = .ok r) :
    keyRefusalWith rule k = none ∧
      r.attribution = attributionOf (sameFor rule k records) (retiredFor rule k records) ∧
      r.retiredFor = retiredFor rule k records ∧
      r.malformed = malformedFor rule k records := by
  unfold lookupWith at h
  cases hk : keyRefusalWith rule k with
  | some e => simp [hk] at h
  | none =>
    simp only [hk, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl⟩

end Lookup

/-! ## Build-time checks

Examples the kernel checks when this module builds (`decide +kernel` uses no
axiom). They are examples, not a proof that the definitions compute what the pages
say: the generated vectors pin that. The digests and numbers were computed with
Python's `hashlib` (`python3 -I`) from the pages' definitions, independently of
this file; every key named here is a real identity key unless the case says it
is not. -/

/-- A hexadecimal digit as its value. For the examples. -/
def hexNibble (c : Char) : Nat := if 97 ≤ c.toNat then c.toNat - 87 else c.toNat - 48

/-- Hexadecimal characters as bytes. For the examples. -/
def hexBytes : List Char → List UInt8
  | a :: b :: rest => UInt8.ofNat (hexNibble a * 16 + hexNibble b) :: hexBytes rest
  | _ => []

/-- A key or digest from hexadecimal text. For the examples. -/
def hexKey (s : String) : Key := hexBytes s.toList

/-- A string of ASCII digits as bytes. For the examples. -/
def asciiOf (s : String) : Key := s.toList.map fun c => UInt8.ofNat c.toNat

/-- Decidable equality of results, for the examples only. -/
local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error a, .error b =>
      if h : a = b then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl)
  | .ok a, .ok b =>
      if h : a = b then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl)
  | .error _, .ok _ => isFalse (by intro h; cases h)
  | .ok _, .error _ => isFalse (by intro h; cases h)

/-- RFC 7748, section 6.1: Alice's and Bob's public keys. -/
def keyAlice : Key := hexKey "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"
def keyBob : Key := hexKey "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f"
/-- Two further honest keys (the X25519 public keys of the secrets of repeated bytes
    0x01 and 0x02, as in the identity-key vectors). -/
def keyH1 : Key := hexKey "a4e09292b651c278b9772c569f5fa9bb13d906b46ab68c9df9dc2b4409f8a209"
def keyH2 : Key := hexKey "ce8d3ad1ccb633ec7b70c17814a5c76ecd029685050d344745ba05870e587d59"
/-- Alice's point plus a point of order 8: canonical, on the curve, not an identity
    key. -/
def keyAlicePlusT : Key := hexKey "ec06a18b2851717cbad4dda975daa176baef2f520371e51e5383029272448859"
/-- u = 0 (order 2), u = 2 (the twist), u = p, and a key with bit 255 set. -/
def keyU0 : Key := hexKey "0000000000000000000000000000000000000000000000000000000000000000"
def keyU2 : Key := hexKey "0200000000000000000000000000000000000000000000000000000000000000"
def keyUp : Key := hexKey "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"
def keyBit255 : Key := hexKey "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"

/-! ### The digest -/

-- RFC 7748 6.1 Alice and Bob, both orders.
example : pairDigest keyAlice keyBob =
    .ok (hexKey "14008811078928fb1c0b1467a9abb2398f06cdbe384d30f1e1c2555aa6a4128d") := by
  decide +kernel
example : pairDigest keyBob keyAlice =
    .ok (hexKey "14008811078928fb1c0b1467a9abb2398f06cdbe384d30f1e1c2555aa6a4128d") := by
  decide +kernel

-- Equal keys.
example : pairDigest keyAlice keyAlice =
    .ok (hexKey "bd9ea428f322bc1156ba40bed0ce489c0c627f1c44457f6b8caf07a12d81583f") := by
  decide +kernel

-- Unsigned byte order and little-endian value order disagree. (Two honest keys
-- whose first bytes are 0x9a and 0x44; the digest does not depend on the order given.)
example : pairDigest
      (hexKey "9adcf8b0b668a3d1265ceaeca21842d68fbed9b24a955d77142b1ef112b49b09")
      (hexKey "4495ae279c3c3726cb968047eb431fc19a94b67c9649016ac7042617384bd930") =
    .ok (hexKey "0027825f48dd255fd917134fc155e774a0ca3349f447bea76c9ec01116c25b01") := by
  decide +kernel
example : pairDigest
      (hexKey "4495ae279c3c3726cb968047eb431fc19a94b67c9649016ac7042617384bd930")
      (hexKey "9adcf8b0b668a3d1265ceaeca21842d68fbed9b24a955d77142b1ef112b49b09") =
    .ok (hexKey "0027825f48dd255fd917134fc155e774a0ca3349f447bea76c9ec01116c25b01") := by
  decide +kernel

-- Unsigned order disagrees with signed-byte, 64-bit-limb and little-endian orders.
example : pairDigest
      (hexKey "024dfc7477b284dd11f4b6562500ce06aaa4d903e085182e76d6bec3a10bc01b")
      (hexKey "b832ea22937fb9b62143d78e2ec1b582baabfc9686593c34e8d1ee72cae95819") =
    .ok (hexKey "8d4322bf83f49d728de0ff1b74146da602f44ecea4d2f68c9474a28fb703ca45") := by
  decide +kernel
example : pairDigest
      (hexKey "b832ea22937fb9b62143d78e2ec1b582baabfc9686593c34e8d1ee72cae95819")
      (hexKey "024dfc7477b284dd11f4b6562500ce06aaa4d903e085182e76d6bec3a10bc01b") =
    .ok (hexKey "8d4322bf83f49d728de0ff1b74146da602f44ecea4d2f68c9474a28fb703ca45") := by
  decide +kernel

-- Two pairs that are not identity keys (`01 00..`
-- against `80 00..`, and `00 ff 00..` against `01 00..`). The rule now refuses them
-- (below). The sort and the hash are still checked on them through `digestOf`, which
-- applies no rule: unsigned byte order, and not a signed or a little-endian one.
example : digestOf (hexKey "0100000000000000000000000000000000000000000000000000000000000000")
      (hexKey "8000000000000000000000000000000000000000000000000000000000000000") =
    hexKey "29264d5204e88ac50296a4a0889ad603eec6745c2f509be4fd7d00093f0b6f2f" := by
  decide +kernel
example : digestOf (hexKey "8000000000000000000000000000000000000000000000000000000000000000")
      (hexKey "0100000000000000000000000000000000000000000000000000000000000000") =
    hexKey "29264d5204e88ac50296a4a0889ad603eec6745c2f509be4fd7d00093f0b6f2f" := by
  decide +kernel
example : digestOf (hexKey "00ff000000000000000000000000000000000000000000000000000000000000")
      (hexKey "0100000000000000000000000000000000000000000000000000000000000000") =
    hexKey "20e29d3541d6d865f70231cd74e79bb0fc439eeb371f685b33397eb113324be6" := by
  decide +kernel
example : digestOf (hexKey "0100000000000000000000000000000000000000000000000000000000000000")
      (hexKey "00ff000000000000000000000000000000000000000000000000000000000000") =
    hexKey "20e29d3541d6d865f70231cd74e79bb0fc439eeb371f685b33397eb113324be6" := by
  decide +kernel
-- ... and the rule refuses both pairs, in both orders: neither first key is an
-- identity key (u = 1 has order 4, `00 ff ..` is not of prime order).
example : pairDigest (hexKey "0100000000000000000000000000000000000000000000000000000000000000")
      (hexKey "8000000000000000000000000000000000000000000000000000000000000000") =
    .error .invalidIdentityKey := by decide +kernel
example : pairDigest (hexKey "00ff000000000000000000000000000000000000000000000000000000000000")
      (hexKey "0100000000000000000000000000000000000000000000000000000000000000") =
    .error .invalidIdentityKey := by decide +kernel

-- Alice's key plus a point of order 8, which gives the same agreement.
example : pairDigest keyAlice keyAlicePlusT = .error .invalidIdentityKey := by decide +kernel
example : pairDigest keyAlicePlusT keyAlice = .error .invalidIdentityKey := by decide +kernel
-- U = 0, u = 1, u = p - 1, an order-8 value, and the twist u = 2.
example : pairDigest keyU0 keyU0 = .error .invalidIdentityKey := by decide +kernel
example : pairDigest keyU0 keyAlice = .error .invalidIdentityKey := by decide +kernel
example : pairDigest keyAlice keyU0 = .error .invalidIdentityKey := by decide +kernel
example : pairDigest keyU2 keyAlice = .error .invalidIdentityKey := by decide +kernel
example : pairDigest
      (hexKey "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f") keyBob =
    .error .invalidIdentityKey := by decide +kernel
example : pairDigest keyBob
      (hexKey "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f") =
    .error .invalidIdentityKey := by decide +kernel
example : pairDigest
      (hexKey "e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800") keyAlice =
    .error .invalidIdentityKey := by decide +kernel
example : pairDigest
      (hexKey "5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157") keyAlice =
    .error .invalidIdentityKey := by decide +kernel
-- A key that is not canonical is a decode failure, in both orders.
example : pairDigest keyUp keyAlice = .error .decodeFailure := by decide +kernel
example : pairDigest keyAlice keyUp = .error .decodeFailure := by decide +kernel
example : pairDigest keyBit255 keyAlice = .error .decodeFailure := by decide +kernel
example : pairDigest keyAlice keyBit255 = .error .decodeFailure := by decide +kernel
example : pairDigest
      (hexKey "0900000000000000000000000000000000000000000000000000000000000080") keyAlice =
    .error .decodeFailure := by decide +kernel
-- Both keys refused with different kinds. The model refuses with the first
-- key's kind; either conforms.
example : pairDigest keyUp keyU0 = .error .decodeFailure := by decide +kernel
example : pairDigest keyU0 keyUp = .error .invalidIdentityKey := by decide +kernel
example : allowedRefusals keyUp keyU0 = [.decodeFailure, .invalidIdentityKey] := by
  decide +kernel
example : allowedRefusals keyU0 keyUp = [.invalidIdentityKey, .decodeFailure] := by
  decide +kernel

-- The label is the one CONSTANTS.md gives, hexadecimal and all.
example : pairDigestLabel =
    hexKey "546163656e74613a6964656e746974793a706169722d6469676573743a7631ff" := by
  decide +kernel

/-! ### The verification number -/

-- The numbers of the real digests above; the first has a leading 0.
example : verificationNumber
      (hexKey "14008811078928fb1c0b1467a9abb2398f06cdbe384d30f1e1c2555aa6a4128d") =
    asciiOf "052232527622821359925098979431014658475034016576229087646349" := by
  decide +kernel
example : verificationNumber
      (hexKey "bd9ea428f322bc1156ba40bed0ce489c0c627f1c44457f6b8caf07a12d81583f") =
    asciiOf "342505388527416776856014407131757739973616090526712340764735" := by
  decide +kernel
example : verificationNumber
      (hexKey "0027825f48dd255fd917134fc155e774a0ca3349f447bea76c9ec01116c25b01") =
    asciiOf "326740346840144235862691584058853149216616459493057048500993" := by
  decide +kernel
example : verificationNumber
      (hexKey "8d4322bf83f49d728de0ff1b74146da602f44ecea4d2f68c9474a28fb703ca45") =
    asciiOf "810580752928734638613309288310412549030767074425684229343813" := by
  decide +kernel
-- All zero: 60 zeros. All 0xFF.
example : verificationNumber (List.replicate 32 0) = List.replicate 60 (0x30 : UInt8) := by
  decide +kernel
example : verificationNumber (List.replicate 32 0xff) =
    asciiOf "423570985008687907853269984665640564039457584007913129639935" := by
  decide +kernel
-- First byte at least 0x80.
example : verificationNumber
      (hexKey "f30f87160c9c36b2645d92005f9555ee30ed00199f19bd6e1dde7c5bb2ec0bde") =
    asciiOf "615284566845113059934298192627384047078637029284611927837662" := by
  decide +kernel
-- A value below 10^30, 55 leading zeros.
example : verificationNumber
      (hexKey "0000000000000000000000000000000000000000000000000000000000003039") =
    asciiOf "000000000000000000000000000000000000000000000000000000012345" := by
  decide +kernel
-- Big-endian; the little-endian reading gives a different number.
example : verificationNumber
      (hexKey "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f") =
    asciiOf "700044960722568376592200742329637303199754547598369979440671" := by
  decide +kernel
-- Twelve groups of five; the digits unchanged.
example : groupsOfFive 12
      (verificationNumber
        (hexKey "14008811078928fb1c0b1467a9abb2398f06cdbe384d30f1e1c2555aa6a4128d")) =
    ["05223", "25276", "22821", "35992", "50989", "79431", "01465", "84750", "34016",
     "57622", "90876", "46349"].map asciiOf := by
  decide +kernel

/-! ### The classification and the lookup -/

-- A record that holds nothing.
example : classify keyAlice ⟨[], []⟩ = .ok .new := by decide +kernel
-- Same, new, retired, a key in both sets, a key only in the other contact's record.
example : classify keyAlice ⟨[keyAlice], []⟩ = .ok .same := by decide +kernel
example : classify keyBob ⟨[keyAlice], []⟩ = .ok .new := by decide +kernel
example : classify keyAlice ⟨[], [keyAlice]⟩ = .ok .retired := by decide +kernel
example : classify keyAlice ⟨[keyAlice], [keyAlice]⟩ = .ok .retired := by decide +kernel
example : classify keyAlice ⟨[], [keyBob]⟩ = .ok .new := by decide +kernel
-- The sum of a key and a point of order 8 is refused, not *new*.
example : classify keyAlicePlusT ⟨[keyAlice], []⟩ = .error .invalidIdentityKey := by
  decide +kernel
-- The middle member.
example : classify keyBob ⟨[keyAlice, keyBob, keyH1], []⟩ = .ok .same := by decide +kernel
-- A presented key that is not canonical.
example : classify keyBit255 ⟨[keyAlice], []⟩ = .error .decodeFailure := by decide +kernel
example : classify keyUp ⟨[keyAlice], []⟩ = .error .decodeFailure := by decide +kernel
-- A malformed record, wherever the non-canonical member is, even
-- when the key matches another member.
example : classify keyAlice ⟨[keyAlice, keyUp], []⟩ = .error .malformedRecord := by
  decide +kernel
example : classify keyAlice ⟨[keyAlice], [keyBit255]⟩ = .error .malformedRecord := by
  decide +kernel
example : classify keyAlice ⟨[keyUp], [keyAlice]⟩ = .error .malformedRecord := by
  decide +kernel
-- Duplicates are ignored.
example : classify keyAlice ⟨[keyAlice, keyAlice, keyBob], []⟩ =
    classify keyAlice ⟨[keyAlice, keyBob], []⟩ := by decide +kernel
-- A canonical member that is not an identity key is not malformed.
example : classify keyAlice ⟨[keyAlice], [keyU0]⟩ = .ok .same := by decide +kernel
-- The presented key is refused even though its bytes are a member.
example : classify keyU0 ⟨[], [keyU0]⟩ = .error .invalidIdentityKey := by decide +kernel
-- The presented key's checks precede the member checks.
example : classify keyAlicePlusT ⟨[keyUp], []⟩ = .error .invalidIdentityKey := by
  decide +kernel
-- The canonical check on the presented key comes first of all.
example : classify keyUp ⟨[keyBit255], []⟩ = .error .decodeFailure := by decide +kernel
-- Members that are not identity keys never match.
example : classify keyAlice ⟨[keyU2, keyAlicePlusT], []⟩ = .ok .new := by decide +kernel

/-- The lookup at the model's rule, for the examples. -/
private abbrev look (k : Key) (l : List (Nat × Record)) :=
  lookupWith (C := Nat) Model.IdentityKey.valid k l

-- Same for one record.
example : look keyAlice [(1, ⟨[keyAlice], []⟩), (2, ⟨[keyBob], []⟩)] =
    .ok ⟨.contact 1, [], []⟩ := by decide +kernel
-- Same for two: ambiguous.
example : look keyAlice [(1, ⟨[keyAlice], []⟩), (2, ⟨[keyAlice], []⟩)] =
    .ok ⟨.ambiguous [1, 2], [], []⟩ := by decide +kernel
-- Retired for one, new elsewhere: a retired key.
example : look keyAlice [(1, ⟨[], [keyAlice]⟩), (2, ⟨[keyBob], []⟩)] =
    .ok ⟨.retiredKey [1], [1], []⟩ := by decide +kernel
-- Same for 2, retired for 1: 2's, with 1 reported.
example : look keyAlice [(1, ⟨[], [keyAlice]⟩), (2, ⟨[keyAlice], []⟩)] =
    .ok ⟨.contact 2, [1], []⟩ := by decide +kernel
-- In no record.
example : look keyAlice [(1, ⟨[keyBob], []⟩)] = .ok ⟨.unattributed, [], []⟩ := by
  decide +kernel
-- A malformed record and a *same* record.
example : look keyAlice [(1, ⟨[keyUp], []⟩), (2, ⟨[keyAlice], []⟩)] =
    .ok ⟨.contact 2, [], [1]⟩ := by decide +kernel
-- Only a malformed record holds the key.
example : look keyAlice [(1, ⟨[keyAlice, keyUp], []⟩)] =
    .ok ⟨.unattributed, [], [1]⟩ := by decide +kernel
-- A key that is not canonical, with records and with none, reports no record.
example : look keyBit255 [(1, ⟨[keyAlice], []⟩)] = .error .decodeFailure := by decide +kernel
example : look keyBit255 [] = .error .decodeFailure := by decide +kernel
-- Same for two, retired for a third: ambiguous, with the retired contact reported.
example : look keyAlice [(1, ⟨[keyAlice], []⟩), (2, ⟨[keyAlice], []⟩), (3, ⟨[], [keyAlice]⟩)] =
    .ok ⟨.ambiguous [1, 2], [3], []⟩ := by decide +kernel
-- Retired for two.
example : look keyAlice [(1, ⟨[], [keyAlice]⟩), (2, ⟨[], [keyAlice]⟩)] =
    .ok ⟨.retiredKey [1, 2], [1, 2], []⟩ := by decide +kernel
-- A record that holds only canonical non-identity keys is not malformed.
example : look keyAlice [(1, ⟨[keyU0], [keyU2]⟩)] = .ok ⟨.unattributed, [], []⟩ := by
  decide +kernel
-- A key that is not an identity key, with records and with none.
example : look keyAlicePlusT [(1, ⟨[keyAlice], []⟩)] = .error .invalidIdentityKey := by
  decide +kernel
example : look keyAlicePlusT [] = .error .invalidIdentityKey := by decide +kernel

end Model.IdentityRecords
