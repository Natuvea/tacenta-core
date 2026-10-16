import Translation.UnitLifecycleDecryptScreen

/-!
# A Braid KEM model read off the shipped `tacenta_kem` wrapper

The Braid refinement agreements `KemLenAgrees K`, `KemAgreesFor K` and `ValidateEkAgrees K`
(`SessionUnitBraidT3.lean`) relate the unit's opaque `tacenta_kem` functions to a Braid KEM model `K`.
`UnitLifecycleDecryptScreen.decrypt_hypotheses_jointly_satisfiable` takes them, with `KemCloneAgrees`,
as the `agreements` field of its law bundle at a free `K`; before this module no `K` was related to the
shipped wrapper (the tree's models are `toyKem` and `shippedSizeKem`, which never refuse and return
constant bytes).  This module builds that `K` from the wrapper itself and proves the agreements of it
from named laws about the wrapper's opaque functions.

## What is shown

* `wrapperKemOf I` (and `wrapperKem := wrapperKemOf Interp.real`): a `Model.Braid.Kem` whose four
  operations call the wrapper's functions on byte views of their arguments, the technique
  `UnitOracleJoint.oracleOfLaws` uses for the DH and AEAD clauses.  The model's randomness `n` is read
  as the byte-stream source `byteRng` holding the little-endian digits of `n` (64 for key generation,
  32 for encapsulation); the private part is the 64 key-generation bytes, and the encapsulation
  secret is the 32 encapsulation bytes followed by the header, from which `encaps2` and `decaps`
  call `generate` or `encapsulate1` again before `decapsulate` or `encapsulate2`.  Each operation
  returns `none` exactly where the call it makes returns `Err` (or does not return).  `hashEk` is read
  off `validate_ek` (`hashEkOf`): the 32-byte `hek` it accepts after the seed, when there is one, and
  the empty string otherwise.  The sizes are the crate's: 1536, 1408, 160.
* Eight laws, each a statement about opaque `tacenta_kem` constants (with the Lean byte-stream
  source `byteRng`), none about translated code: `LawKemConstants`, `LawGenerateSeeded`,
  `LawGeneratedKeyPair`, `LawEncapsulate1Seeded`, `LawEncapsulate2Fresh`, `LawValidateEkTotal`,
  `LawValidateEkUnique` and `LawKemClone`; bundled as `WrapperKemLaws` (`wrapperKemLaws_iff`), and
  over an interpretation as `WrapperKemLawsShape`, each bound by `Iff.rfl`.
* `kemLenAgrees_wrapperKem`, `kemAgreesFor_wrapperKem`, `validateEkAgrees_wrapperKem`,
  `kemCloneAgrees_wrapperKem` and `t3Agreements_wrapperKem`: the agreements at `wrapperKem` from the
  laws (the KDF agreements of `T3Agreements` are taken as given).  `KemCloneAgrees` mentions no KEM
  model and is the law `LawKemClone` restated; the other three are proofs.  `keyPairRefines_wrapperKem`
  and `encapsRefines_wrapperKem`: a key pair or encapsulation state the wrapper produces from any source
  that answers refines, at `wrapperKem`, the model's private part or secret, refusing exactly where
  the model refuses.
* `decrypt_hypotheses_jointly_satisfiable_at_wrapperKem`: `decrypt_hypotheses_jointly_satisfiable` at
  `K := wrapperKem`, under `DecryptWrapperLaws dh`, the joint bundle with its `agreements` field
  replaced by the two KDF agreements and the eight laws (`DecryptWrapperLawsShape.toJoint`).
* `decrypt_wrapper_laws_model`, `decrypt_joint_laws_model_at_wrapperKemOf`,
  `decrypt_wrapper_laws_satisfiable`: one interpretation, `Interp.modelShipped`, whose four KEM length
  constants are the crate's, satisfies the wrapper bundle, and so the joint bundle at
  `wrapperKemOf Interp.modelShipped`.

## What is assumed

The eight laws.  They are about libcrux-backed functions (`tacenta-core/kem/src/lib.rs`) and are not
proved of them: that key generation and the first half of encapsulation are functions of the bytes
they draw; that a generated key pair's header and vector have 64 and 1536 bytes and pass `validate_ek`;
that `decapsulate` on a generated key pair, `encapsulate2` on a state `encapsulate1` produced, and
`validate_ek`, each return on inputs of the crate's lengths (including vectors that were never
validated and ciphertexts that were never produced); that `validate_ek` accepts at most one hash for a
seed and a vector; and that a clone answers as its original.  The coefficient-bound refusal of
`encapsulate2` is in the body of an opaque function here, so it enters only through
`LawEncapsulate2Fresh`, which speaks of states `encapsulate1` produced and says nothing of whether
`encapsulate2` refuses one.
`LawEncapsulate2Fresh` covers every 1536-byte vector, including vectors outside libcrux's stated
precondition that the Braid does not pass it on the states it produces (a restored state may: the
gap register's `KEM-STORED-STATE-TOTALITY` row), because `EncapsRefines` quantifies over all of them.  The
corollary also takes the joint bundle's `braid` field (`BraidReceiveAxiom`), whose `decapsulate`,
`encapsulate2` and `validate_ek` totality fields cover every value, restored ones included; the eight
laws do not narrow them.

## What it does not show

* Nothing about ML-KEM: the operations are whatever the wrapper's functions are.
* A key pair restored by `IncrementalKeyPair::from_bytes`, or a state restored by
  `EncapsState::from_bytes`, has no model value at `wrapperKem`: the private part and the secret are
  the bytes the functions drew, so only key pairs and states `generate` and `encapsulate1` produce are
  covered.  `KemDrawsSucceed` and `Model.Braid.Kem.Correct` are not shown at `wrapperKem`.
* At the witness of `decrypt_hypotheses_jointly_satisfiable` the Braid is in `KeysUnsampled`, so no
  state there holds a key pair or an encapsulation state and the relation of `wrapperKem` to a held
  value is not exercised.
* The model `Interp.modelShipped` is not the wrapper: its key generation and encapsulation ignore the
  source and return constant bytes, and it never refuses.  It shows the laws consistent with each
  other and with the joint bundle at the crate's sizes, by the substitution argument of
  `UnitLifecycleDecryptScreen`, which is an argument about derivations and not a theorem inside Lean.

## Platform width

No proof here chooses a width of `usize`: the bounds used are `le64` and `usize_max_ge`, which hold at
both.  No result depends on a compiler-trust axiom (the pins).
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitSatisfiabilityJoint
open Tacenta.UnitSatisfiabilityBraidAgreements
open Tacenta.SessionUnitBraidT3 (vecOf keyOf sliceOf Bytes u8)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc)

namespace Tacenta.UnitKemWrapperModel

/-! ## Byte views -/

theorem toU8_u8 (x : Std.U8) : toU8 (u8 x) = x := by
  cases x with
  | mk bv =>
    simp only [toU8, u8, UScalar.val]
    congr 1
    simp

theorem bytesOf_sliceOf (s : Slice Std.U8) : bytesOf (sliceOf s) = s.val := by
  simp [bytesOf, sliceOf, List.map_map, Function.comp_def, toU8_u8]

theorem length_bytesOf_le {l : Bytes} (h : l.length ≤ Usize.max) : (bytesOf l).length ≤ Usize.max := by
  simpa [bytesOf] using h

theorem length_nil_le : ([] : List Std.U8).length ≤ Usize.max := by simp

/-- A byte string as a slice: its bytes when it fits `usize`, the empty slice otherwise. -/
def bytesSlice (l : Bytes) : Slice Std.U8 :=
  if h : l.length ≤ Usize.max then ⟨bytesOf l, length_bytesOf_le h⟩ else ⟨[], length_nil_le⟩

theorem bytesSlice_sliceOf (s : Slice Std.U8) : bytesSlice (sliceOf s) = s := by
  have h : (sliceOf s).length ≤ Usize.max := by
    simpa [sliceOf] using s.property
  rw [bytesSlice, dif_pos h]
  apply Subtype.ext
  exact bytesOf_sliceOf s

theorem length_bytesSlice_of (l : Bytes) (h : l.length ≤ Usize.max) :
    (bytesSlice l).length = l.length := by
  simp [bytesSlice, h, bytesOf]

theorem sliceOf_bytesSlice (l : Bytes) (h : l.length ≤ Usize.max) : sliceOf (bytesSlice l) = l := by
  rw [bytesSlice, dif_pos h]
  exact map_u8_bytesOf l

/-- A `Vec<u8>` read as the slice it dereferences to. -/
def vecSlice (v : alloc.vec.Vec Std.U8) : Slice Std.U8 := ⟨v.val, v.property⟩

theorem sliceOf_vecSlice (v : alloc.vec.Vec Std.U8) : sliceOf (vecSlice v) = vecOf v := rfl

/-- The first `k` little-endian base-256 digits of `n`, as bytes. -/
def leBytes : ℕ → ℕ → Bytes
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n % 256) :: leBytes k (n / 256)

/-- A byte string as a number, little-endian. -/
def leNat : Bytes → ℕ
  | [] => 0
  | b :: l => b.toNat + 256 * leNat l

theorem length_leBytes (k n : ℕ) : (leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

theorem leBytes_leNat (l : Bytes) : leBytes l.length (leNat l) = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb := b.toNat_lt
    simp only [List.length_cons, leBytes, leNat]
    have h1 : (b.toNat + 256 * leNat l) % 256 = b.toNat := by omega
    have h2 : (b.toNat + 256 * leNat l) / 256 = leNat l := by omega
    rw [h1, h2, ih, UInt8.ofNat_toNat]

/-- The byte-stream source holding the `k` digits of `n`: the randomness the model KEM's drawing
operations read for the model's randomness `n`. -/
def streamOf (k n : ℕ) : List Std.U8 := bytesOf (leBytes k n)

/-- Every byte stream of length `k` is the stream of some number. -/
theorem streamOf_leNat (s : List Std.U8) : streamOf s.length (leNat (s.map u8)) = s := by
  have h := leBytes_leNat (s.map u8)
  rw [List.length_map] at h
  simp only [streamOf, h, bytesOf, List.map_map, Function.comp_def, toU8_u8, List.map_id']

/-! ## The model KEM: the wrapper's functions read through byte views -/

/-- The header hash the wrapper's `validate_ek` accepts: for a seed and a vector, a 32-byte `hek`
that `validate_ek` accepts after the seed, when there is one, and the empty string (which is no
32-byte hash) when there is none.  The real `validate_ek` returns no hash, so the model's `hashEk`
is read off what it accepts; `LawValidateEkUnique` makes the choice unique where it matters. -/
noncomputable def hashEkOf (I : Interp) (ekSeed ekVector : Bytes) : Bytes :=
  open Classical in
  if h : ∃ hek : Bytes, hek.length = 32 ∧
      I.validateEk (bytesSlice (ekSeed ++ hek)) (bytesSlice ekVector) = ok true
  then Classical.choose h else []

/-- **The Braid KEM model read off the wrapper**, over an interpretation `I` of the unit's opaque
constants.  Each operation calls the wrapper function `I` interprets on the byte views of its
arguments, and answers `some` of the converted value where that call returns `Ok` and `none` where it
returns `Err` (or does not return):

* `keyGen rand`: `IncrementalKeyPair::generate` on the byte-stream source holding the 64 digits of
  `rand`; the private part is those 64 bytes, the seed is the first 32 bytes of `header`, the vector is
  `ek_vector`.
* `hashEk`: `hashEkOf`, read off `validate_ek`.
* `encaps1 rand ekSeed hek`: `encapsulate1` on the header `ekSeed ++ hek` and the 32 digits of `rand`;
  the encapsulation secret is those 32 bytes followed by the header.
* `encaps2 secret _ ekVector`: `encapsulate1` again on the secret's header and randomness, then
  `encapsulate2` of the state it returns on `ekVector`.
* `decaps dk ct1 ct2`: `generate` again on the byte stream `dk`, then `decapsulate`.

The sizes are the crate's (`tacenta-core/kem/src/lib.rs`: `EK_VECTOR_LEN` 1536, `CT1_LEN` 1408,
`CT2_LEN` 160).  Nothing here is ML-KEM: the operations are whatever the interpreted functions are. -/
noncomputable def wrapperKemOf (I : Interp) : Model.Braid.Kem where
  keyGen rand :=
    match I.ikpGenerate byteRng byteCrc (streamOf 64 rand) with
    | ok (.Ok kp, _) =>
      match I.ikpHeader kp, I.ikpEkVector kp with
      | ok h, ok v => some (leBytes 64 rand, (vecOf h).take 32, vecOf v)
      | _, _ => none
    | _ => none
  hashEk := hashEkOf I
  encaps1 rand ekSeed hek :=
    match I.encapsulate1 byteRng byteCrc (bytesSlice (ekSeed ++ hek)) (streamOf 32 rand) with
    | ok (.Ok (_, ct1, ss), _) => some (leBytes 32 rand ++ ekSeed ++ hek, vecOf ct1, keyOf ss)
    | _ => none
  encaps2 secret _ ekVector :=
    match I.encapsulate1 byteRng byteCrc (bytesSlice (secret.drop 32)) (bytesOf (secret.take 32)) with
    | ok (.Ok (es, _, _), _) =>
      match I.encapsulate2 es (bytesSlice ekVector) with
      | ok (.Ok ct2) => some (vecOf ct2)
      | _ => none
    | _ => none
  decaps dk ct1 ct2 :=
    match I.ikpGenerate byteRng byteCrc (bytesOf dk) with
    | ok (.Ok kp, _) =>
      match I.ikpDecapsulate kp (bytesSlice ct1) (bytesSlice ct2) with
      | ok (.Ok raw) => some (keyOf raw)
      | _ => none
    | _ => none
  ekSize := 1536
  ct1Size := 1408
  ct2Size := 160

/-- `wrapperKemOf` at the real constants: the Braid KEM model whose operations are the shipped
`tacenta_kem` wrapper's functions. -/
noncomputable def wrapperKem : Model.Braid.Kem := wrapperKemOf Interp.real

/-! ## The laws, about the wrapper's opaque functions

Each law is a statement about opaque `tacenta_kem` constants of the unit (and, for the byte-stream
source, the Lean definition `byteRng`); none is about translated code.  Each is stated once at the real
constants and once over an interpretation, bound by `Iff.rfl`. -/

/-- The four length constants are the crate's. -/
def LawKemConstants : Prop :=
  tacenta_kem.HEADER_LEN = ok 64#usize ∧ tacenta_kem.EK_VECTOR_LEN = ok 1536#usize ∧
    tacenta_kem.CT1_LEN = ok 1408#usize ∧ tacenta_kem.CT2_LEN = ok 160#usize

/-- Key generation is determined by 64 bytes of randomness: from any source that answers, it returns,
and what it returns is what it returns from the byte stream of some 64 bytes. -/
def LawGenerateSeeded : Prop :=
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (rng : R),
    Tacenta.SessionUnitBraidT1.RngTotal rc →
    ∃ (seed : List Std.U8) (res : core.result.Result tacenta_kem.IncrementalKeyPair
        tacenta_kem.KemError) (rng' : R) (rest : List Std.U8),
      seed.length = 64 ∧
      tacenta_kem.IncrementalKeyPair.generate rc crc rng = ok (res, rng') ∧
      tacenta_kem.IncrementalKeyPair.generate byteRng byteCrc seed = ok (res, rest)

/-- A key pair generated from 64 bytes has a 64-byte header and a 1536-byte vector that
`validate_ek` accepts together, and decapsulates (`Ok` or `Err`) any two ciphertext halves of the
crate's lengths. -/
def LawGeneratedKeyPair : Prop :=
  ∀ (seed : List Std.U8) (kp : tacenta_kem.IncrementalKeyPair) (rest : List Std.U8),
    seed.length = 64 →
    tacenta_kem.IncrementalKeyPair.generate byteRng byteCrc seed = ok (.Ok kp, rest) →
    ∃ h v, tacenta_kem.IncrementalKeyPair.header kp = ok h ∧ h.length = 64 ∧
      tacenta_kem.IncrementalKeyPair.ek_vector kp = ok v ∧ v.length = 1536 ∧
      tacenta_kem.validate_ek (vecSlice h) (vecSlice v) = ok true ∧
      ∀ ct1 ct2 : Slice Std.U8, ct1.length = 1408 → ct2.length = 160 →
        ∃ r, tacenta_kem.IncrementalKeyPair.decapsulate kp ct1 ct2 = ok r

/-- The first half of encapsulation is determined by its header and 32 bytes of randomness: from any
source that answers and a 64-byte header, it returns, and what it returns is what it returns from the
byte stream of some 32 bytes. -/
def LawEncapsulate1Seeded : Prop :=
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (header : Slice Std.U8) (rng : R),
    Tacenta.SessionUnitBraidT1.RngTotal rc → header.length = 64 →
    ∃ (rnd : List Std.U8) (res : core.result.Result (tacenta_kem.EncapsState ×
        alloc.vec.Vec Std.U8 × Array Std.U8 32#usize) tacenta_kem.KemError) (rng' : R)
      (rest : List Std.U8),
      rnd.length = 32 ∧
      tacenta_kem.encapsulate1 rc crc header rng = ok (res, rng') ∧
      tacenta_kem.encapsulate1 byteRng byteCrc header rnd = ok (res, rest)

/-- The second half of encapsulation returns (`Ok` or `Err`) on a state the first half produced and a
vector of the crate's length. -/
def LawEncapsulate2Fresh : Prop :=
  ∀ (header : Slice Std.U8) (rnd : List Std.U8) (es : tacenta_kem.EncapsState)
    (ct1 : alloc.vec.Vec Std.U8) (ss : Array Std.U8 32#usize) (rest : List Std.U8),
    header.length = 64 → rnd.length = 32 →
    tacenta_kem.encapsulate1 byteRng byteCrc header rnd = ok (.Ok (es, ct1, ss), rest) →
    ∀ ekVector : Slice Std.U8, ekVector.length = 1536 →
      ∃ r, tacenta_kem.encapsulate2 es ekVector = ok r

/-- `validate_ek` returns on a header and a vector of the crate's lengths. -/
def LawValidateEkTotal : Prop :=
  ∀ header ekVector : Slice Std.U8, header.length = 64 → ekVector.length = 1536 →
    ∃ r, tacenta_kem.validate_ek header ekVector = ok r

/-- `validate_ek` accepts at most one hash for a seed and a vector: two 64-byte headers with the same
first 32 bytes that it accepts with the same vector are the same bytes. -/
def LawValidateEkUnique : Prop :=
  ∀ h1 h2 ekVector : Slice Std.U8, h1.length = 64 → h2.length = 64 → ekVector.length = 1536 →
    (sliceOf h1).take 32 = (sliceOf h2).take 32 →
    tacenta_kem.validate_ek h1 ekVector = ok true → tacenta_kem.validate_ek h2 ekVector = ok true →
    sliceOf h1 = sliceOf h2

/-- A clone answers `header`, `ek_vector`, `decapsulate` and `encapsulate2` as the original does.  It
is `KemCloneAgrees`, which mentions no KEM model, restated as a law. -/
def LawKemClone : Prop := Tacenta.SessionUnitBraidT3.KemCloneAgrees

/-! ### Over an interpretation -/

def LawKemConstantsShape (I : Interp) : Prop :=
  I.HEADER_LEN = ok 64#usize ∧ I.EK_VECTOR_LEN = ok 1536#usize ∧
    I.CT1_LEN = ok 1408#usize ∧ I.CT2_LEN = ok 160#usize

def LawGenerateSeededShape (I : Interp) : Prop :=
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (rng : R),
    Tacenta.SessionUnitBraidT1.RngTotal rc →
    ∃ (seed : List Std.U8) (res : core.result.Result I.IncrementalKeyPair tacenta_kem.KemError)
      (rng' : R) (rest : List Std.U8),
      seed.length = 64 ∧
      I.ikpGenerate rc crc rng = ok (res, rng') ∧
      I.ikpGenerate byteRng byteCrc seed = ok (res, rest)

def LawGeneratedKeyPairShape (I : Interp) : Prop :=
  ∀ (seed : List Std.U8) (kp : I.IncrementalKeyPair) (rest : List Std.U8),
    seed.length = 64 →
    I.ikpGenerate byteRng byteCrc seed = ok (.Ok kp, rest) →
    ∃ h v, I.ikpHeader kp = ok h ∧ h.length = 64 ∧
      I.ikpEkVector kp = ok v ∧ v.length = 1536 ∧
      I.validateEk (vecSlice h) (vecSlice v) = ok true ∧
      ∀ ct1 ct2 : Slice Std.U8, ct1.length = 1408 → ct2.length = 160 →
        ∃ r, I.ikpDecapsulate kp ct1 ct2 = ok r

def LawEncapsulate1SeededShape (I : Interp) : Prop :=
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (header : Slice Std.U8) (rng : R),
    Tacenta.SessionUnitBraidT1.RngTotal rc → header.length = 64 →
    ∃ (rnd : List Std.U8) (res : core.result.Result (I.EncapsState ×
        alloc.vec.Vec Std.U8 × Array Std.U8 32#usize) tacenta_kem.KemError) (rng' : R)
      (rest : List Std.U8),
      rnd.length = 32 ∧
      I.encapsulate1 rc crc header rng = ok (res, rng') ∧
      I.encapsulate1 byteRng byteCrc header rnd = ok (res, rest)

def LawEncapsulate2FreshShape (I : Interp) : Prop :=
  ∀ (header : Slice Std.U8) (rnd : List Std.U8) (es : I.EncapsState)
    (ct1 : alloc.vec.Vec Std.U8) (ss : Array Std.U8 32#usize) (rest : List Std.U8),
    header.length = 64 → rnd.length = 32 →
    I.encapsulate1 byteRng byteCrc header rnd = ok (.Ok (es, ct1, ss), rest) →
    ∀ ekVector : Slice Std.U8, ekVector.length = 1536 →
      ∃ r, I.encapsulate2 es ekVector = ok r

def LawValidateEkTotalShape (I : Interp) : Prop :=
  ∀ header ekVector : Slice Std.U8, header.length = 64 → ekVector.length = 1536 →
    ∃ r, I.validateEk header ekVector = ok r

def LawValidateEkUniqueShape (I : Interp) : Prop :=
  ∀ h1 h2 ekVector : Slice Std.U8, h1.length = 64 → h2.length = 64 → ekVector.length = 1536 →
    (sliceOf h1).take 32 = (sliceOf h2).take 32 →
    I.validateEk h1 ekVector = ok true → I.validateEk h2 ekVector = ok true →
    sliceOf h1 = sliceOf h2

/-- The eight laws over an interpretation. -/
structure WrapperKemLawsShape (I : Interp) : Prop where
  constants : LawKemConstantsShape I
  generateSeeded : LawGenerateSeededShape I
  generatedKeyPair : LawGeneratedKeyPairShape I
  encapsulate1Seeded : LawEncapsulate1SeededShape I
  encapsulate2Fresh : LawEncapsulate2FreshShape I
  validateEkTotal : LawValidateEkTotalShape I
  validateEkUnique : LawValidateEkUniqueShape I
  clone : KemCloneAgreesShape I

/-- The eight laws at the real constants. -/
def WrapperKemLaws : Prop := WrapperKemLawsShape Interp.real

theorem LawKemConstants_is : LawKemConstants ↔ LawKemConstantsShape Interp.real := Iff.rfl
theorem LawGenerateSeeded_is : LawGenerateSeeded ↔ LawGenerateSeededShape Interp.real := Iff.rfl
theorem LawGeneratedKeyPair_is : LawGeneratedKeyPair ↔ LawGeneratedKeyPairShape Interp.real :=
  Iff.rfl
theorem LawEncapsulate1Seeded_is : LawEncapsulate1Seeded ↔ LawEncapsulate1SeededShape Interp.real :=
  Iff.rfl
theorem LawEncapsulate2Fresh_is : LawEncapsulate2Fresh ↔ LawEncapsulate2FreshShape Interp.real :=
  Iff.rfl
theorem LawValidateEkTotal_is : LawValidateEkTotal ↔ LawValidateEkTotalShape Interp.real := Iff.rfl
theorem LawValidateEkUnique_is : LawValidateEkUnique ↔ LawValidateEkUniqueShape Interp.real :=
  Iff.rfl
theorem LawKemClone_is : LawKemClone ↔ KemCloneAgreesShape Interp.real := Iff.rfl

/-- The eight laws, each at the real constants, are the bundle `WrapperKemLaws`. -/
theorem wrapperKemLaws_iff :
    WrapperKemLaws ↔ LawKemConstants ∧ LawGenerateSeeded ∧ LawGeneratedKeyPair ∧
      LawEncapsulate1Seeded ∧ LawEncapsulate2Fresh ∧ LawValidateEkTotal ∧ LawValidateEkUnique ∧
      LawKemClone :=
  ⟨fun W => ⟨W.constants, W.generateSeeded, W.generatedKeyPair, W.encapsulate1Seeded,
      W.encapsulate2Fresh, W.validateEkTotal, W.validateEkUnique, W.clone⟩,
    fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩⟩

/-! ## The agreements at `wrapperKemOf I`, from the laws -/

section Agreements

variable {I : Interp}

theorem bytesOf_map_u8 (s : List Std.U8) : bytesOf (s.map u8) = s := by
  simp [bytesOf, List.map_map, Function.comp_def, toU8_u8]

theorem append_le_usize {a b : Bytes} (ha : a.length = 32) (hb : b.length = 32) :
    (a ++ b).length ≤ Usize.max := by
  rw [List.length_append, ha, hb]; exact le64

/-- Where `validate_ek` accepts `hek` after the seed, the model's hash is `hek`. -/
theorem hashEkOf_eq (W : WrapperKemLawsShape I) {ekSeed hek : Bytes} {ekVector : Slice Std.U8}
    (hs : ekSeed.length = 32) (hk : hek.length = 32) (hv : ekVector.length = 1536)
    (hval : I.validateEk (bytesSlice (ekSeed ++ hek)) ekVector = ok true) :
    hashEkOf I ekSeed (sliceOf ekVector) = hek := by
  have hex : ∃ hek' : Bytes, hek'.length = 32 ∧
      I.validateEk (bytesSlice (ekSeed ++ hek')) (bytesSlice (sliceOf ekVector)) = ok true :=
    ⟨hek, hk, by rw [bytesSlice_sliceOf]; exact hval⟩
  rw [hashEkOf, dif_pos hex]
  obtain ⟨hl', hv'⟩ := Classical.choose_spec hex
  generalize Classical.choose hex = c at hl' hv' ⊢
  rw [bytesSlice_sliceOf] at hv'
  have hu := W.validateEkUnique (bytesSlice (ekSeed ++ c))
    (bytesSlice (ekSeed ++ hek)) ekVector
    (by rw [length_bytesSlice_of _ (append_le_usize hs hl'), List.length_append, hs, hl'])
    (by rw [length_bytesSlice_of _ (append_le_usize hs hk), List.length_append, hs, hk]) hv
    (by rw [sliceOf_bytesSlice _ (append_le_usize hs hl'), sliceOf_bytesSlice _ (append_le_usize hs hk),
      List.take_left' hs, List.take_left' hs])
    hv' hval
  rw [sliceOf_bytesSlice _ (append_le_usize hs hl'), sliceOf_bytesSlice _ (append_le_usize hs hk)] at hu
  exact List.append_cancel_left hu

/-- Where the model's hash is a 32-byte `hek`, `validate_ek` accepts it after the seed. -/
theorem validate_of_hashEkOf {ekSeed hek : Bytes} {ekVector : Slice Std.U8}
    (hk : hek.length = 32) (he : hashEkOf I ekSeed (sliceOf ekVector) = hek) :
    I.validateEk (bytesSlice (ekSeed ++ hek)) ekVector = ok true := by
  unfold hashEkOf at he
  split at he
  · rename_i hex
    obtain ⟨-, hv'⟩ := Classical.choose_spec hex
    generalize Classical.choose hex = c at hv' he
    rw [he, bytesSlice_sliceOf] at hv'
    exact hv'
  · subst he; simp at hk

/-- The decapsulation clause, for a key pair generated from 64 bytes and the model's private part
holding those bytes. -/
theorem decaps_clause (W : WrapperKemLawsShape I) {seed : List Std.U8} {kp : I.IncrementalKeyPair}
    {rest : List Std.U8} (hlen : seed.length = 64)
    (hgen : I.ikpGenerate byteRng byteCrc seed = ok (.Ok kp, rest)) (dk : Bytes)
    (hdk : bytesOf dk = seed) :
    ∀ ct1 ct2 : Slice Std.U8, ct1.length = (wrapperKemOf I).ct1Size →
      ct2.length = (wrapperKemOf I).ct2Size →
      (∃ raw : Array Std.U8 32#usize, I.ikpDecapsulate kp ct1 ct2 = ok (.Ok raw) ∧
        (wrapperKemOf I).decaps dk (sliceOf ct1) (sliceOf ct2) = some (keyOf raw)) ∨
      ((∃ e, I.ikpDecapsulate kp ct1 ct2 = ok (.Err e)) ∧
        (wrapperKemOf I).decaps dk (sliceOf ct1) (sliceOf ct2) = none) := by
  intro ct1 ct2 h1 h2
  obtain ⟨h, v, -, -, -, -, -, hdec⟩ := W.generatedKeyPair seed kp rest hlen hgen
  obtain ⟨r, hr⟩ := hdec ct1 ct2 h1 h2
  cases r with
  | Ok raw =>
    refine Or.inl ⟨raw, hr, ?_⟩
    simp only [wrapperKemOf, hdk, hgen, bytesSlice_sliceOf, hr]
  | Err e =>
    refine Or.inr ⟨⟨e, hr⟩, ?_⟩
    simp only [wrapperKemOf, hdk, hgen, bytesSlice_sliceOf, hr]

/-- The second-half clause, for a state the first half produced from a header and 32 bytes, and an
encapsulation secret holding those bytes followed by the header. -/
theorem encaps2_clause (W : WrapperKemLawsShape I) {header : Slice Std.U8} {rnd : List Std.U8}
    {es : I.EncapsState} {ct1 : alloc.vec.Vec Std.U8} {ss : Array Std.U8 32#usize}
    {rest : List Std.U8} (hhl : header.length = 64) (hlen : rnd.length = 32)
    (henc : I.encapsulate1 byteRng byteCrc header rnd = ok (.Ok (es, ct1, ss), rest))
    (secret : Bytes) (hsec : bytesOf (secret.take 32) = rnd)
    (hhdr : bytesSlice (secret.drop 32) = header) (ekSeed : Bytes) :
    ∀ ekVector : Slice Std.U8, ekVector.length = (wrapperKemOf I).ekSize →
      (∃ ct2raw, I.encapsulate2 es ekVector = ok (.Ok ct2raw) ∧
        (wrapperKemOf I).encaps2 secret ekSeed (sliceOf ekVector) = some (vecOf ct2raw)) ∨
      ((∃ e, I.encapsulate2 es ekVector = ok (.Err e)) ∧
        (wrapperKemOf I).encaps2 secret ekSeed (sliceOf ekVector) = none) := by
  intro ekVector hv
  obtain ⟨r, hr⟩ := W.encapsulate2Fresh header rnd es ct1 ss rest hhl hlen henc ekVector hv
  cases r with
  | Ok ct2 =>
    refine Or.inl ⟨ct2, hr, ?_⟩
    simp only [wrapperKemOf, hsec, hhdr, henc, bytesSlice_sliceOf, hr]
  | Err e =>
    refine Or.inr ⟨⟨e, hr⟩, ?_⟩
    simp only [wrapperKemOf, hsec, hhdr, henc, bytesSlice_sliceOf, hr]

theorem kemLen_wrapperKemOf (W : WrapperKemLawsShape I) : KemLenShape I (wrapperKemOf I) := by
  obtain ⟨h1, h2, h3, h4⟩ := W.constants
  exact ⟨⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩, ⟨_, h3, rfl⟩, ⟨_, h4, rfl⟩⟩

theorem kemAgrees_wrapperKemOf (W : WrapperKemLawsShape I) : KemAgreesShape I (wrapperKemOf I) := by
  refine ⟨?_, ?_⟩
  · intro R rc crc rng hrt
    obtain ⟨seed, res, rng', rest, hlen, hreal, hbyte⟩ := W.generateSeeded rc crc rng hrt
    have hs : streamOf 64 (leNat (seed.map u8)) = seed := by
      have := streamOf_leNat seed
      rwa [hlen] at this
    refine ⟨rng', leNat (seed.map u8), ?_⟩
    cases res with
    | Ok kp =>
      obtain ⟨h, v, hh, hhl, hv, hvl, hval, -⟩ := W.generatedKeyPair seed kp rest hlen hbyte
      refine Or.inl ⟨kp, leBytes 64 (leNat (seed.map u8)), (vecOf h).take 32, vecOf v, hreal, ?_,
        ⟨h, hh, ?_⟩, ⟨v, hv, rfl⟩, ?_⟩
      · simp only [wrapperKemOf, hs, hbyte, hh, hv]
      · have hvl' : (vecSlice v).length = 1536 := hvl
        have hhl' : (vecOf h).length = 64 := by simpa [vecOf] using hhl
        have htk : ((vecOf h).take 32).length = 32 := by simp [hhl']
        have hdr : ((vecOf h).drop 32).length = 32 := by simp [hhl']
        have hval' : I.validateEk (bytesSlice ((vecOf h).take 32 ++ (vecOf h).drop 32)) (vecSlice v) =
            ok true := by
          rw [List.take_append_drop, ← sliceOf_vecSlice, bytesSlice_sliceOf]; exact hval
        have heq := hashEkOf_eq W htk hdr hvl' hval'
        show vecOf h = (vecOf h).take 32 ++ hashEkOf I ((vecOf h).take 32) (vecOf v)
        rw [← sliceOf_vecSlice v, heq, List.take_append_drop]
      · exact decaps_clause W hlen hbyte _ hs
    | Err e =>
      refine Or.inr ⟨⟨e, hreal⟩, ?_⟩
      simp only [wrapperKemOf, hs, hbyte]
  · intro R rc crc header rng hrt hhl
    have hhl' : header.length = 64 := hhl
    obtain ⟨rnd, res, rng', rest, hlen, hreal, hbyte⟩ :=
      W.encapsulate1Seeded rc crc header rng hrt hhl'
    have hs : streamOf 32 (leNat (rnd.map u8)) = rnd := by
      have := streamOf_leNat rnd
      rwa [hlen] at this
    refine ⟨rng', leNat (rnd.map u8), ?_⟩
    cases res with
    | Ok t =>
      obtain ⟨es, ct1raw, ssraw⟩ := t
      refine Or.inl ⟨es, ct1raw, ssraw, hreal, ?_⟩
      intro ekSeed hek _ hsplit
      have hheader : bytesSlice (ekSeed ++ hek) = header := by rw [← hsplit, bytesSlice_sliceOf]
      refine ⟨leBytes 32 (leNat (rnd.map u8)) ++ ekSeed ++ hek, ?_, ?_⟩
      · simp only [wrapperKemOf, hheader, hs, hbyte]
      · have hl := length_leBytes 32 (leNat (rnd.map u8))
        exact encaps2_clause W hhl' hlen hbyte _ (by rw [List.append_assoc, List.take_left' hl]; exact hs)
          (by rw [List.append_assoc, List.drop_left' hl]; exact hheader) ekSeed
    | Err e =>
      refine Or.inr ⟨⟨e, hreal⟩, fun ekSeed hek _ hsplit => ?_⟩
      have hheader : bytesSlice (ekSeed ++ hek) = header := by rw [← hsplit, bytesSlice_sliceOf]
      simp only [wrapperKemOf, hheader, hs, hbyte]

theorem validateEkAgrees_wrapperKemOf (W : WrapperKemLawsShape I) :
    ValidateEkAgreesShape I (wrapperKemOf I) := by
  intro header ekVector ekSeed hek hs hk hv hsplit
  have hv' : ekVector.length = 1536 := hv
  have hheader : bytesSlice (ekSeed ++ hek) = header := by rw [← hsplit, bytesSlice_sliceOf]
  have hlen : header.length = 64 := by
    have := congrArg List.length hsplit
    simp only [sliceOf, List.length_map, List.length_append, hs, hk] at this
    exact this
  obtain ⟨r, hr⟩ := W.validateEkTotal header ekVector hlen hv'
  refine ⟨r, hr, fun ht => ?_, fun he => ?_⟩
  · subst ht
    exact hashEkOf_eq W hs hk hv' (hheader ▸ hr)
  · have h := validate_of_hashEkOf hk he
    rw [hheader, hr] at h
    injection h

/-- The Braid refinement agreements about opaque constants hold at `wrapperKemOf I`: the four KEM
agreements from the eight laws, and the two KDF agreements as given. -/
theorem t3Agreements_wrapperKemOf (W : WrapperKemLawsShape I) (hkdf : HkdfAgreesShape I)
    (hmac : HmacAgreesShape I) : T3Agreements I (wrapperKemOf I) :=
  ⟨kemLen_wrapperKemOf W, kemAgrees_wrapperKemOf W, validateEkAgrees_wrapperKemOf W, W.clone, hkdf,
    hmac⟩

end Agreements

/-! ## At the real constants -/

theorem kemLenAgrees_wrapperKem (W : WrapperKemLaws) :
    Tacenta.SessionUnitBraidT3.KemLenAgrees wrapperKem :=
  kemLen_wrapperKemOf W

/-- **`KemAgreesFor` holds of the shipped wrapper read through byte views, under the eight laws.**
Both clauses are two-sided: the model's `keyGen`, `encaps1`, `encaps2` and `decaps` answer `none`
exactly where the wrapper's call returns `Err`. -/
theorem kemAgreesFor_wrapperKem (W : WrapperKemLaws) :
    Tacenta.SessionUnitBraidT3.KemAgreesFor wrapperKem :=
  kemAgrees_wrapperKemOf W

theorem validateEkAgrees_wrapperKem (W : WrapperKemLaws) :
    Tacenta.SessionUnitBraidT3.ValidateEkAgrees wrapperKem :=
  validateEkAgrees_wrapperKemOf W

/-- `KemCloneAgrees` mentions no KEM model; it is the law `LawKemClone`, restated. -/
theorem kemCloneAgrees_wrapperKem (W : WrapperKemLaws) : Tacenta.SessionUnitBraidT3.KemCloneAgrees :=
  W.clone

/-- A key pair the wrapper generates from any source that answers refines, at `wrapperKem`, the
model's private part of the 64 bytes `LawGenerateSeeded` gives: it decapsulates like
`wrapperKem.decaps`, refusing exactly where it refuses. -/
theorem keyPairRefines_wrapperKem (W : WrapperKemLaws) {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (rng rng' : R) (kp : tacenta_kem.IncrementalKeyPair)
    (hrt : Tacenta.SessionUnitBraidT1.RngTotal rc)
    (hgen : tacenta_kem.IncrementalKeyPair.generate rc crc rng = ok (.Ok kp, rng')) :
    ∃ dk, Tacenta.SessionUnitBraidT3.KeyPairRefines wrapperKem kp dk := by
  obtain ⟨seed, res, rng'', rest, hlen, hreal, hbyte⟩ := W.generateSeeded rc crc rng hrt
  have h := hgen.symm.trans hreal
  cases h
  exact ⟨seed.map u8, decaps_clause W hlen hbyte _ (bytesOf_map_u8 seed)⟩

/-- An encapsulation state the wrapper's first half produces from any source that answers, on a
64-byte header `ekSeed ++ hek`, refines at `wrapperKem` the model's secret of the 32 bytes
`LawEncapsulate1Seeded` gives followed by the header bytes: it finishes like `wrapperKem.encaps2`, refusing
exactly where it refuses. -/
theorem encapsRefines_wrapperKem (W : WrapperKemLaws) {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (header : Slice Std.U8) (rng rng' : R)
    (es : tacenta_kem.EncapsState) (ct1 : alloc.vec.Vec Std.U8) (ss : Array Std.U8 32#usize)
    (hrt : Tacenta.SessionUnitBraidT1.RngTotal rc) (hhl : header.length = 64) (ekSeed hek : Bytes)
    (hsplit : sliceOf header = ekSeed ++ hek)
    (henc : tacenta_kem.encapsulate1 rc crc header rng = ok (.Ok (es, ct1, ss), rng')) :
    ∃ secret, Tacenta.SessionUnitBraidT3.EncapsRefines wrapperKem es ekSeed secret := by
  obtain ⟨rnd, res, rng'', rest, hlen, hreal, hbyte⟩ := W.encapsulate1Seeded rc crc header rng hrt hhl
  have h := henc.symm.trans hreal
  cases h
  have hl : (rnd.map u8).length = 32 := by rw [List.length_map, hlen]
  refine ⟨rnd.map u8 ++ ekSeed ++ hek, encaps2_clause W hhl hlen hbyte _ ?_ ?_ ekSeed⟩
  · rw [List.append_assoc, List.take_left' hl, bytesOf_map_u8]
  · rw [List.append_assoc, List.drop_left' hl, ← hsplit, bytesSlice_sliceOf]

/-- The Braid refinement agreements about opaque constants at `wrapperKem`, from the eight laws and
the two KDF agreements. -/
theorem t3Agreements_wrapperKem (W : WrapperKemLaws)
    (hkdf : Tacenta.SessionUnitBraidT3.BraidHkdfAgrees)
    (hmac : Tacenta.SessionUnitBraidT3.BraidHmacAgrees) : T3Agreements Interp.real wrapperKem :=
  t3Agreements_wrapperKemOf W hkdf hmac

/-! ## The decrypt refinement's hypotheses together, at `wrapperKem` -/

open Tacenta.UnitLifecycleDecryptScreen
open Tacenta.UnitLifecycleDecryptRatchetScreen (DhViewShape DhCodecOfShape ZeroizeRoundTripShapes)
open Tacenta.UnitHeadroomInvariant (ValidKeyShape OptionEqU64Shape optionEqImpl)

/-- The laws of `DecryptJointLawsShape` with its `agreements` field replaced by the two KDF agreements
and the eight wrapper laws: the bundle the decrypt refinement's hypotheses need at `wrapperKemOf I`.
The other fourteen fields are `DecryptJointLawsShape`'s, field for field. -/
structure DecryptWrapperLawsShape (I : Interp) (dh : DhViewShape I)
    (oeq : {T : Type} → core.cmp.PartialEq T T → Option T → Option T → Result Bool) : Prop where
  dhCodec : DhCodecShape I
  dhAgree : DhAgreeShape I
  aeadOpen : AeadOpenShape I
  viewInjective : Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey
  codec : DhCodecOfShape I dh
  braid : BraidReceiveAxiom I
  triple : TripleReceiveAxiom I
  messageKeyMaterial : MessageKeyMaterialRoundTripShape I
  laws : StdLaws I
  truncatePrefix : TruncatePrefixShape I
  derivedKeys : Nonempty (ZeroizingModelShape I DerivedZ)
  hkdf : HkdfAgreesShape I
  hmac : HmacAgreesShape I
  kem : WrapperKemLawsShape I
  roundTrips : ZeroizeRoundTripShapes I
  validKey : ValidKeyShape I
  optionEq : OptionEqU64Shape oeq

/-- The wrapper bundle gives the joint bundle at `wrapperKemOf I`: the fourteen shared fields as they
are, and the agreements from the eight laws and the two KDF agreements. -/
theorem DecryptWrapperLawsShape.toJoint {I : Interp} {dh : DhViewShape I}
    {oeq : {T : Type} → core.cmp.PartialEq T T → Option T → Option T → Result Bool}
    (L : DecryptWrapperLawsShape I dh oeq) : DecryptJointLawsShape I dh (wrapperKemOf I) oeq where
  dhCodec := L.dhCodec
  dhAgree := L.dhAgree
  aeadOpen := L.aeadOpen
  viewInjective := L.viewInjective
  codec := L.codec
  braid := L.braid
  triple := L.triple
  messageKeyMaterial := L.messageKeyMaterial
  laws := L.laws
  truncatePrefix := L.truncatePrefix
  derivedKeys := L.derivedKeys
  agreements := t3Agreements_wrapperKemOf L.kem L.hkdf L.hmac
  roundTrips := L.roundTrips
  validKey := L.validKey
  optionEq := L.optionEq

/-- The wrapper bundle at the real constants, the real `Option::eq` and a DH view. -/
def DecryptWrapperLaws (dh : Tacenta.UnitLifecycleT3.DhView) : Prop :=
  DecryptWrapperLawsShape Interp.real ⟨dh.privateKey, dh.publicKey⟩
    @core.option.Option.Insts.CoreCmpPartialEqOption.eq

theorem decryptWrapperLaws_joint (dh : Tacenta.UnitLifecycleT3.DhView) (L : DecryptWrapperLaws dh) :
    DecryptJointLaws wrapperKem dh :=
  L.toJoint

/-- **The hypotheses of the decrypt refinement hold together at the real constants with the Braid KEM
model read off the shipped wrapper.**  `decrypt_hypotheses_jointly_satisfiable` at `K := wrapperKem`,
with its law bundle's `agreements` field (the KEM agreements at a free `K`) replaced by the eight laws
about the wrapper's opaque functions and the two KDF agreements: under `DecryptWrapperLaws dh`, there
are an oracle whose Braid KEM model is `wrapperKem`, a session that passes `Session::invariant`, a
related model session, a message that decodes on both sides and is a ratchet frame, and a byte-stream
source, at which every hypothesis of `decrypt_ratchet_refines_complete` holds, for every codeword
view.  The witness is `decrypt_hypotheses_jointly_satisfiable`'s: its Braid is in `KeysUnsampled`, so
no state at it holds a key pair or an encapsulation state. -/
theorem decrypt_hypotheses_jointly_satisfiable_at_wrapperKem (dh : Tacenta.UnitLifecycleT3.DhView)
    (L : DecryptWrapperLaws dh) :
    ∃ (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
      (model : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : List Std.U8),
      oracle.braidKem = wrapperKem ∧
      (∃ decoded, tacenta_wire.decode_message message = ok (.Ok decoded)) ∧
      (∃ composite ciphertext,
        Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
          .ok (composite, ciphertext)) ∧
      Model.Lifecycle.messageType (Tacenta.UnitLifecycleT3.sliceOf message) = some .ratchet ∧
      ∀ view : Model.Lifecycle.CodewordView,
        DecryptHypotheses byteRng byteCrc Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh view
          oracle real model message rng :=
  decrypt_hypotheses_jointly_satisfiable wrapperKem dh (decryptWrapperLaws_joint dh L)

/-! ## One interpretation satisfies the wrapper bundle

`Interp.modelShipped` (`UnitLifecycleDecryptScreen.lean`) already has the crate's four length
constants.  Its wrapper functions satisfy the eight laws: key generation and the first half of
encapsulation ignore the source, so each is determined by any bytes; the header and vector have 64 and
1536 bytes and validate; `validate_ek` compares a hash, so it accepts at most one; every call returns.
So `wrapperKemOf Interp.modelShipped` meets the agreements by the same proof as `wrapperKem`. -/

theorem modelShipped_wrapperKemLaws : WrapperKemLawsShape Interp.modelShipped where
  constants := modelShipped_sizes
  generateSeeded := fun _ _ _ _ => ⟨List.replicate 64 0#u8, _, _, _, by simp, rfl, rfl⟩
  generatedKeyPair := by
    intro seed kp rest _ hgen
    have h : (ok (core.result.Result.Ok (0 : ℕ), seed) :
        Result (core.result.Result ℕ tacenta_kem.KemError × List Std.U8)) = ok (.Ok kp, rest) := hgen
    cases h
    have hs : (seedOf 0).length = 32 := by rw [seedOf, List.length_replicate]
    refine ⟨_, _, rfl, ?_, rfl, ?_, ?_, fun _ _ _ _ => ⟨_, rfl⟩⟩
    · show (vecOfBytes (seedOf 0 ++ shippedSizeKem.hashEk (seedOf 0) (ekVecShipped 0)) _).length = 64
      rw [length_vecOfBytes]
      simp [seedOf, shippedSizeKem, Model.Braid.toyKem]
    · show (vecOfBytes (ekVecShipped 0) _).length = 1536
      rw [length_vecOfBytes, ekVecShipped, List.length_replicate]
    · show ok (decide (shippedSizeKem.hashEk ((sliceOf (vecSlice _)).take 32) (sliceOf (vecSlice _)) =
        (sliceOf (vecSlice _)).drop 32)) = ok true
      rw [sliceOf_vecSlice, sliceOf_vecSlice, vecOf_vecOfBytes, vecOf_vecOfBytes, List.take_left' hs,
        List.drop_left' hs]
      simp
  encapsulate1Seeded := fun _ _ _ _ _ _ => ⟨List.replicate 32 0#u8, _, _, _, by simp, rfl, rfl⟩
  encapsulate2Fresh := fun _ _ _ _ _ _ _ _ _ _ _ => ⟨_, rfl⟩
  validateEkTotal := fun _ _ _ _ => ⟨_, rfl⟩
  validateEkUnique := by
    intro h1 h2 v _ _ _ htake hv1 hv2
    have e1 : shippedSizeKem.hashEk ((sliceOf h1).take 32) (sliceOf v) = (sliceOf h1).drop 32 := by
      have h : ok (decide (shippedSizeKem.hashEk ((sliceOf h1).take 32) (sliceOf v) =
          (sliceOf h1).drop 32)) = ok true := hv1
      injection h with h
      exact of_decide_eq_true h
    have e2 : shippedSizeKem.hashEk ((sliceOf h2).take 32) (sliceOf v) = (sliceOf h2).drop 32 := by
      have h : ok (decide (shippedSizeKem.hashEk ((sliceOf h2).take 32) (sliceOf v) =
          (sliceOf h2).drop 32)) = ok true := hv2
      injection h with h
      exact of_decide_eq_true h
    rw [← List.take_append_drop 32 (sliceOf h1), ← List.take_append_drop 32 (sliceOf h2), ← e1, ← e2,
      htake]
  clone := modelShipped_kemClone

/-- **The wrapper bundle has a model.**  `Interp.modelShipped`, its view `viewShipped` and
`optionEqImpl` satisfy every field of `DecryptWrapperLawsShape` together: the fourteen fields shared
with `DecryptJointLawsShape` and the two KDF agreements as `decrypt_joint_laws_model_at_shipped_sizes`
gives them, and the eight wrapper laws by `modelShipped_wrapperKemLaws`. -/
theorem decrypt_wrapper_laws_model :
    DecryptWrapperLawsShape Interp.modelShipped viewShipped @optionEqImpl where
  dhCodec := decrypt_joint_laws_model_at_shipped_sizes.dhCodec
  dhAgree := decrypt_joint_laws_model_at_shipped_sizes.dhAgree
  aeadOpen := decrypt_joint_laws_model_at_shipped_sizes.aeadOpen
  viewInjective := decrypt_joint_laws_model_at_shipped_sizes.viewInjective
  codec := decrypt_joint_laws_model_at_shipped_sizes.codec
  braid := decrypt_joint_laws_model_at_shipped_sizes.braid
  triple := decrypt_joint_laws_model_at_shipped_sizes.triple
  messageKeyMaterial := decrypt_joint_laws_model_at_shipped_sizes.messageKeyMaterial
  laws := decrypt_joint_laws_model_at_shipped_sizes.laws
  truncatePrefix := decrypt_joint_laws_model_at_shipped_sizes.truncatePrefix
  derivedKeys := decrypt_joint_laws_model_at_shipped_sizes.derivedKeys
  hkdf := decrypt_joint_laws_model_at_shipped_sizes.agreements.hkdf
  hmac := decrypt_joint_laws_model_at_shipped_sizes.agreements.hmac
  kem := modelShipped_wrapperKemLaws
  roundTrips := decrypt_joint_laws_model_at_shipped_sizes.roundTrips
  validKey := decrypt_joint_laws_model_at_shipped_sizes.validKey
  optionEq := decrypt_joint_laws_model_at_shipped_sizes.optionEq

/-- In that interpretation the joint bundle holds at the KEM model read off its wrapper functions,
`wrapperKemOf Interp.modelShipped`, by the proof that gives the agreements at `wrapperKem`. -/
theorem decrypt_joint_laws_model_at_wrapperKemOf :
    DecryptJointLawsShape Interp.modelShipped viewShipped (wrapperKemOf Interp.modelShipped)
      @optionEqImpl :=
  decrypt_wrapper_laws_model.toJoint

/-- The wrapper bundle and the joint bundle at the KEM model read off the wrapper functions, in one
interpretation whose four KEM length constants are the crate's. -/
theorem decrypt_wrapper_laws_satisfiable :
    ∃ (I : Interp) (dh : DhViewShape I)
      (oeq : {T : Type} → core.cmp.PartialEq T T → Option T → Option T → Result Bool),
      I.HEADER_LEN = ok 64#usize ∧ I.EK_VECTOR_LEN = ok 1536#usize ∧ I.CT1_LEN = ok 1408#usize ∧
      I.CT2_LEN = ok 160#usize ∧ DecryptWrapperLawsShape I dh oeq ∧
      DecryptJointLawsShape I dh (wrapperKemOf I) oeq :=
  ⟨Interp.modelShipped, viewShipped, @optionEqImpl, rfl, rfl, rfl, rfl, decrypt_wrapper_laws_model,
    decrypt_joint_laws_model_at_wrapperKemOf⟩

end Tacenta.UnitKemWrapperModel

/-! ## Pins

The axiom list and the statement of each result, and the bodies of the model KEM, its hash, the eight
laws, the two law bundles and the byte views, held by the build.  `attest.py` requires them
(`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`, `REQUIRED_PRINT_FORM`).  No result here lists a
compiler-trust axiom. -/

/--
info: 'Tacenta.UnitKemWrapperModel.toU8_u8' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.toU8_u8

/--
info: Tacenta.UnitKemWrapperModel.toU8_u8 : ∀ (x : U8), toU8 (u8 x) = x
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.toU8_u8

/--
info: 'Tacenta.UnitKemWrapperModel.bytesOf_sliceOf' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.bytesOf_sliceOf

/--
info: Tacenta.UnitKemWrapperModel.bytesOf_sliceOf : ∀ (s : Slice U8), bytesOf (sliceOf s) = ↑s
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.bytesOf_sliceOf

/--
info: 'Tacenta.UnitKemWrapperModel.length_bytesOf_le' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.length_bytesOf_le

/--
info: @Tacenta.UnitKemWrapperModel.length_bytesOf_le : ∀ {l : Bytes},
  List.length l ≤ Usize.max → (bytesOf l).length ≤ Usize.max
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.length_bytesOf_le

/--
info: 'Tacenta.UnitKemWrapperModel.length_nil_le' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.length_nil_le

/--
info: Tacenta.UnitKemWrapperModel.length_nil_le : [].length ≤ Usize.max
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.length_nil_le

/--
info: 'Tacenta.UnitKemWrapperModel.bytesSlice_sliceOf' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.bytesSlice_sliceOf

/--
info: Tacenta.UnitKemWrapperModel.bytesSlice_sliceOf : ∀ (s : Slice U8),
  Tacenta.UnitKemWrapperModel.bytesSlice (sliceOf s) = s
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.bytesSlice_sliceOf

/--
info: 'Tacenta.UnitKemWrapperModel.length_bytesSlice_of' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.length_bytesSlice_of

/--
info: Tacenta.UnitKemWrapperModel.length_bytesSlice_of : ∀ (l : Bytes),
  List.length l ≤ Usize.max → (Tacenta.UnitKemWrapperModel.bytesSlice l).length = List.length l
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.length_bytesSlice_of

/--
info: 'Tacenta.UnitKemWrapperModel.sliceOf_bytesSlice' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.sliceOf_bytesSlice

/--
info: Tacenta.UnitKemWrapperModel.sliceOf_bytesSlice : ∀ (l : Bytes),
  List.length l ≤ Usize.max → sliceOf (Tacenta.UnitKemWrapperModel.bytesSlice l) = l
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.sliceOf_bytesSlice

/--
info: 'Tacenta.UnitKemWrapperModel.sliceOf_vecSlice' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.sliceOf_vecSlice

/--
info: Tacenta.UnitKemWrapperModel.sliceOf_vecSlice : ∀ (v : alloc.vec.Vec U8),
  sliceOf (Tacenta.UnitKemWrapperModel.vecSlice v) = vecOf v
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.sliceOf_vecSlice

/--
info: 'Tacenta.UnitKemWrapperModel.length_leBytes' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.length_leBytes

/--
info: Tacenta.UnitKemWrapperModel.length_leBytes : ∀ (k n : ℕ), List.length (Tacenta.UnitKemWrapperModel.leBytes k n) = k
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.length_leBytes

/--
info: 'Tacenta.UnitKemWrapperModel.leBytes_leNat' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.leBytes_leNat

/--
info: Tacenta.UnitKemWrapperModel.leBytes_leNat : ∀ (l : Bytes),
  Tacenta.UnitKemWrapperModel.leBytes (List.length l) (Tacenta.UnitKemWrapperModel.leNat l) = l
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.leBytes_leNat

/--
info: 'Tacenta.UnitKemWrapperModel.streamOf_leNat' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.streamOf_leNat

/--
info: Tacenta.UnitKemWrapperModel.streamOf_leNat : ∀ (s : List U8),
  Tacenta.UnitKemWrapperModel.streamOf s.length (Tacenta.UnitKemWrapperModel.leNat (List.map u8 s)) = s
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.streamOf_leNat

/--
info: 'Tacenta.UnitKemWrapperModel.LawKemConstants_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.LawKemConstants_is

/--
info: Tacenta.UnitKemWrapperModel.LawKemConstants_is : Tacenta.UnitKemWrapperModel.LawKemConstants ↔
  Tacenta.UnitKemWrapperModel.LawKemConstantsShape Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.LawKemConstants_is

/--
info: 'Tacenta.UnitKemWrapperModel.LawGenerateSeeded_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.LawGenerateSeeded_is

/--
info: Tacenta.UnitKemWrapperModel.LawGenerateSeeded_is : Tacenta.UnitKemWrapperModel.LawGenerateSeeded ↔
  Tacenta.UnitKemWrapperModel.LawGenerateSeededShape Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.LawGenerateSeeded_is

/--
info: 'Tacenta.UnitKemWrapperModel.LawGeneratedKeyPair_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.LawGeneratedKeyPair_is

/--
info: Tacenta.UnitKemWrapperModel.LawGeneratedKeyPair_is : Tacenta.UnitKemWrapperModel.LawGeneratedKeyPair ↔
  Tacenta.UnitKemWrapperModel.LawGeneratedKeyPairShape Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.LawGeneratedKeyPair_is

/--
info: 'Tacenta.UnitKemWrapperModel.LawEncapsulate1Seeded_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.LawEncapsulate1Seeded_is

/--
info: Tacenta.UnitKemWrapperModel.LawEncapsulate1Seeded_is : Tacenta.UnitKemWrapperModel.LawEncapsulate1Seeded ↔
  Tacenta.UnitKemWrapperModel.LawEncapsulate1SeededShape Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.LawEncapsulate1Seeded_is

/--
info: 'Tacenta.UnitKemWrapperModel.LawEncapsulate2Fresh_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.LawEncapsulate2Fresh_is

/--
info: Tacenta.UnitKemWrapperModel.LawEncapsulate2Fresh_is : Tacenta.UnitKemWrapperModel.LawEncapsulate2Fresh ↔
  Tacenta.UnitKemWrapperModel.LawEncapsulate2FreshShape Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.LawEncapsulate2Fresh_is

/--
info: 'Tacenta.UnitKemWrapperModel.LawValidateEkTotal_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.LawValidateEkTotal_is

/--
info: Tacenta.UnitKemWrapperModel.LawValidateEkTotal_is : Tacenta.UnitKemWrapperModel.LawValidateEkTotal ↔
  Tacenta.UnitKemWrapperModel.LawValidateEkTotalShape Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.LawValidateEkTotal_is

/--
info: 'Tacenta.UnitKemWrapperModel.LawValidateEkUnique_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.LawValidateEkUnique_is

/--
info: Tacenta.UnitKemWrapperModel.LawValidateEkUnique_is : Tacenta.UnitKemWrapperModel.LawValidateEkUnique ↔
  Tacenta.UnitKemWrapperModel.LawValidateEkUniqueShape Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.LawValidateEkUnique_is

/--
info: 'Tacenta.UnitKemWrapperModel.LawKemClone_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.LawKemClone_is

/--
info: Tacenta.UnitKemWrapperModel.LawKemClone_is : Tacenta.UnitKemWrapperModel.LawKemClone ↔ KemCloneAgreesShape Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.LawKemClone_is

/--
info: 'Tacenta.UnitKemWrapperModel.wrapperKemLaws_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.wrapperKemLaws_iff

/--
info: Tacenta.UnitKemWrapperModel.wrapperKemLaws_iff : Tacenta.UnitKemWrapperModel.WrapperKemLaws ↔
  Tacenta.UnitKemWrapperModel.LawKemConstants ∧
    Tacenta.UnitKemWrapperModel.LawGenerateSeeded ∧
      Tacenta.UnitKemWrapperModel.LawGeneratedKeyPair ∧
        Tacenta.UnitKemWrapperModel.LawEncapsulate1Seeded ∧
          Tacenta.UnitKemWrapperModel.LawEncapsulate2Fresh ∧
            Tacenta.UnitKemWrapperModel.LawValidateEkTotal ∧
              Tacenta.UnitKemWrapperModel.LawValidateEkUnique ∧ Tacenta.UnitKemWrapperModel.LawKemClone
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.wrapperKemLaws_iff

/--
info: 'Tacenta.UnitKemWrapperModel.bytesOf_map_u8' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.bytesOf_map_u8

/--
info: Tacenta.UnitKemWrapperModel.bytesOf_map_u8 : ∀ (s : List U8), bytesOf (List.map u8 s) = s
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.bytesOf_map_u8

/--
info: 'Tacenta.UnitKemWrapperModel.append_le_usize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.append_le_usize

/--
info: @Tacenta.UnitKemWrapperModel.append_le_usize : ∀ {a b : Bytes},
  List.length a = 32 → List.length b = 32 → List.length (a ++ b) ≤ Usize.max
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.append_le_usize

/--
info: 'Tacenta.UnitKemWrapperModel.hashEkOf_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.hashEkOf_eq

/--
info: @Tacenta.UnitKemWrapperModel.hashEkOf_eq : ∀ {I : Interp},
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape I →
    ∀ {ekSeed hek : Bytes} {ekVector : Slice U8},
      List.length ekSeed = 32 →
        List.length hek = 32 →
          ekVector.length = 1536 →
            I.validateEk (Tacenta.UnitKemWrapperModel.bytesSlice (ekSeed ++ hek)) ekVector = ok true →
              Tacenta.UnitKemWrapperModel.hashEkOf I ekSeed (sliceOf ekVector) = hek
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.hashEkOf_eq

/--
info: 'Tacenta.UnitKemWrapperModel.validate_of_hashEkOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.validate_of_hashEkOf

/--
info: @Tacenta.UnitKemWrapperModel.validate_of_hashEkOf : ∀ {I : Interp} {ekSeed hek : Bytes} {ekVector : Slice U8},
  List.length hek = 32 →
    Tacenta.UnitKemWrapperModel.hashEkOf I ekSeed (sliceOf ekVector) = hek →
      I.validateEk (Tacenta.UnitKemWrapperModel.bytesSlice (ekSeed ++ hek)) ekVector = ok true
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.validate_of_hashEkOf

/--
info: 'Tacenta.UnitKemWrapperModel.decaps_clause' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.decaps_clause

/--
info: @Tacenta.UnitKemWrapperModel.decaps_clause : ∀ {I : Interp},
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape I →
    ∀ {seed : List U8} {kp : I.IncrementalKeyPair} {rest : List U8},
      seed.length = 64 →
        I.ikpGenerate byteRng byteCrc seed = ok (core.result.Result.Ok kp, rest) →
          ∀ (dk : Bytes),
            bytesOf dk = seed →
              ∀ (ct1 ct2 : Slice U8),
                ct1.length = (Tacenta.UnitKemWrapperModel.wrapperKemOf I).ct1Size →
                  ct2.length = (Tacenta.UnitKemWrapperModel.wrapperKemOf I).ct2Size →
                    (∃ raw,
                        I.ikpDecapsulate kp ct1 ct2 = ok (core.result.Result.Ok raw) ∧
                          (Tacenta.UnitKemWrapperModel.wrapperKemOf I).decaps dk (sliceOf ct1) (sliceOf ct2) =
                            some (keyOf raw)) ∨
                      (∃ e, I.ikpDecapsulate kp ct1 ct2 = ok (core.result.Result.Err e)) ∧
                        (Tacenta.UnitKemWrapperModel.wrapperKemOf I).decaps dk (sliceOf ct1) (sliceOf ct2) = none
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.decaps_clause

/--
info: 'Tacenta.UnitKemWrapperModel.encaps2_clause' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.encaps2_clause

/--
info: @Tacenta.UnitKemWrapperModel.encaps2_clause : ∀ {I : Interp},
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape I →
    ∀ {header : Slice U8} {rnd : List U8} {es : I.EncapsState} {ct1 : alloc.vec.Vec U8} {ss : Std.Array U8 32#usize}
      {rest : List U8},
      header.length = 64 →
        rnd.length = 32 →
          I.encapsulate1 byteRng byteCrc header rnd = ok (core.result.Result.Ok (es, ct1, ss), rest) →
            ∀ (secret : Bytes),
              bytesOf (List.take 32 secret) = rnd →
                Tacenta.UnitKemWrapperModel.bytesSlice (List.drop 32 secret) = header →
                  ∀ (ekSeed : Bytes) (ekVector : Slice U8),
                    ekVector.length = (Tacenta.UnitKemWrapperModel.wrapperKemOf I).ekSize →
                      (∃ ct2raw,
                          I.encapsulate2 es ekVector = ok (core.result.Result.Ok ct2raw) ∧
                            (Tacenta.UnitKemWrapperModel.wrapperKemOf I).encaps2 secret ekSeed (sliceOf ekVector) =
                              some (vecOf ct2raw)) ∨
                        (∃ e, I.encapsulate2 es ekVector = ok (core.result.Result.Err e)) ∧
                          (Tacenta.UnitKemWrapperModel.wrapperKemOf I).encaps2 secret ekSeed (sliceOf ekVector) = none
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.encaps2_clause

/--
info: 'Tacenta.UnitKemWrapperModel.kemLen_wrapperKemOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.kemLen_wrapperKemOf

/--
info: @Tacenta.UnitKemWrapperModel.kemLen_wrapperKemOf : ∀ {I : Interp},
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape I → KemLenShape I (Tacenta.UnitKemWrapperModel.wrapperKemOf I)
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.kemLen_wrapperKemOf

/--
info: 'Tacenta.UnitKemWrapperModel.kemAgrees_wrapperKemOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.kemAgrees_wrapperKemOf

/--
info: @Tacenta.UnitKemWrapperModel.kemAgrees_wrapperKemOf : ∀ {I : Interp},
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape I → KemAgreesShape I (Tacenta.UnitKemWrapperModel.wrapperKemOf I)
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.kemAgrees_wrapperKemOf

/--
info: 'Tacenta.UnitKemWrapperModel.validateEkAgrees_wrapperKemOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.validateEkAgrees_wrapperKemOf

/--
info: @Tacenta.UnitKemWrapperModel.validateEkAgrees_wrapperKemOf : ∀ {I : Interp},
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape I →
    ValidateEkAgreesShape I (Tacenta.UnitKemWrapperModel.wrapperKemOf I)
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.validateEkAgrees_wrapperKemOf

/--
info: 'Tacenta.UnitKemWrapperModel.t3Agreements_wrapperKemOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.t3Agreements_wrapperKemOf

/--
info: @Tacenta.UnitKemWrapperModel.t3Agreements_wrapperKemOf : ∀ {I : Interp},
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape I →
    HkdfAgreesShape I → HmacAgreesShape I → T3Agreements I (Tacenta.UnitKemWrapperModel.wrapperKemOf I)
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.t3Agreements_wrapperKemOf

/--
info: 'Tacenta.UnitKemWrapperModel.kemLenAgrees_wrapperKem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.kemLenAgrees_wrapperKem

/--
info: Tacenta.UnitKemWrapperModel.kemLenAgrees_wrapperKem : Tacenta.UnitKemWrapperModel.WrapperKemLaws →
  Tacenta.SessionUnitBraidT3.KemLenAgrees Tacenta.UnitKemWrapperModel.wrapperKem
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.kemLenAgrees_wrapperKem

/--
info: 'Tacenta.UnitKemWrapperModel.kemAgreesFor_wrapperKem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.kemAgreesFor_wrapperKem

/--
info: Tacenta.UnitKemWrapperModel.kemAgreesFor_wrapperKem : Tacenta.UnitKemWrapperModel.WrapperKemLaws →
  Tacenta.SessionUnitBraidT3.KemAgreesFor Tacenta.UnitKemWrapperModel.wrapperKem
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.kemAgreesFor_wrapperKem

/--
info: 'Tacenta.UnitKemWrapperModel.validateEkAgrees_wrapperKem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.validateEkAgrees_wrapperKem

/--
info: Tacenta.UnitKemWrapperModel.validateEkAgrees_wrapperKem : Tacenta.UnitKemWrapperModel.WrapperKemLaws →
  Tacenta.SessionUnitBraidT3.ValidateEkAgrees Tacenta.UnitKemWrapperModel.wrapperKem
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.validateEkAgrees_wrapperKem

/--
info: 'Tacenta.UnitKemWrapperModel.kemCloneAgrees_wrapperKem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.kemCloneAgrees_wrapperKem

/--
info: Tacenta.UnitKemWrapperModel.kemCloneAgrees_wrapperKem : Tacenta.UnitKemWrapperModel.WrapperKemLaws →
  Tacenta.SessionUnitBraidT3.KemCloneAgrees
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.kemCloneAgrees_wrapperKem

/--
info: 'Tacenta.UnitKemWrapperModel.keyPairRefines_wrapperKem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.keyPairRefines_wrapperKem

/--
info: Tacenta.UnitKemWrapperModel.keyPairRefines_wrapperKem : Tacenta.UnitKemWrapperModel.WrapperKemLaws →
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (rng rng' : R)
    (kp : tacenta_kem.IncrementalKeyPair),
    Tacenta.SessionUnitBraidT1.RngTotal rc →
      tacenta_kem.IncrementalKeyPair.generate rc crc rng = ok (core.result.Result.Ok kp, rng') →
        ∃ dk, Tacenta.SessionUnitBraidT3.KeyPairRefines Tacenta.UnitKemWrapperModel.wrapperKem kp dk
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.keyPairRefines_wrapperKem

/--
info: 'Tacenta.UnitKemWrapperModel.encapsRefines_wrapperKem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.encapsRefines_wrapperKem

/--
info: Tacenta.UnitKemWrapperModel.encapsRefines_wrapperKem : Tacenta.UnitKemWrapperModel.WrapperKemLaws →
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (header : Slice U8) (rng rng' : R)
    (es : tacenta_kem.EncapsState) (ct1 : alloc.vec.Vec U8) (ss : Std.Array U8 32#usize),
    Tacenta.SessionUnitBraidT1.RngTotal rc →
      header.length = 64 →
        ∀ (ekSeed hek : Bytes),
          sliceOf header = ekSeed ++ hek →
            tacenta_kem.encapsulate1 rc crc header rng = ok (core.result.Result.Ok (es, ct1, ss), rng') →
              ∃ secret, Tacenta.SessionUnitBraidT3.EncapsRefines Tacenta.UnitKemWrapperModel.wrapperKem es ekSeed secret
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.encapsRefines_wrapperKem

/--
info: 'Tacenta.UnitKemWrapperModel.t3Agreements_wrapperKem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.t3Agreements_wrapperKem

/--
info: Tacenta.UnitKemWrapperModel.t3Agreements_wrapperKem : Tacenta.UnitKemWrapperModel.WrapperKemLaws →
  Tacenta.SessionUnitBraidT3.BraidHkdfAgrees →
    Tacenta.SessionUnitBraidT3.BraidHmacAgrees → T3Agreements Interp.real Tacenta.UnitKemWrapperModel.wrapperKem
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.t3Agreements_wrapperKem

/--
info: 'Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.toJoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.toJoint

/--
info: @Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.toJoint : ∀ {I : Interp}
  {dh : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape I}
  {oeq : {T : Type} → core.cmp.PartialEq T T → Option T → Option T → Result Bool},
  (Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape I dh fun {T} => oeq) →
    Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape I dh (Tacenta.UnitKemWrapperModel.wrapperKemOf I)
      fun {T} => oeq
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.toJoint

/--
info: 'Tacenta.UnitKemWrapperModel.decryptWrapperLaws_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.decryptWrapperLaws_joint

/--
info: Tacenta.UnitKemWrapperModel.decryptWrapperLaws_joint : ∀ (dh : Tacenta.UnitLifecycleT3.DhView),
  Tacenta.UnitKemWrapperModel.DecryptWrapperLaws dh →
    Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws Tacenta.UnitKemWrapperModel.wrapperKem dh
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.decryptWrapperLaws_joint

/--
info: 'Tacenta.UnitKemWrapperModel.decrypt_hypotheses_jointly_satisfiable_at_wrapperKem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.decrypt_hypotheses_jointly_satisfiable_at_wrapperKem

/--
info: Tacenta.UnitKemWrapperModel.decrypt_hypotheses_jointly_satisfiable_at_wrapperKem : ∀
  (dh : Tacenta.UnitLifecycleT3.DhView),
  Tacenta.UnitKemWrapperModel.DecryptWrapperLaws dh →
    ∃ oracle real model message rng,
      oracle.braidKem = Tacenta.UnitKemWrapperModel.wrapperKem ∧
        (∃ decoded, tacenta_wire.decode_message message = ok (core.result.Result.Ok decoded)) ∧
          (∃ composite ciphertext,
              Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
                Except.ok (composite, ciphertext)) ∧
            Model.Lifecycle.messageType (Tacenta.UnitLifecycleT3.sliceOf message) =
                some Model.Lifecycle.MessageType.ratchet ∧
              ∀ (view : Model.Lifecycle.CodewordView),
                Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses byteRng byteCrc
                  Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh view oracle real model message rng
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.decrypt_hypotheses_jointly_satisfiable_at_wrapperKem

/--
info: 'Tacenta.UnitKemWrapperModel.modelShipped_wrapperKemLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.modelShipped_wrapperKemLaws

/--
info: Tacenta.UnitKemWrapperModel.modelShipped_wrapperKemLaws : Tacenta.UnitKemWrapperModel.WrapperKemLawsShape
  Tacenta.UnitLifecycleDecryptScreen.Interp.modelShipped
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.modelShipped_wrapperKemLaws

/--
info: 'Tacenta.UnitKemWrapperModel.decrypt_wrapper_laws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.decrypt_wrapper_laws_model

/--
info: Tacenta.UnitKemWrapperModel.decrypt_wrapper_laws_model : Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape
  Tacenta.UnitLifecycleDecryptScreen.Interp.modelShipped Tacenta.UnitLifecycleDecryptScreen.viewShipped
  @Tacenta.UnitHeadroomInvariant.optionEqImpl
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.decrypt_wrapper_laws_model

/--
info: 'Tacenta.UnitKemWrapperModel.decrypt_joint_laws_model_at_wrapperKemOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.decrypt_joint_laws_model_at_wrapperKemOf

/--
info: Tacenta.UnitKemWrapperModel.decrypt_joint_laws_model_at_wrapperKemOf : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape
  Tacenta.UnitLifecycleDecryptScreen.Interp.modelShipped Tacenta.UnitLifecycleDecryptScreen.viewShipped
  (Tacenta.UnitKemWrapperModel.wrapperKemOf Tacenta.UnitLifecycleDecryptScreen.Interp.modelShipped)
  @Tacenta.UnitHeadroomInvariant.optionEqImpl
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.decrypt_joint_laws_model_at_wrapperKemOf

/--
info: 'Tacenta.UnitKemWrapperModel.decrypt_wrapper_laws_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitKemWrapperModel.decrypt_wrapper_laws_satisfiable

/--
info: Tacenta.UnitKemWrapperModel.decrypt_wrapper_laws_satisfiable : ∃ I dh oeq,
  I.HEADER_LEN = ok 64#usize ∧
    I.EK_VECTOR_LEN = ok 1536#usize ∧
      I.CT1_LEN = ok 1408#usize ∧
        I.CT2_LEN = ok 160#usize ∧
          (Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape I dh fun {T} => oeq) ∧
            Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape I dh (Tacenta.UnitKemWrapperModel.wrapperKemOf I)
              fun {T} => oeq
-/
#guard_msgs in
#check @Tacenta.UnitKemWrapperModel.decrypt_wrapper_laws_satisfiable

/--
info: def Tacenta.UnitKemWrapperModel.wrapperKemOf : Interp → Model.Braid.Kem :=
fun I =>
  {
    keyGen := fun rand =>
      match I.ikpGenerate byteRng byteCrc (Tacenta.UnitKemWrapperModel.streamOf 64 rand) with
      | ok (core.result.Result.Ok kp, snd) =>
        match I.ikpHeader kp, I.ikpEkVector kp with
        | ok h, ok v => some (Tacenta.UnitKemWrapperModel.leBytes 64 rand, List.take 32 (vecOf h), vecOf v)
        | x, x_1 => none
      | x => none,
    hashEk := Tacenta.UnitKemWrapperModel.hashEkOf I,
    encaps1 := fun rand ekSeed hek =>
      match
        I.encapsulate1 byteRng byteCrc (Tacenta.UnitKemWrapperModel.bytesSlice (ekSeed ++ hek))
          (Tacenta.UnitKemWrapperModel.streamOf 32 rand) with
      | ok (core.result.Result.Ok (fst, ct1, ss), snd) =>
        some (Tacenta.UnitKemWrapperModel.leBytes 32 rand ++ ekSeed ++ hek, vecOf ct1, keyOf ss)
      | x => none,
    encaps2 := fun secret x ekVector =>
      match
        I.encapsulate1 byteRng byteCrc (Tacenta.UnitKemWrapperModel.bytesSlice (List.drop 32 secret))
          (bytesOf (List.take 32 secret)) with
      | ok (core.result.Result.Ok (es, fst, snd), snd_1) =>
        match I.encapsulate2 es (Tacenta.UnitKemWrapperModel.bytesSlice ekVector) with
        | ok (core.result.Result.Ok ct2) => some (vecOf ct2)
        | x => none
      | x => none,
    decaps := fun dk ct1 ct2 =>
      match I.ikpGenerate byteRng byteCrc (bytesOf dk) with
      | ok (core.result.Result.Ok kp, snd) =>
        match
          I.ikpDecapsulate kp (Tacenta.UnitKemWrapperModel.bytesSlice ct1)
            (Tacenta.UnitKemWrapperModel.bytesSlice ct2) with
        | ok (core.result.Result.Ok raw) => some (keyOf raw)
        | x => none
      | x => none,
    ekSize := 1536, ct1Size := 1408, ct2Size := 160 }
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.wrapperKemOf

/--
info: def Tacenta.UnitKemWrapperModel.wrapperKem : Model.Braid.Kem :=
Tacenta.UnitKemWrapperModel.wrapperKemOf Interp.real
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.wrapperKem

/--
info: def Tacenta.UnitKemWrapperModel.hashEkOf : Interp → Bytes → Bytes → Bytes :=
fun I ekSeed ekVector =>
  if h :
      ∃ hek,
        List.length hek = 32 ∧
          I.validateEk (Tacenta.UnitKemWrapperModel.bytesSlice (ekSeed ++ hek))
              (Tacenta.UnitKemWrapperModel.bytesSlice ekVector) =
            ok true then
    Classical.choose h
  else []
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.hashEkOf

/--
info: def Tacenta.UnitKemWrapperModel.LawKemConstants : Prop :=
tacenta_kem.HEADER_LEN = ok 64#usize ∧
  tacenta_kem.EK_VECTOR_LEN = ok 1536#usize ∧ tacenta_kem.CT1_LEN = ok 1408#usize ∧ tacenta_kem.CT2_LEN = ok 160#usize
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.LawKemConstants

/--
info: def Tacenta.UnitKemWrapperModel.LawGenerateSeeded : Prop :=
∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (rng : R),
  Tacenta.SessionUnitBraidT1.RngTotal rc →
    ∃ seed res rng' rest,
      seed.length = 64 ∧
        tacenta_kem.IncrementalKeyPair.generate rc crc rng = ok (res, rng') ∧
          tacenta_kem.IncrementalKeyPair.generate byteRng byteCrc seed = ok (res, rest)
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.LawGenerateSeeded

/--
info: def Tacenta.UnitKemWrapperModel.LawGeneratedKeyPair : Prop :=
∀ (seed : List U8) (kp : tacenta_kem.IncrementalKeyPair) (rest : List U8),
  seed.length = 64 →
    tacenta_kem.IncrementalKeyPair.generate byteRng byteCrc seed = ok (core.result.Result.Ok kp, rest) →
      ∃ h v,
        kp.header = ok h ∧
          h.length = 64 ∧
            kp.ek_vector = ok v ∧
              v.length = 1536 ∧
                tacenta_kem.validate_ek (Tacenta.UnitKemWrapperModel.vecSlice h)
                      (Tacenta.UnitKemWrapperModel.vecSlice v) =
                    ok true ∧
                  ∀ (ct1 ct2 : Slice U8), ct1.length = 1408 → ct2.length = 160 → ∃ r, kp.decapsulate ct1 ct2 = ok r
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.LawGeneratedKeyPair

/--
info: def Tacenta.UnitKemWrapperModel.LawEncapsulate1Seeded : Prop :=
∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (header : Slice U8) (rng : R),
  Tacenta.SessionUnitBraidT1.RngTotal rc →
    header.length = 64 →
      ∃ rnd res rng' rest,
        rnd.length = 32 ∧
          tacenta_kem.encapsulate1 rc crc header rng = ok (res, rng') ∧
            tacenta_kem.encapsulate1 byteRng byteCrc header rnd = ok (res, rest)
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.LawEncapsulate1Seeded

/--
info: def Tacenta.UnitKemWrapperModel.LawEncapsulate2Fresh : Prop :=
∀ (header : Slice U8) (rnd : List U8) (es : tacenta_kem.EncapsState) (ct1 : alloc.vec.Vec U8)
  (ss : Std.Array U8 32#usize) (rest : List U8),
  header.length = 64 →
    rnd.length = 32 →
      tacenta_kem.encapsulate1 byteRng byteCrc header rnd = ok (core.result.Result.Ok (es, ct1, ss), rest) →
        ∀ (ekVector : Slice U8), ekVector.length = 1536 → ∃ r, tacenta_kem.encapsulate2 es ekVector = ok r
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.LawEncapsulate2Fresh

/--
info: def Tacenta.UnitKemWrapperModel.LawValidateEkTotal : Prop :=
∀ (header ekVector : Slice U8),
  header.length = 64 → ekVector.length = 1536 → ∃ r, tacenta_kem.validate_ek header ekVector = ok r
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.LawValidateEkTotal

/--
info: def Tacenta.UnitKemWrapperModel.LawValidateEkUnique : Prop :=
∀ (h1 h2 ekVector : Slice U8),
  h1.length = 64 →
    h2.length = 64 →
      ekVector.length = 1536 →
        List.take 32 (sliceOf h1) = List.take 32 (sliceOf h2) →
          tacenta_kem.validate_ek h1 ekVector = ok true →
            tacenta_kem.validate_ek h2 ekVector = ok true → sliceOf h1 = sliceOf h2
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.LawValidateEkUnique

/--
info: def Tacenta.UnitKemWrapperModel.LawKemClone : Prop :=
Tacenta.SessionUnitBraidT3.KemCloneAgrees
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.LawKemClone

/--
info: structure Tacenta.UnitKemWrapperModel.WrapperKemLawsShape (I : Interp) : Prop
number of parameters: 1
fields:
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape.constants : Tacenta.UnitKemWrapperModel.LawKemConstantsShape I
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape.generateSeeded : Tacenta.UnitKemWrapperModel.LawGenerateSeededShape I
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape.generatedKeyPair : Tacenta.UnitKemWrapperModel.LawGeneratedKeyPairShape
      I
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape.encapsulate1Seeded : Tacenta.UnitKemWrapperModel.LawEncapsulate1SeededShape
      I
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape.encapsulate2Fresh : Tacenta.UnitKemWrapperModel.LawEncapsulate2FreshShape
      I
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape.validateEkTotal : Tacenta.UnitKemWrapperModel.LawValidateEkTotalShape
      I
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape.validateEkUnique : Tacenta.UnitKemWrapperModel.LawValidateEkUniqueShape
      I
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape.clone : KemCloneAgreesShape I
constructor:
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape.mk {I : Interp}
    (constants : Tacenta.UnitKemWrapperModel.LawKemConstantsShape I)
    (generateSeeded : Tacenta.UnitKemWrapperModel.LawGenerateSeededShape I)
    (generatedKeyPair : Tacenta.UnitKemWrapperModel.LawGeneratedKeyPairShape I)
    (encapsulate1Seeded : Tacenta.UnitKemWrapperModel.LawEncapsulate1SeededShape I)
    (encapsulate2Fresh : Tacenta.UnitKemWrapperModel.LawEncapsulate2FreshShape I)
    (validateEkTotal : Tacenta.UnitKemWrapperModel.LawValidateEkTotalShape I)
    (validateEkUnique : Tacenta.UnitKemWrapperModel.LawValidateEkUniqueShape I) (clone : KemCloneAgreesShape I) :
    Tacenta.UnitKemWrapperModel.WrapperKemLawsShape I
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.WrapperKemLawsShape

/--
info: def Tacenta.UnitKemWrapperModel.WrapperKemLaws : Prop :=
Tacenta.UnitKemWrapperModel.WrapperKemLawsShape Interp.real
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.WrapperKemLaws

/--
info: structure Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape (I : Interp)
  (dh : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape I)
  (oeq : {T : Type} → core.cmp.PartialEq T T → Option T → Option T → Result Bool) : Prop
number of parameters: 3
fields:
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.dhCodec : DhCodecShape I
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.dhAgree : DhAgreeShape I
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.aeadOpen : AeadOpenShape I
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.viewInjective : Function.Injective dh.privateKey ∧
      Function.Injective dh.publicKey
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.codec : Tacenta.UnitLifecycleDecryptRatchetScreen.DhCodecOfShape I
      dh
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.braid : BraidReceiveAxiom I
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.triple : TripleReceiveAxiom I
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.messageKeyMaterial : MessageKeyMaterialRoundTripShape I
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.laws : StdLaws I
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.truncatePrefix : TruncatePrefixShape I
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.derivedKeys : Nonempty (ZeroizingModelShape I DerivedZ)
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.hkdf : HkdfAgreesShape I
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.hmac : HmacAgreesShape I
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.kem : Tacenta.UnitKemWrapperModel.WrapperKemLawsShape I
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.roundTrips : Tacenta.UnitLifecycleDecryptRatchetScreen.ZeroizeRoundTripShapes
      I
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.validKey : Tacenta.UnitHeadroomInvariant.ValidKeyShape I
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.optionEq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      fun {T} => oeq
constructor:
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape.mk {I : Interp}
    {dh : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape I}
    {oeq : {T : Type} → core.cmp.PartialEq T T → Option T → Option T → Result Bool} (dhCodec : DhCodecShape I)
    (dhAgree : DhAgreeShape I) (aeadOpen : AeadOpenShape I)
    (viewInjective : Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey)
    (codec : Tacenta.UnitLifecycleDecryptRatchetScreen.DhCodecOfShape I dh) (braid : BraidReceiveAxiom I)
    (triple : TripleReceiveAxiom I) (messageKeyMaterial : MessageKeyMaterialRoundTripShape I) (laws : StdLaws I)
    (truncatePrefix : TruncatePrefixShape I) (derivedKeys : Nonempty (ZeroizingModelShape I DerivedZ))
    (hkdf : HkdfAgreesShape I) (hmac : HmacAgreesShape I) (kem : Tacenta.UnitKemWrapperModel.WrapperKemLawsShape I)
    (roundTrips : Tacenta.UnitLifecycleDecryptRatchetScreen.ZeroizeRoundTripShapes I)
    (validKey : Tacenta.UnitHeadroomInvariant.ValidKeyShape I)
    (optionEq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape fun {T} => oeq) :
    Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape I dh oeq
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape

/--
info: def Tacenta.UnitKemWrapperModel.DecryptWrapperLaws : Tacenta.UnitLifecycleT3.DhView → Prop :=
fun dh =>
  Tacenta.UnitKemWrapperModel.DecryptWrapperLawsShape Interp.real
    { privateKey := dh.privateKey, publicKey := dh.publicKey } @core.option.Option.Insts.CoreCmpPartialEqOption.eq
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.DecryptWrapperLaws

/--
info: def Tacenta.UnitKemWrapperModel.bytesSlice : Bytes → Slice U8 :=
fun l => if h : List.length l ≤ Usize.max then ⟨bytesOf l, ⋯⟩ else ⟨[], Tacenta.UnitKemWrapperModel.length_nil_le⟩
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.bytesSlice

/--
info: def Tacenta.UnitKemWrapperModel.vecSlice : alloc.vec.Vec U8 → Slice U8 :=
fun v => ⟨↑v, ⋯⟩
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.vecSlice

/--
info: def Tacenta.UnitKemWrapperModel.leBytes : ℕ → ℕ → Bytes :=
fun x x_1 => Nat.brecOn (motive := fun x => ℕ → Bytes) x Tacenta.UnitKemWrapperModel.leBytes._f x_1
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.leBytes

/--
info: def Tacenta.UnitKemWrapperModel.leNat : Bytes → ℕ :=
fun x => List.brecOn x Tacenta.UnitKemWrapperModel.leNat._f
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.leNat

/--
info: def Tacenta.UnitKemWrapperModel.streamOf : ℕ → ℕ → List U8 :=
fun k n => bytesOf (Tacenta.UnitKemWrapperModel.leBytes k n)
-/
#guard_msgs in
#print Tacenta.UnitKemWrapperModel.streamOf
