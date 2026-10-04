import Translation.UnitSatisfiabilityJoint
import Translation.SessionUnitBraidT3

/-!
# The Braid refinement agreements of the Session unit have a model

`SessionUnitBraidT3.lean` proves `step_send_refines`, `Braid.send_refines`, `step_receive_refines`
and `Braid.receive_refines` about the complete Session translation unit.  Besides the contract
fields of `UnitLifecycleT1`, they take six agreements about the unit's opaque constants:
`KemAgreesFor K`, `KemLenAgrees K`, `ValidateEkAgrees K`, `KemCloneAgrees`, `BraidHkdfAgrees` and
`BraidHmacAgrees`.  Each relates an opaque KEM or KDF constant to `Model.Braid.Kem` or `Model.Kdf`.

`UnitSatisfiabilityJoint.lean` interprets the unit's opaque constants (`Interp`) and shows that one
interpretation satisfies every axiom-level field of the four contract records.  Its model leaves
the KEM family and the two KDFs degenerate (`Unit` key pairs, empty vectors, an all-zero HKDF), so
it does not satisfy these agreements.  The standalone witnesses (`KemWitness.lean`,
`Satisfiability.lean`) are about the constants of the standalone Braid translation
(`tacenta_braid.*`, `Tacenta.BraidT3.*`), which are different Lean constants from the unit's
(`tacenta_session_unit.*`, `Tacenta.SessionUnitBraidT3.*`); the two environments cannot be imported
together, so those witnesses do not cover the unit's statements.  This module does for the unit what
they do for the standalone crate, in the shape `UnitSatisfiabilityJoint` uses:

* one `*Shape` per agreement, over an arbitrary `Interp`, and a theorem `*_is` that binds it, at
  `Interp.real`, to the agreement of `SessionUnitBraidT3.lean` by `Iff.rfl`, so the kernel checks
  that the shape is the very proposition the refinement theorems take;
  `braid_agreement_shapes_are_predicates` collects the bridges;
* `Interp.modelT3`: an interpretation, a conservative extension of `Interp.model` (only the KEM
  family, the two KDFs and their sizes change), over which every agreement holds, together with
  every axiom-level shape of `UnitSatisfiabilityJoint` and the laws of `StdLaws`;
* the two laws under which the translated erasure coder's agreement is a theorem
  (`DivCeilValue`, already a field of `EstablishResponderContracts`, and `TruncatePrefix`, the
  prefix value of `Vec::truncate`), each with a bridge, and a proof that `Interp.modelT3`
  satisfies both.

## What it shows

By the substitution argument of `UnitSatisfiabilityJoint`: the six agreements are jointly
consistent with each other, with every axiom-level contract field of the session records, with
`StdLaws` and with the two laws.  A derivation of `False` from statements about uninterpreted
constants would give one in the model, where every such statement holds.  That last step is an
argument about derivations and not a theorem inside Lean.

## What it does not show

* It does not show that the real ML-KEM wrapper, libcrux or the real KDF satisfies the six
  agreements.  They are assumed and recorded in `LIMITATIONS.md`.  The model's `K` is `toyKem`,
  because `K` is existentially quantified in `KemAgreesFor K`.
* `ValidateEkAgrees K` holds of the real call only for a `K` whose `hashEk` also folds in the
  coefficient check that `validate_ek` makes after the hash; such a `K` exists because `K` is
  existential.
* It does not cover the hypotheses about state and message (`UnitSatisfiabilityBraidStates.lean`)
  or the erasure coder (`UnitSatisfiabilityErasureAgrees.lean`).
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit

namespace Tacenta.UnitSatisfiabilityBraidAgreements

open Tacenta.UnitSatisfiabilityJoint
open Tacenta.SessionUnitBraidT3 (vecOf keyOf sliceOf Bytes)

/-! ## The agreements as shapes over an interpretation -/

def KemLenShape (I : Interp) (K : Model.Braid.Kem) : Prop :=
  (∃ v, I.HEADER_LEN = ok v ∧ v.val = Model.Braid.headerSize) ∧
  (∃ v, I.EK_VECTOR_LEN = ok v ∧ v.val = K.ekSize) ∧
  (∃ v, I.CT1_LEN = ok v ∧ v.val = K.ct1Size) ∧
  (∃ v, I.CT2_LEN = ok v ∧ v.val = K.ct2Size)

def KemAgreesShape (I : Interp) (K : Model.Braid.Kem) : Prop :=
  (∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (rng : R),
      Tacenta.SessionUnitBraidT1.RngTotal rc →
      ∃ kp rng' rand,
        I.ikpGenerate rc crc rng = ok (core.result.Result.Ok kp, rng') ∧
        (∃ h, I.ikpHeader kp = ok h ∧
          vecOf h = (K.keyGen rand).2.1 ++ K.hashEk (K.keyGen rand).2.1 (K.keyGen rand).2.2) ∧
        (∃ v, I.ikpEkVector kp = ok v ∧ vecOf v = (K.keyGen rand).2.2) ∧
        (∀ ct1 ct2 : Slice Std.U8, ct1.length = K.ct1Size → ct2.length = K.ct2Size →
          ∃ raw : Array Std.U8 32#usize,
            I.ikpDecapsulate kp ct1 ct2 = ok (core.result.Result.Ok raw) ∧
            keyOf raw = K.decaps (K.keyGen rand).1 (sliceOf ct1) (sliceOf ct2))) ∧
    (∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
        (header : Slice Std.U8) (rng : R), Tacenta.SessionUnitBraidT1.RngTotal rc →
      header.length = Model.Braid.headerSize →
      ∃ es ct1raw ssraw rng' rand',
        I.encapsulate1 rc crc header rng =
          ok (core.result.Result.Ok (es, ct1raw, ssraw), rng') ∧
        (∀ ekSeed hek : Bytes, ekSeed.length = 32 → sliceOf header = ekSeed ++ hek →
          (K.encaps1 rand' ekSeed hek).2.1 = vecOf ct1raw ∧
          (K.encaps1 rand' ekSeed hek).2.2 = keyOf ssraw ∧
          (∀ ekVector : Slice Std.U8, ekVector.length = K.ekSize →
            ∃ ct2raw,
              I.encapsulate2 es ekVector = ok (core.result.Result.Ok ct2raw) ∧
              vecOf ct2raw =
                K.encaps2 (K.encaps1 rand' ekSeed hek).1 ekSeed (sliceOf ekVector))))

def ValidateEkAgreesShape (I : Interp) (K : Model.Braid.Kem) : Prop :=
  ∀ (header ekVector : Slice Std.U8) (ekSeed hek : Bytes),
    ekSeed.length = 32 → hek.length = 32 → ekVector.length = K.ekSize →
    sliceOf header = ekSeed ++ hek →
    ∃ r, I.validateEk header ekVector = ok r ∧
      (r = true ↔ K.hashEk ekSeed (sliceOf ekVector) = hek)

def KemCloneAgreesShape (I : Interp) : Prop :=
  (∀ kp kp' : I.IncrementalKeyPair,
    I.ikpClone kp = ok kp' →
    (∀ h, I.ikpHeader kp = ok h → I.ikpHeader kp' = ok h) ∧
    (∀ v, I.ikpEkVector kp = ok v → I.ikpEkVector kp' = ok v) ∧
    (∀ (ct1 ct2 : Slice Std.U8) raw,
      I.ikpDecapsulate kp ct1 ct2 = ok (core.result.Result.Ok raw) →
      I.ikpDecapsulate kp' ct1 ct2 = ok (core.result.Result.Ok raw))) ∧
  (∀ es es' : I.EncapsState,
    I.esClone es = ok es' →
    ∀ (ekVector : Slice Std.U8) ct2, I.encapsulate2 es ekVector =
      ok (core.result.Result.Ok ct2) →
      I.encapsulate2 es' ekVector = ok (core.result.Result.Ok ct2))

def HkdfAgreesShape (I : Interp) : Prop :=
  ∀ (N : Usize) (salt ikm info : Slice Std.U8), N.val ≤ 8160 →
    ∃ r, I.hkdfSha256 N salt ikm info = ok r ∧
      keyOf r = Model.Kdf.hkdf (sliceOf salt) (sliceOf ikm) (sliceOf info) N.val

def HmacAgreesShape (I : Interp) : Prop :=
  ∀ (key data : Slice Std.U8),
    ∃ r, I.hmacSha256 key data = ok r ∧
      keyOf r = Model.Kdf.hmac (sliceOf key) (sliceOf data)

/-! ## Each shape, at the real constants, is the agreement of `SessionUnitBraidT3.lean` -/

theorem KemLenAgrees_is (K : Model.Braid.Kem) :
    Tacenta.SessionUnitBraidT3.KemLenAgrees K ↔ KemLenShape Interp.real K := Iff.rfl

theorem KemAgreesFor_is (K : Model.Braid.Kem) :
    Tacenta.SessionUnitBraidT3.KemAgreesFor K ↔ KemAgreesShape Interp.real K := Iff.rfl

theorem ValidateEkAgrees_is (K : Model.Braid.Kem) :
    Tacenta.SessionUnitBraidT3.ValidateEkAgrees K ↔ ValidateEkAgreesShape Interp.real K :=
  Iff.rfl

theorem KemCloneAgrees_is :
    Tacenta.SessionUnitBraidT3.KemCloneAgrees ↔ KemCloneAgreesShape Interp.real := Iff.rfl

theorem BraidHkdfAgrees_is :
    Tacenta.SessionUnitBraidT3.BraidHkdfAgrees ↔ HkdfAgreesShape Interp.real := Iff.rfl

theorem BraidHmacAgrees_is :
    Tacenta.SessionUnitBraidT3.BraidHmacAgrees ↔ HmacAgreesShape Interp.real := Iff.rfl


/-! ## Model bytes as translated bytes -/

/-- A model byte as a translated one. -/
def toU8 (x : UInt8) : Std.U8 := ⟨x.toBitVec⟩

theorem u8_toU8 (x : UInt8) : Tacenta.SessionUnitBraidT3.u8 (toU8 x) = x := by
  show UInt8.ofNat x.toBitVec.toNat = x
  simp

def bytesOf (l : Bytes) : List Std.U8 := l.map toU8

theorem map_u8_bytesOf (l : Bytes) : (bytesOf l).map Tacenta.SessionUnitBraidT3.u8 = l := by
  simp [bytesOf, List.map_map, Function.comp_def, u8_toU8]

/-- Any `n` that fits 32 bits fits `usize`, on a 32-bit and on a 64-bit target alike. -/
theorem usize_max_ge (n : ℕ) (h : n ≤ 2 ^ 32 - 1) : n ≤ Usize.max := by
  simp only [Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq]
  (cases System.Platform.numBits_eq <;> simp_all); omega

/-- A byte string as a `Vec`, for strings that fit. -/
def vecOfBytes (l : Bytes) (h : l.length ≤ Usize.max) : alloc.vec.Vec Std.U8 :=
  ⟨bytesOf l, by simpa [bytesOf] using h⟩

theorem vecOf_vecOfBytes (l : Bytes) (h : l.length ≤ Usize.max) :
    vecOf (vecOfBytes l h) = l := map_u8_bytesOf l

theorem length_vecOfBytes (l : Bytes) (h : l.length ≤ Usize.max) :
    (vecOfBytes l h).length = l.length := by simp [vecOfBytes, bytesOf]

/-- A byte string as a 32-byte array: the first 32 bytes, zero-filled. -/
def arr32 (l : Bytes) : Array Std.U8 32#usize :=
  ⟨(bytesOf l ++ List.replicate 32 0#u8).take 32, by simp⟩

theorem keyOf_arr32 (l : Bytes) (h : l.length = 32) : keyOf (arr32 l) = l := by
  simp only [keyOf, arr32]
  have hl : (bytesOf l).length = 32 := by simp [bytesOf, h]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  exact map_u8_bytesOf l

theorem le64 : 64 ≤ Usize.max := usize_max_ge 64 (by norm_num)
theorem le32 : 32 ≤ Usize.max := usize_max_ge 32 (by norm_num)

/-- `toyKem`'s seed and encapsulation-key vector for randomness `r`. -/
def seedOf (r : ℕ) : Bytes := List.replicate 32 (UInt8.ofNat r)
def ekVecOf (r : ℕ) : Bytes := List.replicate 64 (UInt8.ofNat r)

theorem toy_header_len (r : ℕ) :
    (seedOf r ++ Model.Braid.toyKem.hashEk (seedOf r) (ekVecOf r)).length ≤ Usize.max := by
  simp [seedOf, Model.Braid.toyKem]; exact le64

/-- The KDFs: the model's own bytes, as arrays of exactly the requested length. -/
def hkdfImpl (N : Usize) (salt ikm info : Slice Std.U8) : Array Std.U8 N :=
  ⟨(Model.Kdf.hkdf (sliceOf salt) (sliceOf ikm) (sliceOf info) N.val).map toU8,
    by simp [Model.Kdf.hkdf_length]⟩

def hmacImpl (key data : Slice Std.U8) : Array Std.U8 32#usize :=
  ⟨(Model.Kdf.hmac (sliceOf key) (sliceOf data)).map toU8,
    by simp [Model.Kdf.hmac_length, Model.Kdf.hashLen]⟩

/-! ## The interpretation

`Interp.model` with the KEM family and the two KDFs replaced.  A key pair is its randomness (a
number), an encapsulation state is `Unit`, because `toyKem.encaps2` ignores it; the sizes are
`toyKem`'s (64, 64, 64, 32) and the header size 64 that `Model.Braid.headerSize` fixes.  Every
other field is `Interp.model`'s. -/

noncomputable def Interp.modelT3 : Interp :=
  { Interp.model with
    IncrementalKeyPair := ℕ
    EncapsState := Unit
    hkdfSha256 := fun N salt ikm info => ok (hkdfImpl N salt ikm info)
    hmacSha256 := fun key data => ok (hmacImpl key data)
    HEADER_LEN := ok 64#usize
    EK_VECTOR_LEN := ok 64#usize
    CT1_LEN := ok 64#usize
    CT2_LEN := ok 32#usize
    ikpClone := fun r => ok r
    ikpGenerate := fun _ _ rng => ok (core.result.Result.Ok 0, rng)
    ikpHeader := fun r =>
      ok (vecOfBytes (seedOf r ++ Model.Braid.toyKem.hashEk (seedOf r) (ekVecOf r))
        (toy_header_len r))
    ikpEkVector := fun r => ok (vecOfBytes (ekVecOf r) (by simp [ekVecOf]; exact le64))
    ikpDecapsulate := fun r _ _ => ok (core.result.Result.Ok (arr32 (seedOf r)))
    esClone := fun es => ok es
    encapsulate1 := fun _ _ header rng =>
      ok (core.result.Result.Ok ((), vecOfBytes (List.replicate 64 7) (by simp; exact le64),
        arr32 ((sliceOf header).take 32)), rng)
    encapsulate2 := fun _ _ =>
      ok (core.result.Result.Ok (vecOfBytes (List.replicate 32 9) (by simp; exact le32)))
    validateEk := fun header ekVector =>
      ok (decide (Model.Braid.toyKem.hashEk ((sliceOf header).take 32) (sliceOf ekVector)
        = (sliceOf header).drop 32)) }

/-! ### The agreements hold in the model, at `toyKem` -/

theorem modelT3_kemLen : KemLenShape Interp.modelT3 Model.Braid.toyKem := by
  refine ⟨⟨64#usize, rfl, ?_⟩, ⟨64#usize, rfl, ?_⟩, ⟨64#usize, rfl, ?_⟩, ⟨32#usize, rfl, ?_⟩⟩ <;>
    simp [Model.Braid.headerSize, Model.Braid.toyKem]

theorem modelT3_kemAgrees : KemAgreesShape Interp.modelT3 Model.Braid.toyKem := by
  refine ⟨?_, ?_⟩
  · intro R rc crc rng _
    refine ⟨(0 : ℕ), rng, 0, rfl, ⟨_, rfl, ?_⟩, ⟨_, rfl, ?_⟩, ?_⟩
    · rw [vecOf_vecOfBytes]; rfl
    · rw [vecOf_vecOfBytes]; rfl
    · intro ct1 ct2 _ _
      refine ⟨arr32 (seedOf 0), rfl, ?_⟩
      rw [keyOf_arr32 _ (by simp [seedOf])]; rfl
  · intro R rc crc header rng _ _
    refine ⟨(), _, arr32 ((sliceOf header).take 32), rng, 0, rfl, ?_⟩
    intro ekSeed hek hlen hsplit
    refine ⟨?_, ?_, ?_⟩
    · rw [vecOf_vecOfBytes]; rfl
    · rw [hsplit, List.take_left' hlen, keyOf_arr32 _ hlen]; rfl
    · intro ekVector _
      refine ⟨_, rfl, ?_⟩
      rw [vecOf_vecOfBytes]; rfl

theorem modelT3_validateEk : ValidateEkAgreesShape Interp.modelT3 Model.Braid.toyKem := by
  intro header ekVector ekSeed hek hlen _ _ hsplit
  refine ⟨_, rfl, ?_⟩
  rw [decide_eq_true_iff, hsplit, List.take_left' hlen, List.drop_left' hlen]

theorem modelT3_kemClone : KemCloneAgreesShape Interp.modelT3 := by
  refine ⟨?_, ?_⟩
  · intro kp kp' h
    simp only [Interp.modelT3, ok.injEq] at h
    subst h
    exact ⟨fun _ h => h, fun _ h => h, fun _ _ _ h => h⟩
  · intro es es' _
    cases es; cases es'
    exact fun _ _ h => h

theorem modelT3_hkdfAgrees : HkdfAgreesShape Interp.modelT3 := by
  intro N salt ikm info _
  refine ⟨hkdfImpl N salt ikm info, rfl, ?_⟩
  simp [hkdfImpl, keyOf, List.map_map, Function.comp_def, u8_toU8]

theorem modelT3_hmacAgrees : HmacAgreesShape Interp.modelT3 := by
  intro key data
  refine ⟨hmacImpl key data, rfl, ?_⟩
  simp [hmacImpl, keyOf, List.map_map, Function.comp_def, u8_toU8]

/-- The axiom-level shapes of the Joint module, as one proposition over an interpretation. -/
structure AllT1Shapes (I : Interp) : Prop where
  dhCodec : DhCodecShape I
  dhIdentity : DhIdentityShape I
  dhAgree : DhAgreeShape I
  kemEncapsulate : KemEncapsulateShape I
  kemDecapsulate : KemDecapsulateShape I
  xeddsaVerify : XeddsaVerifyShape I
  aeadOpen : AeadOpenShape I
  aeadSealBounded : AeadSealBoundedShape I
  messageKeyMaterial : MessageKeyMaterialRoundTripShape I
  vecPop : VecPopShape I
  hkdf : HkdfShape I
  hmac : HmacShape I
  zeroizingTotal : ZeroizingTotalShape I
  spqrZeroize : SpqrZeroizeShape I
  vecRetainAxiom : VecRetainAxiomShape I
  optionClone : OptionCloneShape I
  ct1Len : Ct1LenShape I
  ct2Len : Ct2LenShape I
  headerLen : HeaderLenShape I
  ekVectorLen : EkVectorLenShape I
  keyPairEkVector : KeyPairEkVectorShape I
  keyPairHeader : KeyPairHeaderShape I
  keyPairDecapsulate : KeyPairDecapsulateShape I
  keyPairClone : KeyPairCloneShape I
  encapsStateClone : EncapsStateCloneShape I
  validateEk : ValidateEkShape I
  keyPairGenerate : KeyPairGenerateShape I
  encapsulate1 : Encapsulate1Shape I
  encapsulate2 : Encapsulate2Shape I
  zeroizingArray : ZeroizingArrayRoundTripShape I
  arrayZeroize : ArrayZeroizeShape I
  rangeFullIndex : RangeFullIndexShape I
  divCeilValue : DivCeilValueShape I

/-! ### The shapes that mention a changed field -/

theorem modelT3_Hkdf : HkdfShape Interp.modelT3 := fun _ _ _ _ _ => ⟨_, rfl⟩
theorem modelT3_Hmac : HmacShape Interp.modelT3 := fun _ _ => ⟨_, rfl⟩

theorem modelT3_Ct1Len : Ct1LenShape Interp.modelT3 := ⟨64#usize, rfl, by simp⟩
theorem modelT3_Ct2Len : Ct2LenShape Interp.modelT3 := ⟨32#usize, rfl, by simp⟩
theorem modelT3_HeaderLen : HeaderLenShape Interp.modelT3 := ⟨64#usize, rfl, by simp⟩
theorem modelT3_EkVectorLen : EkVectorLenShape Interp.modelT3 := ⟨64#usize, rfl, by simp⟩

theorem modelT3_KeyPairEkVector : KeyPairEkVectorShape Interp.modelT3 := by
  intro kp
  refine ⟨_, rfl, ?_⟩
  show (vecOfBytes (ekVecOf kp) _).length ≤ 4096
  rw [length_vecOfBytes]; simp [ekVecOf]

theorem modelT3_KeyPairHeader : KeyPairHeaderShape Interp.modelT3 := by
  intro kp
  refine ⟨_, rfl, ?_⟩
  show (vecOfBytes (seedOf kp ++ Model.Braid.toyKem.hashEk (seedOf kp) (ekVecOf kp)) _).length ≤ 4096
  rw [length_vecOfBytes]; simp [seedOf, Model.Braid.toyKem]

theorem modelT3_KeyPairDecapsulate : KeyPairDecapsulateShape Interp.modelT3 :=
  fun _ _ _ => ⟨_, rfl⟩

theorem modelT3_KeyPairClone : KeyPairCloneShape Interp.modelT3 := fun _ => ⟨_, rfl⟩
theorem modelT3_EncapsStateClone : EncapsStateCloneShape Interp.modelT3 := fun _ => ⟨_, rfl⟩
theorem modelT3_ValidateEk : ValidateEkShape Interp.modelT3 := fun _ _ => ⟨_, rfl⟩
theorem modelT3_KeyPairGenerate : KeyPairGenerateShape Interp.modelT3 :=
  fun _ _ _ _ => ⟨_, rfl⟩

theorem modelT3_Encapsulate1 : Encapsulate1Shape Interp.modelT3 := by
  intro R rc crc s rng _
  refine ⟨_, rfl, ?_⟩
  intro es ct1 raw h
  simp only [] at h
  obtain ⟨-, rfl, -⟩ := h
  rw [length_vecOfBytes]; simp

theorem modelT3_Encapsulate2 : Encapsulate2Shape Interp.modelT3 := by
  intro es s
  refine ⟨_, rfl, ?_⟩
  intro c h
  simp only [core.result.Result.Ok.injEq] at h
  subst h
  rw [length_vecOfBytes]; simp

/-- Every axiom-level shape of the Joint module holds in `modelT3`.  The shapes that mention no
changed field are the Joint module's own theorems, accepted at `modelT3` by definitional
unfolding. -/
theorem modelT3_allT1 : AllT1Shapes Interp.modelT3 where
  dhCodec := model_DhCodec
  dhIdentity := model_DhIdentity
  dhAgree := model_DhAgree
  kemEncapsulate := model_KemEncapsulate
  kemDecapsulate := model_KemDecapsulate
  xeddsaVerify := model_XeddsaVerify
  aeadOpen := model_AeadOpen
  aeadSealBounded := model_AeadSealBounded
  messageKeyMaterial := model_MessageKeyMaterialRoundTrip
  vecPop := model_VecPop
  hkdf := modelT3_Hkdf
  hmac := modelT3_Hmac
  zeroizingTotal := model_ZeroizingTotal
  spqrZeroize := model_SpqrZeroize
  vecRetainAxiom := model_VecRetainAxiom
  optionClone := model_OptionClone
  ct1Len := modelT3_Ct1Len
  ct2Len := modelT3_Ct2Len
  headerLen := modelT3_HeaderLen
  ekVectorLen := modelT3_EkVectorLen
  keyPairEkVector := modelT3_KeyPairEkVector
  keyPairHeader := modelT3_KeyPairHeader
  keyPairDecapsulate := modelT3_KeyPairDecapsulate
  keyPairClone := modelT3_KeyPairClone
  encapsStateClone := modelT3_EncapsStateClone
  validateEk := modelT3_ValidateEk
  keyPairGenerate := modelT3_KeyPairGenerate
  encapsulate1 := modelT3_Encapsulate1
  encapsulate2 := modelT3_Encapsulate2
  zeroizingArray := model_ZeroizingArrayRoundTrip
  arrayZeroize := model_ArrayZeroize
  rangeFullIndex := model_RangeFullIndex
  divCeilValue := model_DivCeilValue

theorem modelT3_stdLaws : StdLaws Interp.modelT3 where
  pop := model_StdLaws.pop
  asMut := model_StdLaws.asMut
  blanketU32 := model_StdLaws.blanketU32
  truncate := model_StdLaws.truncate
  divCeil := model_StdLaws.divCeil

/-- The two model classes (`ZeroizingModel`, `DerivedKeysModel`) hold at any wrapped type, as in
`Interp.model`: `Zeroizing` is the identity wrapper in both. -/
def modelT3_zeroizingModel (Z : Type) : ZeroizingModelShape Interp.modelT3 Z where
  contents z := z
  new := (model_ZeroizingModel Z).new
  deref := (model_ZeroizingModel Z).deref
  deref_mut := (model_ZeroizingModel Z).deref_mut

/-- The Braid refinement agreements about opaque constants, at `toyKem`, in one interpretation. -/
structure T3Agreements (I : Interp) (K : Model.Braid.Kem) : Prop where
  kemLen : KemLenShape I K
  kemAgrees : KemAgreesShape I K
  validateEk : ValidateEkAgreesShape I K
  kemClone : KemCloneAgreesShape I
  hkdf : HkdfAgreesShape I
  hmac : HmacAgreesShape I

theorem modelT3_t3 : T3Agreements Interp.modelT3 Model.Braid.toyKem where
  kemLen := modelT3_kemLen
  kemAgrees := modelT3_kemAgrees
  validateEk := modelT3_validateEk
  kemClone := modelT3_kemClone
  hkdf := modelT3_hkdfAgrees
  hmac := modelT3_hmacAgrees

/-! ## The two laws under which `ErasureAgrees` is a theorem about the translated unit

The erasure coder is translated Rust, so `ErasureAgrees` is a statement about definitions.  Its
truth is fixed by their bodies and by the two library functions they reach that the translation
leaves opaque: `usize::div_ceil` (in `chunk_count`) and `Vec::truncate` (the last step of
`Decoder::message`).  The laws are the value of each at the arguments the coder uses.  Both hold
in `Interp.modelT3` (the faithful operations of `UnitSatisfiabilityJoint`'s model are unchanged),
so assuming them is consistent with every hypothesis of the four theorems. -/

/-- `Vec::truncate` at `Vec<u8>` keeps the prefix of the requested length. -/
def TruncatePrefix : Prop :=
  ∀ (v : alloc.vec.Vec Std.U8) (n : Usize), ∃ v',
    alloc.vec.Vec.truncate Global v n = ok v' ∧ v'.val = v.val.take n.val

def TruncatePrefixShape (I : Interp) : Prop :=
  ∀ (v : alloc.vec.Vec Std.U8) (n : Usize), ∃ v',
    I.vecTruncate Global v n = ok v' ∧ v'.val = v.val.take n.val

theorem TruncatePrefix_is : TruncatePrefix ↔ TruncatePrefixShape Interp.real := Iff.rfl

theorem modelT3_truncatePrefix : TruncatePrefixShape Interp.modelT3 :=
  fun v n => model_Faithful.truncate v n

/-- `TruncatePrefix` gives the totality law `SessionBraidReceiveRepair` uses. -/
theorem TruncatePrefix.total (h : TruncatePrefix) :
    ∀ (v : alloc.vec.Vec Std.U8) (n : Usize), ∃ r, alloc.vec.Vec.truncate Global v n = ok r :=
  fun v n => let ⟨r, hr, _⟩ := h v n; ⟨r, hr⟩

/-- The six agreements and the law `TruncatePrefix`, each bound to the shape this module proves
satisfiable.  Each bridge is proved by `Iff.rfl`, so the kernel checks that the shape unfolds to the
very proposition `SessionUnitBraidT3.lean` takes (the bridge of `DivCeilValue` is
`UnitSatisfiabilityJoint.all_shapes_are_predicates`'s last conjunct).  They are collected so that one
pin holds all of them, and `check-braid-agreement-negatives.sh` requires this theorem to name
every `_is` bridge of this module. -/
theorem braid_agreement_shapes_are_predicates :
    (∀ K, Tacenta.SessionUnitBraidT3.KemLenAgrees K ↔ KemLenShape Interp.real K) ∧
    (∀ K, Tacenta.SessionUnitBraidT3.KemAgreesFor K ↔ KemAgreesShape Interp.real K) ∧
    (∀ K, Tacenta.SessionUnitBraidT3.ValidateEkAgrees K ↔ ValidateEkAgreesShape Interp.real K) ∧
    (Tacenta.SessionUnitBraidT3.KemCloneAgrees ↔ KemCloneAgreesShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT3.BraidHkdfAgrees ↔ HkdfAgreesShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT3.BraidHmacAgrees ↔ HmacAgreesShape Interp.real) ∧
    (TruncatePrefix ↔ TruncatePrefixShape Interp.real) :=
  ⟨KemLenAgrees_is, KemAgreesFor_is, ValidateEkAgrees_is, KemCloneAgrees_is, BraidHkdfAgrees_is,
    BraidHmacAgrees_is, TruncatePrefix_is⟩

/-- **The six Braid refinement agreements about opaque constants of the complete Session unit, the
33 axiom-level shapes of the session contract records, `StdLaws` and the law `TruncatePrefix` hold
in one interpretation of the unit's opaque constants** (`DivCeilValueShape` is among the 33
shapes).  The agreements are stated over `Interp`; `braid_agreement_shapes_are_predicates` binds each
to the real predicate.  The substitution argument transfers a derivation of `False` from the
real statements to this model.  It does not show that the real KEM or KDF meets the agreements. -/
theorem braid_agreements_have_a_model :
    ∃ (I : Interp) (K : Model.Braid.Kem),
      T3Agreements I K ∧ AllT1Shapes I ∧ StdLaws I ∧ TruncatePrefixShape I :=
  ⟨Interp.modelT3, Model.Braid.toyKem, modelT3_t3, modelT3_allT1, modelT3_stdLaws,
    modelT3_truncatePrefix⟩

end Tacenta.UnitSatisfiabilityBraidAgreements

/--
info: 'Tacenta.UnitSatisfiabilityBraidAgreements.braid_agreement_shapes_are_predicates' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilityBraidAgreements.braid_agreement_shapes_are_predicates

/--
info: 'Tacenta.UnitSatisfiabilityBraidAgreements.braid_agreements_have_a_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityBraidAgreements.braid_agreements_have_a_model

/--
info: Tacenta.UnitSatisfiabilityBraidAgreements.braid_agreement_shapes_are_predicates :
  (∀ (K : Model.Braid.Kem),
      Tacenta.SessionUnitBraidT3.KemLenAgrees K ↔
        Tacenta.UnitSatisfiabilityBraidAgreements.KemLenShape Tacenta.UnitSatisfiabilityJoint.Interp.real K) ∧
    (∀ (K : Model.Braid.Kem),
        Tacenta.SessionUnitBraidT3.KemAgreesFor K ↔
          Tacenta.UnitSatisfiabilityBraidAgreements.KemAgreesShape Tacenta.UnitSatisfiabilityJoint.Interp.real K) ∧
      (∀ (K : Model.Braid.Kem),
          Tacenta.SessionUnitBraidT3.ValidateEkAgrees K ↔
            Tacenta.UnitSatisfiabilityBraidAgreements.ValidateEkAgreesShape Tacenta.UnitSatisfiabilityJoint.Interp.real
              K) ∧
        (Tacenta.SessionUnitBraidT3.KemCloneAgrees ↔
            Tacenta.UnitSatisfiabilityBraidAgreements.KemCloneAgreesShape Tacenta.UnitSatisfiabilityJoint.Interp.real) ∧
          (Tacenta.SessionUnitBraidT3.BraidHkdfAgrees ↔
              Tacenta.UnitSatisfiabilityBraidAgreements.HkdfAgreesShape Tacenta.UnitSatisfiabilityJoint.Interp.real) ∧
            (Tacenta.SessionUnitBraidT3.BraidHmacAgrees ↔
                Tacenta.UnitSatisfiabilityBraidAgreements.HmacAgreesShape Tacenta.UnitSatisfiabilityJoint.Interp.real) ∧
              (Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix ↔
                Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefixShape
                  Tacenta.UnitSatisfiabilityJoint.Interp.real)
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityBraidAgreements.braid_agreement_shapes_are_predicates

/--
info: Tacenta.UnitSatisfiabilityBraidAgreements.braid_agreements_have_a_model :
  ∃ I K,
    Tacenta.UnitSatisfiabilityBraidAgreements.T3Agreements I K ∧
      Tacenta.UnitSatisfiabilityBraidAgreements.AllT1Shapes I ∧
        Tacenta.UnitSatisfiabilityJoint.StdLaws I ∧ Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefixShape I
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityBraidAgreements.braid_agreements_have_a_model
