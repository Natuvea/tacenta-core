import Translation.BraidT3
import Translation.ErasureWitness

/-!
# A model of the Braid's KEM boundary

`BraidT3.lean` assumes, as `KemAgreesFor K`, `ValidateEkAgrees K`,
`KemLenAgrees K` and `KemCloneAgrees`, that the opaque `tacenta_kem`
operations compute what a `Model.Braid.Kem` witness `K` says; `BraidT1.lean`
assumes the same operations return, within stated size bounds. Quantified
over every split of a header, the first two would be refutable
(`Satisfiability.lean`), so, as for the erasure boundary, this file exhibits
a model of the hypotheses as stated: an
implementation of the opaque operations, over the model's own `toyKem`,
satisfying every one of them at once. `ErasureWitness.lean` explains the
method; here nothing needs Mathlib, since `toyKem` is arithmetic-free.

A key pair is its randomness (a number); an encapsulation state is `Unit`,
since `toyKem.encaps2` ignores it. Consistency is all this establishes: the
real `tacenta_kem` is ML-KEM-1024, not `toyKem`, and the hypotheses about it
stay assumed.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.KemWitness

open Tacenta.BraidT3 Tacenta.ErasureWitness tacenta_braid

/-! ## The shape: the KEM hypotheses over any implementation -/

/-- The opaque KEM operations and constants, as data. -/
structure KemApi (KP ES : Type) where
  headerLen : Result Usize
  ekVectorLen : Result Usize
  ct1Len : Result Usize
  ct2Len : Result Usize
  generate : {R : Type} → rand_core_1.RngCore R → rand_core_1.CryptoRng R → R →
    Result (core.result.Result KP tacenta_kem.KemError × R)
  header : KP → Result (alloc.vec.Vec Std.U8)
  ekVector : KP → Result (alloc.vec.Vec Std.U8)
  decapsulate : KP → Slice Std.U8 → Slice Std.U8 →
    Result (core.result.Result (Array Std.U8 32#usize) tacenta_kem.KemError)
  cloneKp : KP → Result KP
  encapsulate1 : {R : Type} → rand_core_1.RngCore R → rand_core_1.CryptoRng R →
    Slice Std.U8 → R →
    Result (core.result.Result (ES × alloc.vec.Vec Std.U8 × Array Std.U8 32#usize)
      tacenta_kem.KemError × R)
  encapsulate2 : ES → Slice Std.U8 →
    Result (core.result.Result (alloc.vec.Vec Std.U8) tacenta_kem.KemError)
  cloneEs : ES → Result ES
  validateEk : Slice Std.U8 → Slice Std.U8 → Result Bool

section Shape
variable {KP ES : Type} (A : KemApi KP ES)

def KemLenAgrees (K : Model.Braid.Kem) : Prop :=
  (∃ v, A.headerLen = ok v ∧ v.val = Model.Braid.headerSize) ∧
  (∃ v, A.ekVectorLen = ok v ∧ v.val = K.ekSize) ∧
  (∃ v, A.ct1Len = ok v ∧ v.val = K.ct1Size) ∧
  (∃ v, A.ct2Len = ok v ∧ v.val = K.ct2Size)

def KemAgreesFor (K : Model.Braid.Kem) : Prop :=
  K.Correct ∧
    (∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (rng : R),
      ∃ kp rng' rand,
        A.generate rc crc rng = ok (core.result.Result.Ok kp, rng') ∧
        (∃ h, A.header kp = ok h ∧
          vecOf h = (K.keyGen rand).2.1 ++ K.hashEk (K.keyGen rand).2.1 (K.keyGen rand).2.2) ∧
        (∃ v, A.ekVector kp = ok v ∧ vecOf v = (K.keyGen rand).2.2) ∧
        (∀ ct1 ct2 : Slice Std.U8, ct1.length = K.ct1Size → ct2.length = K.ct2Size →
          ∃ raw : Array Std.U8 32#usize,
            A.decapsulate kp ct1 ct2 = ok (core.result.Result.Ok raw) ∧
            keyOf raw = K.decaps (K.keyGen rand).1 (sliceOf ct1) (sliceOf ct2))) ∧
    (∀ (kp : KP),
      ∃ dk ekSeed ekVector : Bytes,
        (∃ h, A.header kp = ok h ∧ vecOf h = ekSeed ++ K.hashEk ekSeed ekVector) ∧
        (∃ v, A.ekVector kp = ok v ∧ vecOf v = ekVector) ∧
        (∀ ct1 ct2 : Slice Std.U8, ct1.length = K.ct1Size → ct2.length = K.ct2Size →
          ∃ raw : Array Std.U8 32#usize,
            A.decapsulate kp ct1 ct2 = ok (core.result.Result.Ok raw) ∧
            keyOf raw = K.decaps dk (sliceOf ct1) (sliceOf ct2))) ∧
    (∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
        (header : Slice Std.U8) (rng : R), header.length = Model.Braid.headerSize →
      ∃ es ct1raw ssraw rng',
        A.encapsulate1 rc crc header rng =
          ok (core.result.Result.Ok (es, ct1raw, ssraw), rng') ∧
        (∀ ekSeed hek : Bytes, ekSeed.length = 32 → sliceOf header = ekSeed ++ hek →
          (K.encaps1 ekSeed hek).2.1 = vecOf ct1raw ∧
          (K.encaps1 ekSeed hek).2.2 = keyOf ssraw ∧
          (∀ ekVector : Slice Std.U8, ekVector.length = K.ekSize →
            ∃ ct2raw,
              A.encapsulate2 es ekVector = ok (core.result.Result.Ok ct2raw) ∧
              vecOf ct2raw =
                K.encaps2 (K.encaps1 ekSeed hek).1 ekSeed (sliceOf ekVector))))

def ValidateEkAgrees (K : Model.Braid.Kem) : Prop :=
  ∀ (header ekVector : Slice Std.U8) (ekSeed hek : Bytes),
    ekSeed.length = 32 → hek.length = 32 → ekVector.length = K.ekSize →
    sliceOf header = ekSeed ++ hek →
    ∃ r, A.validateEk header ekVector = ok r ∧
      (r = true ↔ K.hashEk ekSeed (sliceOf ekVector) = hek)

def KemCloneAgrees : Prop :=
  (∀ kp kp' : KP,
    A.cloneKp kp = ok kp' →
    (∀ h, A.header kp = ok h → A.header kp' = ok h) ∧
    (∀ v, A.ekVector kp = ok v → A.ekVector kp' = ok v) ∧
    (∀ (ct1 ct2 : Slice Std.U8) raw,
      A.decapsulate kp ct1 ct2 = ok (core.result.Result.Ok raw) →
      A.decapsulate kp' ct1 ct2 = ok (core.result.Result.Ok raw))) ∧
  (∀ es es' : ES,
    A.cloneEs es = ok es' →
    ∀ (ekVector : Slice Std.U8) ct2, A.encapsulate2 es ekVector =
      ok (core.result.Result.Ok ct2) →
      A.encapsulate2 es' ekVector = ok (core.result.Result.Ok ct2))

/-- `BraidT1.lean`'s totality and size-bound assumptions on the same operations. -/
def Totals : Prop :=
  (∃ v : Usize, A.headerLen = ok v ∧ v.val ≤ 4096) ∧
  (∃ v : Usize, A.ekVectorLen = ok v ∧ v.val ≤ 4096) ∧
  (∃ v : Usize, A.ct1Len = ok v ∧ v.val ≤ 4096) ∧
  (∃ v : Usize, A.ct2Len = ok v ∧ v.val ≤ 4096) ∧
  (∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (rng : R),
    ∃ r, A.generate rc crc rng = ok r) ∧
  (∀ (kp : KP), ∃ r : alloc.vec.Vec Std.U8, A.header kp = ok r ∧ r.length ≤ 4096) ∧
  (∀ (kp : KP), ∃ r : alloc.vec.Vec Std.U8, A.ekVector kp = ok r ∧ r.length ≤ 4096) ∧
  (∀ (kp : KP) (a b : Slice Std.U8), ∃ r, A.decapsulate kp a b = ok r) ∧
  (∀ (kp : KP), ∃ r, A.cloneKp kp = ok r) ∧
  (∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (s : Slice Std.U8) (rng : R),
    ∃ r, A.encapsulate1 rc crc s rng = ok r ∧
      ∀ es (ct1 : alloc.vec.Vec Std.U8) raw,
        r.1 = core.result.Result.Ok (es, ct1, raw) → ct1.length ≤ 4096) ∧
  (∀ (es : ES) (s : Slice Std.U8),
    ∃ r, A.encapsulate2 es s = ok r ∧
      ∀ c : alloc.vec.Vec Std.U8, r = core.result.Result.Ok c → c.length ≤ 4096) ∧
  (∀ (es : ES), ∃ r, A.cloneEs es = ok r) ∧
  (∀ (a b : Slice Std.U8), ∃ r, A.validateEk a b = ok r)

end Shape

/-- The real operations, as a `KemApi`. -/
noncomputable def realKemApi : KemApi tacenta_kem.IncrementalKeyPair tacenta_kem.EncapsState where
  headerLen := tacenta_kem.HEADER_LEN
  ekVectorLen := tacenta_kem.EK_VECTOR_LEN
  ct1Len := tacenta_kem.CT1_LEN
  ct2Len := tacenta_kem.CT2_LEN
  generate := fun rc crc rng => tacenta_kem.IncrementalKeyPair.generate rc crc rng
  header := tacenta_kem.IncrementalKeyPair.header
  ekVector := tacenta_kem.IncrementalKeyPair.ek_vector
  decapsulate := tacenta_kem.IncrementalKeyPair.decapsulate
  cloneKp := tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone
  encapsulate1 := fun rc crc s rng => tacenta_kem.encapsulate1 rc crc s rng
  encapsulate2 := tacenta_kem.encapsulate2
  cloneEs := tacenta_kem.EncapsState.Insts.CoreCloneClone.clone
  validateEk := tacenta_kem.validate_ek

/-! ### The concrete hypotheses are the shape at the real operations -/

theorem kemLenAgrees_iff (K : Model.Braid.Kem) :
    Tacenta.BraidT3.KemLenAgrees K ↔ KemLenAgrees realKemApi K := Iff.rfl

theorem kemAgreesFor_iff (K : Model.Braid.Kem) :
    Tacenta.BraidT3.KemAgreesFor K ↔ KemAgreesFor realKemApi K := Iff.rfl

theorem validateEkAgrees_iff (K : Model.Braid.Kem) :
    Tacenta.BraidT3.ValidateEkAgrees K ↔ ValidateEkAgrees realKemApi K := Iff.rfl

theorem kemCloneAgrees_iff : Tacenta.BraidT3.KemCloneAgrees ↔ KemCloneAgrees realKemApi := Iff.rfl

theorem totals_iff :
    (Tacenta.BraidT1.HeaderLenTotal ∧ Tacenta.BraidT1.EkVectorLenTotal ∧
      Tacenta.BraidT1.Ct1LenTotal ∧ Tacenta.BraidT1.Ct2LenTotal ∧
      Tacenta.BraidT1.KeyPairGenerateTotal ∧ Tacenta.BraidT1.KeyPairHeaderTotal ∧
      Tacenta.BraidT1.KeyPairEkVectorTotal ∧ Tacenta.BraidT1.KeyPairDecapsulateTotal ∧
      Tacenta.BraidT1.KeyPairCloneTotal ∧ Tacenta.BraidT1.Encapsulate1Total ∧
      Tacenta.BraidT1.Encapsulate2Total ∧ Tacenta.BraidT1.EncapsStateCloneTotal ∧
      Tacenta.BraidT1.ValidateEkTotal) ↔ Totals realKemApi := Iff.rfl

/-! ## The witness, over `toyKem` -/

theorem usize_max_ge (n : ℕ) (h : n ≤ 2 ^ 32 - 1) : n ≤ Usize.max := by
  simp only [Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq]
  cases System.Platform.numBits_eq <;> simp_all <;> omega

def bytesOf (l : Bytes) : List Std.U8 := l.map ofU8

theorem map_u8_bytesOf (l : Bytes) : (bytesOf l).map u8 = l := by
  simp only [bytesOf, List.map_map]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro b _
  exact u8_ofU8 b

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

/-- `toyKem`'s seed for randomness `r`. -/
def seedOf (r : ℕ) : Bytes := List.replicate 32 (UInt8.ofNat r)
def ekVecOf (r : ℕ) : Bytes := List.replicate 64 (UInt8.ofNat r)

theorem le64 : 64 ≤ Usize.max := usize_max_ge 64 (by norm_num)

/-- The witness: key pairs are their randomness, encapsulation states carry
nothing. -/
def api : KemApi ℕ Unit where
  headerLen := ok 64#usize
  ekVectorLen := ok 64#usize
  ct1Len := ok 64#usize
  ct2Len := ok 32#usize
  generate := fun _ _ rng => ok (core.result.Result.Ok 0, rng)
  header := fun r =>
    ok (vecOfBytes (seedOf r ++ Model.Braid.toyKem.hashEk (seedOf r) (ekVecOf r))
      (by simp [seedOf, Model.Braid.toyKem]; exact le64))
  ekVector := fun r => ok (vecOfBytes (ekVecOf r) (by simp [ekVecOf]; exact le64))
  decapsulate := fun r _ _ => ok (core.result.Result.Ok (arr32 (seedOf r)))
  cloneKp := fun r => ok r
  encapsulate1 := fun _ _ header rng =>
    ok (core.result.Result.Ok ((), vecOfBytes (List.replicate 64 7) (by simp; exact le64),
      arr32 ((sliceOf header).take 32)), rng)
  encapsulate2 := fun _ _ =>
    ok (core.result.Result.Ok (vecOfBytes (List.replicate 32 9)
      (by simp; exact usize_max_ge 32 (by norm_num))))
  cloneEs := fun es => ok es
  validateEk := fun header ekVector =>
    ok (decide (Model.Braid.toyKem.hashEk ((sliceOf header).take 32) (sliceOf ekVector)
      = (sliceOf header).drop 32))

theorem api_lenAgrees : KemLenAgrees api Model.Braid.toyKem := by
  refine ⟨⟨64#usize, rfl, ?_⟩, ⟨64#usize, rfl, ?_⟩, ⟨64#usize, rfl, ?_⟩, ⟨32#usize, rfl, ?_⟩⟩ <;>
    simp [Model.Braid.headerSize, Model.Braid.toyKem]

theorem api_agreesFor : KemAgreesFor api Model.Braid.toyKem := by
  refine ⟨Model.Braid.toyKem_correct, ?_, ?_, ?_⟩
  · intro R rc crc rng
    refine ⟨0, rng, 0, rfl, ⟨_, rfl, ?_⟩, ⟨_, rfl, ?_⟩, ?_⟩
    · rw [vecOf_vecOfBytes]; rfl
    · rw [vecOf_vecOfBytes]; rfl
    · intro ct1 ct2 _ _
      refine ⟨arr32 (seedOf 0), rfl, ?_⟩
      rw [keyOf_arr32 _ (by simp [seedOf])]; rfl
  · intro r
    refine ⟨seedOf r, seedOf r, ekVecOf r, ⟨_, rfl, vecOf_vecOfBytes _ _⟩,
      ⟨_, rfl, vecOf_vecOfBytes _ _⟩, ?_⟩
    intro ct1 ct2 _ _
    refine ⟨arr32 (seedOf r), rfl, ?_⟩
    rw [keyOf_arr32 _ (by simp [seedOf])]; rfl
  · intro R rc crc header rng _
    refine ⟨(), _, arr32 ((sliceOf header).take 32), rng, rfl, ?_⟩
    intro ekSeed hek hlen hsplit
    refine ⟨?_, ?_, ?_⟩
    · rw [vecOf_vecOfBytes]; rfl
    · rw [hsplit, List.take_left' hlen, keyOf_arr32 _ hlen]; rfl
    · intro ekVector _
      refine ⟨_, rfl, ?_⟩
      rw [vecOf_vecOfBytes]; rfl

theorem api_validateEk : ValidateEkAgrees api Model.Braid.toyKem := by
  intro header ekVector ekSeed hek hlen _ _ hsplit
  refine ⟨_, rfl, ?_⟩
  rw [decide_eq_true_iff, hsplit, List.take_left' hlen, List.drop_left' hlen]

theorem api_cloneAgrees : KemCloneAgrees api := by
  refine ⟨?_, ?_⟩
  · intro kp kp' h
    simp only [api, ok.injEq] at h
    subst h
    exact ⟨fun _ h => h, fun _ h => h, fun _ _ _ h => h⟩
  · intro es es' _
    cases es; cases es'
    exact fun _ _ h => h

theorem api_totals : Totals api := by
  refine ⟨⟨64#usize, rfl, by simp⟩, ⟨64#usize, rfl, by simp⟩, ⟨64#usize, rfl, by simp⟩,
    ⟨32#usize, rfl, by simp⟩, fun _ _ rng => ⟨_, rfl⟩, ?_, ?_, fun _ _ _ => ⟨_, rfl⟩,
    fun _ => ⟨_, rfl⟩, ?_, ?_, fun _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩⟩
  · intro kp
    refine ⟨_, rfl, ?_⟩
    rw [length_vecOfBytes]; simp [seedOf, Model.Braid.toyKem]
  · intro kp
    refine ⟨_, rfl, ?_⟩
    rw [length_vecOfBytes]; simp [ekVecOf]
  · intro R rc crc s rng
    refine ⟨_, rfl, ?_⟩
    intro es ct1 raw h
    simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    rw [length_vecOfBytes]; simp
  · intro es s
    refine ⟨_, rfl, ?_⟩
    intro c h
    simp only [core.result.Result.Ok.injEq] at h
    subst h
    rw [length_vecOfBytes]; simp

/-- **The Braid's KEM boundary has a model.** One implementation of the
opaque KEM operations satisfies, over the model's `toyKem`, every KEM
hypothesis `BraidT3.lean` and `BraidT1.lean` take -- the agreements, the
split guard, the size constants, the clone laws and the totals -- at once. -/
theorem kem_hypotheses_satisfiable :
    ∃ (KP ES : Type) (A : KemApi KP ES),
      KemAgreesFor A Model.Braid.toyKem ∧ ValidateEkAgrees A Model.Braid.toyKem ∧
      KemLenAgrees A Model.Braid.toyKem ∧ KemCloneAgrees A ∧ Totals A :=
  ⟨ℕ, Unit, api, api_agreesFor, api_validateEk, api_lenAgrees, api_cloneAgrees, api_totals⟩

end Tacenta.KemWitness
