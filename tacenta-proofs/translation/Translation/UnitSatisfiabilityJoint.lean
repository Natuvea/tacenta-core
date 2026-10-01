import Translation.UnitLifecyclePublicT1

/-!
# One interpretation of the unit's opaque constants for the session contract records

`UnitSatisfiabilitySession.lean` gives one throwaway model per boundary contract, separately.
This module interprets the opaque axioms of `TacentaSessionUnit.lean` that the four contract
records depend on, all at once, and shows that one interpretation satisfies every axiom-level
field of every record, the two model classes (`SessionUnitSessionT1.ZeroizingModel`,
`SessionUnitT1.DerivedKeysModel`) and the laws of `StdLaws`.  `UnitSatisfiabilityRecords.lean`
then proves the four records from that base at the real constants.

## What is here

* `Interp`: a structure with one field per interpreted axiom, at the exact type of the axiom,
  the axiomatised types replaced by the earlier fields.  It has 48 fields: 6 types and 42
  functions and constants.  `Interp.real` packs the real constants and elaborates only if every
  field type is exact.
* One `*Shape` per axiom-level predicate, over the whole interpretation, and a theorem `*_is`
  binding it, at `Interp.real`, to the predicate of the session proofs by `Iff.rfl`, except that
  `VecRetainTotal`, which is half about opaque constants and half about translated loops, is bound
  by regrouping its five conjuncts.  The kernel accepts an `Iff.rfl` binding only if the two unfold
  to the same proposition, and checks the regrouping proof.  `all_shapes_are_predicates` collects
  the 37 bridges, so that one pin holds all of them.
* Each record (`EncryptContracts`, `DecryptRatchetContracts`, `EstablishInitiatorContracts`,
  `EstablishResponderContracts`, with nested records) cut into an axiom part (over `Interp`) and
  a defined part (over the real translated functions), with `toParts` and `ofParts` functions
  that repack every field.  A field left out of both parts fails to elaborate.
* `Interp.model`: the joint model, and a proof of every shape in it (`model_satisfies_all_axiom_shapes`
  names them all, so removing a witness breaks the module).
* `StdLaws`: the laws about standard-library and `zeroize` operations that the proofs of the defined-function
  fields use and no record states.  `FaithfulShape` says the model's versions of those operations
  are the real operations and not degenerate functions with the weak property.
* Controls: bridges that must be rejected, and models that break one faithful field and must
  make its shape false.

## What it shows

There is one interpretation of the axioms under which every axiom-level field of the four
records holds together.  Because each axiom the records reach is an uninterpreted constant, a derivation of `False`
from the axiom-level fields in the real environment would give, by substituting the model for the
constants, a derivation of `False` in the model.  So those fields are jointly consistent with
each other, with the two classes and with `StdLaws`.  That last step is an argument about
derivations and not a theorem inside Lean.

## What it does not show

* It does not cover the defined-function fields.  Their truth is fixed by the translated bodies.  A
  record is inhabited exactly when its axiom part and its defined part are (`encrypt_iff_parts`
  and its siblings); the defined part is proved from `StdLaws` in `UnitSatisfiabilityErasure.lean`,
  `UnitSatisfiabilityRatchet.lean` and `UnitSatisfiabilityRecords.lean`.
* It does not say that the real primitives satisfy any field or any law.
* The error type inside `RngCore` (`rand_core_1.error.Error`) is the one axiom that occurs in a
  shape and is not interpreted: no contract looks at it.
* It does not cover the headroom records.
* The classification (which field is axiom-level, which is defined) is checked by the audit text in
  `tacenta-proofs/scripts/check-session-satisfiability-negatives.sh`, which that script runs, and not by
  this build.
-/

namespace Tacenta.UnitSatisfiabilityJoint

open Aeneas Aeneas.Std Result
open tacenta_session_unit

abbrev Np {α : Type} (e : Result α) : Prop := ∃ r, e = ok r

/-- One interpretation of the opaque axioms of `TacentaSessionUnit.lean` that
the four session contract records depend on.  Every field has exactly the type
of the axiom it interprets, with the axiomatised types replaced by the earlier
fields of this structure. -/
structure Interp where
  /- types -/
  PrivateKey : Type
  PublicKeyBytes : Type
  KemKeyPair : Type
  IncrementalKeyPair : Type
  EncapsState : Type
  Zeroizing : Type → Type
  /- boundary: Diffie-Hellman -/
  dhPrivFromBytes : Array U8 32#usize → Result PrivateKey
  dhPrivPublicKey : PrivateKey → Result PublicKeyBytes
  dhPrivAgree : PrivateKey → PublicKeyBytes → Result (Option (Array U8 32#usize))
  dhPrivToBytes : PrivateKey → Result (Zeroizing (Array U8 32#usize))
  dhPubFromBytes : Array U8 32#usize → Result PublicKeyBytes
  dhPubAsBytes : PublicKeyBytes → Result (Array U8 32#usize)
  dhPubEq : PublicKeyBytes → PublicKeyBytes → Result Bool
  dhIsPrimeOrderPublic : PublicKeyBytes → Result Bool
  /- boundary: AEAD, KEM, XEdDSA -/
  aeadEncrypt : Array U8 32#usize → Array U8 32#usize → Array U8 16#usize →
    Slice U8 → Slice U8 → Result (alloc.vec.Vec U8)
  aeadDecrypt : Array U8 32#usize → Array U8 32#usize → Array U8 16#usize →
    Slice U8 → Slice U8 →
    Result (core.result.Result (alloc.vec.Vec U8) tacenta_boundary.aead.DecryptError)
  kemEncapsulate : {R : Type} → rand_core_1.RngCore R → rand_core_1.CryptoRng R →
    Slice U8 → R →
    Result (core.result.Result (alloc.vec.Vec U8 × Array U8 32#usize)
      tacenta_boundary.kem.KemError × R)
  kemDecapsulate : KemKeyPair → Slice U8 →
    Result (core.result.Result (Array U8 32#usize) tacenta_boundary.kem.KemError)
  xeddsaVerify : PublicKeyBytes → Slice U8 → Array U8 64#usize →
    Result (core.result.Result Unit tacenta_boundary.xeddsa.VerifyError)
  /- KDFs -/
  hkdfSha256 : (N : Usize) → Slice U8 → Slice U8 → Slice U8 → Result (Array U8 N)
  hmacSha256 : Slice U8 → Slice U8 → Result (Array U8 32#usize)
  /- the incremental KEM -/
  HEADER_LEN : Result Usize
  EK_VECTOR_LEN : Result Usize
  CT1_LEN : Result Usize
  CT2_LEN : Result Usize
  ikpClone : IncrementalKeyPair → Result IncrementalKeyPair
  ikpGenerate : {R : Type} → rand_core_1.RngCore R → rand_core_1.CryptoRng R → R →
    Result (core.result.Result IncrementalKeyPair tacenta_kem.KemError × R)
  ikpHeader : IncrementalKeyPair → Result (alloc.vec.Vec U8)
  ikpEkVector : IncrementalKeyPair → Result (alloc.vec.Vec U8)
  ikpDecapsulate : IncrementalKeyPair → Slice U8 → Slice U8 →
    Result (core.result.Result (Array U8 32#usize) tacenta_kem.KemError)
  esClone : EncapsState → Result EncapsState
  encapsulate1 : {R : Type} → rand_core_1.RngCore R → rand_core_1.CryptoRng R →
    Slice U8 → R →
    Result (core.result.Result (EncapsState × alloc.vec.Vec U8 × Array U8 32#usize)
      tacenta_kem.KemError × R)
  encapsulate2 : EncapsState → Slice U8 →
    Result (core.result.Result (alloc.vec.Vec U8) tacenta_kem.KemError)
  validateEk : Slice U8 → Slice U8 → Result Bool
  /- the `zeroize` crate -/
  blanketZeroize : {Z : Type} → zeroize.DefaultIsZeroes Z → Z → Result Z
  arrayZeroize : {Z : Type} → {N : Usize} → zeroize.Zeroize Z →
    Array Z N → Result (Array Z N)
  tupleZeroize : {A B C : Type} → zeroize.Zeroize A → zeroize.Zeroize B →
    zeroize.Zeroize C → A × B × C → Result (A × B × C)
  vecZeroize : {Z : Type} → zeroize.Zeroize Z → alloc.vec.Vec Z → Result (alloc.vec.Vec Z)
  zNew : {Z : Type} → zeroize.Zeroize Z → Z → Result (Zeroizing Z)
  zDeref : {Z : Type} → zeroize.Zeroize Z → Zeroizing Z → Result Z
  zDerefMut : {Z : Type} → zeroize.Zeroize Z → Zeroizing Z →
    Result (Z × (Z → Zeroizing Z))
  /- standard library operations Aeneas leaves opaque -/
  vecPop : {T : Type} → Type → alloc.vec.Vec T → Result (Option T × alloc.vec.Vec T)
  vecCapacity : {T : Type} → Type → alloc.vec.Vec T → Result Usize
  vecTruncate : {T : Type} → Type → alloc.vec.Vec T → Usize → Result (alloc.vec.Vec T)
  optionClone : {T : Type} → core.clone.Clone T → Option T → Result (Option T)
  optionAsMut : {T : Type} → Option T → Result (Option T × (Option T → Option T))
  rangeFullIndex : {T : Type} → core.ops.range.RangeFull → Slice T → Result (Slice T)
  divCeil : Usize → Usize → Result Usize

/-- The real constants, packaged.  Each field elaborates only if the real
axiom has exactly the field's type. -/
noncomputable def Interp.real : Interp where
  PrivateKey := tacenta_boundary.dh.PrivateKey
  PublicKeyBytes := tacenta_boundary.dh.PublicKeyBytes
  KemKeyPair := tacenta_boundary.kem.KeyPair
  IncrementalKeyPair := tacenta_kem.IncrementalKeyPair
  EncapsState := tacenta_kem.EncapsState
  Zeroizing := zeroize.Zeroizing
  dhPrivFromBytes := tacenta_boundary.dh.PrivateKey.from_bytes
  dhPrivPublicKey := tacenta_boundary.dh.PrivateKey.public_key
  dhPrivAgree := tacenta_boundary.dh.PrivateKey.agree
  dhPrivToBytes := tacenta_boundary.dh.PrivateKey.to_bytes
  dhPubFromBytes := tacenta_boundary.dh.PublicKeyBytes.from_bytes
  dhPubAsBytes := tacenta_boundary.dh.PublicKeyBytes.as_bytes
  dhPubEq := tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq
  dhIsPrimeOrderPublic := tacenta_boundary.dh.is_prime_order_public
  aeadEncrypt := tacenta_boundary.aead.encrypt
  aeadDecrypt := tacenta_boundary.aead.decrypt
  kemEncapsulate := @tacenta_boundary.kem.encapsulate
  kemDecapsulate := tacenta_boundary.kem.decapsulate
  xeddsaVerify := tacenta_boundary.xeddsa.verify
  hkdfSha256 := tacenta_kdf.hkdf_sha256
  hmacSha256 := tacenta_kdf.hmac_sha256
  HEADER_LEN := tacenta_kem.HEADER_LEN
  EK_VECTOR_LEN := tacenta_kem.EK_VECTOR_LEN
  CT1_LEN := tacenta_kem.CT1_LEN
  CT2_LEN := tacenta_kem.CT2_LEN
  ikpClone := tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone
  ikpGenerate := @tacenta_kem.IncrementalKeyPair.generate
  ikpHeader := tacenta_kem.IncrementalKeyPair.header
  ikpEkVector := tacenta_kem.IncrementalKeyPair.ek_vector
  ikpDecapsulate := tacenta_kem.IncrementalKeyPair.decapsulate
  esClone := tacenta_kem.EncapsState.Insts.CoreCloneClone.clone
  encapsulate1 := @tacenta_kem.encapsulate1
  encapsulate2 := tacenta_kem.encapsulate2
  validateEk := tacenta_kem.validate_ek
  blanketZeroize := @zeroize.Zeroize.Blanket.zeroize
  arrayZeroize := @Array.Insts.ZeroizeZeroize.zeroize
  tupleZeroize := @TupleABC.Insts.ZeroizeZeroize.zeroize
  vecZeroize := @alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
  zNew := @zeroize.Zeroizing.new
  zDeref := @zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
  zDerefMut := @zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut
  vecPop := @alloc.vec.Vec.pop
  vecCapacity := @alloc.vec.Vec.capacity
  vecTruncate := @alloc.vec.Vec.truncate
  optionClone := @core.option.Option.Insts.CoreCloneClone.clone
  optionAsMut := @core.option.Option.as_mut
  rangeFullIndex := @core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index
  divCeil := core.num.Usize.div_ceil

/-! ## Zeroize instance records over an interpretation

The contracts that mention a `Zeroize` instance record at a fixed type
(`MessageKeyMaterialRoundTrip`) see the three `zeroize` axioms through the
instance definitions.  Over an interpretation the same records are built from
the interpretation's own functions. -/

def Interp.blanket (I : Interp) {Z : Type} (d : zeroize.DefaultIsZeroes Z) :
    zeroize.Zeroize Z := ⟨I.blanketZeroize d⟩

def Interp.arrayInst (I : Interp) {Z : Type} (N : Usize) (inst : zeroize.Zeroize Z) :
    zeroize.Zeroize (Array Z N) := ⟨I.arrayZeroize inst⟩

def Interp.tupleInst (I : Interp) {A B C : Type} (a : zeroize.Zeroize A)
    (b : zeroize.Zeroize B) (c : zeroize.Zeroize C) :
    zeroize.Zeroize (A × B × C) := ⟨I.tupleZeroize a b c⟩

def Interp.mkmInst (I : Interp) :
    zeroize.Zeroize Tacenta.UnitLifecycleT1.MessageKeyMaterial :=
  I.tupleInst
    (I.arrayInst 32#usize (I.blanket U8.Insts.ZeroizeDefaultIsZeroes))
    (I.arrayInst 32#usize (I.blanket U8.Insts.ZeroizeDefaultIsZeroes))
    (I.arrayInst 16#usize (I.blanket U8.Insts.ZeroizeDefaultIsZeroes))

/-! ## Shapes of the axiom-level contracts

One `Shape` per predicate, over the whole interpretation `I`.  Each `_is`
theorem binds the shape, at `Interp.real`, to the predicate of the session
proofs by `Iff.rfl`: the kernel accepts it only if the two unfold to the same
proposition.  The one exception is `VecRetainTotal_is`, which regroups the five
conjuncts of `VecRetainTotal` into the axiom half and the three loop contracts,
and whose proof the kernel checks. -/

def DhCodecShape (I : Interp) : Prop :=
  (∀ a, Np (I.dhPrivFromBytes a)) ∧
  (∀ k, Np (I.dhPrivPublicKey k)) ∧
  (∀ k, Np (I.dhPrivToBytes k)) ∧
  (∀ a, Np (I.dhPubFromBytes a)) ∧
  (∀ k, Np (I.dhPubAsBytes k)) ∧
  (∀ a b, Np (I.dhPubEq a b))

theorem DhCodecTotal_is :
    Tacenta.UnitLifecycleT1.DhCodecTotal ↔ DhCodecShape Interp.real := Iff.rfl

def DhIdentityShape (I : Interp) : Prop := ∀ k, Np (I.dhIsPrimeOrderPublic k)

theorem DhIdentityTotal_is :
    Tacenta.UnitLifecycleT1.DhIdentityTotal ↔ DhIdentityShape Interp.real := Iff.rfl

def DhAgreeShape (I : Interp) : Prop := ∀ k p, Np (I.dhPrivAgree k p)

theorem DhAgreeTotal_is :
    Tacenta.UnitLifecycleT1.DhAgreeTotal ↔ DhAgreeShape Interp.real := Iff.rfl

def KemEncapsulateShape (I : Interp) : Prop :=
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (cr : rand_core_1.CryptoRng R) p r,
    Tacenta.UnitLifecycleT1.RngTotal rc → Np (I.kemEncapsulate rc cr p r)

theorem KemEncapsulateTotal_is :
    Tacenta.UnitLifecycleT1.KemEncapsulateTotal ↔ KemEncapsulateShape Interp.real := Iff.rfl

def KemDecapsulateShape (I : Interp) : Prop := ∀ k c, Np (I.kemDecapsulate k c)

theorem KemDecapsulateTotal_is :
    Tacenta.UnitLifecycleT1.KemDecapsulateTotal ↔ KemDecapsulateShape Interp.real := Iff.rfl

def XeddsaVerifyShape (I : Interp) : Prop := ∀ p m s, Np (I.xeddsaVerify p m s)

theorem XeddsaVerifyTotal_is :
    Tacenta.UnitLifecycleT1.XeddsaVerifyTotal ↔ XeddsaVerifyShape Interp.real := Iff.rfl

def AeadOpenShape (I : Interp) : Prop :=
  ∀ ek mk n c ad, Np (I.aeadDecrypt ek mk n c ad)

theorem AeadOpenTotal_is :
    Tacenta.UnitLifecycleT1.AeadOpenTotal ↔ AeadOpenShape Interp.real := Iff.rfl

def AeadSealBoundedShape (I : Interp) : Prop :=
  ∀ ek mk : Array U8 32#usize, ∀ iv : Array U8 16#usize,
    ∀ plaintext ad : Slice U8, ∃ r,
      I.aeadEncrypt ek mk iv plaintext ad = ok r ∧
      r.val.length ≤ plaintext.val.length + 48

theorem AeadSealBounded_is :
    Tacenta.UnitLifecycleT1.AeadSealBounded ↔ AeadSealBoundedShape Interp.real := Iff.rfl

def MessageKeyMaterialRoundTripShape (I : Interp) : Prop :=
  ∀ t : Tacenta.UnitLifecycleT1.MessageKeyMaterial, ∃ z,
    I.zNew I.mkmInst t = ok z ∧ I.zDeref I.mkmInst z = ok t

theorem MessageKeyMaterialRoundTrip_is :
    Tacenta.UnitLifecycleT1.MessageKeyMaterialRoundTrip ↔
      MessageKeyMaterialRoundTripShape Interp.real := Iff.rfl

def VecPopShape (I : Interp) : Prop :=
  ∀ (T : Type) (v : alloc.vec.Vec T), ∃ r, I.vecPop Global v = ok r

theorem VecPopTotal_is :
    Tacenta.UnitLifecycleT1.VecPopTotal ↔ VecPopShape Interp.real := Iff.rfl

/-- One shape for the three copies of the key derivation contract. -/
def HkdfShape (I : Interp) : Prop :=
  ∀ (N : Usize) (a b c : Slice U8), N.val ≤ 8160 → ∃ r, I.hkdfSha256 N a b c = ok r

theorem SessionHkdfTotal_is :
    Tacenta.SessionUnitSessionT1.HkdfTotal ↔ HkdfShape Interp.real := Iff.rfl
theorem TripleHkdfTotal_is :
    Tacenta.SessionUnitT1.HkdfTotal ↔ HkdfShape Interp.real := Iff.rfl
theorem BraidHkdfTotal_is :
    Tacenta.SessionUnitBraidT1.HkdfSha256Total ↔ HkdfShape Interp.real := Iff.rfl

def HmacShape (I : Interp) : Prop := ∀ (a b : Slice U8), ∃ r, I.hmacSha256 a b = ok r

theorem TripleHmacTotal_is :
    Tacenta.SessionUnitT1.HmacTotal ↔ HmacShape Interp.real := Iff.rfl
theorem BraidHmacTotal_is :
    Tacenta.SessionUnitBraidT1.HmacSha256Total ↔ HmacShape Interp.real := Iff.rfl

def ZeroizingTotalShape (I : Interp) : Prop :=
  ∀ inst : zeroize.Zeroize (Array U8 64#usize),
    (∀ z, ∃ r, I.zNew inst z = ok r) ∧
    (∀ z, ∃ r, I.zDeref inst z = ok r)

theorem ZeroizingTotal_is :
    Tacenta.SessionUnitT1.ZeroizingTotal ↔ ZeroizingTotalShape Interp.real := Iff.rfl

def SpqrZeroizeShape (I : Interp) : Prop :=
  ∀ {Z : Type} {N : Usize} (inst : zeroize.Zeroize Z) (a : Array Z N),
    ∃ r, I.arrayZeroize inst a = ok r

theorem SpqrZeroizeTotal_is :
    Tacenta.SessionUnitSpqrT1.ZeroizeTotal ↔ SpqrZeroizeShape Interp.real := Iff.rfl

/-- The axiom-level half of `VecRetainTotal`: its first two conjuncts. The
other three conjuncts mention translated loops and stay with the defined part. -/
def VecRetainAxiomShape (I : Interp) : Prop :=
  (∀ {T : Type} (A : Type) (v : alloc.vec.Vec T), ∃ r, I.vecCapacity A v = ok r) ∧
  (∀ {T : Type} (inst : zeroize.Zeroize T) (v : alloc.vec.Vec T),
    ∃ r, I.vecZeroize inst v = ok r)

def VecRetainLoops : Prop :=
  Tacenta.SessionUnitSpqrT1.SetChainsLoopTotal ∧
  Tacenta.SessionUnitSpqrT1.ClearChainsLoop0Total ∧
  Tacenta.SessionUnitSpqrT1.ClearSkippedLoopTotal

theorem VecRetainTotal_is :
    Tacenta.SessionUnitSpqrT1.VecRetainTotal ↔
      VecRetainAxiomShape Interp.real ∧ VecRetainLoops :=
  ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

def OptionCloneShape (I : Interp) : Prop :=
  ∀ {T : Type} (inst : core.clone.Clone T) (o : Option T),
    (∀ x, o = some x → inst.clone x ⦃ fun y => y = x ⦄) →
    I.optionClone inst o ⦃ fun o' => o' = o ⦄

theorem SpqrOptionCloneTotal_is :
    Tacenta.SessionUnitSpqrT1.OptionCloneTotal ↔ OptionCloneShape Interp.real := Iff.rfl
theorem BraidOptionCloneTotal_is :
    Tacenta.SessionUnitBraidT1.OptionCloneTotal ↔ OptionCloneShape Interp.real := Iff.rfl

def Ct1LenShape (I : Interp) : Prop := ∃ v : Usize, I.CT1_LEN = ok v ∧ v.val ≤ 4096
def Ct2LenShape (I : Interp) : Prop := ∃ v : Usize, I.CT2_LEN = ok v ∧ v.val ≤ 4096
def HeaderLenShape (I : Interp) : Prop := ∃ v : Usize, I.HEADER_LEN = ok v ∧ v.val ≤ 4096
def EkVectorLenShape (I : Interp) : Prop :=
  ∃ v : Usize, I.EK_VECTOR_LEN = ok v ∧ v.val ≤ 4096

theorem Ct1LenTotal_is :
    Tacenta.SessionUnitBraidT1.Ct1LenTotal ↔ Ct1LenShape Interp.real := Iff.rfl
theorem Ct2LenTotal_is :
    Tacenta.SessionUnitBraidT1.Ct2LenTotal ↔ Ct2LenShape Interp.real := Iff.rfl
theorem HeaderLenTotal_is :
    Tacenta.SessionUnitBraidT1.HeaderLenTotal ↔ HeaderLenShape Interp.real := Iff.rfl
theorem EkVectorLenTotal_is :
    Tacenta.SessionUnitBraidT1.EkVectorLenTotal ↔ EkVectorLenShape Interp.real := Iff.rfl

def KeyPairEkVectorShape (I : Interp) : Prop :=
  ∀ kp : I.IncrementalKeyPair, ∃ r : alloc.vec.Vec U8,
    I.ikpEkVector kp = ok r ∧ r.length ≤ 4096

theorem KeyPairEkVectorTotal_is :
    Tacenta.SessionUnitBraidT1.KeyPairEkVectorTotal ↔ KeyPairEkVectorShape Interp.real :=
  Iff.rfl

def KeyPairHeaderShape (I : Interp) : Prop :=
  ∀ kp : I.IncrementalKeyPair, ∃ r : alloc.vec.Vec U8,
    I.ikpHeader kp = ok r ∧ r.length ≤ 4096

theorem KeyPairHeaderTotal_is :
    Tacenta.SessionUnitBraidT1.KeyPairHeaderTotal ↔ KeyPairHeaderShape Interp.real :=
  Iff.rfl

def KeyPairDecapsulateShape (I : Interp) : Prop :=
  ∀ (kp : I.IncrementalKeyPair) (a b : Slice U8), ∃ r, I.ikpDecapsulate kp a b = ok r

theorem KeyPairDecapsulateTotal_is :
    Tacenta.SessionUnitBraidT1.KeyPairDecapsulateTotal ↔
      KeyPairDecapsulateShape Interp.real := Iff.rfl

def KeyPairCloneShape (I : Interp) : Prop :=
  ∀ kp : I.IncrementalKeyPair, ∃ r, I.ikpClone kp = ok r

theorem KeyPairCloneTotal_is :
    Tacenta.SessionUnitBraidT1.KeyPairCloneTotal ↔ KeyPairCloneShape Interp.real := Iff.rfl

def EncapsStateCloneShape (I : Interp) : Prop :=
  ∀ es : I.EncapsState, ∃ r, I.esClone es = ok r

theorem EncapsStateCloneTotal_is :
    Tacenta.SessionUnitBraidT1.EncapsStateCloneTotal ↔ EncapsStateCloneShape Interp.real :=
  Iff.rfl

def ValidateEkShape (I : Interp) : Prop :=
  ∀ (a b : Slice U8), ∃ r, I.validateEk a b = ok r

theorem ValidateEkTotal_is :
    Tacenta.SessionUnitBraidT1.ValidateEkTotal ↔ ValidateEkShape Interp.real := Iff.rfl

def KeyPairGenerateShape (I : Interp) : Prop :=
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (rng : R),
    Tacenta.SessionUnitBraidT1.RngTotal rc → ∃ r, I.ikpGenerate rc crc rng = ok r

theorem KeyPairGenerateTotal_is :
    Tacenta.SessionUnitBraidT1.KeyPairGenerateTotal ↔ KeyPairGenerateShape Interp.real :=
  Iff.rfl

def Encapsulate1Shape (I : Interp) : Prop :=
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (s : Slice U8) (rng : R), Tacenta.SessionUnitBraidT1.RngTotal rc →
    ∃ r, I.encapsulate1 rc crc s rng = ok r ∧
      ∀ es (ct1 : alloc.vec.Vec U8) raw,
        r.1 = core.result.Result.Ok (es, ct1, raw) → ct1.length ≤ 4096

theorem Encapsulate1Total_is :
    Tacenta.SessionUnitBraidT1.Encapsulate1Total ↔ Encapsulate1Shape Interp.real := Iff.rfl

def Encapsulate2Shape (I : Interp) : Prop :=
  ∀ (es : I.EncapsState) (s : Slice U8),
    ∃ r, I.encapsulate2 es s = ok r ∧
      ∀ c : alloc.vec.Vec U8, r = core.result.Result.Ok c → c.length ≤ 4096

theorem Encapsulate2Total_is :
    Tacenta.SessionUnitBraidT1.Encapsulate2Total ↔ Encapsulate2Shape Interp.real := Iff.rfl

def ZeroizingArrayRoundTripShape (I : Interp) : Prop :=
  ∀ (N : Usize) (inst : zeroize.Zeroize (Array U8 N)) (a : Array U8 N),
    ∃ z, I.zNew inst a = ok z ∧ I.zDeref inst z = ok a

theorem ZeroizingArrayRoundTrip_is :
    Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip ↔
      ZeroizingArrayRoundTripShape Interp.real := Iff.rfl

def ArrayZeroizeShape (I : Interp) : Prop :=
  ∀ (N : Usize) (inst : zeroize.Zeroize U8) (a : Array U8 N),
    ∃ r, I.arrayZeroize (N := N) inst a = ok r

theorem ArrayZeroizeTotal_is :
    Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal ↔ ArrayZeroizeShape Interp.real := Iff.rfl

def RangeFullIndexShape (I : Interp) : Prop :=
  ∀ (s : Slice U8), I.rangeFullIndex () s = ok s

theorem RangeFullIndexTotal_is :
    Tacenta.SessionUnitBraidT1.RangeFullIndexTotal ↔ RangeFullIndexShape Interp.real :=
  Iff.rfl

/-- The value of `usize::div_ceil` at divisor 32, the field `divCeilValue` of
`EstablishResponderContracts`. -/
def DivCeilValueShape (I : Interp) : Prop :=
  ∀ a : Usize, ∃ r, I.divCeil a 32#usize = ok r ∧ r.val = (a.val + 31) / 32

theorem DivCeilValue_is :
    Tacenta.SessionUnitDecoderBound.DivCeilValue ↔ DivCeilValueShape Interp.real := Iff.rfl

/-- Every shape, at `Interp.real`, is the predicate of the session proofs it replaces.  Thirty-six
of the individual bridges above are proved by `Iff.rfl`, so the kernel checks that the two sides
unfold to the same proposition; the thirty-seventh, `VecRetainTotal_is`, regroups conjuncts and the
kernel checks that proof.  This theorem collects them so that one axiom pin holds all of them. -/
theorem all_shapes_are_predicates :
    (Tacenta.UnitLifecycleT1.DhCodecTotal ↔ DhCodecShape Interp.real) ∧
    (Tacenta.UnitLifecycleT1.DhIdentityTotal ↔ DhIdentityShape Interp.real) ∧
    (Tacenta.UnitLifecycleT1.DhAgreeTotal ↔ DhAgreeShape Interp.real) ∧
    (Tacenta.UnitLifecycleT1.KemEncapsulateTotal ↔ KemEncapsulateShape Interp.real) ∧
    (Tacenta.UnitLifecycleT1.KemDecapsulateTotal ↔ KemDecapsulateShape Interp.real) ∧
    (Tacenta.UnitLifecycleT1.XeddsaVerifyTotal ↔ XeddsaVerifyShape Interp.real) ∧
    (Tacenta.UnitLifecycleT1.AeadOpenTotal ↔ AeadOpenShape Interp.real) ∧
    (Tacenta.UnitLifecycleT1.AeadSealBounded ↔ AeadSealBoundedShape Interp.real) ∧
    (Tacenta.UnitLifecycleT1.MessageKeyMaterialRoundTrip ↔ MessageKeyMaterialRoundTripShape Interp.real) ∧
    (Tacenta.UnitLifecycleT1.VecPopTotal ↔ VecPopShape Interp.real) ∧
    (Tacenta.SessionUnitSessionT1.HkdfTotal ↔ HkdfShape Interp.real) ∧
    (Tacenta.SessionUnitT1.HkdfTotal ↔ HkdfShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.HkdfSha256Total ↔ HkdfShape Interp.real) ∧
    (Tacenta.SessionUnitT1.HmacTotal ↔ HmacShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.HmacSha256Total ↔ HmacShape Interp.real) ∧
    (Tacenta.SessionUnitT1.ZeroizingTotal ↔ ZeroizingTotalShape Interp.real) ∧
    (Tacenta.SessionUnitSpqrT1.ZeroizeTotal ↔ SpqrZeroizeShape Interp.real) ∧
    (Tacenta.SessionUnitSpqrT1.VecRetainTotal ↔ VecRetainAxiomShape Interp.real ∧ VecRetainLoops) ∧
    (Tacenta.SessionUnitSpqrT1.OptionCloneTotal ↔ OptionCloneShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.OptionCloneTotal ↔ OptionCloneShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.Ct1LenTotal ↔ Ct1LenShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.Ct2LenTotal ↔ Ct2LenShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.HeaderLenTotal ↔ HeaderLenShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.EkVectorLenTotal ↔ EkVectorLenShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.KeyPairEkVectorTotal ↔ KeyPairEkVectorShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.KeyPairHeaderTotal ↔ KeyPairHeaderShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.KeyPairDecapsulateTotal ↔ KeyPairDecapsulateShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.KeyPairCloneTotal ↔ KeyPairCloneShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.EncapsStateCloneTotal ↔ EncapsStateCloneShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.ValidateEkTotal ↔ ValidateEkShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.KeyPairGenerateTotal ↔ KeyPairGenerateShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.Encapsulate1Total ↔ Encapsulate1Shape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.Encapsulate2Total ↔ Encapsulate2Shape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip ↔ ZeroizingArrayRoundTripShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal ↔ ArrayZeroizeShape Interp.real) ∧
    (Tacenta.SessionUnitBraidT1.RangeFullIndexTotal ↔ RangeFullIndexShape Interp.real) ∧
    (Tacenta.SessionUnitDecoderBound.DivCeilValue ↔ DivCeilValueShape Interp.real) :=
  ⟨DhCodecTotal_is, DhIdentityTotal_is, DhAgreeTotal_is, KemEncapsulateTotal_is,
    KemDecapsulateTotal_is, XeddsaVerifyTotal_is, AeadOpenTotal_is, AeadSealBounded_is,
    MessageKeyMaterialRoundTrip_is, VecPopTotal_is, SessionHkdfTotal_is, TripleHkdfTotal_is,
    BraidHkdfTotal_is, TripleHmacTotal_is, BraidHmacTotal_is, ZeroizingTotal_is,
    SpqrZeroizeTotal_is, VecRetainTotal_is, SpqrOptionCloneTotal_is, BraidOptionCloneTotal_is,
    Ct1LenTotal_is, Ct2LenTotal_is, HeaderLenTotal_is, EkVectorLenTotal_is,
    KeyPairEkVectorTotal_is, KeyPairHeaderTotal_is, KeyPairDecapsulateTotal_is,
    KeyPairCloneTotal_is, EncapsStateCloneTotal_is, ValidateEkTotal_is, KeyPairGenerateTotal_is,
    Encapsulate1Total_is, Encapsulate2Total_is, ZeroizingArrayRoundTrip_is,
    ArrayZeroizeTotal_is, RangeFullIndexTotal_is, DivCeilValue_is⟩

/-! ### The two classes

`ZeroizingModel` and `DerivedKeysModel` carry data (a `contents` function), so
their shape is a structure and the bridge is a pair of repacking functions whose
round trips are `rfl`. -/

structure ZeroizingModelShape (I : Interp) (Z : Type) where
  contents : I.Zeroizing Z → Z
  new : ∀ (inst : zeroize.Zeroize Z) (v : Z), I.zNew inst v ⦃ fun z => contents z = v ⦄
  deref : ∀ (inst : zeroize.Zeroize Z) (z : I.Zeroizing Z),
    I.zDeref inst z ⦃ fun v => v = contents z ⦄
  deref_mut : ∀ (inst : zeroize.Zeroize Z) (z : I.Zeroizing Z),
    I.zDerefMut inst z ⦃ fun p => p.1 = contents z ∧ ∀ v', contents (p.2 v') = v' ⦄

abbrev SessionZ := alloc.vec.Vec U8
abbrev DerivedZ := alloc.vec.Vec (U32 × Array U8 32#usize)

def ZeroizingModelShape.ofSession (m : Tacenta.SessionUnitSessionT1.ZeroizingModel) :
    ZeroizingModelShape Interp.real SessionZ := ⟨m.contents, m.new, m.deref, m.deref_mut⟩

@[reducible] def ZeroizingModelShape.toSession (s : ZeroizingModelShape Interp.real SessionZ) :
    Tacenta.SessionUnitSessionT1.ZeroizingModel :=
  ⟨s.contents, s.new, s.deref, s.deref_mut⟩

def ZeroizingModelShape.ofDerived (m : Tacenta.SessionUnitT1.DerivedKeysModel) :
    ZeroizingModelShape Interp.real DerivedZ := ⟨m.contents, m.new, m.deref, m.deref_mut⟩

@[reducible] def ZeroizingModelShape.toDerived (s : ZeroizingModelShape Interp.real DerivedZ) :
    Tacenta.SessionUnitT1.DerivedKeysModel :=
  ⟨s.contents, s.new, s.deref, s.deref_mut⟩

theorem ZeroizingModelShape.session_roundtrip (m : Tacenta.SessionUnitSessionT1.ZeroizingModel) :
    (ZeroizingModelShape.ofSession m).toSession = m := rfl
theorem ZeroizingModelShape.session_roundtrip' (s : ZeroizingModelShape Interp.real SessionZ) :
    ZeroizingModelShape.ofSession s.toSession = s := rfl
theorem ZeroizingModelShape.derived_roundtrip (m : Tacenta.SessionUnitT1.DerivedKeysModel) :
    (ZeroizingModelShape.ofDerived m).toDerived = m := rfl
theorem ZeroizingModelShape.derived_roundtrip' (s : ZeroizingModelShape Interp.real DerivedZ) :
    ZeroizingModelShape.ofDerived s.toDerived = s := rfl


/-! ## The four records, split into an axiom part and a defined part

Each record of `UnitLifecyclePublicT1.lean` is cut into the fields that mention
only opaque axioms (over the interpretation, `*Axiom`) and the fields that
mention translated functions (`*Defined`, stated over the real constants).  The
`toParts` and `ofParts` functions repack every field, so a field left out of
both parts, or placed in the wrong one, fails to elaborate. -/

section Parts

open Tacenta.UnitLifecycleT1

structure BraidSendAxiom (I : Interp) {R : Type} (rc : rand_core_1.RngCore R) : Prop where
  rng : Tacenta.SessionUnitBraidT1.RngTotal rc
  keyPairClone : KeyPairCloneShape I
  encapsStateClone : EncapsStateCloneShape I
  keyPairGenerate : KeyPairGenerateShape I
  keyPairHeader : KeyPairHeaderShape I
  hmac : HmacShape I
  hkdf : HkdfShape I
  encapsulate1 : Encapsulate1Shape I
  zeroizingArray : ZeroizingArrayRoundTripShape I
  arrayZeroize : ArrayZeroizeShape I
  rangeFullIndex : RangeFullIndexShape I

structure BraidSendDefined : Prop where
  encoderClone : Tacenta.SessionUnitBraidT1.EncoderCloneTotal
  decoderClone : Tacenta.SessionUnitBraidT1.DecoderCloneTotal
  encoderNew : Tacenta.SessionUnitBraidT1.EncoderNewTotal
  encoderNext : Tacenta.SessionUnitBraidT1.EncoderNextChunkTotal

structure TripleSendAxiom (I : Interp) : Prop where
  hmac : HmacShape I
  hkdf : HkdfShape I
  zeroize : SpqrZeroizeShape I
  vecRetain : VecRetainAxiomShape I
  optionClone : OptionCloneShape I

structure TripleSendDefined : Prop where
  vecRetain : VecRetainLoops
  kdfRk : Tacenta.SessionUnitSpqrT1.KdfRkTotal
  kdfCk : Tacenta.SessionUnitSpqrT1.KdfCkTotal

structure EncryptAxiom (I : Interp) {R : Type} (rc : rand_core_1.RngCore R) : Prop where
  braid : BraidSendAxiom I rc
  triple : TripleSendAxiom I
  aeadSeal : AeadSealBoundedShape I
  messageKeyMaterial : MessageKeyMaterialRoundTripShape I
  dhCodec : DhCodecShape I

structure EncryptDefined : Prop where
  braid : BraidSendDefined
  triple : TripleSendDefined

structure BraidReceiveAxiom (I : Interp) : Prop where
  ct1Len : Ct1LenShape I
  ct2Len : Ct2LenShape I
  headerLen : HeaderLenShape I
  ekVectorLen : EkVectorLenShape I
  keyPairEkVector : KeyPairEkVectorShape I
  keyPairDecapsulate : KeyPairDecapsulateShape I
  hkdf : HkdfShape I
  hmac : HmacShape I
  validateEk : ValidateEkShape I
  encapsulate2 : Encapsulate2Shape I
  keyPairClone : KeyPairCloneShape I
  encapsStateClone : EncapsStateCloneShape I
  optionClone : OptionCloneShape I
  zeroizingArray : ZeroizingArrayRoundTripShape I
  arrayZeroize : ArrayZeroizeShape I
  rangeFullIndex : RangeFullIndexShape I

structure BraidReceiveDefined : Prop where
  decoderNew : Tacenta.SessionUnitBraidT1.DecoderNewTotal
  decoderAdd : Tacenta.SessionUnitBraidT1.DecoderAddChunkTotal
  decoderMessage : Tacenta.SessionUnitBraidT1.DecoderMessageTotal
  encoderNew : Tacenta.SessionUnitBraidT1.EncoderNewTotal
  encoderClone : Tacenta.SessionUnitBraidT1.EncoderCloneTotal
  decoderClone : Tacenta.SessionUnitBraidT1.DecoderCloneTotal

structure TripleReceiveAxiom (I : Interp) : Prop where
  hmac : HmacShape I
  hkdf : HkdfShape I
  zeroizing : ZeroizingTotalShape I
  spqrZeroize : SpqrZeroizeShape I
  vecRetain : VecRetainAxiomShape I
  optionClone : OptionCloneShape I
  /-- Defined as `True`; it mentions no constant. -/
  vecAppend : Tacenta.SessionUnitSpqrT1.VecAppendTotal

structure TripleReceiveDefined : Prop where
  vecRetain : VecRetainLoops
  kdfRk : Tacenta.SessionUnitSpqrT1.KdfRkTotal
  kdfCk : Tacenta.SessionUnitSpqrT1.KdfCkTotal
  ratchetRemove : Tacenta.SessionUnitT1.RemoveSkippedAtTotal
  spqrRemove : Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal

structure DecryptAxiom (I : Interp) {R : Type} (rc : rand_core_1.RngCore R) : Prop where
  dhCodec : DhCodecShape I
  dhAgree : DhAgreeShape I
  aeadOpen : AeadOpenShape I
  random32 : Random32Total rc
  braid : BraidReceiveAxiom I
  triple : TripleReceiveAxiom I
  messageKeyMaterial : MessageKeyMaterialRoundTripShape I

structure DecryptDefined : Prop where
  braid : BraidReceiveDefined
  triple : TripleReceiveDefined

structure InitiatorAxiom (I : Interp) {R : Type} (rc : rand_core_1.RngCore R) : Type where
  dhCodec : DhCodecShape I
  dhIdentity : DhIdentityShape I
  dhAgree : DhAgreeShape I
  kemEncapsulate : KemEncapsulateShape I
  xeddsaVerify : XeddsaVerifyShape I
  rngTotal : RngTotal rc
  random32 : Random32Total rc
  sessionHkdf : HkdfShape I
  sessionZeroizing : ZeroizingModelShape I SessionZ
  tripleZeroizing : ZeroizingTotalShape I
  spqrZeroize : SpqrZeroizeShape I
  braidHkdf : HkdfShape I
  zeroizingArray : ZeroizingArrayRoundTripShape I
  rangeFullIndex : RangeFullIndexShape I

structure InitiatorDefined : Prop where
  spqrKdfInit : Tacenta.SessionUnitTripleT1.KdfInitTotal

structure ResponderAxiom (I : Interp) {R : Type} (rc : rand_core_1.RngCore R) where
  decrypt : DecryptAxiom I rc
  dhIdentity : DhIdentityShape I
  kemDecapsulate : KemDecapsulateShape I
  sessionHkdf : HkdfShape I
  sessionZeroizing : ZeroizingModelShape I SessionZ
  vecPop : VecPopShape I
  divCeilValue : DivCeilValueShape I

structure ResponderDefined : Prop where
  decrypt : DecryptDefined
  spqrKdfInit : Tacenta.SessionUnitTripleT1.KdfInitTotal

/-! ### Repacking

`toParts` reads every field of the real record; `ofParts` builds the real record
from the two halves at `Interp.real`.  The bridge lemmas above are what lets each
field be passed unchanged. -/

theorem braidSendToParts {R : Type} {rc : rand_core_1.RngCore R} (c : BraidSendContracts rc) :
    BraidSendAxiom Interp.real rc ∧ BraidSendDefined :=
  ⟨⟨c.rng, c.keyPairClone, c.encapsStateClone, c.keyPairGenerate, c.keyPairHeader,
      c.hmac, c.hkdf, c.encapsulate1, c.zeroizingArray, c.arrayZeroize,
      c.rangeFullIndex⟩,
    ⟨c.encoderClone, c.decoderClone, c.encoderNew, c.encoderNext⟩⟩

theorem braidSendOfParts {R : Type} {rc : rand_core_1.RngCore R}
    (p : BraidSendAxiom Interp.real rc ∧ BraidSendDefined) : BraidSendContracts rc :=
  { rng := p.1.rng, encoderClone := p.2.encoderClone, decoderClone := p.2.decoderClone,
    keyPairClone := p.1.keyPairClone, encapsStateClone := p.1.encapsStateClone,
    keyPairGenerate := p.1.keyPairGenerate, keyPairHeader := p.1.keyPairHeader,
    hmac := p.1.hmac, encoderNew := p.2.encoderNew, encoderNext := p.2.encoderNext,
    hkdf := p.1.hkdf, encapsulate1 := p.1.encapsulate1, zeroizingArray := p.1.zeroizingArray,
    arrayZeroize := p.1.arrayZeroize, rangeFullIndex := p.1.rangeFullIndex }

theorem tripleSendToParts (c : TripleSendContracts) :
    TripleSendAxiom Interp.real ∧ TripleSendDefined :=
  ⟨⟨c.hmac, c.hkdf, c.zeroize, ((VecRetainTotal_is).1 c.vecRetain).1, c.optionClone⟩,
    ⟨((VecRetainTotal_is).1 c.vecRetain).2, c.kdfRk, c.kdfCk⟩⟩

theorem tripleSendOfParts (p : TripleSendAxiom Interp.real ∧ TripleSendDefined) :
    TripleSendContracts :=
  { hmac := p.1.hmac, hkdf := p.1.hkdf, zeroize := p.1.zeroize,
    vecRetain := (VecRetainTotal_is).2 ⟨p.1.vecRetain, p.2.vecRetain⟩,
    kdfRk := p.2.kdfRk, kdfCk := p.2.kdfCk, optionClone := p.1.optionClone }

theorem encryptToParts {R : Type} {rc : rand_core_1.RngCore R} (c : EncryptContracts rc) :
    EncryptAxiom Interp.real rc ∧ EncryptDefined :=
  ⟨⟨(braidSendToParts c.braid).1, (tripleSendToParts c.triple).1, c.aeadSeal,
      c.messageKeyMaterial, c.dhCodec⟩,
    ⟨(braidSendToParts c.braid).2, (tripleSendToParts c.triple).2⟩⟩

theorem encryptOfParts {R : Type} {rc : rand_core_1.RngCore R}
    (p : EncryptAxiom Interp.real rc ∧ EncryptDefined) : EncryptContracts rc :=
  { braid := braidSendOfParts ⟨p.1.braid, p.2.braid⟩,
    triple := tripleSendOfParts ⟨p.1.triple, p.2.triple⟩, aeadSeal := p.1.aeadSeal,
    messageKeyMaterial := p.1.messageKeyMaterial, dhCodec := p.1.dhCodec }

theorem encrypt_iff_parts {R : Type} (rc : rand_core_1.RngCore R) :
    EncryptContracts rc ↔ EncryptAxiom Interp.real rc ∧ EncryptDefined :=
  ⟨encryptToParts, encryptOfParts⟩

theorem braidReceiveToParts (c : BraidReceiveContracts) :
    BraidReceiveAxiom Interp.real ∧ BraidReceiveDefined :=
  ⟨⟨c.ct1Len, c.ct2Len, c.headerLen, c.ekVectorLen, c.keyPairEkVector,
      c.keyPairDecapsulate, c.hkdf, c.hmac, c.validateEk, c.encapsulate2, c.keyPairClone,
      c.encapsStateClone, c.optionClone, c.zeroizingArray, c.arrayZeroize,
      c.rangeFullIndex⟩,
    ⟨c.decoderNew, c.decoderAdd, c.decoderMessage, c.encoderNew, c.encoderClone,
      c.decoderClone⟩⟩

theorem braidReceiveOfParts (p : BraidReceiveAxiom Interp.real ∧ BraidReceiveDefined) :
    BraidReceiveContracts :=
  { decoderNew := p.2.decoderNew, decoderAdd := p.2.decoderAdd,
    decoderMessage := p.2.decoderMessage, ct1Len := p.1.ct1Len, ct2Len := p.1.ct2Len,
    headerLen := p.1.headerLen, ekVectorLen := p.1.ekVectorLen,
    keyPairEkVector := p.1.keyPairEkVector, encoderNew := p.2.encoderNew,
    keyPairDecapsulate := p.1.keyPairDecapsulate, hkdf := p.1.hkdf, hmac := p.1.hmac,
    validateEk := p.1.validateEk, encapsulate2 := p.1.encapsulate2,
    encoderClone := p.2.encoderClone, decoderClone := p.2.decoderClone,
    keyPairClone := p.1.keyPairClone, encapsStateClone := p.1.encapsStateClone,
    optionClone := p.1.optionClone, zeroizingArray := p.1.zeroizingArray,
    arrayZeroize := p.1.arrayZeroize, rangeFullIndex := p.1.rangeFullIndex }

theorem tripleReceiveToParts (c : TripleReceiveContracts) :
    TripleReceiveAxiom Interp.real ∧ TripleReceiveDefined :=
  ⟨⟨c.hmac, c.hkdf, c.zeroizing, c.spqrZeroize, ((VecRetainTotal_is).1 c.vecRetain).1,
      c.optionClone, c.vecAppend⟩,
    ⟨((VecRetainTotal_is).1 c.vecRetain).2, c.kdfRk, c.kdfCk, c.ratchetRemove,
      c.spqrRemove⟩⟩

theorem tripleReceiveOfParts (p : TripleReceiveAxiom Interp.real ∧ TripleReceiveDefined) :
    TripleReceiveContracts :=
  { hmac := p.1.hmac, hkdf := p.1.hkdf, zeroizing := p.1.zeroizing,
    spqrZeroize := p.1.spqrZeroize,
    vecRetain := (VecRetainTotal_is).2 ⟨p.1.vecRetain, p.2.vecRetain⟩,
    kdfRk := p.2.kdfRk, kdfCk := p.2.kdfCk, optionClone := p.1.optionClone,
    ratchetRemove := p.2.ratchetRemove, spqrRemove := p.2.spqrRemove,
    vecAppend := p.1.vecAppend }

theorem decryptToParts {R : Type} {rc : rand_core_1.RngCore R}
    (c : DecryptRatchetContracts rc) : DecryptAxiom Interp.real rc ∧ DecryptDefined :=
  ⟨⟨c.dhCodec, c.dhAgree, c.aeadOpen, c.random32, (braidReceiveToParts c.braid).1,
      (tripleReceiveToParts c.triple).1, c.messageKeyMaterial⟩,
    ⟨(braidReceiveToParts c.braid).2, (tripleReceiveToParts c.triple).2⟩⟩

theorem decryptOfParts {R : Type} {rc : rand_core_1.RngCore R}
    (p : DecryptAxiom Interp.real rc ∧ DecryptDefined) : DecryptRatchetContracts rc :=
  { dhCodec := p.1.dhCodec, dhAgree := p.1.dhAgree, aeadOpen := p.1.aeadOpen,
    random32 := p.1.random32, braid := braidReceiveOfParts ⟨p.1.braid, p.2.braid⟩,
    triple := tripleReceiveOfParts ⟨p.1.triple, p.2.triple⟩,
    messageKeyMaterial := p.1.messageKeyMaterial }

theorem decrypt_iff_parts {R : Type} (rc : rand_core_1.RngCore R) :
    DecryptRatchetContracts rc ↔ DecryptAxiom Interp.real rc ∧ DecryptDefined :=
  ⟨decryptToParts, decryptOfParts⟩

def initiatorToParts {R : Type} {rc : rand_core_1.RngCore R}
    (c : EstablishInitiatorContracts rc) :
    PProd (InitiatorAxiom Interp.real rc) InitiatorDefined :=
  ⟨⟨c.dhCodec, c.dhIdentity, c.dhAgree, c.kemEncapsulate, c.xeddsaVerify, c.rngTotal,
      c.random32, c.sessionHkdf, ZeroizingModelShape.ofSession c.sessionZeroizing,
      c.tripleZeroizing, c.spqrZeroize, c.braidHkdf, c.zeroizingArray, c.rangeFullIndex⟩,
    ⟨c.spqrKdfInit⟩⟩

def initiatorOfParts {R : Type} {rc : rand_core_1.RngCore R}
    (p : PProd (InitiatorAxiom Interp.real rc) InitiatorDefined) :
    EstablishInitiatorContracts rc :=
  { dhCodec := p.1.dhCodec, dhIdentity := p.1.dhIdentity, dhAgree := p.1.dhAgree,
    kemEncapsulate := p.1.kemEncapsulate, xeddsaVerify := p.1.xeddsaVerify,
    rngTotal := p.1.rngTotal, random32 := p.1.random32, sessionHkdf := p.1.sessionHkdf,
    sessionZeroizing := p.1.sessionZeroizing.toSession, tripleZeroizing := p.1.tripleZeroizing,
    spqrKdfInit := p.2.spqrKdfInit, spqrZeroize := p.1.spqrZeroize,
    braidHkdf := p.1.braidHkdf, zeroizingArray := p.1.zeroizingArray,
    rangeFullIndex := p.1.rangeFullIndex }

theorem initiator_toParts_ofParts {R : Type} {rc : rand_core_1.RngCore R}
    (c : EstablishInitiatorContracts rc) : initiatorOfParts (initiatorToParts c) = c := rfl

theorem initiator_ofParts_toParts {R : Type} {rc : rand_core_1.RngCore R}
    (p : PProd (InitiatorAxiom Interp.real rc) InitiatorDefined) :
    initiatorToParts (initiatorOfParts p) = p := rfl

def responderToParts {R : Type} {rc : rand_core_1.RngCore R}
    (c : EstablishResponderContracts rc) :
    PProd (ResponderAxiom Interp.real rc) ResponderDefined :=
  ⟨⟨(decryptToParts c.decrypt).1, c.dhIdentity, c.kemDecapsulate, c.sessionHkdf,
      ZeroizingModelShape.ofSession c.sessionZeroizing, c.vecPop, c.divCeilValue⟩,
    ⟨(decryptToParts c.decrypt).2, c.spqrKdfInit⟩⟩

def responderOfParts {R : Type} {rc : rand_core_1.RngCore R}
    (p : PProd (ResponderAxiom Interp.real rc) ResponderDefined) :
    EstablishResponderContracts rc :=
  { decrypt := decryptOfParts ⟨p.1.decrypt, p.2.decrypt⟩, dhIdentity := p.1.dhIdentity,
    kemDecapsulate := p.1.kemDecapsulate, sessionHkdf := p.1.sessionHkdf,
    sessionZeroizing := p.1.sessionZeroizing.toSession, spqrKdfInit := p.2.spqrKdfInit,
    vecPop := p.1.vecPop, divCeilValue := p.1.divCeilValue }

theorem responder_toParts_ofParts {R : Type} {rc : rand_core_1.RngCore R}
    (c : EstablishResponderContracts rc) : responderOfParts (responderToParts c) = c := rfl

end Parts


/-! ## The joint model

One interpretation for everything.  Most functions are the constant `ok` of a
default over `Unit` types.  Some functions are faithful, because the contracts
force it or because the defined-function fields will need it:

* `Zeroizing` is the identity wrapper, with `new`, `deref`, `deref_mut` the
  identities.  The round trips, `ZeroizingTotal`, and both model classes
  (`contents` the identity) then hold at every instantiation at once.
* `Option::clone` clones the inner value.
* `RangeFull::index` returns its slice.
* `Vec::pop`, `Vec::truncate`, `usize::div_ceil`, `Option::as_mut` and
  `Vec::capacity` are the real operations (pop of the last element, prefix,
  ceiling division that fails on zero, identity borrow, length), so the extra
  laws in `StdLaws` hold as well.
* every size-capped output is empty or zero, and the functions that can refuse
  (`decrypt`, `encapsulate`, `verify`, `decapsulate`, key-pair generation) return
  their success branch, so the caps on success outputs are not satisfied
  vacuously. -/

def zeros32 : Array U8 32#usize := Array.repeat 32#usize 0#u8

def popImpl {T : Type} (v : alloc.vec.Vec T) : Result (Option T × alloc.vec.Vec T) :=
  if h : v.val = [] then ok (none, v)
  else ok (some (v.val.getLast h),
    ⟨v.val.dropLast, by have := v.property; simp only [List.length_dropLast]; omega⟩)

def truncateImpl {T : Type} (v : alloc.vec.Vec T) (n : Usize) :
    Result (alloc.vec.Vec T) :=
  ok ⟨v.val.take n.val, by have := v.property; simp only [List.length_take]; omega⟩

def divCeilImpl (a b : Usize) : Result Usize :=
  if h : b.val = 0 then fail Error.divisionByZero
  else ok (Usize.ofNatCore ((a.val + b.val - 1) / b.val) (by
    have ha : a.val < 2 ^ UScalarTy.Usize.numBits := a.hBounds
    have hb : 0 < b.val := Nat.pos_of_ne_zero h
    have : (a.val + b.val - 1) / b.val < a.val + 1 := by
      rw [Nat.div_lt_iff_lt_mul hb]
      have h1 : a.val ≤ a.val * b.val := Nat.le_mul_of_pos_right _ hb
      have h2 : (a.val + 1) * b.val = a.val * b.val + b.val := by ring
      omega
    omega))

theorem divCeilImpl_value (a b : Usize) (hb : b.val ≠ 0) :
    ∃ q, divCeilImpl a b = ok q ∧ q.val = (a.val + b.val - 1) / b.val := by
  refine ⟨Usize.ofNatCore ((a.val + b.val - 1) / b.val) ?_, ?_, ?_⟩
  · have ha : a.val < 2 ^ UScalarTy.Usize.numBits := a.hBounds
    have hb' : 0 < b.val := Nat.pos_of_ne_zero hb
    have : (a.val + b.val - 1) / b.val < a.val + 1 := by
      rw [Nat.div_lt_iff_lt_mul hb']
      have h1 : a.val ≤ a.val * b.val := Nat.le_mul_of_pos_right _ hb'
      have h2 : (a.val + 1) * b.val = a.val * b.val + b.val := by ring
      omega
    omega
  · simp only [divCeilImpl, dif_neg hb]
  · simp

def optionCloneImpl {T : Type} (inst : core.clone.Clone T) :
    Option T → Result (Option T)
  | none => ok none
  | some x => do
    let y ← inst.clone x
    ok (some y)

def Interp.model : Interp where
  PrivateKey := Unit
  PublicKeyBytes := Unit
  KemKeyPair := Unit
  IncrementalKeyPair := Unit
  EncapsState := Unit
  Zeroizing := fun Z => Z
  dhPrivFromBytes _ := ok ()
  dhPrivPublicKey _ := ok ()
  dhPrivAgree _ _ := ok (some zeros32)
  dhPrivToBytes _ := ok zeros32
  dhPubFromBytes _ := ok ()
  dhPubAsBytes _ := ok zeros32
  dhPubEq _ _ := ok true
  dhIsPrimeOrderPublic _ := ok true
  aeadEncrypt _ _ _ _ _ := ok (alloc.vec.Vec.new U8)
  aeadDecrypt _ _ _ _ _ := ok (core.result.Result.Ok (alloc.vec.Vec.new U8))
  kemEncapsulate _ _ _ r := ok (core.result.Result.Ok (alloc.vec.Vec.new U8, zeros32), r)
  kemDecapsulate _ _ := ok (core.result.Result.Ok zeros32)
  xeddsaVerify _ _ _ := ok (core.result.Result.Ok ())
  hkdfSha256 N _ _ _ := ok (Array.repeat N 0#u8)
  hmacSha256 _ _ := ok zeros32
  HEADER_LEN := ok 0#usize
  EK_VECTOR_LEN := ok 0#usize
  CT1_LEN := ok 0#usize
  CT2_LEN := ok 0#usize
  ikpClone _ := ok ()
  ikpGenerate _ _ r := ok (core.result.Result.Ok (), r)
  ikpHeader _ := ok (alloc.vec.Vec.new U8)
  ikpEkVector _ := ok (alloc.vec.Vec.new U8)
  ikpDecapsulate _ _ _ := ok (core.result.Result.Ok zeros32)
  esClone _ := ok ()
  encapsulate1 _ _ _ r := ok (core.result.Result.Ok ((), alloc.vec.Vec.new U8, zeros32), r)
  encapsulate2 _ _ := ok (core.result.Result.Ok (alloc.vec.Vec.new U8))
  validateEk _ _ := ok true
  blanketZeroize _ x := ok x
  arrayZeroize _ a := ok a
  tupleZeroize _ _ _ x := ok x
  vecZeroize _ v := ok v
  zNew _ z := ok z
  zDeref _ z := ok z
  zDerefMut _ z := ok (z, fun v => v)
  vecPop _ v := popImpl v
  vecCapacity _ v := ok (alloc.vec.Vec.len v)
  vecTruncate _ v n := truncateImpl v n
  optionClone inst o := optionCloneImpl inst o
  optionAsMut o := ok (o, fun x => x)
  rangeFullIndex _ s := ok s
  divCeil a b := divCeilImpl a b

/-! ### Every axiom-level shape holds in the model -/

theorem model_DhCodec : DhCodecShape Interp.model :=
  ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩,
    fun _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩⟩

theorem model_DhIdentity : DhIdentityShape Interp.model := fun _ => ⟨_, rfl⟩
theorem model_DhAgree : DhAgreeShape Interp.model := fun _ _ => ⟨_, rfl⟩
theorem model_KemEncapsulate : KemEncapsulateShape Interp.model :=
  fun _ _ _ _ _ => ⟨_, rfl⟩
theorem model_KemDecapsulate : KemDecapsulateShape Interp.model := fun _ _ => ⟨_, rfl⟩
theorem model_XeddsaVerify : XeddsaVerifyShape Interp.model := fun _ _ _ => ⟨_, rfl⟩
theorem model_AeadOpen : AeadOpenShape Interp.model := fun _ _ _ _ _ => ⟨_, rfl⟩

theorem model_AeadSealBounded : AeadSealBoundedShape Interp.model := by
  intro ek mk iv plaintext ad
  refine ⟨alloc.vec.Vec.new U8, rfl, ?_⟩
  simp

theorem model_MessageKeyMaterialRoundTrip :
    MessageKeyMaterialRoundTripShape Interp.model := fun t => ⟨t, rfl, rfl⟩

theorem popImpl_ok {T : Type} (v : alloc.vec.Vec T) : ∃ r, popImpl v = ok r := by
  unfold popImpl
  split <;> exact ⟨_, rfl⟩

theorem model_VecPop : VecPopShape Interp.model := fun _ v => popImpl_ok v

theorem model_Hkdf : HkdfShape Interp.model := fun _ _ _ _ _ => ⟨_, rfl⟩
theorem model_Hmac : HmacShape Interp.model := fun _ _ => ⟨_, rfl⟩

theorem model_ZeroizingTotal : ZeroizingTotalShape Interp.model :=
  fun _ => ⟨fun z => ⟨z, rfl⟩, fun z => ⟨z, rfl⟩⟩

theorem model_SpqrZeroize : SpqrZeroizeShape Interp.model := fun _ _ => ⟨_, rfl⟩

theorem model_VecRetainAxiom : VecRetainAxiomShape Interp.model :=
  ⟨fun _ _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩⟩

theorem model_OptionClone : OptionCloneShape Interp.model := by
  intro T inst o h
  cases o with
  | none => simp [Interp.model, optionCloneImpl]
  | some x =>
    obtain ⟨y, hy, hyx⟩ := Std.WP.spec_imp_exists (h x rfl)
    simp [Interp.model, optionCloneImpl, hy, hyx]

theorem model_Ct1Len : Ct1LenShape Interp.model := ⟨0#usize, rfl, by simp⟩
theorem model_Ct2Len : Ct2LenShape Interp.model := ⟨0#usize, rfl, by simp⟩
theorem model_HeaderLen : HeaderLenShape Interp.model := ⟨0#usize, rfl, by simp⟩
theorem model_EkVectorLen : EkVectorLenShape Interp.model := ⟨0#usize, rfl, by simp⟩

theorem model_KeyPairEkVector : KeyPairEkVectorShape Interp.model :=
  fun _ => ⟨alloc.vec.Vec.new U8, rfl, by simp⟩

theorem model_KeyPairHeader : KeyPairHeaderShape Interp.model :=
  fun _ => ⟨alloc.vec.Vec.new U8, rfl, by simp⟩

theorem model_KeyPairDecapsulate : KeyPairDecapsulateShape Interp.model :=
  fun _ _ _ => ⟨_, rfl⟩
theorem model_KeyPairClone : KeyPairCloneShape Interp.model := fun _ => ⟨_, rfl⟩
theorem model_EncapsStateClone : EncapsStateCloneShape Interp.model := fun _ => ⟨_, rfl⟩
theorem model_ValidateEk : ValidateEkShape Interp.model := fun _ _ => ⟨_, rfl⟩
theorem model_KeyPairGenerate : KeyPairGenerateShape Interp.model :=
  fun _ _ _ _ => ⟨_, rfl⟩

theorem model_Encapsulate1 : Encapsulate1Shape Interp.model := by
  intro R rc crc s rng _
  refine ⟨_, rfl, ?_⟩
  intro es ct1 raw h
  cases h
  simp

theorem model_Encapsulate2 : Encapsulate2Shape Interp.model := by
  intro es s
  refine ⟨_, rfl, ?_⟩
  intro c h
  cases h
  simp

theorem model_ZeroizingArrayRoundTrip : ZeroizingArrayRoundTripShape Interp.model :=
  fun _ _ a => ⟨a, rfl, rfl⟩

theorem model_ArrayZeroize : ArrayZeroizeShape Interp.model := fun _ _ _ => ⟨_, rfl⟩
theorem model_RangeFullIndex : RangeFullIndexShape Interp.model := fun _ => rfl

theorem model_DivCeilValue : DivCeilValueShape Interp.model := by
  intro a
  obtain ⟨q, hq, hv⟩ := divCeilImpl_value a 32#usize (by simp)
  exact ⟨q, hq, by rw [hv]; simp⟩

/-- The class equations, at any wrapped type: `contents` is the identity. -/
def model_ZeroizingModel (Z : Type) : ZeroizingModelShape Interp.model Z where
  contents z := z
  new _ _ := by simp [Interp.model]
  deref _ _ := by simp [Interp.model]
  deref_mut _ _ := by simp [Interp.model]


/-! ## The laws about standard-library and `zeroize` operations

The defined-function fields of the records reach a few operations that Aeneas leaves opaque, and
their proofs need more of those operations than that they return.  `StdLaws` lists exactly what
the proofs use, in the weakest form each takes:

* `pop`: `Vec::pop` of a non-empty vector returns the vector without its last element.  The
  sparse and classical removal helpers take their length from it, and the three retain loops
  terminate only because it shortens.
* `asMut`: `Option::as_mut` returns (through `Chains::zeroize`).
* `blanketU32`: the blanket `Zeroize` implementation returns at `u32` (through the classical
  `SkippedKey::zeroize`).
* `truncate`: `Vec::truncate` returns at `Vec<u8>` (`Decoder::message`'s last step).
* `divCeil`: the value of `usize::div_ceil` at divisor 32 (`Decoder::new`, `Encoder::new`).

The first three are stated by no record, and neither is `truncate`.  `divCeil` is the field
`divCeilValue` of `EstablishResponderContracts`; the other three records do not state it, and
the two constructor fields `decoderNew` and `encoderNew` are each equivalent to the weaker
statement that `div_ceil` returns at divisor 32.

`StdLaws` is what is assumed.  `FaithfulShape` is what the model does: `pop` returns the last
element, `truncate` is a prefix, `div_ceil` is ceiling division, `as_mut` borrows without change,
`capacity` is at least the length.  The model is therefore the real operation on these
functions and not a degenerate function that happens to have the weak property, and
`stdLaws_of_faithful` is the step from the one to the other. -/

structure StdLaws (I : Interp) : Prop where
  pop : ∀ (T : Type) (v : alloc.vec.Vec T), v.val ≠ [] →
    ∃ o w, I.vecPop Global v = ok (o, w) ∧ w.val = v.val.dropLast
  asMut : ∀ (T : Type) (o : Option T), ∃ r, I.optionAsMut o = ok r
  blanketU32 : ∀ x : U32,
    ∃ r, I.blanketZeroize U32.Insts.ZeroizeDefaultIsZeroes x = ok r
  truncate : ∀ (v : alloc.vec.Vec U8) (n : Usize), ∃ r, I.vecTruncate Global v n = ok r
  divCeil : DivCeilValueShape I

structure FaithfulShape (I : Interp) : Prop where
  pop_nil : ∀ {T : Type} (v : alloc.vec.Vec T), v.val = [] →
    I.vecPop Global v = ok (none, v)
  pop_snoc : ∀ {T : Type} (v : alloc.vec.Vec T) (l : List T) (x : T),
    v.val = l ++ [x] → ∃ v', I.vecPop Global v = ok (some x, v') ∧ v'.val = l
  truncate : ∀ {T : Type} (v : alloc.vec.Vec T) (n : Usize),
    ∃ v', I.vecTruncate Global v n = ok v' ∧ v'.val = v.val.take n.val
  divCeil : ∀ a b : Usize, b.val ≠ 0 →
    ∃ q, I.divCeil a b = ok q ∧ q.val = (a.val + b.val - 1) / b.val
  asMut : ∀ {T : Type} (o : Option T), I.optionAsMut o = ok (o, fun x => x)
  capacity : ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T),
    ∃ c, I.vecCapacity A v = ok c ∧ v.length ≤ c.val

/-- The faithful behaviour of the five operations, plus that the blanket `Zeroize` returns at
`u32`, gives the laws the proofs use. -/
theorem stdLaws_of_faithful (I : Interp) (f : FaithfulShape I)
    (b : ∀ x : U32, ∃ r, I.blanketZeroize U32.Insts.ZeroizeDefaultIsZeroes x = ok r) :
    StdLaws I where
  pop := by
    intro T v hv
    have hsnoc : v.val = v.val.dropLast ++ [v.val.getLast hv] :=
      (List.dropLast_append_getLast hv).symm
    obtain ⟨v', hp, hv'⟩ := f.pop_snoc v v.val.dropLast (v.val.getLast hv) hsnoc
    exact ⟨_, v', hp, hv'⟩
  asMut := fun _ o => ⟨_, f.asMut o⟩
  blanketU32 := b
  truncate := fun v n => by
    obtain ⟨q, hq, -⟩ := f.truncate v n
    exact ⟨q, hq⟩
  divCeil := fun a => by
    obtain ⟨q, hq, hv⟩ := f.divCeil a 32#usize (by simp)
    exact ⟨q, hq, by rw [hv]; simp⟩

theorem model_Faithful : FaithfulShape Interp.model where
  pop_nil := by
    intro T v hv
    simp [Interp.model, popImpl, hv]
  pop_snoc := by
    intro T v l x hv
    obtain ⟨vl, hvl⟩ := v
    simp only at hv
    subst hv
    refine ⟨⟨l, by simp at hvl; omega⟩, ?_, rfl⟩
    simp [Interp.model, popImpl]
  truncate := fun v n => ⟨_, rfl, rfl⟩
  divCeil := by
    intro a b hb
    exact divCeilImpl_value a b hb
  asMut := fun o => rfl
  capacity := by
    intro T A v
    exact ⟨_, rfl, by simp⟩

/-- The model's `Vec::pop` of an empty vector returns `none` and the vector.  Held by statement, so
weakening the `pop_nil` clause of `FaithfulShape` is refused. -/
theorem model_pop_empty {T : Type} (v : alloc.vec.Vec T) (h : v.val = []) :
    Interp.model.vecPop Global v = ok (none, v) := model_Faithful.pop_nil v h

/-- The model's `Vec::capacity` is at least the length. -/
theorem model_capacity_ge {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    ∃ c, Interp.model.vecCapacity A v = ok c ∧ v.length ≤ c.val := model_Faithful.capacity A v

/-- The model's `Vec::truncate` is a prefix. -/
theorem model_truncate_is_take {T : Type} (v : alloc.vec.Vec T) (n : Usize) :
    ∃ v', Interp.model.vecTruncate Global v n = ok v' ∧ v'.val = v.val.take n.val :=
  model_Faithful.truncate v n

theorem model_BlanketU32 :
    ∀ x : U32, ∃ r, Interp.model.blanketZeroize U32.Insts.ZeroizeDefaultIsZeroes x = ok r :=
  fun x => ⟨x, rfl⟩

theorem model_StdLaws : StdLaws Interp.model :=
  stdLaws_of_faithful Interp.model model_Faithful model_BlanketU32

/-! ## Assembly: the four records at the joint model -/

section Assembly

open Tacenta.UnitLifecycleT1

def totalRngCore : rand_core_1.RngCore Unit where
  next_u32 _ := ok (0#u32, ())
  next_u64 _ := ok (0#u64, ())
  fill_bytes _ bytes := ok ((), bytes)
  try_fill_bytes _ bytes := ok (core.result.Result.Ok (), (), bytes)

theorem totalRngCore_total : RngTotal totalRngCore := fun _ _ => ⟨_, rfl⟩

theorem braidRngTotal_iff {R : Type} (rc : rand_core_1.RngCore R) :
    Tacenta.SessionUnitBraidT1.RngTotal rc ↔ RngTotal rc := Iff.rfl

theorem random32_of_rngTotal {R : Type} {rc : rand_core_1.RngCore R} (h : RngTotal rc) :
    Random32Total rc := fun rng bytes _ => h rng bytes

theorem model_braidSendAxiom {R : Type} {rc : rand_core_1.RngCore R}
    (h : Tacenta.SessionUnitBraidT1.RngTotal rc) : BraidSendAxiom Interp.model rc :=
  ⟨h, model_KeyPairClone, model_EncapsStateClone, model_KeyPairGenerate,
    model_KeyPairHeader, model_Hmac, model_Hkdf, model_Encapsulate1,
    model_ZeroizingArrayRoundTrip, model_ArrayZeroize, model_RangeFullIndex⟩

theorem model_tripleSendAxiom : TripleSendAxiom Interp.model :=
  ⟨model_Hmac, model_Hkdf, model_SpqrZeroize, model_VecRetainAxiom, model_OptionClone⟩

theorem model_encryptAxiom {R : Type} {rc : rand_core_1.RngCore R}
    (h : Tacenta.SessionUnitBraidT1.RngTotal rc) : EncryptAxiom Interp.model rc :=
  ⟨model_braidSendAxiom h, model_tripleSendAxiom, model_AeadSealBounded,
    model_MessageKeyMaterialRoundTrip, model_DhCodec⟩

theorem model_braidReceiveAxiom : BraidReceiveAxiom Interp.model :=
  ⟨model_Ct1Len, model_Ct2Len, model_HeaderLen, model_EkVectorLen,
    model_KeyPairEkVector, model_KeyPairDecapsulate, model_Hkdf, model_Hmac,
    model_ValidateEk, model_Encapsulate2, model_KeyPairClone, model_EncapsStateClone,
    model_OptionClone, model_ZeroizingArrayRoundTrip, model_ArrayZeroize,
    model_RangeFullIndex⟩

theorem model_tripleReceiveAxiom : TripleReceiveAxiom Interp.model :=
  ⟨model_Hmac, model_Hkdf, model_ZeroizingTotal, model_SpqrZeroize,
    model_VecRetainAxiom, model_OptionClone, trivial⟩

theorem model_decryptAxiom {R : Type} {rc : rand_core_1.RngCore R}
    (h : Random32Total rc) : DecryptAxiom Interp.model rc :=
  ⟨model_DhCodec, model_DhAgree, model_AeadOpen, h, model_braidReceiveAxiom,
    model_tripleReceiveAxiom, model_MessageKeyMaterialRoundTrip⟩

def model_initiatorAxiom {R : Type} {rc : rand_core_1.RngCore R}
    (h : RngTotal rc) (h32 : Random32Total rc) : InitiatorAxiom Interp.model rc :=
  ⟨model_DhCodec, model_DhIdentity, model_DhAgree, model_KemEncapsulate,
    model_XeddsaVerify, h, h32, model_Hkdf, model_ZeroizingModel SessionZ,
    model_ZeroizingTotal, model_SpqrZeroize, model_Hkdf,
    model_ZeroizingArrayRoundTrip, model_RangeFullIndex⟩

def model_responderAxiom {R : Type} {rc : rand_core_1.RngCore R}
    (h32 : Random32Total rc) : ResponderAxiom Interp.model rc :=
  ⟨model_decryptAxiom h32, model_DhIdentity, model_KemDecapsulate, model_Hkdf,
    model_ZeroizingModel SessionZ, model_VecPop, model_DivCeilValue⟩

/-- Intentionally repetitive: the module depends on every witness, so removing
one of them makes the build fail. -/
theorem model_satisfies_all_axiom_shapes :
    DhCodecShape Interp.model ∧ DhIdentityShape Interp.model ∧
    DhAgreeShape Interp.model ∧ KemEncapsulateShape Interp.model ∧
    KemDecapsulateShape Interp.model ∧ XeddsaVerifyShape Interp.model ∧
    AeadOpenShape Interp.model ∧ AeadSealBoundedShape Interp.model ∧
    MessageKeyMaterialRoundTripShape Interp.model ∧ VecPopShape Interp.model ∧
    HkdfShape Interp.model ∧ HmacShape Interp.model ∧
    ZeroizingTotalShape Interp.model ∧ SpqrZeroizeShape Interp.model ∧
    VecRetainAxiomShape Interp.model ∧ OptionCloneShape Interp.model ∧
    Ct1LenShape Interp.model ∧ Ct2LenShape Interp.model ∧
    HeaderLenShape Interp.model ∧ EkVectorLenShape Interp.model ∧
    KeyPairEkVectorShape Interp.model ∧ KeyPairHeaderShape Interp.model ∧
    KeyPairDecapsulateShape Interp.model ∧ KeyPairCloneShape Interp.model ∧
    EncapsStateCloneShape Interp.model ∧ ValidateEkShape Interp.model ∧
    KeyPairGenerateShape Interp.model ∧ Encapsulate1Shape Interp.model ∧
    Encapsulate2Shape Interp.model ∧ ZeroizingArrayRoundTripShape Interp.model ∧
    ArrayZeroizeShape Interp.model ∧ RangeFullIndexShape Interp.model ∧
    Nonempty (ZeroizingModelShape Interp.model SessionZ) ∧
    Nonempty (ZeroizingModelShape Interp.model DerivedZ) ∧
    DivCeilValueShape Interp.model ∧ FaithfulShape Interp.model ∧ StdLaws Interp.model :=
  ⟨model_DhCodec, model_DhIdentity, model_DhAgree, model_KemEncapsulate,
    model_KemDecapsulate, model_XeddsaVerify, model_AeadOpen, model_AeadSealBounded,
    model_MessageKeyMaterialRoundTrip, model_VecPop, model_Hkdf, model_Hmac,
    model_ZeroizingTotal, model_SpqrZeroize, model_VecRetainAxiom, model_OptionClone,
    model_Ct1Len, model_Ct2Len, model_HeaderLen, model_EkVectorLen,
    model_KeyPairEkVector, model_KeyPairHeader, model_KeyPairDecapsulate,
    model_KeyPairClone, model_EncapsStateClone, model_ValidateEk, model_KeyPairGenerate,
    model_Encapsulate1, model_Encapsulate2, model_ZeroizingArrayRoundTrip,
    model_ArrayZeroize, model_RangeFullIndex, ⟨model_ZeroizingModel SessionZ⟩,
    ⟨model_ZeroizingModel DerivedZ⟩, model_DivCeilValue, model_Faithful, model_StdLaws⟩

/-! ## Headline theorems -/

/-- Per record, at the minimal hypotheses on the supplied `RngCore`. -/
theorem encrypt_axiom_part_satisfiable :
    ∃ I : Interp, ∀ {R : Type} (rc : rand_core_1.RngCore R),
      Tacenta.SessionUnitBraidT1.RngTotal rc → EncryptAxiom I rc :=
  ⟨Interp.model, fun _ h => model_encryptAxiom h⟩

theorem decrypt_axiom_part_satisfiable :
    ∃ I : Interp, ∀ {R : Type} (rc : rand_core_1.RngCore R),
      Random32Total rc → DecryptAxiom I rc :=
  ⟨Interp.model, fun _ h => model_decryptAxiom h⟩

theorem initiator_axiom_part_satisfiable :
    ∃ I : Interp, ∀ {R : Type} (rc : rand_core_1.RngCore R),
      RngTotal rc → Random32Total rc → Nonempty (InitiatorAxiom I rc) :=
  ⟨Interp.model, fun _ h h32 => ⟨model_initiatorAxiom h h32⟩⟩

theorem responder_axiom_part_satisfiable :
    ∃ I : Interp, Nonempty (ZeroizingModelShape I DerivedZ) ∧
      ∀ {R : Type} (rc : rand_core_1.RngCore R),
        Random32Total rc → Nonempty (ResponderAxiom I rc) :=
  ⟨Interp.model, ⟨model_ZeroizingModel DerivedZ⟩, fun _ h32 => ⟨model_responderAxiom h32⟩⟩

end Assembly



/-! ## An illustration: a defined-function field as a shape

A defined-function field attaches to the model in two ways.

1. *In the real environment.*  Prove the field from `StdLaws` at `Interp.real` with a theorem about
   the translated body, as `UnitSatisfiabilityErasure.decoderNew_of_divCeilValue` does.  The proof
   mentions the real constants only through its hypothesis, so, by substitution, it holds at any
   interpretation that satisfies the hypothesis, the joint model included.  This is the route the
   records use.  It is sound, but the last step is a statement about proofs and not a theorem inside
   Lean.
2. *Generically.*  Copy the translated body with the axioms replaced by the fields of `I`, bind the
   copy to the real function by `Iff.rfl` (so the kernel checks that the copy is the real body),
   and prove the copy for every `I` that satisfies the laws.  The field is then a shape like any
   other and is covered by the model with no substitution step.  `decoderNewI` does this for
   `Decoder::new`.  It costs a copy of every reached definition, which is why it is done for one
   function and not for the records. -/

/-- `tacenta_erasure::chunk_count` over an interpretation. -/
def chunkCountI (I : Interp) (size : Usize) : Result Usize :=
  I.divCeil size tacenta_erasure.CHUNK_BYTES

/-- `tacenta_erasure::Decoder::new` over an interpretation. -/
def decoderNewI (I : Interp) (size : Usize) : Result tacenta_erasure.Decoder := do
  let i ← chunkCountI I size
  ok { size, needed := i, «have» := (alloc.vec.Vec.new tacenta_erasure.Chunk) }

def DecoderNewShape (I : Interp) : Prop := ∀ n : Usize, Np (decoderNewI I n)

/-- The copy is the real body: this is checked by the kernel. -/
theorem DecoderNewTotal_is :
    Tacenta.SessionUnitBraidT1.DecoderNewTotal ↔ DecoderNewShape Interp.real := Iff.rfl

/-- The generic proof, for every interpretation that satisfies the laws. -/
theorem decoderNewShape_of_stdLaws (I : Interp) (h : StdLaws I) : DecoderNewShape I := by
  intro n
  obtain ⟨q, hq, -⟩ := h.divCeil n
  have hC : tacenta_erasure.CHUNK_BYTES = 32#usize := by simp [global_simps]
  have hq' : I.divCeil n tacenta_erasure.CHUNK_BYTES = ok q := by rw [hC]; exact hq
  refine ⟨{ size := n, needed := q, «have» := alloc.vec.Vec.new tacenta_erasure.Chunk }, ?_⟩
  simp only [decoderNewI, chunkCountI, hq', Aeneas.Std.bind_tc_ok]

theorem model_DecoderNew : DecoderNewShape Interp.model :=
  decoderNewShape_of_stdLaws Interp.model model_StdLaws

/-! ## Negative controls

Three kinds of control, all checked when the module builds.

1. A shape that differs from the predicate by one constant, one premise or one conjunct is
   not accepted when bound with `Iff.rfl`.
2. The fields that force a faithful model have teeth: a model that breaks one
   of them makes the corresponding shape false.
3. The value law that the real `Array::zeroize` satisfies (a failing element makes
   it fail) contradicts `ZeroizeTotal`; see `zeroize_failure_propagation_conflicts`. -/

section NegativeControls

/-- Control 1: the bound `4095` instead of `4096` is not the predicate. -/
def Ct1LenCap4095 : Prop := ∃ v : Usize, Interp.real.CT1_LEN = ok v ∧ v.val ≤ 4095

example : True := by
  fail_if_success
    have : Tacenta.SessionUnitBraidT1.Ct1LenTotal ↔ Ct1LenCap4095 := Iff.rfl
  trivial

/-- Control 1: dropping the premise of `OptionCloneTotal` is not the predicate. -/
def OptionCloneNoPremise : Prop :=
  ∀ {T : Type} (inst : core.clone.Clone T) (o : Option T),
    Interp.real.optionClone inst o ⦃ fun o' => o' = o ⦄

example : True := by
  fail_if_success
    have : Tacenta.SessionUnitSpqrT1.OptionCloneTotal ↔ OptionCloneNoPremise := Iff.rfl
  trivial

/-- Control 1: the round trip without its `deref` conjunct is not the predicate. -/
def ZeroizingArrayRoundTripNewOnly : Prop :=
  ∀ (N : Usize) (inst : zeroize.Zeroize (Array U8 N)) (a : Array U8 N),
    ∃ z, Interp.real.zNew inst a = ok z

example : True := by
  fail_if_success
    have : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip ↔ ZeroizingArrayRoundTripNewOnly := Iff.rfl
  trivial

/-- Control 2: `RangeFull::index` that forgets its argument. -/
def badRange : Interp := { Interp.model with rangeFullIndex := fun _ _ => ok (Slice.new _) }

theorem badRange_refutes : ¬ RangeFullIndexShape badRange := by
  intro h
  have h1 := h (Array.to_slice zeros32)
  have h2 : (ok (Slice.new U8) : Result (Slice U8)) = ok (Array.to_slice zeros32) := h1
  have h3 : (Slice.new U8) = Array.to_slice zeros32 := by injection h2
  have h4 := congrArg (fun s : Slice U8 => s.val.length) h3
  simp [zeros32, Slice.new] at h4

/-- Control 2: `Zeroizing::deref` that fails. -/
def badDeref : Interp := { Interp.model with zDeref := fun _ _ => fail Error.panic }

theorem badDeref_refutes_array : ¬ ZeroizingArrayRoundTripShape badDeref := by
  intro h
  obtain ⟨z, -, hz⟩ := h 32#usize (Array.Insts.ZeroizeZeroize 32#usize
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) zeros32
  cases hz

theorem badDeref_refutes_message_key : ¬ MessageKeyMaterialRoundTripShape badDeref := by
  intro h
  obtain ⟨z, -, hz⟩ := h (zeros32, zeros32, Array.repeat 16#usize 0#u8)
  cases hz

/-- Control 2: `Option::clone` that drops its content. -/
def badOptionClone : Interp := { Interp.model with optionClone := fun _ _ => ok none }

theorem badOptionClone_refutes : ¬ OptionCloneShape badOptionClone := by
  intro h
  have := h core.clone.CloneU8 (some 0#u8) (by
    intro x hx
    cases hx
    simp)
  simp [badOptionClone] at this

/-- Control 2: a header constant above the cap. -/
def badCap : Interp := { Interp.model with HEADER_LEN := ok 5000#usize }

theorem badCap_refutes : ¬ HeaderLenShape badCap := by
  rintro ⟨v, hv, hle⟩
  have hv' : (ok 5000#usize : Result Usize) = ok v := hv
  have : (5000#usize) = v := by injection hv'
  subst this
  simp at hle

/-- Control 2: an AEAD seal that adds more than the forty-eight bytes of framing. -/
def badSeal : Interp := { Interp.model with
  aeadEncrypt := fun _ _ _ _ _ => ok ⟨List.replicate 100 0#u8, by scalar_tac⟩ }

theorem badSeal_refutes : ¬ AeadSealBoundedShape badSeal := by
  intro h
  obtain ⟨r, hr, hlen⟩ := h zeros32 zeros32 (Array.repeat 16#usize 0#u8) (Slice.new U8) (Slice.new U8)
  have hr' : (ok ⟨List.replicate 100 0#u8, by scalar_tac⟩ : Result (alloc.vec.Vec U8)) = ok r := hr
  have : (⟨List.replicate 100 0#u8, by scalar_tac⟩ : alloc.vec.Vec U8) = r := by injection hr'
  rw [← this] at hlen
  simp [Slice.new] at hlen

end NegativeControls


end Tacenta.UnitSatisfiabilityJoint

/-! ## Axiom pins

The axiom bases of the results above, held by the build.  A list names the constants that occur
in the statement of a result, not assumptions its proof makes.  The statements about
`Interp.real` and the records (`all_shapes_are_predicates`, the `*_iff_parts` and `*_toParts_ofParts`
results, `DecoderNewTotal_is`) mention the 48 interpreted real constants and the error type.  The
statements that are about the model (`model_*`, the `*_axiom_part_satisfiable` results, the `bad*`
controls) list the three standard axioms and `rand_core_1.error.Error`, the opaque error type inside
`RngCore`, which occurs in the type of `Interp`; `badDeref_refutes_array` also lists `Array::zeroize`
and the blanket `Zeroize`. -/

/--
info: 'Tacenta.UnitSatisfiabilityJoint.all_shapes_are_predicates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.all_shapes_are_predicates

/--
info: 'Tacenta.UnitSatisfiabilityJoint.model_satisfies_all_axiom_shapes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.model_satisfies_all_axiom_shapes

/--
info: 'Tacenta.UnitSatisfiabilityJoint.stdLaws_of_faithful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.stdLaws_of_faithful

/--
info: 'Tacenta.UnitSatisfiabilityJoint.model_Faithful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.model_Faithful

/--
info: 'Tacenta.UnitSatisfiabilityJoint.model_StdLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.model_StdLaws

/--
info: 'Tacenta.UnitSatisfiabilityJoint.encrypt_iff_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.encrypt_iff_parts

/--
info: 'Tacenta.UnitSatisfiabilityJoint.decrypt_iff_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.decrypt_iff_parts

/--
info: 'Tacenta.UnitSatisfiabilityJoint.initiator_toParts_ofParts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.initiator_toParts_ofParts

/--
info: 'Tacenta.UnitSatisfiabilityJoint.responder_toParts_ofParts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.responder_toParts_ofParts

/--
info: 'Tacenta.UnitSatisfiabilityJoint.encrypt_axiom_part_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.encrypt_axiom_part_satisfiable

/--
info: 'Tacenta.UnitSatisfiabilityJoint.decrypt_axiom_part_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.decrypt_axiom_part_satisfiable

/--
info: 'Tacenta.UnitSatisfiabilityJoint.initiator_axiom_part_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.initiator_axiom_part_satisfiable

/--
info: 'Tacenta.UnitSatisfiabilityJoint.responder_axiom_part_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.responder_axiom_part_satisfiable

/--
info: 'Tacenta.UnitSatisfiabilityJoint.DecoderNewTotal_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.DecoderNewTotal_is

/--
info: 'Tacenta.UnitSatisfiabilityJoint.decoderNewShape_of_stdLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.decoderNewShape_of_stdLaws

/--
info: 'Tacenta.UnitSatisfiabilityJoint.model_DecoderNew' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.model_DecoderNew

/--
info: 'Tacenta.UnitSatisfiabilityJoint.badRange_refutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.badRange_refutes

/--
info: 'Tacenta.UnitSatisfiabilityJoint.badDeref_refutes_array' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.badDeref_refutes_array

/--
info: 'Tacenta.UnitSatisfiabilityJoint.badDeref_refutes_message_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.badDeref_refutes_message_key

/--
info: 'Tacenta.UnitSatisfiabilityJoint.badOptionClone_refutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.badOptionClone_refutes

/--
info: 'Tacenta.UnitSatisfiabilityJoint.badCap_refutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.badCap_refutes

/--
info: 'Tacenta.UnitSatisfiabilityJoint.badSeal_refutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.badSeal_refutes

/--
info: 'Tacenta.UnitSatisfiabilityJoint.model_pop_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.model_pop_empty

/--
info: 'Tacenta.UnitSatisfiabilityJoint.model_capacity_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.model_capacity_ge

/--
info: 'Tacenta.UnitSatisfiabilityJoint.model_truncate_is_take' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityJoint.model_truncate_is_take
