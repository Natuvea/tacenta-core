import Translation.UnitLifecyclePublicT1

/-!
# Non-vacuity of the Session primitive contracts

Each predicate below abstracts the opaque types and functions constrained by a
Session boundary contract.  The corresponding `_is` theorem binds the shape
to the generated constants, while the witness gives one joint interpretation
in which the shape holds.  This establishes consistency only; it does not say
that the generated axiom is implemented by the witness.
-/

namespace Tacenta.UnitSatisfiabilitySession

open Aeneas Aeneas.Std Result
open tacenta_session_unit

abbrev Np {α : Type} (e : Result α) : Prop := ∃ r, e = ok r

abbrev DhPrivateFromBytesFn (D : Type) := Array U8 32#usize → Result D
abbrev DhPublicFn (D P : Type) := D → Result P
abbrev DhPrivateToBytesFn (D : Type) (W : Type → Type) :=
  D → Result (W (Array U8 32#usize))
abbrev DhPublicFromBytesFn (P : Type) := Array U8 32#usize → Result P
abbrev DhPublicAsBytesFn (P : Type) := P → Result (Array U8 32#usize)
abbrev DhEqFn (P : Type) := P → P → Result Bool

def DhCodecShape (D P : Type) (W : Type → Type)
    (privateFromBytes : DhPrivateFromBytesFn D)
    (publicKey : DhPublicFn D P)
    (privateToBytes : DhPrivateToBytesFn D W)
    (publicFromBytes : DhPublicFromBytesFn P)
    (publicAsBytes : DhPublicAsBytesFn P)
    (eq : DhEqFn P) : Prop :=
  (∀ a, Np (privateFromBytes a)) ∧
  (∀ k, Np (publicKey k)) ∧
  (∀ k, Np (privateToBytes k)) ∧
  (∀ a, Np (publicFromBytes a)) ∧
  (∀ k, Np (publicAsBytes k)) ∧
  (∀ a b, Np (eq a b))

theorem DhCodecTotal_is : Tacenta.UnitLifecycleT1.DhCodecTotal ↔
    DhCodecShape tacenta_boundary.dh.PrivateKey tacenta_boundary.dh.PublicKeyBytes
      zeroize.Zeroizing
      tacenta_boundary.dh.PrivateKey.from_bytes
      tacenta_boundary.dh.PrivateKey.public_key
      tacenta_boundary.dh.PrivateKey.to_bytes
      tacenta_boundary.dh.PublicKeyBytes.from_bytes
      tacenta_boundary.dh.PublicKeyBytes.as_bytes
      tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq :=
  Iff.rfl

def zeros32 : Array U8 32#usize := Array.repeat 32#usize 0#u8

theorem dh_codec_satisfiable :
    ∃ (D P : Type) (W : Type → Type)
      (privateFromBytes : DhPrivateFromBytesFn D)
      (publicKey : DhPublicFn D P)
      (privateToBytes : DhPrivateToBytesFn D W)
      (publicFromBytes : DhPublicFromBytesFn P)
      (publicAsBytes : DhPublicAsBytesFn P)
      (eq : DhEqFn P),
      DhCodecShape D P W privateFromBytes publicKey privateToBytes
        publicFromBytes publicAsBytes eq := by
  refine ⟨Unit, Unit, (fun Z => Z), (fun _ => ok ()), (fun _ => ok ()),
    (fun _ => ok zeros32), (fun _ => ok ()), (fun _ => ok zeros32),
    (fun _ _ => ok true), ?_⟩
  simp [DhCodecShape, Np]

abbrev DhAgreeFn (D P : Type) := D → P → Result (Option (Array U8 32#usize))
def DhAgreeShape {D P : Type} (f : DhAgreeFn D P) : Prop :=
  ∀ d p, Np (f d p)

theorem DhAgreeTotal_is : Tacenta.UnitLifecycleT1.DhAgreeTotal ↔
    DhAgreeShape tacenta_boundary.dh.PrivateKey.agree := Iff.rfl

theorem dh_agree_satisfiable : ∃ (D P : Type) (f : DhAgreeFn D P), DhAgreeShape f :=
  ⟨Unit, Unit, fun _ _ => ok none, by simp [DhAgreeShape, Np]⟩

abbrev AeadSealFn := Array U8 32#usize → Array U8 32#usize →
  Array U8 16#usize → Slice U8 → Slice U8 → Result (alloc.vec.Vec U8)
def AeadSealShape (f : AeadSealFn) : Prop := ∀ ek mk n p ad, Np (f ek mk n p ad)

theorem AeadSealTotal_is : Tacenta.UnitLifecycleT1.AeadSealTotal ↔
    AeadSealShape tacenta_boundary.aead.encrypt := Iff.rfl

theorem aead_seal_satisfiable : ∃ f : AeadSealFn, AeadSealShape f :=
  ⟨fun _ _ _ _ _ => ok (alloc.vec.Vec.new U8), by simp [AeadSealShape, Np]⟩

def AeadSealBoundedShape (f : AeadSealFn) : Prop :=
  ∀ ek mk iv plaintext ad, ∃ r,
    f ek mk iv plaintext ad = ok r ∧
    r.val.length ≤ plaintext.val.length + 16

theorem AeadSealBounded_is : Tacenta.UnitLifecycleT1.AeadSealBounded ↔
    AeadSealBoundedShape tacenta_boundary.aead.encrypt := Iff.rfl

theorem aead_seal_bounded_satisfiable :
    ∃ f : AeadSealFn, AeadSealBoundedShape f := by
  refine ⟨fun _ _ _ _ _ => ok (alloc.vec.Vec.new U8), ?_⟩
  simp [AeadSealBoundedShape]

abbrev AeadOpenFn := Array U8 32#usize → Array U8 32#usize →
  Array U8 16#usize → Slice U8 → Slice U8 →
    Result (core.result.Result (alloc.vec.Vec U8) tacenta_boundary.aead.DecryptError)
def AeadOpenShape (f : AeadOpenFn) : Prop := ∀ ek mk n c ad, Np (f ek mk n c ad)

theorem AeadOpenTotal_is : Tacenta.UnitLifecycleT1.AeadOpenTotal ↔
    AeadOpenShape tacenta_boundary.aead.decrypt := Iff.rfl

theorem aead_open_satisfiable : ∃ f : AeadOpenFn, AeadOpenShape f :=
  ⟨fun _ _ _ _ _ => ok (core.result.Result.Err ()), by simp [AeadOpenShape, Np]⟩

abbrev KemEncapsulateFn :=
  {R : Type} → rand_core_1.RngCore R → rand_core_1.CryptoRng R →
    Slice U8 → R → Result ((core.result.Result ((alloc.vec.Vec U8) ×
      Array U8 32#usize) tacenta_boundary.kem.KemError) × R)
def KemEncapsulateShape (f : KemEncapsulateFn) : Prop :=
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (cr : rand_core_1.CryptoRng R) p r,
    Np (f rc cr p r)

theorem KemEncapsulateTotal_is : Tacenta.UnitLifecycleT1.KemEncapsulateTotal ↔
    KemEncapsulateShape @tacenta_boundary.kem.encapsulate := Iff.rfl

theorem kem_encapsulate_satisfiable :
    ∃ f : KemEncapsulateFn, KemEncapsulateShape f :=
  ⟨fun _ _ _ r => ok (core.result.Result.Err (), r),
    by simp [KemEncapsulateShape, Np]⟩

abbrev KemDecapsulateFn (K : Type) := K → Slice U8 →
  Result (core.result.Result (Array U8 32#usize) tacenta_boundary.kem.KemError)
def KemDecapsulateShape {K : Type} (f : KemDecapsulateFn K) : Prop :=
  ∀ k c, Np (f k c)

theorem KemDecapsulateTotal_is : Tacenta.UnitLifecycleT1.KemDecapsulateTotal ↔
    KemDecapsulateShape tacenta_boundary.kem.decapsulate := Iff.rfl

theorem kem_decapsulate_satisfiable :
    ∃ (K : Type) (f : KemDecapsulateFn K), KemDecapsulateShape f :=
  ⟨Unit, fun _ _ => ok (core.result.Result.Err ()), by simp [KemDecapsulateShape, Np]⟩

def KemCiphertextLenShape (e : Result Usize) : Prop := Np e

theorem KemCiphertextLenTotal_is : Tacenta.UnitLifecycleT1.KemCiphertextLenTotal ↔
    KemCiphertextLenShape tacenta_boundary.kem.ciphertext_len := Iff.rfl

theorem kem_ciphertext_len_satisfiable :
    ∃ e : Result Usize, KemCiphertextLenShape e :=
  ⟨ok 0#usize, by simp [KemCiphertextLenShape, Np]⟩

abbrev XeddsaVerifyFn (P : Type) := P → Slice U8 → Array U8 64#usize →
  Result (core.result.Result Unit tacenta_boundary.xeddsa.VerifyError)
def XeddsaVerifyShape {P : Type} (f : XeddsaVerifyFn P) : Prop :=
  ∀ p m s, Np (f p m s)

theorem XeddsaVerifyTotal_is : Tacenta.UnitLifecycleT1.XeddsaVerifyTotal ↔
    XeddsaVerifyShape tacenta_boundary.xeddsa.verify := Iff.rfl

theorem xeddsa_verify_satisfiable :
    ∃ (P : Type) (f : XeddsaVerifyFn P), XeddsaVerifyShape f :=
  ⟨Unit, fun _ _ _ => ok (core.result.Result.Err ()), by simp [XeddsaVerifyShape, Np]⟩

abbrev XeddsaSignFn :=
  {R : Type} → rand_core_1.RngCore R → rand_core_1.CryptoRng R →
    Array U8 32#usize → Slice U8 → R → Result (Array U8 64#usize × R)
def XeddsaSignShape (f : XeddsaSignFn) : Prop :=
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (cr : rand_core_1.CryptoRng R) k m r,
    Np (f rc cr k m r)

theorem XeddsaSignTotal_is : Tacenta.UnitLifecycleT1.XeddsaSignTotal ↔
    XeddsaSignShape @tacenta_boundary.xeddsa.sign := Iff.rfl

theorem xeddsa_sign_satisfiable : ∃ f : XeddsaSignFn, XeddsaSignShape f :=
  ⟨fun _ _ _ _ r => ok (Array.repeat 64#usize 0#u8, r),
    by simp [XeddsaSignShape, Np]⟩

def Random32Shape {R : Type} (rc : rand_core_1.RngCore R) : Prop :=
  ∀ r bytes, bytes.val.length = 32 → Np (rc.fill_bytes r bytes)

theorem Random32Total_is {R : Type} (rc : rand_core_1.RngCore R) :
    Tacenta.UnitLifecycleT1.Random32Total rc ↔ Random32Shape rc := Iff.rfl

def totalRngCore : rand_core_1.RngCore Unit where
  next_u32 _ := ok (0#u32, ())
  next_u64 _ := ok (0#u64, ())
  fill_bytes _ bytes := ok ((), bytes)
  try_fill_bytes _ bytes := ok (core.result.Result.Ok (), (), bytes)

theorem random32_satisfiable :
    ∃ (R : Type) (rc : rand_core_1.RngCore R), Random32Shape rc :=
  ⟨Unit, totalRngCore, by simp [Random32Shape, Np, totalRngCore]⟩

abbrev MessageKeyMaterial := Tacenta.UnitLifecycleT1.MessageKeyMaterial
abbrev MessageKeyMaterialNewFn (W : Type → Type) :=
  MessageKeyMaterial → Result (W MessageKeyMaterial)
abbrev MessageKeyMaterialDerefFn (W : Type → Type) :=
  W MessageKeyMaterial → Result MessageKeyMaterial

def MessageKeyMaterialRoundTripShape (W : Type → Type)
    (new : MessageKeyMaterialNewFn W)
    (deref : MessageKeyMaterialDerefFn W) : Prop :=
  ∀ t, ∃ z, new t = ok z ∧ deref z = ok t

theorem MessageKeyMaterialRoundTrip_is :
    Tacenta.UnitLifecycleT1.MessageKeyMaterialRoundTrip ↔
      MessageKeyMaterialRoundTripShape zeroize.Zeroizing
        (zeroize.Zeroizing.new Tacenta.UnitLifecycleT1.messageKeyMaterialZeroize)
        (zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
          Tacenta.UnitLifecycleT1.messageKeyMaterialZeroize) :=
  Iff.rfl

theorem message_key_material_round_trip_satisfiable :
    ∃ (W : Type → Type) (new : MessageKeyMaterialNewFn W)
      (deref : MessageKeyMaterialDerefFn W),
      MessageKeyMaterialRoundTripShape W new deref := by
  refine ⟨(fun Z => Z), (fun t => ok t), (fun t => ok t), ?_⟩
  simp [MessageKeyMaterialRoundTripShape]

/-! ## Coverage

This conjunction is intentionally repetitive.  It makes the module depend on
all twelve named witnesses, so deleting one witness makes the kernel build fail
instead of silently reducing the recorded assumption coverage. -/

theorem all_twelve_contracts_satisfiable :
    (∃ (D P : Type) (W : Type → Type)
      (privateFromBytes : DhPrivateFromBytesFn D)
      (publicKey : DhPublicFn D P)
      (privateToBytes : DhPrivateToBytesFn D W)
      (publicFromBytes : DhPublicFromBytesFn P)
      (publicAsBytes : DhPublicAsBytesFn P)
      (eq : DhEqFn P),
      DhCodecShape D P W privateFromBytes publicKey privateToBytes
        publicFromBytes publicAsBytes eq) ∧
    (∃ (D P : Type) (f : DhAgreeFn D P), DhAgreeShape f) ∧
    (∃ f : AeadSealFn, AeadSealShape f) ∧
    (∃ f : AeadSealFn, AeadSealBoundedShape f) ∧
    (∃ f : AeadOpenFn, AeadOpenShape f) ∧
    (∃ f : KemEncapsulateFn, KemEncapsulateShape f) ∧
    (∃ (K : Type) (f : KemDecapsulateFn K), KemDecapsulateShape f) ∧
    (∃ e : Result Usize, KemCiphertextLenShape e) ∧
    (∃ (P : Type) (f : XeddsaVerifyFn P), XeddsaVerifyShape f) ∧
    (∃ f : XeddsaSignFn, XeddsaSignShape f) ∧
    (∃ (R : Type) (rc : rand_core_1.RngCore R), Random32Shape rc) ∧
    (∃ (W : Type → Type) (new : MessageKeyMaterialNewFn W)
      (deref : MessageKeyMaterialDerefFn W),
      MessageKeyMaterialRoundTripShape W new deref) :=
  ⟨dh_codec_satisfiable, dh_agree_satisfiable, aead_seal_satisfiable,
    aead_seal_bounded_satisfiable, aead_open_satisfiable, kem_encapsulate_satisfiable,
    kem_decapsulate_satisfiable, kem_ciphertext_len_satisfiable,
    xeddsa_verify_satisfiable, xeddsa_sign_satisfiable,
    random32_satisfiable, message_key_material_round_trip_satisfiable⟩

end Tacenta.UnitSatisfiabilitySession
