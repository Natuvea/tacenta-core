import Translation.UnitOracleShape

/-!
# A joint model for `OracleOf`, extending #220's interpretation

`UnitSatisfiabilityJoint.lean` interprets the opaque constants the four session contract records
reach (`Interp.model`); its key types are `Unit` and its primitives return defaults. `OracleOf`
needs more: with `DhCodecOf` beside it, a DH key must carry 32 bytes, and a model whose primitives
answer every input alike would satisfy the clauses only because nothing is refused. This module
gives `InterpO.model`: #220's interpretation with the DH and KEM key types made 32-byte arrays and
the oracle's primitives made toy functions that refuse some inputs, plus `xeddsa::sign`.

## The toy primitives

* DH: the public key of a secret is the secret; agreement is the byte-wise exclusive or of the two
  keys, refused when it is zero (`agreeModel`). Prime-order test: the key is not zero.
* AEAD: sealing puts a zero byte in front of the plaintext (where that fits in a `usize`
  length); opening accepts exactly a string whose first byte is zero and returns the rest.
* KEM: a key is valid when it is 1568 bytes long (the screen's `kemModelValid`); encapsulation
  refuses an invalid key before it reads the RNG, and otherwise reads 32 bytes, which are both the
  ciphertext and the shared secret (`encapModelO`). Decapsulation returns a 32-byte ciphertext as
  the secret and refuses every other length.
* XEdDSA: signing reads 64 bytes and returns the secret followed by 32 zero bytes; verification
  accepts exactly a signature whose first 32 bytes are the public key.
* Key generation (`ikpGenerate`) reads 64 bytes, as `GenerateFillsOnce64` says.

Every other field is #220's. None of these is secure; they are functionally like the primitives
(they refuse, they round trip), which is what a model of the clauses needs.

## What is shown

`modelO_axiomBase`: #220's axiom base (`AxiomBase`, the axiom parts of the four records and the
five standard-library laws) holds at this interpretation with the byte-stream random source.
`modelO_laws`: the DH codec, the two view laws and #234's three random-source laws hold there too.
The clauses themselves are decided in `UnitOracleDh.lean`, `UnitOracleAead.lean` and
`UnitOracleKemSig.lean`, and all together in `UnitOracleJoint.lean`.

No proof here chooses a width of `usize`; the one length fact used (32 at most `Usize.max`) is
`small_le_usize_max`, proved for both widths.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3

namespace Tacenta.UnitOracleModel

open Tacenta.UnitOracleShape
open Tacenta.UnitSatisfiabilityJoint
open Tacenta.UnitSatisfiabilityRecords (AxiomBase)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace zeros32 zeros64 SignFn
  EncapFn kemModelValid SignFillsOnce64Of KemShapeOf)

def zero32 : Array U8 32#usize := Array.repeat 32#usize 0#u8

/-- Byte-wise exclusive or of two 32-byte arrays. -/
def xor32 (a b : Array U8 32#usize) : Array U8 32#usize :=
  ⟨List.zipWith (fun x y => (⟨x.bv ^^^ y.bv⟩ : U8)) a.val b.val, by
    simp [a.property, b.property]⟩

/-- A toy agreement: the exclusive or of the two keys, refused when it is zero. -/
def agreeModel (k p : Array U8 32#usize) : Option (Array U8 32#usize) :=
  if (xor32 k p).val = zero32.val then none else some (xor32 k p)

/-- A toy seal: a zero byte in front of the plaintext, where that fits. -/
def sealModel (p : Slice U8) : alloc.vec.Vec U8 :=
  if h : p.val.length + 1 ≤ Usize.max then ⟨0#u8 :: p.val, by simp; omega⟩
  else ⟨p.val, p.property⟩

/-- A toy open: accepts exactly a string whose first byte is zero, and returns the rest. -/
def openModel (c : Slice U8) : core.result.Result (alloc.vec.Vec U8) Unit :=
  match h : c.val with
  | x :: rest =>
    if x = 0#u8 then .Ok ⟨rest, by have := c.property; rw [h] at this; simp at this; omega⟩
    else .Err ()
  | [] => .Err ()

/-- A byte as the translation's `u8`. -/
def ofByte (x : UInt8) : U8 := ⟨x.toBitVec⟩

/-- At most the first 32 bytes, as a vector. -/
def bytesVec32 (m : Bytes) : alloc.vec.Vec U8 :=
  ⟨(m.take 32).map ofByte, by
    simp only [List.length_map, List.length_take]
    have := Tacenta.SessionUnitSessionT1.small_le_usize_max (n := 32) (by decide)
    omega⟩

/-- The first 32 bytes, padded with zeros, as an array. -/
def bytesArr32 (m : Bytes) : Array U8 32#usize :=
  ⟨((m ++ List.replicate 32 0).take 32).map ofByte, by simp⟩

/-- The toy encapsulation's result: the 32 drawn bytes are both the ciphertext and the secret. -/
def kemModelE (_publicKey m : Bytes) : alloc.vec.Vec U8 × Array U8 32#usize :=
  (bytesVec32 m, bytesArr32 m)

def encapModelO : EncapFn := fun rc _ publicKey rng =>
  if kemModelValid (sliceOf publicKey) then
    (do let (rng', m) ← rc.fill_bytes rng zeros32
        ok (core.result.Result.Ok (kemModelE (sliceOf publicKey) (sliceOf m)), rng'))
  else ok (.Err (), rng)

/-- A toy decapsulation: a 32-byte ciphertext is its own secret; any other length is refused. -/
def decapsModel (_keyPair : Array U8 32#usize) (c : Slice U8) :
    Result (core.result.Result (Array U8 32#usize) Unit) :=
  ok (if h : c.val.length = 32 then .Ok ⟨c.val, by simpa using h⟩ else .Err ())

/-- A toy signature: the secret followed by 32 zero bytes. -/
def signS (sk : Array U8 32#usize) (_m _z : Slice U8) : Array U8 64#usize :=
  ⟨sk.val ++ List.replicate 32 0#u8, by simp [sk.property]⟩

def signModelO : SignFn := fun rc _ sk m rng => do
  let (rng', z) ← rc.fill_bytes rng zeros64
  ok (signS sk m z, rng')

/-- A toy verification: accepts exactly a signature whose first 32 bytes are the public key. -/
def verifyModel (pk : Array U8 32#usize) (_m : Slice U8) (s : Array U8 64#usize) :
    Result (core.result.Result Unit Unit) :=
  ok (if s.val.take 32 = pk.val then .Ok () else .Err ())

/-- The joint interpretation: #220's, with the fields above. -/
def InterpO.model : InterpO :=
  { Interp.model with
    PrivateKey := Array U8 32#usize
    PublicKeyBytes := Array U8 32#usize
    KemKeyPair := Array U8 32#usize
    dhPrivFromBytes := fun a => ok a
    dhPrivPublicKey := fun k => ok k
    dhPrivAgree := fun k p => ok (agreeModel k p)
    dhPrivToBytes := fun k => ok k
    dhPubFromBytes := fun a => ok a
    dhPubAsBytes := fun p => ok p
    dhPubEq := fun a b => ok (decide (a.val = b.val))
    dhIsPrimeOrderPublic := fun p => ok (decide (p.val ≠ zero32.val))
    aeadEncrypt := fun _ _ _ p _ => ok (sealModel p)
    aeadDecrypt := fun _ _ _ c _ => ok (openModel c)
    kemEncapsulate := encapModelO
    kemDecapsulate := decapsModel
    xeddsaVerify := verifyModel
    ikpGenerate := fun rc _ rng => do
      let (rng', _) ← rc.fill_bytes rng zeros64
      ok (.Ok (), rng')
    xeddsaSign := signModelO }

/-- The interpretation without the signing field. -/
abbrev M : Interp := InterpO.model.toInterp

/-- The byte views of the model's key types. -/
def dhM : DhViewOf M := ⟨arrayOf, arrayOf⟩
def kemM : KemViewOf M := ⟨arrayOf⟩

/-! ## #220's axiom base at this interpretation -/

theorem modelO_DhCodec : DhCodecShape M :=
  ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩,
    fun _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩⟩
theorem modelO_DhIdentity : DhIdentityShape M := fun _ => ⟨_, rfl⟩
theorem modelO_DhAgree : DhAgreeShape M := fun _ _ => ⟨_, rfl⟩
theorem modelO_KemDecapsulate : KemDecapsulateShape M := fun _ _ => ⟨_, rfl⟩
theorem modelO_XeddsaVerify : XeddsaVerifyShape M := fun _ _ _ => ⟨_, rfl⟩
theorem modelO_AeadOpen : AeadOpenShape M := fun _ _ _ _ _ => ⟨_, rfl⟩

theorem modelO_AeadSealBounded : AeadSealBoundedShape M := by
  intro ek mk iv plaintext ad
  refine ⟨sealModel plaintext, rfl, ?_⟩
  unfold sealModel
  split <;> simp

theorem modelO_KemEncapsulate : KemEncapsulateShape M := by
  intro R rc cr p r hrng
  show ∃ x, encapModelO rc cr p r = ok x
  unfold encapModelO
  split
  · obtain ⟨⟨r', m⟩, h⟩ := hrng r zeros32
    rw [h]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem modelO_KeyPairGenerate : KeyPairGenerateShape M := by
  intro R rc crc rng hrng
  obtain ⟨⟨r', m⟩, h⟩ := hrng rng zeros64
  show ∃ x, (do let (rng', _) ← rc.fill_bytes rng zeros64
                ok (core.result.Result.Ok (), rng')) = ok x
  rw [h]
  exact ⟨_, rfl⟩

theorem byteRng_total : Tacenta.UnitLifecycleT1.RngTotal byteRng := fun _ _ => ⟨_, rfl⟩

def modelO_ZeroizingModel (Z : Type) : ZeroizingModelShape M Z where
  contents z := z
  new _ _ := by simp [M, InterpO.model, Interp.model]
  deref _ _ := by simp [M, InterpO.model, Interp.model]
  deref_mut _ _ := by simp [M, InterpO.model, Interp.model]

theorem modelO_Faithful : FaithfulShape M :=
  ⟨model_Faithful.pop_nil, model_Faithful.pop_snoc, model_Faithful.truncate,
    model_Faithful.divCeil, model_Faithful.asMut, model_Faithful.capacity⟩

theorem modelO_StdLaws : StdLaws M :=
  stdLaws_of_faithful M modelO_Faithful model_BlanketU32

/-- **#220's axiom base holds at the joint interpretation**, with the byte-stream source. The
fields this module does not change are #220's witnesses, reused unchanged. -/
theorem modelO_axiomBase : AxiomBase M byteRng where
  encrypt :=
    ⟨⟨byteRng_total, model_KeyPairClone, model_EncapsStateClone, modelO_KeyPairGenerate,
        model_KeyPairHeader, model_Hmac, model_Hkdf, model_Encapsulate1,
        model_ZeroizingArrayRoundTrip, model_ArrayZeroize, model_RangeFullIndex⟩,
      ⟨model_Hmac, model_Hkdf, model_SpqrZeroize, model_VecRetainAxiom, model_OptionClone⟩,
      modelO_AeadSealBounded, model_MessageKeyMaterialRoundTrip, modelO_DhCodec⟩
  decrypt :=
    ⟨modelO_DhCodec, modelO_DhAgree, modelO_AeadOpen, random32_of_rngTotal byteRng_total,
      ⟨model_Ct1Len, model_Ct2Len, model_HeaderLen, model_EkVectorLen,
        model_KeyPairEkVector, model_KeyPairDecapsulate, model_Hkdf, model_Hmac,
        model_ValidateEk, model_Encapsulate2, model_KeyPairClone, model_EncapsStateClone,
        model_OptionClone, model_ZeroizingArrayRoundTrip, model_ArrayZeroize,
        model_RangeFullIndex⟩,
      ⟨model_Hmac, model_Hkdf, model_ZeroizingTotal, model_SpqrZeroize,
        model_VecRetainAxiom, model_OptionClone, trivial⟩,
      model_MessageKeyMaterialRoundTrip⟩
  initiator :=
    ⟨⟨modelO_DhCodec, modelO_DhIdentity, modelO_DhAgree, modelO_KemEncapsulate,
      modelO_XeddsaVerify, byteRng_total, random32_of_rngTotal byteRng_total, model_Hkdf,
      modelO_ZeroizingModel SessionZ, model_ZeroizingTotal, model_SpqrZeroize, model_Hkdf,
      model_ZeroizingArrayRoundTrip, model_RangeFullIndex⟩⟩
  responder :=
    ⟨⟨⟨modelO_DhCodec, modelO_DhAgree, modelO_AeadOpen, random32_of_rngTotal byteRng_total,
        ⟨model_Ct1Len, model_Ct2Len, model_HeaderLen, model_EkVectorLen,
          model_KeyPairEkVector, model_KeyPairDecapsulate, model_Hkdf, model_Hmac,
          model_ValidateEk, model_Encapsulate2, model_KeyPairClone, model_EncapsStateClone,
          model_OptionClone, model_ZeroizingArrayRoundTrip, model_ArrayZeroize,
          model_RangeFullIndex⟩,
        ⟨model_Hmac, model_Hkdf, model_ZeroizingTotal, model_SpqrZeroize,
          model_VecRetainAxiom, model_OptionClone, trivial⟩,
        model_MessageKeyMaterialRoundTrip⟩,
      modelO_DhIdentity, modelO_KemDecapsulate, model_Hkdf,
      modelO_ZeroizingModel SessionZ, model_VecPop, model_DivCeilValue⟩⟩
  derivedKeys := ⟨modelO_ZeroizingModel DerivedZ⟩
  laws := modelO_StdLaws

/-! ## The laws `OracleOf` adds hold at this interpretation -/

theorem modelO_dhCodecOf : DhCodecOfShape M dhM :=
  ⟨fun b => ⟨b, rfl, rfl⟩, fun b => ⟨b, rfl, rfl⟩, fun p => ⟨p, rfl, rfl⟩⟩

theorem modelO_dhViewInjective : DhViewInjective dhM :=
  ⟨arrayOf_injective _, arrayOf_injective _⟩

theorem modelO_kemViewInjective : KemViewInjective kemM := arrayOf_injective _

theorem modelO_signLaw : SignFillsOnce64Of InterpO.model.xeddsaSign :=
  ⟨signS, fun _ _ _ _ _ => rfl⟩

theorem modelO_kemLaw : KemShapeOf InterpO.model.kemEncapsulate :=
  ⟨kemModelValid, kemModelE, fun _ _ _ _ => rfl⟩

theorem modelO_generateLaw : GenerateFillsOnce64Shape M :=
  ⟨fun _ => .Ok (), fun _ _ _ => rfl⟩

/-- **The laws `OracleOf` adds hold at the joint interpretation**, together with #220's axiom
base: the DH codec, the two view laws, and #234's signing, KEM and key-generation laws. -/
theorem modelO_laws :
    AxiomBase M byteRng ∧ DhCodecOfShape M dhM ∧ DhViewInjective dhM ∧ KemViewInjective kemM ∧
      SignFillsOnce64Of InterpO.model.xeddsaSign ∧ KemShapeOf InterpO.model.kemEncapsulate ∧
      GenerateFillsOnce64Shape M :=
  ⟨modelO_axiomBase, modelO_dhCodecOf, modelO_dhViewInjective, modelO_kemViewInjective,
    modelO_signLaw, modelO_kemLaw, modelO_generateLaw⟩

/-- The oracle of the joint interpretation. -/
noncomputable def oracleM : Model.Lifecycle.Oracle :=
  oracleOfLaws InterpO.model dhM kemM kemModelValid kemModelE signS

end Tacenta.UnitOracleModel

/-! ## Pins

The axiom list and the statement of each result, held by the build. `attest.py` requires them
(`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`). -/

/--
info: 'Tacenta.UnitOracleModel.modelO_axiomBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleModel.modelO_axiomBase

/--
info: Tacenta.UnitOracleModel.modelO_axiomBase : Tacenta.UnitSatisfiabilityRecords.AxiomBase Tacenta.UnitOracleModel.M
  Tacenta.UnitLifecycleIntegrationScreen.byteRng
-/
#guard_msgs in
#check @Tacenta.UnitOracleModel.modelO_axiomBase

/--
info: 'Tacenta.UnitOracleModel.modelO_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleModel.modelO_laws

/--
info: Tacenta.UnitOracleModel.modelO_laws : Tacenta.UnitSatisfiabilityRecords.AxiomBase Tacenta.UnitOracleModel.M
    Tacenta.UnitLifecycleIntegrationScreen.byteRng ∧
  Tacenta.UnitOracleShape.DhCodecOfShape Tacenta.UnitOracleModel.M Tacenta.UnitOracleModel.dhM ∧
    Tacenta.UnitOracleShape.DhViewInjective Tacenta.UnitOracleModel.dhM ∧
      Tacenta.UnitOracleShape.KemViewInjective Tacenta.UnitOracleModel.kemM ∧
        (Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64Of fun {R} =>
            Tacenta.UnitOracleModel.InterpO.model.xeddsaSign) ∧
          (Tacenta.UnitLifecycleIntegrationScreen.KemShapeOf fun {R} =>
              Tacenta.UnitOracleModel.InterpO.model.kemEncapsulate) ∧
            Tacenta.UnitOracleShape.GenerateFillsOnce64Shape Tacenta.UnitOracleModel.M
-/
#guard_msgs in
#check @Tacenta.UnitOracleModel.modelO_laws

/--
info: def Tacenta.UnitOracleModel.InterpO.model : Tacenta.UnitOracleShape.InterpO :=
let __src := Tacenta.UnitSatisfiabilityJoint.Interp.model;
{ PrivateKey := Std.Array U8 32#usize, PublicKeyBytes := Std.Array U8 32#usize, KemKeyPair := Std.Array U8 32#usize,
  IncrementalKeyPair := __src.IncrementalKeyPair, EncapsState := __src.EncapsState, Zeroizing := __src.Zeroizing,
  dhPrivFromBytes := fun a => ok a, dhPrivPublicKey := fun k => ok k,
  dhPrivAgree := fun k p => ok (Tacenta.UnitOracleModel.agreeModel k p), dhPrivToBytes := fun k => ok k,
  dhPubFromBytes := fun a => ok a, dhPubAsBytes := fun p => ok p, dhPubEq := fun a b => ok (decide (↑a = ↑b)),
  dhIsPrimeOrderPublic := fun p => ok (decide (↑p ≠ ↑Tacenta.UnitOracleModel.zero32)),
  aeadEncrypt := fun x x_1 x_2 p x_3 => ok (Tacenta.UnitOracleModel.sealModel p),
  aeadDecrypt := fun x x_1 x_2 c x_3 => ok (Tacenta.UnitOracleModel.openModel c),
  kemEncapsulate := fun {R} => Tacenta.UnitOracleModel.encapModelO,
  kemDecapsulate := Tacenta.UnitOracleModel.decapsModel, xeddsaVerify := Tacenta.UnitOracleModel.verifyModel,
  hkdfSha256 := __src.hkdfSha256, hmacSha256 := __src.hmacSha256, HEADER_LEN := __src.HEADER_LEN,
  EK_VECTOR_LEN := __src.EK_VECTOR_LEN, CT1_LEN := __src.CT1_LEN, CT2_LEN := __src.CT2_LEN, ikpClone := __src.ikpClone,
  ikpGenerate := fun {R} rc x rng => do
    let (rng', _) ← rc.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros64
    ok (core.result.Result.Ok (), rng'),
  ikpHeader := __src.ikpHeader, ikpEkVector := __src.ikpEkVector, ikpDecapsulate := __src.ikpDecapsulate,
  esClone := __src.esClone, encapsulate1 := @Tacenta.UnitSatisfiabilityJoint.Interp.encapsulate1 __src,
  encapsulate2 := __src.encapsulate2, validateEk := __src.validateEk,
  blanketZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.blanketZeroize __src,
  arrayZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.arrayZeroize __src,
  tupleZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.tupleZeroize __src,
  vecZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.vecZeroize __src,
  zNew := @Tacenta.UnitSatisfiabilityJoint.Interp.zNew __src,
  zDeref := @Tacenta.UnitSatisfiabilityJoint.Interp.zDeref __src,
  zDerefMut := @Tacenta.UnitSatisfiabilityJoint.Interp.zDerefMut __src,
  vecPop := @Tacenta.UnitSatisfiabilityJoint.Interp.vecPop __src,
  vecCapacity := @Tacenta.UnitSatisfiabilityJoint.Interp.vecCapacity __src,
  vecTruncate := @Tacenta.UnitSatisfiabilityJoint.Interp.vecTruncate __src,
  optionClone := @Tacenta.UnitSatisfiabilityJoint.Interp.optionClone __src,
  optionAsMut := @Tacenta.UnitSatisfiabilityJoint.Interp.optionAsMut __src,
  rangeFullIndex := @Tacenta.UnitSatisfiabilityJoint.Interp.rangeFullIndex __src, divCeil := __src.divCeil,
  xeddsaSign := fun {R} => Tacenta.UnitOracleModel.signModelO }
-/
#guard_msgs in
#print Tacenta.UnitOracleModel.InterpO.model

/--
info: def Tacenta.UnitOracleModel.oracleM : Model.Lifecycle.Oracle :=
Tacenta.UnitOracleShape.oracleOfLaws Tacenta.UnitOracleModel.InterpO.model Tacenta.UnitOracleModel.dhM
  Tacenta.UnitOracleModel.kemM Tacenta.UnitLifecycleIntegrationScreen.kemModelValid Tacenta.UnitOracleModel.kemModelE
  Tacenta.UnitOracleModel.signS
-/
#guard_msgs in
#print Tacenta.UnitOracleModel.oracleM
