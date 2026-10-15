import Translation.UnitOracleModel
import Translation.UnitLifecycleDecryptRatchetT3
import Model.LifecycleFrame

/-!
# `DecryptOracleOf` from four laws

`DecryptOracleOf` (`UnitLifecycleDecryptRatchetT3.lean`) is the part of `OracleOf` that the
decrypt refinements take: the `dhPublic`, `dhAgree`, `aeadOpen` and `random32` clauses. The route
from laws to it was `oracleOf_of_laws` (`UnitOracleJoint.lean`) and `DecryptOracleOf.of_oracleOf`,
which takes all eleven `OracleLaws`, because `OracleOf` also has the identity, seal, KEM and
signing clauses the other laws serve. This module shows that four of the laws suffice for the
record. They are not shown necessary: of `DhCodecTotal` the proof uses only the `public_key`
conjunct, and the view law is stronger than the clauses need.

## What is shown

* `InterpO.decrypt`: an interpretation whose two DH types, `zeroize::Zeroizing`, the seven DH
  functions of `DhCodecTotal` and `DhAgreeTotal`, and `aead::decrypt` are the real constants. Its
  other fields are the model's (`InterpO.model`), except five whose types name the real DH or
  `Zeroizing` types and which no clause of `DecryptOracleOf` reads (`is_prime_order_public`,
  `xeddsa::verify` and the three `Zeroizing` methods); those refuse.
* `decryptInterp_laws_iff`: the three totality shapes over `InterpO.decrypt` are `DhCodecTotal`,
  `DhAgreeTotal` and `AeadOpenTotal`, by `Iff.rfl`, so the kernel accepts it only if each field
  those shapes read is the real constant.
* `dhViewInjective_real_iff`: `DhViewInjective` at the real constants is the conjunction the
  lemma below takes.
* `decryptOracleOf_of_laws`: under `DhCodecTotal`, `DhAgreeTotal`, `AeadOpenTotal` and the DH view
  law, for any draws and any Braid KEM, some oracle with those draws and that KEM meets
  `DecryptOracleOf` at the byte-stream source. The oracle is `oracleOfLaws` at `InterpO.decrypt`,
  and the three DH and AEAD clauses come from `dhPublicClause_of_laws`, `dhAgreeClause_of_laws`
  and `aeadOpenClause_of_laws` (`UnitOracleShape.lean`); `random32` is `byte_random32Clause`
  (`UnitLifecycleIntegrationScreen.lean`), which needs no law. It does not go through
  `oracleOf_of_laws`. Its statement takes only the four laws, which is what keeps the other seven
  off this route (held by its statement pin). Its axiom pin shows in addition that the witness
  oracle is built without the KEM, signing, identity-test, AEAD-seal and KDF constants; that is a
  property of this proof, not of the statement, and a proof of the same statement over
  `InterpO.real` mentions all of them.
* `decrypt_oracle_frame` (`Model/LifecycleFrame.lean`, pinned here): `Model.Lifecycle.decrypt`
  reads only the oracle's `draws`, `braidKem`, `dhPublic`, `dhAgree` and `aeadOpen`. So the
  fields of this oracle that `DecryptOracleOf` leaves free, other than `draws` and `braidKem`
  (which the lemma lets the caller choose), are not read by the model's `decrypt`.

## The sense

The four laws are assumed, not proved of the shipped functions: three are totality fields of the
contract records, and the view law is about the view the caller chooses and holds of the real
32-byte wrappers by reading. The oracle on the three read primitives is the code read through
its byte views, as in `oracleOfLaws`; the result ties the decrypt clauses to the code's own
primitives and to no specification of X25519 or the AEAD. The `random32` clause holds at the
byte-stream source (`byteRng`, `byteTrace`); a source with no state of its own is outside it, as
`LIMITATIONS.md` records for `DecryptOracleOf.random32`.

Not checked here: that the oracle's `braidKem` meets the Braid agreements a decrypt refinement
also takes, and that the four laws, the contract records and those agreements hold together at
one interpretation. The lemma lets the caller pick the KEM; it shows nothing about which KEMs
meet the agreements.

**Platform width.** No proof here chooses a width of `usize`, and no result depends on a
compiler-trust axiom (the axiom pins), so each result holds at both widths.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3
open Tacenta.UnitOracleShape
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf)

namespace Tacenta.UnitOracleDecrypt

open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace byte_random32Clause
  kemModelValid kemModelE)

/-- The decrypt-side interpretation: the real DH types, the real `zeroize::Zeroizing`, the
seven real DH functions and the real `aead::decrypt`; every other constant is the model's
(`InterpO.model`), and the five fields whose types mention the real DH or `Zeroizing` types
and that `DecryptOracleOf` does not read (`is_prime_order_public`, `xeddsa::verify` and the
three `Zeroizing` methods) refuse. -/
noncomputable def InterpO.decrypt : InterpO :=
  { Tacenta.UnitOracleModel.InterpO.model with
    PrivateKey := tacenta_boundary.dh.PrivateKey
    PublicKeyBytes := tacenta_boundary.dh.PublicKeyBytes
    Zeroizing := zeroize.Zeroizing
    dhPrivFromBytes := tacenta_boundary.dh.PrivateKey.from_bytes
    dhPrivPublicKey := tacenta_boundary.dh.PrivateKey.public_key
    dhPrivAgree := tacenta_boundary.dh.PrivateKey.agree
    dhPrivToBytes := tacenta_boundary.dh.PrivateKey.to_bytes
    dhPubFromBytes := tacenta_boundary.dh.PublicKeyBytes.from_bytes
    dhPubAsBytes := tacenta_boundary.dh.PublicKeyBytes.as_bytes
    dhPubEq := tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq
    dhIsPrimeOrderPublic := fun _ => fail .panic
    aeadDecrypt := tacenta_boundary.aead.decrypt
    xeddsaVerify := fun _ _ _ => fail .panic
    zNew := fun _ _ => fail .panic
    zDeref := fun _ _ => fail .panic
    zDerefMut := fun _ _ => fail .panic }

/-- A DH view over the decrypt-side interpretation: the caller's view, unchanged. -/
def dhViewD (dh : DhView) : DhViewOf InterpO.decrypt.toInterp := ⟨dh.privateKey, dh.publicKey⟩

/-- **The laws over `InterpO.decrypt` are the real ones.** Each side unfolds to the other, so the
kernel accepts this only if every field the three shapes read is the real constant. -/
theorem decryptInterp_laws_iff :
    (Tacenta.UnitSatisfiabilityJoint.DhCodecShape InterpO.decrypt.toInterp ∧
      Tacenta.UnitSatisfiabilityJoint.DhAgreeShape InterpO.decrypt.toInterp ∧
      Tacenta.UnitSatisfiabilityJoint.AeadOpenShape InterpO.decrypt.toInterp) ↔
    (Tacenta.UnitLifecycleT1.DhCodecTotal ∧ Tacenta.UnitLifecycleT1.DhAgreeTotal ∧
      Tacenta.UnitLifecycleT1.AeadOpenTotal) := Iff.rfl

/-- `DhViewInjective` at the real constants is the conjunction `decryptOracleOf_of_laws` takes. -/
theorem dhViewInjective_real_iff (dh : DhView) :
    DhViewInjective (dhViewOf dh) ↔
      Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey := Iff.rfl

/-- **`DecryptOracleOf` from four laws.** Under `DhCodecTotal`, `DhAgreeTotal`, `AeadOpenTotal`
and the DH view law, for any draws and any Braid KEM, some oracle with those draws and that KEM
meets `DecryptOracleOf` at the byte-stream source. -/
theorem decryptOracleOf_of_laws (dh : DhView)
    (hcodec : Tacenta.UnitLifecycleT1.DhCodecTotal) (hagree : Tacenta.UnitLifecycleT1.DhAgreeTotal)
    (hopen : Tacenta.UnitLifecycleT1.AeadOpenTotal)
    (hdh : Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey)
    (draws : List Model.Lifecycle.Key) (braidKem : Model.Braid.Kem) :
    ∃ oracle : Model.Lifecycle.Oracle, oracle.draws = draws ∧ oracle.braidKem = braidKem ∧
      DecryptOracleOf byteRng byteCrc dh byteTrace oracle := by
  let kem : KemViewOf InterpO.decrypt.toInterp := ⟨arrayOf (n := 32#usize)⟩
  let S : Array Std.U8 32#usize → Slice Std.U8 → Slice Std.U8 → Array Std.U8 64#usize :=
    Tacenta.UnitOracleModel.signS
  let base := oracleOfLaws InterpO.decrypt (dhViewD dh) kem kemModelValid kemModelE S
  refine ⟨{ base with draws := draws, braidKem := braidKem }, rfl, rfl, ?_⟩
  exact ⟨dhPublicClause_of_laws InterpO.decrypt (dhViewD dh) kem kemModelValid kemModelE S hcodec
      hdh.1,
    dhAgreeClause_of_laws InterpO.decrypt (dhViewD dh) kem kemModelValid kemModelE S hagree hdh,
    aeadOpenClause_of_laws InterpO.decrypt (dhViewD dh) kem kemModelValid kemModelE S hopen,
    byte_random32Clause⟩

end Tacenta.UnitOracleDecrypt

/-! ## Pins

The axiom list and the statement of each result, the bodies of the interpretation and the view,
and the model frame lemmas this module relies on, held by the build. `attest.py` requires them
(`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`). -/

/--
info: 'Tacenta.UnitOracleDecrypt.decryptOracleOf_of_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleDecrypt.decryptOracleOf_of_laws

/--
info: Tacenta.UnitOracleDecrypt.decryptOracleOf_of_laws : ∀ (dh : DhView),
  Tacenta.UnitLifecycleT1.DhCodecTotal →
    Tacenta.UnitLifecycleT1.DhAgreeTotal →
      Tacenta.UnitLifecycleT1.AeadOpenTotal →
        Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey →
          ∀ (draws : List Model.Lifecycle.Key) (braidKem : Model.Braid.Kem),
            ∃ oracle,
              oracle.draws = draws ∧
                oracle.braidKem = braidKem ∧
                  DecryptOracleOf Tacenta.UnitLifecycleIntegrationScreen.byteRng
                    Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh Tacenta.UnitLifecycleIntegrationScreen.byteTrace
                    oracle
-/
#guard_msgs in
#check @Tacenta.UnitOracleDecrypt.decryptOracleOf_of_laws

/--
info: 'Tacenta.UnitOracleDecrypt.decryptInterp_laws_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleDecrypt.decryptInterp_laws_iff

/--
info: Tacenta.UnitOracleDecrypt.decryptInterp_laws_iff : Tacenta.UnitSatisfiabilityJoint.DhCodecShape
      Tacenta.UnitOracleDecrypt.InterpO.decrypt.toInterp ∧
    Tacenta.UnitSatisfiabilityJoint.DhAgreeShape Tacenta.UnitOracleDecrypt.InterpO.decrypt.toInterp ∧
      Tacenta.UnitSatisfiabilityJoint.AeadOpenShape Tacenta.UnitOracleDecrypt.InterpO.decrypt.toInterp ↔
  Tacenta.UnitLifecycleT1.DhCodecTotal ∧ Tacenta.UnitLifecycleT1.DhAgreeTotal ∧ Tacenta.UnitLifecycleT1.AeadOpenTotal
-/
#guard_msgs in
#check @Tacenta.UnitOracleDecrypt.decryptInterp_laws_iff

/--
info: 'Tacenta.UnitOracleDecrypt.dhViewInjective_real_iff' depends on axioms: [propext,
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
#print axioms Tacenta.UnitOracleDecrypt.dhViewInjective_real_iff

/--
info: Tacenta.UnitOracleDecrypt.dhViewInjective_real_iff : ∀ (dh : DhView),
  DhViewInjective (dhViewOf dh) ↔ Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey
-/
#guard_msgs in
#check @Tacenta.UnitOracleDecrypt.dhViewInjective_real_iff

/--
info: def Tacenta.UnitOracleDecrypt.InterpO.decrypt : InterpO :=
have __src := Tacenta.UnitOracleModel.InterpO.model;
{ PrivateKey := tacenta_boundary.dh.PrivateKey, PublicKeyBytes := tacenta_boundary.dh.PublicKeyBytes,
  KemKeyPair := __src.KemKeyPair, IncrementalKeyPair := __src.IncrementalKeyPair, EncapsState := __src.EncapsState,
  Zeroizing := zeroize.Zeroizing, dhPrivFromBytes := tacenta_boundary.dh.PrivateKey.from_bytes,
  dhPrivPublicKey := tacenta_boundary.dh.PrivateKey.public_key, dhPrivAgree := tacenta_boundary.dh.PrivateKey.agree,
  dhPrivToBytes := tacenta_boundary.dh.PrivateKey.to_bytes,
  dhPubFromBytes := tacenta_boundary.dh.PublicKeyBytes.from_bytes,
  dhPubAsBytes := tacenta_boundary.dh.PublicKeyBytes.as_bytes,
  dhPubEq := tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
  dhIsPrimeOrderPublic := fun x => fail Error.panic, aeadEncrypt := __src.aeadEncrypt,
  aeadDecrypt := tacenta_boundary.aead.decrypt,
  kemEncapsulate := @Tacenta.UnitSatisfiabilityJoint.Interp.kemEncapsulate __src.toInterp,
  kemDecapsulate := __src.kemDecapsulate, xeddsaVerify := fun x x_1 x_2 => fail Error.panic,
  hkdfSha256 := __src.hkdfSha256, hmacSha256 := __src.hmacSha256, HEADER_LEN := __src.HEADER_LEN,
  EK_VECTOR_LEN := __src.EK_VECTOR_LEN, CT1_LEN := __src.CT1_LEN, CT2_LEN := __src.CT2_LEN, ikpClone := __src.ikpClone,
  ikpGenerate := @Tacenta.UnitSatisfiabilityJoint.Interp.ikpGenerate __src.toInterp, ikpHeader := __src.ikpHeader,
  ikpEkVector := __src.ikpEkVector, ikpDecapsulate := __src.ikpDecapsulate, esClone := __src.esClone,
  encapsulate1 := @Tacenta.UnitSatisfiabilityJoint.Interp.encapsulate1 __src.toInterp,
  encapsulate2 := __src.encapsulate2, validateEk := __src.validateEk,
  blanketZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.blanketZeroize __src.toInterp,
  arrayZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.arrayZeroize __src.toInterp,
  tupleZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.tupleZeroize __src.toInterp,
  pairZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.pairZeroize __src.toInterp,
  vecZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.vecZeroize __src.toInterp,
  zNew := fun {Z} x x_1 => fail Error.panic, zDeref := fun {Z} x x_1 => fail Error.panic,
  zDerefMut := fun {Z} x x_1 => fail Error.panic,
  vecPop := @Tacenta.UnitSatisfiabilityJoint.Interp.vecPop __src.toInterp,
  vecCapacity := @Tacenta.UnitSatisfiabilityJoint.Interp.vecCapacity __src.toInterp,
  vecTruncate := @Tacenta.UnitSatisfiabilityJoint.Interp.vecTruncate __src.toInterp,
  optionClone := @Tacenta.UnitSatisfiabilityJoint.Interp.optionClone __src.toInterp,
  optionAsMut := @Tacenta.UnitSatisfiabilityJoint.Interp.optionAsMut __src.toInterp,
  rangeFullIndex := @Tacenta.UnitSatisfiabilityJoint.Interp.rangeFullIndex __src.toInterp, divCeil := __src.divCeil,
  xeddsaSign := @InterpO.xeddsaSign __src }
-/
#guard_msgs in
#print Tacenta.UnitOracleDecrypt.InterpO.decrypt

/--
info: def Tacenta.UnitOracleDecrypt.dhViewD : DhView → DhViewOf Tacenta.UnitOracleDecrypt.InterpO.decrypt.toInterp :=
fun dh => { privateKey := dh.privateKey, publicKey := dh.publicKey }
-/
#guard_msgs in
#print Tacenta.UnitOracleDecrypt.dhViewD

/--
info: 'Model.Lifecycle.decrypt_oracle_frame' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Lifecycle.decrypt_oracle_frame

/--
info: Model.Lifecycle.decrypt_oracle_frame : ∀ (view : Model.Lifecycle.CodewordView) (oracle oracle' : Model.Lifecycle.Oracle)
  (session : Model.Lifecycle.Session) (message : Model.Lifecycle.Bytes),
  oracle'.draws = oracle.draws →
    oracle'.braidKem = oracle.braidKem →
      oracle'.dhPublic = oracle.dhPublic →
        oracle'.dhAgree = oracle.dhAgree →
          oracle'.aeadOpen = oracle.aeadOpen →
            Model.Lifecycle.decrypt view oracle' session message =
              have __src := Model.Lifecycle.decrypt view oracle session message;
              { session := __src.session, result := __src.result,
                oracle :=
                  { draws := (Model.Lifecycle.decrypt view oracle session message).oracle.draws,
                    braidKem := oracle'.braidKem, dhPublic := oracle'.dhPublic, dhAgree := oracle'.dhAgree,
                    identityValid := oracle'.identityValid, aeadSeal := oracle'.aeadSeal, aeadOpen := oracle'.aeadOpen,
                    kemValid := oracle'.kemValid, kemEncaps := oracle'.kemEncaps, kemDecaps := oracle'.kemDecaps,
                    sigVerify := oracle'.sigVerify, sigSign := oracle'.sigSign } }
-/
#guard_msgs in
#check @Model.Lifecycle.decrypt_oracle_frame

/--
info: 'Model.Lifecycle.decryptRatchet_oracle_frame' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Lifecycle.decryptRatchet_oracle_frame

/--
info: Model.Lifecycle.decryptRatchet_oracle_frame : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle oracle' : Model.Lifecycle.Oracle) (session : Model.Lifecycle.Session) (message : Model.Lifecycle.Bytes),
  oracle'.draws = oracle.draws →
    oracle'.braidKem = oracle.braidKem →
      oracle'.dhPublic = oracle.dhPublic →
        oracle'.dhAgree = oracle.dhAgree →
          oracle'.aeadOpen = oracle.aeadOpen →
            Model.Lifecycle.decryptRatchet view oracle' session message =
              have __src := Model.Lifecycle.decryptRatchet view oracle session message;
              { session := __src.session, result := __src.result,
                oracle :=
                  { draws := (Model.Lifecycle.decryptRatchet view oracle session message).oracle.draws,
                    braidKem := oracle'.braidKem, dhPublic := oracle'.dhPublic, dhAgree := oracle'.dhAgree,
                    identityValid := oracle'.identityValid, aeadSeal := oracle'.aeadSeal, aeadOpen := oracle'.aeadOpen,
                    kemValid := oracle'.kemValid, kemEncaps := oracle'.kemEncaps, kemDecaps := oracle'.kemDecaps,
                    sigVerify := oracle'.sigVerify, sigSign := oracle'.sigSign } }
-/
#guard_msgs in
#check @Model.Lifecycle.decryptRatchet_oracle_frame

/--
info: 'Model.Lifecycle.dispatchDecrypt_oracle_frame' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Lifecycle.dispatchDecrypt_oracle_frame

/--
info: Model.Lifecycle.dispatchDecrypt_oracle_frame : ∀ (oracle oracle' : Model.Lifecycle.Oracle)
  (session : Model.Lifecycle.Session) (message : Model.Lifecycle.Bytes),
  oracle'.dhAgree = oracle.dhAgree →
    Model.Lifecycle.dispatchDecrypt oracle' session message = Model.Lifecycle.dispatchDecrypt oracle session message
-/
#guard_msgs in
#check @Model.Lifecycle.dispatchDecrypt_oracle_frame
