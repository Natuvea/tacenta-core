import Translation.UnitOracleAead
import Translation.UnitOracleKemSig

/-!
# `OracleOf` as a whole: inhabited under named laws, and the laws have a model

`UnitOracleShape.lean`, `UnitOracleDh.lean`, `UnitOracleAead.lean` and `UnitOracleKemSig.lean`
decide the seven clauses #234 left open, one cluster at a time. This module puts them together.

## What is shown

* `OracleLaws I dh kem`: laws under which `OracleOf` holds over an interpretation, sufficient and
  not shown necessary. Seven are totality
  fields of the four contract records (`DhCodecTotal`, `DhAgreeTotal`, `DhIdentityTotal`,
  `AeadSealBounded`, `AeadOpenTotal`, `KemDecapsulateTotal`, `XeddsaVerifyTotal`), two are #234's
  laws (`SignFillsOnce64`, `KemShape`), and two are new: the DH and KEM views are injective.
  `oracleLaws_real_iff` binds them at the real constants to those named predicates.
* `oracleOfShape_of_oracleLaws`: for every interpretation, the laws give one oracle for which all
  twelve clauses and the guarded KEM clause hold at the byte-stream source.
* `oracleOfGuarded_of_laws`, `oracleOf_of_laws`: the same at the real constants: under the laws,
  for any views that meet the two view laws, `OracleOfGuarded` and so `OracleOf` are inhabited at
  the byte-stream source.
* `oracleLaws_hold_jointly`: one interpretation (`InterpO.model`) meets the laws together with
  #220's whole axiom base (`AxiomBase`), the DH codec and #234's key-generation law.
* `oracleOf_joint_model`: at that interpretation, `OracleOf`'s twelve clauses, the guarded KEM
  clause, the axiom base and every law hold together, for an oracle that refuses an input of each
  primitive that can refuse and whose KEM encapsulates at an accepted key.

## The sense

`oracleOf_of_laws` is a theorem at the real constants and holds under its laws for every
assignment of the opaque constants. `oracleLaws_hold_jointly` exhibits an assignment under which
the laws and #220's base hold. So a derivation of `False` from these laws, or from `OracleOf` with
the views it is given and the oracle it supplies, at the real constants, would become, after the
constants are replaced by the model's terms, a derivation of `False` from facts true in the model.
That last step is an argument about derivations, as in `UnitSatisfiabilityJoint.lean`, and not a
theorem inside Lean. No compiler-trust fact in the import closure mentions an interpreted
constant, directly or through a definition. That covers the unit's 143 and the 11 in
`SessionUnitSpqrT3.lean` and `SessionUnitTripleT3.lean`. `xeddsa::sign`, which `InterpO` adds, is
one of the uninterpreted constants of the unit. The classification audit covers `Interp.real` and
the four records. It is not run for `InterpO.real` and `OracleOf`.

The oracle that inhabits the record is the code read through the byte views (`oracleOfLaws`): each
primitive's verdict is the code's answer on arguments with those bytes. So `OracleOf` asks of the
code only that each primitive returns, that its result depends only on the bytes of its arguments,
and that it reads the random source in the stated order. It ties the dispatch theorems to the
code's own primitives and to no specification of X25519, the AEAD, ML-KEM or XEdDSA.

It is not a statement about the Rust. The seven totality laws are assumptions of the records. The
two view laws are about the views the caller chooses: by reading, each real type has an injective
view (its wrapped bytes), which also meets `DhCodecOf`, and a result applies to a caller's view
only if that view is injective. `SignFillsOnce64` and `KemShape` are read from the source (#234)
and tested by `tacenta-core/tests/rng_fill_counts.rs`, not proved. The model's primitives are
toys.

**Pins of the laws.** Besides the pins of the results, the pin section below prints the bodies of
the seven totality predicates, their seven shapes over an interpretation, and `NoPanic` and `Np`,
which they print through, so a change to the text of a law fails the build here.

**Platform width.** `Usize.max` is `u32::MAX` or `u64::MAX` (`Usize.bounds_eq`, a conjunct of
`oracleOf_joint_model`). No proof here chooses one, and no result depends on a compiler-trust axiom
(the axiom pins), so nothing evaluates the width: each result holds at both.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3
open Tacenta.UnitOracleShape
open Tacenta.UnitOracleModel
open Tacenta.UnitOracleKemSig (KemGuardedClause OracleOfGuarded kemGuardedClause_of_law
  oracleOfGuarded_iff_shape key1568)

namespace Tacenta.UnitOracleJoint

open Tacenta.UnitSatisfiabilityJoint (Interp DhCodecShape DhAgreeShape DhIdentityShape
  AeadSealBoundedShape AeadOpenShape KemDecapsulateShape XeddsaVerifyShape)
open Tacenta.UnitSatisfiabilityRecords (AxiomBase)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace SignFillsOnce64Of
  KemShapeOf kemClauses_of_law sigSignClause_of_law byte_random32Clause kemModelValid)

/-- Laws under which `OracleOf` holds, over an interpretation and two views. Some are stronger than
any clause requires. -/
structure OracleLaws (I : InterpO) (dh : DhViewOf I.toInterp) (kem : KemViewOf I.toInterp) :
    Prop where
  dhCodec : DhCodecShape I.toInterp
  dhAgree : DhAgreeShape I.toInterp
  dhIdentity : DhIdentityShape I.toInterp
  aeadSeal : AeadSealBoundedShape I.toInterp
  aeadOpen : AeadOpenShape I.toInterp
  kemDecapsulate : KemDecapsulateShape I.toInterp
  xeddsaVerify : XeddsaVerifyShape I.toInterp
  signLaw : SignFillsOnce64Of I.xeddsaSign
  kemLaw : KemShapeOf I.kemEncapsulate
  dhView : DhViewInjective dh
  kemView : KemViewInjective kem

/-- **The laws at the real constants are the named predicates**: seven totality fields of the
contract records, #234's two laws, and the two view laws. -/
theorem oracleLaws_real_iff (dh : DhView) (kem : KemView) :
    OracleLaws InterpO.real (dhViewOf dh) (kemViewOf kem) ↔
      Tacenta.UnitLifecycleT1.DhCodecTotal ∧ Tacenta.UnitLifecycleT1.DhAgreeTotal ∧
      Tacenta.UnitLifecycleT1.DhIdentityTotal ∧ Tacenta.UnitLifecycleT1.AeadSealBounded ∧
      Tacenta.UnitLifecycleT1.AeadOpenTotal ∧ Tacenta.UnitLifecycleT1.KemDecapsulateTotal ∧
      Tacenta.UnitLifecycleT1.XeddsaVerifyTotal ∧
      Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64 ∧
      Tacenta.UnitLifecycleIntegrationScreen.KemShape ∧
      (Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey) ∧
      Function.Injective kem.keyPair :=
  ⟨fun h => ⟨h.dhCodec, h.dhAgree, h.dhIdentity, h.aeadSeal, h.aeadOpen, h.kemDecapsulate,
      h.xeddsaVerify, h.signLaw, h.kemLaw, h.dhView, h.kemView⟩,
   fun ⟨a, b, c, d, e, f, g, i, j, k, l⟩ => ⟨a, b, c, d, e, f, g, i, j, k, l⟩⟩

/-- **The laws give `OracleOf`'s twelve clauses and the guarded KEM clause** at the byte-stream
source, for one oracle, over every interpretation. -/
theorem oracleOfShape_of_oracleLaws (I : InterpO) (dh : DhViewOf I.toInterp)
    (kem : KemViewOf I.toInterp) (h : OracleLaws I dh kem) :
    ∃ oracle : Model.Lifecycle.Oracle,
      OracleOfShape I byteRng byteCrc dh kem byteTrace oracle ∧
      KemGuardedClause (I.kemEncapsulate byteRng byteCrc) byteTrace oracle := by
  obtain ⟨S, hS⟩ := h.signLaw
  obtain ⟨valid, E, hK⟩ := h.kemLaw
  let oracle := oracleOfLaws I dh kem valid E S
  refine ⟨oracle, (oracleOfShape_iff_clauses I byteRng byteCrc dh kem byteTrace oracle).mpr
    ⟨dhPublicClause_of_laws I dh kem valid E S h.dhCodec h.dhView.1,
     dhAgreeClause_of_laws I dh kem valid E S h.dhAgree h.dhView,
     identityValidClause_of_laws I dh kem valid E S h.dhCodec h.dhIdentity h.dhView.2,
     aeadSealClause_of_laws I dh kem valid E S h.aeadSeal,
     aeadOpenClause_of_laws I dh kem valid E S h.aeadOpen,
     kemClauses_of_law valid E (I.kemEncapsulate byteRng byteCrc)
       (fun pk rng => hK byteRng byteCrc pk rng) oracle rfl rfl,
     kemDecapsulateClause_of_laws I dh kem valid E S h.kemDecapsulate h.kemView,
     sigVerifyClause_of_laws I dh kem valid E S h.xeddsaVerify h.dhView.2,
     sigSignClause_of_law S (I.xeddsaSign byteRng byteCrc)
       (fun secret message rng => hS byteRng byteCrc secret message rng) oracle rfl,
     byte_random32Clause⟩,
    kemGuardedClause_of_law valid E (I.kemEncapsulate byteRng byteCrc)
      (fun pk rng => hK byteRng byteCrc pk rng) oracle rfl rfl⟩

/-- **`OracleOfGuarded` is inhabited at the real constants under the laws**, at the byte-stream
source, for any views that meet the two view laws. -/
theorem oracleOfGuarded_of_laws (dh : DhView) (kem : KemView)
    (hcodec : Tacenta.UnitLifecycleT1.DhCodecTotal) (hagree : Tacenta.UnitLifecycleT1.DhAgreeTotal)
    (hid : Tacenta.UnitLifecycleT1.DhIdentityTotal)
    (hseal : Tacenta.UnitLifecycleT1.AeadSealBounded)
    (hopen : Tacenta.UnitLifecycleT1.AeadOpenTotal)
    (hdecaps : Tacenta.UnitLifecycleT1.KemDecapsulateTotal)
    (hverify : Tacenta.UnitLifecycleT1.XeddsaVerifyTotal)
    (hsign : Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64)
    (hkem : Tacenta.UnitLifecycleIntegrationScreen.KemShape)
    (hdh : Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey)
    (hkv : Function.Injective kem.keyPair) :
    ∃ oracle : Model.Lifecycle.Oracle, OracleOfGuarded byteRng byteCrc dh kem byteTrace oracle := by
  obtain ⟨oracle, hshape, hguarded⟩ := oracleOfShape_of_oracleLaws InterpO.real (dhViewOf dh)
    (kemViewOf kem) ((oracleLaws_real_iff dh kem).mpr
      ⟨hcodec, hagree, hid, hseal, hopen, hdecaps, hverify, hsign, hkem, hdh, hkv⟩)
  exact ⟨oracle, (oracleOfGuarded_iff_shape byteRng byteCrc dh kem byteTrace oracle).mpr
    ⟨hshape, hguarded⟩⟩

/-- **`OracleOf` is inhabited at the real constants under the laws.** -/
theorem oracleOf_of_laws (dh : DhView) (kem : KemView)
    (hcodec : Tacenta.UnitLifecycleT1.DhCodecTotal) (hagree : Tacenta.UnitLifecycleT1.DhAgreeTotal)
    (hid : Tacenta.UnitLifecycleT1.DhIdentityTotal)
    (hseal : Tacenta.UnitLifecycleT1.AeadSealBounded)
    (hopen : Tacenta.UnitLifecycleT1.AeadOpenTotal)
    (hdecaps : Tacenta.UnitLifecycleT1.KemDecapsulateTotal)
    (hverify : Tacenta.UnitLifecycleT1.XeddsaVerifyTotal)
    (hsign : Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64)
    (hkem : Tacenta.UnitLifecycleIntegrationScreen.KemShape)
    (hdh : Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey)
    (hkv : Function.Injective kem.keyPair) :
    ∃ oracle : Model.Lifecycle.Oracle, OracleOf byteRng byteCrc dh kem byteTrace oracle :=
  (oracleOfGuarded_of_laws dh kem hcodec hagree hid hseal hopen hdecaps hverify hsign hkem hdh
    hkv).elim fun oracle h => ⟨oracle, h.toOracleOf⟩

/-- The laws at the joint interpretation. -/
theorem modelO_oracleLaws : OracleLaws InterpO.model dhM kemM :=
  ⟨modelO_DhCodec, modelO_DhAgree, modelO_DhIdentity, modelO_AeadSealBounded, modelO_AeadOpen,
    modelO_KemDecapsulate, modelO_XeddsaVerify, modelO_signLaw, modelO_kemLaw,
    modelO_dhViewInjective, modelO_kemViewInjective⟩

/-- **The laws hold together with #220's axiom base**, the DH codec and #234's key-generation law,
at one interpretation, with the byte-stream source. -/
theorem oracleLaws_hold_jointly :
    ∃ (I : InterpO) (dh : DhViewOf I.toInterp) (kem : KemViewOf I.toInterp),
      OracleLaws I dh kem ∧ AxiomBase I.toInterp byteRng ∧ DhCodecOfShape I.toInterp dh ∧
      GenerateFillsOnce64Shape I.toInterp :=
  ⟨InterpO.model, dhM, kemM, modelO_oracleLaws, modelO_axiomBase, modelO_dhCodecOf,
    modelO_generateLaw⟩

/-- **`OracleOf` as a whole, with the guarded KEM clause, at the joint interpretation.** Every
law and #220's axiom base hold there; the oracle meets the twelve clauses and the guarded clause at
the byte-stream source; it refuses an input of each primitive that can refuse (agreement, the
identity test, opening, decapsulation, verification, and KEM validity); agreement, the identity
test and KEM validity also accept one, and its KEM encapsulates at an accepted key. That opening,
decapsulation and verification accept is in `aead_clauses_in_model` and
`kem_sig_clauses_in_model`. The width of `usize` is either of the two. -/
theorem oracleOf_joint_model :
    (Usize.max = U32.max ∨ Usize.max = U64.max) ∧
      OracleLaws InterpO.model dhM kemM ∧ AxiomBase M byteRng ∧ DhCodecOfShape M dhM ∧
      GenerateFillsOnce64Shape M ∧
      OracleOfShape InterpO.model byteRng byteCrc dhM kemM byteTrace oracleM ∧
      KemGuardedClause (InterpO.model.kemEncapsulate byteRng byteCrc) byteTrace oracleM ∧
      oracleM.dhAgree (arrayOf zero32) (arrayOf zero32) = none ∧
      oracleM.dhAgree (arrayOf zero32) (arrayOf Tacenta.UnitOracleDh.one32) ≠ none ∧
      oracleM.identityValid (arrayOf zero32) = false ∧
      oracleM.identityValid (arrayOf Tacenta.UnitOracleDh.one32) = true ∧
      (∀ (k1 k2 : Array U8 32#usize) (iv : Array U8 16#usize) (ad : Slice U8),
        oracleM.aeadOpen (arrayOf k1) (arrayOf k2) (arrayOf iv) [] (sliceOf ad) = none) ∧
      (∀ k : Array U8 32#usize, oracleM.kemDecaps (arrayOf k) [] = none) ∧
      (∀ m : Slice U8, oracleM.sigVerify (arrayOf Tacenta.UnitOracleDh.one32) (sliceOf m)
        (arrayOf Tacenta.UnitOracleKemSig.zero64) = false) ∧
      oracleM.kemValid (sliceOf key1568) = true ∧ oracleM.kemValid [] = false ∧
      (∀ draw, ∃ r, oracleM.kemEncaps (sliceOf key1568) draw = some r) := by
  obtain ⟨hdPub, hdAgree, hdId, _, _, hdSelf, hdOne, hdIdZero, hdIdOne⟩ :=
    Tacenta.UnitOracleDh.dh_clauses_in_model
  obtain ⟨haSeal, haOpen, _, haNil⟩ := Tacenta.UnitOracleAead.aead_clauses_in_model
  obtain ⟨hkDec, hsVer, hkG, hkValid, hkInvalid, hkEnc, _, hkDecNil, _, hsRefuse⟩ :=
    Tacenta.UnitOracleKemSig.kem_sig_clauses_in_model
  refine ⟨Usize.bounds_eq, modelO_oracleLaws, modelO_axiomBase, modelO_dhCodecOf,
    modelO_generateLaw, ?_, hkG, hdSelf zero32, by rw [hdOne]; simp, hdIdZero, hdIdOne, haNil,
    hkDecNil, hsRefuse, hkValid, hkInvalid, hkEnc⟩
  exact (oracleOfShape_iff_clauses InterpO.model byteRng byteCrc dhM kemM byteTrace oracleM).mpr
    ⟨hdPub, hdAgree, hdId, haSeal, haOpen,
     kemClauses_of_law kemModelValid kemModelE (InterpO.model.kemEncapsulate byteRng byteCrc)
       (fun _ _ => rfl) oracleM rfl rfl,
     hkDec, hsVer,
     sigSignClause_of_law signS (InterpO.model.xeddsaSign byteRng byteCrc)
       (fun _ _ _ => rfl) oracleM rfl,
     byte_random32Clause⟩

/-- The same, as an existence statement: some interpretation meets the laws and #220's axiom base,
and some oracle meets `OracleOf`'s twelve clauses and the guarded KEM clause there. -/
theorem oracleOf_inhabited_jointly :
    ∃ (I : InterpO) (dh : DhViewOf I.toInterp) (kem : KemViewOf I.toInterp)
      (oracle : Model.Lifecycle.Oracle),
      OracleLaws I dh kem ∧ AxiomBase I.toInterp byteRng ∧ DhCodecOfShape I.toInterp dh ∧
      GenerateFillsOnce64Shape I.toInterp ∧
      OracleOfShape I byteRng byteCrc dh kem byteTrace oracle ∧
      KemGuardedClause (I.kemEncapsulate byteRng byteCrc) byteTrace oracle := by
  obtain ⟨_, hl, hb, hc, hg, hs, hk, _⟩ := oracleOf_joint_model
  exact ⟨InterpO.model, dhM, kemM, oracleM, hl, hb, hc, hg, hs, hk⟩

end Tacenta.UnitOracleJoint

/-! ## Pins

The axiom list and the statement of each result, held by the build. `attest.py` requires them
(`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`). -/

/--
info: 'Tacenta.UnitOracleJoint.oracleLaws_real_iff' depends on axioms: [propext,
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
 tacenta_boundary.xeddsa.sign,
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
#print axioms Tacenta.UnitOracleJoint.oracleLaws_real_iff

/--
info: Tacenta.UnitOracleJoint.oracleLaws_real_iff : ∀ (dh : DhView) (kem : KemView),
  Tacenta.UnitOracleJoint.OracleLaws InterpO.real (dhViewOf dh) (kemViewOf kem) ↔
    Tacenta.UnitLifecycleT1.DhCodecTotal ∧
      Tacenta.UnitLifecycleT1.DhAgreeTotal ∧
        Tacenta.UnitLifecycleT1.DhIdentityTotal ∧
          Tacenta.UnitLifecycleT1.AeadSealBounded ∧
            Tacenta.UnitLifecycleT1.AeadOpenTotal ∧
              Tacenta.UnitLifecycleT1.KemDecapsulateTotal ∧
                Tacenta.UnitLifecycleT1.XeddsaVerifyTotal ∧
                  Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64 ∧
                    Tacenta.UnitLifecycleIntegrationScreen.KemShape ∧
                      (Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey) ∧
                        Function.Injective kem.keyPair
-/
#guard_msgs in
#check @Tacenta.UnitOracleJoint.oracleLaws_real_iff

/--
info: 'Tacenta.UnitOracleJoint.oracleOfShape_of_oracleLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleJoint.oracleOfShape_of_oracleLaws

/--
info: Tacenta.UnitOracleJoint.oracleOfShape_of_oracleLaws : ∀ (I : InterpO) (dh : DhViewOf I.toInterp)
  (kem : KemViewOf I.toInterp),
  Tacenta.UnitOracleJoint.OracleLaws I dh kem →
    ∃ oracle,
      OracleOfShape I Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh
          kem Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle ∧
        KemGuardedClause
          (I.kemEncapsulate Tacenta.UnitLifecycleIntegrationScreen.byteRng
            Tacenta.UnitLifecycleIntegrationScreen.byteCrc)
          Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle
-/
#guard_msgs in
#check @Tacenta.UnitOracleJoint.oracleOfShape_of_oracleLaws

/--
info: 'Tacenta.UnitOracleJoint.oracleOfGuarded_of_laws' depends on axioms: [propext,
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
 tacenta_boundary.xeddsa.sign,
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
#print axioms Tacenta.UnitOracleJoint.oracleOfGuarded_of_laws

/--
info: Tacenta.UnitOracleJoint.oracleOfGuarded_of_laws : ∀ (dh : DhView) (kem : KemView),
  Tacenta.UnitLifecycleT1.DhCodecTotal →
    Tacenta.UnitLifecycleT1.DhAgreeTotal →
      Tacenta.UnitLifecycleT1.DhIdentityTotal →
        Tacenta.UnitLifecycleT1.AeadSealBounded →
          Tacenta.UnitLifecycleT1.AeadOpenTotal →
            Tacenta.UnitLifecycleT1.KemDecapsulateTotal →
              Tacenta.UnitLifecycleT1.XeddsaVerifyTotal →
                Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64 →
                  Tacenta.UnitLifecycleIntegrationScreen.KemShape →
                    Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey →
                      Function.Injective kem.keyPair →
                        ∃ oracle,
                          OracleOfGuarded Tacenta.UnitLifecycleIntegrationScreen.byteRng
                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh kem
                            Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle
-/
#guard_msgs in
#check @Tacenta.UnitOracleJoint.oracleOfGuarded_of_laws

/--
info: 'Tacenta.UnitOracleJoint.oracleOf_of_laws' depends on axioms: [propext,
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
 tacenta_boundary.xeddsa.sign,
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
#print axioms Tacenta.UnitOracleJoint.oracleOf_of_laws

/--
info: Tacenta.UnitOracleJoint.oracleOf_of_laws : ∀ (dh : DhView) (kem : KemView),
  Tacenta.UnitLifecycleT1.DhCodecTotal →
    Tacenta.UnitLifecycleT1.DhAgreeTotal →
      Tacenta.UnitLifecycleT1.DhIdentityTotal →
        Tacenta.UnitLifecycleT1.AeadSealBounded →
          Tacenta.UnitLifecycleT1.AeadOpenTotal →
            Tacenta.UnitLifecycleT1.KemDecapsulateTotal →
              Tacenta.UnitLifecycleT1.XeddsaVerifyTotal →
                Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64 →
                  Tacenta.UnitLifecycleIntegrationScreen.KemShape →
                    Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey →
                      Function.Injective kem.keyPair →
                        ∃ oracle,
                          OracleOf Tacenta.UnitLifecycleIntegrationScreen.byteRng
                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh kem
                            Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle
-/
#guard_msgs in
#check @Tacenta.UnitOracleJoint.oracleOf_of_laws

/--
info: 'Tacenta.UnitOracleJoint.oracleLaws_hold_jointly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleJoint.oracleLaws_hold_jointly

/--
info: Tacenta.UnitOracleJoint.oracleLaws_hold_jointly : ∃ I dh kem,
  Tacenta.UnitOracleJoint.OracleLaws I dh kem ∧
    Tacenta.UnitSatisfiabilityRecords.AxiomBase I.toInterp Tacenta.UnitLifecycleIntegrationScreen.byteRng ∧
      DhCodecOfShape I.toInterp dh ∧ GenerateFillsOnce64Shape I.toInterp
-/
#guard_msgs in
#check @Tacenta.UnitOracleJoint.oracleLaws_hold_jointly

/--
info: 'Tacenta.UnitOracleJoint.oracleOf_joint_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleJoint.oracleOf_joint_model

/--
info: Tacenta.UnitOracleJoint.oracleOf_joint_model : (Usize.max = U32.max ∨ Usize.max = U64.max) ∧
  Tacenta.UnitOracleJoint.OracleLaws InterpO.model dhM kemM ∧
    Tacenta.UnitSatisfiabilityRecords.AxiomBase M Tacenta.UnitLifecycleIntegrationScreen.byteRng ∧
      DhCodecOfShape M dhM ∧
        GenerateFillsOnce64Shape M ∧
          OracleOfShape InterpO.model Tacenta.UnitLifecycleIntegrationScreen.byteRng
              Tacenta.UnitLifecycleIntegrationScreen.byteCrc dhM kemM Tacenta.UnitLifecycleIntegrationScreen.byteTrace
              oracleM ∧
            KemGuardedClause
                (InterpO.model.kemEncapsulate Tacenta.UnitLifecycleIntegrationScreen.byteRng
                  Tacenta.UnitLifecycleIntegrationScreen.byteCrc)
                Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracleM ∧
              oracleM.dhAgree (arrayOf zero32) (arrayOf zero32) = none ∧
                oracleM.dhAgree (arrayOf zero32) (arrayOf Tacenta.UnitOracleDh.one32) ≠ none ∧
                  oracleM.identityValid (arrayOf zero32) = false ∧
                    oracleM.identityValid (arrayOf Tacenta.UnitOracleDh.one32) = true ∧
                      (∀ (k1 k2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize) (ad : Slice U8),
                          oracleM.aeadOpen (arrayOf k1) (arrayOf k2) (arrayOf iv) [] (sliceOf ad) = none) ∧
                        (∀ (k : Std.Array U8 32#usize), oracleM.kemDecaps (arrayOf k) [] = none) ∧
                          (∀ (m : Slice U8),
                              oracleM.sigVerify (arrayOf Tacenta.UnitOracleDh.one32) (sliceOf m)
                                  (arrayOf Tacenta.UnitOracleKemSig.zero64) =
                                false) ∧
                            oracleM.kemValid (sliceOf key1568) = true ∧
                              oracleM.kemValid [] = false ∧
                                ∀ (draw : Model.Lifecycle.Key), ∃ r, oracleM.kemEncaps (sliceOf key1568) draw = some r
-/
#guard_msgs in
#check @Tacenta.UnitOracleJoint.oracleOf_joint_model

/--
info: 'Tacenta.UnitOracleJoint.oracleOf_inhabited_jointly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleJoint.oracleOf_inhabited_jointly

/--
info: Tacenta.UnitOracleJoint.oracleOf_inhabited_jointly : ∃ I dh kem oracle,
  Tacenta.UnitOracleJoint.OracleLaws I dh kem ∧
    Tacenta.UnitSatisfiabilityRecords.AxiomBase I.toInterp Tacenta.UnitLifecycleIntegrationScreen.byteRng ∧
      DhCodecOfShape I.toInterp dh ∧
        GenerateFillsOnce64Shape I.toInterp ∧
          OracleOfShape I Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
              dh kem Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle ∧
            KemGuardedClause
              (I.kemEncapsulate Tacenta.UnitLifecycleIntegrationScreen.byteRng
                Tacenta.UnitLifecycleIntegrationScreen.byteCrc)
              Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle
-/
#guard_msgs in
#check @Tacenta.UnitOracleJoint.oracleOf_inhabited_jointly

/--
info: structure Tacenta.UnitOracleJoint.OracleLaws (I : InterpO) (dh : DhViewOf I.toInterp) (kem : KemViewOf I.toInterp) :
  Prop
number of parameters: 3
fields:
  Tacenta.UnitOracleJoint.OracleLaws.dhCodec : Tacenta.UnitSatisfiabilityJoint.DhCodecShape I.toInterp
  Tacenta.UnitOracleJoint.OracleLaws.dhAgree : Tacenta.UnitSatisfiabilityJoint.DhAgreeShape I.toInterp
  Tacenta.UnitOracleJoint.OracleLaws.dhIdentity : Tacenta.UnitSatisfiabilityJoint.DhIdentityShape I.toInterp
  Tacenta.UnitOracleJoint.OracleLaws.aeadSeal : Tacenta.UnitSatisfiabilityJoint.AeadSealBoundedShape I.toInterp
  Tacenta.UnitOracleJoint.OracleLaws.aeadOpen : Tacenta.UnitSatisfiabilityJoint.AeadOpenShape I.toInterp
  Tacenta.UnitOracleJoint.OracleLaws.kemDecapsulate : Tacenta.UnitSatisfiabilityJoint.KemDecapsulateShape I.toInterp
  Tacenta.UnitOracleJoint.OracleLaws.xeddsaVerify : Tacenta.UnitSatisfiabilityJoint.XeddsaVerifyShape I.toInterp
  Tacenta.UnitOracleJoint.OracleLaws.signLaw : Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64Of fun {R} =>
      I.xeddsaSign
  Tacenta.UnitOracleJoint.OracleLaws.kemLaw : Tacenta.UnitLifecycleIntegrationScreen.KemShapeOf fun {R} =>
      I.kemEncapsulate
  Tacenta.UnitOracleJoint.OracleLaws.dhView : DhViewInjective dh
  Tacenta.UnitOracleJoint.OracleLaws.kemView : KemViewInjective kem
constructor:
  Tacenta.UnitOracleJoint.OracleLaws.mk {I : InterpO} {dh : DhViewOf I.toInterp} {kem : KemViewOf I.toInterp}
    (dhCodec : Tacenta.UnitSatisfiabilityJoint.DhCodecShape I.toInterp)
    (dhAgree : Tacenta.UnitSatisfiabilityJoint.DhAgreeShape I.toInterp)
    (dhIdentity : Tacenta.UnitSatisfiabilityJoint.DhIdentityShape I.toInterp)
    (aeadSeal : Tacenta.UnitSatisfiabilityJoint.AeadSealBoundedShape I.toInterp)
    (aeadOpen : Tacenta.UnitSatisfiabilityJoint.AeadOpenShape I.toInterp)
    (kemDecapsulate : Tacenta.UnitSatisfiabilityJoint.KemDecapsulateShape I.toInterp)
    (xeddsaVerify : Tacenta.UnitSatisfiabilityJoint.XeddsaVerifyShape I.toInterp)
    (signLaw : Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64Of fun {R} => I.xeddsaSign)
    (kemLaw : Tacenta.UnitLifecycleIntegrationScreen.KemShapeOf fun {R} => I.kemEncapsulate)
    (dhView : DhViewInjective dh) (kemView : KemViewInjective kem) : Tacenta.UnitOracleJoint.OracleLaws I dh kem
-/
#guard_msgs in
#print Tacenta.UnitOracleJoint.OracleLaws

/--
info: def Tacenta.UnitLifecycleT1.DhCodecTotal : Prop :=
(∀ (a : Std.Array U8 32#usize), Tacenta.UnitLifecycleT1.NoPanic (tacenta_boundary.dh.PrivateKey.from_bytes a)) ∧
  (∀ (k : tacenta_boundary.dh.PrivateKey), Tacenta.UnitLifecycleT1.NoPanic k.public_key) ∧
    (∀ (k : tacenta_boundary.dh.PrivateKey), Tacenta.UnitLifecycleT1.NoPanic k.to_bytes) ∧
      (∀ (a : Std.Array U8 32#usize),
          Tacenta.UnitLifecycleT1.NoPanic (tacenta_boundary.dh.PublicKeyBytes.from_bytes a)) ∧
        (∀ (k : tacenta_boundary.dh.PublicKeyBytes), Tacenta.UnitLifecycleT1.NoPanic k.as_bytes) ∧
          ∀ (a b : tacenta_boundary.dh.PublicKeyBytes),
            Tacenta.UnitLifecycleT1.NoPanic
              (tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq a b)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleT1.DhCodecTotal

/--
info: def Tacenta.UnitLifecycleT1.DhAgreeTotal : Prop :=
∀ (k : tacenta_boundary.dh.PrivateKey) (p : tacenta_boundary.dh.PublicKeyBytes),
  Tacenta.UnitLifecycleT1.NoPanic (k.agree p)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleT1.DhAgreeTotal

/--
info: def Tacenta.UnitLifecycleT1.DhIdentityTotal : Prop :=
∀ (k : tacenta_boundary.dh.PublicKeyBytes),
  Tacenta.UnitLifecycleT1.NoPanic (tacenta_boundary.dh.is_prime_order_public k)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleT1.DhIdentityTotal

/--
info: def Tacenta.UnitLifecycleT1.AeadSealBounded : Prop :=
∀ (ek mk : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize) (plaintext ad : Slice U8),
  ∃ r, tacenta_boundary.aead.encrypt ek mk iv plaintext ad = ok r ∧ (↑r).length ≤ (↑plaintext).length + 48
-/
#guard_msgs in
#print Tacenta.UnitLifecycleT1.AeadSealBounded

/--
info: def Tacenta.UnitLifecycleT1.AeadOpenTotal : Prop :=
∀ (ek mk : Std.Array U8 32#usize) (nonce : Std.Array U8 16#usize) (ciphertext ad : Slice U8),
  Tacenta.UnitLifecycleT1.NoPanic (tacenta_boundary.aead.decrypt ek mk nonce ciphertext ad)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleT1.AeadOpenTotal

/--
info: def Tacenta.UnitLifecycleT1.KemDecapsulateTotal : Prop :=
∀ (keyPair : tacenta_boundary.kem.KeyPair) (ciphertext : Slice U8),
  Tacenta.UnitLifecycleT1.NoPanic (tacenta_boundary.kem.decapsulate keyPair ciphertext)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleT1.KemDecapsulateTotal

/--
info: def Tacenta.UnitLifecycleT1.XeddsaVerifyTotal : Prop :=
∀ (publicKey : tacenta_boundary.dh.PublicKeyBytes) (message : Slice U8) (signature : Std.Array U8 64#usize),
  Tacenta.UnitLifecycleT1.NoPanic (tacenta_boundary.xeddsa.verify publicKey message signature)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleT1.XeddsaVerifyTotal

/--
info: def Tacenta.UnitSatisfiabilityJoint.DhCodecShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  (∀ (a : Std.Array U8 32#usize), Tacenta.UnitSatisfiabilityJoint.Np (I.dhPrivFromBytes a)) ∧
    (∀ (k : I.PrivateKey), Tacenta.UnitSatisfiabilityJoint.Np (I.dhPrivPublicKey k)) ∧
      (∀ (k : I.PrivateKey), Tacenta.UnitSatisfiabilityJoint.Np (I.dhPrivToBytes k)) ∧
        (∀ (a : Std.Array U8 32#usize), Tacenta.UnitSatisfiabilityJoint.Np (I.dhPubFromBytes a)) ∧
          (∀ (k : I.PublicKeyBytes), Tacenta.UnitSatisfiabilityJoint.Np (I.dhPubAsBytes k)) ∧
            ∀ (a b : I.PublicKeyBytes), Tacenta.UnitSatisfiabilityJoint.Np (I.dhPubEq a b)
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityJoint.DhCodecShape

/--
info: def Tacenta.UnitSatisfiabilityJoint.DhAgreeShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I => ∀ (k : I.PrivateKey) (p : I.PublicKeyBytes), Tacenta.UnitSatisfiabilityJoint.Np (I.dhPrivAgree k p)
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityJoint.DhAgreeShape

/--
info: def Tacenta.UnitSatisfiabilityJoint.DhIdentityShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I => ∀ (k : I.PublicKeyBytes), Tacenta.UnitSatisfiabilityJoint.Np (I.dhIsPrimeOrderPublic k)
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityJoint.DhIdentityShape

/--
info: def Tacenta.UnitSatisfiabilityJoint.AeadSealBoundedShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀ (ek mk : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize) (plaintext ad : Slice U8),
    ∃ r, I.aeadEncrypt ek mk iv plaintext ad = ok r ∧ (↑r).length ≤ (↑plaintext).length + 48
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityJoint.AeadSealBoundedShape

/--
info: def Tacenta.UnitSatisfiabilityJoint.AeadOpenShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀ (ek mk : Std.Array U8 32#usize) (n : Std.Array U8 16#usize) (c ad : Slice U8),
    Tacenta.UnitSatisfiabilityJoint.Np (I.aeadDecrypt ek mk n c ad)
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityJoint.AeadOpenShape

/--
info: def Tacenta.UnitSatisfiabilityJoint.KemDecapsulateShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I => ∀ (k : I.KemKeyPair) (c : Slice U8), Tacenta.UnitSatisfiabilityJoint.Np (I.kemDecapsulate k c)
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityJoint.KemDecapsulateShape

/--
info: def Tacenta.UnitSatisfiabilityJoint.XeddsaVerifyShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀ (p : I.PublicKeyBytes) (m : Slice U8) (s : Std.Array U8 64#usize),
    Tacenta.UnitSatisfiabilityJoint.Np (I.xeddsaVerify p m s)
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityJoint.XeddsaVerifyShape

/--
info: @[reducible] def Tacenta.UnitLifecycleT1.NoPanic : {α : Type} → Result α → Prop :=
fun {α} e => ∃ r, e = ok r
-/
#guard_msgs in
#print Tacenta.UnitLifecycleT1.NoPanic

/--
info: @[reducible] def Tacenta.UnitSatisfiabilityJoint.Np : {α : Type} → Result α → Prop :=
fun {α} e => ∃ r, e = ok r
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityJoint.Np
