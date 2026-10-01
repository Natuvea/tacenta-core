import Translation.UnitSatisfiabilityErasure
import Translation.UnitSatisfiabilityRatchet
import Translation.UnitSatisfiabilityJoint

/-!
# The four session contract records follow from an axiom base that has a model

`EncryptContracts`, `DecryptRatchetContracts`, `EstablishInitiatorContracts` and
`EstablishResponderContracts` (`UnitLifecyclePublicT1.lean`) are the hypotheses of the Session
unit's lifecycle theorems.  A theorem whose hypothesis nothing can satisfy is true and says
nothing.  This module shows the four records are not that, in the sense below.

## What is proved

* `AxiomBase I rc` is the axiom parts of the four records (their fields about opaque constants),
  the class `SessionUnitT1.DerivedKeysModel`, and `StdLaws I`, over an interpretation `I` of the
  unit's opaque constants.
* At the real constants, the base gives each record: `encrypt_contracts_of_axiom_base`,
  `decrypt_contracts_of_axiom_base`, `initiator_contracts_of_axiom_base`,
  `responder_contracts_of_axiom_base`, and all four with the class in `records_of_axiom_base`.
  The fields about translated functions (the erasure coder, the ratchets' helper functions, the
  key derivations) are proved from the base with `UnitSatisfiabilityErasure.lean` and
  `UnitSatisfiabilityRatchet.lean`.  The bounded `decoderMessage` is
  `SessionBraidReceiveRepair.decoderMessageTotal_of_truncate` applied to the truncate law.
* `axiom_base_satisfiable`: some interpretation, some `RngCore` satisfy the base
  (`UnitSatisfiabilityJoint.lean`'s model).

## The sense of "inhabited"

Every axiom of the unit that a record reaches is an uninterpreted constant.  The unit has 231 axioms
in all: 88 uninterpreted constants (49 reached by the records, 39 not) and 143 compiler-trust facts
about the byte length of format strings, none of which mentions an interpreted constant, so replacing
the 48 interpreted constants leaves them true.  The 49th reached axiom is the error type inside
`RngCore`, which no contract looks at and which is not interpreted.  `records_of_axiom_base` is a
theorem in the real environment, so, under the base, it holds for every assignment of the constants.
`axiom_base_satisfiable` exhibits an assignment, `Interp.model`, of the 48 interpreted constants,
under which the base holds.  So a derivation of `False` from a record at the real constants would, after the constants
are replaced by the model's terms, become a derivation of `False` from facts that hold in the
model.  That last step is an argument about derivations and not a theorem inside Lean.  Stating it
inside Lean would need a copy of every translated body over the model, each bound to the original
by `Iff.rfl` (`UnitSatisfiabilityJoint.decoderNewI` does this for one function).

## What it does not show

* It does not show that the real primitives satisfy any field of any record, or that the real
  standard-library and `zeroize` functions satisfy `StdLaws`.  The laws are assumptions of this result, recorded
  in `LIMITATIONS.md`.
* It does not cover the headroom records (`EncryptHeadroom`, `DecryptRatchetHeadroom`,
  `EstablishInitiatorHeadroom`, `EstablishResponderHeadroom`): a theorem is also vacuous if no input
  meets them.
* It does not change any record, and three of their fields (`SessionUnitSpqrT1.ZeroizeTotal`,
  `SessionUnitBraidT1.ArrayZeroizeTotal`, the `Vec::zeroize` conjunct of `VecRetainTotal`) stay
  stronger than the crate supports (`UnitSatisfiabilityZeroizeScope.lean`).
* `State.decoders_bounded` and `State.ct1_bounded` are not shown to be kept by a send or a receive.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit

namespace Tacenta.UnitSatisfiabilityRecords

open Tacenta.UnitSatisfiabilityJoint
open Tacenta.UnitLifecycleT1

/-! ## The laws at the real constants -/

/-- `StdLaws` at the real constants is exactly the five laws the proofs use: the three that
`UnitSatisfiabilityRatchet.lean` names, the recorded `TruncateTotal`, and `DivCeilValue`. -/
theorem stdLaws_real_iff :
    StdLaws Interp.real ↔
      Tacenta.UnitSatisfiabilityRatchet.LawPop ∧ Tacenta.UnitSatisfiabilityRatchet.LawAsMut ∧
      Tacenta.UnitSatisfiabilityRatchet.LawBlanketU32 ∧
      Tacenta.SessionUnitErasureT1.TruncateTotal ∧
      Tacenta.SessionUnitDecoderBound.DivCeilValue :=
  ⟨fun l => ⟨l.pop, l.asMut, l.blanketU32, l.truncate, l.divCeil⟩,
    fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-- The nine laws of the ratchet proofs, from the base at the real constants. -/
theorem ratchetLaws_of_base (l : StdLaws Interp.real)
    (vr : VecRetainAxiomShape Interp.real) (z : SpqrZeroizeShape Interp.real)
    (h : HkdfShape Interp.real) (za : ZeroizingArrayRoundTripShape Interp.real) :
    Tacenta.UnitSatisfiabilityRatchet.Laws where
  pop := l.pop
  asMut := l.asMut
  blanketU32 := l.blanketU32
  capacity := vr.1
  vecZeroize := vr.2
  arrayZeroize := z
  hkdf := h
  zeroizing96 := fun x => za 96#usize (Tacenta.UnitSatisfiabilityRatchet.arrInst 96#usize) x
  zeroizing64 := fun x => za 64#usize (Tacenta.UnitSatisfiabilityRatchet.arrInst 64#usize) x

/-! ## The defined parts, from the base -/

theorem encryptDefined_of_base {R : Type} {rc : rand_core_1.RngCore R}
    (a : EncryptAxiom Interp.real rc) (l : StdLaws Interp.real) : EncryptDefined :=
  let L := ratchetLaws_of_base l a.triple.vecRetain a.triple.zeroize a.triple.hkdf
    a.braid.zeroizingArray
  { braid := ⟨Tacenta.UnitSatisfiabilityErasure.encoderClone_total,
      Tacenta.UnitSatisfiabilityErasure.decoderClone_total,
      Tacenta.UnitSatisfiabilityErasure.encoderNew_of_divCeilValue l.divCeil,
      Tacenta.UnitSatisfiabilityErasure.encoderNextChunk_total⟩
    triple :=
      ⟨⟨Tacenta.UnitSatisfiabilityRatchet.setChainsLoopTotal L.arrayZeroize L.asMut L.pop,
          Tacenta.UnitSatisfiabilityRatchet.clearChainsLoop0Total L.arrayZeroize L.asMut L.pop,
          Tacenta.UnitSatisfiabilityRatchet.clearSkippedLoopTotal L.arrayZeroize L.pop⟩,
        Tacenta.UnitSatisfiabilityRatchet.kdfRkTotal L.hkdf L.zeroizing96,
        Tacenta.UnitSatisfiabilityRatchet.kdfCkTotal L.hkdf L.zeroizing64⟩ }

theorem decryptDefined_of_base {R : Type} {rc : rand_core_1.RngCore R}
    (a : DecryptAxiom Interp.real rc) (l : StdLaws Interp.real) : DecryptDefined :=
  let L := ratchetLaws_of_base l a.triple.vecRetain a.triple.spqrZeroize a.triple.hkdf
    a.braid.zeroizingArray
  { braid := ⟨Tacenta.UnitSatisfiabilityErasure.decoderNew_of_divCeilValue l.divCeil,
      Tacenta.UnitSatisfiabilityErasure.decoderAddChunk_total,
      Tacenta.SessionBraidReceiveRepair.decoderMessageTotal_of_truncate l.truncate,
      Tacenta.UnitSatisfiabilityErasure.encoderNew_of_divCeilValue l.divCeil,
      Tacenta.UnitSatisfiabilityErasure.encoderClone_total,
      Tacenta.UnitSatisfiabilityErasure.decoderClone_total⟩
    triple :=
      ⟨⟨Tacenta.UnitSatisfiabilityRatchet.setChainsLoopTotal L.arrayZeroize L.asMut L.pop,
          Tacenta.UnitSatisfiabilityRatchet.clearChainsLoop0Total L.arrayZeroize L.asMut L.pop,
          Tacenta.UnitSatisfiabilityRatchet.clearSkippedLoopTotal L.arrayZeroize L.pop⟩,
        Tacenta.UnitSatisfiabilityRatchet.kdfRkTotal L.hkdf L.zeroizing96,
        Tacenta.UnitSatisfiabilityRatchet.kdfCkTotal L.hkdf L.zeroizing64,
        Tacenta.UnitSatisfiabilityRatchet.ratchetRemoveSkippedAtTotal L.arrayZeroize
          L.blanketU32 L.pop,
        Tacenta.UnitSatisfiabilityRatchet.spqrRemoveSkippedAtTotal L.arrayZeroize L.pop⟩ }

/-! ## The four records from the base -/

/-- **`EncryptContracts` follows from its axiom part and `StdLaws`.**  25 fields: 18 axiom-level
fields from the base, 6 defined fields from the erasure and ratchet modules, and `vecRetain`, whose
first two conjuncts come from the base and whose three loop contracts from the ratchet module. -/
theorem encrypt_contracts_of_axiom_base {R : Type} (rc : rand_core_1.RngCore R)
    (a : EncryptAxiom Interp.real rc) (l : StdLaws Interp.real) : EncryptContracts rc :=
  encryptOfParts ⟨a, encryptDefined_of_base a l⟩

/-- **`DecryptRatchetContracts` follows from its axiom part and `StdLaws`.**  The bounded
`decoderMessage` comes from the truncate law. -/
theorem decrypt_contracts_of_axiom_base {R : Type} (rc : rand_core_1.RngCore R)
    (a : DecryptAxiom Interp.real rc) (l : StdLaws Interp.real) : DecryptRatchetContracts rc :=
  decryptOfParts ⟨a, decryptDefined_of_base a l⟩

/-- **`EstablishInitiatorContracts` follows from its axiom part alone.**  Its one defined field,
`KdfInitTotal`, is proved from the HKDF and wrapper fields the record already has, so no law in
`StdLaws` is used. -/
theorem initiator_contracts_of_axiom_base {R : Type} (rc : rand_core_1.RngCore R)
    (a : Nonempty (InitiatorAxiom Interp.real rc)) :
    Nonempty (EstablishInitiatorContracts rc) := by
  obtain ⟨a⟩ := a
  exact ⟨initiatorOfParts ⟨a, ⟨Tacenta.UnitSatisfiabilityRatchet.kdfInitTotal a.sessionHkdf
    (fun x => a.zeroizingArray 96#usize (Tacenta.UnitSatisfiabilityRatchet.arrInst 96#usize) x)⟩⟩⟩

/-- **`EstablishResponderContracts` follows from its axiom part and `StdLaws`.** -/
theorem responder_contracts_of_axiom_base {R : Type} (rc : rand_core_1.RngCore R)
    (a : Nonempty (ResponderAxiom Interp.real rc)) (l : StdLaws Interp.real) :
    Nonempty (EstablishResponderContracts rc) := by
  obtain ⟨a⟩ := a
  let L := ratchetLaws_of_base l a.decrypt.triple.vecRetain a.decrypt.triple.spqrZeroize
    a.decrypt.triple.hkdf a.decrypt.braid.zeroizingArray
  exact ⟨responderOfParts ⟨a, ⟨decryptDefined_of_base a.decrypt l,
    Tacenta.UnitSatisfiabilityRatchet.kdfInitTotal L.hkdf L.zeroizing96⟩⟩⟩

/-- The axiom base: the axiom parts of the four records, the derived-keys class and `StdLaws`,
over an interpretation `I` of the unit's opaque constants.  At `Interp.real` it is a statement
about the real constants and nothing else.

**Inhabited.**  The records are *inhabited* in this sense and no other.  Every axiom of the unit that
a record reaches is an uninterpreted constant (the unit also holds 143 compiler-trust facts
about format-string lengths, none of which mentions an interpreted constant).
`records_of_axiom_base` is a theorem in the real environment, so, under the base, it holds for every
assignment of the constants.  `axiom_base_satisfiable` exhibits an assignment under which the base
holds.  So a derivation of `False` from a record at the real constants would give,
after the constants are replaced by the model's terms, a derivation of `False` from facts that hold
in the model.  That last step is an argument about derivations, not a theorem inside Lean.  It does
not show that the real primitives satisfy the base, and it does not cover the headroom records. -/
structure AxiomBase (I : Interp) {R : Type} (rc : rand_core_1.RngCore R) : Prop where
  encrypt : EncryptAxiom I rc
  decrypt : DecryptAxiom I rc
  initiator : Nonempty (InitiatorAxiom I rc)
  responder : Nonempty (ResponderAxiom I rc)
  derivedKeys : Nonempty (ZeroizingModelShape I DerivedZ)
  laws : StdLaws I

/-- **The base at the real constants gives all four records and the derived-keys class**, the
hypotheses of `encrypt_no_panic`, `decrypt_no_panic`, `decrypt_ratchet_no_panic`,
`establish_initiator_for_no_panic` and `establish_responder_no_panic` apart from their headroom
records. -/
theorem records_of_axiom_base {R : Type} (rc : rand_core_1.RngCore R)
    (h : AxiomBase Interp.real rc) :
    EncryptContracts rc ∧ DecryptRatchetContracts rc ∧
    Nonempty (EstablishInitiatorContracts rc) ∧ Nonempty (EstablishResponderContracts rc) ∧
    Nonempty Tacenta.SessionUnitT1.DerivedKeysModel :=
  ⟨encrypt_contracts_of_axiom_base rc h.encrypt h.laws,
    decrypt_contracts_of_axiom_base rc h.decrypt h.laws,
    initiator_contracts_of_axiom_base rc h.initiator,
    responder_contracts_of_axiom_base rc h.responder h.laws,
    h.derivedKeys.elim fun s => ⟨s.toDerived⟩⟩

/-! ## The base has a model -/

/-- **The axiom base is satisfiable**: the joint model, with a concrete `RngCore`. -/
theorem axiom_base_satisfiable :
    ∃ (I : Interp) (R : Type) (rc : rand_core_1.RngCore R), AxiomBase I rc :=
  ⟨Interp.model, Unit, totalRngCore,
    { encrypt := model_encryptAxiom totalRngCore_total
      decrypt := model_decryptAxiom (random32_of_rngTotal totalRngCore_total)
      initiator := ⟨model_initiatorAxiom totalRngCore_total
        (random32_of_rngTotal totalRngCore_total)⟩
      responder := ⟨model_responderAxiom (random32_of_rngTotal totalRngCore_total)⟩
      derivedKeys := ⟨model_ZeroizingModel DerivedZ⟩
      laws := model_StdLaws }⟩

/-- The same interpretation satisfies the base for every `RngCore` whose operations return, so the
quantification over `rc` in the records is not met only by one convenient value. -/
theorem axiom_base_satisfiable_for_total_rng :
    ∃ I : Interp, ∀ {R : Type} (rc : rand_core_1.RngCore R), RngTotal rc → AxiomBase I rc :=
  ⟨Interp.model, fun _ h =>
    { encrypt := model_encryptAxiom h
      decrypt := model_decryptAxiom (random32_of_rngTotal h)
      initiator := ⟨model_initiatorAxiom h (random32_of_rngTotal h)⟩
      responder := ⟨model_responderAxiom (random32_of_rngTotal h)⟩
      derivedKeys := ⟨model_ZeroizingModel DerivedZ⟩
      laws := model_StdLaws }⟩

end Tacenta.UnitSatisfiabilityRecords

/-! ## Axiom pins

The axiom bases of the results above, held by the build.  A list names the constants that occur in
the statement of a result, and these are the 48 interpreted constants the records reach, plus the error
type inside `RngCore`; the proofs assume about them exactly the hypotheses in the statements
(`EncryptAxiom`, `StdLaws` and so on).  `axiom_base_satisfiable` and
`axiom_base_satisfiable_for_total_rng` are statements about an interpretation and list the standard
axioms and the error type only. -/

/--
info: 'Tacenta.UnitSatisfiabilityRecords.stdLaws_real_iff' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilityRecords.stdLaws_real_iff

/--
info: 'Tacenta.UnitSatisfiabilityRecords.ratchetLaws_of_base' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilityRecords.ratchetLaws_of_base

/--
info: 'Tacenta.UnitSatisfiabilityRecords.encrypt_contracts_of_axiom_base' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilityRecords.encrypt_contracts_of_axiom_base

/--
info: 'Tacenta.UnitSatisfiabilityRecords.decrypt_contracts_of_axiom_base' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilityRecords.decrypt_contracts_of_axiom_base

/--
info: 'Tacenta.UnitSatisfiabilityRecords.initiator_contracts_of_axiom_base' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilityRecords.initiator_contracts_of_axiom_base

/--
info: 'Tacenta.UnitSatisfiabilityRecords.responder_contracts_of_axiom_base' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilityRecords.responder_contracts_of_axiom_base

/--
info: 'Tacenta.UnitSatisfiabilityRecords.records_of_axiom_base' depends on axioms: [propext,
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
#print axioms Tacenta.UnitSatisfiabilityRecords.records_of_axiom_base

/--
info: 'Tacenta.UnitSatisfiabilityRecords.axiom_base_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityRecords.axiom_base_satisfiable

/--
info: 'Tacenta.UnitSatisfiabilityRecords.axiom_base_satisfiable_for_total_rng' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityRecords.axiom_base_satisfiable_for_total_rng

/-! ## Statement pins

The axiom pins above hold the constants a result depends on and not what it says.  These hold the
statements of the three results that the documents cite as the inhabitation of the four records. -/

/--
info: Tacenta.UnitSatisfiabilityRecords.axiom_base_satisfiable : ∃ I R rc, Tacenta.UnitSatisfiabilityRecords.AxiomBase I rc
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityRecords.axiom_base_satisfiable

/--
info: Tacenta.UnitSatisfiabilityRecords.axiom_base_satisfiable_for_total_rng :
  ∃ I,
    ∀ {R : Type} (rc : rand_core_1.RngCore R),
      Tacenta.UnitLifecycleT1.RngTotal rc → Tacenta.UnitSatisfiabilityRecords.AxiomBase I rc
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityRecords.axiom_base_satisfiable_for_total_rng

/--
info: Tacenta.UnitSatisfiabilityRecords.records_of_axiom_base {R : Type} (rc : rand_core_1.RngCore R)
  (h : Tacenta.UnitSatisfiabilityRecords.AxiomBase Tacenta.UnitSatisfiabilityJoint.Interp.real rc) :
  Tacenta.UnitLifecycleT1.EncryptContracts rc ∧
    Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc ∧
      Nonempty (Tacenta.UnitLifecycleT1.EstablishInitiatorContracts rc) ∧
        Nonempty (Tacenta.UnitLifecycleT1.EstablishResponderContracts rc) ∧
          Nonempty Tacenta.SessionUnitT1.DerivedKeysModel
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityRecords.records_of_axiom_base
