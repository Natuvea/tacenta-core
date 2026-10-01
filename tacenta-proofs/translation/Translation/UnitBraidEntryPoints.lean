import Translation.UnitSatisfiabilityErasureAgrees
import Translation.UnitSatisfiabilityBraidAgreements
import Translation.SessionBraidReceiveRepair

/-!
# The Braid entry points of the Session unit with five of the six defined-function hypotheses discharged

`Braid.send_refines` and `Braid.receive_refines` (`SessionUnitBraidT3.lean`) take six hypotheses
about translated functions: `ErasureAgrees`, `ErasureCloneAgrees`, `DecoderAddChunkTotal`,
`DecoderMessageTotal`, `EncoderCloneTotal` and `DecoderCloneTotal`.  The unit's erasure coder is
translated Rust, so each is a statement about definitions, and five of them are theorems:

* `ErasureCloneAgrees`: outright (`UnitSatisfiabilityErasureAgrees.erasureCloneAgrees`);
* `DecoderAddChunkTotal`, `EncoderCloneTotal`, `DecoderCloneTotal`: outright
  (`UnitSatisfiabilityErasure`);
* `DecoderMessageTotal`, in its bounded form: from the one law `TruncateTotal` (`Vec::truncate`
  returns), by `SessionBraidReceiveRepair.decoderMessageTotal_of_truncate`.

`ErasureAgrees` stays a hypothesis here.  Its encoder half is a theorem
(`UnitSatisfiabilityErasureAgrees.erasureAgrees_encoder`); its decoder half is not proved in this
tree without compiler-trust axioms.

`Braid.send_refines_given_erasure` and `Braid.receive_refines_given_erasure` restate the two entry
points with those hypotheses replaced: the send needs no law, the receive needs `TruncateTotal`.  They do not change any
statement of `SessionUnitBraidT3.lean`: each is a corollary of the entry point it restates, with
fewer premises.  What remains is what a model of the unit's opaque constants can satisfy (the
agreements and totality shapes, `UnitSatisfiabilityBraidAgreements.lean`), the one law, the
hypothesis `ErasureAgrees`, and the hypotheses about state and message
(`UnitSatisfiabilityBraidStates.lean`).
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit

namespace Tacenta.UnitBraidEntryPoints

open Tacenta.SessionUnitBraidT3

/-- Five of the six defined-function hypotheses of the two entry points are theorems, given the
one law `TruncateTotal`.  The sixth, `ErasureAgrees`, is not among them. -/
theorem defined_hypotheses_given_erasure (htr : Tacenta.SessionUnitErasureT1.TruncateTotal) :
    ErasureCloneAgrees ∧ Tacenta.SessionUnitBraidT1.DecoderAddChunkTotal ∧
    Tacenta.SessionUnitBraidT1.DecoderMessageTotal ∧ Tacenta.SessionUnitBraidT1.EncoderCloneTotal ∧
    Tacenta.SessionUnitBraidT1.DecoderCloneTotal :=
  ⟨Tacenta.UnitSatisfiabilityErasureAgrees.erasureCloneAgrees,
    Tacenta.UnitSatisfiabilityErasure.decoderAddChunk_total,
    Tacenta.SessionBraidReceiveRepair.decoderMessageTotal_of_truncate htr,
    Tacenta.UnitSatisfiabilityErasure.encoderClone_total,
    Tacenta.UnitSatisfiabilityErasure.decoderClone_total⟩

theorem Braid.receive_refines_given_erasure
    (htr : Tacenta.SessionUnitErasureT1.TruncateTotal)
    {K : Model.Braid.Kem} (hka : KemAgreesFor K) (hea : ErasureAgrees)
    (hmac : BraidHmacAgrees) (hkdf : BraidHkdfAgrees)
    (hlens : KemLenAgrees K) (hvalek : ValidateEkAgrees K)
    (hencaps2len : Tacenta.SessionUnitBraidT1.Encapsulate2Total)
    (hct1lenB : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2lenB : Tacenta.SessionUnitBraidT1.Ct2LenTotal)
    (hheaderlenB : Tacenta.SessionUnitBraidT1.HeaderLenTotal)
    (hkcl : KemCloneAgrees)
    (hkp : Tacenta.SessionUnitBraidT1.KeyPairCloneTotal)
    (hes : Tacenta.SessionUnitBraidT1.EncapsStateCloneTotal)
    (hopt : Tacenta.SessionUnitBraidT1.OptionCloneTotal)
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (hzz : Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal)
    (hrf : Tacenta.SessionUnitBraidT1.RangeFullIndexTotal)
    (self : tacenta_session_unit.tacenta_braid.Braid)
    (msg : tacenta_session_unit.tacenta_braid.Msg)
    (hct1b : Tacenta.SessionUnitBraidT1.State.ct1_bounded self.state)
    (hdb : Tacenta.SessionUnitBraidT1.State.decoders_bounded self.state)
    (hepoch : (Tacenta.SessionUnitBraidT1.State.epoch_val self.state).val + 1 < Std.U64.max)
    {model : Model.Braid.BraidState} {modelMsg : Model.Braid.Msg}
    (hrel : StateRefines K self.state model) (hmsg : MsgRefines msg modelMsg)
    (hhonest : HonestChunk model modelMsg) :
    tacenta_session_unit.tacenta_braid.Braid.receive self msg ⦃ fun (i, out, next) =>
      i.val = (Model.Braid.receive K model modelMsg).2.2.epoch - 1 ∧
      OptionOutputRefines out (Model.Braid.receive K model modelMsg).2.1 ∧
      StateRefines K next.state (Model.Braid.receive K model modelMsg).2.2 ⦄ := by
  obtain ⟨hecl, hdadd, hdmsg, henc, hdec⟩ := defined_hypotheses_given_erasure htr
  exact Braid.receive_refines hka hea hmac hkdf hlens hvalek hencaps2len hdadd hdmsg hct1lenB
    hct2lenB hheaderlenB hkcl hecl henc hdec hkp hes hopt hz hzz hrf self msg hct1b hdb hepoch
    hrel hmsg hhonest

theorem Braid.send_refines_given_erasure
    {K : Model.Braid.Kem} (hka : KemAgreesFor K) (hea : ErasureAgrees)
    (hmac : BraidHmacAgrees) (hkdf : BraidHkdfAgrees)
    (hhdr : Tacenta.SessionUnitBraidT1.KeyPairHeaderTotal)
    (hekv : Tacenta.SessionUnitBraidT1.KeyPairEkVectorTotal)
    (hct1len : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2len : Tacenta.SessionUnitBraidT1.Ct2LenTotal)
    (hkcl : KemCloneAgrees)
    (hkp : Tacenta.SessionUnitBraidT1.KeyPairCloneTotal)
    (hes : Tacenta.SessionUnitBraidT1.EncapsStateCloneTotal)
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (hzz : Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal)
    (hrf : Tacenta.SessionUnitBraidT1.RangeFullIndexTotal)
    {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
    (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
    (hrng : Tacenta.SessionUnitBraidT1.RngTotal rc)
    (self : tacenta_session_unit.tacenta_braid.Braid) (rng : R)
    {model : Model.Braid.BraidState} (hrel : StateRefines K self.state model)
    (hlive : EncodersLive model) :
    tacenta_session_unit.tacenta_braid.Braid.send rc crc self rng ⦃ fun ((msg, i, out, next), _) =>
      ∃ rand, (∀ modelMsg, (Model.Braid.send K rand model).1 = some modelMsg →
          MsgRefines msg modelMsg) ∧
        i.val = (Model.Braid.send K rand model).2.2.2.epoch - 1 ∧
        OptionOutputRefines out (Model.Braid.send K rand model).2.2.1 ∧
        StateRefines K next.state (Model.Braid.send K rand model).2.2.2 ⦄ := by
  exact Braid.send_refines hka hea hmac hkdf hhdr hekv hct1len hct2len hkcl
    Tacenta.UnitSatisfiabilityErasureAgrees.erasureCloneAgrees
    Tacenta.UnitSatisfiabilityErasure.encoderClone_total
    Tacenta.UnitSatisfiabilityErasure.decoderClone_total hkp hes
    hz hzz hrf rc crc hrng self rng hrel hlive

end Tacenta.UnitBraidEntryPoints

/--
info: 'Tacenta.UnitBraidEntryPoints.defined_hypotheses_given_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 alloc.vec.Vec.truncate]
-/
#guard_msgs in
#print axioms Tacenta.UnitBraidEntryPoints.defined_hypotheses_given_erasure

/--
info: 'Tacenta.UnitBraidEntryPoints.Braid.receive_refines_given_erasure' depends on axioms: [propext,
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
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitBraidEntryPoints.Braid.receive_refines_given_erasure

/--
info: 'Tacenta.UnitBraidEntryPoints.Braid.send_refines_given_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitBraidEntryPoints.Braid.send_refines_given_erasure

/--
info: Tacenta.UnitBraidEntryPoints.defined_hypotheses_given_erasure (htr : Tacenta.SessionUnitErasureT1.TruncateTotal) :
  Tacenta.SessionUnitBraidT3.ErasureCloneAgrees ∧
    Tacenta.SessionUnitBraidT1.DecoderAddChunkTotal ∧
      Tacenta.SessionUnitBraidT1.DecoderMessageTotal ∧
        Tacenta.SessionUnitBraidT1.EncoderCloneTotal ∧ Tacenta.SessionUnitBraidT1.DecoderCloneTotal
-/
#guard_msgs in
#check Tacenta.UnitBraidEntryPoints.defined_hypotheses_given_erasure

/--
info: Tacenta.UnitBraidEntryPoints.Braid.receive_refines_given_erasure (htr : Tacenta.SessionUnitErasureT1.TruncateTotal)
  {K : Model.Braid.Kem} (hka : Tacenta.SessionUnitBraidT3.KemAgreesFor K)
  (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees) (hmac : Tacenta.SessionUnitBraidT3.BraidHmacAgrees)
  (hkdf : Tacenta.SessionUnitBraidT3.BraidHkdfAgrees) (hlens : Tacenta.SessionUnitBraidT3.KemLenAgrees K)
  (hvalek : Tacenta.SessionUnitBraidT3.ValidateEkAgrees K) (hencaps2len : Tacenta.SessionUnitBraidT1.Encapsulate2Total)
  (hct1lenB : Tacenta.SessionUnitBraidT1.Ct1LenTotal) (hct2lenB : Tacenta.SessionUnitBraidT1.Ct2LenTotal)
  (hheaderlenB : Tacenta.SessionUnitBraidT1.HeaderLenTotal) (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees)
  (hkp : Tacenta.SessionUnitBraidT1.KeyPairCloneTotal) (hes : Tacenta.SessionUnitBraidT1.EncapsStateCloneTotal)
  (hopt : Tacenta.SessionUnitBraidT1.OptionCloneTotal) (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
  (hzz : Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal) (hrf : Tacenta.SessionUnitBraidT1.RangeFullIndexTotal)
  (self : tacenta_braid.Braid) (msg : tacenta_braid.Msg)
  (hct1b : Tacenta.SessionUnitBraidT1.State.ct1_bounded self.state)
  (hdb : Tacenta.SessionUnitBraidT1.State.decoders_bounded self.state)
  (hepoch : ↑(Tacenta.SessionUnitBraidT1.State.epoch_val self.state) + 1 < U64.max) {model : Model.Braid.BraidState}
  {modelMsg : Model.Braid.Msg} (hrel : Tacenta.SessionUnitBraidT3.StateRefines K self.state model)
  (hmsg : Tacenta.SessionUnitBraidT3.MsgRefines msg modelMsg)
  (hhonest : Tacenta.SessionUnitBraidT3.HonestChunk model modelMsg) :
  self.receive msg ⦃ x✝ =>
    match x✝ with
    | (i, out, next) =>
      ↑i = (Model.Braid.receive K model modelMsg).2.2.epoch - 1 ∧
        Tacenta.SessionUnitBraidT3.OptionOutputRefines out (Model.Braid.receive K model modelMsg).2.1 ∧
          Tacenta.SessionUnitBraidT3.StateRefines K next.state (Model.Braid.receive K model modelMsg).2.2 ⦄
-/
#guard_msgs in
#check Tacenta.UnitBraidEntryPoints.Braid.receive_refines_given_erasure

/--
info: Tacenta.UnitBraidEntryPoints.Braid.send_refines_given_erasure {K : Model.Braid.Kem}
  (hka : Tacenta.SessionUnitBraidT3.KemAgreesFor K) (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees)
  (hmac : Tacenta.SessionUnitBraidT3.BraidHmacAgrees) (hkdf : Tacenta.SessionUnitBraidT3.BraidHkdfAgrees)
  (hhdr : Tacenta.SessionUnitBraidT1.KeyPairHeaderTotal) (hekv : Tacenta.SessionUnitBraidT1.KeyPairEkVectorTotal)
  (hct1len : Tacenta.SessionUnitBraidT1.Ct1LenTotal) (hct2len : Tacenta.SessionUnitBraidT1.Ct2LenTotal)
  (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees) (hkp : Tacenta.SessionUnitBraidT1.KeyPairCloneTotal)
  (hes : Tacenta.SessionUnitBraidT1.EncapsStateCloneTotal) (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
  (hzz : Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal) (hrf : Tacenta.SessionUnitBraidT1.RangeFullIndexTotal) {R : Type}
  (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (hrng : Tacenta.SessionUnitBraidT1.RngTotal rc)
  (self : tacenta_braid.Braid) (rng : R) {model : Model.Braid.BraidState}
  (hrel : Tacenta.SessionUnitBraidT3.StateRefines K self.state model)
  (hlive : Tacenta.SessionUnitBraidT3.EncodersLive model) :
  tacenta_braid.Braid.send rc crc self rng ⦃ x✝ =>
    match x✝ with
    | ((msg, i, out, next), snd) =>
      ∃ rand,
        (∀ (modelMsg : Model.Braid.Msg),
            (Model.Braid.send K rand model).1 = some modelMsg → Tacenta.SessionUnitBraidT3.MsgRefines msg modelMsg) ∧
          ↑i = (Model.Braid.send K rand model).2.2.2.epoch - 1 ∧
            Tacenta.SessionUnitBraidT3.OptionOutputRefines out (Model.Braid.send K rand model).2.2.1 ∧
              Tacenta.SessionUnitBraidT3.StateRefines K next.state (Model.Braid.send K rand model).2.2.2 ⦄
-/
#guard_msgs in
#check Tacenta.UnitBraidEntryPoints.Braid.send_refines_given_erasure
