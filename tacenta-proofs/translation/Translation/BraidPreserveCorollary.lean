import Translation.BraidPreserve
import Translation.BraidT3

/-!
# The receive theorems for a Braid a run reaches, without the `ct1_bounded` premise

`BraidT1.Braid.receive_no_panic` and `BraidT3.Braid.receive_refines` take
`State.ct1_bounded self.state` as a premise.  `BraidPreserve.lean` shows every Braid a run reaches
from the constructors (and from any Braids that have `sized`) has it.  These two corollaries put the
two together: for such a Braid the premise is a consequence of the run, and the rest of each
theorem is unchanged.  No hypothesis is added beyond the ones `BraidPreserve` takes
(`Laws`, the four KEM length constants, `Encapsulate1Total`).

The refinement corollary keeps every other premise of `receive_refines`, among them the epoch
headroom `epoch + 1 < u64::MAX`, the honest-chunk condition and the relation of the real state to a
model state, none of which a run supplies.
-/

open Aeneas Aeneas.Std Result
open tacenta_braid
open Tacenta.BraidT1
open Tacenta.BraidPreserveDecoder
open Tacenta.BraidPreserve

namespace Tacenta.BraidPreserveCorollary

/-- **`receive` cannot panic on a Braid a run reaches.** -/
theorem Braid.Run.receive_no_panic (hl : Laws) (hencaps1 : Encapsulate1Total)
    (hdnew : DecoderNewTotal) (hdadd : DecoderAddChunkTotal)
    (hdmsg : DecoderMessageTotal) (hct1len : Ct1LenTotal) (hct2len : Ct2LenTotal)
    (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal) (hekvec : KeyPairEkVectorTotal)
    (henew : EncoderNewTotal) (hdecap : KeyPairDecapsulateTotal) (hkdf : HkdfSha256Total)
    (hmac : HmacSha256Total) (hvalek : ValidateEkTotal) (hencaps2 : Encapsulate2Total)
    (henc : EncoderCloneTotal) (hdec : DecoderCloneTotal) (hkp : KeyPairCloneTotal)
    (hes : EncapsStateCloneTotal) (hopt : OptionCloneTotal)
    (hz : ZeroizingArrayRoundTrip) (hzz : ArrayZeroizeTotal) (hrf : RangeFullIndexTotal)
    {Base : Braid → Prop} (hbase : ∀ b, Base b → Braid.sized b) {self : Braid}
    (hrun : Braid.Run Base self) (msg : Msg) :
    Braid.receive self msg ⦃ fun _result => True ⦄ :=
  Braid.receive_no_panic hdnew hdadd hdmsg hct1len hct2len hhdrlen hekveclen hekvec henew hdecap
    hkdf hmac hvalek hencaps2 henc hdec hkp hes hopt hz hzz hrf self msg
    (State.sized_ct1_bounded (Braid.Run.sized hl hct1len hct2len hhdrlen hekveclen hencaps1 hbase
      hrun))

/-- **`receive` refines `Model.Braid.receive` on a Braid a run reaches**, under the premises of
`BraidT3.Braid.receive_refines` other than `ct1_bounded`.  Beyond its own premises it takes `Laws`,
`Encapsulate1Total`, the run `hrun` with its base `hbase`, and `hekveclenB`, the `EkVectorLenTotal`
the T1 theorem takes: `receive_refines` states the vector's size through `KemLenAgrees` and does not
bound it. -/
theorem Braid.Run.receive_refines {K : Model.Braid.Kem} (hl : Laws) (hencaps1 : Encapsulate1Total)
    (hka : Tacenta.BraidT3.KemAgreesFor K) (hea : Tacenta.BraidT3.ErasureAgrees)
    (hmac : Tacenta.BraidT3.BraidHmacAgrees) (hkdf : Tacenta.BraidT3.BraidHkdfAgrees)
    (hlens : Tacenta.BraidT3.KemLenAgrees K) (hvalek : Tacenta.BraidT3.ValidateEkAgrees K)
    (hencaps2len : Encapsulate2Total)
    (hdadd : DecoderAddChunkTotal)
    (hdmsg : DecoderMessageTotal)
    (hct1lenB : Ct1LenTotal) (hct2lenB : Ct2LenTotal)
    (hheaderlenB : HeaderLenTotal) (hekveclenB : EkVectorLenTotal)
    (hkcl : Tacenta.BraidT3.KemCloneAgrees) (hecl : Tacenta.BraidT3.ErasureCloneAgrees)
    (henc : EncoderCloneTotal) (hdec : DecoderCloneTotal)
    (hkp : KeyPairCloneTotal) (hes : EncapsStateCloneTotal)
    (hopt : OptionCloneTotal)
    (hz : ZeroizingArrayRoundTrip) (hzz : ArrayZeroizeTotal)
    (hrf : RangeFullIndexTotal)
    {Base : Braid → Prop} (hbase : ∀ b, Base b → Braid.sized b) {self : Braid}
    (hrun : Braid.Run Base self) (msg : tacenta_braid.Msg)
    (hepoch : (State.epoch_val self.state).val + 1 < Std.U64.max)
    {model : Model.Braid.BraidState} {modelMsg : Model.Braid.Msg}
    (hrel : Tacenta.BraidT3.StateRefines K self.state model)
    (hmsg : Tacenta.BraidT3.MsgRefines msg modelMsg)
    (hhonest : Tacenta.BraidT3.HonestChunk model modelMsg) :
    Braid.receive self msg ⦃ fun result =>
      result.1.val = (Model.Braid.receive K model modelMsg).2.2.epoch - 1 ∧
      Tacenta.BraidT3.OptionOutputRefines result.2.1 (Model.Braid.receive K model modelMsg).2.1 ∧
      Tacenta.BraidT3.StateRefines K result.2.2.state (Model.Braid.receive K model modelMsg).2.2 ⦄ :=
  Tacenta.BraidT3.Braid.receive_refines hka hea hmac hkdf hlens hvalek hencaps2len hdadd hdmsg
    hct1lenB hct2lenB hheaderlenB hkcl hecl henc hdec hkp hes hopt hz hzz hrf self msg
    (State.sized_ct1_bounded (Braid.Run.sized hl hct1lenB hct2lenB hheaderlenB
      hekveclenB hencaps1 hbase hrun))
    hepoch hrel hmsg hhonest

end Tacenta.BraidPreserveCorollary

/-! ## Axiom pins

The axiom base of each result, held by the build. -/

/--
info: 'Tacenta.BraidPreserveCorollary.Braid.Run.receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
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
 tacenta_erasure.Decoder.add_chunk,
 tacenta_erasure.Decoder.message,
 tacenta_erasure.Decoder.new,
 tacenta_erasure.Encoder.new,
 tacenta_erasure.Encoder.next_chunk,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_erasure.Decoder.Insts.CoreCloneClone.clone,
 tacenta_erasure.Encoder.Insts.CoreCloneClone.clone,
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
#print axioms Tacenta.BraidPreserveCorollary.Braid.Run.receive_no_panic

/--
info: 'Tacenta.BraidPreserveCorollary.Braid.Run.receive_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
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
 tacenta_erasure.Decoder.add_chunk,
 tacenta_erasure.Decoder.message,
 tacenta_erasure.Decoder.new,
 tacenta_erasure.Encoder.new,
 tacenta_erasure.Encoder.next_chunk,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_erasure.Decoder.Insts.CoreCloneClone.clone,
 tacenta_erasure.Encoder.Insts.CoreCloneClone.clone,
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
#print axioms Tacenta.BraidPreserveCorollary.Braid.Run.receive_refines

/-! ## Statement pins

The axiom pins hold the constants a result depends on and not what it says.  These hold the
statements of the results below while they are present; no gate requires a statement pin to exist. -/

/--
info: Tacenta.BraidPreserveCorollary.Braid.Run.receive_no_panic (hl : Laws) (hencaps1 : Encapsulate1Total)
  (hdnew : DecoderNewTotal) (hdadd : DecoderAddChunkTotal) (hdmsg : DecoderMessageTotal) (hct1len : Ct1LenTotal)
  (hct2len : Ct2LenTotal) (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal) (hekvec : KeyPairEkVectorTotal)
  (henew : EncoderNewTotal) (hdecap : KeyPairDecapsulateTotal) (hkdf : HkdfSha256Total) (hmac : HmacSha256Total)
  (hvalek : ValidateEkTotal) (hencaps2 : Encapsulate2Total) (henc : EncoderCloneTotal) (hdec : DecoderCloneTotal)
  (hkp : KeyPairCloneTotal) (hes : EncapsStateCloneTotal) (hopt : OptionCloneTotal) (hz : ZeroizingArrayRoundTrip)
  (hzz : ArrayZeroizeTotal) (hrf : RangeFullIndexTotal) {Base : Braid → Prop}
  (hbase : ∀ (b : Braid), Base b → Braid.sized b) {self : Braid} (hrun : Braid.Run Base self) (msg : Msg) :
  self.receive msg ⦃ _result => True ⦄
-/
#guard_msgs in
#check Tacenta.BraidPreserveCorollary.Braid.Run.receive_no_panic

/--
info: Tacenta.BraidPreserveCorollary.Braid.Run.receive_refines {K : Model.Braid.Kem} (hl : Laws)
  (hencaps1 : Encapsulate1Total) (hka : Tacenta.BraidT3.KemAgreesFor K) (hea : Tacenta.BraidT3.ErasureAgrees)
  (hmac : Tacenta.BraidT3.BraidHmacAgrees) (hkdf : Tacenta.BraidT3.BraidHkdfAgrees)
  (hlens : Tacenta.BraidT3.KemLenAgrees K) (hvalek : Tacenta.BraidT3.ValidateEkAgrees K)
  (hencaps2len : Encapsulate2Total) (hdadd : DecoderAddChunkTotal) (hdmsg : DecoderMessageTotal)
  (hct1lenB : Ct1LenTotal) (hct2lenB : Ct2LenTotal) (hheaderlenB : HeaderLenTotal) (hekveclenB : EkVectorLenTotal)
  (hkcl : Tacenta.BraidT3.KemCloneAgrees) (hecl : Tacenta.BraidT3.ErasureCloneAgrees) (henc : EncoderCloneTotal)
  (hdec : DecoderCloneTotal) (hkp : KeyPairCloneTotal) (hes : EncapsStateCloneTotal) (hopt : OptionCloneTotal)
  (hz : ZeroizingArrayRoundTrip) (hzz : ArrayZeroizeTotal) (hrf : RangeFullIndexTotal) {Base : Braid → Prop}
  (hbase : ∀ (b : Braid), Base b → Braid.sized b) {self : Braid} (hrun : Braid.Run Base self) (msg : Msg)
  (hepoch : ↑(State.epoch_val self.state) + 1 < U64.max) {model : Model.Braid.BraidState} {modelMsg : Model.Braid.Msg}
  (hrel : Tacenta.BraidT3.StateRefines K self.state model) (hmsg : Tacenta.BraidT3.MsgRefines msg modelMsg)
  (hhonest : Tacenta.BraidT3.HonestChunk model modelMsg) :
  self.receive msg ⦃ result =>
    ↑result.1 = (Model.Braid.receive K model modelMsg).2.2.epoch - 1 ∧
      Tacenta.BraidT3.OptionOutputRefines result.2.1 (Model.Braid.receive K model modelMsg).2.1 ∧
        Tacenta.BraidT3.StateRefines K result.2.2.state (Model.Braid.receive K model modelMsg).2.2 ⦄
-/
#guard_msgs in
#check Tacenta.BraidPreserveCorollary.Braid.Run.receive_refines
