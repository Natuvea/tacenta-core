import Translation.UnitLifecycleDecryptRatchetT3
import Translation.UnitLifecycleTripleRefusalT3

/-!
# `decrypt_ratchet` refines the model's decrypt step on every path

`UnitLifecycleDecryptRatchetT3.decrypt_ratchet_refines` left one path open: a Triple receive refusal
whose reason is not a full skipped-key store (`TripleRefusalOpen`), because no theorem related such a
concrete refusal to the model's detailed refusal.  `UnitLifecycleTripleRefusalT3` now proves that
relation for one Triple receive (`triple_receive_refusal_refines`).  This module closes the open
case with it:

* `openRefusal_closes`: every refusal the loop theorem reduces to one Triple receive
  (`UnitLifecycleRetryLoopT3.OpenRefusal`) is a refined outcome, so `OpenRefusalCloses` holds under
  the agreements of the Triple receive;
* `receive_with_eviction_refines_complete`: the generated `receive_with_eviction` refines
  `Model.Lifecycle.receiveWithEviction`, a success or a refusal, with no case left open;
* `decrypt_ratchet_refines_complete`: the refinement of `decrypt_ratchet` without the disjunct,
  under exactly the hypotheses of `decrypt_ratchet_refines` (`DecryptRatchetRefinesCompleteStatement`).

No hypothesis is added: the Triple receive's agreements are fields of the records the decrypt theorem
already takes.  The theorems rest on the compiler-trusted constants `decrypt_ratchet_refines` rests
on, which their pins list.
-/

namespace Tacenta.UnitLifecycleDecryptRatchetCompleteT3

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3
open Tacenta.UnitLifecycleDecryptRatchetT3

/-! ## Statement -/

/-- The statement of `decrypt_ratchet_refines_complete`, as a proposition: the hypotheses of
`DecryptRatchetRefinesStatement`, and its conclusion without the open disjunct. -/
def DecryptRatchetRefinesCompleteStatement : Prop :=
  ∀ {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
    DecryptOracleOf rngCore cryptoRng dh trace oracle →
    DhCodecOf dh →
    Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
    ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
    DecryptRatchetAgreements oracle.braidKem →
    ∀ (real : lifecycle.Session) (model : Model.Lifecycle.Session)
      (message : Slice Std.U8) (rng : R),
      SessionRefines dh oracle.braidKem real model →
      Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real →
      trace rng = oracle.draws →
      DecryptRatchetRun view oracle trace real model message rng →
      ∃ output,
        lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng = ok output ∧
        StepRefines trace dh oracle.braidKem output
          (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))

/-! ## One Triple receive refusal, at the retry bounds -/

/-- A refusal of one Triple receive at related states, under the retry bounds, is the model's
detailed refusal under the public mapping.  `triple_receive_refusal_refines` applied to the bounds
record the retry loop keeps. -/
theorem concrete_receive_attempt_refusal_from_retry_bounds
    (tc : Tacenta.UnitLifecycleT1.TripleReceiveContracts)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hmac : Tacenta.SessionUnitT3.HmacAgrees)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hzr : Tacenta.SessionUnitT3.ZeroizingRoundTrips)
    (hz96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.SessionUnitSpqrT3.VecRetainAgrees)
    (hrm : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees)
    {state : tacenta_triple.State} {modelState : Model.Triple.State}
    (hstate : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      state modelState)
    (header : tacenta_triple.Header) (modelHeader : Model.State.Header)
    (hheader : Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr modelHeader)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (bounds : RetryReceiveBounds modelState header modelHeader output)
    (realReason : tacenta_triple.TripleError)
    (hcall : lifecycle.receive_attempt state header dhOutRecv dhOutSend newDhsPub output =
      ok (.Err realReason)) :
    ∃ modelReason, tripleReceiveRefusalOfReal realReason = some modelReason ∧
      Model.Triple.receiveDetailed modelState
          { dr := modelHeader, epoch := header.epoch.val, pqN := header.pq_n.val }
          (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
          (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
          (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
          (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) = .error modelReason := by
  have hpost := Tacenta.UnitLifecycleTripleRefusalT3.triple_receive_refusal_refines hmac hkdf hzr
    tc.ratchetRemove hz96 hz64 hret tc.vecRetain hrm tc.spqrZeroize tc.optionClone state
    modelState hstate header modelHeader hheader dhOutRecv dhOutSend newDhsPub output
    bounds.classicalMatch bounds.classicalStoreRoom bounds.classicalEvents bounds.sparseEpoch
    bounds.sparseChainsRoom bounds.sparseChainEpochs bounds.sparseSkippedEpochs
    bounds.sparseOutputEpoch bounds.sparseStoreRoom bounds.sparseMatch bounds.sparseCounters
  obtain ⟨result, hresult, hpost⟩ := Std.WP.spec_imp_exists hpost
  have hstateCall : tacenta_triple.State.receive state header dhOutRecv dhOutSend newDhsPub
      output = ok (.Err realReason) := by
    simpa [lifecycle.receive_attempt] using hcall
  rw [hstateCall] at hresult
  cases hresult
  exact hpost realReason rfl

/-! ## The open case closes -/

/-- **`OpenRefusalCloses` holds** under the agreements of the Triple receive: the reduced refusal of
`OpenRefusal` is the model's detailed refusal (`concrete_receive_attempt_refusal_from_retry_bounds`),
and `OpenRefusal` already says that the model's loop then returns that refusal. -/
theorem openRefusal_closes
    (tc : Tacenta.UnitLifecycleT1.TripleReceiveContracts)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hmac : Tacenta.SessionUnitT3.HmacAgrees)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hzr : Tacenta.SessionUnitT3.ZeroizingRoundTrips)
    (hz96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.SessionUnitSpqrT3.VecRetainAgrees)
    (hrm : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees) :
    OpenRefusalCloses := by
  intro header mh output dhOutRecv dhOutSend newDhsPub out res hheader hopen
  obtain ⟨reason, work, m, hout, -, hst, bounds, -, hcall, hres⟩ := hopen
  obtain ⟨modelReason, hmap, hdet⟩ := concrete_receive_attempt_refusal_from_retry_bounds tc
    hmac hkdf hzr hz96 hz64 hret hrm hst header mh hheader dhOutRecv dhOutSend newDhsPub output
    bounds reason hcall
  subst hout
  rw [hres modelReason hmap hdet]
  exact hmap

/-! ## `receive_with_eviction`, every outcome -/

/-- **`receive_with_eviction` refines `Model.Lifecycle.receiveWithEviction`**, with no case left
open: at related Triple states with the receive bounds and the store bounds, the generated function
returns, and its result is the model's (a success with related state and key, or a refusal whose
public mapping is the model's refusal).  `UnitLifecycleRetryLoopT3.receive_with_eviction_refines`
with its open case closed by `openRefusal_closes`. -/
theorem receive_with_eviction_refines_complete
    (tc : Tacenta.UnitLifecycleT1.TripleReceiveContracts)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hmac : Tacenta.SessionUnitT3.HmacAgrees)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hzr : Tacenta.SessionUnitT3.ZeroizingRoundTrips)
    (hz96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.SessionUnitSpqrT3.VecRetainAgrees)
    (hrm : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees)
    (composite : tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
    (hcomposite : CompositeRefines composite modelComposite)
    (header : tacenta_triple.Header) (mh : Model.State.Header)
    (hheader : Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr mh)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (state : tacenta_triple.State) (m : Model.Triple.State)
    (hstate : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs state m)
    (hroom : Tacenta.UnitLifecycleT1.ReceiveHeadroom state)
    (bounds : RetryReceiveBounds m header mh output)
    (hcstore : Model.Triple.classicalSkippedLength m + Model.State.maxSkippedStore ≤
      UScalar.cMax UScalarTy.Usize)
    (hpstore : Model.Triple.postQuantumSkippedLength m + Model.SparseRatchet.maxSkippedStore ≤
      UScalar.cMax UScalarTy.Usize) :
    ∃ out,
      lifecycle.receive_with_eviction state composite header dhOutRecv dhOutSend newDhsPub
        output = ok out ∧
      Tacenta.UnitLifecycleRetryLoopT3.OutcomeRefines out
        (Model.Lifecycle.receiveWithEviction m modelComposite
          { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
          (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
          (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
          (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
          (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf)) := by
  obtain ⟨out, hcall, hrel⟩ := Tacenta.UnitLifecycleRetryLoopT3.receive_with_eviction_refines tc
    hmac hkdf hzr hz96 hz64 hret hrm composite modelComposite hcomposite header mh hheader
    dhOutRecv dhOutSend newDhsPub output state m hstate hroom bounds hcstore hpstore
  refine ⟨out, hcall, ?_⟩
  rcases hrel with hrefines | hopen
  · exact hrefines
  · exact openRefusal_closes tc hmac hkdf hzr hz96 hz64 hret hrm _ _ _ _ _ _ _ _ hheader hopen

/-! ## `decrypt_ratchet`, every path -/

/-- **`decrypt_ratchet` refines `Model.Lifecycle.decryptRatchet`, with the eviction retry loop, on
every path.**  For every input that meets the hypotheses of `decrypt_ratchet_refines`, the
generated function returns, and its result, the session it leaves and the remaining trace refine
the model's step: the terminal guard, a decode refusal, either DH refusal, every Triple receive
refusal (from the first attempt or from a retry), an AEAD refusal and a success, with or without
eviction rounds. -/
theorem decrypt_ratchet_refines_complete {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (hrel : SessionRefines dh oracle.braidKem real model)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (htrace : trace rng = oracle.draws)
    (run : DecryptRatchetRun view oracle trace real model message rng) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  have hclose : OpenRefusalCloses := openRefusal_closes contracts.triple agreements.hmac
    agreements.hkdf agreements.zeroizing64 agreements.zeroizing96 agreements.zeroizingSparse64
    agreements.vecRetain agreements.removeSkipped
  obtain ⟨output, hcall, hstep⟩ := decrypt_ratchet_refines_or_open rngCore cryptoRng trace dh
    view oracle oracleOf codec contracts agreements real model message rng hrel headroom htrace run
  exact ⟨output, hcall, hstep.resolve_right (fun h => h.1 hclose)⟩

/-- The theorem has exactly the statement recorded in `DecryptRatchetRefinesCompleteStatement`. -/
theorem decrypt_ratchet_refines_complete_statement : DecryptRatchetRefinesCompleteStatement := by
  intro R rngCore cryptoRng trace dh view oracle oracleOf codec contracts inst agreements real
    model message rng hrel headroom htrace run
  exact decrypt_ratchet_refines_complete rngCore cryptoRng trace dh view oracle oracleOf codec
    contracts agreements real model message rng hrel headroom htrace run

end Tacenta.UnitLifecycleDecryptRatchetCompleteT3

/-! ## Pins -/

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetCompleteT3.concrete_receive_attempt_refusal_from_retry_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetCompleteT3.concrete_receive_attempt_refusal_from_retry_bounds

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetCompleteT3.openRefusal_closes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetCompleteT3.openRefusal_closes

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetCompleteT3.receive_with_eviction_refines_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetCompleteT3.receive_with_eviction_refines_complete

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
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
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete_statement' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
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
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete_statement

/--
info: Tacenta.UnitLifecycleDecryptRatchetCompleteT3.concrete_receive_attempt_refusal_from_retry_bounds : Tacenta.UnitLifecycleT1.TripleReceiveContracts →
  ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
    Tacenta.SessionUnitT3.HmacAgrees →
      Tacenta.SessionUnitT3.HkdfAgrees →
        Tacenta.SessionUnitT3.ZeroizingRoundTrips →
          Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96 →
            Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 →
              Tacenta.SessionUnitSpqrT3.VecRetainAgrees →
                Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees →
                  ∀ {state : tacenta_session_unit.tacenta_triple.State} {modelState : Model.Triple.State},
                    Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
                        Tacenta.SessionUnitTripleT3.spqrAbs state modelState →
                      ∀ (header : tacenta_session_unit.tacenta_triple.Header) (modelHeader : Model.State.Header),
                        Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr modelHeader →
                          ∀ (dhOutRecv dhOutSend newDhsPub : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
                            (output : Option tacenta_session_unit.tacenta_spqr.Output),
                            Tacenta.UnitLifecycleT3.RetryReceiveBounds modelState header modelHeader output →
                              ∀ (realReason : tacenta_session_unit.tacenta_triple.TripleError),
                                tacenta_session_unit.lifecycle.receive_attempt state header dhOutRecv dhOutSend
                                      newDhsPub output =
                                    Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err realReason) →
                                  ∃ modelReason,
                                    Tacenta.UnitLifecycleT3.tripleReceiveRefusalOfReal realReason = some modelReason ∧
                                      Model.Triple.receiveDetailed modelState
                                          { dr := modelHeader, epoch := ↑header.epoch, pqN := ↑header.pq_n }
                                          (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
                                          (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
                                          (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
                                          (Option.map Tacenta.SessionUnitTripleT3.spqrOutputOf output) =
                                        Except.error modelReason
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetCompleteT3.concrete_receive_attempt_refusal_from_retry_bounds

/--
info: Tacenta.UnitLifecycleDecryptRatchetCompleteT3.openRefusal_closes : Tacenta.UnitLifecycleT1.TripleReceiveContracts →
  ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
    Tacenta.SessionUnitT3.HmacAgrees →
      Tacenta.SessionUnitT3.HkdfAgrees →
        Tacenta.SessionUnitT3.ZeroizingRoundTrips →
          Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96 →
            Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 →
              Tacenta.SessionUnitSpqrT3.VecRetainAgrees →
                Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees →
                  Tacenta.UnitLifecycleDecryptRatchetT3.OpenRefusalCloses
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetCompleteT3.openRefusal_closes

/--
info: Tacenta.UnitLifecycleDecryptRatchetCompleteT3.receive_with_eviction_refines_complete : Tacenta.UnitLifecycleT1.TripleReceiveContracts →
  ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
    Tacenta.SessionUnitT3.HmacAgrees →
      Tacenta.SessionUnitT3.HkdfAgrees →
        Tacenta.SessionUnitT3.ZeroizingRoundTrips →
          Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96 →
            Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 →
              Tacenta.SessionUnitSpqrT3.VecRetainAgrees →
                Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees →
                  ∀ (composite : tacenta_session_unit.tacenta_wire.Composite)
                    (modelComposite : Model.CompositeHeader.Composite),
                    Tacenta.UnitLifecycleT3.CompositeRefines composite modelComposite →
                      ∀ (header : tacenta_session_unit.tacenta_triple.Header) (mh : Model.State.Header),
                        Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr mh →
                          ∀ (dhOutRecv dhOutSend newDhsPub : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
                            (output : Option tacenta_session_unit.tacenta_spqr.Output)
                            (state : tacenta_session_unit.tacenta_triple.State) (m : Model.Triple.State),
                            Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
                                Tacenta.SessionUnitTripleT3.spqrAbs state m →
                              Tacenta.UnitLifecycleT1.ReceiveHeadroom state →
                                Tacenta.UnitLifecycleT3.RetryReceiveBounds m header mh output →
                                  Model.Triple.classicalSkippedLength m + Model.State.maxSkippedStore ≤
                                      Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize →
                                    Model.Triple.postQuantumSkippedLength m + Model.SparseRatchet.maxSkippedStore ≤
                                        Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize →
                                      ∃ out,
                                        tacenta_session_unit.lifecycle.receive_with_eviction state composite header
                                              dhOutRecv dhOutSend newDhsPub output =
                                            Aeneas.Std.Result.ok out ∧
                                          Tacenta.UnitLifecycleRetryLoopT3.OutcomeRefines out
                                            (Model.Lifecycle.receiveWithEviction m modelComposite
                                              { dr := mh, epoch := ↑header.epoch, pqN := ↑header.pq_n }
                                              (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
                                              (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
                                              (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
                                              (Option.map Tacenta.SessionUnitTripleT3.spqrOutputOf output))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetCompleteT3.receive_with_eviction_refines_complete

/--
info: @Tacenta.UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete : ∀ {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
            ∀ (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session)
              (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
              Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem real model →
                Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real →
                  trace rng = oracle.draws →
                    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun view oracle trace real model message rng →
                      ∃ output,
                        tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
                            Aeneas.Std.Result.ok output ∧
                          Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                            (Model.Lifecycle.decryptRatchet view oracle model (Tacenta.UnitLifecycleT3.sliceOf message))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete

/--
info: @Tacenta.UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete_statement : Tacenta.UnitLifecycleDecryptRatchetCompleteT3.DecryptRatchetRefinesCompleteStatement
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete_statement

/--
info: def Tacenta.UnitLifecycleDecryptRatchetCompleteT3.DecryptRatchetRefinesCompleteStatement : Prop :=
∀ {R : Type} (rngCore : tacenta_session_unit.rand_core_1.RngCore R)
  (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
  (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
            ∀ (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session)
              (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
              Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem real model →
                Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real →
                  trace rng = oracle.draws →
                    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun view oracle trace real model message rng →
                      ∃ output,
                        tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
                            Aeneas.Std.Result.ok output ∧
                          Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                            (Model.Lifecycle.decryptRatchet view oracle model (Tacenta.UnitLifecycleT3.sliceOf message))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetCompleteT3.DecryptRatchetRefinesCompleteStatement

