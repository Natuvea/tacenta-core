import Translation.UnitLifecycleImportBudget
import Translation.UnitLifecycleDecryptPreserve

/-!
# `Session::decrypt` refined and kept: the decrypt refinement composed with receive preservation

`UnitLifecycleDecryptPreserve` shows that a successful `decrypt_ratchet` or `decrypt` keeps `Session::invariant` and
spends at most one unit of the counter budget, given two hypotheses it does not discharge: the relation after the call
(`SessionRefines` at the session returned) and a model step (`ReceiveStep`).  The decrypt refinement
(`UnitLifecycleDecryptRunBounds.decrypt_ratchet_refines_of_invariant`) shows that `decrypt_ratchet` returns and
refines the model's `decryptRatchet`, refusals included.  This module composes the two, so that the relation after
the call comes from the refinement and the model step from the model's own `decryptRatchet` of a frame in the in-order
scope (`decryptRatchet_receiveStep`), and neither is a hypothesis any more.

## What it shows

* `FrameInOrder`: every header the frame decodes to is in the in-order scope with the agreement's output
  (`InOrderOut`) at the model session; the hypothesis `decryptRatchet_receiveStep` takes, named.
* `decrypt_ratchet_refines_keeps_invariant`: for every session that passes `Session::invariant`, has room for
  `k + 1` operations and refines a model session, and every frame in the in-order scope there, under the hypotheses of
  `decrypt_ratchet_refines_of_invariant` and `ReceiveInvariantLaws`, `decrypt_ratchet` returns, its result, session and
  draws refine the model's `decryptRatchet`, and the session it returns passes `Session::invariant` and has room for
  `k`, whether the call succeeds (`decrypt_ratchet_keeps_invariant`, with the relation and the step derived) or refuses
  (`decrypt_ratchet_err_keeps_invariant`).
* `decrypt_refines_keeps_invariant`: the same for the public `decrypt` of a frame whose type byte is the ratchet type:
  a frame over the size bound is refused with the session unchanged (`decrypt_frame_too_long_step_refines`); otherwise
  the public call refines the model's `decrypt` (`decrypt_ratchet_message_refines`), the model's dispatch passes the
  frame on (`dispatchDecrypt_passthrough`), and the step is the model's own `decrypt` (`decrypt_receiveStep`).
* `restored_decrypt_keeps_invariant`: the route from the bytes `import` accepted: for every byte string `import`
  accepts with a session in the restored scope (`RestoredScope`) whose counters pass `roomCheck s (k + 1)`, the public
  `decrypt` of a ratchet-type frame in the in-order scope at `restoredModelOf dh s` returns, refines the model's
  `decrypt` there, and leaves a session that passes the invariant and has room for `k`.  The invariant is acceptance's,
  the relation and `HonestChunk` the scope's, the budget the check's (`counterRoom_iff_roomCheck`); acceptance itself
  gives no budget (`UnitLifecycleImportBudget.acceptance_does_not_give_headroom`).

## The laws and premises

* No new law.  `ReceiveInvariantLaws` (eleven named fields, among them the assumed laws `KeyPairEkVectorLen` and
  `Encapsulate2Len`, register rows `PRESERVE-LAW-KEYPAIR-EK-VECTOR-LEN` and `PRESERVE-LAW-ENCAPSULATE2-LEN`), and the
  hypotheses of `decrypt_ratchet_refines_of_invariant`: `DecryptOracleOf`, `DhCodecOf`, `DecryptRatchetContracts`,
  `DerivedKeysModel`, `DecryptRatchetAgreements`, the trace equation and the run inputs (`DecryptRatchetRunInputs`:
  the chunk relation, `HonestChunk` and one draw).  The oracle's `dhPublic` clause the preservation step takes is
  `DecryptOracleOf.dhPublic`, so it is no longer a separate premise.
* `DecryptOracleOf`'s `aeadOpen` clause is, by reading, false of the shipping AEAD at long lengths (in a 64-bit build
  with overflow checks, and there only formally, at sizes no real address space supplies; row
  `AEAD-LENGTH-CONTRACTS`), so, as stated, each result here is conditional on a proposition that does not hold and
  says nothing about the shipping code at any length until that contract is repaired.
* `FrameInOrder` is a restriction of scope about the model session and the frame; it says nothing of the result.  The
  restored route adds `RestoredScope` (the Braid at `KeysUnsampled` or `Failed`) and the budget check.

## Non-vacuity

* The hypotheses of `decrypt_ratchet_refines_of_invariant` hold together at one witness session under named laws
  (`UnitLifecycleDecryptRunBounds.decrypt_of_invariant_hypotheses_jointly_satisfiable`); the two new laws of
  `ReceiveInvariantLaws` hold in `Interp.modelT3`.  No theorem shows the whole hypothesis set of the composed results
  jointly satisfiable with a successful receive, and no run here exhibits it; the reply's run reaches the same
  conclusion by another route (`UnitLifecycleDecryptPreserve.initiator_receives_reply_via_general`).
* The success branch has no witness.  The one joint witness of the refinement's hypotheses is at a frame whose
  composite carries the all-zero ratchet key, which the screen's oracle refuses
  (`UnitLifecycleDecryptRatchetScreen.sample_model_refuses`; whether the witness's own oracle refuses it is not
  checked), so the branch where the relation after the call and the model step are derived is exhibited by no
  witness.  A witness there needs, at one interpretation, the invariant at a session holding a receiving chain,
  `ReceiveInvariantLaws`, and `DecryptOracleOf` with an oracle whose agreement and AEAD open succeed on that frame.
  The oracle that meets `DecryptOracleOf` here is read off the opaque primitives (`decryptOracleOf_of_laws`), and no
  law states that they succeed on a given frame; the screen's successful run (`succReal`, `succMessage`) uses an
  oracle that meets the clauses in a model interpretation, not at the real constants.

## What it does not show

* A receive outside the in-order scope (a stored key, a skip on either chain, an eviction from a full store), so
  reordered, delayed or dropped delivery is not covered.
* An initial-type frame through the public `decrypt`: only ratchet-type frames are composed.
* A witness or run that exhibits the composed hypotheses with a successful receive (the success branch has no
  witness), or a receive with an agreement transition or an output on any run.
* That the shipping AEAD meets `DecryptOracleOf` (false by reading at long lengths), or that the shipping KEM and the
  other functions meet `ReceiveInvariantLaws`, the agreements and the contracts.
* A restored session outside the restored scope, or the budget of a restored session without the caller's check.
* That the ceilings are kept (false of the code, so the statements spend a budget).
-/

namespace Tacenta.UnitLifecycleDecryptCompose

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3 (DhView DhCodecOf SessionRefines StepRefines sliceOf PublicDecryptWitness
  decrypt_frame_too_long_step_refines decrypt_ratchet_message_refines message_type_refines_ratchet)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleDecryptRunBounds (CounterHeadroom DecryptRatchetRunInputs
  decrypt_ratchet_refines_of_invariant)
open Tacenta.UnitLifecycleSendPreserve (CounterRoom counterRoom_zero)
open Tacenta.UnitLifecycleEncryptPreserve (counterRoom_mono decrypt_ratchet_err_keeps_invariant
  decrypt_err_keeps_invariant)
open Tacenta.UnitLifecycleDecryptPreserve (ReceiveInvariantLaws InOrderOut decrypt_ratchet_keeps_invariant
  decryptRatchet_receiveStep decrypt_keeps_invariant decrypt_receiveStep)

/-- **The in-order scope of a frame at a model session**: every header the frame decodes to is in the in-order
scope with the agreement's output (`InOrderOut`) for the session's Triple, the agreement message being the one the
view reads off the frame.  A restriction about the model session and the frame only; the hypothesis
`decryptRatchet_receiveStep` takes. -/
def FrameInOrder (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (m : Model.Lifecycle.Session) (msg : Model.Lifecycle.Bytes) : Prop :=
  ∀ c ct, Model.CompositeHeader.decodeDetailed msg = .ok (c, ct) →
    InOrderOut m.triple (Model.Lifecycle.tripleHeaderOf c) (Model.Lifecycle.sparseOutputOf
      (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.1)

/-- **`Session::decrypt_ratchet` refines the model's step and keeps `Session::invariant` and the counter budget,
from one set of hypotheses**: for every session `s` that passes `Session::invariant`, has room for `k + 1`
operations and refines a model session `m`, and every frame in the in-order scope at `m` (`FrameInOrder`), under
the hypotheses of `decrypt_ratchet_refines_of_invariant` and `ReceiveInvariantLaws`, `decrypt_ratchet` returns, its
result, session and draws refine the model's `decryptRatchet`, and the session it returns passes
`Session::invariant` and has room for `k`, whether the call succeeds or refuses.  The relation after the call and
the model step are derived, not assumed: the relation from the refinement, the step from the model's own
`decryptRatchet` (`decryptRatchet_receiveStep`). -/
theorem decrypt_ratchet_refines_keeps_invariant (laws : ReceiveInvariantLaws) {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : R) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true)
    (hrel : SessionRefines dh oracle.braidKem s m)
    (hroom : CounterRoom s (k + 1))
    (htrace : trace rng = oracle.draws)
    (inputs : DecryptRatchetRunInputs view oracle trace s m message rng)
    (hord : FrameInOrder view oracle m (sliceOf message)) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng s message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decryptRatchet view oracle m (sliceOf message)) ∧
      lifecycle.Session.invariant output.2.1 = ok true ∧ CounterRoom output.2.1 k := by
  have hc : CounterHeadroom s := (counterRoom_zero s).mp (counterRoom_mono s (Nat.zero_le _) hroom)
  obtain ⟨⟨res, s', rng'⟩, hcall, hstep⟩ := decrypt_ratchet_refines_of_invariant rngCore cryptoRng trace dh
    view oracle oracleOf codec contracts agreements s m message rng hinv hrel hc htrace inputs
  refine ⟨_, hcall, hstep, ?_⟩
  rcases res with pt | e
  · exact decrypt_ratchet_keeps_invariant laws rngCore cryptoRng dh codec oracle.braidKem oracle
      oracleOf.dhPublic s m _ k hinv hroom hrel message rng pt s' rng' hcall hstep.session
      (decryptRatchet_receiveStep view oracle m (sliceOf message) hord)
  · obtain ⟨h1, h2⟩ := decrypt_ratchet_err_keeps_invariant rngCore cryptoRng s message rng e s' rng' hinv hcall
    exact ⟨h1, h2 k (counterRoom_mono s (Nat.le_succ k) hroom)⟩

/-- **The public `Session::decrypt` of a ratchet-type frame refines the model's `decrypt` and keeps
`Session::invariant` and the counter budget, from one set of hypotheses**: as
`decrypt_ratchet_refines_keeps_invariant`, for the public call on a frame whose type byte is the ratchet type.  A
frame over the size bound is refused with the session unchanged; otherwise the model's dispatch passes the frame on
(`dispatchDecrypt_passthrough`), and the step is the model's own `decrypt` (`decrypt_receiveStep`). -/
theorem decrypt_refines_keeps_invariant (laws : ReceiveInvariantLaws) {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : R) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true)
    (hrel : SessionRefines dh oracle.braidKem s m)
    (hroom : CounterRoom s (k + 1))
    (htype : serialization.message_type message = ok (some serialization.MessageType.Ratchet))
    (htrace : trace rng = oracle.draws)
    (inputs : DecryptRatchetRunInputs view oracle trace s m message rng)
    (hord : FrameInOrder view oracle m (sliceOf message)) :
    ∃ output,
      lifecycle.Session.decrypt rngCore cryptoRng s message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decrypt view oracle m (sliceOf message)) ∧
      lifecycle.Session.invariant output.2.1 = ok true ∧ CounterRoom output.2.1 k := by
  have hkeep : CounterRoom s k := counterRoom_mono s (Nat.le_succ k) hroom
  by_cases hlong : Model.Lifecycle.frameTooLong (sliceOf message) = true
  · obtain ⟨hreal, hstep⟩ := decrypt_frame_too_long_step_refines rngCore cryptoRng trace dh oracle.braidKem
      view oracle s m message rng hrel htrace hlong
    exact ⟨_, hreal, hstep, hinv, hkeep⟩
  have hsize : Model.Lifecycle.frameTooLong (sliceOf message) = false := by simpa using hlong
  obtain ⟨inner, hin, hstepIn, -⟩ := decrypt_ratchet_refines_keeps_invariant laws rngCore cryptoRng trace dh
    view oracle oracleOf codec contracts agreements s m message rng k hinv hrel hroom htrace inputs hord
  obtain ⟨⟨res, s', rng'⟩, hcall, hstep⟩ := decrypt_ratchet_message_refines rngCore cryptoRng trace dh
    oracle.braidKem view oracle s m message rng inner hsize htype hin hstepIn
  refine ⟨_, hcall, hstep, ?_⟩
  rcases res with pt | e
  · have hdisp : Model.Lifecycle.dispatchDecrypt oracle m (sliceOf message) = .ok (sliceOf message) :=
      Model.Lifecycle.dispatchDecrypt_passthrough oracle m _ hsize
        (by rw [message_type_refines_ratchet message htype]; simp)
    exact decrypt_keeps_invariant laws rngCore cryptoRng dh codec oracle.braidKem oracle oracleOf.dhPublic
      s m _ k hinv hroom hrel message rng pt s' rng' hcall hstep.session
      (decrypt_receiveStep view oracle m (sliceOf message) (sliceOf message) hdisp hord)
  · obtain ⟨h1, h2⟩ := decrypt_err_keeps_invariant rngCore cryptoRng s message rng e s' rng' hinv hcall
    exact ⟨h1, h2 k hkeep⟩

/-! ## From the bytes `import` accepted: the restored route -/

open Tacenta.UnitLifecycleRestoredSession (RestoredScope restoredModelOf import_ok_gives_invariant
  sessionRefines_restored honestChunk_restored)
open Tacenta.UnitLifecycleImportBudget (roomCheck counterRoom_iff_roomCheck)

/-- **From the bytes `Session::import` accepted to the next `Session::decrypt`, refined and kept**: for every byte
string `bytes` that `import` accepts with a session `s` in the restored scope (`RestoredScope`) whose counters pass
`roomCheck s (k + 1)`, and every ratchet-type frame in the in-order scope at `restoredModelOf dh s`, the public
`decrypt` returns, refines the model's `decrypt` at `restoredModelOf dh s`, and leaves a session that passes
`Session::invariant` and has room for `k`.  The invariant is acceptance's (`import_ok_gives_invariant`), the relation
the scope's (`sessionRefines_restored`), `HonestChunk` the scope's, and the budget the check's
(`counterRoom_iff_roomCheck`): `import` makes no such check, and acceptance gives no budget
(`UnitLifecycleImportBudget.acceptance_does_not_give_headroom`).  Under the hypotheses of
`decrypt_refines_keeps_invariant` that the restored route leaves the caller's. -/
theorem restored_decrypt_keeps_invariant (laws : ReceiveInvariantLaws) {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (bytes : Slice Std.U8) (s : lifecycle.Session) (k : Nat)
    (h : lifecycle.Session.import bytes = ok (core.result.Result.Ok s))
    (hscope : RestoredScope s) (hcheck : roomCheck s (k + 1) = true)
    (message : Slice Std.U8) (rng : R)
    (htype : serialization.message_type message = ok (some serialization.MessageType.Ratchet))
    (htrace : trace rng = oracle.draws)
    (hchunk : ∀ (realComposite : tacenta_wire.Composite)
      (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Model.Lifecycle.Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (modelComposite, ciphertext) →
      Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
      Tacenta.UnitLifecycleT3.IncomingChunkRefines view (restoredModelOf dh s).braid realComposite
        modelComposite)
    (hdraw : ∃ draw rest, trace rng = draw :: rest)
    (hord : FrameInOrder view oracle (restoredModelOf dh s) (sliceOf message)) :
    ∃ output,
      lifecycle.Session.decrypt rngCore cryptoRng s message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decrypt view oracle (restoredModelOf dh s) (sliceOf message)) ∧
      lifecycle.Session.invariant output.2.1 = ok true ∧ CounterRoom output.2.1 k := by
  exact decrypt_refines_keeps_invariant laws rngCore cryptoRng trace dh view oracle oracleOf codec contracts
    agreements s (restoredModelOf dh s) message rng k (import_ok_gives_invariant bytes s h)
    (sessionRefines_restored dh oracle.braidKem s hscope) ((counterRoom_iff_roomCheck s (k + 1)).mpr hcheck)
    htype htrace ⟨hchunk, fun _ _ _ => honestChunk_restored dh s hscope _, hdraw⟩ hord

end Tacenta.UnitLifecycleDecryptCompose

-- The pins `genpins.py` writes after this line print each statement whole: with no cut at depth 50
-- (`pp.deepTerms`) and each omitted proof with its proposition, `(⋯ : P)` (`pp.proofs.withType`). `attest.py`
-- refuses a statement pin that prints a bare `⋯`, and every other `pp` option.
set_option pp.deepTerms true
set_option pp.proofs.withType true

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleDecryptCompose.decrypt_ratchet_refines_keeps_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
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
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptCompose.decrypt_ratchet_refines_keeps_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptCompose.decrypt_refines_keeps_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
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
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptCompose.decrypt_refines_keeps_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptCompose.restored_decrypt_keeps_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
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
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptCompose.restored_decrypt_keeps_invariant

/--
info: Tacenta.UnitLifecycleDecryptCompose.decrypt_ratchet_refines_keeps_invariant : Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws →
  ∀ {R : Type} (rngCore : tacenta_session_unit.rand_core_1.RngCore R)
    (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
    (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
          ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
              ∀ (s : tacenta_session_unit.lifecycle.Session) (m : Model.Lifecycle.Session)
                (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) (k : ℕ),
                s.invariant = Aeneas.Std.Result.ok true →
                  Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem s m →
                    Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                      trace rng = oracle.draws →
                        Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle trace s m message
                            rng →
                          Tacenta.UnitLifecycleDecryptCompose.FrameInOrder view oracle m
                              (Tacenta.UnitLifecycleT3.sliceOf message) →
                            ∃ output,
                              tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng s message rng =
                                  Aeneas.Std.Result.ok output ∧
                                Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                                    (Model.Lifecycle.decryptRatchet view oracle m
                                      (Tacenta.UnitLifecycleT3.sliceOf message)) ∧
                                  output.2.1.invariant = Aeneas.Std.Result.ok true ∧
                                    Tacenta.UnitLifecycleSendPreserve.CounterRoom output.2.1 k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptCompose.decrypt_ratchet_refines_keeps_invariant

/--
info: Tacenta.UnitLifecycleDecryptCompose.decrypt_refines_keeps_invariant : Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws →
  ∀ {R : Type} (rngCore : tacenta_session_unit.rand_core_1.RngCore R)
    (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
    (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
          ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
              ∀ (s : tacenta_session_unit.lifecycle.Session) (m : Model.Lifecycle.Session)
                (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) (k : ℕ),
                s.invariant = Aeneas.Std.Result.ok true →
                  Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem s m →
                    Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                      tacenta_session_unit.serialization.message_type message =
                          Aeneas.Std.Result.ok (some tacenta_session_unit.serialization.MessageType.Ratchet) →
                        trace rng = oracle.draws →
                          Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle trace s m message
                              rng →
                            Tacenta.UnitLifecycleDecryptCompose.FrameInOrder view oracle m
                                (Tacenta.UnitLifecycleT3.sliceOf message) →
                              ∃ output,
                                tacenta_session_unit.lifecycle.Session.decrypt rngCore cryptoRng s message rng =
                                    Aeneas.Std.Result.ok output ∧
                                  Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                                      (Model.Lifecycle.decrypt view oracle m
                                        (Tacenta.UnitLifecycleT3.sliceOf message)) ∧
                                    output.2.1.invariant = Aeneas.Std.Result.ok true ∧
                                      Tacenta.UnitLifecycleSendPreserve.CounterRoom output.2.1 k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptCompose.decrypt_refines_keeps_invariant

/--
info: Tacenta.UnitLifecycleDecryptCompose.restored_decrypt_keeps_invariant : Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws →
  ∀ {R : Type} (rngCore : tacenta_session_unit.rand_core_1.RngCore R)
    (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
    (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
          ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
              ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (s : tacenta_session_unit.lifecycle.Session) (k : ℕ),
                tacenta_session_unit.lifecycle.Session.import bytes =
                    Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s) →
                  Tacenta.UnitLifecycleRestoredSession.RestoredScope s →
                    Tacenta.UnitLifecycleImportBudget.roomCheck s (k + 1) = true →
                      ∀ (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
                        tacenta_session_unit.serialization.message_type message =
                            Aeneas.Std.Result.ok (some tacenta_session_unit.serialization.MessageType.Ratchet) →
                          trace rng = oracle.draws →
                            (∀ (realComposite : tacenta_session_unit.tacenta_wire.Composite)
                                (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Model.Lifecycle.Bytes),
                                Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
                                    Except.ok (modelComposite, ciphertext) →
                                  Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
                                    Tacenta.UnitLifecycleT3.IncomingChunkRefines view
                                      (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s).braid realComposite
                                      modelComposite) →
                              (∃ draw rest, trace rng = draw :: rest) →
                                Tacenta.UnitLifecycleDecryptCompose.FrameInOrder view oracle
                                    (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s)
                                    (Tacenta.UnitLifecycleT3.sliceOf message) →
                                  ∃ output,
                                    tacenta_session_unit.lifecycle.Session.decrypt rngCore cryptoRng s message rng =
                                        Aeneas.Std.Result.ok output ∧
                                      Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                                          (Model.Lifecycle.decrypt view oracle
                                            (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s)
                                            (Tacenta.UnitLifecycleT3.sliceOf message)) ∧
                                        output.2.1.invariant = Aeneas.Std.Result.ok true ∧
                                          Tacenta.UnitLifecycleSendPreserve.CounterRoom output.2.1 k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptCompose.restored_decrypt_keeps_invariant

/--
info: def Tacenta.UnitLifecycleDecryptCompose.FrameInOrder : Model.Lifecycle.CodewordView →
  Model.Lifecycle.Oracle → Model.Lifecycle.Session → Model.Lifecycle.Bytes → Prop :=
fun view oracle m msg =>
  ∀ (c : Model.CompositeHeader.Composite) (ct : List UInt8),
    Model.CompositeHeader.decodeDetailed msg = Except.ok (c, ct) →
      Tacenta.UnitLifecycleDecryptPreserve.InOrderOut m.triple (Model.Lifecycle.tripleHeaderOf c)
        (Model.Lifecycle.sparseOutputOf
          (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.1)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptCompose.FrameInOrder
