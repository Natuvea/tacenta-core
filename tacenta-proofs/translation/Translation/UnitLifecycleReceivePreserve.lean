import Translation.UnitLifecycleSendPreserve
import Translation.UnitLifecycleResponderReplyReceipt

/-!
# `Session::decrypt` keeps `Session::invariant` on an in-order receive

`UnitLifecycleSendPreserve` proves that a send keeps `Session::invariant` at the agreement states whose send takes no
draw; no receive was covered, and each receipt module so far either rebuilt the invariant at one literal shape
(`UnitLifecycleResponderSuccessor`, the responder after the first frame) or did not show it at all
(`UnitLifecycleResponderReplyReceipt`, the initiator after the reply).  This module proves one receive step for every
invariant session, restricted to an in-order receive that leaves the agreement where it was, and applies it to both
receipts on their runs.

## What it shows

* `InOrder`, the scope: the header names no stored key in either ratchet; on the classical chain the peer holds it does
  not skip ahead; on a new ratchet key nothing is skipped on the chain being left and the message is the first of the
  new chain; on the sparse receiving chain of the header's epoch it does not skip ahead.  A condition on the state and
  the header only.
* `modelRatchetInv_receive_inOrder`, `modelTripleInv_receive_inOrder`: the model Triple's in-order receive without an
  agreement output keeps `ModelTripleInv` (`UnitTripleInvModel`), given a canonical header key and, when it takes a
  Diffie-Hellman step, a canonical candidate key.  `ratchet_receive_inOrder`, `spqr_receive_inOrder`: in order, the
  leaf receives are their last steps (`classicalTail`, `sparseTail`): no stored key, no skip.
* `receiveWithEviction_inOrder`: in order, the session's receive with eviction is the Triple's receive (the store is
  never full, so the retry loop does not run).
* `InOrderReceiveStep oracle m m'`: the agreement keeps its state (`KeepsAgreementState`: `noHeaderReceived` stays
  there, `keysSampled` stays there, at the same epoch), and the Triple and ratchet key are as they were, or the Triple is
  an in-order receive with the oracle's public key of a draw as the candidate and the ratchet key is replaced by that
  draw exactly when the sending key changed.  `decryptRatchet_inOrderStep`, `decrypt_inOrderStep`: the model's own
  `decryptRatchet` and public `decrypt` are such steps, for every view, oracle, session and message whose decoded
  headers are in order and leave the agreement in such a state.
* `modelCounterRoom_receive`: such a step spends at most one unit of the counter budget `CounterRoom`
  (`UnitLifecycleSendPreserve`): the clock rises by at most one, both epochs are kept, one sparse receiving chain steps by
  one.
* `two_chunk_loop`, `add_chunk_one`, `decoder_invariant_le_two`, `decoder_step_keeps`: a header decoder holding at most
  one chunk keeps `Decoder::invariant` and its size through one `add_chunk` (at most two chunks after, of distinct
  indices).
* `braid_receive_keysSampled`, `braid_receive_keeps`: the translated `Braid::receive` at `NoHeaderReceived` (holding at
  most one chunk) or `KeysSampled`, staying in the same kind at the same epoch (`SameAgreementKind`), keeps
  `Braid::invariant` and the four fields the structural clauses read, under `KemCloneAgrees`.
* `structural_receive`, `structural_clear_pending`, `clause_a_of_structural`: `Session::structural_invariant` survives a
  new Triple, agreement and ratchet key whose public key bytes are the new sending key, and survives clearing the pending
  initial message.
* `decrypt_ratchet_keeps_invariant_in_order`: **for every session `s` that passes `Session::invariant`, has room for `k + 1`
  operations and refines a model session `m`, whose agreement is at `NoHeaderReceived` holding at most one chunk or at
  `KeysSampled`, every successful `decrypt_ratchet` there whose session refines a model session that is an
  `InOrderReceiveStep` from `m` leaves a session that passes `Session::invariant` and has room for `k`.**  The relation
  after the call and the step are hypotheses; the records are `KemCloneAgrees`, the oracle's `dhPublic` clause, the
  view's codec relation and the law `DhPublicValid`.  `decrypt_keeps_invariant_in_order` is the same for the public
  `decrypt` (`decrypt_ok_inner`: its success is an inner `decrypt_ratchet` with the pending initial message cleared), and
  `decrypt_keeps_invariant_model_step` takes the relation at the model's own `decrypt` step.
* `initiator_receives_reply_successor`: on the run of the initiator's first send, the responder's receipt and its reply,
  under the hypotheses of `initiator_receives_reply` and no other, the session `s''` the initiator's `decrypt` of the
  reply returns passes `Session::invariant`, meets `CounterHeadroom` and has room for every `j` with `j + 2 < u32::MAX`
  further operations (the clock there is 1, so the bound is exact).  The step there is at `KeysSampled` (`replyReceipt_inOrderStep`).
* `responder_successor_via_preservation`: on the run of the initiator's first frame, under the hypotheses of
  `responder_first_frame_successor`, the conclusion of that theorem (the relation, `Session::invariant` and
  `CounterHeadroom` at the session `establish_responder` returns), derived here from the invariant of the prepared
  session (`responder_prepared_invariant`) and its budget through the general step at `NoHeaderReceived`
  (`firstReceipt_inOrderStep`), with no shape of the session after the call.

## How

The Triple half goes through the model, as in `UnitLifecycleSendPreserve`: the code Triple's invariant is
`ModelTripleInv` of the model Triple it refines, the in-order receive keeps that, and the relation after the call carries
it back.  The agreement half is a walk of the translated `Braid::receive` (the clone of the state, then `step_receive`):
at `KeysSampled` the state is the clone with the key pair cloned, at `NoHeaderReceived` the decoder is the one given or one
`add_chunk` of it (`braid_receive_noHeader`).  Clause (a) of the structural clauses, the ratchet key's public key bytes
against the Triple's sending key, is read from the call's walk (`decrypt_ratchet_ok_parts`): unchanged when the sending key
is, and otherwise the new key is the drawn candidate, whose public key is the model's new sending key by the oracle's
`dhPublic` clause and the codec; its bytes are canonical by `DhPublicValid`.  The other structural clauses read the Triple
only through the direction and the sparse epoch, which an in-order receive keeps, and the agreement through what the walk
keeps.  The budget is carried to the model and back.  On the reply's run, `s'`, its relation and its invariant are
`established_encrypt_successor_hypotheses` on the same first send, the call and the relation after it are
`initiator_receives_reply`'s, and the budget at `s'` is read off the model session the first send leaves.

## Laws and premises

No new law and no new per-run premise.  The general step takes `KemCloneAgrees` (the Braid's records carry it), the
decrypt oracle record's `dhPublic` clause, `DhCodecOf` and `DhPublicValid`, all already premises of the runs it is
applied on; `InOrder` and `KeepsAgreementState` are scope restrictions inside `InOrderReceiveStep`, computed on each run,
never a run premise; `CounterRoom` is internal (the run headlines conclude `CounterHeadroom`).  No premise names a width,
so each result holds on 32- and 64-bit targets.

## Trust

Every result here rests on the kernel and opaque constants only, with no compiler-trust axiom (pins below).  The general
step calls no refinement theorem; its premises are not all walks of translated code: the relation after the call carries
the Triple half, the direction, the sparse epoch and the budget, and the model step is a hypothesis.  The two run results
apply the decrypt and encrypt refinements through `initiator_receives_reply`, `established_encrypt_successor_hypotheses`
and `responder_first_frame_inner_succeeds`, whose nine `native_decide` constants are kernel proofs since 2026-10-21.

## Where its premises are exhibited

The general step quantifies over two agreement states.  Its premises are exhibited together at `KeysSampled` on the
reply's run (`initiator_receives_reply_successor`) and at `NoHeaderReceived` with an empty decoder on the first frame's
run (`responder_successor_via_preservation`).  No run here exhibits them at a decoder holding one chunk, so the two-chunk
case of the decoder lemma is proved but not used on a run.

## What it does not show

* A receive that uses a stored key, skips a message on either chain, or evicts from a full store: outside `InOrder`.  So
  reordered, delayed or dropped delivery is not covered.
* A receive with an agreement output (the sparse ratchet's `advance`, a new chain pair, `clearOldEpochs`), one that
  moves the agreement to another state (the header completing at `NoHeaderReceived`, a `ct1` chunk at `KeysSampled`), or
  one at any other agreement state.
* A header decoder holding more than one chunk before the call, and the two-chunk case on a run.
* A refused `decrypt` or `decrypt_ratchet`: no statement here about the session a refusal returns.
* That the relation after the call holds, or that the model's step is an in-order step: hypotheses of the general step,
  supplied on the two runs by the decrypt refinement and by the model's own step there.
* That the ceilings are kept or refused at (false of the code, `UnitLifecycleSendPreserve`); the budget at any session
  other than the initiator's after its first send and the responder's prepared session.
* The initiator's second send at `s''` composed with this result (`UnitLifecycleInitiatorSecondSend` states its code-level
  part under the invariant and the ceilings at `s''`; `UnitLifecycleInitiatorSecondMessage` joins the two, not this module), the responder's receipt of a
  second message (`UnitLifecycleResponderSecondReceipt` applies this result at the responder's session after its reply;
  this module does not), a second reply, the header's later chunks and every later step.
* The regression at the hypotheses of `initiator_first_send_responder_successor_admissible`: it is stated at those of
  `responder_first_frame_successor`, on the first frame's run.
* A restored copy of a session; the one-time path in a run.
* That the real primitives meet `KemCloneAgrees`, `DhPublicValid` or the records and laws the runs rest on.
* That `Session::invariant` says a session is reachable: it is a predicate on fields.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv)

namespace Tacenta.UnitLifecycleReceivePreserve

open Tacenta.UnitTripleInvModel
open Tacenta.UnitLifecycleSendPreserve (CounterRoom ModelCounterRoom counterRoom_zero counterRoom_iff_model
  mem_sent_chains findChains_mem)
open Tacenta.UnitLifecycleT3 (DhView DhCodecOf SessionRefines arrayOf)

/-! ## The model's in-order receive keeps `ModelTripleInv` -/

section Model
open Model.State (Key)

/-- **The in-order scope of a receive**: the header names no stored key in either ratchet; on the classical chain the
peer holds (`dhrPub = some dh`) it does not skip ahead (`n ≤ nr`); on a new ratchet key nothing is skipped on the
chain being left (no receiving chain, no peer key, or `pn ≤ nr`) and the message is the first of the new chain
(`n = 0`); on the sparse receiving chain of the header's epoch it does not skip ahead (`pqN - 1 ≤` the chain's
counter).  A restriction of scope, about the state and the header only: it says nothing of the result. -/
structure InOrder (m : Model.Triple.State) (h : Model.Triple.Header) : Prop where
  noStoredClassical : Model.Ratchet.trySkipped m.classical h.dr = none
  sameChain : m.classical.dhrPub = some h.dr.dh → h.dr.n ≤ m.classical.nr
  newChain : m.classical.dhrPub ≠ some h.dr.dh →
    (m.classical.ckr = none ∨ m.classical.dhrPub = none ∨ h.dr.pn ≤ m.classical.nr) ∧ h.dr.n = 0
  noStoredSparse : Model.SparseRatchet.trySkipped m.postQuantum h.epoch h.pqN = none
  sparseNext : ∀ cs ch, Model.SparseRatchet.findChains m.postQuantum h.epoch = some cs →
    cs.receive = some ch → h.pqN - 1 ≤ ch.n

/-- A classical skip that has nothing to skip leaves the state as it was. -/
theorem skip_noop {st : Model.State.State} {upto : Nat}
    (h : st.ckr = none ∨ st.dhrPub = none ∨ upto ≤ st.nr) :
    Model.State.skipMessageKeys st upto = some st := by
  unfold Model.State.skipMessageKeys
  rcases hc : st.ckr with _ | ck <;> rcases hd : st.dhrPub with _ | dhr <;> simp_all

/-- The classical receive's last step, once the chain to read is chosen: refuse a message below the counter, read
the chain, refuse at the ceiling, else step the chain and age the store. -/
def classicalTail (st1 : Model.State.State) (hdr : Model.State.Header) :
    Except Model.Ratchet.ReceiveRefusal (Model.State.State × Key) :=
  if hdr.n < st1.nr then .error .outOfOrder
  else
    match st1.ckr with
    | none => .error .noReceivingChain
    | some ck =>
      if st1.nr < Model.State.u32Max then
        .ok (Model.State.ageStore { st1 with ckr := some (Model.State.kdfCk ck).1, nr := st1.nr + 1 },
          (Model.State.kdfCk ck).2)
      else .error .chainExhausted

/-- **The classical receive, in order**: it is `classicalTail` of the state (on the peer's chain) or of the
Diffie-Hellman step (on a new key).  Model only. -/
theorem ratchet_receive_inOrder {st : Model.State.State} {hdr : Model.State.Header} {dr ds np : Key}
    (hts : Model.Ratchet.trySkipped st hdr = none)
    (hsame : st.dhrPub = some hdr.dh → hdr.n ≤ st.nr)
    (hnew : st.dhrPub ≠ some hdr.dh →
      (st.ckr = none ∨ st.dhrPub = none ∨ hdr.pn ≤ st.nr) ∧ hdr.n = 0) :
    Model.Ratchet.receiveDetailed st hdr dr ds np =
      classicalTail (if st.dhrPub = some hdr.dh then st else Model.Ratchet.dhRatchet st hdr dr ds np) hdr := by
  unfold Model.Ratchet.receiveDetailed
  rw [hts]
  by_cases hd : st.dhrPub = some hdr.dh
  · have hsk : Model.Ratchet.skipMessageKeysDetailed st hdr.n = .ok st := by
      rw [Model.Ratchet.skipMessageKeysDetailed_ok_iff]
      exact skip_noop (Or.inr (Or.inr (hsame hd)))
    have hb : (st.dhrPub == some hdr.dh) = true := by simp [hd]
    simp only [hb, if_true, hsk]
    rw [if_pos hd]
    rfl
  · obtain ⟨hpn, hn⟩ := hnew hd
    have hsk : Model.Ratchet.skipMessageKeysDetailed st hdr.pn = .ok st := by
      rw [Model.Ratchet.skipMessageKeysDetailed_ok_iff]
      exact skip_noop hpn
    have hsk2 : Model.Ratchet.skipMessageKeysDetailed (Model.Ratchet.dhRatchet st hdr dr ds np) hdr.n =
        .ok (Model.Ratchet.dhRatchet st hdr dr ds np) := by
      rw [Model.Ratchet.skipMessageKeysDetailed_ok_iff]
      exact skip_noop (Or.inr (Or.inr (by rw [hn]; simp [Model.Ratchet.dhRatchet])))
    have hne : (st.dhrPub == some hdr.dh) = false := by simpa using hd
    simp only [hne, Bool.false_eq_true, if_false, hsk, hsk2]
    rw [if_neg hd]
    rfl

/-- The sparse receive's last step at the header's epoch, without an agreement output and with nothing to skip. -/
def sparseTail (st : Model.SparseRatchet.State) (e n : Nat) :
    Except Model.SparseRatchet.ReceiveRefusal (Model.SparseRatchet.State × Key) :=
  match Model.SparseRatchet.findChains st e with
  | none => .error .noChain
  | some cs =>
    match cs.receive with
    | none => .error .chainRetired
    | some ch =>
      if Model.SparseRatchet.u64Max ≤ ch.n then .error .chainExhausted
      else if n != ch.n + 1 then .error .outOfOrder
      else .ok (Model.SparseRatchet.setChains st e
          { cs with receive := some { ck := (Model.SparseRatchet.kdfCk ch.ck n).1, n := n } },
        (Model.SparseRatchet.kdfCk ch.ck n).2)

/-- **The sparse receive without an agreement output, in order**, is `sparseTail`.  Model only. -/
theorem spqr_receive_inOrder {st : Model.SparseRatchet.State} {e n : Nat}
    (hts : Model.SparseRatchet.trySkipped st e n = none)
    (hnext : ∀ cs ch, Model.SparseRatchet.findChains st e = some cs → cs.receive = some ch → n - 1 ≤ ch.n) :
    Model.SparseRatchet.receiveDetailed st e none n = sparseTail st e n := by
  unfold Model.SparseRatchet.receiveDetailed Model.SparseRatchet.maybeAdvanceReceiveDetailed
    Model.SparseRatchet.maybeAdvanceDetailed
  simp only [hts]
  unfold sparseTail
  rcases hf : Model.SparseRatchet.findChains st e with _ | cs
  · have : Model.SparseRatchet.skipMessageKeysDetailed st e (n - 1) = .error .noChain := by
      rw [Model.SparseRatchet.skipMessageKeysDetailed_no_chain_iff]; exact hf
    simp only [this]
  rcases hr : cs.receive with _ | ch
  · have : Model.SparseRatchet.skipMessageKeysDetailed st e (n - 1) = .error .chainRetired := by
      rw [Model.SparseRatchet.skipMessageKeysDetailed_retired_iff]; exact ⟨cs, hf, hr⟩
    simp only [this, hr]
  have : Model.SparseRatchet.skipMessageKeysDetailed st e (n - 1) = .ok st := by
    rw [Model.SparseRatchet.skipMessageKeysDetailed_ok_iff]
    unfold Model.SparseRatchet.skipMessageKeys
    simp [hf, hr, hnext cs ch hf hr]
  simp only [this, hf, hr]

/-- A successful `classicalTail` read the chain, below the ceiling, and returns the aged state with the chain stepped. -/
theorem classicalTail_ok {st1 st' : Model.State.State} {hdr : Model.State.Header} {mk : Key}
    (h : classicalTail st1 hdr = .ok (st', mk)) :
    ∃ ck, st1.ckr = some ck ∧ st1.nr < Model.State.u32Max ∧
      st' = Model.State.ageStore { st1 with ckr := some (Model.State.kdfCk ck).1, nr := st1.nr + 1 } := by
  unfold classicalTail at h
  by_cases hlt : hdr.n < st1.nr
  · simp [hlt] at h
  simp only [hlt, if_false] at h
  rcases hc : st1.ckr with _ | ck
  · rw [hc] at h; simp at h
  rw [hc] at h
  simp only at h
  by_cases hu : st1.nr < Model.State.u32Max
  · simp only [hu, if_true, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨ck, rfl, hu, h.1.symm⟩
  · simp [hu] at h

/-- **The classical tail keeps `ModelRatchetInv`** when the chosen state has the old store and clock, a sending chain
and a peer key whenever it has a receiving chain, and canonical keys.  Model only. -/
theorem modelRatchetInv_tail {st st1 st' : Model.State.State} {hdr : Model.State.Header} {mk : Key}
    (h : ModelRatchetInv st) (hsk : st1.skipped = st.skipped) (hev : st1.events = st.events)
    (hch : st1.ckr.isSome = true → st1.cks.isSome = true ∧ st1.dhrPub.isSome = true)
    (hdhs : Model.Messages.canonicalKey st1.dhsPub = true)
    (hdhr : ∀ k, st1.dhrPub = some k → Model.Messages.canonicalKey k = true)
    (ht : classicalTail st1 hdr = .ok (st', mk)) : ModelRatchetInv st' := by
  obtain ⟨ck, hck, -, rfl⟩ := classicalTail_ok ht
  have hmax : st.events ≤ Model.State.maxEvents := by
    have := h.clock_room; unfold Model.State.maxEvents; omega
  have hsub : (st.skipped.filter fun e => decide (min (st.events + 1) Model.State.maxEvents - e.2.2.1 <
      Model.State.maxSkippedAge)).Sublist st.skipped := List.filter_sublist
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Model.State.ageStore, hsk, hev]
    exact le_trans hsub.length_le h.store_bound
  · exact Model.State.ageStore_events_lt _
  · simp only [Model.State.ageStore, hsk, hev]
    intro e he
    have := h.fresh e (hsub.subset he)
    omega
  · simp only [Model.State.ageStore, hsk, hev]
    exact h.store_map.sublist hsub
  · intro _
    simp only [Model.State.ageStore]
    exact hch (by rw [hck]; rfl)
  · simpa [Model.State.ageStore] using hdhs
  · simpa [Model.State.ageStore] using hdhr
  · simp only [Model.State.ageStore, hsk, hev]
    intro e he
    exact h.store_canonical e (hsub.subset he)

/-- **The classical in-order receive keeps `ModelRatchetInv`**, given a canonical header key and, when it takes a
Diffie-Hellman step, a canonical candidate key.  Model only. -/
theorem modelRatchetInv_receive_inOrder {st st' : Model.State.State} {hdr : Model.State.Header}
    {dr ds np mk : Key} (h : ModelRatchetInv st) (hhdr : Model.Messages.canonicalKey hdr.dh = true)
    (hnp : st.dhrPub ≠ some hdr.dh → Model.Messages.canonicalKey np = true)
    (hts : Model.Ratchet.trySkipped st hdr = none)
    (hsame : st.dhrPub = some hdr.dh → hdr.n ≤ st.nr)
    (hnew : st.dhrPub ≠ some hdr.dh →
      (st.ckr = none ∨ st.dhrPub = none ∨ hdr.pn ≤ st.nr) ∧ hdr.n = 0)
    (hr : Model.Ratchet.receiveDetailed st hdr dr ds np = .ok (st', mk)) : ModelRatchetInv st' := by
  rw [ratchet_receive_inOrder hts hsame hnew] at hr
  by_cases hd : st.dhrPub = some hdr.dh
  · rw [if_pos hd] at hr
    exact modelRatchetInv_tail h rfl rfl h.chains h.dhs_canonical h.dhr_canonical hr
  · rw [if_neg hd] at hr
    refine modelRatchetInv_tail (st1 := Model.Ratchet.dhRatchet st hdr dr ds np) h rfl rfl
      (fun _ => ⟨rfl, rfl⟩) (hnp hd) ?_ hr
    intro k hk
    simp only [Model.Ratchet.dhRatchet, Option.some.injEq] at hk
    rw [← hk]; exact hhdr

/-- **The classical in-order receive's frame**: the sending key is kept or, on a Diffie-Hellman step, is the
candidate; the clock rises by at most one; a receiving chain is held.  Model only. -/
theorem ratchet_receive_frame {st st' : Model.State.State} {hdr : Model.State.Header} {dr ds np mk : Key}
    (hts : Model.Ratchet.trySkipped st hdr = none)
    (hsame : st.dhrPub = some hdr.dh → hdr.n ≤ st.nr)
    (hnew : st.dhrPub ≠ some hdr.dh →
      (st.ckr = none ∨ st.dhrPub = none ∨ hdr.pn ≤ st.nr) ∧ hdr.n = 0)
    (hr : Model.Ratchet.receiveDetailed st hdr dr ds np = .ok (st', mk)) :
    (st.dhrPub = some hdr.dh → st'.dhsPub = st.dhsPub) ∧ (st.dhrPub ≠ some hdr.dh → st'.dhsPub = np) ∧
      st'.events ≤ st.events + 1 ∧ st'.ckr.isSome = true := by
  rw [ratchet_receive_inOrder hts hsame hnew] at hr
  by_cases hd : st.dhrPub = some hdr.dh
  · rw [if_pos hd] at hr
    obtain ⟨ck, -, -, rfl⟩ := classicalTail_ok hr
    refine ⟨fun _ => rfl, fun h => absurd hd h, ?_, rfl⟩
    simp only [Model.State.ageStore]; omega
  · rw [if_neg hd] at hr
    obtain ⟨ck, -, -, rfl⟩ := classicalTail_ok hr
    refine ⟨fun h => absurd h hd, fun _ => rfl, ?_, rfl⟩
    simp only [Model.State.ageStore, Model.Ratchet.dhRatchet]; omega

/-- A successful `sparseTail` stepped the receiving chain of an entry the table holds, by one, below the ceiling. -/
theorem sparseTail_ok {st st' : Model.SparseRatchet.State} {e n : Nat} {mk : Key}
    (h : sparseTail st e n = .ok (st', mk)) :
    ∃ cs ch, (e, cs) ∈ st.chains ∧ cs.receive = some ch ∧ n = ch.n + 1 ∧ ch.n < Model.SparseRatchet.u64Max ∧
      st' = Model.SparseRatchet.setChains st e
        { cs with receive := some { ck := (Model.SparseRatchet.kdfCk ch.ck n).1, n := n } } := by
  unfold sparseTail at h
  rcases hf : Model.SparseRatchet.findChains st e with _ | cs
  · rw [hf] at h; simp at h
  rw [hf] at h
  simp only at h
  rcases hr : cs.receive with _ | ch
  · rw [hr] at h; simp at h
  rw [hr] at h
  simp only at h
  by_cases hu : Model.SparseRatchet.u64Max ≤ ch.n
  · simp [hu] at h
  by_cases hn : n = ch.n + 1
  · simp only [hu, if_false, hn, bne_self_eq_false, Bool.false_eq_true, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨cs, ch, findChains_mem hf, hr, hn, by omega, by rw [← h.1, hn]⟩
  · have : (n != ch.n + 1) = true := by simpa using hn
    simp [hu, this] at h

/-- **The sparse tail keeps `ModelSpqrInv`**: it replaces one entry of the table at an epoch the table holds and
leaves the epoch, the direction and the store.  Model only. -/
theorem modelSpqrInv_tail {st st' : Model.SparseRatchet.State} {e n : Nat} {mk : Key}
    (h : ModelSpqrInv st) (ht : sparseTail st e n = .ok (st', mk)) : ModelSpqrInv st' := by
  obtain ⟨cs, ch, hmem, -, -, -, rfl⟩ := sparseTail_ok ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.store_bound
  · intro q hq
    simp only [Model.SparseRatchet.setChains] at hq ⊢
    rcases mem_sent_chains hq with ⟨hq', -⟩ | rfl
    · exact h.epoch_window q hq'
    · exact h.epoch_window (e, cs) hmem
  · simp only [Model.SparseRatchet.setChains]
    rw [List.pairwise_append]
    refine ⟨h.chains_distinct.sublist List.filter_sublist, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne] at ha
    simp only [List.mem_singleton] at hb
    subst hb
    exact ha.2
  · obtain ⟨q, hq, hqe⟩ := h.current_present
    simp only [Model.SparseRatchet.setChains]
    by_cases hqe' : q.1 = e
    · exact ⟨(e, _), List.mem_append_right _ (List.mem_singleton_self _), by rw [← hqe', hqe]⟩
    · exact ⟨q, List.mem_append_left _ (List.mem_filter.mpr ⟨hq, by simpa using hqe'⟩), hqe⟩
  · intro a ha
    obtain ⟨q, hq, hqa⟩ := h.skipped_chained a ha
    simp only [Model.SparseRatchet.setChains]
    by_cases hqe' : q.1 = e
    · exact ⟨(e, _), List.mem_append_right _ (List.mem_singleton_self _), by rw [← hqe', hqa]⟩
    · exact ⟨q, List.mem_append_left _ (List.mem_filter.mpr ⟨hq, by simpa using hqe'⟩), hqa⟩
  · exact h.skipped_map

/-- **The model Triple's in-order receive without an agreement output keeps `ModelTripleInv`**, given a canonical
header key and, when the classical receive takes a Diffie-Hellman step, a canonical candidate key.  Model only. -/
theorem modelTripleInv_receive_inOrder {m m' : Model.Triple.State} {hdr : Model.Triple.Header}
    {dr ds np k : Key} (h : ModelTripleInv m) (hhdr : Model.Messages.canonicalKey hdr.dr.dh = true)
    (hnp : m.classical.dhrPub ≠ some hdr.dr.dh → Model.Messages.canonicalKey np = true)
    (hord : InOrder m hdr)
    (hs : Model.Triple.receiveDetailed m hdr dr ds np none = .ok (m', k)) : ModelTripleInv m' := by
  obtain ⟨hr, hq, -⟩ := h
  unfold Model.Triple.receiveDetailed at hs
  rcases hc : Model.Ratchet.receiveDetailed m.classical hdr.dr dr ds np with _ | ⟨c, mkc⟩
  · rw [hc] at hs; simp at hs
  rw [hc] at hs
  simp only at hs
  rcases hp : Model.SparseRatchet.receiveDetailed m.postQuantum hdr.epoch none hdr.pqN with _ | ⟨q, mkq⟩
  · rw [hp] at hs; simp at hs
  rw [hp] at hs
  simp only [Except.ok.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, -⟩ := hs
  rw [spqr_receive_inOrder hord.noStoredSparse hord.sparseNext] at hp
  refine ⟨modelRatchetInv_receive_inOrder hr hhdr hnp hord.noStoredClassical hord.sameChain hord.newChain hc,
    modelSpqrInv_tail hq hp, ?_⟩
  obtain ⟨-, -, -, hck⟩ := ratchet_receive_frame hord.noStoredClassical hord.sameChain hord.newChain hc
  unfold ModelRolesAgree
  simp only
  rcases hk : c.ckr with _ | x
  · rw [hk] at hck; simp at hck
  · rcases c.cks <;> simp

end Model

/-! ## The model's `decryptRatchet` step, in order and without an agreement output -/

section ModelStep
open Model.State (Key)

/-- The model agreement states a receive here leaves in place: `noHeaderReceived` stays `noHeaderReceived` (the
header is not complete) and `keysSampled` stays `keysSampled` (no `ct1` chunk), each at the same epoch. -/
def KeepsAgreementState : Model.Braid.BraidState → Model.Braid.BraidState → Prop
  | .noHeaderReceived e _ _, .noHeaderReceived e' _ _ => e' = e
  | .keysSampled e _ _ _ _, .keysSampled e' _ _ _ _ => e' = e
  | _, _ => False

/-- A model agreement receive that keeps the state has no output. -/
theorem keeps_output_none (K : Model.Braid.Kem) (st : Model.Braid.BraidState) (msg : Model.Braid.Msg)
    (h : KeepsAgreementState st (Model.Braid.receive K st msg).2.2) :
    (Model.Braid.receive K st msg).2.1 = none := by
  cases st <;> simp only [KeepsAgreementState] at h <;> simp only [Model.Braid.receive] at h ⊢
  all_goals
    repeat' first
      | (split at h) | (split) | rfl

/-- A model agreement receive that keeps the state keeps its epoch. -/
theorem keeps_epoch {st st' : Model.Braid.BraidState} (h : KeepsAgreementState st st') : st'.epoch = st.epoch := by
  cases st <;> cases st' <;> simp_all [KeepsAgreementState, Model.Braid.BraidState.epoch]

/-- The model decoder reads a canonical ratchet key: a decoded composite header's key passes `canonicalKey`. -/
theorem decode_dh_canonical {bs : List UInt8} {c : Model.CompositeHeader.Composite} {ct : List UInt8}
    (h : Model.CompositeHeader.decode bs = some (c, ct)) : Model.Messages.canonicalKey c.dh = true := by
  unfold Model.CompositeHeader.decode at h
  split at h
  · split_ifs at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨dh, r1⟩, -, h⟩ := h
    simp only at h
    obtain ⟨u, hu, h⟩ := h
    have hk : Model.Messages.canonicalKey dh = true := by
      unfold Model.Messages.checkKey at hu; split_ifs at hu with hh; exact hh
    obtain ⟨a, -, a1, -, a2, -, a3, -, a4, -, h⟩ := h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨_, _, _, _, _, _, h⟩ := h
      split_ifs at h <;> simp at h <;> (obtain ⟨rfl, -⟩ := h; exact hk)
    · simp at h
  · simp at h

/-- `classicalTail` never refuses for a full store. -/
theorem classicalTail_err {st1 : Model.State.State} {hdr : Model.State.Header}
    {r : Model.Ratchet.ReceiveRefusal} (h : classicalTail st1 hdr = .error r) : r ≠ .skippedStoreFull := by
  unfold classicalTail at h
  rcases hc : st1.ckr with _ | ck <;> simp only [hc] at h <;> split_ifs at h <;>
    simp only [Except.error.injEq] at h <;> subst h <;> decide

/-- `sparseTail` never refuses for a full store. -/
theorem sparseTail_err {st : Model.SparseRatchet.State} {e n : Nat}
    {r : Model.SparseRatchet.ReceiveRefusal} (h : sparseTail st e n = .error r) : r ≠ .skippedStoreFull := by
  unfold sparseTail at h
  split at h
  · simp only [Except.error.injEq] at h; subst h; decide
  · split at h
    · simp only [Except.error.injEq] at h; subst h; decide
    · split_ifs at h
      · simp only [Except.error.injEq] at h; subst h; decide
      · simp only [Except.error.injEq] at h; subst h; decide

/-- **Under the in-order scope the session's receive with eviction is the Triple's receive**: the store is never
full (nothing is skipped), so the retry loop does not run.  Model only. -/
theorem receiveWithEviction_inOrder {m : Model.Triple.State} {c : Model.CompositeHeader.Composite}
    {hdr : Model.Triple.Header} {dr ds np : Key} {r : Model.Triple.State × Key}
    (hord : InOrder m hdr)
    (h : Model.Lifecycle.receiveWithEviction m c hdr dr ds np none = .ok r) :
    Model.Triple.receiveDetailed m hdr dr ds np none = .ok r := by
  unfold Model.Lifecycle.receiveWithEviction at h
  rcases hd : Model.Triple.receiveDetailed m hdr dr ds np none with reason | r'
  · exfalso
    rw [hd] at h
    simp only at h
    have hnf : Model.Lifecycle.fullStore reason = none := by
      unfold Model.Triple.receiveDetailed at hd
      rw [ratchet_receive_inOrder hord.noStoredClassical hord.sameChain hord.newChain,
        spqr_receive_inOrder hord.noStoredSparse hord.sparseNext] at hd
      rcases hc : classicalTail (if m.classical.dhrPub = some hdr.dr.dh then m.classical
          else Model.Ratchet.dhRatchet m.classical hdr.dr dr ds np) hdr.dr with rc | ⟨c1, k1⟩
      · rw [hc] at hd
        simp only [Except.error.injEq] at hd
        subst hd
        have := classicalTail_err hc
        cases rc <;> simp_all [Model.Lifecycle.fullStore]
      · rw [hc] at hd
        simp only at hd
        rcases hp : sparseTail m.postQuantum hdr.epoch hdr.pqN with rp | ⟨q1, k2⟩
        · rw [hp] at hd
          simp only [Except.error.injEq] at hd
          subst hd
          have := sparseTail_err hp
          cases rp <;> simp_all [Model.Lifecycle.fullStore]
        · rw [hp] at hd
          simp at hd
    rw [hnf] at h
    simp at h
  · rw [hd] at h
    simpa using h

/-- **A receive step in order**: the agreement keeps its state (`KeepsAgreementState`), and either the Triple and
the ratchet key are as they were, or the Triple is the model Triple's receive without an agreement output of a
header in the in-order scope whose key is canonical, with the oracle's public key of the draw `cand` as the
candidate, and the ratchet key is replaced by `cand` exactly when the sending key changed.  What the model's
`decryptRatchet` does on an in-order frame (`decryptRatchet_inOrderStep`). -/
def InOrderReceiveStep (oracle : Model.Lifecycle.Oracle) (m m' : Model.Lifecycle.Session) : Prop :=
  KeepsAgreementState m.braid m'.braid ∧
    ((m'.triple = m.triple ∧ m'.ratchetPrivate = m.ratchetPrivate) ∨
      ∃ (hdr : Model.Triple.Header) (dr ds cand mk : Key),
        InOrder m.triple hdr ∧ Model.Messages.canonicalKey hdr.dr.dh = true ∧
        Model.Triple.receiveDetailed m.triple hdr dr ds (oracle.dhPublic cand) none = .ok (m'.triple, mk) ∧
        m'.ratchetPrivate =
          if m'.triple.classical.dhsPub == m.triple.classical.dhsPub then m.ratchetPrivate else cand)

/-- **The model's `decryptRatchet` of a frame in the in-order scope is an `InOrderReceiveStep`**: for every view,
oracle, session and message, when the session's agreement is one `KeepsAgreementState` covers, and every header the
message decodes to is in order for the session's Triple and leaves the agreement in such a state.  Model only. -/
theorem decryptRatchet_inOrderStep (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (m : Model.Lifecycle.Session) (msg : Model.Lifecycle.Bytes)
    (hkeep : KeepsAgreementState m.braid m.braid)
    (hord : ∀ c ct, Model.CompositeHeader.decodeDetailed msg = .ok (c, ct) →
      InOrder m.triple (Model.Lifecycle.tripleHeaderOf c) ∧
      KeepsAgreementState m.braid
        (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.2) :
    InOrderReceiveStep oracle m (Model.Lifecycle.decryptRatchet view oracle m msg).session := by
  have stay : InOrderReceiveStep oracle m m := ⟨hkeep, Or.inl ⟨rfl, rfl⟩⟩
  unfold Model.Lifecycle.decryptRatchet
  by_cases hf : Model.Lifecycle.agreementFailed m = true
  · simp only [hf, if_true]; exact stay
  simp only [hf, Bool.false_eq_true, if_false]
  rcases hd : Model.CompositeHeader.decodeDetailed msg with reason | ⟨c, ct⟩
  · exact stay
  obtain ⟨hio, hk⟩ := hord c ct hd
  have hcan : Model.Messages.canonicalKey c.dh = true :=
    decode_dh_canonical ((Model.CompositeHeader.decodeDetailed_ok_iff _ _).mp hd)
  have hout := keeps_output_none oracle.braidKem m.braid _ hk
  simp only
  rcases oracle.dhAgree m.ratchetPrivate c.dh with _ | dr
  · exact stay
  simp only
  rcases Model.Lifecycle.random32 oracle with _ | ⟨cand, o'⟩
  · exact stay
  simp only
  rcases oracle.dhAgree cand c.dh with _ | ds
  · exact stay
  simp only
  rw [hout]
  rcases hr : Model.Lifecycle.receiveWithEviction m.triple c (Model.Lifecycle.tripleHeaderOf c) dr ds
      (oracle.dhPublic cand) (Model.Lifecycle.sparseOutputOf none) with reason | ⟨t', mk⟩
  · exact stay
  simp only
  split
  · exact stay
  · refine ⟨hk, Or.inr ⟨Model.Lifecycle.tripleHeaderOf c, dr, ds, cand, mk, hio, hcan, ?_, rfl⟩⟩
    exact receiveWithEviction_inOrder hio hr

/-- The model Triple's in-order receive without an agreement output is its two leaf receives: the classical one
and `sparseTail`.  Model only. -/
theorem triple_receive_parts {m m' : Model.Triple.State} {hdr : Model.Triple.Header} {dr ds np k : Key}
    (hord : InOrder m hdr) (hs : Model.Triple.receiveDetailed m hdr dr ds np none = .ok (m', k)) :
    (∃ k1, Model.Ratchet.receiveDetailed m.classical hdr.dr dr ds np = .ok (m'.classical, k1)) ∧
      ∃ k2, sparseTail m.postQuantum hdr.epoch hdr.pqN = .ok (m'.postQuantum, k2) := by
  unfold Model.Triple.receiveDetailed at hs
  rw [spqr_receive_inOrder hord.noStoredSparse hord.sparseNext] at hs
  rcases hc : Model.Ratchet.receiveDetailed m.classical hdr.dr dr ds np with _ | ⟨c, mkc⟩
  · rw [hc] at hs; simp at hs
  rw [hc] at hs
  simp only at hs
  rcases hp : sparseTail m.postQuantum hdr.epoch hdr.pqN with _ | ⟨q, mkq⟩
  · rw [hp] at hs; simp at hs
  rw [hp] at hs
  simp only [Except.ok.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, -⟩ := hs
  exact ⟨⟨mkc, rfl⟩, ⟨mkq, rfl⟩⟩

/-- **An in-order receive step spends at most one unit of the counter budget**: the clock rises by at most one,
the sparse epoch and the agreement's epoch are kept, and one sparse receiving chain steps by one.  Model only. -/
theorem modelCounterRoom_receive (oracle : Model.Lifecycle.Oracle) {m m' : Model.Lifecycle.Session} (k : Nat)
    (hstep : InOrderReceiveStep oracle m m') (h : ModelCounterRoom m (k + 1)) : ModelCounterRoom m' k := by
  obtain ⟨hkeep, htr⟩ := hstep
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hbe := keeps_epoch hkeep
  rcases htr with ⟨htr, -⟩ | ⟨hdr, dr, ds, cand, mk, hord, -, hs, -⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [htr]; omega
    · rw [htr]; omega
    · rw [htr]; intro p hp ch hch; have := h3 p hp ch hch; omega
    · rw [hbe]; omega
  obtain ⟨⟨k1, hc⟩, ⟨k2, hp⟩⟩ := triple_receive_parts hord hs
  obtain ⟨-, -, hev, -⟩ := ratchet_receive_frame hord.noStoredClassical hord.sameChain hord.newChain hc
  obtain ⟨cs, ch, hmem, hrecv, hn, -, hq⟩ := sparseTail_ok hp
  refine ⟨by omega, ?_, ?_, by rw [hbe]; omega⟩
  · rw [hq]; simp only [Model.SparseRatchet.setChains]; omega
  · rw [hq]
    simp only [Model.SparseRatchet.setChains]
    intro p hp' c hcp
    rcases mem_sent_chains hp' with ⟨hp'', -⟩ | rfl
    · have := h3 p hp'' c hcp; omega
    · rcases hcp with hs' | hr'
      · have := h3 _ hmem c (Or.inl hs'); omega
      · simp only [Option.some.injEq] at hr'
        subst hr'
        have := h3 _ hmem ch (Or.inr hrecv)
        simp only; omega

/-- **What an in-order receive step leaves of the Triple's sending key, direction and sparse epoch**: the direction
and the sparse epoch are kept; when the sending key changes, the step took a Diffie-Hellman step, the new sending key
is the oracle's public key of the new ratchet key, and the header's key is canonical as the peer key.  Model only. -/
theorem step_frame (oracle : Model.Lifecycle.Oracle) {m m' : Model.Lifecycle.Session}
    (hstep : InOrderReceiveStep oracle m m') :
    m'.triple.postQuantum.direction = m.triple.postQuantum.direction ∧
      m'.triple.postQuantum.epoch = m.triple.postQuantum.epoch ∧
      (m'.triple.classical.dhsPub ≠ m.triple.classical.dhsPub →
        m'.triple.classical.dhsPub = oracle.dhPublic m'.ratchetPrivate) := by
  obtain ⟨-, htr⟩ := hstep
  rcases htr with ⟨htr, -⟩ | ⟨hdr, dr, ds, cand, mk, hord, -, hs, hrp⟩
  · rw [htr]; exact ⟨rfl, rfl, fun h => absurd rfl h⟩
  obtain ⟨⟨k1, hc⟩, ⟨k2, hp⟩⟩ := triple_receive_parts hord hs
  obtain ⟨hsame, hdh, -, -⟩ := ratchet_receive_frame hord.noStoredClassical hord.sameChain hord.newChain hc
  obtain ⟨cs, ch, -, -, -, -, hq⟩ := sparseTail_ok hp
  refine ⟨by rw [hq]; rfl, by rw [hq]; rfl, fun hne => ?_⟩
  have hrp' : m'.ratchetPrivate = cand := by
    rw [hrp]; simp [hne]
  rw [hrp']
  by_cases hd : m.triple.classical.dhrPub = some hdr.dr.dh
  · exact absurd (hsame hd) hne
  · exact hdh hd

/-- **The model's public `decrypt` of a message the dispatch passes on is an `InOrderReceiveStep`** under the
conditions of `decryptRatchet_inOrderStep` on the message the dispatch returns: the success arm clears the pending
initial message, which the step does not read.  Model only. -/
theorem decrypt_inOrderStep (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (m : Model.Lifecycle.Session) (msg inner : Model.Lifecycle.Bytes)
    (hdisp : Model.Lifecycle.dispatchDecrypt oracle m msg = .ok inner)
    (hkeep : KeepsAgreementState m.braid m.braid)
    (hord : ∀ c ct, Model.CompositeHeader.decodeDetailed inner = .ok (c, ct) →
      InOrder m.triple (Model.Lifecycle.tripleHeaderOf c) ∧
      KeepsAgreementState m.braid
        (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.2) :
    InOrderReceiveStep oracle m (Model.Lifecycle.decrypt view oracle m msg).session := by
  have h := decryptRatchet_inOrderStep view oracle m inner hkeep hord
  unfold Model.Lifecycle.decrypt
  rw [hdisp]
  simp only
  split
  · exact h
  · exact h

end ModelStep

/-! ## The header decoder: one more chunk, at most two held -/

section Decoder

/-- Two distinct bits of a byte share no set bit. -/
theorem pow_and_pow_ne {a b : Nat} (ha : a < 8) (hb : b < 8) (h : a ≠ b) : 2 ^ a &&& 2 ^ b = 0 := by
  interval_cases a <;> interval_cases b <;> first | exact absurd rfl h | decide

/-- The loop of `Decoder::invariant` over a decoder holding exactly two chunks of distinct indices returns its size,
`needed`, chunk list and `true`: the second chunk's bit is not set by the first. -/
theorem two_chunk_loop (d : tacenta_erasure.Decoder) (c1 c2 : tacenta_erasure.Chunk)
    (hv : d.«have».val = [c1, c2]) (hne : c1.index ≠ c2.index) :
    tacenta_erasure.Decoder.invariant_loop d (Array.repeat 8192#usize 0#u8) true 0#usize
      ⦃ fun r => r = (d.size, d.needed, d.«have», true) ⦄ := by
  have hc1 : c1.index.val < 65536 := by scalar_tac
  have hc2 : c2.index.val < 65536 := by scalar_tac
  unfold tacenta_erasure.Decoder.invariant_loop
  apply loop.spec_decr_nat
    (measure := fun p => d.«have».val.length - p.2.2.val)
    (inv := fun p => (p.2.2.val = 0 ∧ p.2.1 = true ∧ p.1 = Array.repeat 8192#usize 0#u8) ∨
      (p.2.2.val = 1 ∧ p.2.1 = true ∧ ∀ w : Nat, w < 8192 →
        (p.1.val[w]!).val = if w = c1.index.val / 8 then 2 ^ (c1.index.val % 8) else 0) ∨
      (p.2.2.val = 2 ∧ p.2.1 = true))
  · rintro ⟨sn, dd, j⟩ hj
    simp only at hj ⊢
    unfold tacenta_erasure.Decoder.invariant_loop.body
    have hlen : d.«have».len.val = 2 := by simp [alloc.vec.Vec.len, hv]
    rcases hj with ⟨hj, h1, h2⟩ | ⟨hj, h1, h2⟩ | ⟨hj, h1⟩
    · rw [h1, h2]
      clear h2
      have hlt : j < d.«have».len := by scalar_tac
      simp only [hlt, if_true]
      step*
      have hw : word.val < 8192 := by
        have : c.index.val < 65536 := by scalar_tac
        simp only [idx_post, UScalar.cast_val_eq] at word_post
        scalar_tac
      have hi3 : i3 = 0#u8 := by
        rw [i3_post]
        simp only [Array.repeat_val, List.getElem_replicate]
      have hi4 : i4 = 0#u8 := by
        apply UScalar.eq_of_val_eq
        rw [i4_post1, hi3]
        simp
      simp only [hi4, bne_self_eq_false, Bool.false_eq_true, if_false]
      step*
      have hc : c = c1 := by
        have h0 : (d.«have».val)[j.val]? = some c := by rw [c_post]; exact List.getElem?_eq_getElem _
        rw [hv, hj] at h0; simpa using h0.symm
      have hidx : idx.val = c1.index.val := by
        rw [idx_post, hc]
        simp only [UScalar.cast_val_eq]
        rcases System.Platform.numBits_eq with h | h <;> simp [h] <;> omega
      have hb : bit.val = 2 ^ (c1.index.val % 8) := by
        rw [bit_post1, i2_post, hidx]
        have : c1.index.val % 8 < 8 := Nat.mod_lt _ (by decide)
        generalize c1.index.val % 8 = r at this ⊢
        interval_cases r <;> simp [U8.size, U8.numBits]
      have hi5 : i5.val = 2 ^ (c1.index.val % 8) := by
        rw [i5_post1, hi3]; simp [hb]
      have hword : word.val = c1.index.val / 8 := by rw [word_post, hidx]
      have hlen2 : (d.«have».val).length = 2 := by rw [hv]; rfl
      refine ⟨Or.inr (Or.inl ⟨by omega, fun w hw' => ?_⟩), by rw [hlen2]; omega⟩
      rw [a_post, Array.set_val_eq, Array.repeat_val]
      simp only [List.getElem!_eq_getElem?_getD]
      by_cases hww : w = c1.index.val / 8
      · subst hww
        rw [← hword, List.getElem?_set_self (by rw [List.length_replicate]; exact hw)]
        simp only [Option.getD_some, hi5, if_true]
      · have : word.val ≠ w := by omega
        rw [List.getElem?_set_ne this, List.getElem?_replicate, if_pos (by simpa using hw')]
        simp only [Option.getD_some, if_neg hww]
        rfl
    · rw [h1]
      have hlt : j < d.«have».len := by scalar_tac
      simp only [hlt, if_true]
      step*
      have hc : c = c2 := by
        have h0 : (d.«have».val)[j.val]? = some c := by rw [c_post]; exact List.getElem?_eq_getElem _
        rw [hv, hj] at h0; simpa using h0.symm
      have hidx : idx.val = c2.index.val := by
        rw [idx_post, hc]
        simp only [UScalar.cast_val_eq]
        rcases System.Platform.numBits_eq with h | h <;> simp [h] <;> omega
      have hword : word.val = c2.index.val / 8 := by rw [word_post, hidx]
      have hw : word.val < 8192 := by omega
      have hb : bit.val = 2 ^ (c2.index.val % 8) := by
        rw [bit_post1, i2_post, hidx]
        have : c2.index.val % 8 < 8 := Nat.mod_lt _ (by decide)
        generalize c2.index.val % 8 = r at this ⊢
        interval_cases r <;> simp [U8.size, U8.numBits]
      have hi3 : i3.val = if word.val = c1.index.val / 8 then 2 ^ (c1.index.val % 8) else 0 := by
        have := h2 word.val hw
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hw)] at this
        rw [i3_post]
        simpa using this
      have hne' : c1.index.val ≠ c2.index.val := fun h => hne (UScalar.eq_of_val_eq h)
      have hi4 : i4 = 0#u8 := by
        apply UScalar.eq_of_val_eq
        rw [i4_post1, UScalar.val_and, hi3, hb]
        split_ifs with hsame
        · have ha : c1.index.val % 8 < 8 := Nat.mod_lt _ (by decide)
          have hb' : c2.index.val % 8 < 8 := Nat.mod_lt _ (by decide)
          have hab : c1.index.val % 8 ≠ c2.index.val % 8 := by omega
          exact pow_and_pow_ne ha hb' hab
        · simp
      simp only [hi4, bne_self_eq_false, Bool.false_eq_true, if_false]
      step*
    · rw [h1]
      have hlt : ¬ j < d.«have».len := by scalar_tac
      simp only [hlt, if_false]
      step*
  · left; exact ⟨rfl, rfl, rfl⟩


/-- A decoder that passes `Decoder::invariant` has `needed` the chunk count of its size, at most `MAX_CODEWORDS`. -/
theorem decoder_invariant_parts (d : tacenta_erasure.Decoder) (h : tacenta_erasure.Decoder.invariant d = ok true) :
    tacenta_erasure.chunk_count d.size = ok d.needed ∧ d.needed.val ≤ 65536 := by
  have hle := Tacenta.SessionUnitDecoderBound.invariant_true_needed_le d h
  unfold tacenta_erasure.Decoder.invariant at h
  obtain ⟨⟨i, i1, v, dist⟩, hloop, h2⟩ := bind_eq_ok_inv h
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
    (Tacenta.SessionUnitDecoderBound.inv_loop_post d (Array.repeat 8192#usize 0#u8) true 0#usize (by simp))
  rw [hloop] at hr
  cases hr
  obtain ⟨hp1, hp2⟩ := hp
  simp only [] at hp1 hp2
  subst hp1 hp2
  obtain ⟨i2, hi2, h3⟩ := bind_eq_ok_inv h2
  by_cases h1 : d.needed = i2
  · subst h1
    exact ⟨hi2, hle⟩
  · rw [if_neg h1] at h3
    simp at h3

/-- `add_chunk` on a decoder holding one chunk keeps its size and `needed`, and leaves the one chunk or adds a
second of a different index (only when `needed` is at least two). -/
theorem add_chunk_one (d d' : tacenta_erasure.Decoder) (c1 c : tacenta_erasure.Chunk) (r : Bool)
    (hv : d.«have».val = [c1]) (h : tacenta_erasure.Decoder.add_chunk d c = ok (r, d')) :
    d' = d ∨ (d'.size = d.size ∧ d'.needed = d.needed ∧ d'.«have».val = [c1, c] ∧ c1.index ≠ c.index ∧
      2 ≤ d.needed.val) := by
  unfold tacenta_erasure.Decoder.add_chunk at h
  by_cases hge : alloc.vec.Vec.len d.«have» ≥ d.needed
  · simp only [hge, if_true, ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Or.inl rfl
  · simp only [hge, if_false] at h
    obtain ⟨⟨b, v⟩, hloop, h⟩ := bind_eq_ok_inv h
    simp at h
    obtain ⟨-, rfl⟩ := h
    have hlen : (alloc.vec.Vec.len d.«have»).val = 1 := by simp [alloc.vec.Vec.len, hv]
    have hn : 2 ≤ d.needed.val := by
      have := (UScalar.le_equiv _ _).not.mp hge
      simp only [not_le] at this
      have : (alloc.vec.Vec.len d.«have»).val < d.needed.val := by scalar_tac
      omega
    unfold tacenta_erasure.Decoder.add_chunk_loop at hloop
    rw [loop.eq_def] at hloop
    simp only [tacenta_erasure.Decoder.add_chunk_loop.body] at hloop
    have h0 : (0#usize : Usize) < alloc.vec.Vec.len d.«have» := by scalar_tac
    have hidx0 : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice tacenta_erasure.Chunk) d.«have» 0#usize =
        ok c1 := by
      rw [alloc.vec.Vec.index_slice_index]; simp [alloc.vec.Vec.index_usize, hv]
    simp only [h0, if_true, hidx0, bind_tc_ok] at hloop
    by_cases heq : c1.index = c.index
    · simp only [heq, if_true, ok.injEq, Prod.mk.injEq] at hloop
      obtain ⟨-, rfl⟩ := hloop
      exact Or.inl rfl
    · simp only [heq, if_false] at hloop
      have h01 : (0#usize : Usize) + 1#usize = ok 1#usize := by
        obtain ⟨z, hz, hzv⟩ := Std.WP.spec_imp_exists (Usize.add_spec (x := 0#usize) (y := 1#usize) (by scalar_tac))
        rw [hz]; congr; apply UScalar.eq_of_val_eq; simp [hzv]
      simp only [h01, bind_tc_ok] at hloop
      rw [loop.eq_def] at hloop
      have h1 : ¬ (1#usize : Usize) < alloc.vec.Vec.len d.«have» := by scalar_tac
      simp only [h1, if_false] at hloop
      rcases hpush : alloc.vec.Vec.push d.«have» c with v1 | e | -
      all_goals (rw [hpush] at hloop; simp at hloop)
      obtain ⟨-, rfl⟩ := hloop
      have := Tacenta.UnitLifecycleEstablishResponder.vec_push_ok hpush
      rw [hv] at this
      exact Or.inr ⟨rfl, rfl, this, heq, hn⟩

/-- **A decoder holding at most two chunks, of distinct indices when two, passes `Decoder::invariant`** when its
`needed` is the chunk count of its size, at most `MAX_CODEWORDS`, and not below the number of chunks held. -/
theorem decoder_invariant_le_two (d : tacenta_erasure.Decoder)
    (hcc : tacenta_erasure.chunk_count d.size = ok d.needed) (hle : d.needed.val ≤ 65536)
    (hn : d.«have».val.length ≤ d.needed.val)
    (hshape : d.«have».val.length ≤ 1 ∨ ∃ c1 c2, d.«have».val = [c1, c2] ∧ c1.index ≠ c2.index) :
    tacenta_erasure.Decoder.invariant d = ok true := by
  rcases hshape with h1 | ⟨c1, c2, hv, hne⟩
  · exact Tacenta.UnitLifecycleResponderSuccessor.decoder_invariant_small d hcc hle h1 hn
  have hloop : tacenta_erasure.Decoder.invariant_loop d (Array.repeat 8192#usize 0#u8) true 0#usize =
      ok (d.size, d.needed, d.«have», true) := by
    obtain ⟨r, hr, hp⟩ := Std.WP.spec_imp_exists (two_chunk_loop d c1 c2 hv hne)
    rw [hr, hp]
  unfold tacenta_erasure.Decoder.invariant
  dsimp only
  rw [hloop]
  have hm : tacenta_erasure.MAX_CODEWORDS.val = 65536 := by simp [tacenta_erasure.MAX_CODEWORDS]
  simp [hcc, hm, hle, hn, alloc.vec.Vec.len]

/-- **One receive's change to a header decoder holding at most one chunk keeps `Decoder::invariant` and the size**:
the decoder as it was, or one `add_chunk` of it. -/
theorem decoder_step_keeps {d d' : tacenta_erasure.Decoder}
    (hinv : tacenta_erasure.Decoder.invariant d = ok true) (hsmall : d.«have».val.length ≤ 1)
    (h : d' = d ∨ ∃ c r, tacenta_erasure.Decoder.add_chunk d c = ok (r, d')) :
    tacenta_erasure.Decoder.invariant d' = ok true ∧ d'.size = d.size := by
  rcases h with rfl | ⟨c, r, hadd⟩
  · exact ⟨hinv, rfl⟩
  obtain ⟨hcc, hle⟩ := decoder_invariant_parts d hinv
  rcases hv : d.«have».val with _ | ⟨c1, _ | ⟨c', rest⟩⟩
  · obtain ⟨hs, hn, hl1, hln⟩ :=
      Tacenta.UnitLifecycleResponderSuccessor.add_chunk_fresh_have d d' c r hv hadd
    refine ⟨decoder_invariant_le_two d' (by rw [hs, hn]; exact hcc) (by rw [hn]; exact hle)
      (by rw [hn]; exact hln) (Or.inl hl1), hs⟩
  · rcases add_chunk_one d d' c1 c r hv hadd with rfl | ⟨hs, hn, hc, hne, h2⟩
    · exact ⟨hinv, rfl⟩
    · refine ⟨decoder_invariant_le_two d' (by rw [hs, hn]; exact hcc) (by rw [hn]; exact hle)
        (by rw [hc, hn]; simp only [List.length_cons, List.length_nil]; omega) (Or.inr ⟨c1, c, hc, hne⟩), hs⟩
  · rw [hv] at hsmall; simp at hsmall

end Decoder

/-! ## The translated agreement receive at `NoHeaderReceived` and `KeysSampled` -/

section BraidReceive

/-- The translated agreement states a receive here leaves in place: `NoHeaderReceived` stays `NoHeaderReceived` and
`KeysSampled` stays `KeysSampled`, each at the same epoch. -/
def SameAgreementKind : tacenta_braid.State → tacenta_braid.State → Prop
  | .NoHeaderReceived e _ _, .NoHeaderReceived e' _ _ => e' = e
  | .KeysSampled e _ _ _, .KeysSampled e' _ _ _ => e' = e
  | _, _ => False

/-- **`Braid::receive` at `KeysSampled` that stays at `KeysSampled` returns the state's clone**: the same epoch,
authenticator and encoder, and the clone of the key pair.  Hypothesis-free. -/
theorem braid_receive_keysSampled (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair)
    (enc : tacenta_erasure.Encoder) (m : tacenta_braid.Msg) (x : U64) (y : Option tacenta_braid.Output)
    (bc : tacenta_braid.Braid)
    (h : tacenta_braid.Braid.receive ⟨tacenta_braid.State.KeysSampled e a kp enc⟩ m = ok (x, y, bc))
    (e' : U64) (a' : tacenta_braid.Auth) (kp2 : tacenta_kem.IncrementalKeyPair) (enc2 : tacenta_erasure.Encoder)
    (hb : bc.state = tacenta_braid.State.KeysSampled e' a' kp2 enc2) :
    e' = e ∧ a' = a ∧ enc2 = enc ∧ tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp = ok kp2 := by
  unfold tacenta_braid.Braid.receive at h
  obtain ⟨st, hst, h⟩ := bind_eq_ok_inv h
  obtain ⟨⟨out, next⟩, hstep, h⟩ := bind_eq_ok_inv h
  have hnext : bc.state = next := by
    rcases out with _ | o
    · obtain ⟨i, -, h⟩ := bind_eq_ok_inv h
      simp only [ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.2]
    · obtain ⟨o1, -, h⟩ := bind_eq_ok_inv h
      simp only [ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.2]
  rw [hnext] at hb
  subst hb
  simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
    bind_tc_ok, Tacenta.UnitLifecycleResponderReply.auth_clone_eq,
    Tacenta.UnitLifecycleSendPreserve.encoder_clone_eq] at hst
  rcases hk : tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp with kp' | _ | _ <;>
    simp only [hk, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hst
  subst hst
  unfold tacenta_braid.Braid.step_receive at hstep
  simp only [tacenta_braid.State.epoch, bind_tc_ok] at hstep
  repeat' first
    | (replace hstep := bind_eq_ok_inv hstep; obtain ⟨_, _, hstep⟩ := hstep)
    | split at hstep
    | (simp only [ok.injEq, Prod.mk.injEq, tacenta_braid.State.KeysSampled.injEq, reduceCtorEq] at hstep
       first
        | (obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hstep; exact ⟨rfl, rfl, rfl, rfl⟩)
        | exact hstep.2.elim)

/-- **`Braid::receive` at `NoHeaderReceived` (holding at most one chunk) or `KeysSampled`, staying in the same kind
at the same epoch, keeps `Braid::invariant`** and the `failed`, `is_initiator`, `epoch` and `state_tag` the session's
structural clauses read.  Under `KemCloneAgrees` (the key pair is cloned at `KeysSampled`). -/
theorem braid_receive_keeps (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees) (b : tacenta_braid.Braid)
    (m : tacenta_braid.Msg) (x : U64) (y : Option tacenta_braid.Output) (bc : tacenta_braid.Braid)
    (h : tacenta_braid.Braid.receive b m = ok (x, y, bc)) (hinv : tacenta_braid.Braid.invariant b = ok true)
    (hsmall : ∀ e a d, b.state = tacenta_braid.State.NoHeaderReceived e a d → d.«have».val.length ≤ 1)
    (hkind : SameAgreementKind b.state bc.state) :
    tacenta_braid.Braid.invariant bc = ok true ∧
      tacenta_braid.Braid.failed bc = tacenta_braid.Braid.failed b ∧
      tacenta_braid.Braid.is_initiator bc = tacenta_braid.Braid.is_initiator b ∧
      tacenta_braid.Braid.epoch bc = tacenta_braid.Braid.epoch b ∧
      tacenta_braid.Braid.state_tag bc = tacenta_braid.Braid.state_tag b ∧
      Tacenta.SessionUnitBraidT1.State.epoch_val bc.state = Tacenta.SessionUnitBraidT1.State.epoch_val b.state := by
  obtain ⟨st⟩ := b
  obtain ⟨st'⟩ := bc
  simp only at hkind hsmall h ⊢
  cases st <;> cases st' <;> simp only [SameAgreementKind] at hkind
  · -- KeysSampled
    rename_i e a kp enc e' a' kp2 enc2
    obtain ⟨-, rfl, rfl, hk⟩ := braid_receive_keysSampled e a kp enc m x y _ h e' a' kp2 enc2 rfl
    subst hkind
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
    unfold tacenta_braid.Braid.invariant at hinv ⊢
    simp only at hinv ⊢
    have hkv : tacenta_braid.key_pair_valid kp = ok true := by
      revert hinv
      generalize tacenta_braid.key_pair_valid kp = r
      intro hr
      repeat' first
        | (replace hr := bind_eq_ok_inv hr; obtain ⟨_, _, hr⟩ := hr)
        | split at hr
        | simp at hr
      all_goals exact hr
    rw [Tacenta.UnitLifecycleSendPreserve.key_pair_valid_clone hkcl hk hkv]
    rw [hkv] at hinv
    exact hinv
  · -- NoHeaderReceived
    rename_i e a d e' a' d'
    subst hkind
    have hd := Tacenta.UnitLifecycleResponderSuccessor.braid_receive_noHeader e' a d m x y _ h e' a' d' rfl
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
    unfold tacenta_braid.Braid.invariant at hinv ⊢
    simp only at hinv ⊢
    have hge' : e' ≥ 1#u64 := by
      by_contra hc
      rw [if_neg hc] at hinv
      simp at hinv
    rw [if_pos hge'] at hinv ⊢
    obtain ⟨bd, hbd, hinv⟩ := bind_eq_ok_inv hinv
    cases bd
    · simp at hinv
    obtain ⟨hdinv, hsize⟩ := decoder_step_keeps hbd (hsmall e' a d rfl) hd
    rw [hdinv]
    simp only [if_true] at hinv ⊢
    simpa [tacenta_braid.decoder_sized, tacenta_erasure.Decoder.impl.size, hsize] using hinv

end BraidReceive

/-! ## The session's own clauses after a receive -/

section Structural

/-- **`Session::structural_invariant` after a receive**: replacing the Triple, the agreement and the ratchet key of a
session that passes it keeps it, when the new ratchet key's public key bytes are the new Triple's sending key, and the
new Triple and agreement agree with the old on the direction, the sparse epoch, `failed`, `is_initiator`, `epoch` and
`state_tag`.  Hypothesis-free beyond those equations. -/
theorem structural_receive (s : lifecycle.Session) (t : tacenta_triple.State) (b : tacenta_braid.Braid)
    (rp : tacenta_boundary.dh.PrivateKey) (hstr : lifecycle.Session.structural_invariant s = ok true)
    (pk : tacenta_boundary.dh.PublicKeyBytes) (hpk : tacenta_boundary.dh.PrivateKey.public_key rp = ok pk)
    (hb : tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok t.classical.dhs_pub)
    (hdir : t.post_quantum.direction = s.triple.post_quantum.direction)
    (hep : t.post_quantum.epoch = s.triple.post_quantum.epoch)
    (hf : tacenta_braid.Braid.failed b = tacenta_braid.Braid.failed s.braid)
    (hi : tacenta_braid.Braid.is_initiator b = tacenta_braid.Braid.is_initiator s.braid)
    (he : tacenta_braid.Braid.epoch b = tacenta_braid.Braid.epoch s.braid)
    (ht : tacenta_braid.Braid.state_tag b = tacenta_braid.Braid.state_tag s.braid) :
    lifecycle.Session.structural_invariant { s with triple := t, braid := b, ratchet_private := rp } = ok true := by
  unfold lifecycle.Session.structural_invariant at hstr ⊢
  obtain ⟨pk0, -, hstr⟩ := bind_eq_ok_inv hstr
  obtain ⟨a0, -, hstr⟩ := bind_eq_ok_inv hstr
  obtain ⟨a1, -, hstr⟩ := bind_eq_ok_inv hstr
  obtain ⟨c, -, hstr⟩ := bind_eq_ok_inv hstr
  cases c
  swap
  · simp at hstr
  simp only [Bool.false_eq_true, if_false] at hstr
  simp only [hpk, hb, bind_tc_ok, tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public,
    Tacenta.UnitHeadroomInvariant.array_ne_self, Bool.false_eq_true, if_false]
  simpa [lifecycle.Session.is_responder, tacenta_triple.State.direction, tacenta_spqr.State.impl.direction,
    tacenta_triple.State.epoch, tacenta_spqr.State.impl.epoch, hdir, hep, hf, hi, he, ht] using hstr

/-- A `true` result of a bind stays `true` when every continuation that returned `true` is replaced by one that also
returns `true`. -/
theorem mono_bind {α : Type} {x : Result α} {f g : α → Result Bool}
    (hfg : ∀ a, f a = ok true → g a = ok true) : (x >>= f) = ok true → (x >>= g) = ok true := by
  rcases x with a | e | _ <;> simp_all

/-- The same for an `if`. -/
theorem mono_ite {c : Prop} [Decidable c] {a b a' b' : Result Bool}
    (ha : a = ok true → a' = ok true) (hb : b = ok true → b' = ok true) :
    (if c then a else b) = ok true → (if c then a' else b') = ok true := by
  split_ifs <;> simp_all

/-- Dropping a leading bind from a `true` result. -/
theorem strip_bind {α : Type} {x : Result α} {f : α → Result Bool} {y : Result Bool}
    (h : ∀ a, f a = ok true → y = ok true) : (x >>= f) = ok true → y = ok true := by
  rcases x with a | e | _
  · exact h a
  · simp
  · simp

/-- Dropping a leading refusing `if` from a `true` result. -/
theorem strip_ite {c : Prop} [Decidable c] {b y : Result Bool} (h : b = ok true → y = ok true) :
    (if c then ok false else b) = ok true → y = ok true := by
  split_ifs <;> simp_all

/-- **Clearing the pending initial message keeps `Session::structural_invariant`**: the clauses on a pending
message (no established ephemeral, the ciphertext length, the ephemeral key canonical) are dropped and every other
clause is read as before.  Hypothesis-free. -/
theorem structural_clear_pending (s : lifecycle.Session)
    (h : lifecycle.Session.structural_invariant s = ok true) :
    lifecycle.Session.structural_invariant { s with pending_initial := none } = ok true := by
  rcases hp : s.pending_initial with _ | p
  · have : { s with pending_initial := none } = s := by rw [← hp]
    rw [this]; exact h
  revert h
  unfold lifecycle.Session.structural_invariant lifecycle.Session.is_responder
  simp only [hp, core.option.Option.is_some, core.option.Option.is_none, Option.isSome_some, Option.isSome_none,
    if_true, Bool.false_eq_true, if_false]
  repeat' first
    | exact id
    | (intro _; rfl)
    | (intro h; simp at h; done)
    | (apply mono_bind; intro _)
    | apply mono_ite
    | split
    | (apply strip_bind; intro _; apply strip_ite)

/-- `Session::structural_invariant` gives clause (a): the ratchet key's public key bytes are the Triple's sending key. -/
theorem clause_a_of_structural (s : lifecycle.Session)
    (h : lifecycle.Session.structural_invariant s = ok true) :
    ∃ pk, tacenta_boundary.dh.PrivateKey.public_key s.ratchet_private = ok pk ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok s.triple.classical.dhs_pub := by
  unfold lifecycle.Session.structural_invariant at h
  obtain ⟨pk0, hpk0, h⟩ := bind_eq_ok_inv h
  obtain ⟨a0, ha0, h⟩ := bind_eq_ok_inv h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok_inv h
  simp only [tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public, ok.injEq] at ha1
  subst ha1
  obtain ⟨c, hc, h⟩ := bind_eq_ok_inv h
  obtain ⟨e, he, hiff⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitT3.array_ne_val a0 s.triple.classical.dhs_pub)
  rw [he] at hc
  simp only [ok.injEq] at hc
  subst hc
  cases e
  · have : a0 = s.triple.classical.dhs_pub := by
      by_contra hne
      exact absurd (hiff.mpr hne) (by simp)
    exact ⟨pk0, hpk0, this ▸ ha0⟩
  · simp at h

end Structural

/-! ## `decrypt_ratchet` and `decrypt` keep the invariant on an in-order receive -/

section Decrypt

open Tacenta.UnitLifecycleSendPreserve (session_invariant_iff)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid dhPublicValid_canonical)

/-- The agreement relation, the model step's `KeepsAgreementState` and the relation after it give the translated
states' `SameAgreementKind`. -/
theorem sameKind_of_refines {K : Model.Braid.Kem} {st st' : tacenta_braid.State} {m m' : Model.Braid.BraidState}
    (hr : Tacenta.SessionUnitBraidT3.StateRefines K st m) (hr' : Tacenta.SessionUnitBraidT3.StateRefines K st' m')
    (hk : KeepsAgreementState m m') : SameAgreementKind st st' := by
  cases m <;> cases m' <;> simp only [KeepsAgreementState] at hk
  all_goals
    cases st <;> simp only [Tacenta.SessionUnitBraidT3.StateRefines] at hr
    cases st' <;> simp only [Tacenta.SessionUnitBraidT3.StateRefines] at hr'
    simp only [SameAgreementKind]
    apply UScalar.eq_of_val_eq
    omega

/-- The code Triple's sending key, read through the relation. -/
theorem keyOf_dhs {t : tacenta_triple.State} {mt : Model.Triple.State}
    (h : Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
      Tacenta.SessionUnitTripleT3.spqrAbs t mt) :
    Tacenta.SessionUnitT3.keyOf t.classical.dhs_pub = mt.classical.dhsPub := by
  have := congrArg Model.State.State.dhsPub h.1
  simpa [Tacenta.SessionUnitTripleT3.ratchetAbs] using this

/-- Two code Triples related to two model Triples agree on the direction and the sparse epoch when the model Triples
do. -/
theorem code_dir_epoch {t t' : tacenta_triple.State} {mt mt' : Model.Triple.State}
    (h : Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
      Tacenta.SessionUnitTripleT3.spqrAbs t mt)
    (h' : Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
      Tacenta.SessionUnitTripleT3.spqrAbs t' mt')
    (hdir : mt'.postQuantum.direction = mt.postQuantum.direction)
    (hep : mt'.postQuantum.epoch = mt.postQuantum.epoch) :
    t'.post_quantum.direction = t.post_quantum.direction ∧ t'.post_quantum.epoch = t.post_quantum.epoch := by
  obtain ⟨-, hq0⟩ := h
  obtain ⟨-, hq1⟩ := h'
  constructor
  · have h1 := congrArg Model.SparseRatchet.State.direction hq1
    have h0 := congrArg Model.SparseRatchet.State.direction hq0
    simp only [Tacenta.SessionUnitTripleT3.spqrAbs] at h1 h0
    have hd : Tacenta.SessionUnitSpqrT3.directionOf t'.post_quantum.direction =
        Tacenta.SessionUnitSpqrT3.directionOf t.post_quantum.direction := by
      rw [h1, h0, hdir]
    revert hd
    cases t'.post_quantum.direction <;> cases t.post_quantum.direction <;>
      simp [Tacenta.SessionUnitSpqrT3.directionOf]
  · have h1 := congrArg Model.SparseRatchet.State.epoch hq1
    have h0 := congrArg Model.SparseRatchet.State.epoch hq0
    simp only [Tacenta.SessionUnitTripleT3.spqrAbs] at h1 h0
    apply UScalar.eq_of_val_eq
    rw [h1, h0, hep]

/-- **`Session::decrypt_ratchet` keeps `Session::invariant` and spends one unit of the counter budget, on an
in-order receive whose agreement stays at `NoHeaderReceived` (holding at most one chunk before the call) or at
`KeysSampled`.**  For every session `s` that passes `Session::invariant`, has room for `k + 1` operations
(`CounterRoom`) and refines a model session `m`, and every successful return `(Ok pt, s', rng')` of
`decrypt_ratchet` there whose session refines a model session `m'` that is an `InOrderReceiveStep` from `m`: `s'`
passes `Session::invariant` and has room for `k` operations.  The relation after the call and the model step are
hypotheses (the decrypt refinement supplies the relation; `decryptRatchet_inOrderStep` shows the model's own step is
such a step); nothing here calls a refinement theorem.  The boundary records are `KemCloneAgrees` (the key pair is
cloned at `KeysSampled`), the oracle's `dhPublic` clause and the view's codec relation (to read the new ratchet key's
public key), and the law `DhPublicValid` (that key's bytes are canonical). -/
theorem decrypt_ratchet_keeps_invariant_in_order (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees)
    (hpub : DhPublicValid) {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (dh : DhView) (codec : DhCodecOf dh) (K : Model.Braid.Kem) (oracle : Model.Lifecycle.Oracle)
    (hdhPublic : ∀ secret, ∃ publicKey, tacenta_boundary.dh.PrivateKey.public_key secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret))
    (s : lifecycle.Session) (m m' : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))
    (hrel : SessionRefines dh K s m)
    (hsmall : ∀ e a d, s.braid.state = tacenta_braid.State.NoHeaderReceived e a d → d.«have».val.length ≤ 1)
    (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.decrypt_ratchet rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng'))
    (hrel' : SessionRefines dh K s' m') (hstep : InOrderReceiveStep oracle m m') :
    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by
  obtain ⟨hstr, htri, hbr⟩ := (session_invariant_iff s).mp hinv
  obtain ⟨msgB, x, y, bc, a, ck, pkb, new, hrecv, -, -, hpkb, hnew, hcases⟩ :=
    Tacenta.UnitLifecycleResponderSuccessor.decrypt_ratchet_ok_parts rc crc s msg rng pt s' rng' hcall
  have hbc : s'.braid = bc := by rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
  -- the agreement half
  have hkind : SameAgreementKind s.braid.state bc.state :=
    sameKind_of_refines hrel.braid (hbc ▸ hrel'.braid) hstep.1
  obtain ⟨hbinv, hf, hi, he, ht, -⟩ := braid_receive_keeps hkcl s.braid msgB x y bc hrecv hbr hsmall hkind
  -- the model's step: direction, sparse epoch, and the sending key
  obtain ⟨hdirM, hepM, hdhsM⟩ := step_frame oracle hstep
  obtain ⟨hdir, hep⟩ := code_dir_epoch hrel.triple hrel'.triple hdirM hepM
  have hk0 := keyOf_dhs hrel.triple
  have hk1 := keyOf_dhs hrel'.triple
  -- clause (a) at the session the call returns
  have ha : ∃ pk, tacenta_boundary.dh.PrivateKey.public_key s'.ratchet_private = ok pk ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok s'.triple.classical.dhs_pub := by
    rcases hcases with ⟨hne, hs'⟩ | ⟨hsame, hs'⟩
    · have hrp : s'.ratchet_private = ck := by rw [hs']
      have hneM : m'.triple.classical.dhsPub ≠ m.triple.classical.dhsPub := by
        rw [← hk0, ← hk1]
        exact fun h => hne (keyOf_injective h)
      have hM := hdhsM hneM
      obtain ⟨pk, hpk, hpkv⟩ := hdhPublic ck
      rw [hpkb] at hpk
      cases hpk
      obtain ⟨b, hb, hbv⟩ := codec.asBytes pkb
      rw [hnew] at hb
      cases hb
      have hd : s'.triple.classical.dhs_pub = new := by
        apply keyOf_injective
        show Tacenta.SessionUnitT3.keyOf _ = arrayOf new
        rw [hk1, hM, ← hrel'.ratchetPrivate, hrp, ← hpkv, hbv]
      rw [hrp, hd]
      exact ⟨pkb, hpkb, hnew⟩
    · have hrp : s'.ratchet_private = s.ratchet_private := by rw [hs']
      rw [hrp, hsame]
      exact clause_a_of_structural s hstr
  obtain ⟨pk', hpk', hb'⟩ := ha
  have hcan' : Tacenta.SessionUnitT1.canonicalX25519 s'.triple.classical.dhs_pub = true :=
    dhPublicValid_canonical hpub hpk' hb'
  -- the Triple half, through the model
  have hmodel := (triple_invariant_iff_model hrel.triple).mp htri
  have hmodel' : ModelTripleInv m'.triple := by
    rcases hstep.2 with ⟨htr, -⟩ | ⟨hdr, dr, ds, cand, mk, hord, hcanH, hs, hrp⟩
    · rw [htr]; exact hmodel
    · refine modelTripleInv_receive_inOrder hmodel hcanH (fun hd => ?_) hord hs
      obtain ⟨⟨k1, hc⟩, -⟩ := triple_receive_parts hord hs
      obtain ⟨-, hdh, -, -⟩ := ratchet_receive_frame hord.noStoredClassical hord.sameChain hord.newChain hc
      rw [← hdh hd, ← hk1, canonicalKey_keyOf]
      exact hcan'
  have htri' : tacenta_triple.State.invariant s'.triple = ok true :=
    (triple_invariant_iff_model hrel'.triple).mpr hmodel'
  -- the session's own clauses
  have hs'eq : s' = { s with triple := s'.triple, braid := bc, ratchet_private := s'.ratchet_private } := by
    rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
  have hstr' : lifecycle.Session.structural_invariant s' = ok true := by
    rw [hs'eq]
    exact structural_receive s s'.triple bc s'.ratchet_private hstr pk' hpk' hb' hdir hep hf hi he ht
  refine ⟨(session_invariant_iff s').mpr ⟨hstr', htri', hbc ▸ hbinv⟩, ?_⟩
  -- the budget
  exact (counterRoom_iff_model hrel' k).mpr
    (modelCounterRoom_receive oracle k hstep ((counterRoom_iff_model hrel (k + 1)).mp hroom))

/-- **A successful `decrypt` is a successful `decrypt_ratchet` of some inner message, with the pending initial
message cleared**: the frame itself, or the message a recognised repeated initial message carries.  Hypothesis-free. -/
theorem decrypt_ok_inner {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (s : lifecycle.Session) (msg : Slice U8) (rng : R) (v : alloc.vec.Vec U8) (s'' : lifecycle.Session) (r : R)
    (h : lifecycle.Session.decrypt rc crc s msg rng = ok (core.result.Result.Ok v, s'', r)) :
    ∃ inner s1, lifecycle.Session.decrypt_ratchet rc crc s inner rng = ok (core.result.Result.Ok v, s1, r) ∧
      s'' = { s1 with pending_initial := none } := by
  unfold lifecycle.Session.decrypt at h
  repeat' first
    | (obtain ⟨⟨r1, s1, rng1⟩, hdr, h⟩ := bind_eq_ok_inv h
       rcases r1 with v1 | e1
       · obtain ⟨cf, hcf, h⟩ := bind_eq_ok_inv h
         simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf
         subst hcf
         simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         exact ⟨_, s1, hdr, rfl⟩
       · obtain ⟨cf, hcf, h⟩ := bind_eq_ok_inv h
         simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf
         subst hcf
         obtain ⟨r2, hr2, h⟩ := bind_eq_ok_inv h
         simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hr2
         subst hr2
         simp at h)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_inv h)
    | (split at h)
    | (simp at h)

/-- **`Session::decrypt` keeps `Session::invariant` and spends one unit of the counter budget, on an in-order
receive**: as `decrypt_ratchet_keeps_invariant_in_order`, for the public call, whose success is a successful inner
`decrypt_ratchet` with the pending initial message cleared (`decrypt_ok_inner`), and whose session after the call
refines a model session that is an `InOrderReceiveStep` from `m` (the step reads only the Triple, the agreement and
the ratchet key, so it does not see the cleared pending message). -/
theorem decrypt_keeps_invariant_in_order (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees)
    (hpub : DhPublicValid) {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (dh : DhView) (codec : DhCodecOf dh) (K : Model.Braid.Kem) (oracle : Model.Lifecycle.Oracle)
    (hdhPublic : ∀ secret, ∃ publicKey, tacenta_boundary.dh.PrivateKey.public_key secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret))
    (s : lifecycle.Session) (m m' : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))
    (hrel : SessionRefines dh K s m)
    (hsmall : ∀ e a d, s.braid.state = tacenta_braid.State.NoHeaderReceived e a d → d.«have».val.length ≤ 1)
    (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.decrypt rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng'))
    (hrel' : SessionRefines dh K s' m') (hstep : InOrderReceiveStep oracle m m') :
    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by
  obtain ⟨inner, s1, hin, rfl⟩ := decrypt_ok_inner rc crc s msg rng pt s' rng' hcall
  have hw := Tacenta.UnitLifecycleAtomicity.decrypt_ratchet_ok_writes rc crc s inner rng pt s1 rng' hin
  have hpend : s1.pending_initial = s.pending_initial := by rw [hw]
  have hrel1 : SessionRefines dh K s1 { m' with pendingInitial := m.pendingInitial } :=
    ⟨hrel'.triple, hrel'.braid, hrel'.ratchetPrivate, hrel'.identityAd, hrel'.ourIdentityPublic,
      hrel'.peerIdentityPublic, by rw [hpend]; exact hrel.pendingInitial, hrel'.establishedEphemeral⟩
  obtain ⟨hinv1, hroom1⟩ := decrypt_ratchet_keeps_invariant_in_order hkcl hpub rc crc dh codec K oracle hdhPublic
    s m _ k hinv hroom hrel hsmall inner rng pt s1 rng' hin hrel1 hstep
  obtain ⟨hstr1, htri1, hbr1⟩ := (session_invariant_iff s1).mp hinv1
  obtain ⟨r1, r2, r3, r4⟩ := hroom1
  exact ⟨(session_invariant_iff _).mpr ⟨structural_clear_pending s1 hstr1, htri1, hbr1⟩, ⟨r1, r2, r3, r4⟩⟩

/-- **`Session::decrypt` keeps `Session::invariant` and spends one unit of the counter budget, at the model's own
`decrypt` step**: `decrypt_keeps_invariant_in_order` with the relation after the call taken at
`Model.Lifecycle.decrypt` of a message the model's dispatch passes on, every header of which is in order for `m`'s
Triple and leaves `m`'s agreement at `NoHeaderReceived` or `KeysSampled` (`decrypt_inOrderStep`). -/
theorem decrypt_keeps_invariant_model_step (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees)
    (hpub : DhPublicValid) {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (dh : DhView) (codec : DhCodecOf dh) (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle)
    (hdhPublic : ∀ secret, ∃ publicKey, tacenta_boundary.dh.PrivateKey.public_key secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret))
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))
    (hrel : SessionRefines dh K s m)
    (hsmall : ∀ e a d, s.braid.state = tacenta_braid.State.NoHeaderReceived e a d → d.«have».val.length ≤ 1)
    (msg : Slice U8) (msgM inner : Model.Lifecycle.Bytes)
    (hdisp : Model.Lifecycle.dispatchDecrypt oracle m msgM = .ok inner)
    (hkeep : KeepsAgreementState m.braid m.braid)
    (hord : ∀ c ct, Model.CompositeHeader.decodeDetailed inner = .ok (c, ct) →
      InOrder m.triple (Model.Lifecycle.tripleHeaderOf c) ∧
      KeepsAgreementState m.braid
        (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.2)
    (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.decrypt rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng'))
    (hrel' : SessionRefines dh K s' (Model.Lifecycle.decrypt view oracle m msgM).session) :
    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k :=
  decrypt_keeps_invariant_in_order hkcl hpub rc crc dh codec K oracle hdhPublic s m _ k hinv hroom hrel hsmall msg
    rng pt s' rng' hcall hrel' (decrypt_inOrderStep view oracle m msgM inner hdisp hkeep hord)

end Decrypt

/-! ## On the runs: the two receipts are in-order steps -/

section RunSteps
open Model.State (Key)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstSenderTriple firstReceiverTriple firstHeader firstKey
  senderAfterFirst receiverAfterFirst firstReceiptSession first_receive_key)
open Tacenta.UnitLifecycleResponderReplyReceipt (initiatorAfterReply replyReceiptSession reply_receive_key)

/-- **The responder's model step on the initiator's first frame is an in-order receive step**: from a model session
whose Triple is the receiver pair form (root `ec'`) and whose agreement waits for the header at epoch 1, the session
`firstReceiptSession` of the receipt (at any root `ec` with the same root step on `d` as `ec'`) is an
`InOrderReceiveStep`: one Diffie-Hellman step on the frame's key `a4`, nothing skipped, the sparse chain stepped once,
the agreement still waiting for the header.  Model only. -/
theorem firstReceipt_inOrderStep (oracle : Model.Lifecycle.Oracle) (mB : Model.Lifecycle.Session)
    (b ec ec' prk k1 k2 a4 d dSend rkA cksA c : Key) (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk)
    (auth : Model.Braid.Auth) (dec : Model.Braid.Decoder)
    (hB : mB.triple = firstReceiverTriple b ec' prk k1 k2)
    (hbraid : mB.braid = .noHeaderReceived 1 auth dec)
    (hkdf : Model.State.kdfRk ec d .tacenta = (rkA, cksA)) (hkdf' : Model.State.kdfRk ec' d .tacenta = (rkA, cksA))
    (hcan : Model.Messages.canonicalKey a4 = true) :
    InOrderReceiveStep oracle mB
      (firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend (oracle.dhPublic c) c) := by
  have hrecv := first_receive_key b ec' prk k1 k2 a4 d dSend (oracle.dhPublic c) rkA cksA hkdf'
  have heq : receiverAfterFirst ec prk k1 k2 a4 d dSend (oracle.dhPublic c) =
      receiverAfterFirst ec' prk k1 k2 a4 d dSend (oracle.dhPublic c) := by
    simp only [receiverAfterFirst, hkdf, hkdf']
  refine ⟨?_, Or.inr ⟨firstHeader a4, d, dSend, c, firstKey cksA k1, ?_, hcan, ?_, ?_⟩⟩
  · simp [firstReceiptSession, hbraid, KeepsAgreementState]
  · rw [hB]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Model.Ratchet.trySkipped, firstReceiverTriple]
    · simp [firstReceiverTriple]
    · intro _; simp [firstReceiverTriple, firstHeader]
    · simp [Model.SparseRatchet.trySkipped, firstReceiverTriple]
    · intro cs ch hf hr
      simp [Model.SparseRatchet.findChains, firstReceiverTriple, firstHeader] at hf
      subst hf
      simp at hr
      subst hr
      simp [firstHeader]
  · simp only [firstReceiptSession]
    rw [hB, heq]
    exact hrecv
  · simp [firstReceiptSession, receiverAfterFirst]

/-- **The initiator's model step on the responder's reply is an in-order receive step**: from a model session whose
Triple is the sender after its first message and whose agreement is at `keysSampled`, the session
`replyReceiptSession` of the reply's receipt on a ratchet key `newPub` that is canonical and not the peer key the
sender holds is an `InOrderReceiveStep`: one Diffie-Hellman step, nothing skipped, the sparse chain stepped once, the
agreement unchanged.  Model only. -/
theorem replyReceipt_inOrderStep (oracle : Model.Lifecycle.Oracle) (mA : Model.Lifecycle.Session)
    (a4 peer rkA cksA prk k1 k2 dSend x newPub c : Key) (e : Nat) (auth : Model.Braid.Auth)
    (dk ekVector : Model.Braid.Bytes) (enc : Model.Braid.Encoder)
    (hA : mA.triple = senderAfterFirst a4 peer rkA cksA prk k1 k2)
    (hbraid : mA.braid = .keysSampled e auth dk ekVector enc)
    (hne : newPub ≠ peer) (hcan : Model.Messages.canonicalKey newPub = true) :
    InOrderReceiveStep oracle mA
      (replyReceiptSession mA rkA prk k1 k2 dSend x newPub (oracle.dhPublic c) c) := by
  refine ⟨?_, Or.inr ⟨firstHeader newPub, dSend, x, c, firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2,
    ?_, hcan, ?_, ?_⟩⟩
  · simp [replyReceiptSession, hbraid, KeepsAgreementState]
  · rw [hA]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Model.Ratchet.trySkipped, senderAfterFirst]
    · intro _; simp [senderAfterFirst, firstHeader]
    · intro _; simp [senderAfterFirst, firstHeader]
    · simp [Model.SparseRatchet.trySkipped, senderAfterFirst]
    · intro cs ch hf hr
      simp [Model.SparseRatchet.findChains, senderAfterFirst, firstHeader] at hf
      subst hf
      simp at hr
      subst hr
      simp [firstHeader]
  · simp only [replyReceiptSession]
    rw [hA]
    exact reply_receive_key a4 peer rkA cksA prk k1 k2 dSend x newPub _ hne
  · simp [replyReceiptSession, initiatorAfterReply, hA, senderAfterFirst]

end RunSteps

/-! ## On the run: the initiator's receipt of the reply keeps the invariant -/

section Run

open Tacenta.UnitLifecycleT3 (KemView vecOf sliceOf OracleOf BraidSendRefinementContracts
  TripleSendRefinementContracts CodewordViewSendOf ZeroizingRoundTrips)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstKey senderAfterFirst DhAgreeContributory AeadRoundTrip)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid establishedModelOf)
open Tacenta.UnitLifecycleResponderReplyReceipt (replyReceiptSession)

/-- **The budget at the model session after the initiator's first send**: clock 0, sparse epoch 0, sparse chain
counters 1 and 0, agreement epoch 1, so room for `j + 1` operations whenever `j + 2 < u32::MAX`.  Model only. -/
theorem modelCounterRoom_afterFirstSend (mA : Model.Lifecycle.Session) (a4 peer rkA cksA prk k1 k2 : Model.State.Key)
    (auth : Model.Braid.Auth) (dk ekVector : Model.Braid.Bytes) (enc : Model.Braid.Encoder) (j : Nat)
    (hA : mA.triple = senderAfterFirst a4 peer rkA cksA prk k1 k2)
    (hbraid : mA.braid = .keysSampled 1 auth dk ekVector enc) (hj : j + 2 < Std.U32.max) :
    ModelCounterRoom mA (j + 1) := by
  have h32 : Std.U32.max = 4294967295 := by simp [Std.U32.max_eq]
  have h64 : Std.U64.max = 18446744073709551615 := by simp [Std.U64.max_eq]
  rw [h32] at hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hA]; simp only [senderAfterFirst]; omega
  · rw [hA]; simp only [senderAfterFirst]; omega
  · rw [hA]
    simp only [senderAfterFirst, List.mem_singleton]
    rintro q rfl ch (h | h) <;> (simp at h; subst h; simp only; omega)
  · rw [hbraid]; simp only [Model.Braid.BraidState.epoch]; omega

/-- **The initiator's receipt of the reply keeps `Session::invariant` and the four ceilings, on the run of the
initiator's first send.**  Under the hypotheses of `initiator_receives_reply` and no other: the responder's `encrypt` at
`sB'` returns `bytesR`, the initiator's public `decrypt` of those bytes at the session `s'` its first send left, from
`rng'`, returns `Ok ptA` (the bytes of `ptR`) and a session `s''` that passes `Session::invariant`, meets the four ceilings
(`CounterHeadroom`), has room for every `j` with `j + 2 < u32::MAX` further operations (`CounterRoom`), and refines
`replyReceiptSession`.  Derived on the run: the call and the relation after it are `initiator_receives_reply`'s, the
invariant and the relation at `s'` are `established_encrypt_successor_hypotheses`' on the same first send, the budget at
`s'` is read off the model session the first send leaves, and `decrypt_keeps_invariant_in_order` composes them at the
agreement state `KeysSampled`, the model step being an in-order step (`replyReceipt_inOrderStep`).  No compiler-trust
axiom (the pin): the nine `native_decide` constants of the refinements it applies are kernel proofs since 2026-10-21. -/
theorem initiator_receives_reply_successor [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E) (ourA : lifecycle.Identity)
    (bundleA : lifecycle.PublishedBundle) (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
    (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE ourA bundleA expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (q : InitiatorSecretParts rcE crcE ourA bundleA) (hq : s = q.session)
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws) (d1 d2 : Model.Lifecycle.Key)
    (rest : List Model.Lifecycle.Key) (hdraws : trace rng = d1 :: d2 :: rest)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng = ok (core.result.Result.Ok bytes, s', rng'))
    (contractsA : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (agreementsA : DecryptRatchetAgreements oracle.braidKem)
    (dA : Model.Lifecycle.Key) (restA : List Model.Lifecycle.Key) (hdrawA : trace rng' = dA :: restA)
    (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (traceB : F → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : OracleOf rcB crcB dh kem traceB oracleB)
    (braidB : BraidSendRefinementContracts rcB oracleB.braidKem)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundleA)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundleA.kem_prekey_id q.kemCiphertext q.kemSecret)
    (rngB : F) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (storeB' : lifecycle.PrekeyStore) (rngB' : F)
    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB'))
    (ptR : Slice Std.U8) (hroomR : 102 + (ptR.val.length + 48) ≤ Usize.max) (rngR : F)
    (hfreshB : oracleB.dhPublic dB ≠ arrayOf q.peerRatchetBytes) :
    ∃ (dSend x : Model.Lifecycle.Key) (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session)
      (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' : R),
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' =
        ok (core.result.Result.Ok ptA, s'', rngA') ∧
      ptA.val = ptR.val ∧
      lifecycle.Session.invariant s'' = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s'' ∧
      (∀ j, j + 2 < Std.U32.max → CounterRoom s'' j) ∧
      SessionRefines dh oracle.braidKem s''
        (replyReceiptSession
          (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
          (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
          (oracleB.dhPublic dB) (oracle.dhPublic dA) dA) := by
  -- the receipt on the run: the reply, the call and the relation after it
  obtain ⟨dSend, x, bytesR, sB'', ptA, s'', rngA', -, -, hcallR, -, hcallA, hpt, -, -, -, hsess⟩ :=
    Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply rc crc trace dh kem view oracle braid triple
      aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected
      rng0 rng1 s h q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall contractsA agreementsA dA
      restA hdrawA rcB crcB contracts hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB
      storeB hpublish hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR
      rngR hfreshB
  -- the key generation at the first send's two draws, from the reply's run
  obtain ⟨-, -, -, dk, ekSeed, ekVector, -, -, hkg, -⟩ :=
    Tacenta.UnitLifecycleResponderReply.initiator_first_send_responder_replies rc crc trace dh kem view oracle braid
      triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA
      expected rng0 rng1 s h q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall rcB crcB contracts
      hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish hidentity
      hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR rngR
  -- the session the first send left: invariant, relation, on the same first send
  obtain ⟨hinv, hrel, -, -⟩ :=
    Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_hypotheses rc crc trace dh kem view
      oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct hbound hpub hoeq
      agreementsA.kemLen agreementsA.validateEk hsizes contracts.divCeilValue rcE crcE ourA bundleA expected rng0
      rng1 s h plaintext hroom rng htrace ⟨d1, d2, rest, hdraws⟩ bytes s' rng' hcall
  subst hq
  obtain ⟨encoder, hmA⟩ := Tacenta.UnitLifecycleResponderReplyReceipt.first_send_model_session dh view oracle q
    (sliceOf plaintext) d1 d2 rest (htrace.symm.trans hdraws) dk ekSeed ekVector hkg
  set mA := (Model.Lifecycle.encrypt view oracle (establishedModelOf dh q.session) (sliceOf plaintext)).session
    with hmAdef
  have hA : mA.triple = senderAfterFirst (arrayOf q.ratchetBytes) (arrayOf q.peerRatchetBytes) (arrayOf q.rootKey)
      (arrayOf q.sendChain) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) := by
    rw [hmA]
  have hbraid : mA.braid = .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector encoder := by
    rw [hmA]
  -- the reply's ratchet key is canonical
  obtain ⟨-, -, -, b, -, -, -, -, -, hcan, -, hnew⟩ :=
    Tacenta.UnitLifecycleResponderReplyReceipt.fresh_public_of_draw hpub codec
      (DecryptOracleOf.of_oracleOf oracleOfB) rngB dB restB hdrawB
  have hcanM : Model.Messages.canonicalKey (oracleB.dhPublic dB) = true := by
    rw [hnew]; exact Tacenta.UnitLifecycleResponderFirstFrame.canonicalKey_arrayOf b hcan
  -- the model's step is an in-order receive step
  have hstep := replyReceipt_inOrderStep oracle mA (arrayOf q.ratchetBytes) (arrayOf q.peerRatchetBytes)
    (arrayOf q.rootKey) (arrayOf q.sendChain) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
    dSend x (oracleB.dhPublic dB) dA 1 _ dk ekVector encoder hA hbraid hfreshB hcanM
  -- the agreement at s' is at KeysSampled, so the decoder scope is empty there
  have hsmall : ∀ e a d, s'.braid.state = tacenta_braid.State.NoHeaderReceived e a d →
      d.«have».val.length ≤ 1 := by
    intro e a d hst
    have hb := hrel.braid
    rw [hst, hbraid] at hb
    simp [Tacenta.SessionUnitBraidT3.StateRefines] at hb
  -- the budget at s'
  have hroomA : ∀ j, j + 2 < Std.U32.max → CounterRoom s' (j + 1) := fun j hj =>
    (counterRoom_iff_model hrel (j + 1)).mpr
      (modelCounterRoom_afterFirstSend mA _ _ _ _ _ _ _ _ dk ekVector encoder j hA hbraid hj)
  -- the general preservation, at KeysSampled
  have key : ∀ j, j + 2 < Std.U32.max → lifecycle.Session.invariant s'' = ok true ∧ CounterRoom s'' j :=
    fun j hj => decrypt_keeps_invariant_in_order agreementsA.kemClone hpub rc crc dh codec oracle.braidKem oracle
      oracleOf.dhPublic s' mA _ j hinv (hroomA j hj) hrel hsmall _ rng' ptA s'' rngA' hcallA hsess hstep
  have h0 : (0 : Nat) + 2 < Std.U32.max := by simp [Std.U32.max_eq]
  exact ⟨dSend, x, bytesR, sB'', ptA, s'', rngA', hcallR, hcallA, hpt, (key 0 h0).1,
    (counterRoom_zero s'').mp (key 0 h0).2, fun j hj => (key j hj).2, hsess⟩

end Run

/-! ## Regression: the responder's session after the first frame, by preservation -/

section Regression

variable {RA : Type} {rcA : rand_core_1.RngCore RA} {crcA : rand_core_1.CryptoRng RA}
  {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}

open Tacenta.UnitLifecycleT3 (vecOf sliceOf modelChunkOf modelCodewordOf CodewordViewSendOf)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid establishedModelOf dhPublicValid_canonical)
open Tacenta.UnitLifecycleEstablishedEncrypt (firstFrame initialWire)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees responder_first_frame_prepares)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstKey firstReceiptSession DhAgreeContributory AeadRoundTrip
  parts_of_first_frame responder_first_frame_inner_succeeds establish_responder_commit_of_inner first_init_pair
  responder_triple_first first_kdf_model zeroized_eq)
open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts responderModelOf)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)
open Tacenta.UnitHeadroomInvariant (OptionEqU64Shape)

/-- **Room for one operation at the responder's prepared session**: clock 0, sparse epoch 0, chain counters 0,
agreement epoch 1.  Hypothesis-free. -/
theorem counterRoom_responder_prepared {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore}
    {msg : Slice U8} (p : ResponderPreparedParts ourB storeB msg) : CounterRoom p.session 1 := by
  obtain ⟨rk, prk, c1, c2, htriple⟩ := Tacenta.UnitLifecycleEstablishResponder.init_receiver_ok _ _ _ p.hTriple
  obtain ⟨auth, d, -, hbraid⟩ := Tacenta.UnitLifecycleEstablishResponder.braid_responder_ok _ _ p.hBraid
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [ResponderPreparedParts.session, htriple, Tacenta.UnitLifecycleEstablishResponder.responderTriple,
      U32.max_eq]
  · simp [ResponderPreparedParts.session, htriple, Tacenta.UnitLifecycleEstablishResponder.responderTriple,
      U64.max_eq]
  · intro q hq ch hch
    simp [ResponderPreparedParts.session, htriple, Tacenta.UnitLifecycleEstablishResponder.responderTriple,
      Tacenta.UnitLifecycleEstablishResponder.responderChains, Tacenta.UnitHeadroomSatisfiable.vecOf] at hq
    subst hq
    rcases hch with h | h <;> (simp at h; subst h; simp [U64.max_eq])
  · simp only [ResponderPreparedParts.session, hbraid, Tacenta.SessionUnitBraidT1.State.epoch_val]
    scalar_tac

/-- The responder's prepared agreement holds a fresh header decoder: no chunk. -/
theorem prepared_decoder_empty {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts ourB storeB msg) (e : U64) (a : tacenta_braid.Auth) (d : tacenta_erasure.Decoder)
    (h : p.session.braid.state = tacenta_braid.State.NoHeaderReceived e a d) : d.«have».val.length ≤ 1 := by
  obtain ⟨auth, d0, hd0, hbraid⟩ := Tacenta.UnitLifecycleEstablishResponder.braid_responder_ok _ _ p.hBraid
  obtain ⟨hv, n, needed, -, -, -, -, hd⟩ := Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_ok d0 hd0
  have : p.session.braid = p.braid := rfl
  rw [this, hbraid] at h
  simp only [tacenta_braid.State.NoHeaderReceived.injEq] at h
  obtain ⟨-, -, rfl⟩ := h
  rw [hd]
  simp

/-- **The responder's session after the initiator's first frame, by preservation.**  Under the hypotheses of
`responder_first_frame_successor`, at every return `Ok (sB', ptB)` of `establish_responder`, the conclusion of that theorem:
`sB'` refines `firstReceiptSession`, passes `Session::invariant` and meets `CounterHeadroom`.  Here the invariant and the
ceilings are derived from the prepared session's invariant (`responder_prepared_invariant`) and its room for one
operation through `decrypt_ratchet_keeps_invariant_in_order` at `NoHeaderReceived` with an empty decoder, the inner call
and the relation after it being `responder_first_frame_inner_succeeds`', the model step an in-order step
(`firstReceipt_inOrderStep`); `responder_first_frame_successor` gets them by fixing the session's shape.  No compiler-trust
axiom (the pin). -/
theorem responder_successor_via_preservation [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type}
    (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {dh : DhView} (codec : DhCodecOf dh) (view : Model.Lifecycle.CodewordView)
    (oracleA : Model.Lifecycle.Oracle) (hsealA : Tacenta.UnitOracleShape.AeadSealClause Interp.real oracleA)
    (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (q : InitiatorSecretParts rcA crcA our bundle) (pending : Model.Lifecycle.PendingInitial)
    (hpend : (establishedModelOf dh q.session).pendingInitial = some pending)
    (plaintext : Slice U8) (hroom : plaintext.val.length + 48 ≤ Usize.max)
    (src : Model.Lifecycle.Bytes) (hsrc : src.length = Model.Braid.headerSize + Model.Braid.macSize)
    (c : tacenta_erasure.Chunk) (hcw : Tacenta.SessionUnitBraidT3.CodewordOf src c)
    (hsend : view.send (establishedModelOf dh q.session).braid (modelChunkOf src c) = modelCodewordOf c)
    (msg : Slice U8)
    (hmsg : sliceOf msg = initialWire (establishedModelOf dh q.session) pending
      (firstFrame view oracleA (establishedModelOf dh q.session) (sliceOf plaintext)
        (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) (modelChunkOf src c)))
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundle)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundle.kem_prekey_id q.kemCiphertext q.kemSecret)
    (rngB : E) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (storeB' : lifecycle.PrekeyStore) (rngB' : E)
    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB')) :
    ∃ (p : ResponderPreparedParts ourB storeB msg) (ec : Array U8 32#usize) (dSend : Model.Lifecycle.Key),
      SessionRefines dh oracleB.braidKem sB'
        (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)
          (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
          (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) ∧
      lifecycle.Session.invariant sB' = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' := by
  rcases responder_first_frame_prepares rcB crcB contracts hpub hsym hrt hct hbound codec q pending hpend _ msg
      hmsg ourB storeB hpublish hidentity hdistinct hkem rngB with ⟨-, e, -, hrefuse⟩ |
    ⟨p, -, -, h3, -, h5, -, -, h8, -⟩
  · rw [hrefuse] at hcallB
    cases hcallB
  obtain ⟨-, -, hsp, hop⟩ := parts_of_first_frame contracts.decrypt.braid.zeroizingArray hpub codec hct
    hbound q pending hpend _ msg hmsg ourB storeB hpublish hidentity p
  obtain ⟨ec, dSend, ptB0, sB0, rngB0, hkdfr, -, hinner, -, -, hrel⟩ :=
    responder_first_frame_inner_succeeds rcB crcB contracts hpub hsym hcon haead hoeq codec view oracleA hsealA
      traceB oracleB oracleOfB agreements q plaintext hroom src hsrc c hcw hsend p h3 h5 hsp hop h8 rngB
      htraceB dB restB hdrawB
  obtain ⟨storeB0, -, hout⟩ := establish_responder_commit_of_inner rcB crcB p rngB ptB0 sB0 rngB0 hinner _ hcallB
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at hout
  obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ := hout
  -- the prepared session: invariant, relation, budget, an empty decoder
  have hinvP := Tacenta.UnitLifecycleEstablishResponder.responder_prepared_invariant hpub hoeq
    contracts.divCeilValue contracts.decrypt.braid.headerLen p
  have hrelP : SessionRefines dh oracleB.braidKem p.session (responderModelOf dh p) :=
    Tacenta.UnitLifecycleEstablishResponder.sessionRefines_responder_prepared agreements.erasure agreements.kemLen
      agreements.hkdf contracts.decrypt.braid.zeroizingArray contracts.divCeilValue dh p
  -- the model's step on the frame is an in-order receive step
  obtain ⟨ec', hkdfr', htrip⟩ := first_init_pair q.sharedSlice q.ratchetBytes q.peerRatchetBytes q.dhOutBytes
    p.ratchetBytes q.rootKey q.sendChain q.sparseRoot q.sparseSend q.sparseReceive p.triple q.hTriple
    (by rw [← h3]; exact p.hTriple)
  have hB := responder_triple_first dh p ec' q.sparseRoot q.sparseSend q.sparseReceive htrip
  have hdo : q.dhOutBytes = q.dhOut :=
    zeroized_eq contracts.decrypt.braid.zeroizingArray q.hDhOutZ q.hDhOutBytes
  have hkdf := first_kdf_model agreements.hkdf agreements.zeroizing64 hkdfr
  have hkdf' := first_kdf_model agreements.hkdf agreements.zeroizing64 hkdfr'
  rw [hdo] at hkdf hkdf'
  have hcanA : Model.Messages.canonicalKey (arrayOf q.ratchetBytes) = true :=
    Tacenta.UnitLifecycleResponderFirstFrame.canonicalKey_arrayOf _
      (dhPublicValid_canonical hpub q.hRatchetPublic q.hRatchetBytes)
  have hstep := firstReceipt_inOrderStep oracleB (responderModelOf dh p) (arrayOf p.ratchetBytes) (arrayOf ec)
    (arrayOf ec') (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) (arrayOf q.ratchetBytes)
    (arrayOf q.dhOut) dSend (arrayOf q.rootKey) (arrayOf q.sendChain) dB (sliceOf p.braidSecret) (modelChunkOf src c)
    _ _ hB rfl hkdf hkdf' hcanA
  -- the general preservation, at NoHeaderReceived
  obtain ⟨hinv, hroom0⟩ := decrypt_ratchet_keeps_invariant_in_order agreements.kemClone hpub rcB crcB dh codec
    oracleB.braidKem oracleB oracleOfB.dhPublic p.session (responderModelOf dh p) _ 0 hinvP
    (counterRoom_responder_prepared p) hrelP (prepared_decoder_empty p) p.message rngB _ _ _ hinner hrel hstep
  exact ⟨p, ec, dSend, hrel, hinv, (counterRoom_zero _).mp hroom0⟩

end Regression

end Tacenta.UnitLifecycleReceivePreserve

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.skip_noop' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.skip_noop

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.ratchet_receive_inOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.ratchet_receive_inOrder

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.spqr_receive_inOrder' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.spqr_receive_inOrder

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.classicalTail_ok' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.classicalTail_ok

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.modelRatchetInv_tail' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.modelRatchetInv_tail

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.modelRatchetInv_receive_inOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.modelRatchetInv_receive_inOrder

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.ratchet_receive_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.ratchet_receive_frame

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.sparseTail_ok' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.sparseTail_ok

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.modelSpqrInv_tail' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.modelSpqrInv_tail

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.modelTripleInv_receive_inOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.modelTripleInv_receive_inOrder

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.keeps_output_none' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.keeps_output_none

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.keeps_epoch' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.keeps_epoch

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.decode_dh_canonical' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.decode_dh_canonical

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.classicalTail_err' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.classicalTail_err

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.sparseTail_err' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.sparseTail_err

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.receiveWithEviction_inOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.receiveWithEviction_inOrder

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.decryptRatchet_inOrderStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.decryptRatchet_inOrderStep

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.triple_receive_parts' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.triple_receive_parts

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.modelCounterRoom_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.modelCounterRoom_receive

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.step_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.step_frame

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.decrypt_inOrderStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.decrypt_inOrderStep

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.pow_and_pow_ne' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.pow_and_pow_ne

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.two_chunk_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.two_chunk_loop

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.decoder_invariant_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.decoder_invariant_parts

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.add_chunk_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.add_chunk_one

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.decoder_invariant_le_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.decoder_invariant_le_two

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.decoder_step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.decoder_step_keeps

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.braid_receive_keysSampled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
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
#print axioms Tacenta.UnitLifecycleReceivePreserve.braid_receive_keysSampled

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.braid_receive_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
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
#print axioms Tacenta.UnitLifecycleReceivePreserve.braid_receive_keeps

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.structural_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.structural_receive

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.mono_bind' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.mono_bind

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.mono_ite' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.mono_ite

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.strip_bind' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.strip_bind

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.strip_ite' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.strip_ite

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.structural_clear_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.structural_clear_pending

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.clause_a_of_structural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.clause_a_of_structural

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.sameKind_of_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.sameKind_of_refines

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.keyOf_dhs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.keyOf_dhs

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.code_dir_epoch' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.code_dir_epoch

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.decrypt_ratchet_keeps_invariant_in_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_boundary.kem.ciphertext_len,
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
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.decrypt_ratchet_keeps_invariant_in_order

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.decrypt_ok_inner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
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
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.decrypt_ok_inner

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.decrypt_keeps_invariant_in_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_boundary.kem.ciphertext_len,
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
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.decrypt_keeps_invariant_in_order

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.decrypt_keeps_invariant_model_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_boundary.kem.ciphertext_len,
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
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.decrypt_keeps_invariant_model_step

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.firstReceipt_inOrderStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.firstReceipt_inOrderStep

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.replyReceipt_inOrderStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.replyReceipt_inOrderStep

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.modelCounterRoom_afterFirstSend' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.modelCounterRoom_afterFirstSend

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.initiator_receives_reply_successor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_boundary.kem.ciphertext_len,
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
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.is_empty,
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
 tacenta_boundary.kem.KeyPair.public_key,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.initiator_receives_reply_successor

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.counterRoom_responder_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 zeroize.Zeroizing,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 core.num.Usize.div_ceil,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.counterRoom_responder_prepared

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.prepared_decoder_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 zeroize.Zeroizing,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 core.num.Usize.div_ceil,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.prepared_decoder_empty

/--
info: 'Tacenta.UnitLifecycleReceivePreserve.responder_successor_via_preservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_boundary.kem.ciphertext_len,
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
 alloc.vec.Vec.is_empty,
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
 tacenta_boundary.kem.KeyPair.public_key,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleReceivePreserve.responder_successor_via_preservation

set_option pp.deepTerms true
set_option pp.proofs.withType true

/--
info: @Tacenta.UnitLifecycleReceivePreserve.skip_noop : ∀ {st : Model.State.State} {upto : ℕ},
  st.ckr = none ∨ st.dhrPub = none ∨ upto ≤ st.nr → Model.State.skipMessageKeys st upto = some st
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.skip_noop

/--
info: @Tacenta.UnitLifecycleReceivePreserve.ratchet_receive_inOrder : ∀ {st : Model.State.State} {hdr : Model.State.Header}
  {dr ds np : Model.State.Key},
  Model.Ratchet.trySkipped st hdr = none →
    (st.dhrPub = some hdr.dh → hdr.n ≤ st.nr) →
      (st.dhrPub ≠ some hdr.dh → (st.ckr = none ∨ st.dhrPub = none ∨ hdr.pn ≤ st.nr) ∧ hdr.n = 0) →
        Model.Ratchet.receiveDetailed st hdr dr ds np =
          Tacenta.UnitLifecycleReceivePreserve.classicalTail
            (if st.dhrPub = some hdr.dh then st else Model.Ratchet.dhRatchet st hdr dr ds np) hdr
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.ratchet_receive_inOrder

/--
info: @Tacenta.UnitLifecycleReceivePreserve.spqr_receive_inOrder : ∀ {st : Model.SparseRatchet.State} {e n : ℕ},
  Model.SparseRatchet.trySkipped st e n = none →
    (∀ (cs : Model.SparseRatchet.Chains) (ch : Model.SparseRatchet.Chain),
        Model.SparseRatchet.findChains st e = some cs → cs.receive = some ch → n - 1 ≤ ch.n) →
      Model.SparseRatchet.receiveDetailed st e none n = Tacenta.UnitLifecycleReceivePreserve.sparseTail st e n
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.spqr_receive_inOrder

/--
info: @Tacenta.UnitLifecycleReceivePreserve.classicalTail_ok : ∀ {st1 st' : Model.State.State} {hdr : Model.State.Header}
  {mk : Model.State.Key},
  Tacenta.UnitLifecycleReceivePreserve.classicalTail st1 hdr = Except.ok (st', mk) →
    ∃ ck,
      st1.ckr = some ck ∧
        st1.nr < Model.State.u32Max ∧
          st' =
            Model.State.ageStore
              { dhsPub := st1.dhsPub, dhrPub := st1.dhrPub, rk := st1.rk, cks := st1.cks,
                ckr := some (Model.State.kdfCk ck).1, ns := st1.ns, nr := st1.nr + 1, pn := st1.pn,
                skipped := st1.skipped, events := st1.events, labels := st1.labels }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.classicalTail_ok

/--
info: @Tacenta.UnitLifecycleReceivePreserve.modelRatchetInv_tail : ∀ {st st1 st' : Model.State.State}
  {hdr : Model.State.Header} {mk : Model.State.Key},
  Tacenta.UnitTripleInvModel.ModelRatchetInv st →
    st1.skipped = st.skipped →
      st1.events = st.events →
        (st1.ckr.isSome = true → st1.cks.isSome = true ∧ st1.dhrPub.isSome = true) →
          Model.Messages.canonicalKey st1.dhsPub = true →
            (∀ (k : Model.State.Key), st1.dhrPub = some k → Model.Messages.canonicalKey k = true) →
              Tacenta.UnitLifecycleReceivePreserve.classicalTail st1 hdr = Except.ok (st', mk) →
                Tacenta.UnitTripleInvModel.ModelRatchetInv st'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.modelRatchetInv_tail

/--
info: @Tacenta.UnitLifecycleReceivePreserve.modelRatchetInv_receive_inOrder : ∀ {st st' : Model.State.State}
  {hdr : Model.State.Header} {dr ds np mk : Model.State.Key},
  Tacenta.UnitTripleInvModel.ModelRatchetInv st →
    Model.Messages.canonicalKey hdr.dh = true →
      (st.dhrPub ≠ some hdr.dh → Model.Messages.canonicalKey np = true) →
        Model.Ratchet.trySkipped st hdr = none →
          (st.dhrPub = some hdr.dh → hdr.n ≤ st.nr) →
            (st.dhrPub ≠ some hdr.dh → (st.ckr = none ∨ st.dhrPub = none ∨ hdr.pn ≤ st.nr) ∧ hdr.n = 0) →
              Model.Ratchet.receiveDetailed st hdr dr ds np = Except.ok (st', mk) →
                Tacenta.UnitTripleInvModel.ModelRatchetInv st'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.modelRatchetInv_receive_inOrder

/--
info: @Tacenta.UnitLifecycleReceivePreserve.ratchet_receive_frame : ∀ {st st' : Model.State.State} {hdr : Model.State.Header}
  {dr ds np mk : Model.State.Key},
  Model.Ratchet.trySkipped st hdr = none →
    (st.dhrPub = some hdr.dh → hdr.n ≤ st.nr) →
      (st.dhrPub ≠ some hdr.dh → (st.ckr = none ∨ st.dhrPub = none ∨ hdr.pn ≤ st.nr) ∧ hdr.n = 0) →
        Model.Ratchet.receiveDetailed st hdr dr ds np = Except.ok (st', mk) →
          (st.dhrPub = some hdr.dh → st'.dhsPub = st.dhsPub) ∧
            (st.dhrPub ≠ some hdr.dh → st'.dhsPub = np) ∧ st'.events ≤ st.events + 1 ∧ st'.ckr.isSome = true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.ratchet_receive_frame

/--
info: @Tacenta.UnitLifecycleReceivePreserve.sparseTail_ok : ∀ {st st' : Model.SparseRatchet.State} {e n : ℕ}
  {mk : Model.State.Key},
  Tacenta.UnitLifecycleReceivePreserve.sparseTail st e n = Except.ok (st', mk) →
    ∃ cs ch,
      (e, cs) ∈ st.chains ∧
        cs.receive = some ch ∧
          n = ch.n + 1 ∧
            ch.n < Model.SparseRatchet.u64Max ∧
              st' =
                Model.SparseRatchet.setChains st e
                  { send := cs.send, receive := some { ck := (Model.SparseRatchet.kdfCk ch.ck n).1, n := n } }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.sparseTail_ok

/--
info: @Tacenta.UnitLifecycleReceivePreserve.modelSpqrInv_tail : ∀ {st st' : Model.SparseRatchet.State} {e n : ℕ}
  {mk : Model.State.Key},
  Tacenta.UnitTripleInvModel.ModelSpqrInv st →
    Tacenta.UnitLifecycleReceivePreserve.sparseTail st e n = Except.ok (st', mk) →
      Tacenta.UnitTripleInvModel.ModelSpqrInv st'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.modelSpqrInv_tail

/--
info: @Tacenta.UnitLifecycleReceivePreserve.modelTripleInv_receive_inOrder : ∀ {m m' : Model.Triple.State}
  {hdr : Model.Triple.Header} {dr ds np k : Model.State.Key},
  Tacenta.UnitTripleInvModel.ModelTripleInv m →
    Model.Messages.canonicalKey hdr.dr.dh = true →
      (m.classical.dhrPub ≠ some hdr.dr.dh → Model.Messages.canonicalKey np = true) →
        Tacenta.UnitLifecycleReceivePreserve.InOrder m hdr →
          Model.Triple.receiveDetailed m hdr dr ds np none = Except.ok (m', k) →
            Tacenta.UnitTripleInvModel.ModelTripleInv m'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.modelTripleInv_receive_inOrder

/--
info: Tacenta.UnitLifecycleReceivePreserve.keeps_output_none : ∀ (K : Model.Braid.Kem) (st : Model.Braid.BraidState)
  (msg : Model.Braid.Msg),
  Tacenta.UnitLifecycleReceivePreserve.KeepsAgreementState st (Model.Braid.receive K st msg).2.2 →
    (Model.Braid.receive K st msg).2.1 = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.keeps_output_none

/--
info: @Tacenta.UnitLifecycleReceivePreserve.keeps_epoch : ∀ {st st' : Model.Braid.BraidState},
  Tacenta.UnitLifecycleReceivePreserve.KeepsAgreementState st st' → st'.epoch = st.epoch
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.keeps_epoch

/--
info: @Tacenta.UnitLifecycleReceivePreserve.decode_dh_canonical : ∀ {bs : List UInt8} {c : Model.CompositeHeader.Composite}
  {ct : List UInt8}, Model.CompositeHeader.decode bs = some (c, ct) → Model.Messages.canonicalKey c.dh = true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.decode_dh_canonical

/--
info: @Tacenta.UnitLifecycleReceivePreserve.classicalTail_err : ∀ {st1 : Model.State.State} {hdr : Model.State.Header}
  {r : Model.Ratchet.ReceiveRefusal},
  Tacenta.UnitLifecycleReceivePreserve.classicalTail st1 hdr = Except.error r →
    r ≠ Model.Ratchet.ReceiveRefusal.skippedStoreFull
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.classicalTail_err

/--
info: @Tacenta.UnitLifecycleReceivePreserve.sparseTail_err : ∀ {st : Model.SparseRatchet.State} {e n : ℕ}
  {r : Model.SparseRatchet.ReceiveRefusal},
  Tacenta.UnitLifecycleReceivePreserve.sparseTail st e n = Except.error r →
    r ≠ Model.SparseRatchet.ReceiveRefusal.skippedStoreFull
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.sparseTail_err

/--
info: @Tacenta.UnitLifecycleReceivePreserve.receiveWithEviction_inOrder : ∀ {m : Model.Triple.State}
  {c : Model.CompositeHeader.Composite} {hdr : Model.Triple.Header} {dr ds np : Model.State.Key}
  {r : Model.Triple.State × Model.State.Key},
  Tacenta.UnitLifecycleReceivePreserve.InOrder m hdr →
    Model.Lifecycle.receiveWithEviction m c hdr dr ds np none = Except.ok r →
      Model.Triple.receiveDetailed m hdr dr ds np none = Except.ok r
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.receiveWithEviction_inOrder

/--
info: Tacenta.UnitLifecycleReceivePreserve.decryptRatchet_inOrderStep : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (m : Model.Lifecycle.Session) (msg : Model.Lifecycle.Bytes),
  Tacenta.UnitLifecycleReceivePreserve.KeepsAgreementState m.braid m.braid →
    (∀ (c : Model.CompositeHeader.Composite) (ct : List UInt8),
        Model.CompositeHeader.decodeDetailed msg = Except.ok (c, ct) →
          Tacenta.UnitLifecycleReceivePreserve.InOrder m.triple (Model.Lifecycle.tripleHeaderOf c) ∧
            Tacenta.UnitLifecycleReceivePreserve.KeepsAgreementState m.braid
              (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.2) →
      Tacenta.UnitLifecycleReceivePreserve.InOrderReceiveStep oracle m
        (Model.Lifecycle.decryptRatchet view oracle m msg).session
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.decryptRatchet_inOrderStep

/--
info: @Tacenta.UnitLifecycleReceivePreserve.triple_receive_parts : ∀ {m m' : Model.Triple.State} {hdr : Model.Triple.Header}
  {dr ds np k : Model.State.Key},
  Tacenta.UnitLifecycleReceivePreserve.InOrder m hdr →
    Model.Triple.receiveDetailed m hdr dr ds np none = Except.ok (m', k) →
      (∃ k1, Model.Ratchet.receiveDetailed m.classical hdr.dr dr ds np = Except.ok (m'.classical, k1)) ∧
        ∃ k2,
          Tacenta.UnitLifecycleReceivePreserve.sparseTail m.postQuantum hdr.epoch hdr.pqN =
            Except.ok (m'.postQuantum, k2)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.triple_receive_parts

/--
info: Tacenta.UnitLifecycleReceivePreserve.modelCounterRoom_receive : ∀ (oracle : Model.Lifecycle.Oracle)
  {m m' : Model.Lifecycle.Session} (k : ℕ),
  Tacenta.UnitLifecycleReceivePreserve.InOrderReceiveStep oracle m m' →
    Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom m (k + 1) →
      Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom m' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.modelCounterRoom_receive

/--
info: Tacenta.UnitLifecycleReceivePreserve.step_frame : ∀ (oracle : Model.Lifecycle.Oracle) {m m' : Model.Lifecycle.Session},
  Tacenta.UnitLifecycleReceivePreserve.InOrderReceiveStep oracle m m' →
    m'.triple.postQuantum.direction = m.triple.postQuantum.direction ∧
      m'.triple.postQuantum.epoch = m.triple.postQuantum.epoch ∧
        (m'.triple.classical.dhsPub ≠ m.triple.classical.dhsPub →
          m'.triple.classical.dhsPub = oracle.dhPublic m'.ratchetPrivate)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.step_frame

/--
info: Tacenta.UnitLifecycleReceivePreserve.decrypt_inOrderStep : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (m : Model.Lifecycle.Session) (msg inner : Model.Lifecycle.Bytes),
  Model.Lifecycle.dispatchDecrypt oracle m msg = Except.ok inner →
    Tacenta.UnitLifecycleReceivePreserve.KeepsAgreementState m.braid m.braid →
      (∀ (c : Model.CompositeHeader.Composite) (ct : List UInt8),
          Model.CompositeHeader.decodeDetailed inner = Except.ok (c, ct) →
            Tacenta.UnitLifecycleReceivePreserve.InOrder m.triple (Model.Lifecycle.tripleHeaderOf c) ∧
              Tacenta.UnitLifecycleReceivePreserve.KeepsAgreementState m.braid
                (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.2) →
        Tacenta.UnitLifecycleReceivePreserve.InOrderReceiveStep oracle m
          (Model.Lifecycle.decrypt view oracle m msg).session
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.decrypt_inOrderStep

/--
info: @Tacenta.UnitLifecycleReceivePreserve.pow_and_pow_ne : ∀ {a b : ℕ}, a < 8 → b < 8 → a ≠ b → 2 ^ a &&& 2 ^ b = 0
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.pow_and_pow_ne

/--
info: Tacenta.UnitLifecycleReceivePreserve.two_chunk_loop : ∀ (d : tacenta_erasure.Decoder) (c1 c2 : tacenta_erasure.Chunk),
  ↑d.have = [c1, c2] →
    c1.index ≠ c2.index →
      d.invariant_loop (Array.repeat 8192#usize 0#u8) true 0#usize ⦃ r => r = (d.size, d.needed, d.have, true) ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.two_chunk_loop

/--
info: Tacenta.UnitLifecycleReceivePreserve.decoder_invariant_parts : ∀ (d : tacenta_erasure.Decoder),
  d.invariant = ok true → tacenta_erasure.chunk_count d.size = ok d.needed ∧ ↑d.needed ≤ 65536
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.decoder_invariant_parts

/--
info: Tacenta.UnitLifecycleReceivePreserve.add_chunk_one : ∀ (d d' : tacenta_erasure.Decoder) (c1 c : tacenta_erasure.Chunk)
  (r : Bool),
  ↑d.have = [c1] →
    d.add_chunk c = ok (r, d') →
      d' = d ∨ d'.size = d.size ∧ d'.needed = d.needed ∧ ↑d'.have = [c1, c] ∧ c1.index ≠ c.index ∧ 2 ≤ ↑d.needed
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.add_chunk_one

/--
info: Tacenta.UnitLifecycleReceivePreserve.decoder_invariant_le_two : ∀ (d : tacenta_erasure.Decoder),
  tacenta_erasure.chunk_count d.size = ok d.needed →
    ↑d.needed ≤ 65536 →
      (↑d.have).length ≤ ↑d.needed →
        ((↑d.have).length ≤ 1 ∨ ∃ c1 c2, ↑d.have = [c1, c2] ∧ c1.index ≠ c2.index) → d.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.decoder_invariant_le_two

/--
info: @Tacenta.UnitLifecycleReceivePreserve.decoder_step_keeps : ∀ {d d' : tacenta_erasure.Decoder},
  d.invariant = ok true →
    (↑d.have).length ≤ 1 → (d' = d ∨ ∃ c r, d.add_chunk c = ok (r, d')) → d'.invariant = ok true ∧ d'.size = d.size
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.decoder_step_keeps

/--
info: Tacenta.UnitLifecycleReceivePreserve.braid_receive_keysSampled : ∀ (e : U64) (a : tacenta_braid.Auth)
  (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) (m : tacenta_braid.Msg) (x : U64)
  (y : Option tacenta_braid.Output) (bc : tacenta_braid.Braid),
  { state := tacenta_braid.State.KeysSampled e a kp enc }.receive m = ok (x, y, bc) →
    ∀ (e' : U64) (a' : tacenta_braid.Auth) (kp2 : tacenta_kem.IncrementalKeyPair) (enc2 : tacenta_erasure.Encoder),
      bc.state = tacenta_braid.State.KeysSampled e' a' kp2 enc2 →
        e' = e ∧ a' = a ∧ enc2 = enc ∧ tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp = ok kp2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.braid_receive_keysSampled

/--
info: Tacenta.UnitLifecycleReceivePreserve.braid_receive_keeps : Tacenta.SessionUnitBraidT3.KemCloneAgrees →
  ∀ (b : tacenta_braid.Braid) (m : tacenta_braid.Msg) (x : U64) (y : Option tacenta_braid.Output)
    (bc : tacenta_braid.Braid),
    b.receive m = ok (x, y, bc) →
      b.invariant = ok true →
        (∀ (e : U64) (a : tacenta_braid.Auth) (d : tacenta_erasure.Decoder),
            b.state = tacenta_braid.State.NoHeaderReceived e a d → (↑d.have).length ≤ 1) →
          Tacenta.UnitLifecycleReceivePreserve.SameAgreementKind b.state bc.state →
            bc.invariant = ok true ∧
              bc.failed = b.failed ∧
                bc.is_initiator = b.is_initiator ∧
                  bc.epoch = b.epoch ∧
                    bc.state_tag = b.state_tag ∧
                      Tacenta.SessionUnitBraidT1.State.epoch_val bc.state =
                        Tacenta.SessionUnitBraidT1.State.epoch_val b.state
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.braid_receive_keeps

/--
info: Tacenta.UnitLifecycleReceivePreserve.structural_receive : ∀ (s : lifecycle.Session) (t : tacenta_triple.State)
  (b : tacenta_braid.Braid) (rp : tacenta_boundary.dh.PrivateKey),
  s.structural_invariant = ok true →
    ∀ (pk : tacenta_boundary.dh.PublicKeyBytes),
      rp.public_key = ok pk →
        pk.as_bytes = ok t.classical.dhs_pub →
          t.post_quantum.direction = s.triple.post_quantum.direction →
            t.post_quantum.epoch = s.triple.post_quantum.epoch →
              b.failed = s.braid.failed →
                b.is_initiator = s.braid.is_initiator →
                  b.epoch = s.braid.epoch →
                    b.state_tag = s.braid.state_tag →
                      { triple := t, braid := b, ratchet_private := rp, identity_ad := s.identity_ad,
                            our_identity_public := s.our_identity_public,
                            peer_identity_public := s.peer_identity_public, pending_initial := s.pending_initial,
                            established_ephemeral := s.established_ephemeral }.structural_invariant =
                        ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.structural_receive

/--
info: @Tacenta.UnitLifecycleReceivePreserve.mono_bind : ∀ {α : Type} {x : Result α} {f g : α → Result Bool},
  (∀ (a : α), f a = ok true → g a = ok true) → x >>= f = ok true → x >>= g = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.mono_bind

/--
info: @Tacenta.UnitLifecycleReceivePreserve.mono_ite : ∀ {c : Prop} [inst : Decidable c] {a b a' b' : Result Bool},
  (a = ok true → a' = ok true) →
    (b = ok true → b' = ok true) → (if c then a else b) = ok true → (if c then a' else b') = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.mono_ite

/--
info: @Tacenta.UnitLifecycleReceivePreserve.strip_bind : ∀ {α : Type} {x : Result α} {f : α → Result Bool} {y : Result Bool},
  (∀ (a : α), f a = ok true → y = ok true) → x >>= f = ok true → y = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.strip_bind

/--
info: @Tacenta.UnitLifecycleReceivePreserve.strip_ite : ∀ {c : Prop} [inst : Decidable c] {b y : Result Bool},
  (b = ok true → y = ok true) → (if c then ok false else b) = ok true → y = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.strip_ite

/--
info: Tacenta.UnitLifecycleReceivePreserve.structural_clear_pending : ∀ (s : lifecycle.Session),
  s.structural_invariant = ok true →
    { triple := s.triple, braid := s.braid, ratchet_private := s.ratchet_private, identity_ad := s.identity_ad,
          our_identity_public := s.our_identity_public, peer_identity_public := s.peer_identity_public,
          pending_initial := none, established_ephemeral := s.established_ephemeral }.structural_invariant =
      ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.structural_clear_pending

/--
info: Tacenta.UnitLifecycleReceivePreserve.clause_a_of_structural : ∀ (s : lifecycle.Session),
  s.structural_invariant = ok true →
    ∃ pk, s.ratchet_private.public_key = ok pk ∧ pk.as_bytes = ok s.triple.classical.dhs_pub
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.clause_a_of_structural

/--
info: @Tacenta.UnitLifecycleReceivePreserve.sameKind_of_refines : ∀ {K : Model.Braid.Kem} {st st' : tacenta_braid.State}
  {m m' : Model.Braid.BraidState},
  Tacenta.SessionUnitBraidT3.StateRefines K st m →
    Tacenta.SessionUnitBraidT3.StateRefines K st' m' →
      Tacenta.UnitLifecycleReceivePreserve.KeepsAgreementState m m' →
        Tacenta.UnitLifecycleReceivePreserve.SameAgreementKind st st'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.sameKind_of_refines

/--
info: @Tacenta.UnitLifecycleReceivePreserve.keyOf_dhs : ∀ {t : tacenta_triple.State} {mt : Model.Triple.State},
  Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs t
      mt →
    Tacenta.SessionUnitT3.keyOf t.classical.dhs_pub = mt.classical.dhsPub
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.keyOf_dhs

/--
info: @Tacenta.UnitLifecycleReceivePreserve.code_dir_epoch : ∀ {t t' : tacenta_triple.State} {mt mt' : Model.Triple.State},
  Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs t
      mt →
    Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        t' mt' →
      mt'.postQuantum.direction = mt.postQuantum.direction →
        mt'.postQuantum.epoch = mt.postQuantum.epoch →
          t'.post_quantum.direction = t.post_quantum.direction ∧ t'.post_quantum.epoch = t.post_quantum.epoch
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.code_dir_epoch

/--
info: Tacenta.UnitLifecycleReceivePreserve.decrypt_ratchet_keeps_invariant_in_order : Tacenta.SessionUnitBraidT3.KemCloneAgrees →
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (dh : Tacenta.UnitLifecycleT3.DhView),
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        ∀ (K : Model.Braid.Kem) (oracle : Model.Lifecycle.Oracle),
          (∀ (secret : tacenta_boundary.dh.PrivateKey),
              ∃ publicKey,
                secret.public_key = ok publicKey ∧ dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)) →
            ∀ (s : lifecycle.Session) (m m' : Model.Lifecycle.Session) (k : ℕ),
              s.invariant = ok true →
                Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                  Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
                    (∀ (e : U64) (a : tacenta_braid.Auth) (d : tacenta_erasure.Decoder),
                        s.braid.state = tacenta_braid.State.NoHeaderReceived e a d → (↑d.have).length ≤ 1) →
                      ∀ (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                        lifecycle.Session.decrypt_ratchet rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng') →
                          Tacenta.UnitLifecycleT3.SessionRefines dh K s' m' →
                            Tacenta.UnitLifecycleReceivePreserve.InOrderReceiveStep oracle m m' →
                              s'.invariant = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.decrypt_ratchet_keeps_invariant_in_order

/--
info: @Tacenta.UnitLifecycleReceivePreserve.decrypt_ok_inner : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (msg : Slice U8) (rng : R) (v : alloc.vec.Vec U8)
  (s'' : lifecycle.Session) (r : R),
  lifecycle.Session.decrypt rc crc s msg rng = ok (core.result.Result.Ok v, s'', r) →
    ∃ inner s1,
      lifecycle.Session.decrypt_ratchet rc crc s inner rng = ok (core.result.Result.Ok v, s1, r) ∧
        s'' =
          { triple := s1.triple, braid := s1.braid, ratchet_private := s1.ratchet_private,
            identity_ad := s1.identity_ad, our_identity_public := s1.our_identity_public,
            peer_identity_public := s1.peer_identity_public, pending_initial := none,
            established_ephemeral := s1.established_ephemeral }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.decrypt_ok_inner

/--
info: Tacenta.UnitLifecycleReceivePreserve.decrypt_keeps_invariant_in_order : Tacenta.SessionUnitBraidT3.KemCloneAgrees →
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (dh : Tacenta.UnitLifecycleT3.DhView),
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        ∀ (K : Model.Braid.Kem) (oracle : Model.Lifecycle.Oracle),
          (∀ (secret : tacenta_boundary.dh.PrivateKey),
              ∃ publicKey,
                secret.public_key = ok publicKey ∧ dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)) →
            ∀ (s : lifecycle.Session) (m m' : Model.Lifecycle.Session) (k : ℕ),
              s.invariant = ok true →
                Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                  Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
                    (∀ (e : U64) (a : tacenta_braid.Auth) (d : tacenta_erasure.Decoder),
                        s.braid.state = tacenta_braid.State.NoHeaderReceived e a d → (↑d.have).length ≤ 1) →
                      ∀ (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                        lifecycle.Session.decrypt rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng') →
                          Tacenta.UnitLifecycleT3.SessionRefines dh K s' m' →
                            Tacenta.UnitLifecycleReceivePreserve.InOrderReceiveStep oracle m m' →
                              s'.invariant = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.decrypt_keeps_invariant_in_order

/--
info: Tacenta.UnitLifecycleReceivePreserve.decrypt_keeps_invariant_model_step : Tacenta.SessionUnitBraidT3.KemCloneAgrees →
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (dh : Tacenta.UnitLifecycleT3.DhView),
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        ∀ (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
          (∀ (secret : tacenta_boundary.dh.PrivateKey),
              ∃ publicKey,
                secret.public_key = ok publicKey ∧ dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)) →
            ∀ (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : ℕ),
              s.invariant = ok true →
                Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                  Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
                    (∀ (e : U64) (a : tacenta_braid.Auth) (d : tacenta_erasure.Decoder),
                        s.braid.state = tacenta_braid.State.NoHeaderReceived e a d → (↑d.have).length ≤ 1) →
                      ∀ (msg : Slice U8) (msgM inner : Model.Lifecycle.Bytes),
                        Model.Lifecycle.dispatchDecrypt oracle m msgM = Except.ok inner →
                          Tacenta.UnitLifecycleReceivePreserve.KeepsAgreementState m.braid m.braid →
                            (∀ (c : Model.CompositeHeader.Composite) (ct : List UInt8),
                                Model.CompositeHeader.decodeDetailed inner = Except.ok (c, ct) →
                                  Tacenta.UnitLifecycleReceivePreserve.InOrder m.triple
                                      (Model.Lifecycle.tripleHeaderOf c) ∧
                                    Tacenta.UnitLifecycleReceivePreserve.KeepsAgreementState m.braid
                                      (Model.Braid.receive oracle.braidKem m.braid
                                            (Model.Lifecycle.braidMessageOf view m.braid c)).2.2) →
                              ∀ (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                                lifecycle.Session.decrypt rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng') →
                                  Tacenta.UnitLifecycleT3.SessionRefines dh K s'
                                      (Model.Lifecycle.decrypt view oracle m msgM).session →
                                    s'.invariant = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.decrypt_keeps_invariant_model_step

/--
info: Tacenta.UnitLifecycleReceivePreserve.firstReceipt_inOrderStep : ∀ (oracle : Model.Lifecycle.Oracle)
  (mB : Model.Lifecycle.Session) (b ec ec' prk k1 k2 a4 d dSend rkA cksA c : Model.State.Key)
  (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk) (auth : Model.Braid.Auth) (dec : Model.Braid.Decoder),
  mB.triple = Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiverTriple b ec' prk k1 k2 →
    mB.braid = Model.Braid.BraidState.noHeaderReceived 1 auth dec →
      Model.State.kdfRk ec d Model.State.LabelSet.tacenta = (rkA, cksA) →
        Model.State.kdfRk ec' d Model.State.LabelSet.tacenta = (rkA, cksA) →
          Model.Messages.canonicalKey a4 = true →
            Tacenta.UnitLifecycleReceivePreserve.InOrderReceiveStep oracle mB
              (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend
                (oracle.dhPublic c) c)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.firstReceipt_inOrderStep

/--
info: Tacenta.UnitLifecycleReceivePreserve.replyReceipt_inOrderStep : ∀ (oracle : Model.Lifecycle.Oracle)
  (mA : Model.Lifecycle.Session) (a4 peer rkA cksA prk k1 k2 dSend x newPub c : Model.State.Key) (e : ℕ)
  (auth : Model.Braid.Auth) (dk ekVector : Model.Braid.Bytes) (enc : Model.Braid.Encoder),
  mA.triple = Tacenta.UnitLifecycleResponderFirstReceipt.senderAfterFirst a4 peer rkA cksA prk k1 k2 →
    mA.braid = Model.Braid.BraidState.keysSampled e auth dk ekVector enc →
      newPub ≠ peer →
        Model.Messages.canonicalKey newPub = true →
          Tacenta.UnitLifecycleReceivePreserve.InOrderReceiveStep oracle mA
            (Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession mA rkA prk k1 k2 dSend x newPub
              (oracle.dhPublic c) c)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.replyReceipt_inOrderStep

/--
info: Tacenta.UnitLifecycleReceivePreserve.modelCounterRoom_afterFirstSend : ∀ (mA : Model.Lifecycle.Session)
  (a4 peer rkA cksA prk k1 k2 : Model.State.Key) (auth : Model.Braid.Auth) (dk ekVector : Model.Braid.Bytes)
  (enc : Model.Braid.Encoder) (j : ℕ),
  mA.triple = Tacenta.UnitLifecycleResponderFirstReceipt.senderAfterFirst a4 peer rkA cksA prk k1 k2 →
    mA.braid = Model.Braid.BraidState.keysSampled 1 auth dk ekVector enc →
      j + 2 < U32.max → Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom mA (j + 1)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.modelCounterRoom_afterFirstSend

/--
info: @Tacenta.UnitLifecycleReceivePreserve.initiator_receives_reply_successor : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {R E F : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
  (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc oracle.braidKem →
    Tacenta.UnitLifecycleT3.TripleSendRefinementContracts →
      Tacenta.UnitLifecycleT1.AeadSealBounded →
        Tacenta.UnitLifecycleT1.DhCodecTotal →
          Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle →
            Tacenta.UnitLifecycleT3.DhCodecOf dh →
              Tacenta.UnitLifecycleT3.CodewordViewSendOf view →
                Tacenta.SessionUnitT3.ZeroizingRoundTrips80 →
                  Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Std.Array U8 32#usize) →
                    Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
                        (Std.Array U8 32#usize × Std.Array U8 32#usize × Std.Array U8 16#usize) →
                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
                        Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem →
                          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                            Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                              ∀ (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
                                (ourA : lifecycle.Identity) (bundleA : lifecycle.PublishedBundle)
                                (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session),
                                lifecycle.establish_initiator_for rcE crcE ourA bundleA expected rng0 =
                                    ok (core.result.Result.Ok s, rng1) →
                                  ∀
                                    (q :
                                      Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcE crcE ourA
                                        bundleA),
                                    s = q.session →
                                      ∀ (plaintext : Slice U8),
                                        (↑plaintext).length + 65770 ≤ Usize.max →
                                          ∀ (rng : R),
                                            trace rng = oracle.draws →
                                              ∀ (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
                                                trace rng = d1 :: d2 :: rest →
                                                  ∀ (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                                                    lifecycle.Session.encrypt rc crc s plaintext rng =
                                                        ok (core.result.Result.Ok bytes, s', rng') →
                                                      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc →
                                                        Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                            oracle.braidKem →
                                                          ∀ (dA : Model.Lifecycle.Key)
                                                            (restA : List Model.Lifecycle.Key),
                                                            trace rng' = dA :: restA →
                                                              ∀ (rcB : rand_core_1.RngCore F)
                                                                (crcB : rand_core_1.CryptoRng F)
                                                                (contracts :
                                                                  Tacenta.UnitLifecycleT1.EstablishResponderContracts
                                                                    rcB),
                                                                Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                                                                  Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                                                                    Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                                                                      Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                                                                        Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                                                                          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                                                                              @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                                                                            ∀ (traceB : F → List Model.Lifecycle.Key)
                                                                              (oracleB : Model.Lifecycle.Oracle),
                                                                              Tacenta.UnitLifecycleT3.OracleOf rcB crcB
                                                                                  dh kem traceB oracleB →
                                                                                Tacenta.UnitLifecycleT3.BraidSendRefinementContracts
                                                                                    rcB oracleB.braidKem →
                                                                                  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                                      oracleB.braidKem →
                                                                                    ∀ (ourB : lifecycle.Identity)
                                                                                      (storeB : lifecycle.PrekeyStore),
                                                                                      storeB.publish = ok bundleA →
                                                                                        ourB.public =
                                                                                            ok storeB.identity_public →
                                                                                          Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                                              storeB →
                                                                                            Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                                                storeB
                                                                                                bundleA.kem_prekey_id
                                                                                                q.kemCiphertext
                                                                                                q.kemSecret →
                                                                                              ∀ (rngB : F),
                                                                                                traceB rngB =
                                                                                                    oracleB.draws →
                                                                                                  ∀
                                                                                                    (dB :
                                                                                                      Model.Lifecycle.Key)
                                                                                                    (restB :
                                                                                                      List
                                                                                                        Model.Lifecycle.Key),
                                                                                                    traceB rngB =
                                                                                                        dB :: restB →
                                                                                                      ∀
                                                                                                        (ptB :
                                                                                                          alloc.vec.Vec
                                                                                                            U8)
                                                                                                        (sB' :
                                                                                                          lifecycle.Session)
                                                                                                        (storeB' :
                                                                                                          lifecycle.PrekeyStore)
                                                                                                        (rngB' : F),
                                                                                                        lifecycle.establish_responder
                                                                                                              rcB crcB
                                                                                                              ourB
                                                                                                              storeB
                                                                                                              bytes.deref
                                                                                                              rngB =
                                                                                                            ok
                                                                                                              (core.result.Result.Ok
                                                                                                                  (sB',
                                                                                                                    ptB),
                                                                                                                storeB',
                                                                                                                rngB') →
                                                                                                          ∀
                                                                                                            (ptR :
                                                                                                              Slice U8),
                                                                                                            102 +
                                                                                                                  ((↑ptR).length +
                                                                                                                    48) ≤
                                                                                                                Usize.max →
                                                                                                              ∀
                                                                                                                (rngR :
                                                                                                                  F),
                                                                                                                oracleB.dhPublic
                                                                                                                      dB ≠
                                                                                                                    Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                      q.peerRatchetBytes →
                                                                                                                  ∃
                                                                                                                    dSend
                                                                                                                    x
                                                                                                                    bytesR
                                                                                                                    sB''
                                                                                                                    ptA
                                                                                                                    s''
                                                                                                                    rngA',
                                                                                                                    lifecycle.Session.encrypt
                                                                                                                          rcB
                                                                                                                          crcB
                                                                                                                          sB'
                                                                                                                          ptR
                                                                                                                          rngR =
                                                                                                                        ok
                                                                                                                          (core.result.Result.Ok
                                                                                                                              bytesR,
                                                                                                                            sB'',
                                                                                                                            rngR) ∧
                                                                                                                      lifecycle.Session.decrypt
                                                                                                                            rc
                                                                                                                            crc
                                                                                                                            s'
                                                                                                                            bytesR.deref
                                                                                                                            rng' =
                                                                                                                          ok
                                                                                                                            (core.result.Result.Ok
                                                                                                                                ptA,
                                                                                                                              s'',
                                                                                                                              rngA') ∧
                                                                                                                        ↑ptA =
                                                                                                                            ↑ptR ∧
                                                                                                                          s''.invariant =
                                                                                                                              ok
                                                                                                                                true ∧
                                                                                                                            Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                                                                s'' ∧
                                                                                                                              (∀
                                                                                                                                  (j :
                                                                                                                                    ℕ),
                                                                                                                                  j +
                                                                                                                                        2 <
                                                                                                                                      U32.max →
                                                                                                                                    Tacenta.UnitLifecycleSendPreserve.CounterRoom
                                                                                                                                      s''
                                                                                                                                      j) ∧
                                                                                                                                Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                                                  dh
                                                                                                                                  oracle.braidKem
                                                                                                                                  s''
                                                                                                                                  (Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession
                                                                                                                                    (Model.Lifecycle.encrypt
                                                                                                                                        view
                                                                                                                                        oracle
                                                                                                                                        (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                                                                          dh
                                                                                                                                          s)
                                                                                                                                        (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                          plaintext)).session
                                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                      q.rootKey)
                                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                      q.sparseRoot)
                                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                      q.sparseSend)
                                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                      q.sparseReceive)
                                                                                                                                    dSend
                                                                                                                                    x
                                                                                                                                    (oracleB.dhPublic
                                                                                                                                      dB)
                                                                                                                                    (oracle.dhPublic
                                                                                                                                      dA)
                                                                                                                                    dA)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.initiator_receives_reply_successor

/--
info: @Tacenta.UnitLifecycleReceivePreserve.counterRoom_responder_prepared : ∀ {ourB : lifecycle.Identity}
  {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg),
  Tacenta.UnitLifecycleSendPreserve.CounterRoom p.session 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.counterRoom_responder_prepared

/--
info: @Tacenta.UnitLifecycleReceivePreserve.prepared_decoder_empty : ∀ {ourB : lifecycle.Identity}
  {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg) (e : U64)
  (a : tacenta_braid.Auth) (d : tacenta_erasure.Decoder),
  p.session.braid.state = tacenta_braid.State.NoHeaderReceived e a d → (↑d.have).length ≤ 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.prepared_decoder_empty

/--
info: @Tacenta.UnitLifecycleReceivePreserve.responder_successor_via_preservation : ∀ {RA : Type}
  {rcA : rand_core_1.RngCore RA} {crcA : rand_core_1.CryptoRng RA} {our : lifecycle.Identity}
  {bundle : lifecycle.PublishedBundle} [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type} (rcB : rand_core_1.RngCore E)
  (crcB : rand_core_1.CryptoRng E) (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
      Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
        Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
          Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
            Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
              Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                Tacenta.UnitHeadroomInvariant.OptionEqU64Shape @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                  ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
                    Tacenta.UnitLifecycleT3.DhCodecOf dh →
                      ∀ (view : Model.Lifecycle.CodewordView) (oracleA : Model.Lifecycle.Oracle),
                        Tacenta.UnitOracleShape.AeadSealClause Tacenta.UnitSatisfiabilityJoint.Interp.real oracleA →
                          ∀ (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle),
                            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
                              Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracleB.braidKem →
                                ∀
                                  (q :
                                    Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcA crcA our bundle)
                                  (pending : Model.Lifecycle.PendingInitial),
                                  (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh
                                          q.session).pendingInitial =
                                      some pending →
                                    ∀ (plaintext : Slice U8),
                                      (↑plaintext).length + 48 ≤ Usize.max →
                                        ∀ (src : Model.Lifecycle.Bytes),
                                          List.length src = Model.Braid.headerSize + Model.Braid.macSize →
                                            ∀ (c : tacenta_erasure.Chunk),
                                              Tacenta.SessionUnitBraidT3.CodewordOf src c →
                                                view.send
                                                      (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                          dh q.session).braid
                                                      (Tacenta.UnitLifecycleT3.modelChunkOf src c) =
                                                    Tacenta.UnitLifecycleT3.modelCodewordOf c →
                                                  ∀ (msg : Slice U8),
                                                    Tacenta.UnitLifecycleT3.sliceOf msg =
                                                        Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
                                                          (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                            dh q.session)
                                                          pending
                                                          (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame view
                                                            oracleA
                                                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                              dh q.session)
                                                            (Tacenta.UnitLifecycleT3.sliceOf plaintext)
                                                            (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                              (Tacenta.UnitLifecycleT3.arrayOf q.sendChain)
                                                              (Tacenta.UnitLifecycleT3.arrayOf q.sparseSend))
                                                            (Tacenta.UnitLifecycleT3.modelChunkOf src c)) →
                                                      ∀ (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore),
                                                        storeB.publish = ok bundle →
                                                          ourB.public = ok storeB.identity_public →
                                                            Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                storeB →
                                                              Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                  storeB bundle.kem_prekey_id q.kemCiphertext
                                                                  q.kemSecret →
                                                                ∀ (rngB : E),
                                                                  traceB rngB = oracleB.draws →
                                                                    ∀ (dB : Model.Lifecycle.Key)
                                                                      (restB : List Model.Lifecycle.Key),
                                                                      traceB rngB = dB :: restB →
                                                                        ∀ (ptB : alloc.vec.Vec U8)
                                                                          (sB' : lifecycle.Session)
                                                                          (storeB' : lifecycle.PrekeyStore) (rngB' : E),
                                                                          lifecycle.establish_responder rcB crcB ourB
                                                                                storeB msg rngB =
                                                                              ok
                                                                                (core.result.Result.Ok (sB', ptB),
                                                                                  storeB', rngB') →
                                                                            ∃ p ec dSend,
                                                                              Tacenta.UnitLifecycleT3.SessionRefines dh
                                                                                  oracleB.braidKem sB'
                                                                                  (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                                    (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                      dh p)
                                                                                    (Tacenta.UnitLifecycleT3.sliceOf
                                                                                      p.braidSecret)
                                                                                    (Tacenta.UnitLifecycleT3.modelChunkOf
                                                                                      src c)
                                                                                    (Tacenta.UnitLifecycleT3.arrayOf ec)
                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                      q.sparseRoot)
                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                      q.sparseSend)
                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                      q.sparseReceive)
                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                      q.ratchetBytes)
                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                      q.dhOut)
                                                                                    dSend (oracleB.dhPublic dB) dB) ∧
                                                                                sB'.invariant = ok true ∧
                                                                                  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                    sB'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleReceivePreserve.responder_successor_via_preservation

/--
info: structure Tacenta.UnitLifecycleReceivePreserve.InOrder (m : Model.Triple.State) (h : Model.Triple.Header) : Prop
number of parameters: 2
fields:
  Tacenta.UnitLifecycleReceivePreserve.InOrder.noStoredClassical : Model.Ratchet.trySkipped m.classical h.dr = none
  Tacenta.UnitLifecycleReceivePreserve.InOrder.sameChain : m.classical.dhrPub = some h.dr.dh → h.dr.n ≤ m.classical.nr
  Tacenta.UnitLifecycleReceivePreserve.InOrder.newChain : m.classical.dhrPub ≠ some h.dr.dh →
      (m.classical.ckr = none ∨ m.classical.dhrPub = none ∨ h.dr.pn ≤ m.classical.nr) ∧ h.dr.n = 0
  Tacenta.UnitLifecycleReceivePreserve.InOrder.noStoredSparse : Model.SparseRatchet.trySkipped m.postQuantum h.epoch
        h.pqN =
      none
  Tacenta.UnitLifecycleReceivePreserve.InOrder.sparseNext : ∀ (cs : Model.SparseRatchet.Chains)
      (ch : Model.SparseRatchet.Chain),
      Model.SparseRatchet.findChains m.postQuantum h.epoch = some cs → cs.receive = some ch → h.pqN - 1 ≤ ch.n
constructor:
  Tacenta.UnitLifecycleReceivePreserve.InOrder.mk {m : Model.Triple.State} {h : Model.Triple.Header}
    (noStoredClassical : Model.Ratchet.trySkipped m.classical h.dr = none)
    (sameChain : m.classical.dhrPub = some h.dr.dh → h.dr.n ≤ m.classical.nr)
    (newChain :
      m.classical.dhrPub ≠ some h.dr.dh →
        (m.classical.ckr = none ∨ m.classical.dhrPub = none ∨ h.dr.pn ≤ m.classical.nr) ∧ h.dr.n = 0)
    (noStoredSparse : Model.SparseRatchet.trySkipped m.postQuantum h.epoch h.pqN = none)
    (sparseNext :
      ∀ (cs : Model.SparseRatchet.Chains) (ch : Model.SparseRatchet.Chain),
        Model.SparseRatchet.findChains m.postQuantum h.epoch = some cs → cs.receive = some ch → h.pqN - 1 ≤ ch.n) :
    Tacenta.UnitLifecycleReceivePreserve.InOrder m h
-/
#guard_msgs in
#print Tacenta.UnitLifecycleReceivePreserve.InOrder

/--
info: def Tacenta.UnitLifecycleReceivePreserve.classicalTail : Model.State.State →
  Model.State.Header → Except Model.Ratchet.ReceiveRefusal (Model.State.State × Model.State.Key) :=
fun st1 hdr =>
  if hdr.n < st1.nr then Except.error Model.Ratchet.ReceiveRefusal.outOfOrder
  else
    match st1.ckr with
    | none => Except.error Model.Ratchet.ReceiveRefusal.noReceivingChain
    | some ck =>
      if st1.nr < Model.State.u32Max then
        Except.ok
          (Model.State.ageStore
              { dhsPub := st1.dhsPub, dhrPub := st1.dhrPub, rk := st1.rk, cks := st1.cks,
                ckr := some (Model.State.kdfCk ck).1, ns := st1.ns, nr := st1.nr + 1, pn := st1.pn,
                skipped := st1.skipped, events := st1.events, labels := st1.labels },
            (Model.State.kdfCk ck).2)
      else Except.error Model.Ratchet.ReceiveRefusal.chainExhausted
-/
#guard_msgs in
#print Tacenta.UnitLifecycleReceivePreserve.classicalTail

/--
info: def Tacenta.UnitLifecycleReceivePreserve.sparseTail : Model.SparseRatchet.State →
  ℕ → ℕ → Except Model.SparseRatchet.ReceiveRefusal (Model.SparseRatchet.State × Model.State.Key) :=
fun st e n =>
  match Model.SparseRatchet.findChains st e with
  | none => Except.error Model.SparseRatchet.ReceiveRefusal.noChain
  | some cs =>
    match cs.receive with
    | none => Except.error Model.SparseRatchet.ReceiveRefusal.chainRetired
    | some ch =>
      if Model.SparseRatchet.u64Max ≤ ch.n then Except.error Model.SparseRatchet.ReceiveRefusal.chainExhausted
      else
        if (n != ch.n + 1) = true then Except.error Model.SparseRatchet.ReceiveRefusal.outOfOrder
        else
          Except.ok
            (Model.SparseRatchet.setChains st e
                { send := cs.send, receive := some { ck := (Model.SparseRatchet.kdfCk ch.ck n).1, n := n } },
              (Model.SparseRatchet.kdfCk ch.ck n).2)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleReceivePreserve.sparseTail

/--
info: def Tacenta.UnitLifecycleReceivePreserve.KeepsAgreementState : Model.Braid.BraidState → Model.Braid.BraidState → Prop :=
fun x x_1 =>
  match x, x_1 with
  | Model.Braid.BraidState.noHeaderReceived e auth hdrDec, Model.Braid.BraidState.noHeaderReceived e' auth_1 hdrDec_1 =>
    e' = e
  | Model.Braid.BraidState.keysSampled e auth dk ekVector hdrEnc,
    Model.Braid.BraidState.keysSampled e' auth_1 dk_1 ekVector_1 hdrEnc_1 => e' = e
  | x, x_2 => False
-/
#guard_msgs in
#print Tacenta.UnitLifecycleReceivePreserve.KeepsAgreementState

/--
info: def Tacenta.UnitLifecycleReceivePreserve.InOrderReceiveStep : Model.Lifecycle.Oracle →
  Model.Lifecycle.Session → Model.Lifecycle.Session → Prop :=
fun oracle m m' =>
  Tacenta.UnitLifecycleReceivePreserve.KeepsAgreementState m.braid m'.braid ∧
    (m'.triple = m.triple ∧ m'.ratchetPrivate = m.ratchetPrivate ∨
      ∃ hdr dr ds cand mk,
        Tacenta.UnitLifecycleReceivePreserve.InOrder m.triple hdr ∧
          Model.Messages.canonicalKey hdr.dr.dh = true ∧
            Model.Triple.receiveDetailed m.triple hdr dr ds (oracle.dhPublic cand) none = Except.ok (m'.triple, mk) ∧
              m'.ratchetPrivate =
                if (m'.triple.classical.dhsPub == m.triple.classical.dhsPub) = true then m.ratchetPrivate else cand)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleReceivePreserve.InOrderReceiveStep

/--
info: def Tacenta.UnitLifecycleReceivePreserve.SameAgreementKind : tacenta_braid.State → tacenta_braid.State → Prop :=
fun x x_1 =>
  match x, x_1 with
  | tacenta_braid.State.NoHeaderReceived e a a_1, tacenta_braid.State.NoHeaderReceived e' a_2 a_3 => e' = e
  | tacenta_braid.State.KeysSampled e a a_1 a_2, tacenta_braid.State.KeysSampled e' a_3 a_4 a_5 => e' = e
  | x, x_2 => False
-/
#guard_msgs in
#print Tacenta.UnitLifecycleReceivePreserve.SameAgreementKind
