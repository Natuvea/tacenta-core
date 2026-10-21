import Translation.UnitTripleInvModel
import Translation.UnitLifecycleResponderReply

/-!
# `Session::encrypt` keeps `Session::invariant` at an agreement state that takes no draw

`UnitLifecycleResponderReply` shows that the responder's `Session::encrypt` at the session `establish_responder`
returned emits the reply and leaves a session `sB''` that refines the model's step; it does not say whether `sB''`
passes `Session::invariant`.  Each earlier successor (`UnitLifecycleEstablishedEncrypt`,
`UnitLifecycleResponderSuccessor`) rebuilt the invariant by hand at one literal shape.  This module proves the step
once, for every session at an agreement state whose send takes no draw, and applies it to the reply.

## What it shows

* `modelTripleInv_send`: the model Triple's send without an agreement output keeps `ModelTripleInv`
  (`UnitTripleInvModel`), at every sending epoch.  The classical send steps the sending chain and leaves the keys, the
  receiving chain, the clock and the store; the sparse send replaces one chain entry of the table at an epoch the
  table holds and leaves the epoch, the direction and the store (`ratchet_send_frame`, `spqr_send_frame`).
* `encrypt_session_cases`: at a model agreement state whose send takes no draw, the model's `encrypt` leaves the
  Triple as it was or as a successful Triple send without an agreement output, and the agreement at its epoch.
* `CounterRoom s k`, the counter budget: room for `k` more operations below the four ceilings `CounterHeadroom`
  names, each costing at most one step of the clock and of each epoch and at most `MAX_SKIP + 1` of a chain counter.
  `counterRoom_zero`: `CounterRoom s 0` is `CounterHeadroom s`.  `counterRoom_iff_model`: the budget is the model
  session's.  `modelCounterRoom_encrypt`: such an `encrypt` spends at most one unit.
* `braid_send_no_draw`: the translated `Braid::send` at each of the nine agreement states whose send takes no draw
  (the six encoder states `KeysSampled`, `HeaderSent`, `Ct1Received`, `Ct1Sampled`, `EkReceivedCt1Sampled`,
  `Ct2Sampled`, and the three that send an empty message, `EkSentCt1Received`, `NoHeaderReceived`,
  `Ct1Acknowledged`) keeps `Braid::invariant`, takes no randomness, has no output, and returns a state of the same
  kind at the same epoch.  Under `KemCloneAgrees` (the state's key pair is cloned before the step).
* `structural_congr`: `Session::structural_invariant` reads the Triple only through its sending key, direction and
  sparse epoch, and the agreement only through `failed`, `is_initiator`, `epoch` and `state_tag`.
* `encrypt_keeps_invariant_no_draw`: **for every session that passes `Session::invariant`, has room for `k + 1`
  operations and refines a model session whose agreement send takes no draw, every successful `encrypt` there whose
  session refines the model's `encrypt` step leaves a session that passes `Session::invariant` and has room for `k`.**
  The relation after the call is a hypothesis (the encrypt refinement supplies it); the boundary record is
  `KemCloneAgrees`.
* `initiator_first_send_responder_reply_successor`: on the run of the initiator's first send, under the hypotheses of
  `initiator_first_send_responder_replies` and no other, the session `sB''` the responder's reply leaves passes
  `Session::invariant`, meets `CounterHeadroom` and has room for every `j` with `j + 3 < u32::MAX` further
  operations.  `initiator_first_send_responder_reply_admissible` states the invariant and the ceilings at every return
  of that call.
* `established_encrypt_triple_invariant_via_preservation`: the Triple leaf of the initiator's session after its first
  send, re-derived from the establishment's invariant through the bridge and the model's send, with no shape.

## How

The Triple half goes through the model: the code Triple's invariant is `ModelTripleInv` of the model Triple it refines
(`triple_invariant_iff_model`), the model's send keeps that, and the relation after the call carries it back.  The
agreement half is a walk of the translated send: the clone of the state is the state up to its opaque key pair and
encapsulation state (`encoder_clone_eq`, `decoder_clone_eq`, `vec_clone_u8`, the authenticator's clone), `next_chunk`
keeps the codewords and the value of `Encoder::invariant` (`next_chunk_keeps`), and `key_pair_valid` passes at a
clone when it passes at the original (`key_pair_valid_clone`).  The budget is carried to the model and back.  On the
run, `sB'`, its relation and its invariant are the successor results' at the same call, and the call and the
relation after it are the reply's.

## Laws and premises

No new law and no new per-run premise.  The general lemma takes `KemCloneAgrees`, a boundary record the Braid send
record `BraidSendRefinementContracts` already carries (a key pair's clone answers `header`, `ek_vector` and `decapsulate`
as the original did, and an encapsulation state's clone answers `encapsulate2`; this step uses the first two); `CounterRoom` is internal to the lemma (the run headline
concludes `CounterHeadroom` and states the budget it computes).  No premise names a width, so each result holds on 32-
and 64-bit targets.

## Trust

`initiator_first_send_responder_reply_successor`, `initiator_first_send_responder_reply_admissible` and
`established_encrypt_triple_invariant_via_preservation` are compiler-trusted through the nine `native_decide`
constants of the encrypt and decrypt refinements they apply.  Every other result here, the general lemma included,
rests on the kernel and opaque constants only (pins below).  That label does not extend to any instance of the general
lemma: the relation after the call carries the Triple half (the code Triple's invariant is read off the model Triple
it relates to), the three Triple fields the structural clauses read and the budget, and only the agreement half is a
walk of translated code; every instance gets that relation from the encrypt refinement, which is compiler-trusted.

## Where its premises are exhibited

The general lemma quantifies over the nine agreement states whose send takes no draw.  Its premises, the relation after
the call and the agreement walk's included, are exhibited together only at `NoHeaderReceived`, on the reply's run; at
the other eight states no run in this tree exhibits them, and the relation after the call there would come from an
encrypt refinement whose leaf hypotheses are not discharged at those states.

## What it does not show

* The general lemma at any of the eight no-draw states other than `NoHeaderReceived` on a run: no run here exhibits
  its premises there.
* `encrypt` at an agreement state whose send draws (`KeysUnsampled`, `HeaderReceived`), and so a Triple send with an
  agreement output (`advance`, a new chain pair, `clearOldEpochs`): not covered.  In particular the initiator's first
  send itself is not an instance; only its Triple leaf is re-derived.
* A refused `encrypt`: no statement here about the session a refusal returns.
* Any receive: `decrypt` and `decrypt_ratchet` keeping the invariant are not shown.
* That the ceilings are kept or refused at: false of the code, which refuses one step later than `CounterHeadroom`
  asks (the clock clamps at `u32::MAX - 1` and never refuses; a chain counter reaches `u64::MAX`; both epochs reach
  `u64::MAX - 1`), so the statements spend a budget instead.
* The budget at any session other than the model session after the first receipt (`modelCounterRoom_firstReceipt`).
* That the relation after the call holds: a hypothesis of the general lemma, supplied on the run by the encrypt
  refinement.
* A second message in either direction, the header's later chunks, the responder's first sampling send, a restored
  copy of a session; that the real primitives meet `KemCloneAgrees` or the records and laws the run rests on.
* That `Session::invariant` says the session is reachable: it is a predicate on fields.
* A new reach: the headline's hypotheses are those of `initiator_first_send_responder_replies`, whose reach
  `first_send_reply_reachable` exhibits them at the real constants; this module adds none.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv)

namespace Tacenta.UnitLifecycleSendPreserve

open Tacenta.UnitTripleInvModel
open Tacenta.UnitLifecycleT3 (DhView SessionRefines)

/-! ## The model's send without an agreement output keeps `ModelTripleInv` -/

section Model

/-- **The classical model send's frame**: a successful send had a sending chain, keeps one, and leaves the sending
key, the peer key, the receiving chain, the clock and the store as they were.  Model only. -/
theorem ratchet_send_frame {st st' : Model.State.State} {hd : Model.State.Header} {key : Model.State.Key}
    (hs : Model.Ratchet.sendDetailed st = .ok (st', hd, key)) :
    st.cks.isSome = true ∧ st'.cks.isSome = true ∧ st'.dhsPub = st.dhsPub ∧ st'.dhrPub = st.dhrPub ∧
      st'.ckr = st.ckr ∧ st'.events = st.events ∧ st'.skipped = st.skipped := by
  unfold Model.Ratchet.sendDetailed at hs
  rcases hck : st.cks with _ | ck
  · rw [hck] at hs; simp at hs
  · rw [hck] at hs
    simp only at hs
    split_ifs at hs
    simp only [Except.ok.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, -, -⟩ := hs
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The classical model send keeps `ModelRatchetInv`.**  Model only. -/
theorem modelRatchetInv_send {st st' : Model.State.State} {hd : Model.State.Header} {key : Model.State.Key}
    (h : ModelRatchetInv st) (hs : Model.Ratchet.sendDetailed st = .ok (st', hd, key)) :
    ModelRatchetInv st' := by
  obtain ⟨-, hcks', hdhs, hdhr, hckr, hev, hsk⟩ := ratchet_send_frame hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsk]; exact h.store_bound
  · rw [hev]; exact h.clock_room
  · rw [hsk, hev]; exact h.fresh
  · rw [hsk]; exact h.store_map
  · intro hc
    rw [hckr] at hc
    exact ⟨hcks', hdhr ▸ (h.chains hc).2⟩
  · rw [hdhs]; exact h.dhs_canonical
  · rw [hdhr]; exact h.dhr_canonical
  · rw [hsk]; exact h.store_canonical

/-- The chain entry `findChains` returns is in the table, at the epoch asked for. -/
theorem findChains_mem {st : Model.SparseRatchet.State} {e : Nat} {cs : Model.SparseRatchet.Chains}
    (h : Model.SparseRatchet.findChains st e = some cs) : (e, cs) ∈ st.chains := by
  unfold Model.SparseRatchet.findChains at h
  rcases hf : st.chains.find? (fun p => p.1 == e) with _ | p
  · rw [hf] at h; simp at h
  · rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hmem := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [beq_iff_eq] at hp
    obtain ⟨p1, p2⟩ := p
    simp only at hp h
    subst hp h
    exact hmem

/-- **The sparse model send's frame, without an agreement output**: the epoch, the direction and the store are as
they were, every chain epoch of the new table is one of the old table's, and every chain counter of the new table is
at most one more than a counter of the old table.  Model only. -/
theorem spqr_send_frame {st st' : Model.SparseRatchet.State} {e n : Nat} {key : Model.State.Key}
    (hs : Model.SparseRatchet.sendDetailed st e none = .ok (st', n, key)) :
    ∃ cs : Model.SparseRatchet.Chains, (e, cs) ∈ st.chains ∧ ∃ c' : Model.SparseRatchet.Chains,
      st'.chains = st.chains.filter (fun p => !(p.1 == e)) ++ [(e, c')] ∧ c'.receive = cs.receive ∧
      (∀ ch, c'.send = some ch → ∃ ch0, cs.send = some ch0 ∧ ch.n = ch0.n + 1) ∧
      st'.epoch = st.epoch ∧ st'.direction = st.direction ∧ st'.skipped = st.skipped := by
  simp only [Model.SparseRatchet.sendDetailed, Model.SparseRatchet.maybeAdvanceDetailed] at hs
  rcases hf : Model.SparseRatchet.findChains st e with _ | cs
  · rw [hf] at hs; simp at hs
  rw [hf] at hs
  simp only at hs
  rcases hsend : cs.send with _ | ch
  · rw [hsend] at hs; simp at hs
  rw [hsend] at hs
  simp only at hs
  split_ifs at hs
  simp only [Except.ok.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, -, -⟩ := hs
  refine ⟨cs, findChains_mem hf, _, rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro ch' hch'
  simp only [Option.some.injEq] at hch'
  exact ⟨ch, hsend, by rw [← hch']⟩

/-- Membership in the table after a send at epoch `e`. -/
theorem mem_sent_chains {L : List (Nat × Model.SparseRatchet.Chains)} {e : Nat} {c' : Model.SparseRatchet.Chains}
    {p : Nat × Model.SparseRatchet.Chains} (h : p ∈ L.filter (fun p => !(p.1 == e)) ++ [(e, c')]) :
    (p ∈ L ∧ p.1 ≠ e) ∨ p = (e, c') := by
  simp only [List.mem_append, List.mem_filter, List.mem_singleton, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact h

/-- **The sparse model send without an agreement output keeps `ModelSpqrInv`.**  Model only. -/
theorem modelSpqrInv_send {st st' : Model.SparseRatchet.State} {e n : Nat} {key : Model.State.Key}
    (h : ModelSpqrInv st) (hs : Model.SparseRatchet.sendDetailed st e none = .ok (st', n, key)) :
    ModelSpqrInv st' := by
  obtain ⟨cs, hmem, c', hch, -, -, hep, -, hsk⟩ := spqr_send_frame hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsk]; exact h.store_bound
  · intro q hq
    rw [hch] at hq
    rw [hep]
    rcases mem_sent_chains hq with ⟨hq', -⟩ | rfl
    · exact h.epoch_window q hq'
    · exact h.epoch_window (e, cs) hmem
  · rw [hch, List.pairwise_append]
    refine ⟨h.chains_distinct.sublist List.filter_sublist, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne] at ha
    simp only [List.mem_singleton] at hb
    subst hb
    exact ha.2
  · obtain ⟨q, hq, hqe⟩ := h.current_present
    rw [hch, hep]
    by_cases hqe' : q.1 = e
    · exact ⟨(e, c'), List.mem_append_right _ (List.mem_singleton_self _), by rw [← hqe', hqe]⟩
    · exact ⟨q, List.mem_append_left _ (List.mem_filter.mpr ⟨hq, by simpa using hqe'⟩), hqe⟩
  · intro a ha
    rw [hsk] at ha
    obtain ⟨q, hq, hqa⟩ := h.skipped_chained a ha
    rw [hch]
    by_cases hqe' : q.1 = e
    · exact ⟨(e, c'), List.mem_append_right _ (List.mem_singleton_self _), by rw [← hqe', hqa]⟩
    · exact ⟨q, List.mem_append_left _ (List.mem_filter.mpr ⟨hq, by simpa using hqe'⟩), hqa⟩
  · rw [hsk]; exact h.skipped_map

/-- **The model Triple's send without an agreement output keeps `ModelTripleInv`**, at every sending epoch.  Model
only. -/
theorem modelTripleInv_send {m m' : Model.Triple.State} {e : Nat} {hd : Model.Triple.Header}
    {key : Model.State.Key} (h : ModelTripleInv m)
    (hs : Model.Triple.sendDetailed m e none = .ok (m', hd, key)) : ModelTripleInv m' := by
  obtain ⟨hr, hq, hroles⟩ := h
  unfold Model.Triple.sendDetailed at hs
  rcases hc : Model.Ratchet.sendDetailed m.classical with _ | ⟨c, dr, mkc⟩
  · rw [hc] at hs; simp at hs
  rw [hc] at hs
  simp only at hs
  rcases hp : Model.SparseRatchet.sendDetailed m.postQuantum e none with _ | ⟨q, pqN, mkq⟩
  · rw [hp] at hs; simp at hs
  rw [hp] at hs
  simp only [Except.ok.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, -, -⟩ := hs
  refine ⟨modelRatchetInv_send hr hc, modelSpqrInv_send hq hp, ?_⟩
  obtain ⟨hcks, hcks', -, -, hckr, -, -⟩ := ratchet_send_frame hc
  obtain ⟨-, -, -, -, -, -, -, hdir, -⟩ := spqr_send_frame hp
  unfold ModelRolesAgree at hroles ⊢
  simp only
  rw [hckr, hdir]
  rcases hm : m.classical.cks with _ | x
  · rw [hm] at hcks; simp at hcks
  rcases hm' : c.cks with _ | y
  · rw [hm'] at hcks'; simp at hcks'
  rw [hm] at hroles
  rcases hk : m.classical.ckr with _ | z
  · simp only [hk] at hroles ⊢; exact hroles
  · simp

end Model

/-! ## The model's `encrypt` at an agreement state that takes no draw -/

section ModelEncrypt

/-- At an agreement state that takes no draw, the model's agreement send has no output and keeps the epoch.  Model
only. -/
theorem braid_send_no_draw_model (K : Model.Braid.Kem) (st : Model.Braid.BraidState)
    (h : Model.Lifecycle.braidSendNeedsDraw st = false) :
    (Model.Braid.send K 0 st).2.2.1 = none ∧ (Model.Braid.send K 0 st).2.2.2.epoch = st.epoch := by
  cases st <;> simp_all [Model.Lifecycle.braidSendNeedsDraw, Model.Braid.send, Model.Braid.BraidState.epoch]

/-- **The model's `encrypt` at an agreement state that takes no draw leaves a session whose Triple is either the one
it was given or a successful Triple send without an agreement output from it, and whose agreement is at the epoch it
was.**  Every view, oracle and plaintext.  Model only. -/
theorem encrypt_session_cases (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (m : Model.Lifecycle.Session) (pt : Model.Lifecycle.Bytes)
    (hdraw : Model.Lifecycle.braidSendNeedsDraw m.braid = false) :
    ((Model.Lifecycle.encrypt view oracle m pt).session.triple = m.triple ∨
      ∃ e hd key, Model.Triple.sendDetailed m.triple e none =
        .ok ((Model.Lifecycle.encrypt view oracle m pt).session.triple, hd, key)) ∧
    (Model.Lifecycle.encrypt view oracle m pt).session.braid.epoch = m.braid.epoch := by
  obtain ⟨hout, hep⟩ := braid_send_no_draw_model oracle.braidKem m.braid hdraw
  unfold Model.Lifecycle.encrypt
  by_cases hf : Model.Lifecycle.agreementFailed m = true
  · simp [hf]
  · simp only [hf, Bool.false_eq_true, if_false, Model.Lifecycle.sendAgreement_no_draw oracle m.braid hdraw]
    rcases hb : Model.Braid.send oracle.braidKem 0 m.braid with ⟨msg, ep, out, nxt⟩
    rw [hb] at hout hep
    simp only at hout hep
    subst hout
    simp only [Model.Lifecycle.sparseOutputOf, Option.map_none]
    split
    · exact ⟨Or.inl rfl, hep⟩
    · split
      · exact ⟨Or.inl rfl, rfl⟩
      · split
        · exact ⟨Or.inl rfl, rfl⟩
        · rename_i tripleNext header messageKey hsend
          split
          · exact ⟨Or.inl rfl, rfl⟩
          · exact ⟨Or.inr ⟨ep, header, messageKey, hsend⟩, hep⟩

end ModelEncrypt

/-! ## The counter budget -/

section Budget

/-- **The counter budget**: room for `k` more operations below each of the four ceilings the refinement theorems
take (`CounterHeadroom`), each operation costing at most one step of the clock and of each epoch, and at most
`MAX_SKIP + 1` steps of a chain counter.  `CounterRoom s 0` is `CounterHeadroom s` (`counterRoom_zero`).  Stated of the
translated session, at its machine widths. -/
structure CounterRoom (s : lifecycle.Session) (k : Nat) : Prop where
  classicalEvents : s.triple.classical.events.val + k + 1 < Std.U32.max
  sparseEpoch : s.triple.post_quantum.epoch.val + k + 1 < Std.U64.max
  sparseCounters : ∀ p ∈ s.triple.post_quantum.chains.val, ∀ ch : tacenta_spqr.Chain,
    (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n.val + 1001 * k < Std.U64.max
  braidEpoch : (Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state).val + k + 1 < Std.U64.max

/-- **No room for further operations is exactly the four ceilings.** -/
theorem counterRoom_zero (s : lifecycle.Session) :
    CounterRoom s 0 ↔ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by simpa using h1, by simpa using h2, fun p hp ch hch => by simpa using h3 p hp ch hch,
      by simpa using h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by simpa using h1, by simpa using h2, fun p hp ch hch => by simpa using h3 p hp ch hch,
      by simpa using h4⟩

/-- The same budget, read on the model session. -/
structure ModelCounterRoom (m : Model.Lifecycle.Session) (k : Nat) : Prop where
  classicalEvents : m.triple.classical.events + k + 1 < Std.U32.max
  sparseEpoch : m.triple.postQuantum.epoch + k + 1 < Std.U64.max
  sparseCounters : ∀ p ∈ m.triple.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
    (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n + 1001 * k < Std.U64.max
  braidEpoch : m.braid.epoch + k + 1 < Std.U64.max

/-- The agreement's epoch is the model's. -/
theorem epoch_val_refines {K : Model.Braid.Kem} {st : tacenta_braid.State} {m : Model.Braid.BraidState}
    (h : Tacenta.SessionUnitBraidT3.StateRefines K st m) :
    (Tacenta.SessionUnitBraidT1.State.epoch_val st).val = m.epoch := by
  cases st <;> cases m <;>
    simp_all [Tacenta.SessionUnitBraidT3.StateRefines, Tacenta.SessionUnitBraidT1.State.epoch_val,
      Model.Braid.BraidState.epoch]

/-- **The budget of a translated session is the budget of the model session it refines.** -/
theorem counterRoom_iff_model {dh : DhView} {K : Model.Braid.Kem} {s : lifecycle.Session}
    {m : Model.Lifecycle.Session} (hrel : SessionRefines dh K s m) (k : Nat) :
    CounterRoom s k ↔ ModelCounterRoom m k := by
  obtain ⟨hc, hq⟩ := hrel.triple
  have hev : s.triple.classical.events.val = m.triple.classical.events := by rw [← hc]; rfl
  have hep : s.triple.post_quantum.epoch.val = m.triple.postQuantum.epoch := by rw [← hq]; rfl
  have hch : s.triple.post_quantum.chains.val.map Tacenta.SessionUnitSpqrT3.chainsEntryOf =
      m.triple.postQuantum.chains := by rw [← hq]; rfl
  have hbe := epoch_val_refines hrel.braid
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by omega, by omega, ?_, by omega⟩
    intro p hp ch hcp
    rw [← hch, List.mem_map] at hp
    obtain ⟨q, hq', rfl⟩ := hp
    simp only [Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf,
      Option.map_eq_some_iff] at hcp
    rcases hcp with ⟨c, hc', rfl⟩ | ⟨c, hc', rfl⟩
    · exact h3 q hq' c (Or.inl hc')
    · exact h3 q hq' c (Or.inr hc')
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by omega, by omega, ?_, by omega⟩
    intro q hq' c hcq
    have := h3 (Tacenta.SessionUnitSpqrT3.chainsEntryOf q) (hch ▸ List.mem_map_of_mem hq')
      (Tacenta.SessionUnitSpqrT3.chainOf c)
    simp only [Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf,
      Tacenta.SessionUnitSpqrT3.chainOf] at this
    rcases hcq with h | h
    · exact this (Or.inl (by rw [h]; rfl))
    · exact this (Or.inr (by rw [h]; rfl))

/-- **The model's `encrypt` at an agreement state that takes no draw spends at most one unit of the budget.**  Model
only. -/
theorem modelCounterRoom_encrypt (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (m : Model.Lifecycle.Session) (pt : Model.Lifecycle.Bytes)
    (hdraw : Model.Lifecycle.braidSendNeedsDraw m.braid = false) (k : Nat) (h : ModelCounterRoom m (k + 1)) :
    ModelCounterRoom (Model.Lifecycle.encrypt view oracle m pt).session k := by
  obtain ⟨htr, hbe⟩ := encrypt_session_cases view oracle m pt hdraw
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, by rw [hbe]; omega⟩
  · rcases htr with htr | ⟨e, hd, key, hs⟩
    · rw [htr]; omega
    · unfold Model.Triple.sendDetailed at hs
      split at hs
      · simp at hs
      · rename_i c dr mkc hc
        split at hs
        · simp at hs
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hs
          rw [← hs.1]
          obtain ⟨-, -, -, -, -, hev, -⟩ := ratchet_send_frame hc
          simp only; rw [hev]; omega
  · rcases htr with htr | ⟨e, hd, key, hs⟩
    · rw [htr]; omega
    · unfold Model.Triple.sendDetailed at hs
      split at hs
      · simp at hs
      · split at hs
        · simp at hs
        · rename_i q pqN mkq hp
          simp only [Except.ok.injEq, Prod.mk.injEq] at hs
          rw [← hs.1]
          obtain ⟨-, -, -, -, -, -, hep, -, -⟩ := spqr_send_frame hp
          simp only; rw [hep]; omega
  · rcases htr with htr | ⟨e, hd, key, hs⟩
    · rw [htr]
      intro p hp ch hch
      have := h3 p hp ch hch
      omega
    · unfold Model.Triple.sendDetailed at hs
      split at hs
      · simp at hs
      · split at hs
        · simp at hs
        · rename_i q pqN mkq hp
          simp only [Except.ok.injEq, Prod.mk.injEq] at hs
          rw [← hs.1]
          obtain ⟨cs, hmem, c', hch, hrecv, hsend, -, -, -⟩ := spqr_send_frame hp
          simp only
          rw [hch]
          intro p hp' ch hchp
          rcases mem_sent_chains hp' with ⟨hp'', -⟩ | rfl
          · have := h3 p hp'' ch hchp
            omega
          · rcases hchp with hs' | hr'
            · obtain ⟨ch0, hch0, hn⟩ := hsend ch hs'
              have := h3 _ hmem ch0 (Or.inl hch0)
              omega
            · have := h3 _ hmem ch (Or.inr (by rw [← hrecv]; exact hr'))
              omega

end Budget

/-! ## The translated agreement send at a state that takes no draw -/

section BraidSend

/-- The agreement states whose send takes no draw and has not failed. -/
def SendsWithoutDraw : tacenta_braid.State → Prop
  | .KeysUnsampled _ _ => False
  | .HeaderReceived _ _ _ _ => False
  | .Failed => False
  | _ => True

/-- A state related to a model state whose send takes no draw, and that has not failed, sends without a draw. -/
theorem sendsWithoutDraw_of_refines {K : Model.Braid.Kem} {st : tacenta_braid.State}
    {m : Model.Braid.BraidState} (h : Tacenta.SessionUnitBraidT3.StateRefines K st m)
    (hdraw : Model.Lifecycle.braidSendNeedsDraw m = false) (hf : st ≠ .Failed) : SendsWithoutDraw st := by
  cases st <;> cases m <;>
    simp_all [Tacenta.SessionUnitBraidT3.StateRefines, Model.Lifecycle.braidSendNeedsDraw, SendsWithoutDraw]

/-- A byte vector's clone is the vector.  Hypothesis-free. -/
theorem vec_clone_u8 (v : alloc.vec.Vec U8) : alloc.vec.CloneVec.clone core.clone.CloneU8 v = ok v :=
  Tacenta.SessionUnitTripleT1.vec_clone_id _ v (fun _ _ => rfl)

/-- An encoder's clone is the encoder.  Hypothesis-free. -/
theorem encoder_clone_eq (e : tacenta_erasure.Encoder) :
    tacenta_erasure.Encoder.Insts.CoreCloneClone.clone e = ok e := by
  unfold tacenta_erasure.Encoder.Insts.CoreCloneClone.clone
  rw [Tacenta.SessionUnitTripleT1.vec_clone_id _ e.chunks
    (fun x _ => Tacenta.UnitLifecycleResponderReply.array_clone_u8 x)]
  simp [lift, core.clone.impls.CloneU16.clone, core.clone.impls.CloneBool.clone]

/-- A decoder's clone is the decoder.  Hypothesis-free. -/
theorem decoder_clone_eq (d : tacenta_erasure.Decoder) :
    tacenta_erasure.Decoder.Insts.CoreCloneClone.clone d = ok d := by
  unfold tacenta_erasure.Decoder.Insts.CoreCloneClone.clone
  rw [Tacenta.SessionUnitTripleT1.vec_clone_id _ d.«have» (fun _ _ => rfl)]
  simp [lift, core.clone.impls.CloneUsize.clone]

/-- **`next_chunk` keeps the encoder's codewords and the value of `Encoder::invariant`.**  Hypothesis-free. -/
theorem next_chunk_keeps {enc enc' : tacenta_erasure.Encoder} {c : Option tacenta_erasure.Chunk}
    (h : tacenta_erasure.Encoder.next_chunk enc = ok (c, enc')) :
    enc'.chunks = enc.chunks ∧ tacenta_erasure.Encoder.invariant enc' = tacenta_erasure.Encoder.invariant enc := by
  unfold tacenta_erasure.Encoder.next_chunk at h
  by_cases hex : enc.exhausted = true
  · simp only [hex, if_true, ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · have hex' : enc.exhausted = false := by simpa using hex
    simp only [hex', Bool.false_eq_true, if_false] at h
    obtain ⟨t, -, h⟩ := bind_eq_ok_inv h
    have hinv : ∀ e' : tacenta_erasure.Encoder, e'.chunks = enc.chunks →
        (e'.exhausted = true → e'.next = core.num.U16.MAX) → e'.exhausted = false ∨ enc.next = core.num.U16.MAX →
        tacenta_erasure.Encoder.invariant e' = tacenta_erasure.Encoder.invariant enc := by
      intro e' hc hx _
      unfold tacenta_erasure.Encoder.invariant
      rw [hc, hex']
      rcases he : e'.exhausted
      · simp
      · simp [hx he]
    by_cases hmax : enc.next = core.num.U16.MAX
    · simp only [hmax, if_true] at h
      split at h
      all_goals
        repeat' (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
        simp only [ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ⟨rfl, hinv _ rfl (fun _ => rfl) (Or.inr hmax)⟩
    · simp only [hmax, if_false] at h
      split at h
      all_goals
        repeat' (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
        simp only [ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ⟨rfl, hinv _ rfl (fun h' => by simp at h') (Or.inl rfl)⟩

/-- `encoder_sized` reads only the encoder's codewords. -/
theorem encoder_sized_congr {enc enc' : tacenta_erasure.Encoder} (h : enc'.chunks = enc.chunks) :
    tacenta_braid.encoder_sized enc' = tacenta_braid.encoder_sized enc := by
  funext len
  simp [tacenta_braid.encoder_sized, tacenta_erasure.Encoder.needed, h]

/-- A key pair's clone passes `key_pair_valid` when the key pair does, under `KemCloneAgrees`. -/
theorem key_pair_valid_clone (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees)
    {kp kp' : tacenta_kem.IncrementalKeyPair}
    (hc : tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp = ok kp')
    (h : tacenta_braid.key_pair_valid kp = ok true) : tacenta_braid.key_pair_valid kp' = ok true := by
  unfold tacenta_braid.key_pair_valid at h ⊢
  obtain ⟨hd, hh, h⟩ := bind_eq_ok_inv h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_inv h
  rw [(hkcl.1 kp kp' hc).1 hd hh, (hkcl.1 kp kp' hc).2.1 v hv]
  exact h



set_option linter.unusedSimpArgs false in
/-- **`Braid::send` at an agreement state that takes no draw keeps `Braid::invariant`**, takes no randomness, has no
output, and returns a state of the same kind at the same epoch: the same `failed`, `is_initiator`, `epoch` and
`state_tag` the session's structural clauses read.  Under `KemCloneAgrees` (the state's key pair is cloned before the
step).  Covers the six encoder states (`KeysSampled`, `HeaderSent`, `Ct1Received`, `Ct1Sampled`,
`EkReceivedCt1Sampled`, `Ct2Sampled`), where the encoder emits its next chunk, and the three states that send an
empty message (`EkSentCt1Received`, `NoHeaderReceived`, `Ct1Acknowledged`). -/
theorem braid_send_no_draw (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees) {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (b : tacenta_braid.Braid)
    (hnd : SendsWithoutDraw b.state) (hinv : tacenta_braid.Braid.invariant b = ok true) (rng : R)
    (msg : tacenta_braid.Msg) (ep : U64) (out : Option tacenta_braid.Output) (b' : tacenta_braid.Braid) (rng' : R)
    (h : tacenta_braid.Braid.send rc crc b rng = ok ((msg, ep, out, b'), rng')) :
    rng' = rng ∧ out = none ∧ tacenta_braid.Braid.invariant b' = ok true ∧
      tacenta_braid.Braid.failed b' = tacenta_braid.Braid.failed b ∧
      tacenta_braid.Braid.is_initiator b' = tacenta_braid.Braid.is_initiator b ∧
      tacenta_braid.Braid.epoch b' = tacenta_braid.Braid.epoch b ∧
      tacenta_braid.Braid.state_tag b' = tacenta_braid.Braid.state_tag b ∧
      Tacenta.SessionUnitBraidT1.State.epoch_val b'.state = Tacenta.SessionUnitBraidT1.State.epoch_val b.state := by
  obtain ⟨st⟩ := b
  unfold tacenta_braid.Braid.send at h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_inv h
  obtain ⟨⟨⟨m1, o1, nxt⟩, rng1⟩, hstep, h⟩ := bind_eq_ok_inv h
  obtain ⟨i, -, h⟩ := bind_eq_ok_inv h
  simp only [ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, -, rfl, rfl⟩, rfl⟩ := h
  cases st with
  | KeysUnsampled e a => exact False.elim hnd
  | HeaderReceived e a hdr d => exact False.elim hnd
  | Failed => exact False.elim hnd
  | KeysSampled e a kp enc =>
    simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
      bind_tc_ok, Tacenta.UnitLifecycleResponderReply.auth_clone_eq, encoder_clone_eq, decoder_clone_eq,
      vec_clone_u8, ok.injEq] at hs
    rcases hk : tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp with kp' | _ | _ <;>
      simp only [hk, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hs
    subst hs
    simp only [tacenta_braid.Braid.step_send] at hstep
    obtain ⟨⟨c, enc'⟩, hnc, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨mm, -, hstep⟩ := bind_eq_ok_inv hstep
    simp only [ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := hstep
    obtain ⟨hch, hei⟩ := next_chunk_keeps hnc
    refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    unfold tacenta_braid.Braid.invariant at hinv ⊢
    simp only at hinv ⊢
    rw [hei, encoder_sized_congr hch]
    have hkv : tacenta_braid.key_pair_valid kp = ok true := by
      revert hinv
      generalize tacenta_braid.key_pair_valid kp = r
      intro hr
      repeat' first
        | (replace hr := bind_eq_ok_inv hr; obtain ⟨_, _, hr⟩ := hr)
        | split at hr
        | simp at hr
      all_goals exact hr
    rw [key_pair_valid_clone hkcl hk hkv]
    rw [hkv] at hinv
    exact hinv
  | HeaderSent e a kp d enc =>
    simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
      bind_tc_ok, Tacenta.UnitLifecycleResponderReply.auth_clone_eq, encoder_clone_eq, decoder_clone_eq,
      vec_clone_u8, ok.injEq] at hs
    rcases hk : tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp with kp' | _ | _ <;>
      simp only [hk, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hs
    subst hs
    simp only [tacenta_braid.Braid.step_send] at hstep
    obtain ⟨⟨c, enc'⟩, hnc, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨mm, -, hstep⟩ := bind_eq_ok_inv hstep
    simp only [ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := hstep
    obtain ⟨hch, hei⟩ := next_chunk_keeps hnc
    refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    unfold tacenta_braid.Braid.invariant at hinv ⊢
    simp only at hinv ⊢
    rw [hei, encoder_sized_congr hch]
    have hkv : tacenta_braid.key_pair_valid kp = ok true := by
      revert hinv
      generalize tacenta_braid.key_pair_valid kp = r
      intro hr
      repeat' first
        | (replace hr := bind_eq_ok_inv hr; obtain ⟨_, _, hr⟩ := hr)
        | split at hr
        | simp at hr
      all_goals exact hr
    rw [key_pair_valid_clone hkcl hk hkv]
    rw [hkv] at hinv
    exact hinv
  | Ct1Received e a kp ct1 enc =>
    simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
      bind_tc_ok, Tacenta.UnitLifecycleResponderReply.auth_clone_eq, encoder_clone_eq, decoder_clone_eq,
      vec_clone_u8, ok.injEq] at hs
    rcases hk : tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp with kp' | _ | _ <;>
      simp only [hk, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hs
    subst hs
    simp only [tacenta_braid.Braid.step_send] at hstep
    obtain ⟨⟨c, enc'⟩, hnc, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨mm, -, hstep⟩ := bind_eq_ok_inv hstep
    simp only [ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := hstep
    obtain ⟨hch, hei⟩ := next_chunk_keeps hnc
    refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    unfold tacenta_braid.Braid.invariant at hinv ⊢
    simp only at hinv ⊢
    rw [hei, encoder_sized_congr hch]
    have hkv : tacenta_braid.key_pair_valid kp = ok true := by
      revert hinv
      generalize tacenta_braid.key_pair_valid kp = r
      intro hr
      repeat' first
        | (replace hr := bind_eq_ok_inv hr; obtain ⟨_, _, hr⟩ := hr)
        | split at hr
        | simp at hr
      all_goals exact hr
    rw [key_pair_valid_clone hkcl hk hkv]
    rw [hkv] at hinv
    exact hinv
  | EkSentCt1Received e a kp ct1 d =>
    simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
      bind_tc_ok, Tacenta.UnitLifecycleResponderReply.auth_clone_eq, encoder_clone_eq, decoder_clone_eq,
      vec_clone_u8, ok.injEq] at hs
    rcases hk : tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp with kp' | _ | _ <;>
      simp only [hk, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hs
    subst hs
    simp only [tacenta_braid.Braid.step_send, tacenta_braid.state_back, tacenta_braid.Msg.empty, bind_tc_ok,
      ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := hstep
    refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
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
    rw [key_pair_valid_clone hkcl hk hkv]
    rw [hkv] at hinv
    exact hinv
  | NoHeaderReceived e a d =>
    simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
      bind_tc_ok, Tacenta.UnitLifecycleResponderReply.auth_clone_eq, encoder_clone_eq, decoder_clone_eq,
      vec_clone_u8, ok.injEq] at hs
    subst hs
    simp only [tacenta_braid.Braid.step_send, tacenta_braid.state_back, tacenta_braid.Msg.empty, bind_tc_ok,
      ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := hstep
    refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    unfold tacenta_braid.Braid.invariant at hinv ⊢
    simp only at hinv ⊢
    exact hinv
  | Ct1Sampled e a hdr es ct1 enc d =>
    simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
      bind_tc_ok, Tacenta.UnitLifecycleResponderReply.auth_clone_eq, encoder_clone_eq, decoder_clone_eq,
      vec_clone_u8, ok.injEq] at hs
    rcases hes : tacenta_kem.EncapsState.Insts.CoreCloneClone.clone es with es' | _ | _ <;>
      simp only [hes, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hs
    subst hs
    simp only [tacenta_braid.Braid.step_send] at hstep
    obtain ⟨⟨c, enc'⟩, hnc, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨mm, -, hstep⟩ := bind_eq_ok_inv hstep
    simp only [ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := hstep
    obtain ⟨hch, hei⟩ := next_chunk_keeps hnc
    refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    unfold tacenta_braid.Braid.invariant at hinv ⊢
    simp only at hinv ⊢
    rw [hei, encoder_sized_congr hch]
    exact hinv
  | EkReceivedCt1Sampled e a es ct1 ekv enc =>
    simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
      bind_tc_ok, Tacenta.UnitLifecycleResponderReply.auth_clone_eq, encoder_clone_eq, decoder_clone_eq,
      vec_clone_u8, ok.injEq] at hs
    rcases hes : tacenta_kem.EncapsState.Insts.CoreCloneClone.clone es with es' | _ | _ <;>
      simp only [hes, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hs
    subst hs
    simp only [tacenta_braid.Braid.step_send] at hstep
    obtain ⟨⟨c, enc'⟩, hnc, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨mm, -, hstep⟩ := bind_eq_ok_inv hstep
    simp only [ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := hstep
    obtain ⟨hch, hei⟩ := next_chunk_keeps hnc
    refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    unfold tacenta_braid.Braid.invariant at hinv ⊢
    simp only at hinv ⊢
    rw [hei, encoder_sized_congr hch]
    exact hinv
  | Ct1Acknowledged e a hdr es ct1 d =>
    simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
      bind_tc_ok, Tacenta.UnitLifecycleResponderReply.auth_clone_eq, encoder_clone_eq, decoder_clone_eq,
      vec_clone_u8, ok.injEq] at hs
    rcases hes : tacenta_kem.EncapsState.Insts.CoreCloneClone.clone es with es' | _ | _ <;>
      simp only [hes, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hs
    subst hs
    simp only [tacenta_braid.Braid.step_send, tacenta_braid.state_back, tacenta_braid.Msg.empty, bind_tc_ok,
      ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := hstep
    refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    unfold tacenta_braid.Braid.invariant at hinv ⊢
    simp only at hinv ⊢
    exact hinv
  | Ct2Sampled e a enc =>
    simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
      bind_tc_ok, Tacenta.UnitLifecycleResponderReply.auth_clone_eq, encoder_clone_eq, decoder_clone_eq,
      vec_clone_u8, ok.injEq] at hs
    subst hs
    simp only [tacenta_braid.Braid.step_send] at hstep
    obtain ⟨⟨c, enc'⟩, hnc, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨mm, -, hstep⟩ := bind_eq_ok_inv hstep
    simp only [ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := hstep
    obtain ⟨hch, hei⟩ := next_chunk_keeps hnc
    refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    unfold tacenta_braid.Braid.invariant at hinv ⊢
    simp only at hinv ⊢
    rw [hei, encoder_sized_congr hch]
    exact hinv


end BraidSend

/-! ## The session's own clauses -/

section Session

/-- `Session::invariant` is its three parts: the structural clauses, `Triple::invariant` and `Braid::invariant`. -/
theorem session_invariant_iff (s : lifecycle.Session) :
    lifecycle.Session.invariant s = ok true ↔
      lifecycle.Session.structural_invariant s = ok true ∧
        tacenta_triple.State.invariant s.triple = ok true ∧ tacenta_braid.Braid.invariant s.braid = ok true := by
  constructor
  · intro h
    have hleaf := Tacenta.UnitLifecycleT1.session_invariant_gives_leaf_check s h
    refine ⟨?_, Tacenta.UnitLifecycleT1.leaf_check_gives_leaf_invariants s hleaf⟩
    unfold lifecycle.Session.invariant at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_inv h
    cases b
    · simp at h
    · exact hb
  · rintro ⟨h1, h2, h3⟩
    unfold lifecycle.Session.invariant lifecycle.Session.leaf_invariants
    simp [h1, h2, h3]

/-- **`Session::structural_invariant` reads the Triple only through its sending key, its direction and its sparse
epoch, and the agreement only through `failed`, `is_initiator`, `epoch` and `state_tag`**: replacing the two by ones
that agree on those leaves its value as it was.  Hypothesis-free. -/
theorem structural_congr (s : lifecycle.Session) (t : tacenta_triple.State) (b : tacenta_braid.Braid)
    (hdhs : t.classical.dhs_pub = s.triple.classical.dhs_pub)
    (hdir : t.post_quantum.direction = s.triple.post_quantum.direction)
    (hep : t.post_quantum.epoch = s.triple.post_quantum.epoch)
    (hf : tacenta_braid.Braid.failed b = tacenta_braid.Braid.failed s.braid)
    (hi : tacenta_braid.Braid.is_initiator b = tacenta_braid.Braid.is_initiator s.braid)
    (he : tacenta_braid.Braid.epoch b = tacenta_braid.Braid.epoch s.braid)
    (ht : tacenta_braid.Braid.state_tag b = tacenta_braid.Braid.state_tag s.braid) :
    lifecycle.Session.structural_invariant { s with triple := t, braid := b } =
      lifecycle.Session.structural_invariant s := by
  unfold lifecycle.Session.structural_invariant lifecycle.Session.is_responder
  simp only [tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public,
    tacenta_triple.State.direction, tacenta_spqr.State.impl.direction, tacenta_triple.State.epoch,
    tacenta_spqr.State.impl.epoch, hdhs, hdir, hep, hf, hi, he, ht]

/-- A successful `encrypt` passed the terminal guard: the agreement it was given had not failed. -/
theorem encrypt_ok_not_failed {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (s : lifecycle.Session) (pt : Slice U8) (rng : R) (v : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (h : lifecycle.Session.encrypt rc crc s pt rng = ok (core.result.Result.Ok v, s', rng')) :
    tacenta_braid.Braid.failed s.braid = ok false := by
  unfold lifecycle.Session.encrypt at h
  obtain ⟨fb, hfb, h⟩ := bind_eq_ok_inv h
  cases fb
  · exact hfb
  · simp at h

end Session

/-! ## `encrypt` keeps the invariant at an agreement state that takes no draw -/

section Encrypt

open Tacenta.UnitLifecycleEstablishedEncrypt (encrypt_ok_parts)

/-- **`Session::encrypt` keeps `Session::invariant` and spends one unit of the counter budget, at an agreement
state whose send takes no draw.**  For every session `s` that passes `Session::invariant`, has room for `k + 1`
operations (`CounterRoom`) and refines a model session `m` whose agreement send takes no draw
(`braidSendNeedsDraw m.braid = false`), and every successful return `(Ok bytes, s', rng')` of `encrypt` there whose
session refines the model's `encrypt` step from `m` (at any view, oracle and model plaintext): `s'` passes
`Session::invariant` and has room for `k` operations.  The only boundary record is `KemCloneAgrees` (the agreement's
key pair is cloned before the step).  The relation after the call is a hypothesis, which is what the encrypt
refinement supplies; nothing here calls that refinement, so this rests on the kernel and opaque constants only.

The Triple half goes through the model: `Triple::invariant` of the code Triple is `ModelTripleInv` of the model Triple
it refines (`triple_invariant_iff_model`), which the model's send without an agreement output keeps
(`modelTripleInv_send`).  The agreement half is the code walk (`braid_send_no_draw`).  The structural clauses read the
Triple only through its sending key, direction and sparse epoch, which the model's send keeps, and the agreement only
through what the walk keeps (`structural_congr`). -/
theorem encrypt_keeps_invariant_no_draw (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees) {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))
    (hrel : SessionRefines dh K s m)
    (hdraw : Model.Lifecycle.braidSendNeedsDraw m.braid = false)
    (pt : Slice U8) (ptM : Model.Lifecycle.Bytes) (rng : R)
    (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s pt rng = ok (core.result.Result.Ok bytes, s', rng'))
    (hrel' : SessionRefines dh K s' (Model.Lifecycle.encrypt view oracle m ptM).session) :
    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by
  obtain ⟨hstr, htri, hbr⟩ := (session_invariant_iff s).mp hinv
  -- the walk of the call
  obtain ⟨msg, ep, out, b, hsend, sparse, cand, hdr, mk, -, hs'⟩ := encrypt_ok_parts rc crc s pt rng bytes s' rng' hcall
  have hnf := encrypt_ok_not_failed rc crc s pt rng bytes s' rng' hcall
  have hstf : s.braid.state ≠ .Failed := by
    intro hst
    simp [tacenta_braid.Braid.failed, hst] at hnf
  -- the agreement half
  have hnd := sendsWithoutDraw_of_refines hrel.braid hdraw hstf
  obtain ⟨-, -, hbinv, hf, hi, he, ht, -⟩ := braid_send_no_draw hkcl rc crc s.braid hnd hbr rng msg ep out b rng' hsend
  -- the Triple half, through the model
  set m' := (Model.Lifecycle.encrypt view oracle m ptM).session with hm'
  have hmodel := (triple_invariant_iff_model hrel.triple).mp htri
  obtain ⟨htr, hbe⟩ := encrypt_session_cases view oracle m ptM hdraw
  have hmodel' : ModelTripleInv m'.triple := by
    rcases htr with htr | ⟨e, hd, key, hsd⟩
    · rw [htr]; exact hmodel
    · exact modelTripleInv_send hmodel hsd
  have htri' : tacenta_triple.State.invariant s'.triple = ok true :=
    (triple_invariant_iff_model hrel'.triple).mpr hmodel'
  -- the Triple's sending key, direction and sparse epoch, which the model's send keeps
  have hframe : m'.triple.classical.dhsPub = m.triple.classical.dhsPub ∧
      m'.triple.postQuantum.direction = m.triple.postQuantum.direction ∧
      m'.triple.postQuantum.epoch = m.triple.postQuantum.epoch := by
    rcases htr with htr | ⟨e, hd, key, hsd⟩
    · rw [htr]; exact ⟨rfl, rfl, rfl⟩
    · unfold Model.Triple.sendDetailed at hsd
      split at hsd
      · simp at hsd
      · rename_i c dr mkc hc
        split at hsd
        · simp at hsd
        · rename_i q pqN mkq hp
          simp only [Except.ok.injEq, Prod.mk.injEq] at hsd
          rw [← hsd.1]
          obtain ⟨-, -, hdhs, -, -, -, -⟩ := ratchet_send_frame hc
          obtain ⟨-, -, -, -, -, -, hep, hdir, -⟩ := spqr_send_frame hp
          exact ⟨hdhs, hdir, hep⟩
  obtain ⟨hc0, hq0⟩ := hrel.triple
  obtain ⟨hc1, hq1⟩ := hrel'.triple
  have hdhs : s'.triple.classical.dhs_pub = s.triple.classical.dhs_pub := by
    apply keyOf_injective
    have h1 := congrArg Model.State.State.dhsPub hc1
    have h0 := congrArg Model.State.State.dhsPub hc0
    simp only [Tacenta.SessionUnitTripleT3.ratchetAbs] at h1 h0
    rw [h1, h0, hframe.1]
  have hdir : s'.triple.post_quantum.direction = s.triple.post_quantum.direction := by
    have h1 := congrArg Model.SparseRatchet.State.direction hq1
    have h0 := congrArg Model.SparseRatchet.State.direction hq0
    simp only [Tacenta.SessionUnitTripleT3.spqrAbs] at h1 h0
    have h : Tacenta.SessionUnitSpqrT3.directionOf s'.triple.post_quantum.direction =
        Tacenta.SessionUnitSpqrT3.directionOf s.triple.post_quantum.direction := by
      rw [h1, h0, hframe.2.1]
    revert h
    cases s'.triple.post_quantum.direction <;> cases s.triple.post_quantum.direction <;>
      simp [Tacenta.SessionUnitSpqrT3.directionOf]
  have hep : s'.triple.post_quantum.epoch = s.triple.post_quantum.epoch := by
    have h1 := congrArg Model.SparseRatchet.State.epoch hq1
    have h0 := congrArg Model.SparseRatchet.State.epoch hq0
    simp only [Tacenta.SessionUnitTripleT3.spqrAbs] at h1 h0
    apply UScalar.eq_of_val_eq
    rw [h1, h0, hframe.2.2]
  -- the session's own clauses
  have hb' : s'.braid = b := by rw [hs']
  have hstr' : lifecycle.Session.structural_invariant s' = ok true := by
    have hs'' : s' = { s with triple := s'.triple, braid := b } := by
      rw [hs']
    rw [hs'', structural_congr s s'.triple b hdhs hdir hep hf hi he ht]
    exact hstr
  refine ⟨(session_invariant_iff s').mpr ⟨hstr', htri', hb' ▸ hbinv⟩, ?_⟩
  -- the budget
  exact (counterRoom_iff_model hrel' k).mpr
    (modelCounterRoom_encrypt view oracle m ptM hdraw k ((counterRoom_iff_model hrel (k + 1)).mp hroom))

end Encrypt

/-! ## On the run: the responder's reply keeps the invariant, and the initiator's first send keeps the Triple's -/

section Run

open Tacenta.UnitLifecycleT3 (KemView arrayOf vecOf sliceOf OracleOf DhCodecOf BraidSendRefinementContracts
  TripleSendRefinementContracts CodewordViewSendOf ZeroizingRoundTrips)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstReceiptSession receiverAfterFirst headerSource
  DhAgreeContributory AeadRoundTrip)
open Tacenta.UnitLifecycleResponderReply (replierAfterSend reply_model_step initiator_first_send_responder_replies)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid KemCiphertextLenOf establishedModelOf)
open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts responderModelOf)

/-- **The budget at the model session after the first receipt**: clock 1, sparse epoch 0, chain counters 0 and 1,
agreement epoch 1, so room for every `j` with `j + 2 < u32::MAX`.  Model only. -/
theorem modelCounterRoom_firstReceipt (mB : Model.Lifecycle.Session) (secret : Model.Lifecycle.Bytes)
    (rcv : Model.Braid.Chunk) (ec prk k1 k2 a4 d dSend newPub c : Model.State.Key) (j : Nat)
    (hj : j + 2 < Std.U32.max) :
    ModelCounterRoom (firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c) j := by
  have h32 : Std.U32.max = 4294967295 := by simp [Std.U32.max_eq]
  have h64 : Std.U64.max = 18446744073709551615 := by simp [Std.U64.max_eq]
  rw [h32] at hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [firstReceiptSession, receiverAfterFirst]; omega
  · simp only [firstReceiptSession, receiverAfterFirst]; omega
  · simp only [firstReceiptSession, receiverAfterFirst, List.mem_singleton]
    rintro q rfl ch (h | h) <;> (simp at h; subst h; simp only; omega)
  · simp only [firstReceiptSession, Model.Braid.BraidState.epoch]; omega

/-- **The responder's reply keeps `Session::invariant` and the four ceilings, on the run of the initiator's first
send.**  Under the hypotheses of `initiator_first_send_responder_replies` (no other), at every successful return of
`establish_responder` on the bytes the initiator's first `encrypt` emitted, for every reply plaintext `ptR` of at most
`Usize.max - 150` bytes and every source state `rngR`: `Session::encrypt` at `sB'` returns `Ok bytesR` and `sB''`
and leaves `rngR` as it was, `sB''` passes `Session::invariant`, meets the four ceilings (`CounterHeadroom`) and has
room for every `j` with `j + 3 < u32::MAX` further operations (`CounterRoom`), and refines the model session after
the receipt with the Triple `replierAfterSend`.  Derived on the run: `sB'`, its relation and its invariant are the
successor results' at the same call, the call and the relation after it are the reply's, and
`encrypt_keeps_invariant_no_draw` composes them at the agreement state `NoHeaderReceived`, whose send takes no draw.
Compiler-trusted through the nine `native_decide` constants of the encrypt and decrypt refinements. -/
theorem initiator_first_send_responder_reply_successor [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
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
    (ptR : Slice Std.U8) (hroomR : 102 + (ptR.val.length + 48) ≤ Usize.max) (rngR : F) :
    ∃ (p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes)) (ec : Array U8 32#usize)
      (dSend : Model.Lifecycle.Key) (dk ekSeed ekVector : Model.Braid.Bytes) (bytesR : alloc.vec.Vec Std.U8)
      (sB'' : lifecycle.Session),
      oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector) ∧
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      lifecycle.Session.invariant sB'' = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB'' ∧
      (∀ j, j + 3 < Std.U32.max → CounterRoom sB'' j) ∧
      SessionRefines dh oracleB.braidKem sB''
        { firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret)
            ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
            (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
            (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB with
          triple := replierAfterSend (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend)
            (arrayOf q.sparseReceive) (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) } := by
  -- the reply on the run: the call, the relation before it and the relation after it
  obtain ⟨p, ec, dSend, dk, ekSeed, ekVector, bytesR, sB'', hkg, -, -, -, hrel, hcallR, -, -, -, -, hrel''⟩ :=
    initiator_first_send_responder_replies rc crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec
      codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h q hq
      plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall rcB crcB contracts hpub hsym hcon haead hrt
      hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish hidentity hdistinct hkem rngB htraceB dB
      restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR rngR
  -- the invariant at the session establish_responder returned, on the same call
  have hinv := Tacenta.UnitLifecycleResponderSuccessor.initiator_first_send_responder_successor_admissible rc crc
    trace dh kem view oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct
    hbound rcE crcE ourA bundleA expected rng0 rng1 s h q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s'
    rng' hcall rcB crcB contracts hpub hsym hcon haead hrt hoeq traceB oracleB
    (DecryptOracleOf.of_oracleOf oracleOfB) agreements ourB storeB hpublish hidentity hdistinct hkem rngB htraceB dB
    restB hdrawB ptB sB' storeB' rngB' hcallB
  -- the relation after the call, read as the model's encrypt step
  have hpend : (responderModelOf dh p).pendingInitial = none := rfl
  have hrel' : SessionRefines dh oracleB.braidKem sB''
      (Model.Lifecycle.encrypt view oracleB
        (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret)
          ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
          (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
          (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) (sliceOf ptR)).session := by
    rw [reply_model_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpend]
    exact hrel''
  -- the budget at sB', from the relation
  have hroomB : ∀ j, j + 3 < Std.U32.max → CounterRoom sB' (j + 1) := fun j hj =>
    (counterRoom_iff_model hrel (j + 1)).mpr (modelCounterRoom_firstReceipt _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega))
  -- the general preservation, at NoHeaderReceived
  have key : ∀ j, j + 3 < Std.U32.max →
      lifecycle.Session.invariant sB'' = ok true ∧ CounterRoom sB'' j := fun j hj =>
    encrypt_keeps_invariant_no_draw braidB.kemClone rcB crcB dh oracleB.braidKem view oracleB sB' _ j hinv
      (hroomB j hj) hrel rfl ptR (sliceOf ptR) rngR bytesR sB'' rngR hcallR hrel'
  have h0 : (0 : Nat) + 3 < Std.U32.max := by simp [Std.U32.max_eq]
  exact ⟨p, ec, dSend, dk, ekSeed, ekVector, bytesR, sB'', hkg, hcallR, (key 0 h0).1,
    (counterRoom_zero sB'').mp (key 0 h0).2, fun j hj => (key j hj).2, hrel''⟩

/-- **`Session::invariant` and the four ceilings at the session the responder's reply leaves**: the invariant and
ceiling conjuncts of `initiator_first_send_responder_reply_successor`, at every successful return of the reply's
`encrypt` at `sB'`, under its hypotheses.  Compiler-trusted as that theorem is. -/
theorem initiator_first_send_responder_reply_admissible [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
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
    (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session) (rngR' : F)
    (hcallR : lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR')) :
    lifecycle.Session.invariant sB'' = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB'' := by
  obtain ⟨-, -, -, -, -, -, bytes2, s2, -, hcall2, hinv2, hhead2, -, -⟩ :=
    initiator_first_send_responder_reply_successor rc crc trace dh kem view oracle braid triple aead dhCodec oracleOf
      codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h q hq
      plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall rcB crcB contracts hpub hsym hcon haead hrt
      hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish hidentity hdistinct hkem rngB htraceB dB
      restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR rngR
  rw [hcallR] at hcall2
  simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hcall2
  obtain ⟨-, rfl, -⟩ := hcall2
  exact ⟨hinv2, hhead2⟩

open Tacenta.UnitLifecycleEstablishedEncrypt (KeyGenSeededFor established_encrypt_outcomes) in
open Tacenta.UnitLifecycleRestoredSession (KemCiphertextLenBound) in
/-- **The Triple leaf of the initiator's session after its first send, derived by preservation**: under the
hypotheses of `established_encrypt_outcomes` and the establishment's laws `DhPublicValid` and `OptionEqU64Shape`, at
every successful return of the first `encrypt` at the session `establish_initiator_for` returned, the Triple passes
`Triple::invariant`.  The same leaf `established_encrypt_successor_admissible` gets by fixing the Triple's shape;
here it comes from the establishment's invariant through the bridge and the model's send (`modelTripleInv_send`),
with no shape.  The agreement's send there draws (`KeysUnsampled`), so the session-level preservation above does not
apply; only the Triple leaf is re-derived.  Compiler-trusted through the nine `native_decide` constants of the encrypt
refinement. -/
theorem established_encrypt_triple_invariant_via_preservation [Tacenta.SessionUnitT1.DerivedKeysModel]
    {R E : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem) (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : KeyGenSeededFor oracle.braidKem rc crc trace) (hct : KemCiphertextLenOf)
    (hbound : KemCiphertextLenBound)
    (hpub : DhPublicValid)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws) (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key)
    (hdraws : trace rng = d1 :: d2 :: rest)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng =
      ok (core.result.Result.Ok bytes, s', rng')) :
    tacenta_triple.State.invariant s'.triple = ok true := by
  obtain ⟨output, hcall', -, hcases⟩ := established_encrypt_outcomes rc crc trace dh kem view oracle
    braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct hbound rcE crcE our
    bundle expected rng0 rng1 s h plaintext hroom rng htrace d1 d2 rest hdraws
  rw [hcall] at hcall'
  cases hcall'
  rcases hcases with ⟨-, hres, -⟩ | ⟨dk, ekSeed, ekVector, hkg, bytes', hres, hframe, hst, tripleNext, messageKey,
      chunk, encoder, pending, a, ⟨header, htriple⟩, hbraidM, hnc, hpend, hwire, hrel⟩
  · cases hres
  -- the establishment's invariant, read on the model through the bridge
  have hinv := Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_admissible rcE crcE hpub hct
    hoeq our bundle expected rng0 rng1 s h
  have hrel0 := Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_established rcE crcE dh
    oracle.braidKem our bundle expected rng0 rng1 s h
  have hm := (triple_invariant_iff_model hrel0.triple).mp ((session_invariant_iff s).mp hinv).2.1
  -- the model's send keeps it, and the bridge carries it back to the Triple after the call
  exact (triple_invariant_iff_model hrel.triple).mpr (modelTripleInv_send hm htriple)

end Run

end Tacenta.UnitLifecycleSendPreserve

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleSendPreserve.ratchet_send_frame' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.ratchet_send_frame

/--
info: 'Tacenta.UnitLifecycleSendPreserve.modelRatchetInv_send' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.modelRatchetInv_send

/--
info: 'Tacenta.UnitLifecycleSendPreserve.findChains_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.findChains_mem

/--
info: 'Tacenta.UnitLifecycleSendPreserve.spqr_send_frame' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.spqr_send_frame

/--
info: 'Tacenta.UnitLifecycleSendPreserve.mem_sent_chains' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.mem_sent_chains

/--
info: 'Tacenta.UnitLifecycleSendPreserve.modelSpqrInv_send' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.modelSpqrInv_send

/--
info: 'Tacenta.UnitLifecycleSendPreserve.modelTripleInv_send' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.modelTripleInv_send

/--
info: 'Tacenta.UnitLifecycleSendPreserve.braid_send_no_draw_model' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.braid_send_no_draw_model

/--
info: 'Tacenta.UnitLifecycleSendPreserve.encrypt_session_cases' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.encrypt_session_cases

/--
info: 'Tacenta.UnitLifecycleSendPreserve.counterRoom_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.counterRoom_zero

/--
info: 'Tacenta.UnitLifecycleSendPreserve.epoch_val_refines' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleSendPreserve.epoch_val_refines

/--
info: 'Tacenta.UnitLifecycleSendPreserve.counterRoom_iff_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.counterRoom_iff_model

/--
info: 'Tacenta.UnitLifecycleSendPreserve.modelCounterRoom_encrypt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.modelCounterRoom_encrypt

/--
info: 'Tacenta.UnitLifecycleSendPreserve.sendsWithoutDraw_of_refines' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleSendPreserve.sendsWithoutDraw_of_refines

/--
info: 'Tacenta.UnitLifecycleSendPreserve.vec_clone_u8' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.vec_clone_u8

/--
info: 'Tacenta.UnitLifecycleSendPreserve.encoder_clone_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.encoder_clone_eq

/--
info: 'Tacenta.UnitLifecycleSendPreserve.decoder_clone_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.decoder_clone_eq

/--
info: 'Tacenta.UnitLifecycleSendPreserve.next_chunk_keeps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.next_chunk_keeps

/--
info: 'Tacenta.UnitLifecycleSendPreserve.encoder_sized_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.encoder_sized_congr

/--
info: 'Tacenta.UnitLifecycleSendPreserve.key_pair_valid_clone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.key_pair_valid_clone

/--
info: 'Tacenta.UnitLifecycleSendPreserve.braid_send_no_draw' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleSendPreserve.braid_send_no_draw

/--
info: 'Tacenta.UnitLifecycleSendPreserve.session_invariant_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.validate_ek,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 core.num.Usize.div_ceil,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.session_invariant_iff

/--
info: 'Tacenta.UnitLifecycleSendPreserve.structural_congr' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleSendPreserve.structural_congr

/--
info: 'Tacenta.UnitLifecycleSendPreserve.encrypt_ok_not_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
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
#print axioms Tacenta.UnitLifecycleSendPreserve.encrypt_ok_not_failed

/--
info: 'Tacenta.UnitLifecycleSendPreserve.encrypt_keeps_invariant_no_draw' depends on axioms: [propext,
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
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
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
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.encrypt_keeps_invariant_no_draw

/--
info: 'Tacenta.UnitLifecycleSendPreserve.modelCounterRoom_firstReceipt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSendPreserve.modelCounterRoom_firstReceipt

/--
info: 'Tacenta.UnitLifecycleSendPreserve.initiator_first_send_responder_reply_successor' depends on axioms: [propext,
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
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
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
#print axioms Tacenta.UnitLifecycleSendPreserve.initiator_first_send_responder_reply_successor

/--
info: 'Tacenta.UnitLifecycleSendPreserve.initiator_first_send_responder_reply_admissible' depends on axioms: [propext,
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
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
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
#print axioms Tacenta.UnitLifecycleSendPreserve.initiator_first_send_responder_reply_admissible

/--
info: 'Tacenta.UnitLifecycleSendPreserve.established_encrypt_triple_invariant_via_preservation' depends on axioms: [propext,
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
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
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
#print axioms Tacenta.UnitLifecycleSendPreserve.established_encrypt_triple_invariant_via_preservation

/--
info: @Tacenta.UnitLifecycleSendPreserve.ratchet_send_frame : ∀ {st st' : Model.State.State} {hd : Model.State.Header}
  {key : Model.State.Key},
  Model.Ratchet.sendDetailed st = Except.ok (st', hd, key) →
    st.cks.isSome = true ∧
      st'.cks.isSome = true ∧
        st'.dhsPub = st.dhsPub ∧
          st'.dhrPub = st.dhrPub ∧ st'.ckr = st.ckr ∧ st'.events = st.events ∧ st'.skipped = st.skipped
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.ratchet_send_frame

/--
info: @Tacenta.UnitLifecycleSendPreserve.modelRatchetInv_send : ∀ {st st' : Model.State.State} {hd : Model.State.Header}
  {key : Model.State.Key},
  Tacenta.UnitTripleInvModel.ModelRatchetInv st →
    Model.Ratchet.sendDetailed st = Except.ok (st', hd, key) → Tacenta.UnitTripleInvModel.ModelRatchetInv st'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.modelRatchetInv_send

/--
info: @Tacenta.UnitLifecycleSendPreserve.findChains_mem : ∀ {st : Model.SparseRatchet.State} {e : ℕ}
  {cs : Model.SparseRatchet.Chains}, Model.SparseRatchet.findChains st e = some cs → (e, cs) ∈ st.chains
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.findChains_mem

/--
info: @Tacenta.UnitLifecycleSendPreserve.spqr_send_frame : ∀ {st st' : Model.SparseRatchet.State} {e n : ℕ}
  {key : Model.State.Key},
  Model.SparseRatchet.sendDetailed st e none = Except.ok (st', n, key) →
    ∃ cs,
      (e, cs) ∈ st.chains ∧
        ∃ c',
          st'.chains = List.filter (fun p => !p.1 == e) st.chains ++ [(e, c')] ∧
            c'.receive = cs.receive ∧
              (∀ (ch : Model.SparseRatchet.Chain), c'.send = some ch → ∃ ch0, cs.send = some ch0 ∧ ch.n = ch0.n + 1) ∧
                st'.epoch = st.epoch ∧ st'.direction = st.direction ∧ st'.skipped = st.skipped
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.spqr_send_frame

/--
info: @Tacenta.UnitLifecycleSendPreserve.mem_sent_chains : ∀ {L : List (ℕ × Model.SparseRatchet.Chains)} {e : ℕ}
  {c' : Model.SparseRatchet.Chains} {p : ℕ × Model.SparseRatchet.Chains},
  p ∈ List.filter (fun p => !p.1 == e) L ++ [(e, c')] → p ∈ L ∧ p.1 ≠ e ∨ p = (e, c')
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.mem_sent_chains

/--
info: @Tacenta.UnitLifecycleSendPreserve.modelSpqrInv_send : ∀ {st st' : Model.SparseRatchet.State} {e n : ℕ}
  {key : Model.State.Key},
  Tacenta.UnitTripleInvModel.ModelSpqrInv st →
    Model.SparseRatchet.sendDetailed st e none = Except.ok (st', n, key) → Tacenta.UnitTripleInvModel.ModelSpqrInv st'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.modelSpqrInv_send

/--
info: @Tacenta.UnitLifecycleSendPreserve.modelTripleInv_send : ∀ {m m' : Model.Triple.State} {e : ℕ}
  {hd : Model.Triple.Header} {key : Model.State.Key},
  Tacenta.UnitTripleInvModel.ModelTripleInv m →
    Model.Triple.sendDetailed m e none = Except.ok (m', hd, key) → Tacenta.UnitTripleInvModel.ModelTripleInv m'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.modelTripleInv_send

/--
info: Tacenta.UnitLifecycleSendPreserve.braid_send_no_draw_model : ∀ (K : Model.Braid.Kem) (st : Model.Braid.BraidState),
  Model.Lifecycle.braidSendNeedsDraw st = false →
    (Model.Braid.send K 0 st).2.2.1 = none ∧ (Model.Braid.send K 0 st).2.2.2.epoch = st.epoch
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.braid_send_no_draw_model

/--
info: Tacenta.UnitLifecycleSendPreserve.encrypt_session_cases : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (m : Model.Lifecycle.Session) (pt : Model.Lifecycle.Bytes),
  Model.Lifecycle.braidSendNeedsDraw m.braid = false →
    ((Model.Lifecycle.encrypt view oracle m pt).session.triple = m.triple ∨
        ∃ e hd key,
          Model.Triple.sendDetailed m.triple e none =
            Except.ok ((Model.Lifecycle.encrypt view oracle m pt).session.triple, hd, key)) ∧
      (Model.Lifecycle.encrypt view oracle m pt).session.braid.epoch = m.braid.epoch
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.encrypt_session_cases

/--
info: Tacenta.UnitLifecycleSendPreserve.counterRoom_zero : ∀ (s : lifecycle.Session),
  Tacenta.UnitLifecycleSendPreserve.CounterRoom s 0 ↔ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.counterRoom_zero

/--
info: @Tacenta.UnitLifecycleSendPreserve.epoch_val_refines : ∀ {K : Model.Braid.Kem} {st : tacenta_braid.State}
  {m : Model.Braid.BraidState},
  Tacenta.SessionUnitBraidT3.StateRefines K st m → ↑(Tacenta.SessionUnitBraidT1.State.epoch_val st) = m.epoch
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.epoch_val_refines

/--
info: @Tacenta.UnitLifecycleSendPreserve.counterRoom_iff_model : ∀ {dh : Tacenta.UnitLifecycleT3.DhView} {K : Model.Braid.Kem}
  {s : lifecycle.Session} {m : Model.Lifecycle.Session},
  Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
    ∀ (k : ℕ),
      Tacenta.UnitLifecycleSendPreserve.CounterRoom s k ↔ Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom m k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.counterRoom_iff_model

/--
info: Tacenta.UnitLifecycleSendPreserve.modelCounterRoom_encrypt : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (m : Model.Lifecycle.Session) (pt : Model.Lifecycle.Bytes),
  Model.Lifecycle.braidSendNeedsDraw m.braid = false →
    ∀ (k : ℕ),
      Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom m (k + 1) →
        Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom (Model.Lifecycle.encrypt view oracle m pt).session k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.modelCounterRoom_encrypt

/--
info: @Tacenta.UnitLifecycleSendPreserve.sendsWithoutDraw_of_refines : ∀ {K : Model.Braid.Kem} {st : tacenta_braid.State}
  {m : Model.Braid.BraidState},
  Tacenta.SessionUnitBraidT3.StateRefines K st m →
    Model.Lifecycle.braidSendNeedsDraw m = false →
      st ≠ tacenta_braid.State.Failed → Tacenta.UnitLifecycleSendPreserve.SendsWithoutDraw st
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.sendsWithoutDraw_of_refines

/--
info: Tacenta.UnitLifecycleSendPreserve.vec_clone_u8 : ∀ (v : alloc.vec.Vec U8),
  alloc.vec.CloneVec.clone core.clone.CloneU8 v = ok v
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.vec_clone_u8

/--
info: Tacenta.UnitLifecycleSendPreserve.encoder_clone_eq : ∀ (e : tacenta_erasure.Encoder),
  tacenta_erasure.Encoder.Insts.CoreCloneClone.clone e = ok e
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.encoder_clone_eq

/--
info: Tacenta.UnitLifecycleSendPreserve.decoder_clone_eq : ∀ (d : tacenta_erasure.Decoder),
  tacenta_erasure.Decoder.Insts.CoreCloneClone.clone d = ok d
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.decoder_clone_eq

/--
info: @Tacenta.UnitLifecycleSendPreserve.next_chunk_keeps : ∀ {enc enc' : tacenta_erasure.Encoder}
  {c : Option tacenta_erasure.Chunk},
  enc.next_chunk = ok (c, enc') → enc'.chunks = enc.chunks ∧ enc'.invariant = enc.invariant
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.next_chunk_keeps

/--
info: @Tacenta.UnitLifecycleSendPreserve.encoder_sized_congr : ∀ {enc enc' : tacenta_erasure.Encoder},
  enc'.chunks = enc.chunks → tacenta_braid.encoder_sized enc' = tacenta_braid.encoder_sized enc
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.encoder_sized_congr

/--
info: Tacenta.UnitLifecycleSendPreserve.key_pair_valid_clone : Tacenta.SessionUnitBraidT3.KemCloneAgrees →
  ∀ {kp kp' : tacenta_kem.IncrementalKeyPair},
    tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp = ok kp' →
      tacenta_braid.key_pair_valid kp = ok true → tacenta_braid.key_pair_valid kp' = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.key_pair_valid_clone

/--
info: Tacenta.UnitLifecycleSendPreserve.braid_send_no_draw : Tacenta.SessionUnitBraidT3.KemCloneAgrees →
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (b : tacenta_braid.Braid),
    Tacenta.UnitLifecycleSendPreserve.SendsWithoutDraw b.state →
      b.invariant = ok true →
        ∀ (rng : R) (msg : tacenta_braid.Msg) (ep : U64) (out : Option tacenta_braid.Output) (b' : tacenta_braid.Braid)
          (rng' : R),
          tacenta_braid.Braid.send rc crc b rng = ok ((msg, ep, out, b'), rng') →
            rng' = rng ∧
              out = none ∧
                b'.invariant = ok true ∧
                  b'.failed = b.failed ∧
                    b'.is_initiator = b.is_initiator ∧
                      b'.epoch = b.epoch ∧
                        b'.state_tag = b.state_tag ∧
                          Tacenta.SessionUnitBraidT1.State.epoch_val b'.state =
                            Tacenta.SessionUnitBraidT1.State.epoch_val b.state
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.braid_send_no_draw

/--
info: Tacenta.UnitLifecycleSendPreserve.session_invariant_iff : ∀ (s : lifecycle.Session),
  s.invariant = ok true ↔ s.structural_invariant = ok true ∧ s.triple.invariant = ok true ∧ s.braid.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.session_invariant_iff

/--
info: Tacenta.UnitLifecycleSendPreserve.structural_congr : ∀ (s : lifecycle.Session) (t : tacenta_triple.State)
  (b : tacenta_braid.Braid),
  t.classical.dhs_pub = s.triple.classical.dhs_pub →
    t.post_quantum.direction = s.triple.post_quantum.direction →
      t.post_quantum.epoch = s.triple.post_quantum.epoch →
        b.failed = s.braid.failed →
          b.is_initiator = s.braid.is_initiator →
            b.epoch = s.braid.epoch →
              b.state_tag = s.braid.state_tag →
                { triple := t, braid := b, ratchet_private := s.ratchet_private, identity_ad := s.identity_ad,
                      our_identity_public := s.our_identity_public, peer_identity_public := s.peer_identity_public,
                      pending_initial := s.pending_initial,
                      established_ephemeral := s.established_ephemeral }.structural_invariant =
                  s.structural_invariant
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.structural_congr

/--
info: @Tacenta.UnitLifecycleSendPreserve.encrypt_ok_not_failed : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (pt : Slice U8) (rng : R) (v : alloc.vec.Vec U8)
  (s' : lifecycle.Session) (rng' : R),
  lifecycle.Session.encrypt rc crc s pt rng = ok (core.result.Result.Ok v, s', rng') → s.braid.failed = ok false
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.encrypt_ok_not_failed

/--
info: Tacenta.UnitLifecycleSendPreserve.encrypt_keeps_invariant_no_draw : Tacenta.SessionUnitBraidT3.KemCloneAgrees →
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (dh : Tacenta.UnitLifecycleT3.DhView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : ℕ),
    s.invariant = ok true →
      Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
        Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
          Model.Lifecycle.braidSendNeedsDraw m.braid = false →
            ∀ (pt : Slice U8) (ptM : Model.Lifecycle.Bytes) (rng : R) (bytes : alloc.vec.Vec U8)
              (s' : lifecycle.Session) (rng' : R),
              lifecycle.Session.encrypt rc crc s pt rng = ok (core.result.Result.Ok bytes, s', rng') →
                Tacenta.UnitLifecycleT3.SessionRefines dh K s' (Model.Lifecycle.encrypt view oracle m ptM).session →
                  s'.invariant = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.encrypt_keeps_invariant_no_draw

/--
info: Tacenta.UnitLifecycleSendPreserve.modelCounterRoom_firstReceipt : ∀ (mB : Model.Lifecycle.Session)
  (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk) (ec prk k1 k2 a4 d dSend newPub c : Model.State.Key)
  (j : ℕ),
  j + 2 < U32.max →
    Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom
      (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c) j
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.modelCounterRoom_firstReceipt

/--
info: @Tacenta.UnitLifecycleSendPreserve.initiator_first_send_responder_reply_successor : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
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
                                                      ∀ (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
                                                        (contracts :
                                                          Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
                                                        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                                                          Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                                                            Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                                                              Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                                                                ⋯
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.initiator_first_send_responder_reply_successor

/--
info: @Tacenta.UnitLifecycleSendPreserve.initiator_first_send_responder_reply_admissible : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
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
                                                      ∀ (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
                                                        (contracts :
                                                          Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
                                                        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                                                          Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                                                            Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                                                              Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                                                                ⋯
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.initiator_first_send_responder_reply_admissible

/--
info: @Tacenta.UnitLifecycleSendPreserve.established_encrypt_triple_invariant_via_preservation : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
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
                        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                            Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                              Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                                  @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                                ∀ (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
                                  (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
                                  (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                                  (s : lifecycle.Session),
                                  lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
                                      ok (core.result.Result.Ok s, rng1) →
                                    ∀ (plaintext : Slice U8),
                                      (↑plaintext).length + 65770 ≤ Usize.max →
                                        ∀ (rng : R),
                                          trace rng = oracle.draws →
                                            ∀ (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
                                              trace rng = d1 :: d2 :: rest →
                                                ∀ (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                                                  lifecycle.Session.encrypt rc crc s plaintext rng =
                                                      ok (core.result.Result.Ok bytes, s', rng') →
                                                    s'.triple.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSendPreserve.established_encrypt_triple_invariant_via_preservation

/--
info: structure Tacenta.UnitLifecycleSendPreserve.CounterRoom (s : lifecycle.Session) (k : ℕ) : Prop
number of parameters: 2
fields:
  Tacenta.UnitLifecycleSendPreserve.CounterRoom.classicalEvents : ↑s.triple.classical.events + k + 1 < U32.max
  Tacenta.UnitLifecycleSendPreserve.CounterRoom.sparseEpoch : ↑s.triple.post_quantum.epoch + k + 1 < U64.max
  Tacenta.UnitLifecycleSendPreserve.CounterRoom.sparseCounters : ∀ p ∈ ↑s.triple.post_quantum.chains,
      ∀ (ch : tacenta_spqr.Chain), p.2.send = some ch ∨ p.2.receive = some ch → ↑ch.n + 1001 * k < U64.max
  Tacenta.UnitLifecycleSendPreserve.CounterRoom.braidEpoch : ↑(Tacenta.SessionUnitBraidT1.State.epoch_val
              s.braid.state) +
          k +
        1 <
      U64.max
constructor:
  Tacenta.UnitLifecycleSendPreserve.CounterRoom.mk {s : lifecycle.Session} {k : ℕ}
    (classicalEvents : ↑s.triple.classical.events + k + 1 < U32.max)
    (sparseEpoch : ↑s.triple.post_quantum.epoch + k + 1 < U64.max)
    (sparseCounters :
      ∀ p ∈ ↑s.triple.post_quantum.chains,
        ∀ (ch : tacenta_spqr.Chain), p.2.send = some ch ∨ p.2.receive = some ch → ↑ch.n + 1001 * k < U64.max)
    (braidEpoch : ↑(Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state) + k + 1 < U64.max) :
    Tacenta.UnitLifecycleSendPreserve.CounterRoom s k
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSendPreserve.CounterRoom

/--
info: structure Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom (m : Model.Lifecycle.Session) (k : ℕ) : Prop
number of parameters: 2
fields:
  Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom.classicalEvents : m.triple.classical.events + k + 1 < U32.max
  Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom.sparseEpoch : m.triple.postQuantum.epoch + k + 1 < U64.max
  Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom.sparseCounters : ∀ p ∈ m.triple.postQuantum.chains,
      ∀ (ch : Model.SparseRatchet.Chain), p.2.send = some ch ∨ p.2.receive = some ch → ch.n + 1001 * k < U64.max
  Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom.braidEpoch : m.braid.epoch + k + 1 < U64.max
constructor:
  Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom.mk {m : Model.Lifecycle.Session} {k : ℕ}
    (classicalEvents : m.triple.classical.events + k + 1 < U32.max)
    (sparseEpoch : m.triple.postQuantum.epoch + k + 1 < U64.max)
    (sparseCounters :
      ∀ p ∈ m.triple.postQuantum.chains,
        ∀ (ch : Model.SparseRatchet.Chain), p.2.send = some ch ∨ p.2.receive = some ch → ch.n + 1001 * k < U64.max)
    (braidEpoch : m.braid.epoch + k + 1 < U64.max) : Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom m k
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom

/--
info: def Tacenta.UnitLifecycleSendPreserve.SendsWithoutDraw : tacenta_braid.State → Prop :=
fun x =>
  match x with
  | tacenta_braid.State.KeysUnsampled a a_1 => False
  | tacenta_braid.State.HeaderReceived a a_1 a_2 a_3 => False
  | tacenta_braid.State.Failed => False
  | x => True
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSendPreserve.SendsWithoutDraw
