import Translation.UnitLifecycleSendPreserve
import Translation.UnitLifecycleReceivePreserve
import Translation.UnitHeldKemWitness

/-!
# `Session::encrypt` keeps `Session::invariant` at every agreement state, and a refused call keeps it

`UnitLifecycleSendPreserve` shows the step for the nine agreement states whose send takes no draw.  This module adds
the two that draw, key generation at `KeysUnsampled` and the first half of encapsulation at `HeaderReceived` (whose
send carries the agreement's output, so the Triple's sparse ratchet advances), puts the three together into one step
at every agreement state, derives the relation after the call from the general encrypt refinement, and shows that
every refused `encrypt`, `decrypt` and `decrypt_ratchet` keeps the invariant and the whole budget.

## What it shows

* `encrypt_err_keeps_invariant`, `decrypt_err_keeps_invariant`, `decrypt_ratchet_err_keeps_invariant`: every refused
  call keeps `Session::invariant` and every budget `CounterRoom s k`.  `decrypt` and `decrypt_ratchet` return the
  session they were given; `encrypt` returns it, or returns it with its agreement committed `Failed`
  (`encrypt_err_leaves_state`), which passes the invariant (`structural_failed`, `failed_invariant`) and counts its
  epoch as zero (`counterRoom_failed`).  No hypothesis about any opaque operation.  The size refusals are named
  instances (`encrypt_size_refusal_keeps_invariant`, `decrypt_size_refusal_keeps_invariant`).
* The model: `advance` keeps `ModelSpqrInv` (`modelSpqrInv_advance`); the Triple's send keeps `ModelTripleInv` with
  or without an agreement output (`modelTripleInv_send_any`); the model's `encrypt` leaves the session, the session
  with its agreement failed, or a successful Triple send at the agreement send's epoch and output
  (`encrypt_model_outcomes`); and it spends at most one unit of the budget at every agreement state
  (`modelCounterRoom_encrypt_any`).  Model only.
* The translated agreement send at the two states that draw keeps `Braid::invariant` or commits `Failed`:
  `braid_send_keysUnsampled` (the key pair passes `key_pair_valid`, the header encoder is a fresh encoder after one
  chunk, `fresh_encoder_step`) and `braid_send_headerReceived` (`ct1` has `CT1_LEN` bytes, the `ct1` encoder is
  fresh after one chunk, the header and the `ek_vector` decoder are carried, and the output is for the state's
  epoch).
* `encrypt_keeps_invariant_keysUnsampled`, `encrypt_keeps_invariant_headerReceived`, `encrypt_keeps_invariant`:
  **for every session that passes `Session::invariant`, has room for `k + 1` operations and refines a model session,
  every successful `encrypt` whose session refines the model's `encrypt` step leaves a session that passes
  `Session::invariant` and has room for `k`, at every agreement state and every epoch.**  At `HeaderReceived`
  clause (b) moves from tag 6 (sparse epoch one behind) to tag 7 (sparse epoch equal), shown through the model:
  the model's Triple send there carries the output and advances to the agreement's epoch (`structural_folded`).
  `encrypt_keeps_invariant_unless_sampling`: the same at every state but `HeaderReceived`, without `Encaps1SizesOf`.
* `encrypt_keeps_invariant_of_witness`, `encrypt_keeps_invariant_of_contracts`: every outcome of `encrypt` (success
  and refusal) keeps the invariant and the budget, with the relation after the call taken from the encrypt
  refinement's conclusion, and composed with the general encrypt refinement `public_session_encrypt_of_send_contracts`
  under exactly its hypotheses and the laws above.
* `established_encrypt_invariant_via_general`, `established_encrypt_via_general_reachable`: the established
  initiator's first send re-derived through the general step, with no shape of the session after it, and every
  premise of that use holding together at the real constants under the laws of the existing reach.

## The laws and premises

* **New, assumed: `Encaps1SizesOf K`.**  Every `ct1` the KEM model's `encaps1` returns has `K.ct1Size` bytes: the
  twin of `KeyGenSizesOf` for encapsulation.  A statement about the model KEM.  Used only at `HeaderReceived`
  (`encrypt_keeps_invariant_unless_sampling` does without it).  It has a toy model (`encaps1Sizes_toyKemR`), which
  shows the statement consistent and nothing about the shipping KEM.  It is not derived at the KEM model read off the
  wrapper (`UnitKemWrapperModel`): no wrapper law states the length of `encapsulate1`'s `ct1`.  Of the shipping
  wrapper it holds by reading (the wrapper copies libcrux's fixed-size first ciphertext half; the crate's test
  `the_sizes_are_the_specifications_sizes` checks one call), which is not a proof.
* Existing records and laws: `KemCloneAgrees`; `KemAgreesFor K`, its key-generation and encapsulation clauses, whose
  model randomness is existential (the seeded encapsulation law `Encapsulate1SeededFor` is **not** used: the invariant
  does not depend on which randomness was drawn); `RngTotal`; `Ct1LenTotal`; and the four of `SendInvariantLaws`:
  `KemLenAgrees`, `KeyGenSizesOf`, `ValidateEkAgrees`, `DivCeilValue`.
* The relation after the call is a hypothesis of the step theorems.  `encrypt_keeps_invariant_of_contracts` derives
  it from the encrypt refinement, whose hypotheses it takes unchanged; among them the per-call records `braidTrace`
  (`BraidSendTraceAgreementCounted`: what the agreement send at this call returns at the run's draws) and
  `providers` (`EncryptNonterminalRouteProviders`: what the model's Triple does at the generated call) state what one
  call returns.  They are intermediate hypotheses, not discharged here; at a `HeaderReceived` session no theorem in
  the tree supplies `braidTrace` (it would need a seeded encapsulation law).
* `CounterRoom` is the budget of `UnitLifecycleSendPreserve`; the step spends it because the code refuses one step
  later than `CounterHeadroom` asks.  No premise names a platform width.

## Non-vacuity

* The refusal results assume nothing about any opaque operation; that a refusal is reached is shown only for the
  terminal refusal at every failed session (`UnitLifecycleAtomicity`) and the size refusals (`UnitLifecycleSizeRule`).
* The step at `KeysUnsampled`: every premise holds together on the established initiator's first send at the real
  constants, under the laws of `established_encrypt_successor_reachable`, which a toy model holds together
  (`established_encrypt_via_general_reachable`).
* The step at `HeaderReceived`: no run in the tree reaches that state, so its premises are not exhibited together;
  `Encaps1SizesOf` has a toy model only.  The nine no-draw states are as `UnitLifecycleSendPreserve` says (exhibited
  at `NoHeaderReceived` only).
* `encrypt_keeps_invariant_of_contracts` adds no reach: its premises are the encrypt refinement's, the four laws of
  `SendInvariantLaws`, `Encaps1SizesOf`, the invariant and the budget.

## What it does not show

* A `decrypt` or `decrypt_ratchet` that succeeds and keeps the invariant beyond the in-order scope of
  `UnitLifecycleReceivePreserve`: a receive with an agreement transition or output, a stored key, a skip or an
  eviction is not covered here.
* The step at `HeaderReceived` on any run, or with the relation after the call derived there: the encrypt
  refinement's per-call record `braidTrace` has no supplier at that state.
* That the shipping KEM meets `Encaps1SizesOf`, `KemAgreesFor`, `KemLenAgrees`, `KeyGenSizesOf`, `ValidateEkAgrees`
  or `KemCloneAgrees`, or that `usize::div_ceil` meets `DivCeilValue`.
* Whether `encapsulate1` can refuse an authenticated 64-byte header in the shipping code (not determined); the refusal
  arm is covered, not shown reachable.
* That the ceilings are kept: false of the code, so the statements spend a budget; that a session's budget is
  positive at any session other than the established and model sessions named in the earlier modules.
* The budget at a session `Session::import` returns: `Session::invariant` does not give it.
* The out-of-order family, restored sessions beyond `RestoredScope`, a second party, and the conversation.
* That `Session::invariant` says a session is reachable: it is a predicate on fields.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv)

namespace Tacenta.UnitLifecycleEncryptPreserve

open Tacenta.UnitTripleInvModel
open Tacenta.UnitLifecycleSendPreserve
open Tacenta.UnitLifecycleReceivePreserve (mono_bind mono_ite strip_bind strip_ite)
open Tacenta.UnitLifecycleT3 (DhView SessionRefines)
open Tacenta.SessionUnitBraidT3 (KemAgreesFor KemLenAgrees ValidateEkAgrees vecOf sliceOf)
open Tacenta.UnitLifecycleEstablishedEncrypt (KeyGenSizesOf keyPairValid_of_header)

/-! ## A refused call keeps the invariant and the whole budget -/

section Refusal

theorem failed_iff (b : tacenta_braid.Braid) :
    tacenta_braid.Braid.failed b = ok true ↔ b.state = .Failed := by
  obtain ⟨st⟩ := b
  cases st <;> simp [tacenta_braid.Braid.failed]

theorem failed_invariant (b : tacenta_braid.Braid) (h : tacenta_braid.Braid.failed b = ok true) :
    tacenta_braid.Braid.invariant b = ok true := by
  obtain ⟨st⟩ := b
  rw [failed_iff] at h
  simp only at h
  subst h
  rfl

theorem strip_ite_else {c : Prop} [Decidable c] {b y : Result Bool} (h : b = ok true → y = ok true) :
    (if c then b else ok false) = ok true → y = ok true := by
  split_ifs <;> simp_all

set_option maxHeartbeats 1000000 in
theorem structural_failed (s : lifecycle.Session) (b : tacenta_braid.Braid)
    (hb : tacenta_braid.Braid.failed b = ok true)
    (h : lifecycle.Session.structural_invariant s = ok true) :
    lifecycle.Session.structural_invariant { s with braid := b } = ok true := by
  obtain ⟨st⟩ := b
  rw [failed_iff] at hb
  simp only at hb
  subst hb
  revert h
  unfold lifecycle.Session.structural_invariant lifecycle.Session.is_responder
  rcases hsb : s.braid with ⟨st0⟩
  cases st0 <;>
  simp only [tacenta_braid.Braid.failed, tacenta_braid.Braid.is_initiator, Bool.false_eq_true, if_false,
    if_true, bind_tc_ok] <;>
  repeat' first
    | (with_reducible exact id)
    | (intro h; simp at h; done)
    | (apply mono_bind; intro _)
    | apply mono_ite
    | (apply strip_bind; intro _)
    | (apply strip_ite_else)
    | (apply strip_ite)
    | split


set_option maxHeartbeats 1000000 in
/-- Into a folded state: the structural clauses hold after a step into an agreement state of tag 7 to 10 whose
epoch is the sparse epoch, when they held before at a state that had not failed. -/
theorem structural_folded (s : lifecycle.Session) (t : tacenta_triple.State) (b : tacenta_braid.Braid) (x : U8)
    (h : lifecycle.Session.structural_invariant s = ok true)
    (hdhs : t.classical.dhs_pub = s.triple.classical.dhs_pub)
    (hdir : t.post_quantum.direction = s.triple.post_quantum.direction)
    (hfs : tacenta_braid.Braid.failed s.braid = ok false) (hfb : tacenta_braid.Braid.failed b = ok false)
    (hi : tacenta_braid.Braid.is_initiator b = tacenta_braid.Braid.is_initiator s.braid)
    (hE : tacenta_braid.Braid.epoch b = ok t.post_quantum.epoch)
    (htag : tacenta_braid.Braid.state_tag b = ok x) (hx7 : 7#u8 ≤ x) (hx10 : x ≤ 10#u8) :
    lifecycle.Session.structural_invariant { s with triple := t, braid := b } = ok true := by
  revert h
  unfold lifecycle.Session.structural_invariant lifecycle.Session.is_responder
  simp only [tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public,
    tacenta_triple.State.direction, tacenta_spqr.State.impl.direction, tacenta_triple.State.epoch,
    tacenta_spqr.State.impl.epoch, hdhs, hdir, hfs, hfb, hi, hE, htag, hx7, hx10, if_true, decide_true,
    bind_tc_ok, Bool.false_eq_true, if_false]
  repeat' first
    | (with_reducible exact id)
    | (intro h; simp at h; done)
    | (apply mono_bind; intro _)
    | apply mono_ite
    | (apply strip_bind; intro _)
    | (apply strip_ite_else)

/-- Between two states whose tags are below 7, with the same epochs: the structural clauses read the same. -/
theorem structural_congr_low (s : lifecycle.Session) (t : tacenta_triple.State) (b : tacenta_braid.Braid)
    (x y : U8)
    (hdhs : t.classical.dhs_pub = s.triple.classical.dhs_pub)
    (hdir : t.post_quantum.direction = s.triple.post_quantum.direction)
    (hep : t.post_quantum.epoch = s.triple.post_quantum.epoch)
    (hf : tacenta_braid.Braid.failed b = tacenta_braid.Braid.failed s.braid)
    (hi : tacenta_braid.Braid.is_initiator b = tacenta_braid.Braid.is_initiator s.braid)
    (he : tacenta_braid.Braid.epoch b = tacenta_braid.Braid.epoch s.braid)
    (htb : tacenta_braid.Braid.state_tag b = ok x) (hts : tacenta_braid.Braid.state_tag s.braid = ok y)
    (hx : ¬ 7#u8 ≤ x) (hy : ¬ 7#u8 ≤ y) :
    lifecycle.Session.structural_invariant { s with triple := t, braid := b } =
      lifecycle.Session.structural_invariant s := by
  unfold lifecycle.Session.structural_invariant lifecycle.Session.is_responder
  simp only [tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public,
    tacenta_triple.State.direction, tacenta_spqr.State.impl.direction, tacenta_triple.State.epoch,
    tacenta_spqr.State.impl.epoch, hdhs, hdir, hep, hf, hi, he, htb, hts, hx, hy, if_false, bind_tc_ok]


/-- Committing a failed agreement keeps every budget: its epoch counts as zero. -/
theorem counterRoom_failed (s : lifecycle.Session) (b : tacenta_braid.Braid)
    (hb : tacenta_braid.Braid.failed b = ok true) (k : Nat) (h : CounterRoom s k) :
    CounterRoom { s with braid := b } k := by
  obtain ⟨st⟩ := b
  rw [failed_iff] at hb
  simp only at hb
  subst hb
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  simp only [Tacenta.SessionUnitBraidT1.State.epoch_val]
  have : (0#u64 : U64).val = 0 := rfl
  omega

/-- A budget for more operations is a budget for fewer. -/
theorem counterRoom_mono (s : lifecycle.Session) {j k : Nat} (hjk : j ≤ k) (h : CounterRoom s k) :
    CounterRoom s j := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by omega, by omega, fun p hp ch hch => by have := h3 p hp ch hch; omega, by omega⟩

/-- **A refused `encrypt` keeps `Session::invariant` and every budget**, for every session that passes the
invariant and every refusal: the session returned is the one given, or the one given with its agreement
committed failed (`encrypt_err_leaves_state`), which passes the invariant because a failed agreement is exempt from
clauses (b) and (d) and passes `Braid::invariant`, and counts its epoch as zero.  No hypothesis about any opaque
operation. -/
theorem encrypt_err_keeps_invariant {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (s : lifecycle.Session) (pt : Slice U8) (rng : R) (e : lifecycle.Error) (s' : lifecycle.Session) (rng' : R)
    (hinv : lifecycle.Session.invariant s = ok true)
    (h : lifecycle.Session.encrypt rc crc s pt rng = ok (core.result.Result.Err e, s', rng')) :
    lifecycle.Session.invariant s' = ok true ∧ ∀ k, CounterRoom s k → CounterRoom s' k := by
  rcases Tacenta.UnitLifecycleAtomicity.encrypt_err_leaves_state rc crc s pt rng e s' rng' h with
    rfl | ⟨-, b, rfl, hb⟩
  · exact ⟨hinv, fun _ hk => hk⟩
  · obtain ⟨hstr, htri, -⟩ := (session_invariant_iff s).mp hinv
    exact ⟨(session_invariant_iff _).mpr ⟨structural_failed s b hb hstr, htri, failed_invariant b hb⟩,
      fun k hk => counterRoom_failed s b hb k hk⟩

/-- **A refused `decrypt_ratchet` keeps `Session::invariant` and every budget**: it returns the session it was
given (`decrypt_ratchet_err_leaves_state`).  No hypothesis about any opaque operation. -/
theorem decrypt_ratchet_err_keeps_invariant {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (msg : Slice U8) (rng : R) (e : lifecycle.Error)
    (s' : lifecycle.Session) (rng' : R) (hinv : lifecycle.Session.invariant s = ok true)
    (h : lifecycle.Session.decrypt_ratchet rc crc s msg rng = ok (core.result.Result.Err e, s', rng')) :
    lifecycle.Session.invariant s' = ok true ∧ ∀ k, CounterRoom s k → CounterRoom s' k := by
  rw [Tacenta.UnitLifecycleAtomicity.decrypt_ratchet_err_leaves_state rc crc s msg rng e s' rng' h]
  exact ⟨hinv, fun _ hk => hk⟩

/-- **A refused `decrypt` keeps `Session::invariant` and every budget**: it returns the session it was given
(`decrypt_err_leaves_state`), the size refusal, the initial-message refusals and the inner receive's refusals
included.  No hypothesis about any opaque operation. -/
theorem decrypt_err_keeps_invariant {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (s : lifecycle.Session) (msg : Slice U8) (rng : R) (e : lifecycle.Error) (s' : lifecycle.Session) (rng' : R)
    (hinv : lifecycle.Session.invariant s = ok true)
    (h : lifecycle.Session.decrypt rc crc s msg rng = ok (core.result.Result.Err e, s', rng')) :
    lifecycle.Session.invariant s' = ok true ∧ ∀ k, CounterRoom s k → CounterRoom s' k := by
  rw [Tacenta.UnitLifecycleAtomicity.decrypt_err_leaves_state rc crc s msg rng e s' rng' h]
  exact ⟨hinv, fun _ hk => hk⟩

/-- **The sender's size refusal keeps `Session::invariant` and every budget, and draws nothing**: above
`MAX_PLAINTEXT_LEN`, `encrypt` returns `PlaintextTooLong`, the session and the source as given
(`encrypt_refuses_long_plaintext`).  No hypothesis about any opaque operation. -/
theorem encrypt_size_refusal_keeps_invariant {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (pt : Slice U8) (rng : R)
    (hlong : serialization.MAX_PLAINTEXT_LEN.val < pt.val.length)
    (hinv : lifecycle.Session.invariant s = ok true) :
    ∃ s', lifecycle.Session.encrypt rc crc s pt rng =
        ok (core.result.Result.Err lifecycle.Error.PlaintextTooLong, s', rng) ∧
      lifecycle.Session.invariant s' = ok true ∧ ∀ k, CounterRoom s k → CounterRoom s' k :=
  ⟨s, Tacenta.UnitLifecycleAtomicity.encrypt_refuses_long_plaintext rc crc s pt rng hlong, hinv,
    fun _ hk => hk⟩

/-- **The receiver's size refusal keeps `Session::invariant` and every budget, and draws nothing**: when
`check_frame_size` refuses, `decrypt` returns `Decode(TooLong)`, the session and the source as given
(`decrypt_refuses_long_frame`).  No hypothesis about any opaque operation. -/
theorem decrypt_size_refusal_keeps_invariant {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (msg : Slice U8) (rng : R)
    (hsize : serialization.check_frame_size msg =
      ok (core.result.Result.Err tacenta_wire.DecodeError.TooLong))
    (hinv : lifecycle.Session.invariant s = ok true) :
    ∃ s', lifecycle.Session.decrypt rc crc s msg rng =
        ok (core.result.Result.Err (lifecycle.Error.Decode tacenta_wire.DecodeError.TooLong), s', rng) ∧
      lifecycle.Session.invariant s' = ok true ∧ ∀ k, CounterRoom s k → CounterRoom s' k :=
  ⟨s, Tacenta.UnitLifecycleAtomicity.decrypt_refuses_long_frame rc crc s msg rng hsize, hinv,
    fun _ hk => hk⟩

end Refusal

/-! ## The model: the Triple send with or without an agreement output, and `encrypt` at every agreement state -/

section Model

/-- The sparse model's `advance`, unfolded. -/
theorem advance_ok_parts {st st1 : Model.SparseRatchet.State} {o : Model.SparseRatchet.Output}
    (h : Model.SparseRatchet.advanceDetailed st o = .ok st1) :
    o.keyEpoch = st.epoch + 1 ∧ st.epoch + 1 < Model.SparseRatchet.u64Max ∧
      st1.epoch = o.keyEpoch ∧ st1.direction = st.direction ∧
      st1.skipped = st.skipped.filter
        (fun a => decide (o.keyEpoch < a.1 + Model.SparseRatchet.epochsKept)) ∧
      ∃ c : Model.SparseRatchet.Chains,
        (∀ ch, (c.send = some ch ∨ c.receive = some ch) → ch.n = 0) ∧
        st1.chains = (st.chains.filter (fun p => !(p.1 == o.keyEpoch)) ++ [(o.keyEpoch, c)]).filter
          (fun p => decide (o.keyEpoch < p.1 + Model.SparseRatchet.epochsKept)) := by
  unfold Model.SparseRatchet.advanceDetailed at h
  split_ifs at h with h1 h2
  · simp only [Except.ok.injEq] at h
    subst h
    have he : o.keyEpoch = st.epoch + 1 := by simpa using h2
    refine ⟨he, by omega, rfl, rfl, rfl, _, ?_, rfl⟩
    rintro ch (hc | hc) <;> (simp only [Option.some.injEq] at hc; rw [← hc])

/-- **The sparse model's `advance` keeps `ModelSpqrInv`.**  Model only. -/
theorem modelSpqrInv_advance {st st1 : Model.SparseRatchet.State} {o : Model.SparseRatchet.Output}
    (h : ModelSpqrInv st) (ha : Model.SparseRatchet.advanceDetailed st o = .ok st1) :
    ModelSpqrInv st1 := by
  obtain ⟨he, hlt, hep, -, hsk, c, -, hch⟩ := advance_ok_parts ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsk]; exact (List.length_filter_le _ _).trans h.store_bound
  · intro q hq
    rw [hch, List.mem_filter] at hq
    obtain ⟨hq, hwin⟩ := hq
    simp only [decide_eq_true_eq] at hwin
    rw [hep]
    rcases mem_sent_chains hq with ⟨hq', -⟩ | rfl
    · have := h.epoch_window q hq'
      simp only [Model.SparseRatchet.epochsKept] at hwin ⊢
      constructor
      · omega
      · rw [Nat.lt_min]; omega
    · simp only [Model.SparseRatchet.epochsKept]
      constructor
      · omega
      · rw [Nat.lt_min]; omega
  · rw [hch]
    apply List.Pairwise.sublist List.filter_sublist
    rw [List.pairwise_append]
    refine ⟨h.chains_distinct.sublist List.filter_sublist, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne] at ha
    simp only [List.mem_singleton] at hb
    subst hb
    exact ha.2
  · refine ⟨(o.keyEpoch, c), ?_, by rw [hep]⟩
    rw [hch, List.mem_filter]
    refine ⟨List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    simp [Model.SparseRatchet.epochsKept]
  · intro a ha
    rw [hsk, List.mem_filter] at ha
    obtain ⟨ha, hwin⟩ := ha
    obtain ⟨q, hq, hqa⟩ := h.skipped_chained a ha
    rw [hch]
    by_cases hqe : q.1 = o.keyEpoch
    · refine ⟨(o.keyEpoch, c), ?_, by rw [← hqe, hqa]⟩
      rw [List.mem_filter]
      exact ⟨List.mem_append_right _ (List.mem_singleton_self _), by simp [Model.SparseRatchet.epochsKept]⟩
    · refine ⟨q, ?_, hqa⟩
      rw [List.mem_filter]
      refine ⟨List.mem_append_left _ (List.mem_filter.mpr ⟨hq, by simpa using hqe⟩), ?_⟩
      rw [hqa]; exact hwin
  · rw [hsk]; exact h.skipped_map.sublist List.filter_sublist

/-- A sparse send with an agreement output is an `advance` followed by a send without one.  Model only. -/
theorem spqr_send_some_split {st st' : Model.SparseRatchet.State} {e n : Nat} {key : Model.State.Key}
    {o : Model.SparseRatchet.Output}
    (h : Model.SparseRatchet.sendDetailed st e (some o) = .ok (st', n, key)) :
    ∃ st1, Model.SparseRatchet.advanceDetailed st o = .ok st1 ∧
      Model.SparseRatchet.sendDetailed st1 e none = .ok (st', n, key) := by
  simp only [Model.SparseRatchet.sendDetailed, Model.SparseRatchet.maybeAdvanceDetailed] at h
  rcases ha : Model.SparseRatchet.advanceDetailed st o with r | st1
  · rw [ha] at h; simp at h
  · rw [ha] at h
    refine ⟨st1, rfl, ?_⟩
    simp only [Model.SparseRatchet.sendDetailed, Model.SparseRatchet.maybeAdvanceDetailed]
    exact h

/-- **The sparse model's send keeps `ModelSpqrInv`, with or without an agreement output.**  Model only. -/
theorem modelSpqrInv_send_any {st st' : Model.SparseRatchet.State} {e n : Nat} {key : Model.State.Key}
    {out : Option Model.SparseRatchet.Output}
    (h : ModelSpqrInv st) (hs : Model.SparseRatchet.sendDetailed st e out = .ok (st', n, key)) :
    ModelSpqrInv st' := by
  rcases out with _ | o
  · exact modelSpqrInv_send h hs
  · obtain ⟨st1, ha, hs1⟩ := spqr_send_some_split hs
    exact modelSpqrInv_send (modelSpqrInv_advance h ha) hs1

/-- The sparse send's direction and epoch, with or without an output.  Model only. -/
theorem spqr_send_dir_epoch {st st' : Model.SparseRatchet.State} {e n : Nat} {key : Model.State.Key}
    {out : Option Model.SparseRatchet.Output}
    (hs : Model.SparseRatchet.sendDetailed st e out = .ok (st', n, key)) :
    st'.direction = st.direction ∧ (out = none → st'.epoch = st.epoch) ∧
      (∀ o, out = some o → st'.epoch = o.keyEpoch ∧ o.keyEpoch = st.epoch + 1) := by
  rcases out with _ | o
  · obtain ⟨-, -, -, -, -, -, hep, hdir, -⟩ := spqr_send_frame hs
    exact ⟨hdir, fun _ => hep, fun _ h => by cases h⟩
  · obtain ⟨st1, ha, hs1⟩ := spqr_send_some_split hs
    obtain ⟨he, -, hep1, hdir1, -⟩ := advance_ok_parts ha
    obtain ⟨-, -, -, -, -, -, hep, hdir, -⟩ := spqr_send_frame hs1
    refine ⟨hdir.trans hdir1, fun h => (by cases h), ?_⟩
    intro o' ho'
    cases ho'
    exact ⟨hep.trans hep1, he⟩

/-- **The model Triple's send keeps `ModelTripleInv`, with or without an agreement output**, at every sending
epoch.  Model only. -/
theorem modelTripleInv_send_any {m m' : Model.Triple.State} {e : Nat} {hd : Model.Triple.Header}
    {key : Model.State.Key} {out : Option Model.SparseRatchet.Output} (h : ModelTripleInv m)
    (hs : Model.Triple.sendDetailed m e out = .ok (m', hd, key)) : ModelTripleInv m' := by
  obtain ⟨hr, hq, hroles⟩ := h
  unfold Model.Triple.sendDetailed at hs
  rcases hc : Model.Ratchet.sendDetailed m.classical with _ | ⟨c, dr, mkc⟩
  · rw [hc] at hs; simp at hs
  rw [hc] at hs
  simp only at hs
  rcases hp : Model.SparseRatchet.sendDetailed m.postQuantum e out with _ | ⟨q, pqN, mkq⟩
  · rw [hp] at hs; simp at hs
  rw [hp] at hs
  simp only [Except.ok.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, -, -⟩ := hs
  refine ⟨modelRatchetInv_send hr hc, modelSpqrInv_send_any hq hp, ?_⟩
  obtain ⟨hcks, hcks', -, -, hckr, -, -⟩ := ratchet_send_frame hc
  obtain ⟨hdir, -, -⟩ := spqr_send_dir_epoch hp
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


/-- The lifecycle's agreement send is the Braid model's send at some randomness.  Model only. -/
theorem sendAgreement_is_send {oracle oracle' : Model.Lifecycle.Oracle} {st : Model.Braid.BraidState}
    {r : Option Model.Braid.Msg × Nat × Option Model.Braid.Output × Model.Braid.BraidState}
    (h : Model.Lifecycle.sendAgreement oracle st = some (r, oracle')) :
    ∃ rand, r = Model.Braid.send oracle.braidKem rand st := by
  unfold Model.Lifecycle.sendAgreement at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨draws, rest⟩, -, hr, -⟩ := h
    exact ⟨_, hr.symm⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨0, h.1.symm⟩

/-- **The model's `encrypt` outcomes, at every agreement state**: the session is the one given, or the one given
with its agreement failed, or the one given with the Triple a successful Triple send at the agreement send's
reported epoch and output and the agreement the send's next state, which has not failed.  Model only. -/
theorem encrypt_model_outcomes (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (m : Model.Lifecycle.Session) (pt : Model.Lifecycle.Bytes) :
    (Model.Lifecycle.encrypt view oracle m pt).session = m ∨
      (Model.Lifecycle.encrypt view oracle m pt).session = { m with braid := .failed } ∨
      ∃ rand msg ep out braidNext tripleNext hd key,
        Model.Braid.send oracle.braidKem rand m.braid = (msg, ep, out, braidNext) ∧
        Model.Lifecycle.braidFailed braidNext = false ∧
        Model.Triple.sendDetailed m.triple ep (Model.Lifecycle.sparseOutputOf out) =
          .ok (tripleNext, hd, key) ∧
        (Model.Lifecycle.encrypt view oracle m pt).session =
          { m with triple := tripleNext, braid := braidNext } := by
  unfold Model.Lifecycle.encrypt
  by_cases hl : Model.Lifecycle.maxPlaintextLen < pt.length
  · simp [hl]
  simp only [hl, if_false]
  by_cases hf : Model.Lifecycle.agreementFailed m = true
  · simp [hf]
  simp only [hf, Bool.false_eq_true, if_false]
  rcases hsa : Model.Lifecycle.sendAgreement oracle m.braid with _ | ⟨⟨msg, ep, out, nxt⟩, oracleNext⟩
  · simp
  obtain ⟨rand, hr⟩ := sendAgreement_is_send hsa
  simp only
  by_cases hbf : Model.Lifecycle.braidFailed nxt = true
  · simp only [hbf, if_true]
    rw [(Model.Lifecycle.braidFailed_iff nxt).mp hbf]
    exact Or.inr (Or.inl rfl)
  simp only [hbf, Bool.false_eq_true, if_false]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · rename_i tripleNext header messageKey hsend
      split
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨rand, _, ep, out, nxt, tripleNext, header, messageKey, hr.symm,
          by simpa using hbf, hsend, rfl⟩)

/-- The Braid model's send leaves the epoch, or fails.  Model only. -/
theorem braid_send_epoch (K : Model.Braid.Kem) (rand : Nat) (st : Model.Braid.BraidState) :
    (Model.Braid.send K rand st).2.2.2.epoch = st.epoch ∨ (Model.Braid.send K rand st).2.2.2 = .failed := by
  cases st <;> simp only [Model.Braid.send] <;> (try split) <;>
    simp [Model.Braid.BraidState.epoch]

/-- The Braid model's send has an output only at `headerReceived`, for its epoch.  Model only. -/
theorem braid_send_output (K : Model.Braid.Kem) (rand : Nat) (st : Model.Braid.BraidState)
    (o : Model.Braid.Output) (h : (Model.Braid.send K rand st).2.2.1 = some o) :
    o.keyEpoch = st.epoch ∧ ∃ e a s hk d, st = .headerReceived e a s hk d := by
  cases st <;> simp only [Model.Braid.send] at h <;> (try split at h) <;> simp at h
  rename_i e a s hk d _ _ _ _ _
  subst h
  exact ⟨rfl, e, a, s, hk, d, rfl⟩


/-- The model Triple's send is its two leaf sends.  Model only. -/
theorem triple_send_parts {m m' : Model.Triple.State} {e : Nat} {hd : Model.Triple.Header}
    {key : Model.State.Key} {out : Option Model.SparseRatchet.Output}
    (hs : Model.Triple.sendDetailed m e out = .ok (m', hd, key)) :
    ∃ c dr mkc q pqN mkq, Model.Ratchet.sendDetailed m.classical = .ok (c, dr, mkc) ∧
      Model.SparseRatchet.sendDetailed m.postQuantum e out = .ok (q, pqN, mkq) ∧
      m' = { classical := c, postQuantum := q } := by
  unfold Model.Triple.sendDetailed at hs
  rcases hc : Model.Ratchet.sendDetailed m.classical with _ | ⟨c, dr, mkc⟩
  · rw [hc] at hs; simp at hs
  rw [hc] at hs
  simp only at hs
  rcases hp : Model.SparseRatchet.sendDetailed m.postQuantum e out with _ | ⟨q, pqN, mkq⟩
  · rw [hp] at hs; simp at hs
  rw [hp] at hs
  simp only [Except.ok.injEq, Prod.mk.injEq] at hs
  exact ⟨c, dr, mkc, q, pqN, mkq, rfl, rfl, hs.1.symm⟩

/-- A chain value an entry holds. -/
def InChain (p : Nat × Model.SparseRatchet.Chains) (ch : Model.SparseRatchet.Chain) : Prop :=
  p.2.send = some ch ∨ p.2.receive = some ch

/-- **Every chain counter after a sparse send, with or without an output, is at most one, or at most one more
than a counter the table held before.**  Model only. -/
theorem spqr_send_counters {st st' : Model.SparseRatchet.State} {e n : Nat} {key : Model.State.Key}
    {out : Option Model.SparseRatchet.Output}
    (hs : Model.SparseRatchet.sendDetailed st e out = .ok (st', n, key)) :
    ∀ p ∈ st'.chains, ∀ ch, InChain p ch →
      ch.n ≤ 1 ∨ ∃ p0 ∈ st.chains, ∃ ch0, InChain p0 ch0 ∧ ch.n ≤ ch0.n + 1 := by
  -- one send without an output: each counter is at most one more than a counter of the table it is sent from
  have hone : ∀ {s0 s1 : Model.SparseRatchet.State} {n1 : Nat} {k1 : Model.State.Key},
      Model.SparseRatchet.sendDetailed s0 e none = .ok (s1, n1, k1) →
      ∀ p ∈ s1.chains, ∀ ch, InChain p ch → ∃ p0 ∈ s0.chains, ∃ ch0, InChain p0 ch0 ∧ ch.n ≤ ch0.n + 1 := by
    intro s0 s1 n1 k1 h1 p hp ch hch
    obtain ⟨cs, hmem, c', hc, hrecv, hsend, -, -, -⟩ := spqr_send_frame h1
    rw [hc] at hp
    rcases mem_sent_chains hp with ⟨hp', -⟩ | rfl
    · exact ⟨p, hp', ch, hch, by omega⟩
    · rcases hch with hs' | hr'
      · obtain ⟨ch0, hch0, hn⟩ := hsend ch hs'
        exact ⟨(e, cs), hmem, ch0, Or.inl hch0, by omega⟩
      · exact ⟨(e, cs), hmem, ch, Or.inr (by rw [← hrecv]; exact hr'), by omega⟩
  rcases out with _ | o
  · intro p hp ch hch
    exact Or.inr (hone hs p hp ch hch)
  · obtain ⟨st1, ha, hs1⟩ := spqr_send_some_split hs
    obtain ⟨-, -, -, -, -, c, hc0, hch1⟩ := advance_ok_parts ha
    intro p hp ch hch
    obtain ⟨p1, hp1, ch1, hin1, hle⟩ := hone hs1 p hp ch hch
    rw [hch1, List.mem_filter] at hp1
    rcases mem_sent_chains hp1.1 with ⟨hp1', -⟩ | rfl
    · exact Or.inr ⟨p1, hp1', ch1, hin1, hle⟩
    · have := hc0 ch1 hin1
      exact Or.inl (by omega)

/-- **The model's `encrypt` spends at most one unit of the budget, at every agreement state.**  Model only. -/
theorem modelCounterRoom_encrypt_any (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (m : Model.Lifecycle.Session) (pt : Model.Lifecycle.Bytes) (k : Nat) (h : ModelCounterRoom m (k + 1)) :
    ModelCounterRoom (Model.Lifecycle.encrypt view oracle m pt).session k := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases encrypt_model_outcomes view oracle m pt with he | he | ⟨rand, msg, ep, out, nxt, tn, hd, key, hb, -, hs, he⟩
  · rw [he]
    exact ⟨by omega, by omega, fun p hp ch hch => by have := h3 p hp ch hch; omega, by omega⟩
  · rw [he]
    exact ⟨by simpa using (by omega : m.triple.classical.events + k + 1 < Std.U32.max),
      by simpa using (by omega : m.triple.postQuantum.epoch + k + 1 < Std.U64.max),
      fun p hp ch hch => by have := h3 p hp ch hch; simp only at hp; omega,
      by simp only [Model.Braid.BraidState.epoch]; omega⟩
  · rw [he]
    obtain ⟨c, dr, mkc, q, pqN, mkq, hc, hq, rfl⟩ := triple_send_parts hs
    obtain ⟨-, -, -, -, -, hev, -⟩ := ratchet_send_frame hc
    obtain ⟨-, hep, hoe⟩ := spqr_send_dir_epoch hq
    have hk : k < 2 ^ 32 := by
      have : Std.U32.max = 2 ^ 32 - 1 := by simp [Std.U32.max_eq]
      omega
    have hU : Std.U64.max = 2 ^ 64 - 1 := by simp [Std.U64.max_eq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only; rw [hev]; omega
    · simp only
      rcases hso : Model.Lifecycle.sparseOutputOf out with _ | o
      · rw [hep hso]; omega
      · obtain ⟨h5, h6⟩ := hoe o hso
        rw [h5, h6]; omega
    · intro p hp ch hch
      simp only at hp
      rcases spqr_send_counters hq p hp ch hch with hle | ⟨p0, hp0, ch0, hin0, hle⟩
      · omega
      · have := h3 p0 hp0 ch0 hin0
        omega
    · simp only
      have hbe := braid_send_epoch oracle.braidKem rand m.braid
      rw [hb] at hbe
      simp only at hbe
      rcases hbe with hbe | hbe
      · rw [hbe]; omega
      · rw [hbe]; simp only [Model.Braid.BraidState.epoch]; omega


/-- At `headerReceived`, a send that does not fail has an output for the state's epoch.  Model only. -/
theorem braid_send_headerReceived_output (K : Model.Braid.Kem) (rand e : Nat) (a : Model.Braid.Auth)
    (s0 hk : Model.Braid.Bytes) (d : Model.Braid.Decoder) (msg : Option Model.Braid.Msg) (ep : Nat)
    (out : Option Model.Braid.Output) (nxt : Model.Braid.BraidState)
    (h : Model.Braid.send K rand (.headerReceived e a s0 hk d) = (msg, ep, out, nxt))
    (hnf : nxt ≠ .failed) : ∃ o, out = some o ∧ o.keyEpoch = e := by
  simp only [Model.Braid.send] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.2.2.2.symm hnf
  · simp only [Prod.mk.injEq] at h
    exact ⟨_, h.2.2.1.symm, rfl⟩

end Model

/-! ## The translated agreement send at the two states that draw -/

section BraidSend

/-- **A fresh encoder after one chunk passes `Encoder::invariant` and is sized for its message**, for every
message of at most `32 · MAX_CODEWORDS` bytes, under `DivCeilValue`. -/
theorem fresh_encoder_step (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (s : Slice Std.U8)
    (hcap : (Tacenta.SessionUnitBraidT3.sliceOf s).length ≤ 32 * 65536)
    {enc0 enc1 : tacenta_erasure.Encoder} {c : Option tacenta_erasure.Chunk}
    (hnew : tacenta_erasure.Encoder.new s = ok enc0)
    (hnc : tacenta_erasure.Encoder.next_chunk enc0 = ok (c, enc1)) :
    tacenta_erasure.Encoder.invariant enc1 = ok true ∧
      ∀ len : Usize, len.val = (Tacenta.SessionUnitBraidT3.sliceOf s).length →
        tacenta_braid.encoder_sized enc1 len = ok true := by
  obtain ⟨r0, hr0, hpost0⟩ := Std.WP.spec_imp_exists (Tacenta.UnitErasureRs.Encoder.E_new hdiv s)
  rw [hnew] at hr0; cases hr0
  obtain ⟨-, -, hstore⟩ := hpost0
  obtain ⟨hex0, hnext0⟩ := Tacenta.UnitSatisfiabilityErasureAgrees.new_shape s enc0 hnew
  obtain ⟨r1, hr1, -, hchunks, -, hne⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitSatisfiabilityErasureAgrees.next_chunk_shape' enc0 hex0)
  rw [hnc] at hr1; cases hr1
  simp only at hchunks hne
  have hnmax : enc0.next ≠ core.num.U16.MAX := by
    rw [hnext0]; decide
  obtain ⟨hex1, -⟩ := hne hnmax
  have hlen0 : enc0.chunks.val.length = ((Tacenta.SessionUnitBraidT3.sliceOf s).length + 31) / 32 := by
    have := congrArg List.length hstore
    simp only [Tacenta.UnitErasureRs.storeBytes, List.length_map, List.length_take,
      Tacenta.UnitHeldKemWitness.chunks_length] at this
    omega
  have hlen1 : enc1.chunks.val.length = ((Tacenta.SessionUnitBraidT3.sliceOf s).length + 31) / 32 := by
    rw [hchunks]; exact hlen0
  refine ⟨?_, ?_⟩
  · unfold tacenta_erasure.Encoder.invariant
    have : alloc.vec.Vec.len enc1.chunks ≤ tacenta_erasure.MAX_CODEWORDS := by
      have h1 := alloc.vec.Vec.len_val enc1.chunks
      simp only [tacenta_erasure.MAX_CODEWORDS]
      scalar_tac
    simp [this, hex1]
  · intro len hlen
    obtain ⟨r, hr, hrv⟩ := hdiv len
    unfold tacenta_braid.encoder_sized tacenta_erasure.Encoder.needed
    simp only [Tacenta.UnitSatisfiabilityErasure.chunk_count_eq, hr, bind_tc_ok]
    have h1 := alloc.vec.Vec.len_val enc1.chunks
    have : alloc.vec.Vec.len enc1.chunks = r := by
      apply UScalar.eq_of_val_eq; rw [h1, hrv, hlen]; simpa [alloc.vec.Vec.length] using hlen1
    simp [this]


/-- A successful `extend_from_slice` appends. -/
theorem extend_ok_val {v w : alloc.vec.Vec Std.U8} {s : Slice Std.U8}
    (h : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s = ok w) : w.val = v.val ++ s.val := by
  unfold alloc.vec.Vec.extend_from_slice at h
  split at h
  · split at h
    · rename_i s' hs'
      simp only [ok.injEq] at h
      subst h
      have : s' = s := by
        have := Slice.clone_spec (clone := core.clone.CloneU8.clone) (s := s) (fun _ _ => rfl)
        obtain ⟨r, hr, hp⟩ := Std.WP.spec_imp_exists this
        rw [hs'] at hr; cases hr; exact hp.symm
      subst this; rfl
    · simp at h
    · simp at h
  · simp at h


set_option maxHeartbeats 1000000 in
/-- **`Braid::send` at `KeysUnsampled` (transition (1)) keeps `Braid::invariant` or fails**: the send has no
output, and the next state is `Failed` (key generation refused) or `KeysSampled` at the same epoch and
authenticator, holding the generated key pair and the header encoder after one chunk, and passes
`Braid::invariant`.  Under `KemAgreesFor` (its key-generation clause), `RngTotal`, `KemLenAgrees`,
`KeyGenSizesOf`, `ValidateEkAgrees` and `DivCeilValue`. -/
theorem braid_send_keysUnsampled {K : Model.Braid.Kem} (hka : KemAgreesFor K) {R : Type}
    {rc : rand_core_1.RngCore R} (crc : rand_core_1.CryptoRng R) (hrt : Tacenta.SessionUnitBraidT1.RngTotal rc)
    (hlen : KemLenAgrees K) (hsizes : KeyGenSizesOf K) (hval : ValidateEkAgrees K)
    (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (e : U64) (a : tacenta_braid.Auth) (he : e >= 1#u64) (rng : R)
    (msg : tacenta_braid.Msg) (ep : U64) (out : Option tacenta_braid.Output) (b' : tacenta_braid.Braid) (rng' : R)
    (h : tacenta_braid.Braid.send rc crc ⟨.KeysUnsampled e a⟩ rng = ok ((msg, ep, out, b'), rng')) :
    out = none ∧ (b'.state = .Failed ∨
      ∃ kp enc, b'.state = .KeysSampled e a kp enc ∧ tacenta_braid.Braid.invariant b' = ok true) := by
  unfold tacenta_braid.Braid.send at h
  obtain ⟨st, hs, h⟩ := bind_eq_ok_inv h
  simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
    bind_tc_ok, Tacenta.UnitLifecycleResponderReply.auth_clone_eq, ok.injEq] at hs
  subst hs
  obtain ⟨⟨⟨m1, o1, nxt⟩, rng1⟩, hstep, h⟩ := bind_eq_ok_inv h
  obtain ⟨i, -, h⟩ := bind_eq_ok_inv h
  simp only [ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, -, rfl, rfl⟩, rfl⟩ := h
  simp only [tacenta_braid.Braid.step_send] at hstep
  obtain ⟨⟨r, rngg⟩, hgen, hstep⟩ := bind_eq_ok_inv hstep
  rcases r with kp | err
  · obtain ⟨hh, hhh, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨mac, hmac, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨s1, hs1, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨header1, hext, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨enc, hnew, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨⟨chunk, enc1⟩, hnc, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨mm, -, hstep⟩ := bind_eq_ok_inv hstep
    simp only [ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨⟨-, rfl, rfl⟩, -⟩ := hstep
    refine ⟨rfl, Or.inr ⟨kp, enc1, rfl, ?_⟩⟩
    -- the key pair: from the key-generation clause at this source
    obtain ⟨rng'', rand, hcl⟩ := hka.1 rc crc rng hrt
    rcases hcl with ⟨kp', dk, ekSeed, ekVector, hgen', hkg, ⟨h0, hh0, hh0v⟩, ⟨v, hv, hvv⟩, -⟩ |
      ⟨⟨err, hgen'⟩, -⟩
    · rw [hgen] at hgen'
      simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hgen'
      obtain ⟨rfl, -⟩ := hgen'
      rw [hhh] at hh0; cases hh0
      obtain ⟨hs32, hvl, hhl⟩ := hsizes _ _ _ _ hkg
      have hkp := keyPairValid_of_header hval kp hh v hhh hv ekSeed ekVector hh0v hvv hs32 hvl hhl
      -- the header message: 64 header bytes and a 32-byte MAC
      have hlen96 : (sliceOf header1.deref).length = 96 := by
        have hx := extend_ok_val hext
        simp only [lift, ok.injEq] at hs1
        subst hs1
        have hhv : (vecOf hh).length = 64 := by rw [hh0v]; simp [hs32, hhl]
        simp only [sliceOf, alloc.vec.Vec.deref, List.length_map, hx, List.length_append] at hhv ⊢
        simp only [vecOf, List.length_map] at hhv
        rw [hhv]
        simp [Array.to_slice]
      obtain ⟨henc, hsized⟩ := fresh_encoder_step hdiv _ (by rw [hlen96]; norm_num) hnew hnc
      obtain ⟨⟨v64, hv64, hv64v⟩, -⟩ := hlen
      unfold tacenta_braid.Braid.invariant
      simp only [he, if_true, henc, bind_tc_ok, hv64]
      obtain ⟨x, hx, hxv⟩ : ∃ x : Usize, v64 + tacenta_braid.MAC_LEN = ok x ∧ x.val = 96 := by
        have : tacenta_braid.MAC_LEN.val = 32 := by simp [tacenta_braid.MAC_LEN]
        have hmx := Tacenta.UnitSatisfiabilityBraidAgreements.usize_max_ge 96 (by norm_num)
        obtain ⟨x, hx, hxv⟩ := Std.WP.spec_imp_exists (Usize.add_spec (x := v64)
          (y := tacenta_braid.MAC_LEN) (by simp [Model.Braid.headerSize] at hv64v; scalar_tac))
        exact ⟨x, hx, by simp [Model.Braid.headerSize] at hv64v; scalar_tac⟩
      rw [hx]
      simp only [bind_tc_ok, hsized x (by rw [hxv, hlen96]), if_true, hkp]
    · rw [hgen] at hgen'
      simp at hgen'
  · simp only [tacenta_braid.Msg.empty, bind_tc_ok] at hstep
    obtain ⟨⟨-, rfl, rfl⟩, -⟩ := hstep
    exact ⟨rfl, Or.inl rfl⟩


/-- **The size law of the first half of encapsulation**: every `ct1` the KEM model's `encaps1` returns has the
model's `ct1Size` bytes.  The twin of `KeyGenSizesOf` for encapsulation.  An assumed law. -/
def Encaps1SizesOf (K : Model.Braid.Kem) : Prop :=
  ∀ rand ekSeed hek es ct1 ss, K.encaps1 rand ekSeed hek = some (es, ct1, ss) → ct1.length = K.ct1Size

set_option maxHeartbeats 1000000 in
/-- **`Braid::send` at `HeaderReceived` (transition (7)) keeps `Braid::invariant` or fails**: either the next state is
`Failed` with no output (`encapsulate1` refused), or it is `Ct1Sampled` at the same epoch, with the same header and
`ek_vector` decoder, an output for the state's epoch, and passes `Braid::invariant`.  Under `KemAgreesFor` (its
encapsulation clause), `RngTotal`, `KemLenAgrees`, the size law `Encaps1SizesOf`, `Ct1LenTotal` and `DivCeilValue`. -/
theorem braid_send_headerReceived {K : Model.Braid.Kem} (hka : KemAgreesFor K) {R : Type}
    {rc : rand_core_1.RngCore R} (crc : rand_core_1.CryptoRng R) (hrt : Tacenta.SessionUnitBraidT1.RngTotal rc)
    (hlen : KemLenAgrees K) (hsz : Encaps1SizesOf K) (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8) (dec : tacenta_erasure.Decoder)
    (hinv : tacenta_braid.Braid.invariant ⟨.HeaderReceived e a hdr dec⟩ = ok true) (rng : R)
    (msg : tacenta_braid.Msg) (ep : U64) (out : Option tacenta_braid.Output) (b' : tacenta_braid.Braid) (rng' : R)
    (h : tacenta_braid.Braid.send rc crc ⟨.HeaderReceived e a hdr dec⟩ rng = ok ((msg, ep, out, b'), rng')) :
    (out = none ∧ b'.state = .Failed) ∨
      ∃ a' es ct1 enc key, b'.state = .Ct1Sampled e a' hdr es ct1 enc dec ∧
        out = some { key_epoch := e, key := key } ∧ tacenta_braid.Braid.invariant b' = ok true := by
  unfold tacenta_braid.Braid.send at h
  obtain ⟨st, hs, h⟩ := bind_eq_ok_inv h
  simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
    bind_tc_ok, Tacenta.UnitLifecycleResponderReply.auth_clone_eq, decoder_clone_eq, vec_clone_u8,
    ok.injEq] at hs
  subst hs
  obtain ⟨⟨⟨m1, o1, nxt⟩, rng1⟩, hstep, h⟩ := bind_eq_ok_inv h
  obtain ⟨i, -, h⟩ := bind_eq_ok_inv h
  simp only [ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, -, rfl, rfl⟩, rfl⟩ := h
  simp only [tacenta_braid.Braid.step_send] at hstep
  obtain ⟨⟨r, rngg⟩, henc1, hstep⟩ := bind_eq_ok_inv hstep
  rcases r with ⟨es, ct1, raw1⟩ | err
  · obtain ⟨s1, -, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨a0, -, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨key, -, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨z, -, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨a1, -, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨s2, -, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨auth1, -, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨enc, hnew, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨⟨chunk, enc1⟩, hnc, hstep⟩ := bind_eq_ok_inv hstep
    obtain ⟨mm, -, hstep⟩ := bind_eq_ok_inv hstep
    simp only [ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨⟨-, rfl, rfl⟩, -⟩ := hstep
    refine Or.inr ⟨auth1, es, ct1, enc1, a1, rfl, rfl, ?_⟩
    -- the invariant before: epoch, header length, the vector decoder
    obtain ⟨⟨vh, hvh, hvhv⟩, -, ⟨v1, hv1, hv1v⟩, -⟩ := hlen
    have hpre := hinv
    unfold tacenta_braid.Braid.invariant at hpre
    simp only [hvh, bind_tc_ok] at hpre
    by_cases he : e >= 1#u64
    swap
    · simp [he] at hpre
    by_cases hhl : alloc.vec.Vec.len hdr = vh
    swap
    · simp [he, hhl] at hpre
    simp only [he, hhl, if_true] at hpre
    -- the ciphertext's length, from the encapsulation clause and the size law
    have hs64 : (alloc.vec.Vec.deref hdr).length = Model.Braid.headerSize := by
      have := alloc.vec.Vec.len_val hdr
      rw [hhl] at this
      simp only [Slice.length, alloc.vec.Vec.deref]
      rw [← hvhv, this]
    obtain ⟨rng'', rand', hcl⟩ := hka.2 rc crc (alloc.vec.Vec.deref hdr) rng hrt hs64
    have hct1len : alloc.vec.Vec.len ct1 = v1 := by
      rcases hcl with ⟨es0, ct1raw, ssraw, henc1', hmod⟩ | ⟨⟨err, henc1'⟩, -⟩
      · rw [henc1] at henc1'
        simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at henc1'
        obtain ⟨⟨rfl, rfl, rfl⟩, -⟩ := henc1'
        have hsl : (sliceOf (alloc.vec.Vec.deref hdr)).length = 64 := by
          simpa [sliceOf, Slice.length, Model.Braid.headerSize] using hs64
        obtain ⟨es', hk, -⟩ := hmod ((sliceOf (alloc.vec.Vec.deref hdr)).take 32)
          ((sliceOf (alloc.vec.Vec.deref hdr)).drop 32) (by simp [hsl]) (List.take_append_drop _ _).symm
        have := hsz _ _ _ _ _ _ hk
        apply UScalar.eq_of_val_eq
        rw [alloc.vec.Vec.len_val, hv1v, ← this]
        simp [vecOf]
      · rw [henc1] at henc1'; simp at henc1'
    -- the fresh `ct1` encoder
    have hcap : (sliceOf (alloc.vec.Vec.deref ct1)).length ≤ 32 * 65536 := by
      obtain ⟨v1', hv1', hv1'le⟩ := hct1
      rw [hv1] at hv1'; cases hv1'
      have := alloc.vec.Vec.len_val ct1
      rw [hct1len] at this
      simp only [sliceOf, alloc.vec.Vec.deref, List.length_map]
      simp only [alloc.vec.Vec.length] at this
      omega
    obtain ⟨henc, hsized⟩ := fresh_encoder_step hdiv _ hcap hnew hnc
    have hlv : v1.val = (sliceOf (alloc.vec.Vec.deref ct1)).length := by
      have := alloc.vec.Vec.len_val ct1
      rw [hct1len] at this
      simp only [sliceOf, alloc.vec.Vec.deref, List.length_map]
      simpa [alloc.vec.Vec.length] using this
    unfold tacenta_braid.Braid.invariant
    simp only [he, hhl, hvh, hv1, hct1len, henc, hsized v1 hlv, bind_tc_ok, if_true]
    exact hpre
  · simp only [tacenta_braid.Msg.empty, bind_tc_ok] at hstep
    obtain ⟨⟨-, rfl, rfl⟩, -⟩ := hstep
    exact Or.inl ⟨rfl, rfl⟩


end BraidSend

/-! ## `encrypt` at every agreement state -/

section Encrypt

open Tacenta.SessionUnitRatchetImportInv (bind3_eq_ok_inv)

/-- A Braid is its state. -/
theorem braid_eta (b : tacenta_braid.Braid) : b = ⟨b.state⟩ := rfl

/-- A successful `encrypt` ran the agreement send to a state that has not failed, and a Triple candidate send that
succeeded, and returned the session with the candidate and that state. -/
theorem encrypt_ok_live {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (s : lifecycle.Session) (plaintext : Slice Std.U8) (rng : R) (v : alloc.vec.Vec Std.U8)
    (s' : lifecycle.Session) (rng' : R)
    (h : lifecycle.Session.encrypt rc crc s plaintext rng = ok (core.result.Result.Ok v, s', rng')) :
    ∃ m e o b, tacenta_braid.Braid.send rc crc s.braid rng = ok ((m, e, o, b), rng') ∧
      tacenta_braid.Braid.failed b = ok false ∧
      ∃ sparse cand hdr mk, lifecycle.send_candidate s.triple e sparse = ok (cand, .Ok (hdr, mk)) ∧
        s' = { s with triple := cand, braid := b } := by
  unfold lifecycle.Session.encrypt at h
  by_cases hlong : Slice.len plaintext > serialization.MAX_PLAINTEXT_LEN
  · simp [hlong] at h
  rw [if_neg hlong] at h
  obtain ⟨fb, hfb, h⟩ := bind_eq_ok_inv h
  split at h
  · simp at h
  obtain ⟨⟨⟨m, e, o, b⟩, rng1⟩, hsend, h⟩ := bind_eq_ok_inv h
  obtain ⟨fb1, hfb1, h⟩ := bind_eq_ok_inv h
  split at h
  · simp at h
  rename_i hnf
  obtain ⟨sp, hsp, h⟩ := bind_eq_ok_inv h
  obtain ⟨⟨cand, sent⟩, hcand, h⟩ := bind_eq_ok_inv h
  rcases sent with ⟨hdr, mk⟩ | err
  · simp only at h
    have key : s' = { s with triple := cand, braid := b } ∧ rng' = rng1 := by
      repeat' first
        | (replace h := bind3_eq_ok_inv h; obtain ⟨_, _, _, _, h⟩ := h)
        | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
        | split at h
        | simp only [ok.injEq, Prod.mk.injEq] at h
      all_goals (obtain ⟨-, rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)
    obtain ⟨rfl, rfl⟩ := key
    refine ⟨m, e, o, b, hsend, ?_, sp, cand, hdr, mk, hcand, rfl⟩
    cases fb1
    · exact hfb1
    · exact absurd rfl hnf
  · simp at h

/-- The code Triple's sending key and direction are read through the relation: when the model Triples agree on
them, so do the code Triples. -/
theorem code_triple_frame {dh : DhView} {K : Model.Braid.Kem} {s s' : lifecycle.Session}
    {m m' : Model.Lifecycle.Session} (hrel : SessionRefines dh K s m) (hrel' : SessionRefines dh K s' m')
    (hdhs : m'.triple.classical.dhsPub = m.triple.classical.dhsPub)
    (hdir : m'.triple.postQuantum.direction = m.triple.postQuantum.direction) :
    s'.triple.classical.dhs_pub = s.triple.classical.dhs_pub ∧
      s'.triple.post_quantum.direction = s.triple.post_quantum.direction := by
  obtain ⟨hc0, hq0⟩ := hrel.triple
  obtain ⟨hc1, hq1⟩ := hrel'.triple
  constructor
  · apply keyOf_injective
    have h1 := congrArg Model.State.State.dhsPub hc1
    have h0 := congrArg Model.State.State.dhsPub hc0
    simp only [Tacenta.SessionUnitTripleT3.ratchetAbs] at h1 h0
    rw [h1, h0, hdhs]
  · have h1 := congrArg Model.SparseRatchet.State.direction hq1
    have h0 := congrArg Model.SparseRatchet.State.direction hq0
    simp only [Tacenta.SessionUnitTripleT3.spqrAbs] at h1 h0
    have h : Tacenta.SessionUnitSpqrT3.directionOf s'.triple.post_quantum.direction =
        Tacenta.SessionUnitSpqrT3.directionOf s.triple.post_quantum.direction := by
      rw [h1, h0, hdir]
    revert h
    cases s'.triple.post_quantum.direction <;> cases s.triple.post_quantum.direction <;>
      simp [Tacenta.SessionUnitSpqrT3.directionOf]

/-- The code Triple's sparse epoch is the model's. -/
theorem code_epoch_val {dh : DhView} {K : Model.Braid.Kem} {s : lifecycle.Session} {m : Model.Lifecycle.Session}
    (hrel : SessionRefines dh K s m) : s.triple.post_quantum.epoch.val = m.triple.postQuantum.epoch := by
  have h := congrArg Model.SparseRatchet.State.epoch hrel.triple.2
  simpa [Tacenta.SessionUnitTripleT3.spqrAbs] using h

/-- The model's `encrypt` at a model state the code state's kind fixes: either it is the session given, with
its agreement failed, or a success whose agreement send's next state and Triple are named.  When the code's next
agreement state relates to the model's next session and is of a kind the model state cannot stay at, the outcome is
the success. -/
theorem encrypt_model_success_of_moved {K : Model.Braid.Kem} (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (m : Model.Lifecycle.Session) (pt : Model.Lifecycle.Bytes)
    (st' : tacenta_braid.State)
    (hrel' : Tacenta.SessionUnitBraidT3.StateRefines K st' (Model.Lifecycle.encrypt view oracle m pt).session.braid)
    (hstay : ¬ Tacenta.SessionUnitBraidT3.StateRefines K st' m.braid)
    (hnf : st' ≠ .Failed) :
    ∃ rand msg ep out braidNext tripleNext hd key,
      Model.Braid.send oracle.braidKem rand m.braid = (msg, ep, out, braidNext) ∧
      Model.Triple.sendDetailed m.triple ep (Model.Lifecycle.sparseOutputOf out) = .ok (tripleNext, hd, key) ∧
      (Model.Lifecycle.encrypt view oracle m pt).session = { m with triple := tripleNext, braid := braidNext } := by
  rcases encrypt_model_outcomes view oracle m pt with he | he | ⟨rand, msg, ep, out, nxt, tn, hd, key, hb, -, hs, he⟩
  · rw [he] at hrel'; exact absurd hrel' hstay
  · rw [he] at hrel'
    cases st' <;> simp [Tacenta.SessionUnitBraidT3.StateRefines] at hrel' hnf
  · exact ⟨rand, msg, ep, out, nxt, tn, hd, key, hb, hs, he⟩

/-- The laws the agreement-state walks use beside the Braid send records: the KEM length constants, the
key-generation size law, the key-pair check's agreement and the value law of `div_ceil`.  All four are existing
assumed records or laws of the tree; none is new. -/
structure SendInvariantLaws (K : Model.Braid.Kem) : Prop where
  kemLen : KemLenAgrees K
  keyGenSizes : KeyGenSizesOf K
  validateEk : ValidateEkAgrees K
  divCeil : Tacenta.SessionUnitDecoderBound.DivCeilValue

set_option maxHeartbeats 1000000 in
/-- **`Session::encrypt` at `KeysUnsampled` (key generation) keeps `Session::invariant` and spends one unit of the
budget**, at every session at that agreement state, any epoch: for every session `s` that passes the invariant, has
room for `k + 1` operations and refines a model session `m`, and every successful return `(Ok bytes, s', rng')` of
`encrypt` there whose session refines the model's `encrypt` step from `m`: `s'` passes the invariant and has room
for `k`.  Under `KemAgreesFor` (key generation), `RngTotal` and the four laws of `SendInvariantLaws`; the relation
after the call is a hypothesis. -/
theorem encrypt_keeps_invariant_keysUnsampled {K : Model.Braid.Kem} (hka : KemAgreesFor K) (laws : SendInvariantLaws K)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (hrt : Tacenta.SessionUnitBraidT1.RngTotal rc) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))
    (hrel : SessionRefines dh K s m)
    (hst : ∃ e a, s.braid.state = .KeysUnsampled e a)
    (pt : Slice U8) (ptM : Model.Lifecycle.Bytes) (rng : R)
    (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s pt rng = ok (core.result.Result.Ok bytes, s', rng'))
    (hrel' : SessionRefines dh K s' (Model.Lifecycle.encrypt view oracle m ptM).session) :
    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by
  obtain ⟨hstr, htri, hbr⟩ := (session_invariant_iff s).mp hinv
  obtain ⟨e, a, hst⟩ := hst
  obtain ⟨msg, ep, out, b, hsend, hlive, sparse, cand, hdr, mk, -, hs'⟩ :=
    encrypt_ok_live rc crc s pt rng bytes s' rng' hcall
  have hb0 : s.braid = ⟨.KeysUnsampled e a⟩ := by rw [braid_eta s.braid, hst]
  rw [hb0] at hsend hbr
  have he1 : e >= 1#u64 := by
    unfold tacenta_braid.Braid.invariant at hbr
    simpa using hbr
  obtain ⟨-, hcases⟩ := braid_send_keysUnsampled hka crc hrt laws.kemLen laws.keyGenSizes laws.validateEk
    laws.divCeil e a he1 rng msg ep out b rng' hsend
  rcases hcases with hf | ⟨kp, enc, hbst, hbinv⟩
  · rw [braid_eta b, hf] at hlive; simp [tacenta_braid.Braid.failed] at hlive
  have hb' : s'.braid = b := by rw [hs']
  -- the model step is the success arm, without an agreement output
  have hrelB := hrel.braid
  rw [hst] at hrelB
  have hrelB' := hrel'.braid
  rw [hb', hbst] at hrelB'
  obtain ⟨rand, msgM, epM, outM, nxtM, tn, hd, key, hbM, hts, hm'⟩ :=
    encrypt_model_success_of_moved view oracle m ptM _ hrelB'
      (by
        intro hc
        rcases hmb : m.braid with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
          rw [hmb] at hc hrelB <;> simp [Tacenta.SessionUnitBraidT3.StateRefines] at hc hrelB)
      (by simp)
  have hout : outM = none := by
    rcases houtM : outM with _ | o
    · rfl
    · have := braid_send_output oracle.braidKem rand m.braid o (by rw [hbM, houtM])
      obtain ⟨-, e', a', s0, hk0, d0, hmb⟩ := this
      rw [hmb] at hrelB
      simp [Tacenta.SessionUnitBraidT3.StateRefines] at hrelB
  subst hout
  -- the Triple half, through the model
  have hmodel := (triple_invariant_iff_model hrel.triple).mp htri
  have hmodel' : ModelTripleInv (Model.Lifecycle.encrypt view oracle m ptM).session.triple := by
    rw [hm']; exact modelTripleInv_send_any hmodel hts
  have htri' : tacenta_triple.State.invariant s'.triple = ok true :=
    (triple_invariant_iff_model hrel'.triple).mpr hmodel'
  obtain ⟨c, dr, mkc, q, pqN, mkq, hc, hq, htn⟩ := triple_send_parts hts
  obtain ⟨-, -, hdhsM, -, -, -, -⟩ := ratchet_send_frame hc
  obtain ⟨hdirM, hepM, -⟩ := spqr_send_dir_epoch hq
  have hm'tr : (Model.Lifecycle.encrypt view oracle m ptM).session.triple = tn := by rw [hm']
  obtain ⟨hdhs, hdir⟩ := code_triple_frame hrel hrel'
    (by rw [hm'tr, htn]; exact hdhsM) (by rw [hm'tr, htn]; exact hdirM)
  have hep : s'.triple.post_quantum.epoch = s.triple.post_quantum.epoch := by
    apply UScalar.eq_of_val_eq
    rw [code_epoch_val hrel', code_epoch_val hrel, hm'tr, htn]
    exact hepM (by simp [Model.Lifecycle.sparseOutputOf])
  -- the session's own clauses
  have hstr' : lifecycle.Session.structural_invariant s' = ok true := by
    have hs'' : s' = { s with triple := s'.triple, braid := b } := by rw [hs']
    rw [hs'', structural_congr_low s s'.triple b 1#u8 0#u8 hdhs hdir hep
      (by rw [braid_eta b, hbst, hb0]; simp [tacenta_braid.Braid.failed])
      (by rw [braid_eta b, hbst, hb0]; simp [tacenta_braid.Braid.is_initiator, tacenta_braid.State.epoch])
      (by rw [braid_eta b, hbst, hb0]; simp [tacenta_braid.Braid.epoch, tacenta_braid.State.epoch])
      (by rw [braid_eta b, hbst]; rfl) (by rw [hb0]; rfl) (by decide) (by decide)]
    exact hstr
  refine ⟨(session_invariant_iff s').mpr ⟨hstr', htri', hb' ▸ hbinv⟩, ?_⟩
  exact (counterRoom_iff_model hrel' k).mpr
    (modelCounterRoom_encrypt_any view oracle m ptM k ((counterRoom_iff_model hrel (k + 1)).mp hroom))

set_option maxHeartbeats 1000000 in
/-- **`Session::encrypt` at `HeaderReceived` (the first half of encapsulation, with an agreement output) keeps
`Session::invariant` and spends one unit of the budget**, at every session at that agreement state, any epoch: the
same statement as `encrypt_keeps_invariant_keysUnsampled`, where the step is transition (7) to `Ct1Sampled` and the
Triple's send carries the agreement output, so the sparse ratchet advances to the agreement's epoch (clause (b) at
tag 7).  Under `KemAgreesFor` (encapsulation), `RngTotal`, `Ct1LenTotal`, the laws of `SendInvariantLaws` and the
size law `Encaps1SizesOf`; the relation after the call is a hypothesis. -/
theorem encrypt_keeps_invariant_headerReceived {K : Model.Braid.Kem} (hka : KemAgreesFor K)
    (laws : SendInvariantLaws K) (hsz : Encaps1SizesOf K) (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (hrt : Tacenta.SessionUnitBraidT1.RngTotal rc) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))
    (hrel : SessionRefines dh K s m)
    (hst : ∃ e a hdr dec, s.braid.state = .HeaderReceived e a hdr dec)
    (pt : Slice U8) (ptM : Model.Lifecycle.Bytes) (rng : R)
    (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s pt rng = ok (core.result.Result.Ok bytes, s', rng'))
    (hrel' : SessionRefines dh K s' (Model.Lifecycle.encrypt view oracle m ptM).session) :
    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by
  obtain ⟨hstr, htri, hbr⟩ := (session_invariant_iff s).mp hinv
  obtain ⟨e, a, hdr, dec, hst⟩ := hst
  obtain ⟨msg, ep, out, b, hsend, hlive, sparse, cand, hh, mk, -, hs'⟩ :=
    encrypt_ok_live rc crc s pt rng bytes s' rng' hcall
  have hb0 : s.braid = ⟨.HeaderReceived e a hdr dec⟩ := by rw [braid_eta s.braid, hst]
  rw [hb0] at hsend hbr
  rcases braid_send_headerReceived hka crc hrt laws.kemLen hsz hct1 laws.divCeil e a hdr dec hbr rng msg ep out
      b rng' hsend with ⟨-, hf⟩ | ⟨a', es, ct1, enc, key, hbst, -, hbinv⟩
  · rw [braid_eta b, hf] at hlive; simp [tacenta_braid.Braid.failed] at hlive
  have hb' : s'.braid = b := by rw [hs']
  -- the model step is the success arm, with an agreement output at the agreement's epoch
  have hrelB := hrel.braid
  rw [hst] at hrelB
  have hrelB' := hrel'.braid
  rw [hb', hbst] at hrelB'
  obtain ⟨rand, msgM, epM, outM, nxtM, tn, hd, key', hbM, hts, hm'⟩ :=
    encrypt_model_success_of_moved view oracle m ptM _ hrelB'
      (by
        intro hc
        rcases hmb : m.braid with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
          rw [hmb] at hc hrelB <;> simp [Tacenta.SessionUnitBraidT3.StateRefines] at hc hrelB)
      (by simp)
  obtain ⟨eM, aM, s0, hk0, d0, hmb⟩ : ∃ eM aM s0 hk0 d0, m.braid = .headerReceived eM aM s0 hk0 d0 := by
    rcases hmb : m.braid with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
      rw [hmb] at hrelB <;> simp [Tacenta.SessionUnitBraidT3.StateRefines] at hrelB
    exact ⟨_, _, _, _, _, rfl⟩
  have heM : e.val = eM := by
    rw [hmb] at hrelB
    exact hrelB.1
  have hnxt : nxtM ≠ .failed := by
    intro hn
    rw [hm', hn] at hrelB'
    simp [Tacenta.SessionUnitBraidT3.StateRefines] at hrelB'
  rw [hmb] at hbM
  obtain ⟨o, hout, hoe⟩ := braid_send_headerReceived_output oracle.braidKem rand eM aM s0 hk0 d0 msgM epM outM
    nxtM hbM hnxt
  subst hout
  -- the Triple half, through the model
  have hmodel := (triple_invariant_iff_model hrel.triple).mp htri
  have hmodel' : ModelTripleInv (Model.Lifecycle.encrypt view oracle m ptM).session.triple := by
    rw [hm']; exact modelTripleInv_send_any hmodel hts
  have htri' : tacenta_triple.State.invariant s'.triple = ok true :=
    (triple_invariant_iff_model hrel'.triple).mpr hmodel'
  obtain ⟨c, dr, mkc, q, pqN, mkq, hc, hq, htn⟩ := triple_send_parts hts
  obtain ⟨-, -, hdhsM, -, -, -, -⟩ := ratchet_send_frame hc
  obtain ⟨hdirM, -, hepM⟩ := spqr_send_dir_epoch hq
  have hm'tr : (Model.Lifecycle.encrypt view oracle m ptM).session.triple = tn := by rw [hm']
  obtain ⟨hdhs, hdir⟩ := code_triple_frame hrel hrel'
    (by rw [hm'tr, htn]; exact hdhsM) (by rw [hm'tr, htn]; exact hdirM)
  have hep : s'.triple.post_quantum.epoch = e := by
    apply UScalar.eq_of_val_eq
    rw [code_epoch_val hrel', hm'tr, htn]
    obtain ⟨h5, -⟩ := hepM { keyEpoch := o.keyEpoch, key := o.key } (by simp [Model.Lifecycle.sparseOutputOf])
    simp only at h5
    rw [h5, hoe, heM]
  -- the session's own clauses: into tag 7, whose epoch is the sparse epoch
  have hstr' : lifecycle.Session.structural_invariant s' = ok true := by
    have hs'' : s' = { s with triple := s'.triple, braid := b } := by rw [hs']
    rw [hs'']
    refine structural_folded s s'.triple b 7#u8 hstr hdhs hdir
      (by rw [hb0]; simp [tacenta_braid.Braid.failed]) hlive
      (by rw [braid_eta b, hbst, hb0]; simp [tacenta_braid.Braid.is_initiator, tacenta_braid.State.epoch])
      (by rw [braid_eta b, hbst, hep]; simp [tacenta_braid.Braid.epoch, tacenta_braid.State.epoch])
      (by rw [braid_eta b, hbst]; rfl) (by decide) (by decide)
  refine ⟨(session_invariant_iff s').mpr ⟨hstr', htri', hb' ▸ hbinv⟩, ?_⟩
  exact (counterRoom_iff_model hrel' k).mpr
    (modelCounterRoom_encrypt_any view oracle m ptM k ((counterRoom_iff_model hrel (k + 1)).mp hroom))

/-- A state related to a model state, of a kind whose send takes no draw and that has not failed, is related to a
model state whose send takes no draw. -/
theorem needsDraw_false_of_kind {K : Model.Braid.Kem} {st : tacenta_braid.State} {m : Model.Braid.BraidState}
    (h : Tacenta.SessionUnitBraidT3.StateRefines K st m) (hku : ∀ e a, st ≠ .KeysUnsampled e a)
    (hhr : ∀ e a hdr dec, st ≠ .HeaderReceived e a hdr dec) :
    Model.Lifecycle.braidSendNeedsDraw m = false := by
  cases st <;> cases m <;> simp only [Tacenta.SessionUnitBraidT3.StateRefines] at h <;>
    first
      | rfl
      | exact absurd rfl (hku _ _)
      | exact absurd rfl (hhr _ _ _ _)

/-- **`Session::encrypt` keeps `Session::invariant` and spends one unit of the counter budget at every agreement
state.**  For every session `s` that passes `Session::invariant`, has room for `k + 1` operations (`CounterRoom`)
and refines a model session `m`, and every successful return `(Ok bytes, s', rng')` of `encrypt` there whose
session refines the model's `encrypt` step from `m` (at any view, oracle and model plaintext): `s'` passes
`Session::invariant` and has room for `k` operations.  The cases: the nine states whose send takes no draw
(`encrypt_keeps_invariant_no_draw`), key generation at `KeysUnsampled` and the first half of encapsulation at
`HeaderReceived` (above); at `Failed` no `encrypt` returns `Ok`.  Under `KemCloneAgrees`, `KemAgreesFor`,
`RngTotal`, `Ct1LenTotal`, the four laws of `SendInvariantLaws` and the size law `Encaps1SizesOf`; the relation after
the call is a hypothesis (`encrypt_keeps_invariant_of_contracts` derives it from the encrypt refinement). -/
theorem encrypt_keeps_invariant {K : Model.Braid.Kem} (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees)
    (hka : KemAgreesFor K) (laws : SendInvariantLaws K) (hsz : Encaps1SizesOf K)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (hrt : Tacenta.SessionUnitBraidT1.RngTotal rc) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))
    (hrel : SessionRefines dh K s m)
    (pt : Slice U8) (ptM : Model.Lifecycle.Bytes) (rng : R)
    (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s pt rng = ok (core.result.Result.Ok bytes, s', rng'))
    (hrel' : SessionRefines dh K s' (Model.Lifecycle.encrypt view oracle m ptM).session) :
    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by
  by_cases hku : ∃ e a, s.braid.state = .KeysUnsampled e a
  · exact encrypt_keeps_invariant_keysUnsampled hka laws rc crc hrt dh view oracle s m k hinv hroom hrel
      hku pt ptM rng bytes s' rng' hcall hrel'
  by_cases hhr : ∃ e a hdr dec, s.braid.state = .HeaderReceived e a hdr dec
  · exact encrypt_keeps_invariant_headerReceived hka laws hsz hct1 rc crc hrt dh view oracle s m k hinv hroom
      hrel hhr pt ptM rng bytes s' rng' hcall hrel'
  exact encrypt_keeps_invariant_no_draw hkcl rc crc dh K view oracle s m k hinv hroom hrel
    (needsDraw_false_of_kind hrel.braid (fun e a h => hku ⟨e, a, h⟩)
      (fun e a hdr dec h => hhr ⟨e, a, hdr, dec, h⟩)) pt ptM rng bytes s' rng' hcall hrel'

/-- **The same at every agreement state other than `HeaderReceived`, without the size law of encapsulation**: the
complement of the one state where `encrypt_keeps_invariant` uses `Encaps1SizesOf`. -/
theorem encrypt_keeps_invariant_unless_sampling {K : Model.Braid.Kem}
    (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees) (hka : KemAgreesFor K) (laws : SendInvariantLaws K)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (hrt : Tacenta.SessionUnitBraidT1.RngTotal rc) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))
    (hrel : SessionRefines dh K s m)
    (hns : ∀ e a hdr dec, s.braid.state ≠ .HeaderReceived e a hdr dec)
    (pt : Slice U8) (ptM : Model.Lifecycle.Bytes) (rng : R)
    (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s pt rng = ok (core.result.Result.Ok bytes, s', rng'))
    (hrel' : SessionRefines dh K s' (Model.Lifecycle.encrypt view oracle m ptM).session) :
    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by
  by_cases hku : ∃ e a, s.braid.state = .KeysUnsampled e a
  · exact encrypt_keeps_invariant_keysUnsampled hka laws rc crc hrt dh view oracle s m k hinv hroom hrel
      hku pt ptM rng bytes s' rng' hcall hrel'
  have hhr : ¬ ∃ e a hdr dec, s.braid.state = .HeaderReceived e a hdr dec := by
    rintro ⟨e, a, hdr, dec, h⟩; exact hns e a hdr dec h
  exact encrypt_keeps_invariant_no_draw hkcl rc crc dh K view oracle s m k hinv hroom hrel
    (needsDraw_false_of_kind hrel.braid (fun e a h => hku ⟨e, a, h⟩)
      (fun e a hdr dec h => hhr ⟨e, a, hdr, dec, h⟩)) pt ptM rng bytes s' rng' hcall hrel'

end Encrypt

/-! ## Composed with the encrypt refinement: every outcome of `encrypt` -/

section Composed

open Tacenta.UnitLifecycleT3 (PublicEncryptWitness KemView OracleOf DhCodecOf CodewordViewSendOf
  BraidSendRefinementContracts TripleSendRefinementContracts ZeroizingRoundTrips
  BraidSendTraceAgreementCounted EncryptNonterminalRouteProviders public_session_encrypt_of_send_contracts)

/-- **Every outcome of `encrypt` keeps `Session::invariant` and the budget, given the encrypt refinement's
conclusion at the call** (`PublicEncryptWitness`): the call returns, its session refines the model's `encrypt`
step, passes `Session::invariant` and has room for `k` operations when the session given had room for `k + 1`.
A success is `encrypt_keeps_invariant` with the relation the witness carries; a refusal is
`encrypt_err_keeps_invariant`, which keeps the whole budget. -/
theorem encrypt_keeps_invariant_of_witness {K : Model.Braid.Kem}
    (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees) (hka : KemAgreesFor K) (laws : SendInvariantLaws K)
    (hsz : Encaps1SizesOf K) (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (hrt : Tacenta.SessionUnitBraidT1.RngTotal rc) (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))
    (hrel : SessionRefines dh K s m) (pt : Slice U8) (rng : R)
    (hw : PublicEncryptWitness rc crc trace dh K view oracle s m pt rng) :
    ∃ output, lifecycle.Session.encrypt rc crc s pt rng = ok output ∧
      SessionRefines dh K output.2.1
        (Model.Lifecycle.encrypt view oracle m (Tacenta.UnitLifecycleT3.sliceOf pt)).session ∧
      lifecycle.Session.invariant output.2.1 = ok true ∧ CounterRoom output.2.1 k := by
  obtain ⟨⟨r, s', rng'⟩, hcall, hstep⟩ := hw
  refine ⟨_, hcall, hstep.session, ?_⟩
  rcases r with bytes | e
  · exact encrypt_keeps_invariant hkcl hka laws hsz hct1 rc crc hrt dh view oracle s m k hinv hroom hrel pt _
      rng bytes s' rng' hcall hstep.session
  · obtain ⟨h1, h2⟩ := encrypt_err_keeps_invariant rc crc s pt rng e s' rng' hinv hcall
    exact ⟨h1, h2 k (counterRoom_mono s (by omega) hroom)⟩

/-- **`Session::encrypt` keeps `Session::invariant` and the counter budget at every session and every agreement
state, composed with the encrypt refinement**: under exactly the hypotheses of the general encrypt refinement
`public_session_encrypt_of_send_contracts` (its per-call records `braidTrace` and `providers` among them, which are
not discharged here), the Braid send records it already takes (whose `KemCloneAgrees`, `KemAgreesFor`, `RngTotal`
and `Ct1LenTotal` fields are used), the four laws of `SendInvariantLaws`, the size law `Encaps1SizesOf`, and, at the
call, `Session::invariant` and room for `k + 1` operations: the call returns, and the session it returns refines the
model's `encrypt` step, passes `Session::invariant` and has room for `k` operations.  Every outcome: success at each
agreement state, and every refusal. -/
theorem encrypt_keeps_invariant_of_contracts
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
    {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
    {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session}
    {model : Model.Lifecycle.Session} {plaintext : Slice Std.U8} {rng : R}
    (braid : BraidSendRefinementContracts rc K)
    (braidTrace : BraidSendTraceAgreementCounted rc crc trace K oracle real model rng)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded)
    (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (headroom : Tacenta.UnitLifecycleT1.EncryptHeadroom real plaintext)
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (codec : DhCodecOf dh) (codewordView : CodewordViewSendOf view)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (providers : EncryptNonterminalRouteProviders rc crc trace dh kem K view oracle
      real model plaintext rng)
    (laws : SendInvariantLaws K) (hsz : Encaps1SizesOf K) (k : Nat)
    (hinv : lifecycle.Session.invariant real = ok true) (hroom : CounterRoom real (k + 1)) :
    ∃ output, lifecycle.Session.encrypt rc crc real plaintext rng = ok output ∧
      SessionRefines dh K output.2.1
        (Model.Lifecycle.encrypt view oracle model (Tacenta.UnitLifecycleT3.sliceOf plaintext)).session ∧
      lifecycle.Session.invariant output.2.1 = ok true ∧ CounterRoom output.2.1 k :=
  encrypt_keeps_invariant_of_witness braid.kemClone braid.hka laws hsz braid.ct1Len rc crc braid.rng trace dh
    view oracle real model k hinv hroom hrel plaintext rng
    (public_session_encrypt_of_send_contracts braid braidTrace triple aead dhCodec headroom oracleOf codec
      codewordView hkdf hz80 hz32 hzKeys hrel htrace providers)

end Composed

/-! ## On the run: the established initiator's first send, through the general step -/

section Run

open Tacenta.UnitLifecycleT3 (KemView OracleOf DhCodecOf CodewordViewSendOf BraidSendRefinementContracts
  TripleSendRefinementContracts ZeroizingRoundTrips)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid KemCiphertextLenOf establishedModelOf
  establish_initiator_for_parts establish_initiator_for_admissible sessionRefines_established)
open Tacenta.UnitLifecycleEstablishedEncrypt (KeyGenSeededFor established_encrypt_successor_refines)
open Tacenta.UnitLifecycleRestoredSession (KemCiphertextLenBound)
open Tacenta.UnitHeadroomInvariant (OptionEqU64Shape)

/-- **Every successful `establish_initiator_for` output has room for `k` operations whenever `k + 1 < u32::MAX`**:
its clock and chain counters are 0, its sparse epoch 0 and its agreement epoch 1.  No hypothesis. -/
theorem counterRoom_established {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : R) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1)) (k : Nat) (hk : k + 1 < Std.U32.max) :
    CounterRoom s k := by
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rc crc our bundle expected rng0 rng1 s h
  have hU32 : Std.U32.max = 2 ^ 32 - 1 := by simp [Std.U32.max_eq]
  have hU64 : Std.U64.max = 2 ^ 64 - 1 := by simp [Std.U64.max_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.session,
      Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple]
    simp; omega
  · simp only [Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.session,
      Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple]
    simp; omega
  · intro q hq ch hch
    simp [Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.session,
      Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple,
      Tacenta.UnitLifecycleEstablishInitiatorShape.initChains, Tacenta.UnitHeadroomSatisfiable.vecOf] at hq
    subst hq
    rcases hch with h | h <;> (simp at h; subst h; simp; omega)
  · simp only [Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.session,
      Tacenta.SessionUnitBraidT1.State.epoch_val]
    simp; omega

/-- **The established initiator's first send, through the general step**: under the hypotheses of
`established_encrypt_successor_refines` (which supplies the relation after the call), the establishment's laws
`DhPublicValid`, `OptionEqU64Shape` (which with `KemCiphertextLenOf` give the invariant before the call,
`establish_initiator_for_admissible`) and the four laws of `SendInvariantLaws`, at every successful first `encrypt`
at a session `establish_initiator_for` returned: the session after it passes `Session::invariant` and has room for
every `j` with `j + 2 < u32::MAX` further operations, so it meets `CounterHeadroom`.  Derived from
`encrypt_keeps_invariant_keysUnsampled`, with no shape of the session after the send
(`established_encrypt_successor_admissible` gets the invariant by fixing the shape). -/
theorem established_encrypt_invariant_via_general [Tacenta.SessionUnitT1.DerivedKeysModel] {R E : Type}
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
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (laws : SendInvariantLaws oracle.braidKem)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws)
    (hdraws : ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng =
      ok (core.result.Result.Ok bytes, s', rng')) :
    lifecycle.Session.invariant s' = ok true ∧
      (∀ j, j + 2 < Std.U32.max → CounterRoom s' j) ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s' := by
  have hinv := establish_initiator_for_admissible rcE crcE hpub hct hoeq our bundle expected rng0 rng1 s h
  have hrel := sessionRefines_established rcE crcE dh oracle.braidKem our bundle expected rng0 rng1 s h
  have hrel' := (established_encrypt_successor_refines rc crc trace dh kem view oracle braid triple aead
    dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct hbound rcE crcE our bundle expected rng0
    rng1 s h plaintext hroom rng htrace hdraws bytes s' rng' hcall).1
  have hst : ∃ e a, s.braid.state = .KeysUnsampled e a := by
    obtain ⟨p, rfl⟩ := establish_initiator_for_parts rcE crcE our bundle expected rng0 rng1 s h
    exact ⟨_, _, rfl⟩
  have hstep : ∀ j, j + 2 < Std.U32.max →
      lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' j := fun j hj =>
    encrypt_keeps_invariant_keysUnsampled braid.hka laws rc crc braid.rng dh view oracle s
      (establishedModelOf dh s) j hinv
      (counterRoom_established rcE crcE our bundle expected rng0 rng1 s h (j + 1) (by omega)) hrel hst
      plaintext _ rng bytes s' rng' hcall hrel'
  have hU32 : Std.U32.max = 2 ^ 32 - 1 := by simp [Std.U32.max_eq]
  refine ⟨(hstep 0 (by omega)).1, fun j hj => (hstep j hj).2, ?_⟩
  exact (counterRoom_zero s').mp (hstep 0 (by omega)).2

/-- `Encaps1SizesOf` has a model: the toy KEM's first half of encapsulation returns a `ct1` of its `ct1Size` (64)
bytes.  Consistency of the statement only; not a statement about the shipping KEM. -/
theorem encaps1Sizes_toyKemR : Encaps1SizesOf Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR := by
  intro rand ekSeed hek es ct1 ss h
  simp only [Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR, Model.Braid.toyKem, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨-, rfl, -⟩ := h
  simp [Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR, Model.Braid.toyKem]

/-- **The general step's premises at `KeysUnsampled` hold together on a run**: at the real constants, under the laws
of `established_encrypt_successor_reachable` (a toy model holds them together, `established_encrypt_laws_model`), at
every 64-byte source where the model's key generation answers, there is an establishment and a first `encrypt` at
which every hypothesis of `established_encrypt_invariant_via_general` holds (`EstablishedEncryptSuccessorHypotheses`),
the call returns `Ok`, and the session it leaves passes `Session::invariant` and has room for every `j` with `j + 2 <
u32::MAX` further operations, derived through the general step. -/
theorem established_encrypt_via_general_reachable (K : Model.Braid.Kem) (dh : DhView) (kem : KemView)
    (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom
      Tacenta.UnitSatisfiabilityJoint.Interp.real Tacenta.UnitLifecycleIntegrationScreen.byteRng))
    (S : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape
      Tacenta.UnitSatisfiabilityJoint.Interp.real Tacenta.UnitLifecycleIntegrationScreen.byteRng
      Tacenta.UnitLifecycleIntegrationScreen.byteCrc)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf)
    (X : Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLaws K dh kem)
    (hsizes : KeyGenSizesOf K) (our : lifecycle.Identity) (seed : List Std.U8)
    (hseed : seed.length = 64)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle) (s : lifecycle.Session)
      (rng1 : List Std.U8) (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : List Std.U8),
      oracle.braidKem = K ∧
      Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses
        Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
        Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh kem
        Tacenta.UnitLifecycleRepair.witnessView oracle Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc our bundle
        bundle.bundle.identity_key [] rng1 s Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed ∧
      lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc s Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext
        seed = ok (core.result.Result.Ok bytes, s', rng') ∧
      lifecycle.Session.invariant s' = ok true ∧ (∀ j, j + 2 < Std.U32.max → CounterRoom s' j) := by
  obtain ⟨oracle, bundle, s, rng1, bytes, s', rng', hK, H, hcall, -, -⟩ :=
    Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_reachable K dh kem L A S hpub hct X
      hsizes our seed hseed hkg
  obtain ⟨inst⟩ := H.derivedKeys
  obtain ⟨hinv, hroom, -⟩ := established_encrypt_invariant_via_general _ _ _ dh kem _ oracle H.braid H.triple
    H.aead H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen
    H.kemCiphertextLen H.kemCiphertextBound H.dhPublicValid H.optionEq
    ⟨H.kemLen, H.keyGenSizes, H.validateEk, H.divCeil⟩ _ _ our bundle _ [] rng1 s H.established _ H.room
    seed H.trace_eq H.draws bytes s' rng' hcall
  exact ⟨oracle, bundle, s, rng1, bytes, s', rng', hK, H, hcall, hinv, hroom⟩

end Run

end Tacenta.UnitLifecycleEncryptPreserve

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
info: 'Tacenta.UnitLifecycleEncryptPreserve.failed_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.failed_iff

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.failed_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.validate_ek,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.failed_invariant

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.strip_ite_else' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.strip_ite_else

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.structural_failed' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.structural_failed

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.structural_folded' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.structural_folded

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.structural_congr_low' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.structural_congr_low

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.counterRoom_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.counterRoom_failed

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.counterRoom_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.counterRoom_mono

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.encrypt_err_keeps_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_kem.IncrementalKeyPair.ek_vector,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.encrypt_err_keeps_invariant

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.decrypt_ratchet_err_keeps_invariant' depends on axioms: [propext,
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
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
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
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.decrypt_ratchet_err_keeps_invariant

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.decrypt_err_keeps_invariant' depends on axioms: [propext,
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
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
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
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.decrypt_err_keeps_invariant

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.encrypt_size_refusal_keeps_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_kem.IncrementalKeyPair.ek_vector,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.encrypt_size_refusal_keeps_invariant

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.decrypt_size_refusal_keeps_invariant' depends on axioms: [propext,
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
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
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
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.decrypt_size_refusal_keeps_invariant

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.advance_ok_parts' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.advance_ok_parts

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.modelSpqrInv_advance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.modelSpqrInv_advance

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.spqr_send_some_split' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.spqr_send_some_split

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.modelSpqrInv_send_any' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.modelSpqrInv_send_any

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.spqr_send_dir_epoch' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.spqr_send_dir_epoch

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.modelTripleInv_send_any' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.modelTripleInv_send_any

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.sendAgreement_is_send' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.sendAgreement_is_send

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.encrypt_model_outcomes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.encrypt_model_outcomes

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.braid_send_epoch' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.braid_send_epoch

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.braid_send_output' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.braid_send_output

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.triple_send_parts' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.triple_send_parts

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.spqr_send_counters' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.spqr_send_counters

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.modelCounterRoom_encrypt_any' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.modelCounterRoom_encrypt_any

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.braid_send_headerReceived_output' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.braid_send_headerReceived_output

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.fresh_encoder_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.fresh_encoder_step

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.extend_ok_val' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.extend_ok_val

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.braid_send_keysUnsampled' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.braid_send_keysUnsampled

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.braid_send_headerReceived' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.braid_send_headerReceived

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.braid_eta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.braid_eta

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.encrypt_ok_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.encrypt_ok_live

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.code_triple_frame' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.code_triple_frame

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.code_epoch_val' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.code_epoch_val

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.encrypt_model_success_of_moved' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.encrypt_model_success_of_moved

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_keysUnsampled' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_keysUnsampled

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_headerReceived' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_headerReceived

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.needsDraw_false_of_kind' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.needsDraw_false_of_kind

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_unless_sampling' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_unless_sampling

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_of_witness' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_of_witness

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_of_contracts' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_of_contracts

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.counterRoom_established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.counterRoom_established

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.established_encrypt_invariant_via_general' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.established_encrypt_invariant_via_general

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.encaps1Sizes_toyKemR' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEncryptPreserve.encaps1Sizes_toyKemR

/--
info: 'Tacenta.UnitLifecycleEncryptPreserve.established_encrypt_via_general_reachable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEncryptPreserve.established_encrypt_via_general_reachable

/--
info: Tacenta.UnitLifecycleEncryptPreserve.failed_iff : ∀ (b : tacenta_braid.Braid),
  b.failed = ok true ↔ b.state = tacenta_braid.State.Failed
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.failed_iff

/--
info: Tacenta.UnitLifecycleEncryptPreserve.failed_invariant : ∀ (b : tacenta_braid.Braid),
  b.failed = ok true → b.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.failed_invariant

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.strip_ite_else : ∀ {c : Prop} [inst : Decidable c] {b y : Result Bool},
  (b = ok true → y = ok true) → (if c then b else ok false) = ok true → y = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.strip_ite_else

/--
info: Tacenta.UnitLifecycleEncryptPreserve.structural_failed : ∀ (s : lifecycle.Session) (b : tacenta_braid.Braid),
  b.failed = ok true →
    s.structural_invariant = ok true →
      { triple := s.triple, braid := b, ratchet_private := s.ratchet_private, identity_ad := s.identity_ad,
            our_identity_public := s.our_identity_public, peer_identity_public := s.peer_identity_public,
            pending_initial := s.pending_initial,
            established_ephemeral := s.established_ephemeral }.structural_invariant =
        ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.structural_failed

/--
info: Tacenta.UnitLifecycleEncryptPreserve.structural_folded : ∀ (s : lifecycle.Session) (t : tacenta_triple.State)
  (b : tacenta_braid.Braid) (x : U8),
  s.structural_invariant = ok true →
    t.classical.dhs_pub = s.triple.classical.dhs_pub →
      t.post_quantum.direction = s.triple.post_quantum.direction →
        s.braid.failed = ok false →
          b.failed = ok false →
            b.is_initiator = s.braid.is_initiator →
              b.epoch = ok t.post_quantum.epoch →
                b.state_tag = ok x →
                  7#u8 ≤ x →
                    x ≤ 10#u8 →
                      { triple := t, braid := b, ratchet_private := s.ratchet_private, identity_ad := s.identity_ad,
                            our_identity_public := s.our_identity_public,
                            peer_identity_public := s.peer_identity_public, pending_initial := s.pending_initial,
                            established_ephemeral := s.established_ephemeral }.structural_invariant =
                        ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.structural_folded

/--
info: Tacenta.UnitLifecycleEncryptPreserve.structural_congr_low : ∀ (s : lifecycle.Session) (t : tacenta_triple.State)
  (b : tacenta_braid.Braid) (x y : U8),
  t.classical.dhs_pub = s.triple.classical.dhs_pub →
    t.post_quantum.direction = s.triple.post_quantum.direction →
      t.post_quantum.epoch = s.triple.post_quantum.epoch →
        b.failed = s.braid.failed →
          b.is_initiator = s.braid.is_initiator →
            b.epoch = s.braid.epoch →
              b.state_tag = ok x →
                s.braid.state_tag = ok y →
                  ¬7#u8 ≤ x →
                    ¬7#u8 ≤ y →
                      { triple := t, braid := b, ratchet_private := s.ratchet_private, identity_ad := s.identity_ad,
                            our_identity_public := s.our_identity_public,
                            peer_identity_public := s.peer_identity_public, pending_initial := s.pending_initial,
                            established_ephemeral := s.established_ephemeral }.structural_invariant =
                        s.structural_invariant
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.structural_congr_low

/--
info: Tacenta.UnitLifecycleEncryptPreserve.counterRoom_failed : ∀ (s : lifecycle.Session) (b : tacenta_braid.Braid),
  b.failed = ok true →
    ∀ (k : ℕ),
      Tacenta.UnitLifecycleSendPreserve.CounterRoom s k →
        Tacenta.UnitLifecycleSendPreserve.CounterRoom
          { triple := s.triple, braid := b, ratchet_private := s.ratchet_private, identity_ad := s.identity_ad,
            our_identity_public := s.our_identity_public, peer_identity_public := s.peer_identity_public,
            pending_initial := s.pending_initial, established_ephemeral := s.established_ephemeral }
          k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.counterRoom_failed

/--
info: Tacenta.UnitLifecycleEncryptPreserve.counterRoom_mono : ∀ (s : lifecycle.Session) {j k : ℕ},
  j ≤ k → Tacenta.UnitLifecycleSendPreserve.CounterRoom s k → Tacenta.UnitLifecycleSendPreserve.CounterRoom s j
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.counterRoom_mono

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.encrypt_err_keeps_invariant : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (pt : Slice U8) (rng : R) (e : lifecycle.Error)
  (s' : lifecycle.Session) (rng' : R),
  s.invariant = ok true →
    lifecycle.Session.encrypt rc crc s pt rng = ok (core.result.Result.Err e, s', rng') →
      s'.invariant = ok true ∧
        ∀ (k : ℕ),
          Tacenta.UnitLifecycleSendPreserve.CounterRoom s k → Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.encrypt_err_keeps_invariant

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.decrypt_ratchet_err_keeps_invariant : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (msg : Slice U8) (rng : R) (e : lifecycle.Error)
  (s' : lifecycle.Session) (rng' : R),
  s.invariant = ok true →
    lifecycle.Session.decrypt_ratchet rc crc s msg rng = ok (core.result.Result.Err e, s', rng') →
      s'.invariant = ok true ∧
        ∀ (k : ℕ),
          Tacenta.UnitLifecycleSendPreserve.CounterRoom s k → Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.decrypt_ratchet_err_keeps_invariant

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.decrypt_err_keeps_invariant : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (msg : Slice U8) (rng : R) (e : lifecycle.Error)
  (s' : lifecycle.Session) (rng' : R),
  s.invariant = ok true →
    lifecycle.Session.decrypt rc crc s msg rng = ok (core.result.Result.Err e, s', rng') →
      s'.invariant = ok true ∧
        ∀ (k : ℕ),
          Tacenta.UnitLifecycleSendPreserve.CounterRoom s k → Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.decrypt_err_keeps_invariant

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.encrypt_size_refusal_keeps_invariant : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (pt : Slice U8) (rng : R),
  ↑serialization.MAX_PLAINTEXT_LEN < (↑pt).length →
    s.invariant = ok true →
      ∃ s',
        lifecycle.Session.encrypt rc crc s pt rng =
            ok (core.result.Result.Err lifecycle.Error.PlaintextTooLong, s', rng) ∧
          s'.invariant = ok true ∧
            ∀ (k : ℕ),
              Tacenta.UnitLifecycleSendPreserve.CounterRoom s k → Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.encrypt_size_refusal_keeps_invariant

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.decrypt_size_refusal_keeps_invariant : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (msg : Slice U8) (rng : R),
  serialization.check_frame_size msg = ok (core.result.Result.Err tacenta_wire.DecodeError.TooLong) →
    s.invariant = ok true →
      ∃ s',
        lifecycle.Session.decrypt rc crc s msg rng =
            ok (core.result.Result.Err (lifecycle.Error.Decode tacenta_wire.DecodeError.TooLong), s', rng) ∧
          s'.invariant = ok true ∧
            ∀ (k : ℕ),
              Tacenta.UnitLifecycleSendPreserve.CounterRoom s k → Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.decrypt_size_refusal_keeps_invariant

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.advance_ok_parts : ∀ {st st1 : Model.SparseRatchet.State}
  {o : Model.SparseRatchet.Output},
  Model.SparseRatchet.advanceDetailed st o = Except.ok st1 →
    o.keyEpoch = st.epoch + 1 ∧
      st.epoch + 1 < Model.SparseRatchet.u64Max ∧
        st1.epoch = o.keyEpoch ∧
          st1.direction = st.direction ∧
            st1.skipped = List.filter (fun a => decide (o.keyEpoch < a.1 + Model.SparseRatchet.epochsKept)) st.skipped ∧
              ∃ c,
                (∀ (ch : Model.SparseRatchet.Chain), c.send = some ch ∨ c.receive = some ch → ch.n = 0) ∧
                  st1.chains =
                    List.filter (fun p => decide (o.keyEpoch < p.1 + Model.SparseRatchet.epochsKept))
                      (List.filter (fun p => !p.1 == o.keyEpoch) st.chains ++ [(o.keyEpoch, c)])
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.advance_ok_parts

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.modelSpqrInv_advance : ∀ {st st1 : Model.SparseRatchet.State}
  {o : Model.SparseRatchet.Output},
  Tacenta.UnitTripleInvModel.ModelSpqrInv st →
    Model.SparseRatchet.advanceDetailed st o = Except.ok st1 → Tacenta.UnitTripleInvModel.ModelSpqrInv st1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.modelSpqrInv_advance

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.spqr_send_some_split : ∀ {st st' : Model.SparseRatchet.State} {e n : ℕ}
  {key : Model.State.Key} {o : Model.SparseRatchet.Output},
  Model.SparseRatchet.sendDetailed st e (some o) = Except.ok (st', n, key) →
    ∃ st1,
      Model.SparseRatchet.advanceDetailed st o = Except.ok st1 ∧
        Model.SparseRatchet.sendDetailed st1 e none = Except.ok (st', n, key)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.spqr_send_some_split

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.modelSpqrInv_send_any : ∀ {st st' : Model.SparseRatchet.State} {e n : ℕ}
  {key : Model.State.Key} {out : Option Model.SparseRatchet.Output},
  Tacenta.UnitTripleInvModel.ModelSpqrInv st →
    Model.SparseRatchet.sendDetailed st e out = Except.ok (st', n, key) → Tacenta.UnitTripleInvModel.ModelSpqrInv st'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.modelSpqrInv_send_any

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.spqr_send_dir_epoch : ∀ {st st' : Model.SparseRatchet.State} {e n : ℕ}
  {key : Model.State.Key} {out : Option Model.SparseRatchet.Output},
  Model.SparseRatchet.sendDetailed st e out = Except.ok (st', n, key) →
    st'.direction = st.direction ∧
      (out = none → st'.epoch = st.epoch) ∧
        ∀ (o : Model.SparseRatchet.Output), out = some o → st'.epoch = o.keyEpoch ∧ o.keyEpoch = st.epoch + 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.spqr_send_dir_epoch

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.modelTripleInv_send_any : ∀ {m m' : Model.Triple.State} {e : ℕ}
  {hd : Model.Triple.Header} {key : Model.State.Key} {out : Option Model.SparseRatchet.Output},
  Tacenta.UnitTripleInvModel.ModelTripleInv m →
    Model.Triple.sendDetailed m e out = Except.ok (m', hd, key) → Tacenta.UnitTripleInvModel.ModelTripleInv m'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.modelTripleInv_send_any

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.sendAgreement_is_send : ∀ {oracle oracle' : Model.Lifecycle.Oracle}
  {st : Model.Braid.BraidState} {r : Option Model.Braid.Msg × ℕ × Option Model.Braid.Output × Model.Braid.BraidState},
  Model.Lifecycle.sendAgreement oracle st = some (r, oracle') → ∃ rand, r = Model.Braid.send oracle.braidKem rand st
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.sendAgreement_is_send

/--
info: Tacenta.UnitLifecycleEncryptPreserve.encrypt_model_outcomes : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (m : Model.Lifecycle.Session) (pt : Model.Lifecycle.Bytes),
  (Model.Lifecycle.encrypt view oracle m pt).session = m ∨
    (Model.Lifecycle.encrypt view oracle m pt).session =
        { triple := m.triple, braid := Model.Braid.BraidState.failed, ratchetPrivate := m.ratchetPrivate,
          identityAd := m.identityAd, ourIdentityPublic := m.ourIdentityPublic,
          peerIdentityPublic := m.peerIdentityPublic, pendingInitial := m.pendingInitial,
          establishedEphemeral := m.establishedEphemeral } ∨
      ∃ rand msg ep out braidNext tripleNext hd key,
        Model.Braid.send oracle.braidKem rand m.braid = (msg, ep, out, braidNext) ∧
          Model.Lifecycle.braidFailed braidNext = false ∧
            Model.Triple.sendDetailed m.triple ep (Model.Lifecycle.sparseOutputOf out) =
                Except.ok (tripleNext, hd, key) ∧
              (Model.Lifecycle.encrypt view oracle m pt).session =
                { triple := tripleNext, braid := braidNext, ratchetPrivate := m.ratchetPrivate,
                  identityAd := m.identityAd, ourIdentityPublic := m.ourIdentityPublic,
                  peerIdentityPublic := m.peerIdentityPublic, pendingInitial := m.pendingInitial,
                  establishedEphemeral := m.establishedEphemeral }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.encrypt_model_outcomes

/--
info: Tacenta.UnitLifecycleEncryptPreserve.braid_send_epoch : ∀ (K : Model.Braid.Kem) (rand : ℕ)
  (st : Model.Braid.BraidState),
  (Model.Braid.send K rand st).2.2.2.epoch = st.epoch ∨
    (Model.Braid.send K rand st).2.2.2 = Model.Braid.BraidState.failed
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.braid_send_epoch

/--
info: Tacenta.UnitLifecycleEncryptPreserve.braid_send_output : ∀ (K : Model.Braid.Kem) (rand : ℕ)
  (st : Model.Braid.BraidState) (o : Model.Braid.Output),
  (Model.Braid.send K rand st).2.2.1 = some o →
    o.keyEpoch = st.epoch ∧ ∃ e a s hk d, st = Model.Braid.BraidState.headerReceived e a s hk d
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.braid_send_output

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.triple_send_parts : ∀ {m m' : Model.Triple.State} {e : ℕ}
  {hd : Model.Triple.Header} {key : Model.State.Key} {out : Option Model.SparseRatchet.Output},
  Model.Triple.sendDetailed m e out = Except.ok (m', hd, key) →
    ∃ c dr mkc q pqN mkq,
      Model.Ratchet.sendDetailed m.classical = Except.ok (c, dr, mkc) ∧
        Model.SparseRatchet.sendDetailed m.postQuantum e out = Except.ok (q, pqN, mkq) ∧
          m' = { classical := c, postQuantum := q }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.triple_send_parts

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.spqr_send_counters : ∀ {st st' : Model.SparseRatchet.State} {e n : ℕ}
  {key : Model.State.Key} {out : Option Model.SparseRatchet.Output},
  Model.SparseRatchet.sendDetailed st e out = Except.ok (st', n, key) →
    ∀ p ∈ st'.chains,
      ∀ (ch : Model.SparseRatchet.Chain),
        Tacenta.UnitLifecycleEncryptPreserve.InChain p ch →
          ch.n ≤ 1 ∨ ∃ p0 ∈ st.chains, ∃ ch0, Tacenta.UnitLifecycleEncryptPreserve.InChain p0 ch0 ∧ ch.n ≤ ch0.n + 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.spqr_send_counters

/--
info: Tacenta.UnitLifecycleEncryptPreserve.modelCounterRoom_encrypt_any : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (m : Model.Lifecycle.Session) (pt : Model.Lifecycle.Bytes) (k : ℕ),
  Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom m (k + 1) →
    Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom (Model.Lifecycle.encrypt view oracle m pt).session k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.modelCounterRoom_encrypt_any

/--
info: Tacenta.UnitLifecycleEncryptPreserve.braid_send_headerReceived_output : ∀ (K : Model.Braid.Kem) (rand e : ℕ)
  (a : Model.Braid.Auth) (s0 hk : Model.Braid.Bytes) (d : Model.Braid.Decoder) (msg : Option Model.Braid.Msg) (ep : ℕ)
  (out : Option Model.Braid.Output) (nxt : Model.Braid.BraidState),
  Model.Braid.send K rand (Model.Braid.BraidState.headerReceived e a s0 hk d) = (msg, ep, out, nxt) →
    nxt ≠ Model.Braid.BraidState.failed → ∃ o, out = some o ∧ o.keyEpoch = e
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.braid_send_headerReceived_output

/--
info: Tacenta.UnitLifecycleEncryptPreserve.fresh_encoder_step : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  ∀ (s : Slice U8),
    (Tacenta.SessionUnitBraidT3.sliceOf s).length ≤ 32 * 65536 →
      ∀ {enc0 enc1 : tacenta_erasure.Encoder} {c : Option tacenta_erasure.Chunk},
        tacenta_erasure.Encoder.new s = ok enc0 →
          enc0.next_chunk = ok (c, enc1) →
            enc1.invariant = ok true ∧
              ∀ (len : Usize),
                ↑len = (Tacenta.SessionUnitBraidT3.sliceOf s).length → tacenta_braid.encoder_sized enc1 len = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.fresh_encoder_step

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.extend_ok_val : ∀ {v w : alloc.vec.Vec U8} {s : Slice U8},
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s = ok w → ↑w = ↑v ++ ↑s
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.extend_ok_val

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.braid_send_keysUnsampled : ∀ {K : Model.Braid.Kem},
  Tacenta.SessionUnitBraidT3.KemAgreesFor K →
    ∀ {R : Type} {rc : rand_core_1.RngCore R} (crc : rand_core_1.CryptoRng R),
      Tacenta.SessionUnitBraidT1.RngTotal rc →
        Tacenta.SessionUnitBraidT3.KemLenAgrees K →
          Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K →
            Tacenta.SessionUnitBraidT3.ValidateEkAgrees K →
              Tacenta.SessionUnitDecoderBound.DivCeilValue →
                ∀ (e : U64) (a : tacenta_braid.Auth),
                  e ≥ 1#u64 →
                    ∀ (rng : R) (msg : tacenta_braid.Msg) (ep : U64) (out : Option tacenta_braid.Output)
                      (b' : tacenta_braid.Braid) (rng' : R),
                      tacenta_braid.Braid.send rc crc { state := tacenta_braid.State.KeysUnsampled e a } rng =
                          ok ((msg, ep, out, b'), rng') →
                        out = none ∧
                          (b'.state = tacenta_braid.State.Failed ∨
                            ∃ kp enc, b'.state = tacenta_braid.State.KeysSampled e a kp enc ∧ b'.invariant = ok true)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.braid_send_keysUnsampled

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.braid_send_headerReceived : ∀ {K : Model.Braid.Kem},
  Tacenta.SessionUnitBraidT3.KemAgreesFor K →
    ∀ {R : Type} {rc : rand_core_1.RngCore R} (crc : rand_core_1.CryptoRng R),
      Tacenta.SessionUnitBraidT1.RngTotal rc →
        Tacenta.SessionUnitBraidT3.KemLenAgrees K →
          Tacenta.UnitLifecycleEncryptPreserve.Encaps1SizesOf K →
            Tacenta.SessionUnitBraidT1.Ct1LenTotal →
              Tacenta.SessionUnitDecoderBound.DivCeilValue →
                ∀ (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8) (dec : tacenta_erasure.Decoder),
                  { state := tacenta_braid.State.HeaderReceived e a hdr dec }.invariant = ok true →
                    ∀ (rng : R) (msg : tacenta_braid.Msg) (ep : U64) (out : Option tacenta_braid.Output)
                      (b' : tacenta_braid.Braid) (rng' : R),
                      tacenta_braid.Braid.send rc crc { state := tacenta_braid.State.HeaderReceived e a hdr dec } rng =
                          ok ((msg, ep, out, b'), rng') →
                        out = none ∧ b'.state = tacenta_braid.State.Failed ∨
                          ∃ a' es ct1 enc key,
                            b'.state = tacenta_braid.State.Ct1Sampled e a' hdr es ct1 enc dec ∧
                              out = some { key_epoch := e, key := key } ∧ b'.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.braid_send_headerReceived

/--
info: Tacenta.UnitLifecycleEncryptPreserve.braid_eta : ∀ (b : tacenta_braid.Braid), b = { state := b.state }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.braid_eta

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.encrypt_ok_live : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (plaintext : Slice U8) (rng : R) (v : alloc.vec.Vec U8)
  (s' : lifecycle.Session) (rng' : R),
  lifecycle.Session.encrypt rc crc s plaintext rng = ok (core.result.Result.Ok v, s', rng') →
    ∃ m e o b,
      tacenta_braid.Braid.send rc crc s.braid rng = ok ((m, e, o, b), rng') ∧
        b.failed = ok false ∧
          ∃ sparse cand hdr mk,
            lifecycle.send_candidate s.triple e sparse = ok (cand, core.result.Result.Ok (hdr, mk)) ∧
              s' =
                { triple := cand, braid := b, ratchet_private := s.ratchet_private, identity_ad := s.identity_ad,
                  our_identity_public := s.our_identity_public, peer_identity_public := s.peer_identity_public,
                  pending_initial := s.pending_initial, established_ephemeral := s.established_ephemeral }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.encrypt_ok_live

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.code_triple_frame : ∀ {dh : Tacenta.UnitLifecycleT3.DhView} {K : Model.Braid.Kem}
  {s s' : lifecycle.Session} {m m' : Model.Lifecycle.Session},
  Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
    Tacenta.UnitLifecycleT3.SessionRefines dh K s' m' →
      m'.triple.classical.dhsPub = m.triple.classical.dhsPub →
        m'.triple.postQuantum.direction = m.triple.postQuantum.direction →
          s'.triple.classical.dhs_pub = s.triple.classical.dhs_pub ∧
            s'.triple.post_quantum.direction = s.triple.post_quantum.direction
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.code_triple_frame

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.code_epoch_val : ∀ {dh : Tacenta.UnitLifecycleT3.DhView} {K : Model.Braid.Kem}
  {s : lifecycle.Session} {m : Model.Lifecycle.Session},
  Tacenta.UnitLifecycleT3.SessionRefines dh K s m → ↑s.triple.post_quantum.epoch = m.triple.postQuantum.epoch
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.code_epoch_val

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.encrypt_model_success_of_moved : ∀ {K : Model.Braid.Kem}
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle) (m : Model.Lifecycle.Session)
  (pt : Model.Lifecycle.Bytes) (st' : tacenta_braid.State),
  Tacenta.SessionUnitBraidT3.StateRefines K st' (Model.Lifecycle.encrypt view oracle m pt).session.braid →
    ¬Tacenta.SessionUnitBraidT3.StateRefines K st' m.braid →
      st' ≠ tacenta_braid.State.Failed →
        ∃ rand msg ep out braidNext tripleNext hd key,
          Model.Braid.send oracle.braidKem rand m.braid = (msg, ep, out, braidNext) ∧
            Model.Triple.sendDetailed m.triple ep (Model.Lifecycle.sparseOutputOf out) =
                Except.ok (tripleNext, hd, key) ∧
              (Model.Lifecycle.encrypt view oracle m pt).session =
                { triple := tripleNext, braid := braidNext, ratchetPrivate := m.ratchetPrivate,
                  identityAd := m.identityAd, ourIdentityPublic := m.ourIdentityPublic,
                  peerIdentityPublic := m.peerIdentityPublic, pendingInitial := m.pendingInitial,
                  establishedEphemeral := m.establishedEphemeral }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.encrypt_model_success_of_moved

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_keysUnsampled : ∀ {K : Model.Braid.Kem},
  Tacenta.SessionUnitBraidT3.KemAgreesFor K →
    Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws K →
      ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R),
        Tacenta.SessionUnitBraidT1.RngTotal rc →
          ∀ (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
            (oracle : Model.Lifecycle.Oracle) (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : ℕ),
            s.invariant = ok true →
              Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
                  (∃ e a, s.braid.state = tacenta_braid.State.KeysUnsampled e a) →
                    ∀ (pt : Slice U8) (ptM : Model.Lifecycle.Bytes) (rng : R) (bytes : alloc.vec.Vec U8)
                      (s' : lifecycle.Session) (rng' : R),
                      lifecycle.Session.encrypt rc crc s pt rng = ok (core.result.Result.Ok bytes, s', rng') →
                        Tacenta.UnitLifecycleT3.SessionRefines dh K s'
                            (Model.Lifecycle.encrypt view oracle m ptM).session →
                          s'.invariant = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_keysUnsampled

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_headerReceived : ∀ {K : Model.Braid.Kem},
  Tacenta.SessionUnitBraidT3.KemAgreesFor K →
    Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws K →
      Tacenta.UnitLifecycleEncryptPreserve.Encaps1SizesOf K →
        Tacenta.SessionUnitBraidT1.Ct1LenTotal →
          ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R),
            Tacenta.SessionUnitBraidT1.RngTotal rc →
              ∀ (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
                (oracle : Model.Lifecycle.Oracle) (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : ℕ),
                s.invariant = ok true →
                  Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                    Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
                      (∃ e a hdr dec, s.braid.state = tacenta_braid.State.HeaderReceived e a hdr dec) →
                        ∀ (pt : Slice U8) (ptM : Model.Lifecycle.Bytes) (rng : R) (bytes : alloc.vec.Vec U8)
                          (s' : lifecycle.Session) (rng' : R),
                          lifecycle.Session.encrypt rc crc s pt rng = ok (core.result.Result.Ok bytes, s', rng') →
                            Tacenta.UnitLifecycleT3.SessionRefines dh K s'
                                (Model.Lifecycle.encrypt view oracle m ptM).session →
                              s'.invariant = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_headerReceived

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.needsDraw_false_of_kind : ∀ {K : Model.Braid.Kem} {st : tacenta_braid.State}
  {m : Model.Braid.BraidState},
  Tacenta.SessionUnitBraidT3.StateRefines K st m →
    (∀ (e : U64) (a : tacenta_braid.Auth), st ≠ tacenta_braid.State.KeysUnsampled e a) →
      (∀ (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8) (dec : tacenta_erasure.Decoder),
          st ≠ tacenta_braid.State.HeaderReceived e a hdr dec) →
        Model.Lifecycle.braidSendNeedsDraw m = false
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.needsDraw_false_of_kind

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant : ∀ {K : Model.Braid.Kem},
  Tacenta.SessionUnitBraidT3.KemCloneAgrees →
    Tacenta.SessionUnitBraidT3.KemAgreesFor K →
      Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws K →
        Tacenta.UnitLifecycleEncryptPreserve.Encaps1SizesOf K →
          Tacenta.SessionUnitBraidT1.Ct1LenTotal →
            ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R),
              Tacenta.SessionUnitBraidT1.RngTotal rc →
                ∀ (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
                  (oracle : Model.Lifecycle.Oracle) (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : ℕ),
                  s.invariant = ok true →
                    Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                      Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
                        ∀ (pt : Slice U8) (ptM : Model.Lifecycle.Bytes) (rng : R) (bytes : alloc.vec.Vec U8)
                          (s' : lifecycle.Session) (rng' : R),
                          lifecycle.Session.encrypt rc crc s pt rng = ok (core.result.Result.Ok bytes, s', rng') →
                            Tacenta.UnitLifecycleT3.SessionRefines dh K s'
                                (Model.Lifecycle.encrypt view oracle m ptM).session →
                              s'.invariant = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_unless_sampling : ∀ {K : Model.Braid.Kem},
  Tacenta.SessionUnitBraidT3.KemCloneAgrees →
    Tacenta.SessionUnitBraidT3.KemAgreesFor K →
      Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws K →
        ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R),
          Tacenta.SessionUnitBraidT1.RngTotal rc →
            ∀ (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
              (oracle : Model.Lifecycle.Oracle) (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : ℕ),
              s.invariant = ok true →
                Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                  Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
                    (∀ (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8) (dec : tacenta_erasure.Decoder),
                        s.braid.state ≠ tacenta_braid.State.HeaderReceived e a hdr dec) →
                      ∀ (pt : Slice U8) (ptM : Model.Lifecycle.Bytes) (rng : R) (bytes : alloc.vec.Vec U8)
                        (s' : lifecycle.Session) (rng' : R),
                        lifecycle.Session.encrypt rc crc s pt rng = ok (core.result.Result.Ok bytes, s', rng') →
                          Tacenta.UnitLifecycleT3.SessionRefines dh K s'
                              (Model.Lifecycle.encrypt view oracle m ptM).session →
                            s'.invariant = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_unless_sampling

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_of_witness : ∀ {K : Model.Braid.Kem},
  Tacenta.SessionUnitBraidT3.KemCloneAgrees →
    Tacenta.SessionUnitBraidT3.KemAgreesFor K →
      Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws K →
        Tacenta.UnitLifecycleEncryptPreserve.Encaps1SizesOf K →
          Tacenta.SessionUnitBraidT1.Ct1LenTotal →
            ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R),
              Tacenta.SessionUnitBraidT1.RngTotal rc →
                ∀ (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView)
                  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle) (s : lifecycle.Session)
                  (m : Model.Lifecycle.Session) (k : ℕ),
                  s.invariant = ok true →
                    Tacenta.UnitLifecycleSendPreserve.CounterRoom s (k + 1) →
                      Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
                        ∀ (pt : Slice U8) (rng : R),
                          Tacenta.UnitLifecycleT3.PublicEncryptWitness rc crc trace dh K view oracle s m pt rng →
                            ∃ output,
                              lifecycle.Session.encrypt rc crc s pt rng = ok output ∧
                                Tacenta.UnitLifecycleT3.SessionRefines dh K output.2.1
                                    (Model.Lifecycle.encrypt view oracle m
                                        (Tacenta.UnitLifecycleT3.sliceOf pt)).session ∧
                                  output.2.1.invariant = ok true ∧
                                    Tacenta.UnitLifecycleSendPreserve.CounterRoom output.2.1 k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_of_witness

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_of_contracts : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView}
  {kem : Tacenta.UnitLifecycleT3.KemView} {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
  {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session} {model : Model.Lifecycle.Session} {plaintext : Slice U8}
  {rng : R},
  Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc K →
    Tacenta.UnitLifecycleT3.BraidSendTraceAgreementCounted rc crc trace K oracle real model rng →
      Tacenta.UnitLifecycleT3.TripleSendRefinementContracts →
        Tacenta.UnitLifecycleT1.AeadSealBounded →
          Tacenta.UnitLifecycleT1.DhCodecTotal →
            Tacenta.UnitLifecycleT1.EncryptHeadroom real plaintext →
              Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle →
                Tacenta.UnitLifecycleT3.DhCodecOf dh →
                  Tacenta.UnitLifecycleT3.CodewordViewSendOf view →
                    Tacenta.SessionUnitT3.HkdfAgrees →
                      Tacenta.SessionUnitT3.ZeroizingRoundTrips80 →
                        Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Std.Array U8 32#usize) →
                          Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
                              (Std.Array U8 32#usize × Std.Array U8 32#usize × Std.Array U8 16#usize) →
                            Tacenta.UnitLifecycleT3.SessionRefines dh K real model →
                              trace rng = oracle.draws →
                                ∀
                                  (providers :
                                    Tacenta.UnitLifecycleT3.EncryptNonterminalRouteProviders rc crc trace dh kem K view
                                      oracle real model plaintext rng),
                                  Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws K →
                                    Tacenta.UnitLifecycleEncryptPreserve.Encaps1SizesOf K →
                                      ∀ (k : ℕ),
                                        real.invariant = ok true →
                                          Tacenta.UnitLifecycleSendPreserve.CounterRoom real (k + 1) →
                                            ∃ output,
                                              lifecycle.Session.encrypt rc crc real plaintext rng = ok output ∧
                                                Tacenta.UnitLifecycleT3.SessionRefines dh K output.2.1
                                                    (Model.Lifecycle.encrypt view oracle model
                                                        (Tacenta.UnitLifecycleT3.sliceOf plaintext)).session ∧
                                                  output.2.1.invariant = ok true ∧
                                                    Tacenta.UnitLifecycleSendPreserve.CounterRoom output.2.1 k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.encrypt_keeps_invariant_of_contracts

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.counterRoom_established : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
  (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : R) (s : lifecycle.Session),
  lifecycle.establish_initiator_for rc crc our bundle expected rng0 = ok (core.result.Result.Ok s, rng1) →
    ∀ (k : ℕ), k + 1 < U32.max → Tacenta.UnitLifecycleSendPreserve.CounterRoom s k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.counterRoom_established

/--
info: @Tacenta.UnitLifecycleEncryptPreserve.established_encrypt_invariant_via_general : ∀
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
                                Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws oracle.braidKem →
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
                                              (∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) →
                                                ∀ (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                                                  lifecycle.Session.encrypt rc crc s plaintext rng =
                                                      ok (core.result.Result.Ok bytes, s', rng') →
                                                    s'.invariant = ok true ∧
                                                      (∀ (j : ℕ),
                                                          j + 2 < U32.max →
                                                            Tacenta.UnitLifecycleSendPreserve.CounterRoom s' j) ∧
                                                        Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.established_encrypt_invariant_via_general

/--
info: Tacenta.UnitLifecycleEncryptPreserve.encaps1Sizes_toyKemR : Tacenta.UnitLifecycleEncryptPreserve.Encaps1SizesOf
  Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.encaps1Sizes_toyKemR

/--
info: Tacenta.UnitLifecycleEncryptPreserve.established_encrypt_via_general_reachable : ∀ (K : Model.Braid.Kem)
  (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    Nonempty
        (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
      Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc →
        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
            Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLaws K dh kem →
              Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K →
                ∀ (our : lifecycle.Identity) (seed : List U8),
                  seed.length = 64 →
                    K.keyGen (Model.Lifecycle.braidRandomness (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠ none →
                      ∃ oracle bundle s rng1 bytes s' rng',
                        oracle.braidKem = K ∧
                          Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses
                              Tacenta.UnitLifecycleIntegrationScreen.byteRng
                              Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                              Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh kem
                              Tacenta.UnitLifecycleRepair.witnessView oracle
                              Tacenta.UnitLifecycleIntegrationScreen.byteRng
                              Tacenta.UnitLifecycleIntegrationScreen.byteCrc our bundle bundle.bundle.identity_key []
                              rng1 s Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed ∧
                            lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                  Tacenta.UnitLifecycleIntegrationScreen.byteCrc s
                                  Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed =
                                ok (core.result.Result.Ok bytes, s', rng') ∧
                              s'.invariant = ok true ∧
                                ∀ (j : ℕ), j + 2 < U32.max → Tacenta.UnitLifecycleSendPreserve.CounterRoom s' j
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEncryptPreserve.established_encrypt_via_general_reachable

/--
info: def Tacenta.UnitLifecycleEncryptPreserve.InChain : ℕ × Model.SparseRatchet.Chains → Model.SparseRatchet.Chain → Prop :=
fun p ch => p.2.send = some ch ∨ p.2.receive = some ch
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEncryptPreserve.InChain

/--
info: def Tacenta.UnitLifecycleEncryptPreserve.Encaps1SizesOf : Model.Braid.Kem → Prop :=
fun K =>
  ∀ (rand : ℕ) (ekSeed hek es ct1 ss : Model.Braid.Bytes),
    K.encaps1 rand ekSeed hek = some (es, ct1, ss) → List.length ct1 = K.ct1Size
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEncryptPreserve.Encaps1SizesOf

/--
info: structure Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws (K : Model.Braid.Kem) : Prop
number of parameters: 1
fields:
  Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws.kemLen : Tacenta.SessionUnitBraidT3.KemLenAgrees K
  Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws.keyGenSizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf
      K
  Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws.validateEk : Tacenta.SessionUnitBraidT3.ValidateEkAgrees K
  Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws.divCeil : Tacenta.SessionUnitDecoderBound.DivCeilValue
constructor:
  Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws.mk {K : Model.Braid.Kem}
    (kemLen : Tacenta.SessionUnitBraidT3.KemLenAgrees K)
    (keyGenSizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K)
    (validateEk : Tacenta.SessionUnitBraidT3.ValidateEkAgrees K)
    (divCeil : Tacenta.SessionUnitDecoderBound.DivCeilValue) : Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws K
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws
