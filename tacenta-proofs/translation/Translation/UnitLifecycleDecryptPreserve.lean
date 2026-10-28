import Translation.UnitLifecycleReceivePreserve
import Translation.UnitLifecycleEncryptPreserve
import Translation.UnitErasureRsGlue

/-!
# `Session::decrypt` keeps `Session::invariant` at every agreement state

`UnitLifecycleReceivePreserve` shows the receive step in the in-order scope while the agreement stays at
`NoHeaderReceived` (holding at most one chunk) or at `KeysSampled`, without an agreement output.  This module removes
both restrictions on the agreement: the translated `Braid::receive` keeps `Braid::invariant` at every state and every
transition, the model's receive keeps clause (b) and the role in step with the sparse epoch, and the Triple's receive
keeps `ModelTripleInv` with or without the agreement's output (the sparse ratchet's `advance`).  Together:
`decrypt_ratchet` and `decrypt` keep the invariant and spend one unit of the budget at every agreement state, in the
in-order scope of the Triple with the output (`InOrderOut`).

## What it shows

* The header decoder at any number of chunks: `decoder_invariant_iff` (`Decoder::invariant` is its four clauses),
  `add_chunk_keeps` (`add_chunk` keeps it, the size and `needed`), `decoder_message_len` (a completed message has the
  decoder's size, under `DivCeilValue` and `TruncatePrefix`).  The earlier module covered at most two chunks.
* `braid_receive_keeps_invariant`: **every successful `Braid::receive`, of every message, from any agreement that
  passes `Braid::invariant`, returns a candidate that passes it**, at all twelve states (the `Failed` arms
  included).  Stated of the translated agreement alone, with no model relation, so it holds of an agreement restored
  from bytes as well.  The state arms are `step_receive_*`, `finish_encaps_inv` and `clone_inv`.
* The model: `receive_clauses` (the agreement's receive keeps the role or fails, and keeps clause (b) at the sparse
  epoch its output moves the sparse ratchet to); `modelTripleInv_receive_out` (the Triple's receive with or without
  the output keeps `ModelTripleInv` in the scope `InOrderOut`); `decryptRatchet_receiveStep` and
  `decrypt_receiveStep` (the model's own `decryptRatchet` and `decrypt` of a frame in that scope are a `ReceiveStep`,
  at every agreement state); `modelCounterRoom_receive_any` (a `ReceiveStep` spends at most one unit of the budget);
  `step_frame_any` (what a `ReceiveStep` keeps of the direction, the sending key, clause (b) and the role).  Model
  only.
* The session's own clauses: `structural_after` (`Session::structural_invariant` after a new Triple, agreement and
  ratchet key whose agreement has failed, or reads the same role and clause (b)); `modelClauseB_of_structural` and
  `codeClauseB_of_model` (clause (b) moved between the code and the model through the relation).  Under
  `OptionEqU64Shape`.
* `decrypt_ratchet_keeps_invariant`, `decrypt_keeps_invariant`: **for every session `s` that passes
  `Session::invariant`, has room for `k + 1` operations and refines a model session `m`, every successful
  `decrypt_ratchet` (or public `decrypt`) there whose session refines a model session that is a `ReceiveStep` from
  `m` leaves a session that passes `Session::invariant` and has room for `k`, at every agreement state.**
  `decrypt_keeps_invariant_model_step` takes the relation at the model's own `decrypt` step.  The refused calls are
  `UnitLifecycleEncryptPreserve`'s.
* `receiveStep_of_inOrder`: the narrow step of `UnitLifecycleReceivePreserve` is a `ReceiveStep` whenever some message
  reaches its agreement state, so the general results apply wherever the narrow ones did.
* `initiator_receives_reply_via_general`: the initiator's receipt of the responder's reply keeps the invariant and has
  the budget of `initiator_receives_reply_successor`, derived through the general step.
* `modelT3_keyPairEkVectorLen`, `modelT3_encapsulate2Len`: the two new laws hold in `Interp.modelT3`.
* `prepared_receive_keeps_invariant`, `establish_responder_keeps_invariant`: **every session `establish_responder`
  returns, at every identity, prekey store, initial message and source, is the session its inner `decrypt_ratchet`
  returned at the prepared session (`establish_responder_cases`), and for every prepared parts whose inner receive
  returned it, that session passes `Session::invariant` and meets the four ceilings when it refines a model session
  that is a `ReceiveStep` from the prepared model session.**  The prepared session's invariant, relation and room for
  one operation are the earlier modules'; the step is `decrypt_ratchet_keeps_invariant`.  Under
  `ReceiveInvariantLaws` and the four Braid agreements the prepared session's relation takes (`ErasureAgrees`,
  `KemLenAgrees`, `BraidHkdfAgrees`, `ZeroizingArrayRoundTrip`).
* `responder_first_frame_via_general`: the responder's session after the initiator's first frame, under the hypotheses
  of `responder_first_frame_successor` and the three laws, passes `Session::invariant` and meets the ceilings, derived
  through `establish_responder_keeps_invariant`.

## The laws and premises

`ReceiveInvariantLaws` bundles them, one named field each.

* **New, assumed: `KeyPairEkVectorLen`.**  Every key pair's `ek_vector` has `EK_VECTOR_LEN` bytes.  A statement about
  the opaque KEM wrapper, for every key pair (a restored one included).  Used at `KeysSampled` only, where the
  agreement starts streaming the vector.  Of the shipping wrapper it holds by reading (`ek_vector` copies the slice
  libcrux's `pk2` returns, `pk2_len()` bytes of the key pair, and `EK_VECTOR_LEN` is `pk2_len()`; the crate's test
  `the_sizes_are_the_specifications_sizes` checks one generated pair), which is not a proof.  The wrapper laws of `UnitKemWrapperModel` give the length for a generated key pair
  only (`LawGeneratedKeyPair`).
* **New, assumed: `Encapsulate2Len`.**  Every `ct2` the second half of encapsulation returns has `CT2_LEN` bytes.  A
  statement about the opaque KEM wrapper.  Used where the agreement finishes its encapsulation (`finish_encaps`, at
  `Ct1Sampled`, `EkReceivedCt1Sampled` and `Ct1Acknowledged`).  Of the shipping wrapper it holds by reading (the
  wrapper copies the value of libcrux's second ciphertext half; the crate's test
  `the_split_encapsulation_agrees_with_decapsulation` checks one call), which is not a proof.
* Both hold in `Interp.modelT3` (`modelT3_keyPairEkVectorLen`, `modelT3_encapsulate2Len`), the interpretation in which
  `UnitSatisfiabilityBraidAgreements` holds the six agreements and the laws `DivCeilValue` and `TruncatePrefix`.
  That shows each statement consistent with those; it says nothing about the shipping KEM.
* Existing records and laws: `KemCloneAgrees`, `DivCeilValue`, `TruncatePrefix`, the four length totality records
  (`HeaderLenTotal`, `EkVectorLenTotal`, `Ct1LenTotal`, `Ct2LenTotal`), `OptionEqU64Shape` and `DhPublicValid`; the
  oracle's `dhPublic` clause and the view's codec relation.
* The relation after the call and the model step are hypotheses of the step theorems: intermediate hypotheses, not
  discharged here.  The relation is what the decrypt refinement supplies; this module does not compose with it.
* `InOrderOut` is a restriction of scope about the Triple, the header and the agreement's output: the classical
  clauses of `InOrder` at the Triple, and `InOrder` at the Triple whose sparse ratchet has taken the output.  It says
  nothing of the result.

## Non-vacuity

* Every premise of `decrypt_keeps_invariant` holds together on the reply's run at `KeysSampled`
  (`initiator_receives_reply_via_general`), under the hypotheses of `initiator_receives_reply_successor` and the laws
  `TruncatePrefix`, `KeyPairEkVectorLen` and `Encapsulate2Len`.  That step has no agreement transition and no output.
* Every premise of `establish_responder_keeps_invariant` holds together on the first frame's run at `NoHeaderReceived`
  (`responder_first_frame_via_general`), under the hypotheses of `responder_first_frame_successor` and the same three
  laws; the agreement there takes one header chunk and stays.
* No run in the tree reaches a receive with an agreement transition or an output, so the general step's premises are
  not exhibited together there.  The agreement lemma (`braid_receive_keeps_invariant`) and the model lemmas are
  stated of every state and need no run.

## What it does not show

* A receive outside `InOrderOut`: one that uses a stored key, skips a message on either chain, or evicts from a full
  store (the out-of-order family).  So reordered, delayed or dropped delivery is not covered.
* That the relation after the call holds, or that the model's step is a `ReceiveStep`: hypotheses, supplied on the one
  run by the decrypt refinement and the model's own step.  No composition with the decrypt refinement here.
* A receive with an agreement transition or an output on any run.
* That the shipping KEM meets `KeyPairEkVectorLen`, `Encapsulate2Len` or `KemCloneAgrees`, that `usize::div_ceil` and
  `Vec::truncate` meet `DivCeilValue` and `TruncatePrefix`, or that the opaque `Option<u64>` comparison meets
  `OptionEqU64Shape`.
* That an `establish_responder` input's inner receive is a `ReceiveStep` (an initial frame that skips or names a
  stored key is outside it) or that its relation after the call holds, at any input other than the first frame's run.
* The budget at a session `Session::import` returns: `Session::invariant` does not give it, and the counters a
  restored session holds are its bytes'.
* That the ceilings are kept (false of the code, so the statements spend a budget).
* That `Session::invariant` says a session is reachable: it is a predicate on fields.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv)

namespace Tacenta.UnitLifecycleDecryptPreserve


/-! ## The header decoder at any number of chunks -/

/-- The indices of the first `j` chunks a decoder holds. -/
def prefixIdx (d : tacenta_erasure.Decoder) (j : Nat) : List Nat :=
  (d.«have».val.take j).map (fun c => c.index.val)

set_option maxHeartbeats 2000000 in
/-- **The loop of `Decoder::invariant` returns the size, `needed`, the chunks held and whether their indices are
pairwise distinct**, at any number of chunks held.  Hypothesis-free. -/
theorem inv_loop_general (d : tacenta_erasure.Decoder) :
    tacenta_erasure.Decoder.invariant_loop d (Array.repeat 8192#usize 0#u8) true 0#usize
      ⦃ fun r => r = (d.size, d.needed, d.«have»,
          decide ((d.«have».val.map (fun c => c.index.val)).Nodup)) ⦄ := by
  unfold tacenta_erasure.Decoder.invariant_loop
  apply loop.spec_decr_nat
    (measure := fun p => d.«have».val.length - p.2.2.val)
    (inv := fun p => p.2.2.val ≤ d.«have».val.length ∧
      p.2.1 = decide (prefixIdx d p.2.2.val).Nodup ∧
      ∀ w b : Nat, w < 8192 → b < 8 → ((p.1.val[w]!).val.testBit b ↔ 8 * w + b ∈ prefixIdx d p.2.2.val))
  · rintro ⟨sn, dd, j⟩ ⟨hj, hdd, hbits⟩
    simp only at hj hdd hbits ⊢
    unfold tacenta_erasure.Decoder.invariant_loop.body
    by_cases hlt : j < alloc.vec.Vec.len d.«have»
    · simp only [hlt, if_true]
      step*
      have hjl : j.val < d.«have».val.length := by scalar_tac
      have hidx : idx.val = c.index.val := by
        rw [idx_post]
        simp only [UScalar.cast_val_eq]
        have : c.index.val < 65536 := by scalar_tac
        rcases System.Platform.numBits_eq with h | h <;> simp [h] <;> omega
      have hcl : c.index.val < 65536 := by scalar_tac
      have hword : word.val = c.index.val / 8 := by rw [word_post, hidx]
      have hw : word.val < 8192 := by omega
      have hr : i2.val = c.index.val % 8 := by rw [i2_post, hidx]
      have hr8 : c.index.val % 8 < 8 := Nat.mod_lt _ (by decide)
      have hb : bit.val = 2 ^ (c.index.val % 8) := by
        rw [bit_post1, hr]
        generalize c.index.val % 8 = r at hr8 ⊢
        interval_cases r <;> simp [U8.size, U8.numBits]
      have hi3 : i3.val = (sn.val[word.val]!).val := by
        rw [i3_post, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hw)]; rfl
      have hpre : prefixIdx d (j.val + 1) = prefixIdx d j.val ++ [c.index.val] := by
        unfold prefixIdx
        rw [List.take_add_one, List.map_append, List.getElem?_eq_getElem hjl]
        simp [c_post]
      have hdec : 8 * (c.index.val / 8) + c.index.val % 8 = c.index.val := by omega
      have hin : (i4 != 0#u8) = decide (c.index.val ∈ prefixIdx d j.val) := by
        have key := hbits word.val (c.index.val % 8) hw hr8
        rw [hword, hdec, ← hword, ← hi3] at key
        have hi4 : i4.val = i3.val &&& 2 ^ (c.index.val % 8) := by
          rw [i4_post1, UScalar.val_and, hb]
        by_cases hm : c.index.val ∈ prefixIdx d j.val
        · have ht : i3.val.testBit (c.index.val % 8) = true := key.mpr hm
          have : i4.val ≠ 0 := by
            rw [hi4]; intro h0
            have := congrArg (fun x => Nat.testBit x (c.index.val % 8)) h0
            simp [Nat.testBit_and, Nat.testBit_two_pow_self, ht] at this
          have : i4 ≠ 0#u8 := fun h => this (by rw [h]; rfl)
          simp [hm, this]
        · have hf : i3.val.testBit (c.index.val % 8) = false := by
            cases h : i3.val.testBit (c.index.val % 8)
            · rfl
            · exact absurd (key.mp h) hm
          have : i4.val = 0 := by
            rw [hi4]; apply Nat.eq_of_testBit_eq; intro i
            simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
            by_cases hii : c.index.val % 8 = i
            · subst hii; simp [hf]
            · simp [hii]
          have : i4 = 0#u8 := UScalar.eq_of_val_eq (by simpa using this)
          simp [hm, this]
      rw [hin]
      have hbits' : ∀ (i5 : U8), i5.val = i3.val ||| bit.val → ∀ w b : Nat, w < 8192 → b < 8 →
          (((sn.set word i5).val[w]!).val.testBit b ↔ 8 * w + b ∈ prefixIdx d j.val ++ [c.index.val]) := by
        intro i5 hi5 w b hw' hb'
        rw [Array.set_val_eq, List.mem_append, List.mem_singleton]
        by_cases hww : w = word.val
        · subst hww
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by simpa using hw)]
          simp only [Option.getD_some, hi5, hb, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true]
          rw [← hbits word.val b hw hb', hi3]
          constructor
          · rintro (h | h)
            · exact Or.inl h
            · right; simp at h; rw [hword]; omega
          · rintro (h | h)
            · exact Or.inl h
            · right; rw [hword] at h; simp; omega
        · have hne : word.val ≠ w := fun h => hww h.symm
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getElem!_eq_getElem?_getD]
          rw [hbits w b hw' hb']
          constructor
          · exact Or.inl
          · rintro (h | h)
            · exact h
            · exfalso; apply hww; rw [hword]; omega
      by_cases hm : c.index.val ∈ prefixIdx d j.val
      · simp only [hm, decide_true, if_true, bind_tc_ok]
        step*
        rw [i6_post, hpre, a_post]
        refine ⟨by omega, by simp [List.nodup_append, hm], hbits' i5 (by rw [i5_post1, UScalar.val_or]), by omega⟩
      · simp only [hm, decide_false, Bool.false_eq_true, if_false, bind_tc_ok]
        step*
        rw [i6_post, hpre, a_post]
        refine ⟨by omega, by rw [hdd]; simp [List.nodup_append]; intro _ a ha h; exact hm (h ▸ ha), hbits' i5 (by rw [i5_post1, UScalar.val_or]),
          by omega⟩
    · simp only [hlt, if_false]
      have hjeq : j.val = d.«have».val.length := by
        have : ¬ j.val < (alloc.vec.Vec.len d.«have»).val := fun h => hlt (by scalar_tac)
        simp [alloc.vec.Vec.len] at this
        omega
      rw [hdd]
      simp only [prefixIdx, hjeq, List.take_length]
      step*
  · refine ⟨by simp, by simp [prefixIdx], ?_⟩
    intro w b hw hb
    have : ((Array.repeat 8192#usize 0#u8).val[w]!) = 0#u8 := by
      rw [Array.repeat_val, List.getElem!_eq_getElem?_getD, List.getElem?_replicate]
      simp [hw]
    rw [this]
    simp [prefixIdx]


/-- **`Decoder::invariant` is its four clauses**: `needed` is the chunk count of the size, at most `MAX_CODEWORDS`, the
chunks held are at most `needed`, and their indices are pairwise distinct.  Hypothesis-free. -/
theorem decoder_invariant_iff (d : tacenta_erasure.Decoder) :
    tacenta_erasure.Decoder.invariant d = ok true ↔
      tacenta_erasure.chunk_count d.size = ok d.needed ∧ d.needed.val ≤ 65536 ∧
        d.«have».val.length ≤ d.needed.val ∧ (d.«have».val.map (fun c => c.index.val)).Nodup := by
  obtain ⟨r, hr, hp⟩ := Std.WP.spec_imp_exists (inv_loop_general d)
  unfold tacenta_erasure.Decoder.invariant
  dsimp only
  rw [hr, hp]
  have hm : tacenta_erasure.MAX_CODEWORDS.val = 65536 := by simp [tacenta_erasure.MAX_CODEWORDS]
  rcases hcc : tacenta_erasure.chunk_count d.size with n | e | _
  · by_cases hn : d.needed = n
    · subst hn
      by_cases h1 : d.needed.val ≤ 65536 <;> by_cases h2 : d.«have».val.length ≤ d.needed.val <;>
        simp [hcc, hm, h1, h2, UScalar.le_equiv, alloc.vec.Vec.len]
    · have hn' : ¬ (n = d.needed) := fun h => hn h.symm
      simp [hcc, hn]
      intro h; cases h; exact absurd rfl hn
  · simp [hcc]
  · simp [hcc]

/-- **`add_chunk` keeps `Decoder::invariant`, the size and `needed`, at any number of chunks held.**  Hypothesis-free. -/
theorem add_chunk_keeps (d d' : tacenta_erasure.Decoder) (c : tacenta_erasure.Chunk) (r : Bool)
    (hinv : tacenta_erasure.Decoder.invariant d = ok true)
    (h : tacenta_erasure.Decoder.add_chunk d c = ok (r, d')) :
    tacenta_erasure.Decoder.invariant d' = ok true ∧ d'.size = d.size ∧ d'.needed = d.needed := by
  obtain ⟨r1, hr1, hheld, hs, hn, -⟩ := Std.WP.spec_imp_exists (Tacenta.UnitErasureRs.Decoder.D_add d c)
  rw [h] at hr1; cases hr1
  simp only at hheld hs hn
  obtain ⟨hcc, hle, hlen, hnd⟩ := (decoder_invariant_iff d).mp hinv
  refine ⟨(decoder_invariant_iff d').mpr ⟨by rw [hs, hn]; exact hcc, by rw [hn]; exact hle, ?_, ?_⟩, hs, hn⟩
  · have hl := congrArg List.length hheld
    simp only [Tacenta.UnitErasureRs.haveHeld, List.length_map] at hl
    rw [hl, hn]
    unfold Model.Erasure.Decoder.add
    simp only [List.length_map]
    split_ifs with h1 h2
    · simpa using hlen
    · simpa using hlen
    · simp only [List.length_append, List.length_map, List.length_singleton]
      simp only [not_le] at h1; omega
  · have hidx : d'.«have».val.map (fun c => c.index.val) = (Tacenta.UnitErasureRs.haveHeld d').map Prod.fst := by
      simp [Tacenta.UnitErasureRs.haveHeld]
    have hidx0 : d.«have».val.map (fun c => c.index.val) = (Tacenta.UnitErasureRs.haveHeld d).map Prod.fst := by
      simp [Tacenta.UnitErasureRs.haveHeld]
    rw [hidx, hheld]
    rw [hidx0] at hnd
    unfold Model.Erasure.Decoder.add
    simp only
    split_ifs with h1 h2
    · exact hnd
    · exact hnd
    · simp only [List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨hnd, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      intro hab
      apply h2
      simp only [List.any_eq_true, beq_iff_eq]
      rw [List.mem_map] at ha
      obtain ⟨x, hx, rfl⟩ := ha
      exact ⟨x, hx, by simpa using hab⟩


/-- Every chunk the model decoder reads off a held list of 32-byte codewords is 32 bytes.  Model only. -/
theorem model_chunk_len (d : Model.Erasure.Decoder) (hheld : ∀ h ∈ d.held, h.2.length = 32) (t : Nat) :
    (d.chunk t).length = 32 := by
  unfold Model.Erasure.Decoder.chunk
  rcases hf : d.held.find? (fun h => h.1 == t) with _ | h
  · simp only [hf]
    simp only [Model.Erasure.ofLanes, Model.Erasure.elementBytes, Model.Erasure.lanes, List.length_flatten,
      List.map_map, Function.comp_def, List.length_cons, List.length_nil]
    rfl
  · simp only [hf]
    exact hheld h (List.mem_of_find?_eq_some hf)

/-- **A decoded message is as long as the decoder was sized for**: when `Decoder::message` returns a value at a
decoder that passes `Decoder::invariant`, that value has `size` bytes.  Under `DivCeilValue` and the law
`TruncatePrefix`. -/
theorem decoder_message_len (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (htr : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix) (d : tacenta_erasure.Decoder)
    (hinv : tacenta_erasure.Decoder.invariant d = ok true) (v : alloc.vec.Vec Std.U8)
    (h : tacenta_erasure.Decoder.message d = ok (some v)) : v.val.length = d.size.val := by
  obtain ⟨hcc, hle, hlen, hnd⟩ := (decoder_invariant_iff d).mp hinv
  have hwf : Tacenta.UnitErasureRs.DWf d := ⟨hnd, hlen, hle⟩
  obtain ⟨r, hr, hp⟩ := Std.WP.spec_imp_exists (Tacenta.UnitErasureRs.D_message htr d hwf)
  rw [h] at hr; cases hr
  obtain ⟨n, hn, hnv⟩ := hdiv d.size
  have hneed : d.needed.val = (d.size.val + 31) / 32 := by
    rw [Tacenta.UnitSatisfiabilityErasure.chunk_count_eq] at hcc
    rw [hn] at hcc; cases hcc; exact hnv
  unfold Model.Erasure.Decoder.message at hp
  split_ifs at hp with hlt
  · simp at hp
  simp only [Option.map_some, Option.some.injEq] at hp
  have hvl : (Tacenta.UnitErasureRs.vbytes v).length = v.val.length := by
    simp [Tacenta.UnitErasureRs.vbytes]
  rw [← hvl, hp, List.length_take]
  have hflat : (((List.range d.needed.val).map
      (Model.Erasure.Decoder.chunk ⟨d.size.val, d.needed.val, Tacenta.UnitErasureRs.haveHeld d⟩)).flatten).length =
      32 * d.needed.val := by
    rw [List.length_flatten, List.map_map]
    have : ∀ t ∈ List.range d.needed.val, (List.length ∘ Model.Erasure.Decoder.chunk
        ⟨d.size.val, d.needed.val, Tacenta.UnitErasureRs.haveHeld d⟩) t = 32 := by
      intro t _
      simp only [Function.comp]
      apply model_chunk_len
      intro h hh
      simp only [Tacenta.UnitErasureRs.haveHeld, List.mem_map] at hh
      obtain ⟨c, -, rfl⟩ := hh
      simp [Tacenta.UnitErasureRs.cbytes]
    rw [List.map_congr_left this]
    simp [List.sum_replicate]; ring
  rw [hflat]
  omega


/-! ## `Braid::invariant` by parts, and `Braid::receive` at every state -/

/-- `Braid::invariant` at `HeaderSent`, by parts. -/
theorem inv_headerSent (c1 ev : Usize) (hc1 : tacenta_kem.CT1_LEN = ok c1) (hev : tacenta_kem.EK_VECTOR_LEN = ok ev)
    (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair) (d : tacenta_erasure.Decoder)
    (enc : tacenta_erasure.Encoder) :
    tacenta_braid.Braid.invariant ⟨.HeaderSent e a kp d enc⟩ = ok true ↔
      e ≥ 1#u64 ∧ tacenta_erasure.Decoder.invariant d = ok true ∧ d.size = c1 ∧
        tacenta_erasure.Encoder.invariant enc = ok true ∧ tacenta_braid.encoder_sized enc ev = ok true ∧
        tacenta_braid.key_pair_valid kp = ok true := by
  unfold tacenta_braid.Braid.invariant
  simp only [hc1, hev, bind_tc_ok, tacenta_braid.decoder_sized, tacenta_erasure.Decoder.impl.size]
  by_cases h1 : e ≥ 1#u64 <;> simp only [h1, if_true, if_false]
  · rcases hdi : tacenta_erasure.Decoder.invariant d with b | _ | _ <;> simp
    cases b <;> simp
    by_cases hs : d.size = c1 <;> simp [hs]
    rcases hei : tacenta_erasure.Encoder.invariant enc with b2 | _ | _ <;> simp
    cases b2 <;> simp
    rcases hes : tacenta_braid.encoder_sized enc ev with b3 | _ | _ <;> simp
    cases b3 <;> simp
  · simp


/-- `Braid::invariant` at `keysSampled`, by parts. -/
theorem inv_keysSampled (c1 ev c2 hl n96 n2 : Usize) (_hc1 : tacenta_kem.CT1_LEN = ok c1)
    (_hev : tacenta_kem.EK_VECTOR_LEN = ok ev) (_hc2 : tacenta_kem.CT2_LEN = ok c2) (hhl : tacenta_kem.HEADER_LEN = ok hl)
    (hn96 : hl + tacenta_braid.MAC_LEN = ok n96) (_hn2 : c2 + tacenta_braid.MAC_LEN = ok n2)
    (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) :
    tacenta_braid.Braid.invariant ⟨.KeysSampled e a kp enc⟩ = ok true ↔
      e ≥ 1#u64 ∧ tacenta_erasure.Encoder.invariant enc = ok true ∧ tacenta_braid.encoder_sized enc n96 = ok true ∧
        tacenta_braid.key_pair_valid kp = ok true := by
  unfold tacenta_braid.Braid.invariant
  simp only [hhl, hn96, bind_tc_ok]
  by_cases h1 : e ≥ 1#u64 <;> simp only [h1, if_true, if_false]
  swap
  · simp
  rcases hx1 : tacenta_erasure.Encoder.invariant enc with bhx1 | _ | _ <;> simp
  cases bhx1 <;> simp
  rcases hx2 : tacenta_braid.encoder_sized enc n96 with bhx2 | _ | _ <;> simp
  cases bhx2 <;> simp

/-- `Braid::invariant` at `ct1Received`, by parts. -/
theorem inv_ct1Received (c1 ev c2 hl n96 n2 : Usize) (hc1 : tacenta_kem.CT1_LEN = ok c1)
    (hev : tacenta_kem.EK_VECTOR_LEN = ok ev) (_hc2 : tacenta_kem.CT2_LEN = ok c2) (_hhl : tacenta_kem.HEADER_LEN = ok hl)
    (_hn96 : hl + tacenta_braid.MAC_LEN = ok n96) (_hn2 : c2 + tacenta_braid.MAC_LEN = ok n2)
    (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair) (ct1 : alloc.vec.Vec U8)
    (enc : tacenta_erasure.Encoder) :
    tacenta_braid.Braid.invariant ⟨.Ct1Received e a kp ct1 enc⟩ = ok true ↔
      e ≥ 1#u64 ∧ alloc.vec.Vec.len ct1 = c1 ∧ tacenta_erasure.Encoder.invariant enc = ok true ∧
        tacenta_braid.encoder_sized enc ev = ok true ∧ tacenta_braid.key_pair_valid kp = ok true := by
  unfold tacenta_braid.Braid.invariant
  simp only [hc1, hev, bind_tc_ok]
  by_cases h1 : e ≥ 1#u64 <;> simp only [h1, if_true, if_false]
  swap
  · simp
  by_cases hct1 : alloc.vec.Vec.len ct1 = c1 <;> simp [hct1]
  rcases hx1 : tacenta_erasure.Encoder.invariant enc with bhx1 | _ | _ <;> simp
  cases bhx1 <;> simp
  rcases hx2 : tacenta_braid.encoder_sized enc ev with bhx2 | _ | _ <;> simp
  cases bhx2 <;> simp

/-- `Braid::invariant` at `ekSentCt1Received`, by parts. -/
theorem inv_ekSentCt1Received (c1 ev c2 hl n96 n2 : Usize) (hc1 : tacenta_kem.CT1_LEN = ok c1)
    (_hev : tacenta_kem.EK_VECTOR_LEN = ok ev) (hc2 : tacenta_kem.CT2_LEN = ok c2) (_hhl : tacenta_kem.HEADER_LEN = ok hl)
    (_hn96 : hl + tacenta_braid.MAC_LEN = ok n96) (hn2 : c2 + tacenta_braid.MAC_LEN = ok n2)
    (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair) (ct1 : alloc.vec.Vec U8)
    (d : tacenta_erasure.Decoder) :
    tacenta_braid.Braid.invariant ⟨.EkSentCt1Received e a kp ct1 d⟩ = ok true ↔
      e ≥ 1#u64 ∧ alloc.vec.Vec.len ct1 = c1 ∧ tacenta_erasure.Decoder.invariant d = ok true ∧ d.size = n2 ∧
        tacenta_braid.key_pair_valid kp = ok true := by
  unfold tacenta_braid.Braid.invariant
  simp only [hc1, hc2, hn2, bind_tc_ok, tacenta_braid.decoder_sized,
    tacenta_erasure.Decoder.impl.size]
  by_cases h1 : e ≥ 1#u64 <;> simp only [h1, if_true, if_false]
  swap
  · simp
  by_cases hct1 : alloc.vec.Vec.len ct1 = c1 <;> simp [hct1]
  rcases hx1 : tacenta_erasure.Decoder.invariant d with bhx1 | _ | _ <;> simp
  cases bhx1 <;> simp
  by_cases hsd : d.size = n2 <;> simp [hsd]

/-- `Braid::invariant` at `noHeaderReceived`, by parts. -/
theorem inv_noHeaderReceived (c1 ev c2 hl n96 n2 : Usize) (_hc1 : tacenta_kem.CT1_LEN = ok c1)
    (_hev : tacenta_kem.EK_VECTOR_LEN = ok ev) (_hc2 : tacenta_kem.CT2_LEN = ok c2) (hhl : tacenta_kem.HEADER_LEN = ok hl)
    (hn96 : hl + tacenta_braid.MAC_LEN = ok n96) (_hn2 : c2 + tacenta_braid.MAC_LEN = ok n2)
    (e : U64) (a : tacenta_braid.Auth) (d : tacenta_erasure.Decoder) :
    tacenta_braid.Braid.invariant ⟨.NoHeaderReceived e a d⟩ = ok true ↔
      e ≥ 1#u64 ∧ tacenta_erasure.Decoder.invariant d = ok true ∧ d.size = n96 := by
  unfold tacenta_braid.Braid.invariant
  simp only [hhl, hn96, bind_tc_ok, tacenta_braid.decoder_sized,
    tacenta_erasure.Decoder.impl.size]
  by_cases h1 : e ≥ 1#u64 <;> simp only [h1, if_true, if_false]
  swap
  · simp
  rcases hx1 : tacenta_erasure.Decoder.invariant d with bhx1 | _ | _ <;> simp
  cases bhx1 <;> simp

/-- `Braid::invariant` at `headerReceived`, by parts. -/
theorem inv_headerReceived (c1 ev c2 hl n96 n2 : Usize) (_hc1 : tacenta_kem.CT1_LEN = ok c1)
    (hev : tacenta_kem.EK_VECTOR_LEN = ok ev) (_hc2 : tacenta_kem.CT2_LEN = ok c2) (hhl : tacenta_kem.HEADER_LEN = ok hl)
    (_hn96 : hl + tacenta_braid.MAC_LEN = ok n96) (_hn2 : c2 + tacenta_braid.MAC_LEN = ok n2)
    (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8) (d : tacenta_erasure.Decoder) :
    tacenta_braid.Braid.invariant ⟨.HeaderReceived e a hdr d⟩ = ok true ↔
      e ≥ 1#u64 ∧ alloc.vec.Vec.len hdr = hl ∧ tacenta_erasure.Decoder.invariant d = ok true ∧ d.size = ev := by
  unfold tacenta_braid.Braid.invariant
  simp only [hev, hhl, bind_tc_ok, tacenta_braid.decoder_sized,
    tacenta_erasure.Decoder.impl.size]
  by_cases h1 : e ≥ 1#u64 <;> simp only [h1, if_true, if_false]
  swap
  · simp
  by_cases hhdr : alloc.vec.Vec.len hdr = hl <;> simp [hhdr]
  rcases hx1 : tacenta_erasure.Decoder.invariant d with bhx1 | _ | _ <;> simp
  cases bhx1 <;> simp

/-- `Braid::invariant` at `ct1Sampled`, by parts. -/
theorem inv_ct1Sampled (c1 ev c2 hl n96 n2 : Usize) (hc1 : tacenta_kem.CT1_LEN = ok c1)
    (hev : tacenta_kem.EK_VECTOR_LEN = ok ev) (_hc2 : tacenta_kem.CT2_LEN = ok c2) (hhl : tacenta_kem.HEADER_LEN = ok hl)
    (_hn96 : hl + tacenta_braid.MAC_LEN = ok n96) (_hn2 : c2 + tacenta_braid.MAC_LEN = ok n2)
    (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8) (es : tacenta_kem.EncapsState)
    (ct1 : alloc.vec.Vec U8) (enc : tacenta_erasure.Encoder) (d : tacenta_erasure.Decoder) :
    tacenta_braid.Braid.invariant ⟨.Ct1Sampled e a hdr es ct1 enc d⟩ = ok true ↔
      e ≥ 1#u64 ∧ alloc.vec.Vec.len hdr = hl ∧ alloc.vec.Vec.len ct1 = c1 ∧
        tacenta_erasure.Encoder.invariant enc = ok true ∧ tacenta_braid.encoder_sized enc c1 = ok true ∧
        tacenta_erasure.Decoder.invariant d = ok true ∧ d.size = ev := by
  unfold tacenta_braid.Braid.invariant
  simp only [hc1, hev, hhl, bind_tc_ok, tacenta_braid.decoder_sized,
    tacenta_erasure.Decoder.impl.size]
  by_cases h1 : e ≥ 1#u64 <;> simp only [h1, if_true, if_false]
  swap
  · simp
  by_cases hhdr : alloc.vec.Vec.len hdr = hl <;> simp [hhdr]
  by_cases hct1 : alloc.vec.Vec.len ct1 = c1 <;> simp [hct1]
  rcases hx1 : tacenta_erasure.Encoder.invariant enc with bhx1 | _ | _ <;> simp
  cases bhx1 <;> simp
  rcases hx2 : tacenta_braid.encoder_sized enc c1 with bhx2 | _ | _ <;> simp
  cases bhx2 <;> simp
  rcases hx3 : tacenta_erasure.Decoder.invariant d with bhx3 | _ | _ <;> simp
  cases bhx3 <;> simp

/-- `Braid::invariant` at `ekReceivedCt1Sampled`, by parts. -/
theorem inv_ekReceivedCt1Sampled (c1 ev c2 hl n96 n2 : Usize) (hc1 : tacenta_kem.CT1_LEN = ok c1)
    (hev : tacenta_kem.EK_VECTOR_LEN = ok ev) (_hc2 : tacenta_kem.CT2_LEN = ok c2) (_hhl : tacenta_kem.HEADER_LEN = ok hl)
    (_hn96 : hl + tacenta_braid.MAC_LEN = ok n96) (_hn2 : c2 + tacenta_braid.MAC_LEN = ok n2)
    (e : U64) (a : tacenta_braid.Auth) (es : tacenta_kem.EncapsState) (ct1 ekv : alloc.vec.Vec U8)
    (enc : tacenta_erasure.Encoder) :
    tacenta_braid.Braid.invariant ⟨.EkReceivedCt1Sampled e a es ct1 ekv enc⟩ = ok true ↔
      e ≥ 1#u64 ∧ alloc.vec.Vec.len ct1 = c1 ∧ alloc.vec.Vec.len ekv = ev ∧
        tacenta_erasure.Encoder.invariant enc = ok true ∧ tacenta_braid.encoder_sized enc c1 = ok true := by
  unfold tacenta_braid.Braid.invariant
  simp only [hc1, hev, bind_tc_ok]
  by_cases h1 : e ≥ 1#u64 <;> simp only [h1, if_true, if_false]
  swap
  · simp
  by_cases hct1 : alloc.vec.Vec.len ct1 = c1 <;> simp [hct1]
  by_cases hekv : alloc.vec.Vec.len ekv = ev <;> simp [hekv]
  rcases hx1 : tacenta_erasure.Encoder.invariant enc with bhx1 | _ | _ <;> simp
  cases bhx1 <;> simp

/-- `Braid::invariant` at `ct1Acknowledged`, by parts. -/
theorem inv_ct1Acknowledged (c1 ev c2 hl n96 n2 : Usize) (hc1 : tacenta_kem.CT1_LEN = ok c1)
    (hev : tacenta_kem.EK_VECTOR_LEN = ok ev) (_hc2 : tacenta_kem.CT2_LEN = ok c2) (hhl : tacenta_kem.HEADER_LEN = ok hl)
    (_hn96 : hl + tacenta_braid.MAC_LEN = ok n96) (_hn2 : c2 + tacenta_braid.MAC_LEN = ok n2)
    (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8) (es : tacenta_kem.EncapsState)
    (ct1 : alloc.vec.Vec U8) (d : tacenta_erasure.Decoder) :
    tacenta_braid.Braid.invariant ⟨.Ct1Acknowledged e a hdr es ct1 d⟩ = ok true ↔
      e ≥ 1#u64 ∧ alloc.vec.Vec.len hdr = hl ∧ alloc.vec.Vec.len ct1 = c1 ∧
        tacenta_erasure.Decoder.invariant d = ok true ∧ d.size = ev := by
  unfold tacenta_braid.Braid.invariant
  simp only [hc1, hev, hhl, bind_tc_ok, tacenta_braid.decoder_sized,
    tacenta_erasure.Decoder.impl.size]
  by_cases h1 : e ≥ 1#u64 <;> simp only [h1, if_true, if_false]
  swap
  · simp
  by_cases hhdr : alloc.vec.Vec.len hdr = hl <;> simp [hhdr]
  by_cases hct1 : alloc.vec.Vec.len ct1 = c1 <;> simp [hct1]
  rcases hx1 : tacenta_erasure.Decoder.invariant d with bhx1 | _ | _ <;> simp
  cases bhx1 <;> simp

/-- `Braid::invariant` at `ct2Sampled`, by parts. -/
theorem inv_ct2Sampled (c1 ev c2 hl n96 n2 : Usize) (_hc1 : tacenta_kem.CT1_LEN = ok c1)
    (_hev : tacenta_kem.EK_VECTOR_LEN = ok ev) (hc2 : tacenta_kem.CT2_LEN = ok c2) (_hhl : tacenta_kem.HEADER_LEN = ok hl)
    (_hn96 : hl + tacenta_braid.MAC_LEN = ok n96) (hn2 : c2 + tacenta_braid.MAC_LEN = ok n2)
    (e : U64) (a : tacenta_braid.Auth) (enc : tacenta_erasure.Encoder) :
    tacenta_braid.Braid.invariant ⟨.Ct2Sampled e a enc⟩ = ok true ↔
      e ≥ 1#u64 ∧ tacenta_erasure.Encoder.invariant enc = ok true ∧ tacenta_braid.encoder_sized enc n2 = ok true := by
  unfold tacenta_braid.Braid.invariant
  simp only [hc2, hn2, bind_tc_ok]
  by_cases h1 : e ≥ 1#u64 <;> simp only [h1, if_true, if_false]
  swap
  · simp
  rcases hx1 : tacenta_erasure.Encoder.invariant enc with bhx1 | _ | _ <;> simp
  cases bhx1 <;> simp


/-- A fresh decoder for at most 4096 bytes passes `Decoder::invariant` and has the size it was made for.  Under
`DivCeilValue`. -/
theorem fresh_decoder (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (n : Usize) (hn : n.val ≤ 32 * 65536)
    (d : tacenta_erasure.Decoder) (h : tacenta_erasure.Decoder.new n = ok d) :
    tacenta_erasure.Decoder.invariant d = ok true ∧ d.size = n := by
  obtain ⟨d0, h0, hs, hneed, hv⟩ := Tacenta.UnitErasureRs.Glue.decoder_new_shape hdiv n
  rw [h] at h0; cases h0
  refine ⟨(decoder_invariant_iff _).mpr ⟨?_, by omega, by rw [hv]; simp, by rw [hv]; simp⟩, hs⟩
  obtain ⟨r, hr, hrv⟩ := hdiv n
  rw [Tacenta.UnitSatisfiabilityErasure.chunk_count_eq, hs, hr]
  congr 1; apply UScalar.eq_of_val_eq; rw [hrv, hneed]

/-- A fresh encoder (no chunk emitted) of a message of at most `32 · 65536` bytes passes `Encoder::invariant` and is
sized for the message.  Under `DivCeilValue`. -/
theorem fresh_encoder (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (s : Slice Std.U8)
    (hcap : (Tacenta.SessionUnitBraidT3.sliceOf s).length ≤ 32 * 65536)
    {enc : tacenta_erasure.Encoder} (hnew : tacenta_erasure.Encoder.new s = ok enc) :
    tacenta_erasure.Encoder.invariant enc = ok true ∧
      ∀ len : Usize, len.val = (Tacenta.SessionUnitBraidT3.sliceOf s).length →
        tacenta_braid.encoder_sized enc len = ok true := by
  obtain ⟨r0, hr0, hpost0⟩ := Std.WP.spec_imp_exists (Tacenta.UnitErasureRs.Encoder.E_new hdiv s)
  rw [hnew] at hr0; cases hr0
  obtain ⟨-, hex0, hstore⟩ := hpost0
  have hlen0 : enc.chunks.val.length = ((Tacenta.SessionUnitBraidT3.sliceOf s).length + 31) / 32 := by
    have := congrArg List.length hstore
    simp only [Tacenta.UnitErasureRs.storeBytes, List.length_map, List.length_take,
      Tacenta.UnitHeldKemWitness.chunks_length] at this
    omega
  refine ⟨?_, ?_⟩
  · unfold tacenta_erasure.Encoder.invariant
    have : alloc.vec.Vec.len enc.chunks ≤ tacenta_erasure.MAX_CODEWORDS := by
      have h1 := alloc.vec.Vec.len_val enc.chunks
      simp only [tacenta_erasure.MAX_CODEWORDS]
      scalar_tac
    simp [this, hex0]
  · intro len hlen
    obtain ⟨r, hr, hrv⟩ := hdiv len
    unfold tacenta_braid.encoder_sized tacenta_erasure.Encoder.needed
    simp only [Tacenta.UnitSatisfiabilityErasure.chunk_count_eq, hr, bind_tc_ok]
    have h1 := alloc.vec.Vec.len_val enc.chunks
    have : alloc.vec.Vec.len enc.chunks = r := by
      apply UScalar.eq_of_val_eq; rw [h1, hrv, hlen]; simpa [alloc.vec.Vec.length] using hlen0
    simp [this]


/-- The KEM length constants of the unit, with their sums with `MAC_LEN`: the values the Braid's invariant compares
lengths and sizes with.  Read off the existing totality records (`braidLens_of_totals`). -/
structure BraidLens where
  c1 : Usize
  ev : Usize
  c2 : Usize
  hl : Usize
  n96 : Usize
  n2 : Usize
  hc1 : tacenta_kem.CT1_LEN = ok c1
  hev : tacenta_kem.EK_VECTOR_LEN = ok ev
  hc2 : tacenta_kem.CT2_LEN = ok c2
  hhl : tacenta_kem.HEADER_LEN = ok hl
  hn96 : hl + tacenta_braid.MAC_LEN = ok n96
  hn2 : c2 + tacenta_braid.MAC_LEN = ok n2
  hn96v : n96.val = hl.val + 32
  hn2v : n2.val = c2.val + 32
  bc1 : c1.val ≤ 4096
  bev : ev.val ≤ 4096
  bc2 : c2.val ≤ 4096
  bhl : hl.val ≤ 4096

/-- A length of at most 4096 bytes plus `MAC_LEN` does not overflow and is 32 more. -/
theorem add_mac (x : Usize) (hx : x.val ≤ 4096) : ∃ n : Usize, x + tacenta_braid.MAC_LEN = ok n ∧ n.val = x.val + 32 := by
  have : tacenta_braid.MAC_LEN.val = 32 := by simp [tacenta_braid.MAC_LEN]
  have hmx := Tacenta.UnitSatisfiabilityBraidAgreements.usize_max_ge 4128 (by norm_num)
  obtain ⟨n, hn, hnv⟩ := Std.WP.spec_imp_exists (Usize.add_spec (x := x) (y := tacenta_braid.MAC_LEN) (by scalar_tac))
  exact ⟨n, hn, by scalar_tac⟩

/-- The lengths exist under the four existing totality records. -/
theorem braidLens_of_totals (hh : Tacenta.SessionUnitBraidT1.HeaderLenTotal)
    (he : Tacenta.SessionUnitBraidT1.EkVectorLenTotal) (h1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (h2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) : Nonempty BraidLens := by
  obtain ⟨hl, hhl, bhl⟩ := hh
  obtain ⟨ev, hev, bev⟩ := he
  obtain ⟨c1, hc1, bc1⟩ := h1
  obtain ⟨c2, hc2, bc2⟩ := h2
  obtain ⟨n96, hn96, hn96v⟩ := add_mac hl bhl
  obtain ⟨n2, hn2, hn2v⟩ := add_mac c2 bc2
  exact ⟨⟨c1, ev, c2, hl, n96, n2, hc1, hev, hc2, hhl, hn96, hn2, hn96v, hn2v, bc1, bev, bc2, bhl⟩⟩


/-- **`step_receive` at `HeaderSent` keeps `Braid::invariant`**: it stays (the decoder grows by one chunk or not) or
moves to `Ct1Received` with the completed `ct1`, whose length is the decoder's size. -/
theorem step_receive_headerSent (L : BraidLens) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (htr : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix) (self : tacenta_braid.Braid)
    (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair) (d : tacenta_erasure.Decoder)
    (enc : tacenta_erasure.Encoder) (msg : tacenta_braid.Msg) (out : Option tacenta_braid.Output)
    (next : tacenta_braid.State)
    (hinv : tacenta_braid.Braid.invariant ⟨.HeaderSent e a kp d enc⟩ = ok true)
    (h : tacenta_braid.Braid.step_receive self (.HeaderSent e a kp d enc) msg = ok (out, next)) :
    tacenta_braid.Braid.invariant ⟨next⟩ = ok true := by
  have hinv0 := hinv
  rw [inv_headerSent L.c1 L.ev L.hc1 L.hev] at hinv
  obtain ⟨he, hdi, hds, hei, hes, hkv⟩ := hinv
  unfold tacenta_braid.Braid.step_receive at h
  simp only [tacenta_braid.State.epoch, bind_tc_ok] at h
  split_ifs at h with hep
  swap
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  obtain ⟨b, -, h⟩ := bind_eq_ok_inv h
  cases b
  · simp only [Bool.false_eq_true, if_false, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [if_true] at h
  rcases hmd : msg.data with _ | c
  · simp only [hmd, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [hmd] at h
  obtain ⟨⟨r, d1⟩, hadd, h⟩ := bind_eq_ok_inv h
  obtain ⟨hdi1, hs1, -⟩ := add_chunk_keeps d d1 c r hdi hadd
  obtain ⟨o, hmsg, h⟩ := bind_eq_ok_inv h
  rcases o with _ | ct1
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact (inv_headerSent L.c1 L.ev L.hc1 L.hev _ _ _ _ _).mpr ⟨he, hdi1, by rw [hs1, hds], hei, hes, hkv⟩
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    have hl := decoder_message_len hdiv htr d1 hdi1 ct1 hmsg
    refine (inv_ct1Received L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2 _ _ _ _ _).mpr
      ⟨he, ?_, hei, hes, hkv⟩
    apply UScalar.eq_of_val_eq
    rw [alloc.vec.Vec.len_val]
    simp only [alloc.vec.Vec.length]
    rw [hl, hs1, hds]


/-- **Every key pair's `ek_vector` has `EK_VECTOR_LEN` bytes.**  An assumed law about the opaque KEM wrapper: the
shipping `ek_vector` is `inc::pk2(&self.0).to_vec()`, a copy of libcrux's fixed-size second public-key part, whose size
`EK_VECTOR_LEN` is defined as (`inc::pk2_len()`), by reading; the crate's own unit test checks it on a generated key
pair. -/
def KeyPairEkVectorLen : Prop :=
  ∀ (kp : tacenta_kem.IncrementalKeyPair) (v : alloc.vec.Vec Std.U8),
    tacenta_kem.IncrementalKeyPair.ek_vector kp = ok v →
      ∃ n : Usize, tacenta_kem.EK_VECTOR_LEN = ok n ∧ v.length = n.val

/-- **Every `ct2` the second half of encapsulation returns has `CT2_LEN` bytes.**  An assumed law about the opaque KEM
wrapper: the shipping `encapsulate2` returns `inc::encapsulate2(s, pk2).value.to_vec()`, a copy of libcrux's fixed-size
second ciphertext half (`CT2_LEN` = 160), by reading; the crate's own unit test checks it on one encapsulation. -/
def Encapsulate2Len : Prop :=
  ∀ (es : tacenta_kem.EncapsState) (s : Slice Std.U8) (c : alloc.vec.Vec Std.U8),
    tacenta_kem.encapsulate2 es s = ok (core.result.Result.Ok c) →
      ∃ n : Usize, tacenta_kem.CT2_LEN = ok n ∧ c.length = n.val

/-- `Failed` passes `Braid::invariant`. -/
theorem failed_inv : tacenta_braid.Braid.invariant ⟨.Failed⟩ = ok true := rfl

/-- **`finish_encaps` builds a state that passes `Braid::invariant`**: `Ct2Sampled` with a fresh encoder of `ct2`
and its MAC, or `Failed`.  Under `Encapsulate2Len` and `DivCeilValue`. -/
theorem finish_encaps_inv (L : BraidLens) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (henc2 : Encapsulate2Len) (e : U64) (a : tacenta_braid.Auth) (es : tacenta_kem.EncapsState)
    (ct1 ekv : Slice Std.U8) (st : tacenta_braid.State) (he : e ≥ 1#u64)
    (h : tacenta_braid.finish_encaps e a es ct1 ekv = ok st) : tacenta_braid.Braid.invariant ⟨st⟩ = ok true := by
  unfold tacenta_braid.finish_encaps at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_inv h
  rcases r with c | err
  · simp only at h
    obtain ⟨mac, -, h⟩ := bind_eq_ok_inv h
    obtain ⟨s1, hs1, h⟩ := bind_eq_ok_inv h
    obtain ⟨c1, hext, h⟩ := bind_eq_ok_inv h
    obtain ⟨enc, hnew, h⟩ := bind_eq_ok_inv h
    simp only [ok.injEq] at h
    subst h
    obtain ⟨n, hn, hcl⟩ := henc2 es ekv c hr
    rw [L.hc2] at hn; cases hn
    have hlen : (Tacenta.SessionUnitBraidT3.sliceOf (alloc.vec.Vec.deref c1)).length = L.n2.val := by
      have hx := Tacenta.UnitLifecycleEncryptPreserve.extend_ok_val hext
      simp only [lift, ok.injEq] at hs1
      subst hs1
      simp only [Tacenta.SessionUnitBraidT3.sliceOf, alloc.vec.Vec.deref, List.length_map, hx, List.length_append]
      simp only [alloc.vec.Vec.length] at hcl
      rw [hcl, L.hn2v]
      simp [Array.to_slice]
    obtain ⟨hei, hes⟩ := fresh_encoder hdiv _ (by rw [hlen, L.hn2v]; have := L.bc2; omega) hnew
    exact (inv_ct2Sampled L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2 _ _ _).mpr
      ⟨he, hei, hes L.n2 hlen.symm⟩
  · simp only [ok.injEq] at h; subst h; exact failed_inv

/-- **`step_receive` at `Ct2Sampled` keeps `Braid::invariant`**: it stays, moves to `KeysUnsampled` one epoch on, or
fails. -/
theorem step_receive_ct2Sampled (_L : BraidLens) (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth)
    (enc : tacenta_erasure.Encoder) (msg : tacenta_braid.Msg) (out : Option tacenta_braid.Output)
    (next : tacenta_braid.State)
    (hinv : tacenta_braid.Braid.invariant ⟨.Ct2Sampled e a enc⟩ = ok true)
    (h : tacenta_braid.Braid.step_receive self (.Ct2Sampled e a enc) msg = ok (out, next)) :
    tacenta_braid.Braid.invariant ⟨next⟩ = ok true := by
  have hinv0 := hinv
  unfold tacenta_braid.Braid.step_receive at h
  simp only [tacenta_braid.State.epoch, bind_tc_ok] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_inv h
  rcases o with _ | ne
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact failed_inv
  simp only at h
  split_ifs at h with hmax hep
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact failed_inv
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    have hne : ne.val = e.val + 1 := by
      simp only [lift, ok.injEq] at ho
      have := U64.checked_add_bv_spec e 1#u64
      rw [ho] at this
      simpa using this.2.1
    unfold tacenta_braid.Braid.invariant
    simp only
    have : ne ≥ 1#u64 := by scalar_tac
    simp [this]
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0


/-- **`step_receive` at `KeysSampled` keeps `Braid::invariant`**: it stays, or moves to `HeaderSent` with a fresh
`ct1` decoder holding the chunk and a fresh encoder of the key pair's `ek_vector`.  Under `KeyPairEkVectorLen`. -/
theorem step_receive_keysSampled (L : BraidLens) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (hekl : KeyPairEkVectorLen) (self : tacenta_braid.Braid)
    (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder)
    (msg : tacenta_braid.Msg) (out : Option tacenta_braid.Output) (next : tacenta_braid.State)
    (hinv : tacenta_braid.Braid.invariant ⟨.KeysSampled e a kp enc⟩ = ok true)
    (h : tacenta_braid.Braid.step_receive self (.KeysSampled e a kp enc) msg = ok (out, next)) :
    tacenta_braid.Braid.invariant ⟨next⟩ = ok true := by
  have hinv0 := hinv
  rw [inv_keysSampled L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2] at hinv
  obtain ⟨he, -, -, hkv⟩ := hinv
  unfold tacenta_braid.Braid.step_receive at h
  simp only [tacenta_braid.State.epoch, bind_tc_ok] at h
  split_ifs at h with hep
  swap
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  obtain ⟨b, -, h⟩ := bind_eq_ok_inv h
  cases b
  · simp only [Bool.false_eq_true, if_false, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [if_true] at h
  rcases hmd : msg.data with _ | c
  · simp only [hmd, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [hmd] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_inv h
  rw [L.hc1] at hi; cases hi
  obtain ⟨d0, hd0, h⟩ := bind_eq_ok_inv h
  obtain ⟨hdi0, hs0⟩ := fresh_decoder hdiv L.c1 (by have := L.bc1; omega) d0 hd0
  obtain ⟨⟨r, d1⟩, hadd, h⟩ := bind_eq_ok_inv h
  obtain ⟨hdi1, hs1, -⟩ := add_chunk_keeps d0 d1 c r hdi0 hadd
  obtain ⟨v, hv, h⟩ := bind_eq_ok_inv h
  obtain ⟨enc1, hnew, h⟩ := bind_eq_ok_inv h
  simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  obtain ⟨n, hn, hvl⟩ := hekl kp v hv
  rw [L.hev] at hn; cases hn
  have hlen : (Tacenta.SessionUnitBraidT3.sliceOf (alloc.vec.Vec.deref v)).length = L.ev.val := by
    simp only [Tacenta.SessionUnitBraidT3.sliceOf, alloc.vec.Vec.deref, List.length_map]
    simpa [alloc.vec.Vec.length] using hvl
  obtain ⟨hei, hes⟩ := fresh_encoder hdiv _ (by rw [hlen]; have := L.bev; omega) hnew
  exact (inv_headerSent L.c1 L.ev L.hc1 L.hev _ _ _ _ _).mpr ⟨he, hdi1, by rw [hs1, hs0], hei, hes L.ev hlen.symm, hkv⟩

/-- **`step_receive` at `Ct1Received` keeps `Braid::invariant`**: it stays, or moves to `EkSentCt1Received` with a
fresh `ct2` decoder holding the chunk. -/
theorem step_receive_ct1Received (L : BraidLens) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair)
    (ct1 : alloc.vec.Vec U8) (enc : tacenta_erasure.Encoder)
    (msg : tacenta_braid.Msg) (out : Option tacenta_braid.Output) (next : tacenta_braid.State)
    (hinv : tacenta_braid.Braid.invariant ⟨.Ct1Received e a kp ct1 enc⟩ = ok true)
    (h : tacenta_braid.Braid.step_receive self (.Ct1Received e a kp ct1 enc) msg = ok (out, next)) :
    tacenta_braid.Braid.invariant ⟨next⟩ = ok true := by
  have hinv0 := hinv
  rw [inv_ct1Received L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2] at hinv
  obtain ⟨he, hl1, -, -, hkv⟩ := hinv
  unfold tacenta_braid.Braid.step_receive at h
  simp only [tacenta_braid.State.epoch, bind_tc_ok] at h
  split_ifs at h with hep
  swap
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  obtain ⟨b, -, h⟩ := bind_eq_ok_inv h
  cases b
  · simp only [Bool.false_eq_true, if_false, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [if_true] at h
  rcases hmd : msg.data with _ | c
  · simp only [hmd, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [hmd] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_inv h
  rw [L.hc2] at hi; cases hi
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_inv h
  rw [L.hn2] at hi1; cases hi1
  obtain ⟨d0, hd0, h⟩ := bind_eq_ok_inv h
  obtain ⟨hdi0, hs0⟩ := fresh_decoder hdiv L.n2 (by have := L.bc2; have := L.hn2v; omega) d0 hd0
  obtain ⟨⟨r, d1⟩, hadd, h⟩ := bind_eq_ok_inv h
  obtain ⟨hdi1, hs1, -⟩ := add_chunk_keeps d0 d1 c r hdi0 hadd
  change ok (none, tacenta_braid.State.EkSentCt1Received e a kp ct1 d1) = ok (out, next) at h
  simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (inv_ekSentCt1Received L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2 _ _ _ _ _).mpr ⟨he, hl1, hdi1, by rw [hs1, hs0], hkv⟩


/-- **`step_receive` at `NoHeaderReceived` keeps `Braid::invariant`**: it stays (the decoder grows by one chunk or
not), fails, or moves to `HeaderReceived` with the first `HEADER_LEN` bytes of the completed message and a fresh
`ek_vector` decoder. -/
theorem step_receive_noHeaderReceived (L : BraidLens) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth) (d : tacenta_erasure.Decoder)
    (msg : tacenta_braid.Msg) (out : Option tacenta_braid.Output) (next : tacenta_braid.State)
    (hinv : tacenta_braid.Braid.invariant ⟨.NoHeaderReceived e a d⟩ = ok true)
    (h : tacenta_braid.Braid.step_receive self (.NoHeaderReceived e a d) msg = ok (out, next)) :
    tacenta_braid.Braid.invariant ⟨next⟩ = ok true := by
  have hinv0 := hinv
  rw [inv_noHeaderReceived L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2] at hinv
  obtain ⟨he, hdi, hds⟩ := hinv
  unfold tacenta_braid.Braid.step_receive at h
  simp only [tacenta_braid.State.epoch, bind_tc_ok] at h
  split_ifs at h with hep
  swap
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  obtain ⟨b, -, h⟩ := bind_eq_ok_inv h
  cases b
  · simp only [Bool.false_eq_true, if_false, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [if_true] at h
  rcases hmd : msg.data with _ | c
  · simp only [hmd, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [hmd] at h
  obtain ⟨⟨r, d1⟩, hadd, h⟩ := bind_eq_ok_inv h
  obtain ⟨hdi1, hs1, -⟩ := add_chunk_keeps d d1 c r hdi hadd
  obtain ⟨o, hmsg, h⟩ := bind_eq_ok_inv h
  rcases o with _ | framed
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact (inv_noHeaderReceived L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2 _ _ _).mpr ⟨he, hdi1, by rw [hs1, hds]⟩
  simp only at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_inv h
  rw [L.hhl] at hi1; cases hi1
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_inv h
  rw [L.hn96] at hi2; cases hi2
  split_ifs at h with hne
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact failed_inv
  have hfl : framed.val.length = L.n96.val := by simpa using hne
  obtain ⟨⟨hdr, mac⟩, hsplit, h⟩ := bind_eq_ok_inv h
  obtain ⟨r0, hr0, hl0, -, -, -⟩ := Std.WP.spec_imp_exists
    (core.slice.Slice.split_at.spec (alloc.vec.Vec.deref framed) L.hl (by
      simp only [Slice.length, alloc.vec.Vec.deref]
      have := L.hn96v
      scalar_tac))
  rw [hsplit] at hr0; cases hr0
  obtain ⟨mac1, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨s1, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨b1, -, h⟩ := bind_eq_ok_inv h
  cases b1
  · simp only [Bool.false_eq_true, if_false, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact failed_inv
  simp only [if_true] at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_inv h
  obtain ⟨r1, hr1, hp1⟩ := Std.WP.spec_imp_exists
    (alloc.slice.Slice.to_vec_spec core.clone.CloneU8 hdr (fun _ _ => rfl))
  rw [hv] at hr1; cases hr1
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok_inv h
  rw [L.hev] at hi3; cases hi3
  obtain ⟨d2, hd2, h⟩ := bind_eq_ok_inv h
  obtain ⟨hdi2, hs2⟩ := fresh_decoder hdiv L.ev (by have := L.bev; omega) d2 hd2
  simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  refine (inv_headerReceived L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2 _ _ _ _).mpr ⟨he, ?_, hdi2, hs2⟩
  apply UScalar.eq_of_val_eq
  rw [alloc.vec.Vec.len_val, ← hp1]
  simpa [Slice.length] using hl0


/-- **`step_receive` at `EkSentCt1Received` keeps `Braid::invariant`**: it stays (the `ct2` decoder grows by one chunk
or not), fails (wrong length, the epoch at its ceiling, decapsulation refused, the MAC refused), or moves to
`NoHeaderReceived` one epoch on with a fresh header decoder (transition (5)). -/
theorem step_receive_ekSentCt1Received (L : BraidLens) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair)
    (ct1 : alloc.vec.Vec U8) (d : tacenta_erasure.Decoder)
    (msg : tacenta_braid.Msg) (out : Option tacenta_braid.Output) (next : tacenta_braid.State)
    (hinv : tacenta_braid.Braid.invariant ⟨.EkSentCt1Received e a kp ct1 d⟩ = ok true)
    (h : tacenta_braid.Braid.step_receive self (.EkSentCt1Received e a kp ct1 d) msg = ok (out, next)) :
    tacenta_braid.Braid.invariant ⟨next⟩ = ok true := by
  have hinv0 := hinv
  rw [inv_ekSentCt1Received L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2] at hinv
  obtain ⟨he, hl1, hdi, hds, hkv⟩ := hinv
  unfold tacenta_braid.Braid.step_receive at h
  simp only [tacenta_braid.State.epoch, bind_tc_ok] at h
  split_ifs at h with hep
  swap
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  obtain ⟨b, -, h⟩ := bind_eq_ok_inv h
  cases b
  · simp only [Bool.false_eq_true, if_false, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [if_true] at h
  rcases hmd : msg.data with _ | c
  · simp only [hmd, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [hmd] at h
  obtain ⟨⟨r, d1⟩, hadd, h⟩ := bind_eq_ok_inv h
  obtain ⟨hdi1, hs1, -⟩ := add_chunk_keeps d d1 c r hdi hadd
  obtain ⟨o, hmsg, h⟩ := bind_eq_ok_inv h
  rcases o with _ | framed
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact (inv_ekSentCt1Received L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2 _ _ _ _ _).mpr ⟨he, hl1, hdi1, by rw [hs1, hds], hkv⟩
  simp only at h
  obtain ⟨i1, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨i2, -, h⟩ := bind_eq_ok_inv h
  split_ifs at h with hne
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact failed_inv
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_inv h
  rcases o1 with _ | ne
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact failed_inv
  have hne1 : ne.val = e.val + 1 := by
    simp only [lift, ok.injEq] at ho1
    have := U64.checked_add_bv_spec e 1#u64
    rw [ho1] at this
    simpa using this.2.1
  simp only at h
  split_ifs at h with hmax
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact failed_inv
  repeat' first
    | (simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact failed_inv)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_inv h)
    | split at h
  simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  obtain ⟨hv, n, needed, hhv, hn, hnv, hcc, rfl⟩ :=
    Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_ok _ ‹tacenta_braid.hdr_decoder = ok _›
  rw [L.hhl] at hhv; cases hhv
  rw [L.hn96] at hn; cases hn
  refine (inv_noHeaderReceived L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2 _ _ _).mpr ⟨by scalar_tac, ?_, rfl⟩
  apply Tacenta.UnitLifecycleEstablishResponder.fresh_decoder_invariant _ _ hcc
  obtain ⟨r2, hr2, hr2v⟩ := hdiv L.n96
  rw [Tacenta.UnitSatisfiabilityErasure.chunk_count_eq, hr2] at hcc; cases hcc
  have := L.hn96v; have := L.bhl; omega


/-- **`step_receive` at `Ct1Sampled` keeps `Braid::invariant`**: it stays, moves to `Ct1Acknowledged` (transition
(8)), to `EkReceivedCt1Sampled` with the completed `ek_vector` (transition (10)), through `finish_encaps`
(transition (9)), or fails. -/
theorem step_receive_ct1Sampled (L : BraidLens) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (htr : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix) (henc2 : Encapsulate2Len)
    (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8)
    (es : tacenta_kem.EncapsState) (ct1 : alloc.vec.Vec U8) (enc : tacenta_erasure.Encoder)
    (d : tacenta_erasure.Decoder)
    (msg : tacenta_braid.Msg) (out : Option tacenta_braid.Output) (next : tacenta_braid.State)
    (hinv : tacenta_braid.Braid.invariant ⟨.Ct1Sampled e a hdr es ct1 enc d⟩ = ok true)
    (h : tacenta_braid.Braid.step_receive self (.Ct1Sampled e a hdr es ct1 enc d) msg = ok (out, next)) :
    tacenta_braid.Braid.invariant ⟨next⟩ = ok true := by
  have hinv0 := hinv
  rw [inv_ct1Sampled L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2] at hinv
  obtain ⟨he, hlh, hl1, hei, hes, hdi, hds⟩ := hinv
  unfold tacenta_braid.Braid.step_receive at h
  simp only [tacenta_braid.State.epoch, bind_tc_ok] at h
  obtain ⟨rel, -, h⟩ := bind_eq_ok_inv h
  cases rel
  · simp only [Bool.false_eq_true, if_false, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [if_true] at h
  rcases hmd : msg.data with _ | c
  · simp only [hmd, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [hmd] at h
  obtain ⟨acked, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨⟨r, d1⟩, hadd, h⟩ := bind_eq_ok_inv h
  obtain ⟨hdi1, hs1, -⟩ := add_chunk_keeps d d1 c r hdi hadd
  obtain ⟨o, hmsg, h⟩ := bind_eq_ok_inv h
  rcases o with _ | ekv
  · cases acked
    · simp only [Bool.false_eq_true, if_false, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      exact (inv_ct1Sampled L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2 _ _ _ _ _ _ _).mpr ⟨he, hlh, hl1, hei, hes, hdi1, by rw [hs1, hds]⟩
    · simp only [if_true, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      exact (inv_ct1Acknowledged L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2 _ _ _ _ _ _).mpr ⟨he, hlh, hl1, hdi1, by rw [hs1, hds]⟩
  simp only at h
  obtain ⟨vb, -, h⟩ := bind_eq_ok_inv h
  cases vb
  · simp only [Bool.false_eq_true, if_false, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact failed_inv
  simp only [if_true] at h
  cases acked
  · simp only [Bool.false_eq_true, if_false, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    have hlv := decoder_message_len hdiv htr d1 hdi1 ekv hmsg
    refine (inv_ekReceivedCt1Sampled L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2 _ _ _ _ _ _).mpr ⟨he, hl1, ?_, hei, hes⟩
    apply UScalar.eq_of_val_eq
    rw [alloc.vec.Vec.len_val]
    simp only [alloc.vec.Vec.length]
    rw [hlv, hs1, hds]
  · simp only [if_true] at h
    obtain ⟨s4, hfin, h⟩ := bind_eq_ok_inv h
    simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact finish_encaps_inv L hdiv henc2 e a es _ _ s4 he hfin

/-- **`step_receive` at `EkReceivedCt1Sampled` keeps `Braid::invariant`**: it stays or goes through `finish_encaps`
(transition (12)). -/
theorem step_receive_ekReceivedCt1Sampled (L : BraidLens) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (henc2 : Encapsulate2Len) (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth)
    (es : tacenta_kem.EncapsState) (ct1 ekv : alloc.vec.Vec U8) (enc : tacenta_erasure.Encoder)
    (msg : tacenta_braid.Msg) (out : Option tacenta_braid.Output) (next : tacenta_braid.State)
    (hinv : tacenta_braid.Braid.invariant ⟨.EkReceivedCt1Sampled e a es ct1 ekv enc⟩ = ok true)
    (h : tacenta_braid.Braid.step_receive self (.EkReceivedCt1Sampled e a es ct1 ekv enc) msg = ok (out, next)) :
    tacenta_braid.Braid.invariant ⟨next⟩ = ok true := by
  have hinv0 := hinv
  rw [inv_ekReceivedCt1Sampled L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2] at hinv
  obtain ⟨he, -, -, -, -⟩ := hinv
  unfold tacenta_braid.Braid.step_receive at h
  simp only [tacenta_braid.State.epoch, bind_tc_ok] at h
  split_ifs at h with hep
  swap
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  obtain ⟨b, -, h⟩ := bind_eq_ok_inv h
  cases b
  · simp only [Bool.false_eq_true, if_false, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [if_true] at h
  obtain ⟨s4, hfin, h⟩ := bind_eq_ok_inv h
  simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact finish_encaps_inv L hdiv henc2 e a es _ _ s4 he hfin

/-- **`step_receive` at `Ct1Acknowledged` keeps `Braid::invariant`**: it stays (the decoder grows by one chunk or
not), goes through `finish_encaps` (transition (11)), or fails. -/
theorem step_receive_ct1Acknowledged (L : BraidLens) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (henc2 : Encapsulate2Len) (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth)
    (hdr : alloc.vec.Vec U8) (es : tacenta_kem.EncapsState) (ct1 : alloc.vec.Vec U8) (d : tacenta_erasure.Decoder)
    (msg : tacenta_braid.Msg) (out : Option tacenta_braid.Output) (next : tacenta_braid.State)
    (hinv : tacenta_braid.Braid.invariant ⟨.Ct1Acknowledged e a hdr es ct1 d⟩ = ok true)
    (h : tacenta_braid.Braid.step_receive self (.Ct1Acknowledged e a hdr es ct1 d) msg = ok (out, next)) :
    tacenta_braid.Braid.invariant ⟨next⟩ = ok true := by
  have hinv0 := hinv
  rw [inv_ct1Acknowledged L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2] at hinv
  obtain ⟨he, hlh, hl1, hdi, hds⟩ := hinv
  unfold tacenta_braid.Braid.step_receive at h
  simp only [tacenta_braid.State.epoch, bind_tc_ok] at h
  split_ifs at h with hep
  swap
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  obtain ⟨b, -, h⟩ := bind_eq_ok_inv h
  cases b
  · simp only [Bool.false_eq_true, if_false, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [if_true] at h
  rcases hmd : msg.data with _ | c
  · simp only [hmd, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hinv0
  simp only [hmd] at h
  obtain ⟨⟨r, d1⟩, hadd, h⟩ := bind_eq_ok_inv h
  obtain ⟨hdi1, hs1, -⟩ := add_chunk_keeps d d1 c r hdi hadd
  obtain ⟨o, hmsg, h⟩ := bind_eq_ok_inv h
  rcases o with _ | ekv
  · simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact (inv_ct1Acknowledged L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2 _ _ _ _ _ _).mpr ⟨he, hlh, hl1, hdi1, by rw [hs1, hds]⟩
  simp only at h
  obtain ⟨vb, -, h⟩ := bind_eq_ok_inv h
  cases vb
  · simp only [Bool.false_eq_true, if_false, ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact failed_inv
  simp only [if_true] at h
  obtain ⟨s4, hfin, h⟩ := bind_eq_ok_inv h
  simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact finish_encaps_inv L hdiv henc2 e a es _ _ s4 he hfin


open Tacenta.UnitLifecycleSendPreserve (vec_clone_u8 encoder_clone_eq decoder_clone_eq key_pair_valid_clone) in
/-- **A state's clone passes `Braid::invariant` when the state does**: the clone is the state up to its key pair and
encapsulation state, and the key pair's clone passes `key_pair_valid` (`KemCloneAgrees`). -/
theorem clone_inv (L : BraidLens) (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees) (st st' : tacenta_braid.State)
    (hc : tacenta_braid.State.Insts.CoreCloneClone.clone st = ok st')
    (hinv : tacenta_braid.Braid.invariant ⟨st⟩ = ok true) : tacenta_braid.Braid.invariant ⟨st'⟩ = ok true := by
  cases st <;>
    simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, lift, core.clone.impls.CloneU64.clone,
      bind_tc_ok, Tacenta.UnitLifecycleResponderReply.auth_clone_eq, encoder_clone_eq, decoder_clone_eq,
      vec_clone_u8, ok.injEq] at hc
  case KeysSampled e a kp enc =>
    rcases hk : tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp with kp' | _ | _ <;>
      simp only [hk, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hc
    subst hc
    rw [inv_keysSampled L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2] at hinv ⊢
    exact ⟨hinv.1, hinv.2.1, hinv.2.2.1, key_pair_valid_clone hkcl hk hinv.2.2.2⟩
  case HeaderSent e a kp d enc =>
    rcases hk : tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp with kp' | _ | _ <;>
      simp only [hk, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hc
    subst hc
    rw [inv_headerSent L.c1 L.ev L.hc1 L.hev] at hinv ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hinv
    exact ⟨h1, h2, h3, h4, h5, key_pair_valid_clone hkcl hk h6⟩
  case Ct1Received e a kp ct1 enc =>
    rcases hk : tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp with kp' | _ | _ <;>
      simp only [hk, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hc
    subst hc
    rw [inv_ct1Received L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2] at hinv ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
    exact ⟨h1, h2, h3, h4, key_pair_valid_clone hkcl hk h5⟩
  case EkSentCt1Received e a kp ct1 d =>
    rcases hk : tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp with kp' | _ | _ <;>
      simp only [hk, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hc
    subst hc
    rw [inv_ekSentCt1Received L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2] at hinv ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
    exact ⟨h1, h2, h3, h4, key_pair_valid_clone hkcl hk h5⟩
  case Ct1Sampled e a hdr es ct1 enc d =>
    rcases hk : tacenta_kem.EncapsState.Insts.CoreCloneClone.clone es with es' | _ | _ <;>
      simp only [hk, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hc
    subst hc
    rw [inv_ct1Sampled L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2] at hinv ⊢
    exact hinv
  case EkReceivedCt1Sampled e a es ct1 ekv enc =>
    rcases hk : tacenta_kem.EncapsState.Insts.CoreCloneClone.clone es with es' | _ | _ <;>
      simp only [hk, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hc
    subst hc
    rw [inv_ekReceivedCt1Sampled L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2] at hinv ⊢
    exact hinv
  case Ct1Acknowledged e a hdr es ct1 d =>
    rcases hk : tacenta_kem.EncapsState.Insts.CoreCloneClone.clone es with es' | _ | _ <;>
      simp only [hk, bind_tc_ok, bind_tc_fail, bind_tc_div, ok.injEq, reduceCtorEq] at hc
    subst hc
    rw [inv_ct1Acknowledged L.c1 L.ev L.c2 L.hl L.n96 L.n2 L.hc1 L.hev L.hc2 L.hhl L.hn96 L.hn2] at hinv ⊢
    exact hinv
  all_goals (subst hc; exact hinv)


/-- **`step_receive` keeps `Braid::invariant` at every state.** -/
theorem step_receive_inv (L : BraidLens) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (htr : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix) (hekl : KeyPairEkVectorLen)
    (henc2 : Encapsulate2Len) (self : tacenta_braid.Braid) (st : tacenta_braid.State) (msg : tacenta_braid.Msg)
    (out : Option tacenta_braid.Output) (next : tacenta_braid.State)
    (hinv : tacenta_braid.Braid.invariant ⟨st⟩ = ok true)
    (h : tacenta_braid.Braid.step_receive self st msg = ok (out, next)) :
    tacenta_braid.Braid.invariant ⟨next⟩ = ok true := by
  cases st with
  | KeysUnsampled e a =>
    simp only [tacenta_braid.Braid.step_receive, tacenta_braid.State.epoch, bind_tc_ok, ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact hinv
  | KeysSampled e a kp enc => exact step_receive_keysSampled L hdiv hekl self e a kp enc msg out next hinv h
  | HeaderSent e a kp d enc => exact step_receive_headerSent L hdiv htr self e a kp d enc msg out next hinv h
  | Ct1Received e a kp ct1 enc => exact step_receive_ct1Received L hdiv self e a kp ct1 enc msg out next hinv h
  | EkSentCt1Received e a kp ct1 d =>
    exact step_receive_ekSentCt1Received L hdiv self e a kp ct1 d msg out next hinv h
  | NoHeaderReceived e a d => exact step_receive_noHeaderReceived L hdiv self e a d msg out next hinv h
  | HeaderReceived e a hdr d =>
    simp only [tacenta_braid.Braid.step_receive, tacenta_braid.State.epoch, bind_tc_ok, ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact hinv
  | Ct1Sampled e a hdr es ct1 enc d =>
    exact step_receive_ct1Sampled L hdiv htr henc2 self e a hdr es ct1 enc d msg out next hinv h
  | EkReceivedCt1Sampled e a es ct1 ekv enc =>
    exact step_receive_ekReceivedCt1Sampled L hdiv henc2 self e a es ct1 ekv enc msg out next hinv h
  | Ct1Acknowledged e a hdr es ct1 d =>
    exact step_receive_ct1Acknowledged L hdiv henc2 self e a hdr es ct1 d msg out next hinv h
  | Ct2Sampled e a enc => exact step_receive_ct2Sampled L self e a enc msg out next hinv h
  | Failed =>
    simp only [tacenta_braid.Braid.step_receive, tacenta_braid.State.epoch, bind_tc_ok, ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact failed_inv

/-- **`Braid::receive` keeps `Braid::invariant` at every state**: every successful receive, of every message, from a
Braid that passes the invariant returns a candidate that passes it, whatever the transition (the twelve states' arms,
the `Failed` arms included).  Under `KemCloneAgrees`, `DivCeilValue`, `TruncatePrefix`, the four length totality
records (through `BraidLens`), and two assumed length laws, `KeyPairEkVectorLen` (used at `KeysSampled`) and
`Encapsulate2Len` (used where the agreement finishes its encapsulation). -/
theorem braid_receive_keeps_invariant (L : BraidLens) (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees)
    (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (htr : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix) (hekl : KeyPairEkVectorLen)
    (henc2 : Encapsulate2Len) (b : tacenta_braid.Braid) (msg : tacenta_braid.Msg) (x : U64)
    (y : Option tacenta_braid.Output) (bc : tacenta_braid.Braid)
    (hinv : tacenta_braid.Braid.invariant b = ok true)
    (h : tacenta_braid.Braid.receive b msg = ok (x, y, bc)) : tacenta_braid.Braid.invariant bc = ok true := by
  unfold tacenta_braid.Braid.receive at h
  obtain ⟨st', hc, h⟩ := bind_eq_ok_inv h
  obtain ⟨⟨out, next⟩, hstep, h⟩ := bind_eq_ok_inv h
  have hbc : bc = ⟨next⟩ := by
    rcases out with _ | o
    · obtain ⟨i, -, h⟩ := bind_eq_ok_inv h
      simp only [ok.injEq, Prod.mk.injEq] at h
      exact h.2.2.symm
    · obtain ⟨o1, -, h⟩ := bind_eq_ok_inv h
      simp only [ok.injEq, Prod.mk.injEq] at h
      exact h.2.2.symm
  rw [hbc]
  exact step_receive_inv L hdiv htr hekl henc2 _ st' msg out next (clone_inv L hkcl b.state st' hc hinv) hstep


/-! ## The model agreement's clause (b) and role across a receive -/

/-- The model state's tag, as `Braid::state_tag` numbers the code's states. -/
def modelTag : Model.Braid.BraidState → Nat
  | .keysUnsampled .. => 0 | .keysSampled .. => 1 | .headerSent .. => 2 | .ct1Received .. => 3
  | .ekSentCt1Received .. => 4 | .noHeaderReceived .. => 5 | .headerReceived .. => 6 | .ct1Sampled .. => 7
  | .ekReceivedCt1Sampled .. => 8 | .ct1Acknowledged .. => 9 | .ct2Sampled .. => 10 | .failed => 11

/-- Whether the model state sends a header this epoch (`Braid::is_initiator`'s first reading). -/
def modelSendsHeader : Model.Braid.BraidState → Bool
  | .keysUnsampled .. | .keysSampled .. | .headerSent .. | .ct1Received .. | .ekSentCt1Received .. => true
  | _ => false

/-- `Braid::is_initiator`, read on the model state. -/
def modelIsInit (st : Model.Braid.BraidState) : Option Bool :=
  match st with
  | .failed => none
  | _ => some (if modelSendsHeader st then st.epoch % 2 = 1 else ¬ (st.epoch % 2 = 1))

/-- **Clause (b) of `Session::structural_invariant`, read on the model**: a failed agreement is exempt; at tags 7 to
10 the sparse epoch is the agreement's; elsewhere it is one behind. -/
def ModelClauseB (sp : Nat) (st : Model.Braid.BraidState) : Prop :=
  st = .failed ∨ ((7 ≤ modelTag st ∧ modelTag st ≤ 10) → sp = st.epoch) ∧
    (¬ (7 ≤ modelTag st ∧ modelTag st ≤ 10) → sp + 1 = st.epoch)

set_option maxHeartbeats 2000000 in
/-- **The model agreement's receive keeps clause (b) and the role, in step with the sparse epoch**: the next state is
failed, or reads the same role, and clause (b) holds there at the sparse epoch the receive's output moves the sparse
ratchet to (unchanged without an output; the output's epoch with one, which is one past the old sparse epoch).
Model only. -/
theorem receive_clauses (K : Model.Braid.Kem) (st : Model.Braid.BraidState) (msg : Model.Braid.Msg) (sp : Nat)
    (hcb : ModelClauseB sp st) :
    ((Model.Braid.receive K st msg).2.2 = .failed ∨
        modelIsInit (Model.Braid.receive K st msg).2.2 = modelIsInit st) ∧
      ((Model.Braid.receive K st msg).2.1 = none → ModelClauseB sp (Model.Braid.receive K st msg).2.2) ∧
      (∀ o, (Model.Braid.receive K st msg).2.1 = some o →
        o.keyEpoch = sp + 1 ∧ ModelClauseB o.keyEpoch (Model.Braid.receive K st msg).2.2) := by
  rcases hcb with rfl | ⟨hf, hn⟩
  · simp [Model.Braid.receive, ModelClauseB]
  cases st <;> simp only [modelTag] at hf hn <;> simp only [Model.Braid.receive] <;>
    (repeat' split) <;>
    (try simp only [Model.Braid.finishEncaps]) <;> (try split) <;>
    (try simp_all [ModelClauseB, modelTag, modelIsInit, modelSendsHeader, Model.Braid.BraidState.epoch]) <;>
    (try omega)


/-! ## The model Triple's receive with an agreement output, in order -/

open Tacenta.UnitLifecycleReceivePreserve (InOrder modelTripleInv_receive_inOrder triple_receive_parts
  ratchet_receive_frame sparseTail_ok spqr_receive_inOrder)
open Tacenta.UnitLifecycleEncryptPreserve (modelSpqrInv_advance advance_ok_parts spqr_send_counters InChain)
open Tacenta.UnitTripleInvModel
open Tacenta.UnitLifecycleSendPreserve (ModelCounterRoom CounterRoom counterRoom_iff_model session_invariant_iff)

/-- The sparse state a receive with an agreement output reads its chain from: the advanced one, or the state itself
without an output. -/
def advancedOf (st : Model.SparseRatchet.State) (out : Option Model.SparseRatchet.Output) :
    Option Model.SparseRatchet.State :=
  match Model.SparseRatchet.maybeAdvanceReceiveDetailed st out with
  | .ok st1 => some st1
  | .error _ => none

/-- **The in-order scope of a receive with or without an agreement output**: the classical clauses of `InOrder` at
the Triple, and `InOrder` of the Triple whose sparse ratchet has taken the output (every such state).  A restriction
about the state, the header and the output only. -/
def InOrderOut (m : Model.Triple.State) (h : Model.Triple.Header) (out : Option Model.SparseRatchet.Output) : Prop :=
  (Model.Ratchet.trySkipped m.classical h.dr = none ∧
    (m.classical.dhrPub = some h.dr.dh → h.dr.n ≤ m.classical.nr) ∧
    (m.classical.dhrPub ≠ some h.dr.dh →
      (m.classical.ckr = none ∨ m.classical.dhrPub = none ∨ h.dr.pn ≤ m.classical.nr) ∧ h.dr.n = 0)) ∧
  ∀ st1, advancedOf m.postQuantum out = some st1 → InOrder { classical := m.classical, postQuantum := st1 } h

/-- A Triple receive with an agreement output is the advance and a receive without one.  Model only. -/
theorem triple_receive_advance {m m' : Model.Triple.State} {hdr : Model.Triple.Header} {dr ds np k : Model.State.Key}
    {out : Option Model.SparseRatchet.Output}
    (hs : Model.Triple.receiveDetailed m hdr dr ds np out = .ok (m', k)) :
    ∃ st1, advancedOf m.postQuantum out = some st1 ∧
      Model.Triple.receiveDetailed { classical := m.classical, postQuantum := st1 } hdr dr ds np none = .ok (m', k) := by
  unfold Model.Triple.receiveDetailed at hs ⊢
  rcases hc : Model.Ratchet.receiveDetailed m.classical hdr.dr dr ds np with _ | ⟨c, mkc⟩
  · rw [hc] at hs; simp at hs
  rw [hc] at hs
  simp only at hs ⊢
  unfold Model.SparseRatchet.receiveDetailed at hs
  rcases ha : Model.SparseRatchet.maybeAdvanceReceiveDetailed m.postQuantum out with r | st1
  · rw [ha] at hs; simp at hs
  rw [ha] at hs
  refine ⟨st1, by simp [advancedOf, ha], ?_⟩
  unfold Model.SparseRatchet.receiveDetailed
  simp only [Model.SparseRatchet.maybeAdvanceReceiveDetailed, Model.SparseRatchet.maybeAdvanceDetailed, hc]
  exact hs

/-- The advance a receive takes keeps `ModelTripleInv` of the Triple it acts on.  Model only. -/
theorem modelTripleInv_advanced {m : Model.Triple.State} {out : Option Model.SparseRatchet.Output}
    {st1 : Model.SparseRatchet.State} (h : ModelTripleInv m) (ha : advancedOf m.postQuantum out = some st1) :
    ModelTripleInv { classical := m.classical, postQuantum := st1 } ∧ st1.direction = m.postQuantum.direction ∧
      (out = none → st1 = m.postQuantum) ∧ (∀ o, out = some o → st1.epoch = o.keyEpoch ∧
        o.keyEpoch = m.postQuantum.epoch + 1) := by
  obtain ⟨hr, hq, hroles⟩ := h
  unfold advancedOf Model.SparseRatchet.maybeAdvanceReceiveDetailed Model.SparseRatchet.maybeAdvanceDetailed at ha
  rcases out with _ | o
  · simp only [Option.some.injEq] at ha
    subst ha
    exact ⟨⟨hr, hq, hroles⟩, rfl, fun _ => rfl, fun _ h => by cases h⟩
  · simp only at ha
    rcases hadv : Model.SparseRatchet.advanceDetailed m.postQuantum o with e | st2
    · rw [hadv] at ha; simp at ha
    rw [hadv] at ha
    simp only [Option.some.injEq] at ha
    subst ha
    obtain ⟨he, -, hep, hdir, -⟩ := advance_ok_parts hadv
    refine ⟨⟨hr, modelSpqrInv_advance hq hadv, ?_⟩, hdir, fun h => (by cases h), ?_⟩
    · unfold ModelRolesAgree at hroles ⊢
      simp only at hroles ⊢
      rw [hdir]; exact hroles
    · intro o' ho'; cases ho'; exact ⟨hep, he⟩

/-- **The model Triple's receive keeps `ModelTripleInv`, with or without an agreement output**, in the in-order scope
of the advanced state, given a canonical header key and, on a Diffie-Hellman step, a canonical candidate key.  Model
only. -/
theorem modelTripleInv_receive_out {m m' : Model.Triple.State} {hdr : Model.Triple.Header}
    {dr ds np k : Model.State.Key} {out : Option Model.SparseRatchet.Output} (h : ModelTripleInv m)
    (hhdr : Model.Messages.canonicalKey hdr.dr.dh = true)
    (hnp : m.classical.dhrPub ≠ some hdr.dr.dh → Model.Messages.canonicalKey np = true)
    (hord : InOrderOut m hdr out)
    (hs : Model.Triple.receiveDetailed m hdr dr ds np out = .ok (m', k)) : ModelTripleInv m' := by
  obtain ⟨st1, ha, hs1⟩ := triple_receive_advance hs
  obtain ⟨h1, -, -, -⟩ := modelTripleInv_advanced h ha
  exact modelTripleInv_receive_inOrder h1 hhdr hnp (hord.2 st1 ha) hs1


open Tacenta.UnitLifecycleReceivePreserve (classicalTail sparseTail classicalTail_err sparseTail_err
  ratchet_receive_inOrder decode_dh_canonical) in
/-- **Under the in-order scope with an output, the session's receive with eviction is the Triple's receive**: no
refusal of the Triple's receive there is a full store.  Model only. -/
theorem receiveWithEviction_inOrderOut {m : Model.Triple.State} {c : Model.CompositeHeader.Composite}
    {hdr : Model.Triple.Header} {dr ds np : Model.State.Key} {out : Option Model.SparseRatchet.Output}
    {r : Model.Triple.State × Model.State.Key} (hord : InOrderOut m hdr out)
    (h : Model.Lifecycle.receiveWithEviction m c hdr dr ds np out = .ok r) :
    Model.Triple.receiveDetailed m hdr dr ds np out = .ok r := by
  unfold Model.Lifecycle.receiveWithEviction at h
  rcases hd : Model.Triple.receiveDetailed m hdr dr ds np out with reason | r'
  · exfalso
    rw [hd] at h
    simp only at h
    have hnf : Model.Lifecycle.fullStore reason = none := by
      unfold Model.Triple.receiveDetailed at hd
      obtain ⟨⟨hts, hsame, hnew⟩, hsp⟩ := hord
      rcases hcr : Model.Ratchet.receiveDetailed m.classical hdr.dr dr ds np with rc | ⟨c1, k1⟩
      · rw [hcr] at hd
        simp only [Except.error.injEq] at hd
        subst hd
        rw [ratchet_receive_inOrder hts hsame hnew] at hcr
        have := classicalTail_err hcr
        cases rc <;> simp_all [Model.Lifecycle.fullStore]
      · rw [hcr] at hd
        simp only at hd
        unfold Model.SparseRatchet.receiveDetailed at hd
        rcases ha : Model.SparseRatchet.maybeAdvanceReceiveDetailed m.postQuantum out with ra | st1
        · rw [ha] at hd
          simp only [Except.error.injEq] at hd
          subst hd
          unfold Model.SparseRatchet.maybeAdvanceReceiveDetailed at ha
          split at ha
          · simp at ha
          · simp only [Except.error.injEq] at ha
            subst ha
            rename_i reason _
            cases reason <;> simp [Model.Lifecycle.fullStore, Model.SparseRatchet.receiveRefusalOfSend]
        · rw [ha] at hd
          have hio := hsp st1 (by simp [advancedOf, ha])
          have hsp1 : Model.SparseRatchet.receiveDetailed st1 hdr.epoch none hdr.pqN = sparseTail st1 hdr.epoch hdr.pqN :=
            spqr_receive_inOrder hio.noStoredSparse hio.sparseNext
          unfold Model.SparseRatchet.receiveDetailed at hsp1
          simp only [Model.SparseRatchet.maybeAdvanceReceiveDetailed, Model.SparseRatchet.maybeAdvanceDetailed] at hsp1
          simp only at hd
          rw [hsp1] at hd
          rcases hp : sparseTail st1 hdr.epoch hdr.pqN with rp | ⟨q1, k2⟩
          · rw [hp] at hd
            simp only [Except.error.injEq] at hd
            subst hd
            have := sparseTail_err hp
            cases rp <;> simp_all [Model.Lifecycle.fullStore]
          · rw [hp] at hd; simp at hd
    rw [hnf] at h
    simp at h
  · rw [hd] at h
    simpa using h


/-- **A receive step at any agreement state**: the session as it was (Triple, ratchet key and agreement), or the
agreement's next state for some message, with the Triple the model Triple's receive (with the agreement's output, if
any) of a header in the in-order scope whose key is canonical, with the oracle's public key of the draw `cand` as the
candidate, and the ratchet key replaced by `cand` exactly when the sending key changed.  What the model's
`decryptRatchet` does on an in-order frame (`decryptRatchet_receiveStep`). -/
def ReceiveStep (oracle : Model.Lifecycle.Oracle) (m m' : Model.Lifecycle.Session) : Prop :=
  (m'.triple = m.triple ∧ m'.ratchetPrivate = m.ratchetPrivate ∧ m'.braid = m.braid) ∨
    ∃ (msgB : Model.Braid.Msg) (hdr : Model.Triple.Header) (dr ds cand mk : Model.State.Key),
      m'.braid = (Model.Braid.receive oracle.braidKem m.braid msgB).2.2 ∧
      InOrderOut m.triple hdr (Model.Lifecycle.sparseOutputOf (Model.Braid.receive oracle.braidKem m.braid msgB).2.1) ∧
      Model.Messages.canonicalKey hdr.dr.dh = true ∧
      Model.Triple.receiveDetailed m.triple hdr dr ds (oracle.dhPublic cand)
        (Model.Lifecycle.sparseOutputOf (Model.Braid.receive oracle.braidKem m.braid msgB).2.1) = .ok (m'.triple, mk) ∧
      m'.ratchetPrivate = if m'.triple.classical.dhsPub == m.triple.classical.dhsPub then m.ratchetPrivate else cand

/-- **The model's `decryptRatchet` of a frame in the in-order scope is a `ReceiveStep`**, at every agreement state:
for every view, oracle, session and message whose every decoded header is in order (with the agreement's output) for
the session's Triple.  Model only. -/
theorem decryptRatchet_receiveStep (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (m : Model.Lifecycle.Session) (msg : Model.Lifecycle.Bytes)
    (hord : ∀ c ct, Model.CompositeHeader.decodeDetailed msg = .ok (c, ct) →
      InOrderOut m.triple (Model.Lifecycle.tripleHeaderOf c) (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.1)) :
    ReceiveStep oracle m (Model.Lifecycle.decryptRatchet view oracle m msg).session := by
  have stay : ReceiveStep oracle m m := Or.inl ⟨rfl, rfl, rfl⟩
  unfold Model.Lifecycle.decryptRatchet
  by_cases hf : Model.Lifecycle.agreementFailed m = true
  · simp only [hf, if_true]; exact stay
  simp only [hf, Bool.false_eq_true, if_false]
  rcases hd : Model.CompositeHeader.decodeDetailed msg with reason | ⟨c, ct⟩
  · exact stay
  have hio := hord c ct hd
  have hcan : Model.Messages.canonicalKey c.dh = true :=
    Tacenta.UnitLifecycleReceivePreserve.decode_dh_canonical
      ((Model.CompositeHeader.decodeDetailed_ok_iff _ _).mp hd)
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
  rcases hr : Model.Lifecycle.receiveWithEviction m.triple c (Model.Lifecycle.tripleHeaderOf c) dr ds
      (oracle.dhPublic cand) (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.1)
      with reason | ⟨t', mk⟩
  · exact stay
  simp only
  split
  · exact stay
  · exact Or.inr ⟨_, Model.Lifecycle.tripleHeaderOf c, dr, ds, cand, mk, rfl, hio, hcan,
      receiveWithEviction_inOrderOut hio hr, rfl⟩

/-- **The model's public `decrypt` of a message the dispatch passes on is a `ReceiveStep`** under the conditions of
`decryptRatchet_receiveStep` on the message the dispatch returns.  Model only. -/
theorem decrypt_receiveStep (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (m : Model.Lifecycle.Session) (msg inner : Model.Lifecycle.Bytes)
    (hdisp : Model.Lifecycle.dispatchDecrypt oracle m msg = .ok inner)
    (hord : ∀ c ct, Model.CompositeHeader.decodeDetailed inner = .ok (c, ct) →
      InOrderOut m.triple (Model.Lifecycle.tripleHeaderOf c) (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.1)) :
    ReceiveStep oracle m (Model.Lifecycle.decrypt view oracle m msg).session := by
  have h := decryptRatchet_receiveStep view oracle m inner hord
  unfold Model.Lifecycle.decrypt
  rw [hdisp]
  simp only
  split
  · exact h
  · exact h


set_option maxHeartbeats 2000000 in
/-- The model agreement's receive moves the epoch by at most one.  Model only. -/
theorem receive_epoch_le (K : Model.Braid.Kem) (st : Model.Braid.BraidState) (msg : Model.Braid.Msg) :
    (Model.Braid.receive K st msg).2.2.epoch ≤ st.epoch + 1 := by
  cases st <;> simp only [Model.Braid.receive] <;> (repeat' split) <;>
    (try simp only [Model.Braid.finishEncaps]) <;> (try split) <;>
    simp_all [Model.Braid.BraidState.epoch]

/-- **A receive step spends at most one unit of the budget, at every agreement state**: the clock rises by at most
one, the sparse epoch and the agreement's epoch by at most one, and every chain counter is at most one, or at most one
more than a counter before.  Model only. -/
theorem modelCounterRoom_receive_any (oracle : Model.Lifecycle.Oracle) {m m' : Model.Lifecycle.Session} (k : Nat)
    (hstep : ReceiveStep oracle m m') (h : ModelCounterRoom m (k + 1)) : ModelCounterRoom m' k := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases hstep with ⟨htr, -, hb⟩ | ⟨msgB, hdr, dr, ds, cand, mk, hb, hord, -, hs, -⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [htr]; omega
    · rw [htr]; omega
    · rw [htr]; intro p hp ch hch; have := h3 p hp ch hch; omega
    · rw [hb]; omega
  have hk : k < 2 ^ 32 := by
    have : Std.U32.max = 2 ^ 32 - 1 := by simp [Std.U32.max_eq]
    omega
  have hU : Std.U64.max = 2 ^ 64 - 1 := by simp [Std.U64.max_eq]
  obtain ⟨st1, ha, hs1⟩ := triple_receive_advance hs
  have hio := hord.2 st1 ha
  obtain ⟨⟨k1, hc⟩, ⟨k2, hp⟩⟩ := triple_receive_parts hio hs1
  obtain ⟨-, -, hev, -⟩ := ratchet_receive_frame hio.noStoredClassical hio.sameChain hio.newChain hc
  obtain ⟨cs, ch, hmem, hrecv, hn, -, hq⟩ := sparseTail_ok hp
  -- the advance: epoch at most one more; chains old or new at counter 0
  have hadv : st1.epoch ≤ m.triple.postQuantum.epoch + 1 ∧ ∀ p ∈ st1.chains, ∀ c, InChain p c →
      c.n = 0 ∨ ∃ p0 ∈ m.triple.postQuantum.chains, InChain p0 c := by
    unfold advancedOf Model.SparseRatchet.maybeAdvanceReceiveDetailed Model.SparseRatchet.maybeAdvanceDetailed at ha
    rcases hout : Model.Lifecycle.sparseOutputOf (Model.Braid.receive oracle.braidKem m.braid msgB).2.1 with _ | o
    · rw [hout] at ha; simp only [Option.some.injEq] at ha; subst ha
      exact ⟨by omega, fun p hp c hc => Or.inr ⟨p, hp, hc⟩⟩
    · rw [hout] at ha
      simp only at ha
      rcases hadv : Model.SparseRatchet.advanceDetailed m.triple.postQuantum o with e | st2
      · rw [hadv] at ha; simp at ha
      rw [hadv] at ha; simp only [Option.some.injEq] at ha; subst ha
      obtain ⟨he, -, hep, -, -, c0, hc0, hch⟩ := advance_ok_parts hadv
      refine ⟨by omega, fun p hp c hc => ?_⟩
      rw [hch, List.mem_filter] at hp
      rcases Tacenta.UnitLifecycleSendPreserve.mem_sent_chains hp.1 with ⟨hp', -⟩ | rfl
      · exact Or.inr ⟨p, hp', hc⟩
      · exact Or.inl (hc0 c hc)
  obtain ⟨hep1, hch1⟩ := hadv
  refine ⟨by simp only at hev; omega, ?_, ?_, ?_⟩
  · rw [hq]; simp only [Model.SparseRatchet.setChains]; omega
  · rw [hq]
    simp only [Model.SparseRatchet.setChains]
    intro p hp' c hcp
    rcases Tacenta.UnitLifecycleSendPreserve.mem_sent_chains hp' with ⟨hp'', -⟩ | rfl
    · rcases hch1 p hp'' c hcp with h0 | ⟨p0, hp0, hin0⟩
      · omega
      · have := h3 p0 hp0 c hin0; omega
    · rcases hcp with hs' | hr'
      · rcases hch1 _ hmem c (Or.inl hs') with h0 | ⟨p0, hp0, hin0⟩
        · omega
        · have := h3 p0 hp0 c hin0; omega
      · simp only [Option.some.injEq] at hr'
        subst hr'
        rcases hch1 _ hmem ch (Or.inr hrecv) with h0 | ⟨p0, hp0, hin0⟩
        · simp only; omega
        · have := h3 p0 hp0 ch hin0; simp only; omega
  · rw [hb]
    have := receive_epoch_le oracle.braidKem m.braid msgB
    omega


/-- **What a receive step leaves of the Triple's direction and sending key, and of clause (b) and the role**: the
direction is kept; a changed sending key is the oracle's public key of the new ratchet key; clause (b) holds after the
step at the new sparse epoch when it held before; and the agreement after is failed or reads the same role.  Model
only. -/
theorem step_frame_any (oracle : Model.Lifecycle.Oracle) {m m' : Model.Lifecycle.Session}
    (hstep : ReceiveStep oracle m m') (hcb : ModelClauseB m.triple.postQuantum.epoch m.braid) :
    m'.triple.postQuantum.direction = m.triple.postQuantum.direction ∧
      (m'.triple.classical.dhsPub ≠ m.triple.classical.dhsPub →
        m'.triple.classical.dhsPub = oracle.dhPublic m'.ratchetPrivate) ∧
      ModelClauseB m'.triple.postQuantum.epoch m'.braid ∧
      (m'.braid = .failed ∨ modelIsInit m'.braid = modelIsInit m.braid) := by
  rcases hstep with ⟨htr, hrp, hb⟩ | ⟨msgB, hdr, dr, ds, cand, mk, hb, hord, -, hs, hrp⟩
  · rw [htr, hb]; exact ⟨rfl, fun h => absurd rfl h, hcb, Or.inr rfl⟩
  obtain ⟨st1, ha, hs1⟩ := triple_receive_advance hs
  have hio := hord.2 st1 ha
  obtain ⟨⟨k1, hc⟩, ⟨k2, hp⟩⟩ := triple_receive_parts hio hs1
  obtain ⟨hsame, hdh, -, -⟩ := ratchet_receive_frame hio.noStoredClassical hio.sameChain hio.newChain hc
  obtain ⟨cs, ch, -, -, -, -, hq⟩ := sparseTail_ok hp
  have hq' : m'.triple.postQuantum.epoch = st1.epoch ∧ m'.triple.postQuantum.direction = st1.direction := by
    rw [hq]; exact ⟨rfl, rfl⟩
  have hadv : st1.direction = m.triple.postQuantum.direction ∧
      ((Model.Braid.receive oracle.braidKem m.braid msgB).2.1 = none → st1.epoch = m.triple.postQuantum.epoch) ∧
      (∀ o, (Model.Braid.receive oracle.braidKem m.braid msgB).2.1 = some o → st1.epoch = o.keyEpoch) := by
    unfold advancedOf Model.SparseRatchet.maybeAdvanceReceiveDetailed Model.SparseRatchet.maybeAdvanceDetailed at ha
    rcases hout : (Model.Braid.receive oracle.braidKem m.braid msgB).2.1 with _ | o
    · rw [hout] at ha; simp only [Model.Lifecycle.sparseOutputOf, Option.map_none, Option.some.injEq] at ha
      subst ha; exact ⟨rfl, fun _ => rfl, fun _ h => by cases h⟩
    · rw [hout] at ha
      simp only [Model.Lifecycle.sparseOutputOf, Option.map_some] at ha
      rcases hadv : Model.SparseRatchet.advanceDetailed m.triple.postQuantum
          { keyEpoch := o.keyEpoch, key := o.key } with e | st2
      · rw [hadv] at ha; simp at ha
      rw [hadv] at ha; simp only [Option.some.injEq] at ha; subst ha
      obtain ⟨-, -, hep, hdir, -⟩ := advance_ok_parts hadv
      exact ⟨hdir, fun h => (by cases h), fun o' h => (by cases h; exact hep)⟩
  obtain ⟨hdir1, hnone, hsome⟩ := hadv
  obtain ⟨hrole, hcbn, hcbs⟩ := receive_clauses oracle.braidKem m.braid msgB _ hcb
  refine ⟨by rw [hq'.2, hdir1], fun hne => ?_, ?_, by rw [hb]; exact hrole⟩
  · have hrp' : m'.ratchetPrivate = cand := by rw [hrp]; simp [hne]
    rw [hrp']
    by_cases hd : m.triple.classical.dhrPub = some hdr.dr.dh
    · exact absurd (hsame hd) hne
    · exact hdh hd
  · rw [hb, hq'.1]
    rcases hout : (Model.Braid.receive oracle.braidKem m.braid msgB).2.1 with _ | o
    · rw [hnone hout]; exact hcbn hout
    · rw [hsome o hout]; exact (hcbs o hout).2


/-! ## The session's own clauses after a receive at any agreement state -/

open Tacenta.UnitLifecycleReceivePreserve (mono_bind mono_ite strip_bind strip_ite)
open Tacenta.UnitLifecycleEncryptPreserve (strip_ite_else)

/-- Clause (b) read on a code Triple and agreement: the agreement's tag and epoch, and the sparse epoch equal to the
agreement's at tags 7 to 10 and one behind elsewhere. -/
def CodeClauseB (t : tacenta_triple.State) (b : tacenta_braid.Braid) : Prop :=
  ∃ T E, tacenta_braid.Braid.state_tag b = ok T ∧ tacenta_braid.Braid.epoch b = ok E ∧
    ((7#u8 ≤ T ∧ T ≤ 10#u8) → t.post_quantum.epoch = E) ∧
    (¬ (7#u8 ≤ T ∧ T ≤ 10#u8) → t.post_quantum.epoch.val + 1 = E.val)

set_option maxHeartbeats 2000000 in
/-- **`Session::structural_invariant` after a receive at any agreement state**: replacing the Triple, the agreement
and the ratchet key of a session that passes it (and whose agreement had not failed) keeps it, when the new ratchet
key's public key is the new sending key, the direction is kept, and the new agreement has failed or reads the same
role and clause (b) holds of it with the new sparse epoch.  Under `OptionEqU64Shape`. -/
theorem structural_after
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (s : lifecycle.Session) (t : tacenta_triple.State) (b : tacenta_braid.Braid)
    (rp : tacenta_boundary.dh.PrivateKey) (hstr : lifecycle.Session.structural_invariant s = ok true)
    (pk : tacenta_boundary.dh.PublicKeyBytes) (hpk : tacenta_boundary.dh.PrivateKey.public_key rp = ok pk)
    (hb : tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok t.classical.dhs_pub)
    (hdir : t.post_quantum.direction = s.triple.post_quantum.direction)
    (hsnf : tacenta_braid.Braid.failed s.braid = ok false)
    (hcase : tacenta_braid.Braid.failed b = ok true ∨
      (tacenta_braid.Braid.failed b = ok false ∧
        tacenta_braid.Braid.is_initiator b = tacenta_braid.Braid.is_initiator s.braid ∧ CodeClauseB t b)) :
    lifecycle.Session.structural_invariant { s with triple := t, braid := b, ratchet_private := rp } = ok true := by
  revert hstr
  unfold lifecycle.Session.structural_invariant lifecycle.Session.is_responder
  rcases hcase with hfb | ⟨hfb, hi, T, E, hT, hE, hfold, hnf⟩
  · simp only [hpk, hb, bind_tc_ok, tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public,
      Tacenta.UnitHeadroomInvariant.array_ne_self, Bool.false_eq_true, if_false, hfb, hsnf, if_true,
      tacenta_triple.State.direction, tacenta_spqr.State.impl.direction, hdir]
    have hif : tacenta_braid.Braid.is_initiator b = ok none := by
      obtain ⟨st⟩ := b
      rw [Tacenta.UnitLifecycleEncryptPreserve.failed_iff] at hfb; simp only at hfb; subst hfb; rfl
    simp only [hif, bind_tc_ok]
    repeat' first
      | (with_reducible exact id)
      | (intro h; simp at h; done)
      | (apply mono_bind; intro _)
      | apply mono_ite
      | (apply strip_bind; intro _)
      | (apply strip_ite_else)
      | (apply strip_ite)
      | split
  · have hrel : (if 7#u8 ≤ T then
          (if T ≤ 10#u8 then ok (decide (t.post_quantum.epoch = E)) else do
            let o ← lift (U64.checked_add t.post_quantum.epoch 1#u64)
            core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqU64 o (some E))
        else do
          let o ← lift (U64.checked_add t.post_quantum.epoch 1#u64)
          core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqU64 o (some E)) = ok true := by
      have hadd : ¬ (7#u8 ≤ T ∧ T ≤ 10#u8) → U64.checked_add t.post_quantum.epoch 1#u64 = some E := by
        intro hn
        have h1 := hnf hn
        have := U64.checked_add_bv_spec t.post_quantum.epoch 1#u64
        rcases hc : U64.checked_add t.post_quantum.epoch 1#u64 with _ | z
        · rw [hc] at this; simp at this; scalar_tac
        · rw [hc] at this; congr 1; apply UScalar.eq_of_val_eq; simp at this; omega
      by_cases h7 : 7#u8 ≤ T
      · by_cases h10 : T ≤ 10#u8
        · simp [h7, h10, hfold ⟨h7, h10⟩]
        · simp only [h7, h10, if_true, if_false]
          rw [hadd (fun h => h10 h.2)]
          simp only [lift, bind_tc_ok]; rw [hoeq E E]; simp
      · simp only [h7, if_false]
        rw [hadd (fun h => h7 h.1)]
        simp only [lift, bind_tc_ok]; rw [hoeq E E]; simp
    simp only [hpk, hb, bind_tc_ok, tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public,
      Tacenta.UnitHeadroomInvariant.array_ne_self, Bool.false_eq_true, if_false, hfb, hsnf,
      tacenta_triple.State.direction, tacenta_spqr.State.impl.direction, hdir, hT, hE, tacenta_triple.State.epoch,
      tacenta_spqr.State.impl.epoch, hi]
    rw [hrel]
    simp only [bind_tc_ok, if_true]
    repeat' first
      | (with_reducible exact id)
      | (intro h; simp at h; done)
      | apply mono_ite
      | (apply strip_bind; intro _)
      | (apply strip_ite_else)
      | (apply strip_ite)


/-- `e % 2` on a `u64`, by value. -/
theorem u64_mod2 (e : U64) : ∃ r : U64, e % 2#u64 = ok r ∧ (r = 1#u64 ↔ e.val % 2 = 1) ∧ r.val = e.val % 2 := by
  obtain ⟨r, hr, hrv⟩ := Std.WP.spec_imp_exists (U64.rem_spec e (y := 2#u64) (by simp))
  have hv : r.val = e.val % 2 := by simpa using hrv
  refine ⟨r, hr, ?_, hv⟩
  constructor
  · intro h; rw [h] at hv; simp at hv; omega
  · intro h; apply UScalar.eq_of_val_eq; simp; omega

/-- The code agreement's tag, epoch, `failed` and role are the model state's it refines. -/
theorem braid_reads_refines {K : Model.Braid.Kem} {st : tacenta_braid.State} {m : Model.Braid.BraidState}
    (h : Tacenta.SessionUnitBraidT3.StateRefines K st m) :
    (∃ T : U8, tacenta_braid.Braid.state_tag ⟨st⟩ = ok T ∧ T.val = modelTag m) ∧
      (∃ E : U64, tacenta_braid.Braid.epoch ⟨st⟩ = ok E ∧ E.val = m.epoch) ∧
      tacenta_braid.Braid.failed ⟨st⟩ = ok (Model.Lifecycle.braidFailed m) ∧
      tacenta_braid.Braid.is_initiator ⟨st⟩ = ok (modelIsInit m) := by
  cases st <;> cases m <;> simp only [Tacenta.SessionUnitBraidT3.StateRefines] at h <;>
    refine ⟨⟨_, rfl, by simp [modelTag]⟩, ⟨_, rfl, ?_⟩,
      by simp [tacenta_braid.Braid.failed, Model.Lifecycle.braidFailed], ?_⟩ <;>
    simp_all [tacenta_braid.State.epoch, Model.Braid.BraidState.epoch, tacenta_braid.Braid.is_initiator,
      modelIsInit, modelSendsHeader]
  all_goals
    obtain ⟨rfl, _⟩ := h
    obtain ⟨r, hr, hiff, hv⟩ := u64_mod2 _
    rw [hr]
    simp [hiff, hv]


open Tacenta.UnitLifecycleT3 (DhView SessionRefines)
open Tacenta.UnitLifecycleEncryptPreserve (braid_eta code_epoch_val)

/-- **Clause (b) of `Session::structural_invariant` gives the model's clause (b)** at the model session the session
refines, when the agreement has not failed and the sparse epoch is below `u64::MAX - 1`.  Under `OptionEqU64Shape`. -/
theorem modelClauseB_of_structural
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {dh : DhView} {K : Model.Braid.Kem} {s : lifecycle.Session} {m : Model.Lifecycle.Session}
    (hrel : SessionRefines dh K s m) (hstr : lifecycle.Session.structural_invariant s = ok true)
    (hsnf : tacenta_braid.Braid.failed s.braid = ok false)
    (hroomE : s.triple.post_quantum.epoch.val + 1 < Std.U64.max) :
    ModelClauseB m.triple.postQuantum.epoch m.braid := by
  obtain ⟨⟨T, hT, hTv⟩, ⟨E, hE, hEv⟩, hfm, -⟩ := braid_reads_refines hrel.braid
  rw [← braid_eta] at hT hE hfm
  rw [hsnf] at hfm
  have hmf : m.braid ≠ .failed := by
    intro h; rw [h] at hfm; simp [Model.Lifecycle.braidFailed] at hfm
  have hF := code_epoch_val hrel
  unfold lifecycle.Session.structural_invariant at hstr
  obtain ⟨_, -, hstr⟩ := bind_eq_ok_inv hstr
  obtain ⟨_, -, hstr⟩ := bind_eq_ok_inv hstr
  obtain ⟨_, -, hstr⟩ := bind_eq_ok_inv hstr
  obtain ⟨c, -, hstr⟩ := bind_eq_ok_inv hstr
  cases c
  swap
  · simp at hstr
  simp only [Bool.false_eq_true, if_false] at hstr
  rw [hsnf] at hstr
  simp only [bind_tc_ok, Bool.false_eq_true, if_false, hE, hT, tacenta_triple.State.epoch,
    tacenta_spqr.State.impl.epoch] at hstr
  obtain ⟨rel, hrelv, hstr⟩ := bind_eq_ok_inv hstr
  cases rel
  · simp at hstr
  right
  have hadd : ∃ z, U64.checked_add s.triple.post_quantum.epoch 1#u64 = some z ∧
      z.val = s.triple.post_quantum.epoch.val + 1 := by
    have := U64.checked_add_bv_spec s.triple.post_quantum.epoch 1#u64
    rcases hc : U64.checked_add s.triple.post_quantum.epoch 1#u64 with _ | z
    · rw [hc] at this; simp at this; scalar_tac
    · rw [hc] at this; exact ⟨z, rfl, by simpa using this.2.1⟩
  obtain ⟨z, hz, hzv⟩ := hadd
  have h7 : (7#u8 ≤ T) ↔ 7 ≤ modelTag m.braid := by rw [← hTv]; simp [UScalar.le_equiv]
  have h10 : (T ≤ 10#u8) ↔ modelTag m.braid ≤ 10 := by rw [← hTv]; simp [UScalar.le_equiv]
  constructor
  · intro ⟨a, b⟩
    simp only [h7.mpr a, h10.mpr b, if_true, ok.injEq, decide_eq_true_eq] at hrelv
    rw [← hF, ← hEv, hrelv]
  · intro hn
    have hrel2 : core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqU64 (some z) (some E) =
        ok true := by
      by_cases a : 7#u8 ≤ T
      · have b : ¬ T ≤ 10#u8 := fun b => hn ⟨h7.mp a, h10.mp b⟩
        simp only [a, b, if_true, if_false, lift, hz, bind_tc_ok] at hrelv
        exact hrelv
      · simp only [a, if_false, lift, hz, bind_tc_ok] at hrelv
        exact hrelv
    rw [hoeq] at hrel2
    simp only [ok.injEq, decide_eq_true_eq] at hrel2
    subst hrel2
    rw [← hF, ← hEv, hzv]

/-- **The model's clause (b) gives clause (b) read on the code** at a code Triple and agreement related to the model
ones, when the agreement has not failed. -/
theorem codeClauseB_of_model {K : Model.Braid.Kem} {t : tacenta_triple.State} {st : tacenta_braid.State}
    {mt : Model.Triple.State} {mb : Model.Braid.BraidState}
    (ht : Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
      Tacenta.SessionUnitTripleT3.spqrAbs t mt)
    (hb : Tacenta.SessionUnitBraidT3.StateRefines K st mb) (hcb : ModelClauseB mt.postQuantum.epoch mb)
    (hnf : mb ≠ .failed) : CodeClauseB t ⟨st⟩ := by
  obtain ⟨⟨T, hT, hTv⟩, ⟨E, hE, hEv⟩, -, -⟩ := braid_reads_refines hb
  have hF : t.post_quantum.epoch.val = mt.postQuantum.epoch := by
    have h := congrArg Model.SparseRatchet.State.epoch ht.2
    simpa [Tacenta.SessionUnitTripleT3.spqrAbs] using h
  rcases hcb with h | ⟨hf, hn⟩
  · exact absurd h hnf
  have h7 : (7#u8 ≤ T) ↔ 7 ≤ modelTag mb := by rw [← hTv]; simp [UScalar.le_equiv]
  have h10 : (T ≤ 10#u8) ↔ modelTag mb ≤ 10 := by rw [← hTv]; simp [UScalar.le_equiv]
  refine ⟨T, E, hT, hE, fun ⟨a, b⟩ => ?_, fun hnn => ?_⟩
  · apply UScalar.eq_of_val_eq; rw [hF, hEv]; exact hf ⟨h7.mp a, h10.mp b⟩
  · rw [hF, hEv]; exact hn (fun ⟨a, b⟩ => hnn ⟨h7.mpr a, h10.mpr b⟩)

open Tacenta.UnitLifecycleT3 (DhCodecOf arrayOf)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid dhPublicValid_canonical)
open Tacenta.UnitLifecycleReceivePreserve (keyOf_dhs clause_a_of_structural structural_clear_pending decrypt_ok_inner)

/-! ## `decrypt_ratchet` and `decrypt` keep the invariant at every agreement state -/

/-- A successful `decrypt_ratchet` was called on a session whose agreement had not failed.  Hypothesis-free. -/
theorem decrypt_ratchet_ok_live {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (s : lifecycle.Session) (msg : Slice U8) (rng : R) (v : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (h : lifecycle.Session.decrypt_ratchet rc crc s msg rng = ok (core.result.Result.Ok v, s', rng')) :
    tacenta_braid.Braid.failed s.braid = ok false := by
  unfold lifecycle.Session.decrypt_ratchet at h
  obtain ⟨fb, hfb, h⟩ := bind_eq_ok_inv h
  cases fb
  · exact hfb
  · simp at h

/-- **The laws the receive side rests on**, each a named field: the clone record `KemCloneAgrees`, the value laws
`DivCeilValue` and `TruncatePrefix`, the four KEM length totality records, the two assumed length laws
`KeyPairEkVectorLen` and `Encapsulate2Len`, the shape law `OptionEqU64Shape` of the opaque `Option<u64>` comparison
clause (b) uses, and `DhPublicValid` (a new ratchet key's bytes are canonical). -/
structure ReceiveInvariantLaws : Prop where
  kemClone : Tacenta.SessionUnitBraidT3.KemCloneAgrees
  divCeil : Tacenta.SessionUnitDecoderBound.DivCeilValue
  truncate : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix
  headerLen : Tacenta.SessionUnitBraidT1.HeaderLenTotal
  ekVectorLen : Tacenta.SessionUnitBraidT1.EkVectorLenTotal
  ct1Len : Tacenta.SessionUnitBraidT1.Ct1LenTotal
  ct2Len : Tacenta.SessionUnitBraidT1.Ct2LenTotal
  keyPairEkVector : KeyPairEkVectorLen
  encapsulate2Len : Encapsulate2Len
  optionEq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq)
  dhPublicValid : DhPublicValid

/-- **`Session::decrypt_ratchet` keeps `Session::invariant` and spends one unit of the counter budget, at every
agreement state**: for every session `s` that passes `Session::invariant`, has room for `k + 1` operations and refines
a model session `m`, and every successful return of `decrypt_ratchet` there whose session refines a model session `m'`
that is a `ReceiveStep` from `m`, the session returned passes `Session::invariant` and has room for `k`.  Every
agreement state and every transition (the agreement's output and the sparse `advance` included); the Triple's receive in
the in-order scope with an output (`InOrderOut`).  The relation after the call and the step are hypotheses; nothing here
calls a refinement theorem.  Under `ReceiveInvariantLaws`, the oracle's `dhPublic` clause and the view's codec relation.
-/
theorem decrypt_ratchet_keeps_invariant (laws : ReceiveInvariantLaws)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (dh : DhView) (codec : DhCodecOf dh) (K : Model.Braid.Kem) (oracle : Model.Lifecycle.Oracle)
    (hdhPublic : ∀ secret, ∃ publicKey, tacenta_boundary.dh.PrivateKey.public_key secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret))
    (s : lifecycle.Session) (m m' : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))
    (hrel : SessionRefines dh K s m)
    (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.decrypt_ratchet rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng'))
    (hrel' : SessionRefines dh K s' m') (hstep : ReceiveStep oracle m m') :
    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by
  obtain ⟨L⟩ := braidLens_of_totals laws.headerLen laws.ekVectorLen laws.ct1Len laws.ct2Len
  have hoeq := laws.optionEq
  have hpub := laws.dhPublicValid
  obtain ⟨hstr, htri, hbr⟩ := (session_invariant_iff s).mp hinv
  have hsnf := decrypt_ratchet_ok_live rc crc s msg rng pt s' rng' hcall
  obtain ⟨msgB, x, y, bc, a, ck, pkb, new, hrecv, -, -, hpkb, hnew, hcases⟩ :=
    Tacenta.UnitLifecycleResponderSuccessor.decrypt_ratchet_ok_parts rc crc s msg rng pt s' rng' hcall
  have hbc : s'.braid = bc := by rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
  -- the agreement half, at every state
  have hbinv : tacenta_braid.Braid.invariant bc = ok true :=
    braid_receive_keeps_invariant L laws.kemClone laws.divCeil laws.truncate laws.keyPairEkVector
      laws.encapsulate2Len s.braid msgB x y bc hbr hrecv
  -- the model's step: direction, the sending key, clause (b) and the role
  have hcb : ModelClauseB m.triple.postQuantum.epoch m.braid :=
    modelClauseB_of_structural hoeq hrel hstr hsnf (by have := hroom.sparseEpoch; omega)
  obtain ⟨hdirM, hdhsM, hcb', hrole⟩ := step_frame_any oracle hstep hcb
  have hdir : s'.triple.post_quantum.direction = s.triple.post_quantum.direction := by
    have h1 := congrArg Model.SparseRatchet.State.direction hrel'.triple.2
    have h0 := congrArg Model.SparseRatchet.State.direction hrel.triple.2
    simp only [Tacenta.SessionUnitTripleT3.spqrAbs] at h1 h0
    have hd : Tacenta.SessionUnitSpqrT3.directionOf s'.triple.post_quantum.direction =
        Tacenta.SessionUnitSpqrT3.directionOf s.triple.post_quantum.direction := by
      rw [h1, h0, hdirM]
    revert hd
    cases s'.triple.post_quantum.direction <;> cases s.triple.post_quantum.direction <;>
      simp [Tacenta.SessionUnitSpqrT3.directionOf]
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
    rcases hstep with ⟨htr', -⟩ | ⟨msgM, hdr, dr, ds, cand, mk, -, hord, hcanH, hs, -⟩
    · rw [htr']; exact hmodel
    · refine modelTripleInv_receive_out hmodel hcanH (fun hd => ?_) hord hs
      obtain ⟨st1, ha1, hs1⟩ := triple_receive_advance hs
      obtain ⟨⟨k1, hc⟩, -⟩ := triple_receive_parts (hord.2 st1 ha1) hs1
      have hio := hord.2 st1 ha1
      obtain ⟨-, hdh, -, -⟩ := ratchet_receive_frame hio.noStoredClassical hio.sameChain hio.newChain hc
      rw [← hdh hd, ← hk1, canonicalKey_keyOf]
      exact hcan'
  have htri' : tacenta_triple.State.invariant s'.triple = ok true :=
    (triple_invariant_iff_model hrel'.triple).mpr hmodel'
  -- the session's own clauses
  have hs'eq : s' = { s with triple := s'.triple, braid := bc, ratchet_private := s'.ratchet_private } := by
    rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
  obtain ⟨-, -, hfm, him⟩ := braid_reads_refines hrel'.braid
  obtain ⟨-, -, -, him0⟩ := braid_reads_refines hrel.braid
  rw [← braid_eta, hbc] at hfm him
  rw [← braid_eta] at him0
  have hcase : tacenta_braid.Braid.failed bc = ok true ∨
      (tacenta_braid.Braid.failed bc = ok false ∧
        tacenta_braid.Braid.is_initiator bc = tacenta_braid.Braid.is_initiator s.braid ∧
        CodeClauseB s'.triple bc) := by
    by_cases hmf : m'.braid = .failed
    · left; rw [hfm, hmf]; rfl
    · right
      have hnf : Model.Lifecycle.braidFailed m'.braid = false := by
        revert hmf; cases m'.braid <;> simp [Model.Lifecycle.braidFailed]
      refine ⟨by rw [hfm, hnf], ?_, ?_⟩
      · rw [him, him0]
        rcases hrole with h | h
        · exact absurd h hmf
        · rw [h]
      · have := codeClauseB_of_model hrel'.triple hrel'.braid hcb' hmf
        rwa [← braid_eta, hbc] at this
  have hstr' : lifecycle.Session.structural_invariant s' = ok true := by
    rw [hs'eq]
    exact structural_after hoeq s s'.triple bc s'.ratchet_private hstr pk' hpk' hb' hdir hsnf hcase
  refine ⟨(session_invariant_iff s').mpr ⟨hstr', htri', hbc ▸ hbinv⟩, ?_⟩
  exact (counterRoom_iff_model hrel' k).mpr
    (modelCounterRoom_receive_any oracle k hstep ((counterRoom_iff_model hrel (k + 1)).mp hroom))

/-- **`Session::decrypt` keeps `Session::invariant` and spends one unit of the counter budget, at every agreement
state**: as `decrypt_ratchet_keeps_invariant`, for the public call, whose success is a successful inner
`decrypt_ratchet` with the pending initial message cleared (`decrypt_ok_inner`). -/
theorem decrypt_keeps_invariant (laws : ReceiveInvariantLaws)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (dh : DhView) (codec : DhCodecOf dh) (K : Model.Braid.Kem) (oracle : Model.Lifecycle.Oracle)
    (hdhPublic : ∀ secret, ∃ publicKey, tacenta_boundary.dh.PrivateKey.public_key secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret))
    (s : lifecycle.Session) (m m' : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))
    (hrel : SessionRefines dh K s m)
    (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.decrypt rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng'))
    (hrel' : SessionRefines dh K s' m') (hstep : ReceiveStep oracle m m') :
    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by
  obtain ⟨inner, s1, hin, rfl⟩ := decrypt_ok_inner rc crc s msg rng pt s' rng' hcall
  have hw := Tacenta.UnitLifecycleAtomicity.decrypt_ratchet_ok_writes rc crc s inner rng pt s1 rng' hin
  have hpend : s1.pending_initial = s.pending_initial := by rw [hw]
  have hrel1 : SessionRefines dh K s1 { m' with pendingInitial := m.pendingInitial } :=
    ⟨hrel'.triple, hrel'.braid, hrel'.ratchetPrivate, hrel'.identityAd, hrel'.ourIdentityPublic,
      hrel'.peerIdentityPublic, by rw [hpend]; exact hrel.pendingInitial, hrel'.establishedEphemeral⟩
  obtain ⟨hinv1, hroom1⟩ := decrypt_ratchet_keeps_invariant laws rc crc dh codec K oracle hdhPublic
    s m _ k hinv hroom hrel inner rng pt s1 rng' hin hrel1 hstep
  obtain ⟨hstr1, htri1, hbr1⟩ := (session_invariant_iff s1).mp hinv1
  obtain ⟨r1, r2, r3, r4⟩ := hroom1
  exact ⟨(session_invariant_iff _).mpr ⟨structural_clear_pending s1 hstr1, htri1, hbr1⟩, ⟨r1, r2, r3, r4⟩⟩

/-- **`Session::decrypt` keeps `Session::invariant` and spends one unit of the counter budget, at the model's own
`decrypt` step, at every agreement state**: `decrypt_keeps_invariant` with the relation after the call taken at
`Model.Lifecycle.decrypt` of a message the model's dispatch passes on, every header of which is in the in-order scope
with the agreement's output (`decrypt_receiveStep`). -/
theorem decrypt_keeps_invariant_model_step (laws : ReceiveInvariantLaws)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (dh : DhView) (codec : DhCodecOf dh) (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle)
    (hdhPublic : ∀ secret, ∃ publicKey, tacenta_boundary.dh.PrivateKey.public_key secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret))
    (s : lifecycle.Session) (m : Model.Lifecycle.Session) (k : Nat)
    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))
    (hrel : SessionRefines dh K s m)
    (msg : Slice U8) (msgM inner : Model.Lifecycle.Bytes)
    (hdisp : Model.Lifecycle.dispatchDecrypt oracle m msgM = .ok inner)
    (hord : ∀ c ct, Model.CompositeHeader.decodeDetailed inner = .ok (c, ct) →
      InOrderOut m.triple (Model.Lifecycle.tripleHeaderOf c) (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.1))
    (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.decrypt rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng'))
    (hrel' : SessionRefines dh K s' (Model.Lifecycle.decrypt view oracle m msgM).session) :
    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k :=
  decrypt_keeps_invariant laws rc crc dh codec K oracle hdhPublic s m _ k hinv hroom hrel msg rng pt s' rng' hcall
    hrel' (decrypt_receiveStep view oracle m msgM inner hdisp hord)

/-- The in-order scope without an output is the in-order scope of `UnitLifecycleReceivePreserve`.  Model only. -/
theorem inOrderOut_none {m : Model.Triple.State} {h : Model.Triple.Header} (hio : InOrder m h) :
    InOrderOut m h none := by
  refine ⟨⟨hio.noStoredClassical, hio.sameChain, hio.newChain⟩, fun st1 ha => ?_⟩
  simp only [advancedOf, Model.SparseRatchet.maybeAdvanceReceiveDetailed, Model.SparseRatchet.maybeAdvanceDetailed,
    Option.some.injEq] at ha
  subst ha
  exact hio

open Tacenta.UnitLifecycleReceivePreserve (InOrderReceiveStep keeps_output_none) in
/-- **An in-order receive step whose agreement state some message reaches is a `ReceiveStep`**: the narrow step of
`UnitLifecycleReceivePreserve` is a case of the general one, whenever the agreement after it is the model agreement's
receive of some message and stays put when the Triple and the ratchet key do.  Model only. -/
theorem receiveStep_of_inOrder (oracle : Model.Lifecycle.Oracle) {m m' : Model.Lifecycle.Session}
    (hstep : InOrderReceiveStep oracle m m') (msgB : Model.Braid.Msg)
    (hb : (Model.Braid.receive oracle.braidKem m.braid msgB).2.2 = m'.braid)
    (hstay : m'.triple = m.triple → m'.ratchetPrivate = m.ratchetPrivate → m'.braid = m.braid) :
    ReceiveStep oracle m m' := by
  have hnone := keeps_output_none oracle.braidKem m.braid msgB (by rw [hb]; exact hstep.1)
  rcases hstep.2 with ⟨ht, hr⟩ | ⟨hdr, dr, ds, cand, mk, hio, hcan, hs, hrp⟩
  · exact Or.inl ⟨ht, hr, hstay ht hr⟩
  · refine Or.inr ⟨msgB, hdr, dr, ds, cand, mk, hb.symm, ?_, hcan, ?_, hrp⟩
    · rw [hnone]; exact inOrderOut_none hio
    · rw [hnone]; exact hs


section Run
open Tacenta.UnitLifecycleT3 (KemView vecOf sliceOf OracleOf BraidSendRefinementContracts
  TripleSendRefinementContracts CodewordViewSendOf ZeroizingRoundTrips)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstKey senderAfterFirst DhAgreeContributory AeadRoundTrip)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid establishedModelOf)
open Tacenta.UnitLifecycleResponderReplyReceipt (replyReceiptSession)
open Tacenta.UnitLifecycleReceivePreserve (replyReceipt_inOrderStep modelCounterRoom_afterFirstSend)

/-- **Regression: the initiator's receipt of the reply keeps the invariant, through the general step**: on the run of
`initiator_receives_reply_successor`, under its hypotheses and the three laws `TruncatePrefix`, `KeyPairEkVectorLen`
and `Encapsulate2Len`, the session `s''` the initiator's `decrypt` of the reply returns passes `Session::invariant` and
has room for every `j` with `j + 2 < u32::MAX` further operations, derived through `decrypt_keeps_invariant` (every
agreement state) rather than the narrow in-order step.  The run's step is in the narrow scope
(`replyReceipt_inOrderStep`); `receiveStep_of_inOrder` makes it a general step. -/
theorem initiator_receives_reply_via_general [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
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
    (ptR : Slice Std.U8) (hroomR : 102 + (ptR.val.length + 48) ≤ Usize.max)
    (hfitR : (Tacenta.UnitLifecycleT3.sliceOf ptR).length + 150 ≤ Model.Lifecycle.maxRatchetFrameLen) (rngR : F)
    (hfreshB : oracleB.dhPublic dB ≠ arrayOf q.peerRatchetBytes)
    (htr : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix) (hekl : KeyPairEkVectorLen)
    (henc2 : Encapsulate2Len) :
    ∃ (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session)
      (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' : R),
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' =
        ok (core.result.Result.Ok ptA, s'', rngA') ∧
      lifecycle.Session.invariant s'' = ok true ∧
      (∀ j, j + 2 < Std.U32.max → CounterRoom s'' j) := by
  have hlenR : (Tacenta.UnitLifecycleT3.sliceOf ptR).length ≤ Model.Lifecycle.maxPlaintextLen := by
    rw [Model.Lifecycle.maxRatchetFrameLen_value] at hfitR
    simp only [Model.Lifecycle.maxPlaintextLen]; omega
  -- the receipt on the run: the reply, the call and the relation after it
  obtain ⟨dSend, x, bytesR, sB'', ptA, s'', rngA', -, -, hcallR, -, hcallA, hpt, -, -, -, hsess⟩ :=
    Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply rc crc trace dh kem view oracle braid triple
      aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected
      rng0 rng1 s h q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall contractsA agreementsA dA
      restA hdrawA rcB crcB contracts hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB
      storeB hpublish hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR hfitR
      rngR hfreshB
  -- the key generation at the first send's two draws, from the reply's run
  obtain ⟨-, -, -, dk, ekSeed, ekVector, -, -, hkg, -⟩ :=
    Tacenta.UnitLifecycleResponderReply.initiator_first_send_responder_replies rc crc trace dh kem view oracle braid
      triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA
      expected rng0 rng1 s h q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall rcB crcB contracts
      hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish hidentity
      hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR hlenR rngR
  -- the session the first send left: invariant, relation, on the same first send
  obtain ⟨hinv, hrel, -, -⟩ :=
    Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_hypotheses rc crc trace dh kem view
      oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct hbound hpub hoeq
      agreementsA.kemLen agreementsA.validateEk hsizes contracts.divCeilValue rcE crcE ourA bundleA expected rng0
      rng1 s h plaintext hroom rng htrace ⟨d1, d2, rest, hdraws⟩ bytes s' rng' hcall
  subst hq
  have hfits := Tacenta.UnitLifecycleT3.encrypt_ok_plaintext_fits rc crc q.session plaintext rng bytes s' rng'
    hcall
  obtain ⟨encoder, hmA⟩ := Tacenta.UnitLifecycleResponderReplyReceipt.first_send_model_session dh view oracle q
    (sliceOf plaintext) hfits d1 d2 rest (htrace.symm.trans hdraws) dk ekSeed ekVector hkg
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
  -- the narrow step is a general step: the agreement stays at `KeysSampled`, which a message without data reaches
  have hstep' : ReceiveStep oracle mA _ := receiveStep_of_inOrder oracle hstep ⟨0, .ct1, none⟩
    (by simp [Model.Braid.receive, hbraid, replyReceiptSession]) (fun _ _ => by simp [replyReceiptSession])
  -- the budget at s'
  have hroomA : ∀ j, j + 2 < Std.U32.max → CounterRoom s' (j + 1) := fun j hj =>
    (counterRoom_iff_model hrel (j + 1)).mpr
      (modelCounterRoom_afterFirstSend mA _ _ _ _ _ _ _ _ dk ekVector encoder j hA hbraid hj)
  -- the laws of the receive side, from the run's records and the three named laws
  have laws : ReceiveInvariantLaws := ⟨agreementsA.kemClone, contracts.divCeilValue, htr, contractsA.braid.headerLen,
    contractsA.braid.ekVectorLen, contractsA.braid.ct1Len, contractsA.braid.ct2Len, hekl, henc2, hoeq, hpub⟩
  -- the general preservation
  have key : ∀ j, j + 2 < Std.U32.max → lifecycle.Session.invariant s'' = ok true ∧ CounterRoom s'' j :=
    fun j hj => decrypt_keeps_invariant laws rc crc dh codec oracle.braidKem oracle oracleOf.dhPublic s' mA _ j hinv
      (hroomA j hj) hrel _ rng' ptA s'' rngA' hcallA hsess hstep'
  have h0 : (0 : Nat) + 2 < Std.U32.max := by simp [Std.U32.max_eq]
  exact ⟨bytesR, sB'', ptA, s'', rngA', hcallR, hcallA, (key 0 h0).1, fun j hj => (key j hj).2⟩

end Run

/-! ## The two length laws hold in the faithful model interpretation -/

section Laws
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)
open Tacenta.UnitSatisfiabilityBraidAgreements (Interp.modelT3 vecOfBytes ekVecOf)

/-- `KeyPairEkVectorLen` read at an interpretation of the unit's opaque operations. -/
def KeyPairEkVectorLenShape (I : Interp) : Prop :=
  ∀ (kp : I.IncrementalKeyPair) (v : alloc.vec.Vec Std.U8), I.ikpEkVector kp = ok v →
    ∃ n : Usize, I.EK_VECTOR_LEN = ok n ∧ v.length = n.val

/-- `Encapsulate2Len` read at an interpretation of the unit's opaque operations. -/
def Encapsulate2LenShape (I : Interp) : Prop :=
  ∀ (es : I.EncapsState) (s : Slice Std.U8) (c : alloc.vec.Vec Std.U8),
    I.encapsulate2 es s = ok (core.result.Result.Ok c) → ∃ n : Usize, I.CT2_LEN = ok n ∧ c.length = n.val

/-- `KeyPairEkVectorLen` is its shape at the real constants. -/
theorem KeyPairEkVectorLen_is : KeyPairEkVectorLen ↔ KeyPairEkVectorLenShape Interp.real := Iff.rfl

/-- `Encapsulate2Len` is its shape at the real constants. -/
theorem Encapsulate2Len_is : Encapsulate2Len ↔ Encapsulate2LenShape Interp.real := Iff.rfl

/-- **`KeyPairEkVectorLen` holds in `Interp.modelT3`**, the interpretation in which the agreements and the laws
`DivCeilValue` and `TruncatePrefix` already hold: its key pairs' `ek_vector` is 64 bytes and `EK_VECTOR_LEN` is 64. -/
theorem modelT3_keyPairEkVectorLen : KeyPairEkVectorLenShape Interp.modelT3 := by
  intro kp v h
  simp only [Interp.modelT3, ok.injEq] at h
  subst h
  exact ⟨64#usize, rfl, by simp [vecOfBytes, ekVecOf, alloc.vec.Vec.length,
    Tacenta.UnitSatisfiabilityBraidAgreements.bytesOf]⟩

/-- **`Encapsulate2Len` holds in `Interp.modelT3`**: its `encapsulate2` returns 32 bytes and `CT2_LEN` is 32. -/
theorem modelT3_encapsulate2Len : Encapsulate2LenShape Interp.modelT3 := by
  intro es s c h
  simp only [Interp.modelT3, ok.injEq, core.result.Result.Ok.injEq] at h
  subst h
  exact ⟨32#usize, rfl, by simp [vecOfBytes, alloc.vec.Vec.length,
    Tacenta.UnitSatisfiabilityBraidAgreements.bytesOf]⟩

end Laws

/-! ## `establish_responder` at every input -/

section Establish
open Tacenta.UnitLifecycleSendPreserve (CounterRoom counterRoom_zero)
open Tacenta.UnitLifecycleT3 (DhView DhCodecOf SessionRefines)
open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts responderModelOf PrepareRefusal ResponderCommit)

/-- **The inner receive of `establish_responder` keeps `Session::invariant` and leaves the four ceilings**, at every
input that reaches it: for the prepared parts `p` the code reads off the input (`ResponderPreparedParts`), every
successful `decrypt_ratchet` of `p.message` at `p.session` whose session refines a model session that is a
`ReceiveStep` from `responderModelOf dh p` returns a session that passes `Session::invariant` and meets
`CounterHeadroom`.  The prepared session passes the invariant (`responder_prepared_invariant`), refines
`responderModelOf dh p` (`sessionRefines_responder_prepared`) and has room for one operation
(`counterRoom_responder_prepared`); the step is `decrypt_ratchet_keeps_invariant`. -/
theorem prepared_receive_keeps_invariant (laws : ReceiveInvariantLaws)
    (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees) {K : Model.Braid.Kem}
    (hlens : Tacenta.SessionUnitBraidT3.KemLenAgrees K) (hkdf : Tacenta.SessionUnitBraidT3.BraidHkdfAgrees)
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (dh : DhView) (codec : DhCodecOf dh) (oracle : Model.Lifecycle.Oracle)
    (hdhPublic : ∀ secret, ∃ publicKey, tacenta_boundary.dh.PrivateKey.public_key secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret))
    {our : lifecycle.Identity} {store : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts our store msg) (rng : R)
    (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)
    (hin : lifecycle.Session.decrypt_ratchet rc crc p.session p.message rng = ok (core.result.Result.Ok pt, s', rng'))
    (m' : Model.Lifecycle.Session) (hrel' : SessionRefines dh K s' m')
    (hstep : ReceiveStep oracle (responderModelOf dh p) m') :
    lifecycle.Session.invariant s' = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s' := by
  have hinvP := Tacenta.UnitLifecycleEstablishResponder.responder_prepared_invariant laws.dhPublicValid
    laws.optionEq laws.divCeil laws.headerLen p
  have hrelP : SessionRefines dh K p.session (responderModelOf dh p) :=
    Tacenta.UnitLifecycleEstablishResponder.sessionRefines_responder_prepared hea hlens hkdf hz laws.divCeil dh p
  obtain ⟨hinv, hroom⟩ := decrypt_ratchet_keeps_invariant laws rc crc dh codec K oracle hdhPublic p.session
    (responderModelOf dh p) m' 0 hinvP (Tacenta.UnitLifecycleReceivePreserve.counterRoom_responder_prepared p)
    hrelP p.message rng pt s' rng' hin hrel' hstep
  exact ⟨hinv, (counterRoom_zero _).mp hroom⟩

/-- **Every session `establish_responder` returns is the inner receive's, which keeps `Session::invariant`**, at
every identity, prekey store, initial message and source: a return `Ok (s', pt)` is the successful
`decrypt_ratchet` of the prepared parts' message at the prepared session with the store after `ResponderCommit`
(`establish_responder_cases`), and for every prepared parts whose inner receive returned it
`prepared_receive_keeps_invariant` applies.  The refusals return no session. -/
theorem establish_responder_keeps_invariant (laws : ReceiveInvariantLaws)
    (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees) {K : Model.Braid.Kem}
    (hlens : Tacenta.SessionUnitBraidT3.KemLenAgrees K) (hkdf : Tacenta.SessionUnitBraidT3.BraidHkdfAgrees)
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (dh : DhView) (codec : DhCodecOf dh) (oracle : Model.Lifecycle.Oracle)
    (hdhPublic : ∀ secret, ∃ publicKey, tacenta_boundary.dh.PrivateKey.public_key secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret))
    (our : lifecycle.Identity) (store : lifecycle.PrekeyStore) (msg : Slice U8) (rng : R)
    (s' : lifecycle.Session) (pt : alloc.vec.Vec U8) (store' : lifecycle.PrekeyStore) (rng' : R)
    (h : lifecycle.establish_responder rc crc our store msg rng = ok (core.result.Result.Ok (s', pt), store', rng')) :
    (∃ p : ResponderPreparedParts our store msg,
      lifecycle.Session.decrypt_ratchet rc crc p.session p.message rng = ok (core.result.Result.Ok pt, s', rng') ∧
      ResponderCommit store p.decoded.kem_prekey_id p.decoded.one_time_prekey_id p.lastResort p.replay store') ∧
    ∀ p : ResponderPreparedParts our store msg,
      lifecycle.Session.decrypt_ratchet rc crc p.session p.message rng = ok (core.result.Result.Ok pt, s', rng') →
      ∀ m', SessionRefines dh K s' m' → ReceiveStep oracle (responderModelOf dh p) m' →
        lifecycle.Session.invariant s' = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s' := by
  refine ⟨?_, fun p hin m' hrel' hstep =>
    prepared_receive_keeps_invariant laws hea hlens hkdf hz rc crc dh codec oracle hdhPublic p rng pt s' rng' hin m'
      hrel' hstep⟩
  rcases Tacenta.UnitLifecycleEstablishResponder.establish_responder_cases rc crc our store msg rng _ h with
    ⟨e, -, hout⟩ | ⟨p, inner, hin, ⟨e, -, hout⟩ | ⟨pt0, store0, hpt, hcommit, hout⟩⟩
  · simp at hout
  · simp at hout
  obtain ⟨r1, s1, rng1⟩ := inner
  simp only at hpt hout
  subst hpt
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at hout
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hout
  exact ⟨p, hin, hcommit⟩

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

open Tacenta.UnitLifecycleT3 (KemView vecOf sliceOf OracleOf arrayOf)
open Tacenta.UnitLifecycleEstablishInitiatorShape (dhPublicValid_canonical)
open Tacenta.UnitLifecycleReceivePreserve (firstReceipt_inOrderStep)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstReceiptSession receiverAfterFirst firstReceiverTriple)

theorem responder_first_frame_via_general [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type}
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
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB'))
    (htr : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix) (hekl : KeyPairEkVectorLen)
    (henc2 : Encapsulate2Len) :
    lifecycle.Session.invariant sB' = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' := by
  have hsize := Tacenta.UnitLifecycleEstablishResponder.establish_responder_ok_fits rcB crcB ourB storeB
    msg rngB _ _ _ hcallB
  rcases responder_first_frame_prepares rcB crcB contracts hpub hsym hrt hct hbound codec q pending hpend _ msg
      hmsg hsize ourB storeB hpublish hidentity hdistinct hkem rngB with ⟨-, e, -, hrefuse⟩ |
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
  -- the narrow step is a general step: a header chunk of epoch 1 reaches the agreement it leaves
  have hstep' : ReceiveStep oracleB (responderModelOf dh p) _ := receiveStep_of_inOrder oracleB hstep
    ⟨1, .hdr, some (modelChunkOf src c)⟩
    (by simp [Model.Braid.receive, responderModelOf, firstReceiptSession, Model.Braid.initBob,
      Model.Braid.Decoder.addChunk, Model.Braid.Decoder.new, Model.Braid.Decoder.message,
      Model.Braid.Decoder.hasMessage, Model.Braid.chunkBytes, Model.Braid.headerSize, Model.Braid.macSize])
    (fun ht _ => absurd (congrArg (fun t => t.classical.events) ht)
      (by rw [hB]; simp [firstReceiptSession, receiverAfterFirst, firstReceiverTriple]))
  -- the laws of the receive side, from the run's records and the three named laws
  have laws : ReceiveInvariantLaws := ⟨agreements.kemClone, contracts.divCeilValue, htr,
    contracts.decrypt.braid.headerLen, contracts.decrypt.braid.ekVectorLen, contracts.decrypt.braid.ct1Len,
    contracts.decrypt.braid.ct2Len, hekl, henc2, hoeq, hpub⟩
  -- the general preservation at `establish_responder`
  exact (establish_responder_keeps_invariant laws agreements.erasure agreements.kemLen agreements.hkdf
    contracts.decrypt.braid.zeroizingArray rcB crcB dh codec oracleB oracleOfB.dhPublic ourB storeB msg rngB _ _ _ _
    hcallB).2 p hinner _ hrel hstep'

end Regression

end Establish

end Tacenta.UnitLifecycleDecryptPreserve

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
info: 'Tacenta.UnitLifecycleDecryptPreserve.inv_loop_general' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.inv_loop_general

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.decoder_invariant_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.decoder_invariant_iff

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.add_chunk_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.add_chunk_keeps

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.model_chunk_len' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.model_chunk_len

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.decoder_message_len' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.decoder_message_len

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.inv_headerSent' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.inv_headerSent

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.inv_keysSampled' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.inv_keysSampled

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.inv_ct1Received' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.inv_ct1Received

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.inv_ekSentCt1Received' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.inv_ekSentCt1Received

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.inv_noHeaderReceived' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.inv_noHeaderReceived

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.inv_headerReceived' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.inv_headerReceived

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.inv_ct1Sampled' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.inv_ct1Sampled

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.inv_ekReceivedCt1Sampled' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.inv_ekReceivedCt1Sampled

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.inv_ct1Acknowledged' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.inv_ct1Acknowledged

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.inv_ct2Sampled' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.inv_ct2Sampled

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.fresh_decoder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.fresh_decoder

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.fresh_encoder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.fresh_encoder

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.add_mac' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.add_mac

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.braidLens_of_totals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.HEADER_LEN]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.braidLens_of_totals

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.step_receive_headerSent' depends on axioms: [propext,
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
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.step_receive_headerSent

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.failed_inv' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.failed_inv

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.finish_encaps_inv' depends on axioms: [propext,
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
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.finish_encaps_inv

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct2Sampled' depends on axioms: [propext,
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
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct2Sampled

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.step_receive_keysSampled' depends on axioms: [propext,
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
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.step_receive_keysSampled

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct1Received' depends on axioms: [propext,
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
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct1Received

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.step_receive_noHeaderReceived' depends on axioms: [propext,
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
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.step_receive_noHeaderReceived

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.step_receive_ekSentCt1Received' depends on axioms: [propext,
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
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.step_receive_ekSentCt1Received

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct1Sampled' depends on axioms: [propext,
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
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct1Sampled

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.step_receive_ekReceivedCt1Sampled' depends on axioms: [propext,
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
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.step_receive_ekReceivedCt1Sampled

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct1Acknowledged' depends on axioms: [propext,
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
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct1Acknowledged

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.clone_inv' depends on axioms: [propext,
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
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 core.num.Usize.div_ceil,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.clone_inv

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.step_receive_inv' depends on axioms: [propext,
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
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.step_receive_inv

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.braid_receive_keeps_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.braid_receive_keeps_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.receive_clauses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.receive_clauses

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.triple_receive_advance' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.triple_receive_advance

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.modelTripleInv_advanced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.modelTripleInv_advanced

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.modelTripleInv_receive_out' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.modelTripleInv_receive_out

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.receiveWithEviction_inOrderOut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.receiveWithEviction_inOrderOut

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.decryptRatchet_receiveStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.decryptRatchet_receiveStep

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.decrypt_receiveStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.decrypt_receiveStep

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.receive_epoch_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.receive_epoch_le

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.modelCounterRoom_receive_any' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.modelCounterRoom_receive_any

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.step_frame_any' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.step_frame_any

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.structural_after' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.structural_after

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.u64_mod2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.u64_mod2

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.braid_reads_refines' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.braid_reads_refines

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.modelClauseB_of_structural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.modelClauseB_of_structural

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.codeClauseB_of_model' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.codeClauseB_of_model

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.decrypt_ratchet_ok_live' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.decrypt_ratchet_ok_live

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.decrypt_ratchet_keeps_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.decrypt_ratchet_keeps_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.decrypt_keeps_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.decrypt_keeps_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.decrypt_keeps_invariant_model_step' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.decrypt_keeps_invariant_model_step

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.inOrderOut_none' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.inOrderOut_none

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.receiveStep_of_inOrder' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.receiveStep_of_inOrder

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.initiator_receives_reply_via_general' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.initiator_receives_reply_via_general

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen_is' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen_is

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len_is' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len_is

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.modelT3_keyPairEkVectorLen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.modelT3_keyPairEkVectorLen

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.modelT3_encapsulate2Len' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptPreserve.modelT3_encapsulate2Len

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.prepared_receive_keeps_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.prepared_receive_keeps_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.establish_responder_keeps_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.establish_responder_keeps_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptPreserve.responder_first_frame_via_general' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptPreserve.responder_first_frame_via_general

/--
info: Tacenta.UnitLifecycleDecryptPreserve.inv_loop_general : ∀ (d : tacenta_erasure.Decoder),
  d.invariant_loop (Array.repeat 8192#usize 0#u8) true 0#usize ⦃ r =>
    r = (d.size, d.needed, d.have, decide (List.map (fun c => ↑c.index) ↑d.have).Nodup) ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.inv_loop_general

/--
info: Tacenta.UnitLifecycleDecryptPreserve.decoder_invariant_iff : ∀ (d : tacenta_erasure.Decoder),
  d.invariant = ok true ↔
    tacenta_erasure.chunk_count d.size = ok d.needed ∧
      ↑d.needed ≤ 65536 ∧ (↑d.have).length ≤ ↑d.needed ∧ (List.map (fun c => ↑c.index) ↑d.have).Nodup
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.decoder_invariant_iff

/--
info: Tacenta.UnitLifecycleDecryptPreserve.add_chunk_keeps : ∀ (d d' : tacenta_erasure.Decoder) (c : tacenta_erasure.Chunk)
  (r : Bool),
  d.invariant = ok true → d.add_chunk c = ok (r, d') → d'.invariant = ok true ∧ d'.size = d.size ∧ d'.needed = d.needed
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.add_chunk_keeps

/--
info: Tacenta.UnitLifecycleDecryptPreserve.model_chunk_len : ∀ (d : Model.Erasure.Decoder),
  (∀ h ∈ d.held, List.length h.2 = 32) → ∀ (t : ℕ), List.length (d.chunk t) = 32
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.model_chunk_len

/--
info: Tacenta.UnitLifecycleDecryptPreserve.decoder_message_len : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix →
    ∀ (d : tacenta_erasure.Decoder),
      d.invariant = ok true → ∀ (v : alloc.vec.Vec U8), d.message = ok (some v) → (↑v).length = ↑d.size
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.decoder_message_len

/--
info: Tacenta.UnitLifecycleDecryptPreserve.inv_headerSent : ∀ (c1 ev : Usize),
  tacenta_kem.CT1_LEN = ok c1 →
    tacenta_kem.EK_VECTOR_LEN = ok ev →
      ∀ (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair) (d : tacenta_erasure.Decoder)
        (enc : tacenta_erasure.Encoder),
        { state := tacenta_braid.State.HeaderSent e a kp d enc }.invariant = ok true ↔
          e ≥ 1#u64 ∧
            d.invariant = ok true ∧
              d.size = c1 ∧
                enc.invariant = ok true ∧
                  tacenta_braid.encoder_sized enc ev = ok true ∧ tacenta_braid.key_pair_valid kp = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.inv_headerSent

/--
info: Tacenta.UnitLifecycleDecryptPreserve.inv_keysSampled : ∀ (c1 ev c2 hl n96 n2 : Usize),
  tacenta_kem.CT1_LEN = ok c1 →
    tacenta_kem.EK_VECTOR_LEN = ok ev →
      tacenta_kem.CT2_LEN = ok c2 →
        tacenta_kem.HEADER_LEN = ok hl →
          hl + tacenta_braid.MAC_LEN = ok n96 →
            c2 + tacenta_braid.MAC_LEN = ok n2 →
              ∀ (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair)
                (enc : tacenta_erasure.Encoder),
                { state := tacenta_braid.State.KeysSampled e a kp enc }.invariant = ok true ↔
                  e ≥ 1#u64 ∧
                    enc.invariant = ok true ∧
                      tacenta_braid.encoder_sized enc n96 = ok true ∧ tacenta_braid.key_pair_valid kp = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.inv_keysSampled

/--
info: Tacenta.UnitLifecycleDecryptPreserve.inv_ct1Received : ∀ (c1 ev c2 hl n96 n2 : Usize),
  tacenta_kem.CT1_LEN = ok c1 →
    tacenta_kem.EK_VECTOR_LEN = ok ev →
      tacenta_kem.CT2_LEN = ok c2 →
        tacenta_kem.HEADER_LEN = ok hl →
          hl + tacenta_braid.MAC_LEN = ok n96 →
            c2 + tacenta_braid.MAC_LEN = ok n2 →
              ∀ (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair) (ct1 : alloc.vec.Vec U8)
                (enc : tacenta_erasure.Encoder),
                { state := tacenta_braid.State.Ct1Received e a kp ct1 enc }.invariant = ok true ↔
                  e ≥ 1#u64 ∧
                    ct1.len = c1 ∧
                      enc.invariant = ok true ∧
                        tacenta_braid.encoder_sized enc ev = ok true ∧ tacenta_braid.key_pair_valid kp = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.inv_ct1Received

/--
info: Tacenta.UnitLifecycleDecryptPreserve.inv_ekSentCt1Received : ∀ (c1 ev c2 hl n96 n2 : Usize),
  tacenta_kem.CT1_LEN = ok c1 →
    tacenta_kem.EK_VECTOR_LEN = ok ev →
      tacenta_kem.CT2_LEN = ok c2 →
        tacenta_kem.HEADER_LEN = ok hl →
          hl + tacenta_braid.MAC_LEN = ok n96 →
            c2 + tacenta_braid.MAC_LEN = ok n2 →
              ∀ (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair) (ct1 : alloc.vec.Vec U8)
                (d : tacenta_erasure.Decoder),
                { state := tacenta_braid.State.EkSentCt1Received e a kp ct1 d }.invariant = ok true ↔
                  e ≥ 1#u64 ∧
                    ct1.len = c1 ∧ d.invariant = ok true ∧ d.size = n2 ∧ tacenta_braid.key_pair_valid kp = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.inv_ekSentCt1Received

/--
info: Tacenta.UnitLifecycleDecryptPreserve.inv_noHeaderReceived : ∀ (c1 ev c2 hl n96 n2 : Usize),
  tacenta_kem.CT1_LEN = ok c1 →
    tacenta_kem.EK_VECTOR_LEN = ok ev →
      tacenta_kem.CT2_LEN = ok c2 →
        tacenta_kem.HEADER_LEN = ok hl →
          hl + tacenta_braid.MAC_LEN = ok n96 →
            c2 + tacenta_braid.MAC_LEN = ok n2 →
              ∀ (e : U64) (a : tacenta_braid.Auth) (d : tacenta_erasure.Decoder),
                { state := tacenta_braid.State.NoHeaderReceived e a d }.invariant = ok true ↔
                  e ≥ 1#u64 ∧ d.invariant = ok true ∧ d.size = n96
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.inv_noHeaderReceived

/--
info: Tacenta.UnitLifecycleDecryptPreserve.inv_headerReceived : ∀ (c1 ev c2 hl n96 n2 : Usize),
  tacenta_kem.CT1_LEN = ok c1 →
    tacenta_kem.EK_VECTOR_LEN = ok ev →
      tacenta_kem.CT2_LEN = ok c2 →
        tacenta_kem.HEADER_LEN = ok hl →
          hl + tacenta_braid.MAC_LEN = ok n96 →
            c2 + tacenta_braid.MAC_LEN = ok n2 →
              ∀ (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8) (d : tacenta_erasure.Decoder),
                { state := tacenta_braid.State.HeaderReceived e a hdr d }.invariant = ok true ↔
                  e ≥ 1#u64 ∧ hdr.len = hl ∧ d.invariant = ok true ∧ d.size = ev
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.inv_headerReceived

/--
info: Tacenta.UnitLifecycleDecryptPreserve.inv_ct1Sampled : ∀ (c1 ev c2 hl n96 n2 : Usize),
  tacenta_kem.CT1_LEN = ok c1 →
    tacenta_kem.EK_VECTOR_LEN = ok ev →
      tacenta_kem.CT2_LEN = ok c2 →
        tacenta_kem.HEADER_LEN = ok hl →
          hl + tacenta_braid.MAC_LEN = ok n96 →
            c2 + tacenta_braid.MAC_LEN = ok n2 →
              ∀ (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8) (es : tacenta_kem.EncapsState)
                (ct1 : alloc.vec.Vec U8) (enc : tacenta_erasure.Encoder) (d : tacenta_erasure.Decoder),
                { state := tacenta_braid.State.Ct1Sampled e a hdr es ct1 enc d }.invariant = ok true ↔
                  e ≥ 1#u64 ∧
                    hdr.len = hl ∧
                      ct1.len = c1 ∧
                        enc.invariant = ok true ∧
                          tacenta_braid.encoder_sized enc c1 = ok true ∧ d.invariant = ok true ∧ d.size = ev
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.inv_ct1Sampled

/--
info: Tacenta.UnitLifecycleDecryptPreserve.inv_ekReceivedCt1Sampled : ∀ (c1 ev c2 hl n96 n2 : Usize),
  tacenta_kem.CT1_LEN = ok c1 →
    tacenta_kem.EK_VECTOR_LEN = ok ev →
      tacenta_kem.CT2_LEN = ok c2 →
        tacenta_kem.HEADER_LEN = ok hl →
          hl + tacenta_braid.MAC_LEN = ok n96 →
            c2 + tacenta_braid.MAC_LEN = ok n2 →
              ∀ (e : U64) (a : tacenta_braid.Auth) (es : tacenta_kem.EncapsState) (ct1 ekv : alloc.vec.Vec U8)
                (enc : tacenta_erasure.Encoder),
                { state := tacenta_braid.State.EkReceivedCt1Sampled e a es ct1 ekv enc }.invariant = ok true ↔
                  e ≥ 1#u64 ∧
                    ct1.len = c1 ∧ ekv.len = ev ∧ enc.invariant = ok true ∧ tacenta_braid.encoder_sized enc c1 = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.inv_ekReceivedCt1Sampled

/--
info: Tacenta.UnitLifecycleDecryptPreserve.inv_ct1Acknowledged : ∀ (c1 ev c2 hl n96 n2 : Usize),
  tacenta_kem.CT1_LEN = ok c1 →
    tacenta_kem.EK_VECTOR_LEN = ok ev →
      tacenta_kem.CT2_LEN = ok c2 →
        tacenta_kem.HEADER_LEN = ok hl →
          hl + tacenta_braid.MAC_LEN = ok n96 →
            c2 + tacenta_braid.MAC_LEN = ok n2 →
              ∀ (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8) (es : tacenta_kem.EncapsState)
                (ct1 : alloc.vec.Vec U8) (d : tacenta_erasure.Decoder),
                { state := tacenta_braid.State.Ct1Acknowledged e a hdr es ct1 d }.invariant = ok true ↔
                  e ≥ 1#u64 ∧ hdr.len = hl ∧ ct1.len = c1 ∧ d.invariant = ok true ∧ d.size = ev
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.inv_ct1Acknowledged

/--
info: Tacenta.UnitLifecycleDecryptPreserve.inv_ct2Sampled : ∀ (c1 ev c2 hl n96 n2 : Usize),
  tacenta_kem.CT1_LEN = ok c1 →
    tacenta_kem.EK_VECTOR_LEN = ok ev →
      tacenta_kem.CT2_LEN = ok c2 →
        tacenta_kem.HEADER_LEN = ok hl →
          hl + tacenta_braid.MAC_LEN = ok n96 →
            c2 + tacenta_braid.MAC_LEN = ok n2 →
              ∀ (e : U64) (a : tacenta_braid.Auth) (enc : tacenta_erasure.Encoder),
                { state := tacenta_braid.State.Ct2Sampled e a enc }.invariant = ok true ↔
                  e ≥ 1#u64 ∧ enc.invariant = ok true ∧ tacenta_braid.encoder_sized enc n2 = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.inv_ct2Sampled

/--
info: Tacenta.UnitLifecycleDecryptPreserve.fresh_decoder : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  ∀ (n : Usize),
    ↑n ≤ 32 * 65536 →
      ∀ (d : tacenta_erasure.Decoder), tacenta_erasure.Decoder.new n = ok d → d.invariant = ok true ∧ d.size = n
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.fresh_decoder

/--
info: Tacenta.UnitLifecycleDecryptPreserve.fresh_encoder : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  ∀ (s : Slice U8),
    (Tacenta.SessionUnitBraidT3.sliceOf s).length ≤ 32 * 65536 →
      ∀ {enc : tacenta_erasure.Encoder},
        tacenta_erasure.Encoder.new s = ok enc →
          enc.invariant = ok true ∧
            ∀ (len : Usize),
              ↑len = (Tacenta.SessionUnitBraidT3.sliceOf s).length → tacenta_braid.encoder_sized enc len = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.fresh_encoder

/--
info: Tacenta.UnitLifecycleDecryptPreserve.add_mac : ∀ (x : Usize),
  ↑x ≤ 4096 → ∃ n, x + tacenta_braid.MAC_LEN = ok n ∧ ↑n = ↑x + 32
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.add_mac

/--
info: Tacenta.UnitLifecycleDecryptPreserve.braidLens_of_totals : Tacenta.SessionUnitBraidT1.HeaderLenTotal →
  Tacenta.SessionUnitBraidT1.EkVectorLenTotal →
    Tacenta.SessionUnitBraidT1.Ct1LenTotal →
      Tacenta.SessionUnitBraidT1.Ct2LenTotal → Nonempty Tacenta.UnitLifecycleDecryptPreserve.BraidLens
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.braidLens_of_totals

/--
info: Tacenta.UnitLifecycleDecryptPreserve.step_receive_headerSent : ∀ (L : Tacenta.UnitLifecycleDecryptPreserve.BraidLens),
  Tacenta.SessionUnitDecoderBound.DivCeilValue →
    Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix →
      ∀ (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair)
        (d : tacenta_erasure.Decoder) (enc : tacenta_erasure.Encoder) (msg : tacenta_braid.Msg)
        (out : Option tacenta_braid.Output) (next : tacenta_braid.State),
        { state := tacenta_braid.State.HeaderSent e a kp d enc }.invariant = ok true →
          self.step_receive (tacenta_braid.State.HeaderSent e a kp d enc) msg = ok (out, next) →
            { state := next }.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.step_receive_headerSent

/--
info: Tacenta.UnitLifecycleDecryptPreserve.failed_inv : { state := tacenta_braid.State.Failed }.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.failed_inv

/--
info: Tacenta.UnitLifecycleDecryptPreserve.finish_encaps_inv : ∀ (L : Tacenta.UnitLifecycleDecryptPreserve.BraidLens),
  Tacenta.SessionUnitDecoderBound.DivCeilValue →
    Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len →
      ∀ (e : U64) (a : tacenta_braid.Auth) (es : tacenta_kem.EncapsState) (ct1 ekv : Slice U8)
        (st : tacenta_braid.State),
        e ≥ 1#u64 → tacenta_braid.finish_encaps e a es ct1 ekv = ok st → { state := st }.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.finish_encaps_inv

/--
info: Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct2Sampled : ∀ (_L : Tacenta.UnitLifecycleDecryptPreserve.BraidLens)
  (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth) (enc : tacenta_erasure.Encoder)
  (msg : tacenta_braid.Msg) (out : Option tacenta_braid.Output) (next : tacenta_braid.State),
  { state := tacenta_braid.State.Ct2Sampled e a enc }.invariant = ok true →
    self.step_receive (tacenta_braid.State.Ct2Sampled e a enc) msg = ok (out, next) →
      { state := next }.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct2Sampled

/--
info: Tacenta.UnitLifecycleDecryptPreserve.step_receive_keysSampled : ∀ (L : Tacenta.UnitLifecycleDecryptPreserve.BraidLens),
  Tacenta.SessionUnitDecoderBound.DivCeilValue →
    Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen →
      ∀ (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair)
        (enc : tacenta_erasure.Encoder) (msg : tacenta_braid.Msg) (out : Option tacenta_braid.Output)
        (next : tacenta_braid.State),
        { state := tacenta_braid.State.KeysSampled e a kp enc }.invariant = ok true →
          self.step_receive (tacenta_braid.State.KeysSampled e a kp enc) msg = ok (out, next) →
            { state := next }.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.step_receive_keysSampled

/--
info: Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct1Received : ∀ (L : Tacenta.UnitLifecycleDecryptPreserve.BraidLens),
  Tacenta.SessionUnitDecoderBound.DivCeilValue →
    ∀ (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair)
      (ct1 : alloc.vec.Vec U8) (enc : tacenta_erasure.Encoder) (msg : tacenta_braid.Msg)
      (out : Option tacenta_braid.Output) (next : tacenta_braid.State),
      { state := tacenta_braid.State.Ct1Received e a kp ct1 enc }.invariant = ok true →
        self.step_receive (tacenta_braid.State.Ct1Received e a kp ct1 enc) msg = ok (out, next) →
          { state := next }.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct1Received

/--
info: Tacenta.UnitLifecycleDecryptPreserve.step_receive_noHeaderReceived : ∀
  (L : Tacenta.UnitLifecycleDecryptPreserve.BraidLens),
  Tacenta.SessionUnitDecoderBound.DivCeilValue →
    ∀ (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth) (d : tacenta_erasure.Decoder)
      (msg : tacenta_braid.Msg) (out : Option tacenta_braid.Output) (next : tacenta_braid.State),
      { state := tacenta_braid.State.NoHeaderReceived e a d }.invariant = ok true →
        self.step_receive (tacenta_braid.State.NoHeaderReceived e a d) msg = ok (out, next) →
          { state := next }.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.step_receive_noHeaderReceived

/--
info: Tacenta.UnitLifecycleDecryptPreserve.step_receive_ekSentCt1Received : ∀
  (L : Tacenta.UnitLifecycleDecryptPreserve.BraidLens),
  Tacenta.SessionUnitDecoderBound.DivCeilValue →
    ∀ (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth) (kp : tacenta_kem.IncrementalKeyPair)
      (ct1 : alloc.vec.Vec U8) (d : tacenta_erasure.Decoder) (msg : tacenta_braid.Msg)
      (out : Option tacenta_braid.Output) (next : tacenta_braid.State),
      { state := tacenta_braid.State.EkSentCt1Received e a kp ct1 d }.invariant = ok true →
        self.step_receive (tacenta_braid.State.EkSentCt1Received e a kp ct1 d) msg = ok (out, next) →
          { state := next }.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.step_receive_ekSentCt1Received

/--
info: Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct1Sampled : ∀ (L : Tacenta.UnitLifecycleDecryptPreserve.BraidLens),
  Tacenta.SessionUnitDecoderBound.DivCeilValue →
    Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix →
      Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len →
        ∀ (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8)
          (es : tacenta_kem.EncapsState) (ct1 : alloc.vec.Vec U8) (enc : tacenta_erasure.Encoder)
          (d : tacenta_erasure.Decoder) (msg : tacenta_braid.Msg) (out : Option tacenta_braid.Output)
          (next : tacenta_braid.State),
          { state := tacenta_braid.State.Ct1Sampled e a hdr es ct1 enc d }.invariant = ok true →
            self.step_receive (tacenta_braid.State.Ct1Sampled e a hdr es ct1 enc d) msg = ok (out, next) →
              { state := next }.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct1Sampled

/--
info: Tacenta.UnitLifecycleDecryptPreserve.step_receive_ekReceivedCt1Sampled : ∀
  (L : Tacenta.UnitLifecycleDecryptPreserve.BraidLens),
  Tacenta.SessionUnitDecoderBound.DivCeilValue →
    Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len →
      ∀ (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth) (es : tacenta_kem.EncapsState)
        (ct1 ekv : alloc.vec.Vec U8) (enc : tacenta_erasure.Encoder) (msg : tacenta_braid.Msg)
        (out : Option tacenta_braid.Output) (next : tacenta_braid.State),
        { state := tacenta_braid.State.EkReceivedCt1Sampled e a es ct1 ekv enc }.invariant = ok true →
          self.step_receive (tacenta_braid.State.EkReceivedCt1Sampled e a es ct1 ekv enc) msg = ok (out, next) →
            { state := next }.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.step_receive_ekReceivedCt1Sampled

/--
info: Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct1Acknowledged : ∀
  (L : Tacenta.UnitLifecycleDecryptPreserve.BraidLens),
  Tacenta.SessionUnitDecoderBound.DivCeilValue →
    Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len →
      ∀ (self : tacenta_braid.Braid) (e : U64) (a : tacenta_braid.Auth) (hdr : alloc.vec.Vec U8)
        (es : tacenta_kem.EncapsState) (ct1 : alloc.vec.Vec U8) (d : tacenta_erasure.Decoder) (msg : tacenta_braid.Msg)
        (out : Option tacenta_braid.Output) (next : tacenta_braid.State),
        { state := tacenta_braid.State.Ct1Acknowledged e a hdr es ct1 d }.invariant = ok true →
          self.step_receive (tacenta_braid.State.Ct1Acknowledged e a hdr es ct1 d) msg = ok (out, next) →
            { state := next }.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.step_receive_ct1Acknowledged

/--
info: Tacenta.UnitLifecycleDecryptPreserve.clone_inv : ∀ (L : Tacenta.UnitLifecycleDecryptPreserve.BraidLens),
  Tacenta.SessionUnitBraidT3.KemCloneAgrees →
    ∀ (st st' : tacenta_braid.State),
      tacenta_braid.State.Insts.CoreCloneClone.clone st = ok st' →
        { state := st }.invariant = ok true → { state := st' }.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.clone_inv

/--
info: Tacenta.UnitLifecycleDecryptPreserve.step_receive_inv : ∀ (L : Tacenta.UnitLifecycleDecryptPreserve.BraidLens),
  Tacenta.SessionUnitDecoderBound.DivCeilValue →
    Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix →
      Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen →
        Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len →
          ∀ (self : tacenta_braid.Braid) (st : tacenta_braid.State) (msg : tacenta_braid.Msg)
            (out : Option tacenta_braid.Output) (next : tacenta_braid.State),
            { state := st }.invariant = ok true →
              self.step_receive st msg = ok (out, next) → { state := next }.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.step_receive_inv

/--
info: Tacenta.UnitLifecycleDecryptPreserve.braid_receive_keeps_invariant : ∀
  (L : Tacenta.UnitLifecycleDecryptPreserve.BraidLens),
  Tacenta.SessionUnitBraidT3.KemCloneAgrees →
    Tacenta.SessionUnitDecoderBound.DivCeilValue →
      Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix →
        Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen →
          Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len →
            ∀ (b : tacenta_braid.Braid) (msg : tacenta_braid.Msg) (x : U64) (y : Option tacenta_braid.Output)
              (bc : tacenta_braid.Braid), b.invariant = ok true → b.receive msg = ok (x, y, bc) → bc.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.braid_receive_keeps_invariant

/--
info: Tacenta.UnitLifecycleDecryptPreserve.receive_clauses : ∀ (K : Model.Braid.Kem) (st : Model.Braid.BraidState)
  (msg : Model.Braid.Msg) (sp : ℕ),
  Tacenta.UnitLifecycleDecryptPreserve.ModelClauseB sp st →
    ((Model.Braid.receive K st msg).2.2 = Model.Braid.BraidState.failed ∨
        Tacenta.UnitLifecycleDecryptPreserve.modelIsInit (Model.Braid.receive K st msg).2.2 =
          Tacenta.UnitLifecycleDecryptPreserve.modelIsInit st) ∧
      ((Model.Braid.receive K st msg).2.1 = none →
          Tacenta.UnitLifecycleDecryptPreserve.ModelClauseB sp (Model.Braid.receive K st msg).2.2) ∧
        ∀ (o : Model.Braid.Output),
          (Model.Braid.receive K st msg).2.1 = some o →
            o.keyEpoch = sp + 1 ∧
              Tacenta.UnitLifecycleDecryptPreserve.ModelClauseB o.keyEpoch (Model.Braid.receive K st msg).2.2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.receive_clauses

/--
info: @Tacenta.UnitLifecycleDecryptPreserve.triple_receive_advance : ∀ {m m' : Model.Triple.State} {hdr : Model.Triple.Header}
  {dr ds np k : Model.State.Key} {out : Option Model.SparseRatchet.Output},
  Model.Triple.receiveDetailed m hdr dr ds np out = Except.ok (m', k) →
    ∃ st1,
      Tacenta.UnitLifecycleDecryptPreserve.advancedOf m.postQuantum out = some st1 ∧
        Model.Triple.receiveDetailed { classical := m.classical, postQuantum := st1 } hdr dr ds np none =
          Except.ok (m', k)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.triple_receive_advance

/--
info: @Tacenta.UnitLifecycleDecryptPreserve.modelTripleInv_advanced : ∀ {m : Model.Triple.State}
  {out : Option Model.SparseRatchet.Output} {st1 : Model.SparseRatchet.State},
  Tacenta.UnitTripleInvModel.ModelTripleInv m →
    Tacenta.UnitLifecycleDecryptPreserve.advancedOf m.postQuantum out = some st1 →
      Tacenta.UnitTripleInvModel.ModelTripleInv { classical := m.classical, postQuantum := st1 } ∧
        st1.direction = m.postQuantum.direction ∧
          (out = none → st1 = m.postQuantum) ∧
            ∀ (o : Model.SparseRatchet.Output),
              out = some o → st1.epoch = o.keyEpoch ∧ o.keyEpoch = m.postQuantum.epoch + 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.modelTripleInv_advanced

/--
info: @Tacenta.UnitLifecycleDecryptPreserve.modelTripleInv_receive_out : ∀ {m m' : Model.Triple.State}
  {hdr : Model.Triple.Header} {dr ds np k : Model.State.Key} {out : Option Model.SparseRatchet.Output},
  Tacenta.UnitTripleInvModel.ModelTripleInv m →
    Model.Messages.canonicalKey hdr.dr.dh = true →
      (m.classical.dhrPub ≠ some hdr.dr.dh → Model.Messages.canonicalKey np = true) →
        Tacenta.UnitLifecycleDecryptPreserve.InOrderOut m hdr out →
          Model.Triple.receiveDetailed m hdr dr ds np out = Except.ok (m', k) →
            Tacenta.UnitTripleInvModel.ModelTripleInv m'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.modelTripleInv_receive_out

/--
info: @Tacenta.UnitLifecycleDecryptPreserve.receiveWithEviction_inOrderOut : ∀ {m : Model.Triple.State}
  {c : Model.CompositeHeader.Composite} {hdr : Model.Triple.Header} {dr ds np : Model.State.Key}
  {out : Option Model.SparseRatchet.Output} {r : Model.Triple.State × Model.State.Key},
  Tacenta.UnitLifecycleDecryptPreserve.InOrderOut m hdr out →
    Model.Lifecycle.receiveWithEviction m c hdr dr ds np out = Except.ok r →
      Model.Triple.receiveDetailed m hdr dr ds np out = Except.ok r
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.receiveWithEviction_inOrderOut

/--
info: Tacenta.UnitLifecycleDecryptPreserve.decryptRatchet_receiveStep : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (m : Model.Lifecycle.Session) (msg : Model.Lifecycle.Bytes),
  (∀ (c : Model.CompositeHeader.Composite) (ct : List UInt8),
      Model.CompositeHeader.decodeDetailed msg = Except.ok (c, ct) →
        Tacenta.UnitLifecycleDecryptPreserve.InOrderOut m.triple (Model.Lifecycle.tripleHeaderOf c)
          (Model.Lifecycle.sparseOutputOf
            (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.1)) →
    Tacenta.UnitLifecycleDecryptPreserve.ReceiveStep oracle m (Model.Lifecycle.decryptRatchet view oracle m msg).session
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.decryptRatchet_receiveStep

/--
info: Tacenta.UnitLifecycleDecryptPreserve.decrypt_receiveStep : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (m : Model.Lifecycle.Session) (msg inner : Model.Lifecycle.Bytes),
  Model.Lifecycle.dispatchDecrypt oracle m msg = Except.ok inner →
    (∀ (c : Model.CompositeHeader.Composite) (ct : List UInt8),
        Model.CompositeHeader.decodeDetailed inner = Except.ok (c, ct) →
          Tacenta.UnitLifecycleDecryptPreserve.InOrderOut m.triple (Model.Lifecycle.tripleHeaderOf c)
            (Model.Lifecycle.sparseOutputOf
              (Model.Braid.receive oracle.braidKem m.braid (Model.Lifecycle.braidMessageOf view m.braid c)).2.1)) →
      Tacenta.UnitLifecycleDecryptPreserve.ReceiveStep oracle m (Model.Lifecycle.decrypt view oracle m msg).session
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.decrypt_receiveStep

/--
info: Tacenta.UnitLifecycleDecryptPreserve.receive_epoch_le : ∀ (K : Model.Braid.Kem) (st : Model.Braid.BraidState)
  (msg : Model.Braid.Msg), (Model.Braid.receive K st msg).2.2.epoch ≤ st.epoch + 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.receive_epoch_le

/--
info: Tacenta.UnitLifecycleDecryptPreserve.modelCounterRoom_receive_any : ∀ (oracle : Model.Lifecycle.Oracle)
  {m m' : Model.Lifecycle.Session} (k : ℕ),
  Tacenta.UnitLifecycleDecryptPreserve.ReceiveStep oracle m m' →
    Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom m (k + 1) →
      Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom m' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.modelCounterRoom_receive_any

/--
info: Tacenta.UnitLifecycleDecryptPreserve.step_frame_any : ∀ (oracle : Model.Lifecycle.Oracle)
  {m m' : Model.Lifecycle.Session},
  Tacenta.UnitLifecycleDecryptPreserve.ReceiveStep oracle m m' →
    Tacenta.UnitLifecycleDecryptPreserve.ModelClauseB m.triple.postQuantum.epoch m.braid →
      m'.triple.postQuantum.direction = m.triple.postQuantum.direction ∧
        (m'.triple.classical.dhsPub ≠ m.triple.classical.dhsPub →
            m'.triple.classical.dhsPub = oracle.dhPublic m'.ratchetPrivate) ∧
          Tacenta.UnitLifecycleDecryptPreserve.ModelClauseB m'.triple.postQuantum.epoch m'.braid ∧
            (m'.braid = Model.Braid.BraidState.failed ∨
              Tacenta.UnitLifecycleDecryptPreserve.modelIsInit m'.braid =
                Tacenta.UnitLifecycleDecryptPreserve.modelIsInit m.braid)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.step_frame_any

/--
info: Tacenta.UnitLifecycleDecryptPreserve.structural_after : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
    @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
  ∀ (s : lifecycle.Session) (t : tacenta_triple.State) (b : tacenta_braid.Braid) (rp : tacenta_boundary.dh.PrivateKey),
    s.structural_invariant = ok true →
      ∀ (pk : tacenta_boundary.dh.PublicKeyBytes),
        rp.public_key = ok pk →
          pk.as_bytes = ok t.classical.dhs_pub →
            t.post_quantum.direction = s.triple.post_quantum.direction →
              s.braid.failed = ok false →
                b.failed = ok true ∨
                    b.failed = ok false ∧
                      b.is_initiator = s.braid.is_initiator ∧ Tacenta.UnitLifecycleDecryptPreserve.CodeClauseB t b →
                  { triple := t, braid := b, ratchet_private := rp, identity_ad := s.identity_ad,
                        our_identity_public := s.our_identity_public, peer_identity_public := s.peer_identity_public,
                        pending_initial := s.pending_initial,
                        established_ephemeral := s.established_ephemeral }.structural_invariant =
                    ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.structural_after

/--
info: Tacenta.UnitLifecycleDecryptPreserve.u64_mod2 : ∀ (e : U64),
  ∃ r, e % 2#u64 = ok r ∧ (r = 1#u64 ↔ ↑e % 2 = 1) ∧ ↑r = ↑e % 2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.u64_mod2

/--
info: @Tacenta.UnitLifecycleDecryptPreserve.braid_reads_refines : ∀ {K : Model.Braid.Kem} {st : tacenta_braid.State}
  {m : Model.Braid.BraidState},
  Tacenta.SessionUnitBraidT3.StateRefines K st m →
    (∃ T, { state := st }.state_tag = ok T ∧ ↑T = Tacenta.UnitLifecycleDecryptPreserve.modelTag m) ∧
      (∃ E, { state := st }.epoch = ok E ∧ ↑E = m.epoch) ∧
        { state := st }.failed = ok (Model.Lifecycle.braidFailed m) ∧
          { state := st }.is_initiator = ok (Tacenta.UnitLifecycleDecryptPreserve.modelIsInit m)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.braid_reads_refines

/--
info: Tacenta.UnitLifecycleDecryptPreserve.modelClauseB_of_structural : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
    @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
  ∀ {dh : Tacenta.UnitLifecycleT3.DhView} {K : Model.Braid.Kem} {s : lifecycle.Session} {m : Model.Lifecycle.Session},
    Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
      s.structural_invariant = ok true →
        s.braid.failed = ok false →
          ↑s.triple.post_quantum.epoch + 1 < U64.max →
            Tacenta.UnitLifecycleDecryptPreserve.ModelClauseB m.triple.postQuantum.epoch m.braid
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.modelClauseB_of_structural

/--
info: @Tacenta.UnitLifecycleDecryptPreserve.codeClauseB_of_model : ∀ {K : Model.Braid.Kem} {t : tacenta_triple.State}
  {st : tacenta_braid.State} {mt : Model.Triple.State} {mb : Model.Braid.BraidState},
  Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs t
      mt →
    Tacenta.SessionUnitBraidT3.StateRefines K st mb →
      Tacenta.UnitLifecycleDecryptPreserve.ModelClauseB mt.postQuantum.epoch mb →
        mb ≠ Model.Braid.BraidState.failed → Tacenta.UnitLifecycleDecryptPreserve.CodeClauseB t { state := st }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.codeClauseB_of_model

/--
info: @Tacenta.UnitLifecycleDecryptPreserve.decrypt_ratchet_ok_live : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (msg : Slice U8) (rng : R) (v : alloc.vec.Vec U8)
  (s' : lifecycle.Session) (rng' : R),
  lifecycle.Session.decrypt_ratchet rc crc s msg rng = ok (core.result.Result.Ok v, s', rng') →
    s.braid.failed = ok false
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.decrypt_ratchet_ok_live

/--
info: Tacenta.UnitLifecycleDecryptPreserve.decrypt_ratchet_keeps_invariant : Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws →
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
                  ∀ (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                    lifecycle.Session.decrypt_ratchet rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng') →
                      Tacenta.UnitLifecycleT3.SessionRefines dh K s' m' →
                        Tacenta.UnitLifecycleDecryptPreserve.ReceiveStep oracle m m' →
                          s'.invariant = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.decrypt_ratchet_keeps_invariant

/--
info: Tacenta.UnitLifecycleDecryptPreserve.decrypt_keeps_invariant : Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws →
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
                  ∀ (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                    lifecycle.Session.decrypt rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng') →
                      Tacenta.UnitLifecycleT3.SessionRefines dh K s' m' →
                        Tacenta.UnitLifecycleDecryptPreserve.ReceiveStep oracle m m' →
                          s'.invariant = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.decrypt_keeps_invariant

/--
info: Tacenta.UnitLifecycleDecryptPreserve.decrypt_keeps_invariant_model_step : Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws →
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
                  ∀ (msg : Slice U8) (msgM inner : Model.Lifecycle.Bytes),
                    Model.Lifecycle.dispatchDecrypt oracle m msgM = Except.ok inner →
                      (∀ (c : Model.CompositeHeader.Composite) (ct : List UInt8),
                          Model.CompositeHeader.decodeDetailed inner = Except.ok (c, ct) →
                            Tacenta.UnitLifecycleDecryptPreserve.InOrderOut m.triple (Model.Lifecycle.tripleHeaderOf c)
                              (Model.Lifecycle.sparseOutputOf
                                (Model.Braid.receive oracle.braidKem m.braid
                                      (Model.Lifecycle.braidMessageOf view m.braid c)).2.1)) →
                        ∀ (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                          lifecycle.Session.decrypt rc crc s msg rng = ok (core.result.Result.Ok pt, s', rng') →
                            Tacenta.UnitLifecycleT3.SessionRefines dh K s'
                                (Model.Lifecycle.decrypt view oracle m msgM).session →
                              s'.invariant = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom s' k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.decrypt_keeps_invariant_model_step

/--
info: @Tacenta.UnitLifecycleDecryptPreserve.inOrderOut_none : ∀ {m : Model.Triple.State} {h : Model.Triple.Header},
  Tacenta.UnitLifecycleReceivePreserve.InOrder m h → Tacenta.UnitLifecycleDecryptPreserve.InOrderOut m h none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.inOrderOut_none

/--
info: Tacenta.UnitLifecycleDecryptPreserve.receiveStep_of_inOrder : ∀ (oracle : Model.Lifecycle.Oracle)
  {m m' : Model.Lifecycle.Session},
  Tacenta.UnitLifecycleReceivePreserve.InOrderReceiveStep oracle m m' →
    ∀ (msgB : Model.Braid.Msg),
      (Model.Braid.receive oracle.braidKem m.braid msgB).2.2 = m'.braid →
        (m'.triple = m.triple → m'.ratchetPrivate = m.ratchetPrivate → m'.braid = m.braid) →
          Tacenta.UnitLifecycleDecryptPreserve.ReceiveStep oracle m m'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.receiveStep_of_inOrder

/--
info: @Tacenta.UnitLifecycleDecryptPreserve.initiator_receives_reply_via_general : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
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
                                                                                                              List.length
                                                                                                                      (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                        ptR) +
                                                                                                                    150 ≤
                                                                                                                  Model.Lifecycle.maxRatchetFrameLen →
                                                                                                                ∀
                                                                                                                  (rngR :
                                                                                                                    F),
                                                                                                                  oracleB.dhPublic
                                                                                                                        dB ≠
                                                                                                                      Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                        q.peerRatchetBytes →
                                                                                                                    Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix →
                                                                                                                      Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen →
                                                                                                                        Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len →
                                                                                                                          ∃
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
                                                                                                                                s''.invariant =
                                                                                                                                    ok
                                                                                                                                      true ∧
                                                                                                                                  ∀
                                                                                                                                    (j :
                                                                                                                                      ℕ),
                                                                                                                                    j +
                                                                                                                                          2 <
                                                                                                                                        U32.max →
                                                                                                                                      Tacenta.UnitLifecycleSendPreserve.CounterRoom
                                                                                                                                        s''
                                                                                                                                        j
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.initiator_receives_reply_via_general

/--
info: Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen_is : Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen ↔
  Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLenShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen_is

/--
info: Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len_is : Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len ↔
  Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2LenShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len_is

/--
info: Tacenta.UnitLifecycleDecryptPreserve.modelT3_keyPairEkVectorLen : Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLenShape
  Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.modelT3_keyPairEkVectorLen

/--
info: Tacenta.UnitLifecycleDecryptPreserve.modelT3_encapsulate2Len : Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2LenShape
  Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.modelT3_encapsulate2Len

/--
info: Tacenta.UnitLifecycleDecryptPreserve.prepared_receive_keeps_invariant : Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws →
  Tacenta.SessionUnitBraidT3.ErasureAgrees →
    ∀ {K : Model.Braid.Kem},
      Tacenta.SessionUnitBraidT3.KemLenAgrees K →
        Tacenta.SessionUnitBraidT3.BraidHkdfAgrees →
          Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip →
            ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
              (dh : Tacenta.UnitLifecycleT3.DhView),
              Tacenta.UnitLifecycleT3.DhCodecOf dh →
                ∀ (oracle : Model.Lifecycle.Oracle),
                  (∀ (secret : tacenta_boundary.dh.PrivateKey),
                      ∃ publicKey,
                        secret.public_key = ok publicKey ∧
                          dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)) →
                    ∀ {our : lifecycle.Identity} {store : lifecycle.PrekeyStore} {msg : Slice U8}
                      (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg) (rng : R)
                      (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                      lifecycle.Session.decrypt_ratchet rc crc p.session p.message rng =
                          ok (core.result.Result.Ok pt, s', rng') →
                        ∀ (m' : Model.Lifecycle.Session),
                          Tacenta.UnitLifecycleT3.SessionRefines dh K s' m' →
                            Tacenta.UnitLifecycleDecryptPreserve.ReceiveStep oracle
                                (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) m' →
                              s'.invariant = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.prepared_receive_keeps_invariant

/--
info: Tacenta.UnitLifecycleDecryptPreserve.establish_responder_keeps_invariant : Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws →
  Tacenta.SessionUnitBraidT3.ErasureAgrees →
    ∀ {K : Model.Braid.Kem},
      Tacenta.SessionUnitBraidT3.KemLenAgrees K →
        Tacenta.SessionUnitBraidT3.BraidHkdfAgrees →
          Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip →
            ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
              (dh : Tacenta.UnitLifecycleT3.DhView),
              Tacenta.UnitLifecycleT3.DhCodecOf dh →
                ∀ (oracle : Model.Lifecycle.Oracle),
                  (∀ (secret : tacenta_boundary.dh.PrivateKey),
                      ∃ publicKey,
                        secret.public_key = ok publicKey ∧
                          dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)) →
                    ∀ (our : lifecycle.Identity) (store : lifecycle.PrekeyStore) (msg : Slice U8) (rng : R)
                      (s' : lifecycle.Session) (pt : alloc.vec.Vec U8) (store' : lifecycle.PrekeyStore) (rng' : R),
                      lifecycle.establish_responder rc crc our store msg rng =
                          ok (core.result.Result.Ok (s', pt), store', rng') →
                        (∃ p,
                            lifecycle.Session.decrypt_ratchet rc crc p.session p.message rng =
                                ok (core.result.Result.Ok pt, s', rng') ∧
                              Tacenta.UnitLifecycleEstablishResponder.ResponderCommit store p.decoded.kem_prekey_id
                                p.decoded.one_time_prekey_id p.lastResort p.replay store') ∧
                          ∀ (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg),
                            lifecycle.Session.decrypt_ratchet rc crc p.session p.message rng =
                                ok (core.result.Result.Ok pt, s', rng') →
                              ∀ (m' : Model.Lifecycle.Session),
                                Tacenta.UnitLifecycleT3.SessionRefines dh K s' m' →
                                  Tacenta.UnitLifecycleDecryptPreserve.ReceiveStep oracle
                                      (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) m' →
                                    s'.invariant = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.establish_responder_keeps_invariant

/--
info: @Tacenta.UnitLifecycleDecryptPreserve.responder_first_frame_via_general : ∀ {RA : Type} {rcA : rand_core_1.RngCore RA}
  {crcA : rand_core_1.CryptoRng RA} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
  [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type} (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
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
                                                                            Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix →
                                                                              Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen →
                                                                                Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len →
                                                                                  sB'.invariant = ok true ∧
                                                                                    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                      sB'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptPreserve.responder_first_frame_via_general

/--
info: def Tacenta.UnitLifecycleDecryptPreserve.prefixIdx : tacenta_erasure.Decoder → ℕ → List ℕ :=
fun d j => List.map (fun c => ↑c.index) (List.take j ↑d.have)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.prefixIdx

/--
info: structure Tacenta.UnitLifecycleDecryptPreserve.BraidLens : Type
number of parameters: 0
fields:
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.c1 : Usize
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.ev : Usize
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.c2 : Usize
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.hl : Usize
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.n96 : Usize
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.n2 : Usize
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.hc1 : tacenta_kem.CT1_LEN = ok self.c1
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.hev : tacenta_kem.EK_VECTOR_LEN = ok self.ev
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.hc2 : tacenta_kem.CT2_LEN = ok self.c2
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.hhl : tacenta_kem.HEADER_LEN = ok self.hl
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.hn96 : self.hl + tacenta_braid.MAC_LEN = ok self.n96
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.hn2 : self.c2 + tacenta_braid.MAC_LEN = ok self.n2
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.hn96v : ↑self.n96 = ↑self.hl + 32
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.hn2v : ↑self.n2 = ↑self.c2 + 32
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.bc1 : ↑self.c1 ≤ 4096
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.bev : ↑self.ev ≤ 4096
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.bc2 : ↑self.c2 ≤ 4096
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.bhl : ↑self.hl ≤ 4096
constructor:
  Tacenta.UnitLifecycleDecryptPreserve.BraidLens.mk (c1 ev c2 hl n96 n2 : Usize) (hc1 : tacenta_kem.CT1_LEN = ok c1)
    (hev : tacenta_kem.EK_VECTOR_LEN = ok ev) (hc2 : tacenta_kem.CT2_LEN = ok c2) (hhl : tacenta_kem.HEADER_LEN = ok hl)
    (hn96 : hl + tacenta_braid.MAC_LEN = ok n96) (hn2 : c2 + tacenta_braid.MAC_LEN = ok n2) (hn96v : ↑n96 = ↑hl + 32)
    (hn2v : ↑n2 = ↑c2 + 32) (bc1 : ↑c1 ≤ 4096) (bev : ↑ev ≤ 4096) (bc2 : ↑c2 ≤ 4096) (bhl : ↑hl ≤ 4096) :
    Tacenta.UnitLifecycleDecryptPreserve.BraidLens
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.BraidLens

/--
info: def Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen : Prop :=
∀ (kp : tacenta_kem.IncrementalKeyPair) (v : alloc.vec.Vec U8),
  kp.ek_vector = ok v → ∃ n, tacenta_kem.EK_VECTOR_LEN = ok n ∧ v.length = ↑n
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen

/--
info: def Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len : Prop :=
∀ (es : tacenta_kem.EncapsState) (s : Slice U8) (c : alloc.vec.Vec U8),
  tacenta_kem.encapsulate2 es s = ok (core.result.Result.Ok c) → ∃ n, tacenta_kem.CT2_LEN = ok n ∧ c.length = ↑n
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len

/--
info: def Tacenta.UnitLifecycleDecryptPreserve.modelTag : Model.Braid.BraidState → ℕ :=
fun x =>
  match x with
  | Model.Braid.BraidState.keysUnsampled epoch auth => 0
  | Model.Braid.BraidState.keysSampled epoch auth dk ekVector hdrEnc => 1
  | Model.Braid.BraidState.headerSent epoch auth dk ct1Dec ekEnc => 2
  | Model.Braid.BraidState.ct1Received epoch auth dk ct1 ekEnc => 3
  | Model.Braid.BraidState.ekSentCt1Received epoch auth dk ct1 ct2Dec => 4
  | Model.Braid.BraidState.noHeaderReceived epoch auth hdrDec => 5
  | Model.Braid.BraidState.headerReceived epoch auth ekSeed hek ekDec => 6
  | Model.Braid.BraidState.ct1Sampled epoch auth ekSeed hek encapsSecret ct1 ct1Enc ekDec => 7
  | Model.Braid.BraidState.ekReceivedCt1Sampled epoch auth encapsSecret ct1 ekSeed ekVector ct1Enc => 8
  | Model.Braid.BraidState.ct1Acknowledged epoch auth ekSeed hek encapsSecret ct1 ekDec => 9
  | Model.Braid.BraidState.ct2Sampled epoch auth ct2Enc => 10
  | Model.Braid.BraidState.failed => 11
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.modelTag

/--
info: def Tacenta.UnitLifecycleDecryptPreserve.modelSendsHeader : Model.Braid.BraidState → Bool :=
fun x =>
  match x with
  | Model.Braid.BraidState.keysUnsampled epoch auth => true
  | Model.Braid.BraidState.keysSampled epoch auth dk ekVector hdrEnc => true
  | Model.Braid.BraidState.headerSent epoch auth dk ct1Dec ekEnc => true
  | Model.Braid.BraidState.ct1Received epoch auth dk ct1 ekEnc => true
  | Model.Braid.BraidState.ekSentCt1Received epoch auth dk ct1 ct2Dec => true
  | x => false
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.modelSendsHeader

/--
info: def Tacenta.UnitLifecycleDecryptPreserve.modelIsInit : Model.Braid.BraidState → Option Bool :=
fun st =>
  match st with
  | Model.Braid.BraidState.failed => none
  | x =>
    some
      (if Tacenta.UnitLifecycleDecryptPreserve.modelSendsHeader st = true then decide (st.epoch % 2 = 1)
      else decide ¬st.epoch % 2 = 1)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.modelIsInit

/--
info: def Tacenta.UnitLifecycleDecryptPreserve.ModelClauseB : ℕ → Model.Braid.BraidState → Prop :=
fun sp st =>
  st = Model.Braid.BraidState.failed ∨
    (7 ≤ Tacenta.UnitLifecycleDecryptPreserve.modelTag st ∧ Tacenta.UnitLifecycleDecryptPreserve.modelTag st ≤ 10 →
        sp = st.epoch) ∧
      (¬(7 ≤ Tacenta.UnitLifecycleDecryptPreserve.modelTag st ∧ Tacenta.UnitLifecycleDecryptPreserve.modelTag st ≤ 10) →
        sp + 1 = st.epoch)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.ModelClauseB

/--
info: def Tacenta.UnitLifecycleDecryptPreserve.advancedOf : Model.SparseRatchet.State →
  Option Model.SparseRatchet.Output → Option Model.SparseRatchet.State :=
fun st out =>
  match Model.SparseRatchet.maybeAdvanceReceiveDetailed st out with
  | Except.ok st1 => some st1
  | Except.error a => none
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.advancedOf

/--
info: def Tacenta.UnitLifecycleDecryptPreserve.InOrderOut : Model.Triple.State →
  Model.Triple.Header → Option Model.SparseRatchet.Output → Prop :=
fun m h out =>
  (Model.Ratchet.trySkipped m.classical h.dr = none ∧
      (m.classical.dhrPub = some h.dr.dh → h.dr.n ≤ m.classical.nr) ∧
        (m.classical.dhrPub ≠ some h.dr.dh →
          (m.classical.ckr = none ∨ m.classical.dhrPub = none ∨ h.dr.pn ≤ m.classical.nr) ∧ h.dr.n = 0)) ∧
    ∀ (st1 : Model.SparseRatchet.State),
      Tacenta.UnitLifecycleDecryptPreserve.advancedOf m.postQuantum out = some st1 →
        Tacenta.UnitLifecycleReceivePreserve.InOrder { classical := m.classical, postQuantum := st1 } h
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.InOrderOut

/--
info: def Tacenta.UnitLifecycleDecryptPreserve.ReceiveStep : Model.Lifecycle.Oracle →
  Model.Lifecycle.Session → Model.Lifecycle.Session → Prop :=
fun oracle m m' =>
  m'.triple = m.triple ∧ m'.ratchetPrivate = m.ratchetPrivate ∧ m'.braid = m.braid ∨
    ∃ msgB hdr dr ds cand mk,
      m'.braid = (Model.Braid.receive oracle.braidKem m.braid msgB).2.2 ∧
        Tacenta.UnitLifecycleDecryptPreserve.InOrderOut m.triple hdr
            (Model.Lifecycle.sparseOutputOf (Model.Braid.receive oracle.braidKem m.braid msgB).2.1) ∧
          Model.Messages.canonicalKey hdr.dr.dh = true ∧
            Model.Triple.receiveDetailed m.triple hdr dr ds (oracle.dhPublic cand)
                  (Model.Lifecycle.sparseOutputOf (Model.Braid.receive oracle.braidKem m.braid msgB).2.1) =
                Except.ok (m'.triple, mk) ∧
              m'.ratchetPrivate =
                if (m'.triple.classical.dhsPub == m.triple.classical.dhsPub) = true then m.ratchetPrivate else cand
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.ReceiveStep

/--
info: def Tacenta.UnitLifecycleDecryptPreserve.CodeClauseB : tacenta_triple.State → tacenta_braid.Braid → Prop :=
fun t b =>
  ∃ T E,
    b.state_tag = ok T ∧
      b.epoch = ok E ∧
        (7#u8 ≤ T ∧ T ≤ 10#u8 → t.post_quantum.epoch = E) ∧ (¬(7#u8 ≤ T ∧ T ≤ 10#u8) → ↑t.post_quantum.epoch + 1 = ↑E)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.CodeClauseB

/--
info: structure Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws : Prop
number of parameters: 0
fields:
  Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws.kemClone : Tacenta.SessionUnitBraidT3.KemCloneAgrees
  Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws.divCeil : Tacenta.SessionUnitDecoderBound.DivCeilValue
  Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws.truncate : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix
  Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws.headerLen : Tacenta.SessionUnitBraidT1.HeaderLenTotal
  Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws.ekVectorLen : Tacenta.SessionUnitBraidT1.EkVectorLenTotal
  Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws.ct1Len : Tacenta.SessionUnitBraidT1.Ct1LenTotal
  Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws.ct2Len : Tacenta.SessionUnitBraidT1.Ct2LenTotal
  Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws.keyPairEkVector : Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen
  Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws.encapsulate2Len : Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len
  Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws.optionEq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      @core.option.Option.Insts.CoreCmpPartialEqOption.eq
  Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws.dhPublicValid : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid
constructor:
  Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws.mk (kemClone : Tacenta.SessionUnitBraidT3.KemCloneAgrees)
    (divCeil : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (truncate : Tacenta.UnitSatisfiabilityBraidAgreements.TruncatePrefix)
    (headerLen : Tacenta.SessionUnitBraidT1.HeaderLenTotal) (ekVectorLen : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (ct1Len : Tacenta.SessionUnitBraidT1.Ct1LenTotal) (ct2Len : Tacenta.SessionUnitBraidT1.Ct2LenTotal)
    (keyPairEkVector : Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen)
    (encapsulate2Len : Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2Len)
    (optionEq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape @core.option.Option.Insts.CoreCmpPartialEqOption.eq)
    (dhPublicValid : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid) :
    Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.ReceiveInvariantLaws

/--
info: def Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLenShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀ (kp : I.IncrementalKeyPair) (v : alloc.vec.Vec U8),
    I.ikpEkVector kp = ok v → ∃ n, I.EK_VECTOR_LEN = ok n ∧ v.length = ↑n
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLenShape

/--
info: def Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2LenShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀ (es : I.EncapsState) (s : Slice U8) (c : alloc.vec.Vec U8),
    I.encapsulate2 es s = ok (core.result.Result.Ok c) → ∃ n, I.CT2_LEN = ok n ∧ c.length = ↑n
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptPreserve.Encapsulate2LenShape
