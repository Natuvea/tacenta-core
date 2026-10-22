import Translation.UnitLifecycleResponderFirstReceipt

/-!
# The responder's successor: `Session::invariant` and the four counter ceilings after the first receipt

`UnitLifecycleResponderFirstReceipt` feeds the bytes the initiator's first `encrypt` emits to the responder's
`establish_responder` and shows that the call either refuses with one of the three refusals the store decides, or
succeeds and returns a session that refines the model's step (`firstReceiptSession`).  This module proves, for that
same returned session, the two session-side facts the relation does not give: `Session::invariant` returns `true`
there, and the four counter ceilings (`CounterHeadroom`) hold.  With the relation, these are every session-side
premise `decrypt_ratchet_refines_of_invariant` takes.

## How

No theorem in the tree says that a receive keeps `Session::invariant` (the lifecycle theorems are single-step), so
the invariant is proved for this frame's path, the first receive at the responder's prepared session, and not
through a general preservation theorem:
* `decrypt_ratchet_ok_parts`: a successful translated `decrypt_ratchet` returns the session it was given with the
  Triple candidate, the agreement candidate `Braid::receive` returned, and the ratchet private key replaced by the
  drawn candidate exactly when the Triple's sending key changed; the candidate's public key bytes are the ones the
  call computed from the draw.
* `triple_eq_received`: the relation to the model's `receiverAfterFirst` fixes every counter and store of the code's
  Triple, by injectivity of the byte reading, and leaves the root and chain keys open (`receivedTriple`: classical
  clock 1, one message received, both classical chains open, the peer key the model's; the sparse receiving chain at
  counter 1 and the sending chain at 0 at epoch 0; both stores empty; direction `B2a`).
* `first_receipt_successor_shape`: the Triple's new sending key is the drawn candidate's public key bytes, from the
  relation, the responder's oracle record (`dhPublic`, `random32`) and the view's codec relation; when the sending key
  did not change, the private key and the sending key are the prepared session's.  The relation fixes the agreement's
  state (`NoHeaderReceived` at epoch 1) but not its decoder, since the decoder relation is behavioural.  The walk of
  `Braid::receive` at that state (`braid_receive_noHeader`; a decoder's clone is the decoder, `erasureCloneAgrees`)
  gives the fresh header decoder or one `add_chunk` of it.  Such a decoder holds at most one chunk and passes
  `Decoder::invariant` (`decoder_invariant_small`, `one_chunk_loop`) and the size check (`received_decoder_checks`).
* The clauses about fields the receive does not write (associated data, identities, established ephemeral, no pending
  initial message) are discharged from the prepared parts, as at the prepared session (`structural_received`,
  `received_invariant`); the ceilings are read off the shape (`received_counterHeadroom`).

## The statements

* `first_receipt_successor_shape`, `first_receipt_successor_facts`: for parts of the responder's prepare phase, a
  successful inner `decrypt_ratchet` at the prepared session, and a returned session that refines a
  `firstReceiptSession` whose peer ratchet key is the bytes of a canonical key: the session is `receivedSession` of the
  parts, and it passes `Session::invariant` and meets the four ceilings.
* `responder_first_frame_successor`: under the hypotheses of `responder_first_frame_succeeds` without the store bound,
  and the call's success equation, the relation, the invariant and the ceilings at the session the call returned.
* `initiator_first_send_responder_successor_hypotheses`, `initiator_first_send_responder_successor_admissible`,
  `initiator_first_send_responder_successor_counterHeadroom`: the same at the session `establish_responder` returns on
  the bytes a successful first `encrypt` at an establishment output emitted.
* `first_send_receive_successor_reachable`: the reach run of the receipt module, now with the invariant and the
  ceilings at the responder's session.

## Laws and premises

No new law and no new per-run premise.  The statements take the hypotheses of `initiator_first_send_responder_receives`
(or of `responder_first_frame_succeeds`) except the store bound `EstablishResponderHeadroom`, which the call's success
equation makes unnecessary, and add that equation.  The invariant uses `DhPublicValid` and `OptionEqU64Shape`, already
hypotheses there, and `DivCeilValue` and the header-length bound, both fields of the responder's contracts.  The
responder's oracle record and the view's codec relation enter only to tie the drawn candidate's public key to the
Triple's new sending key.

## Trust

The four composed results and the reach rest on the kernel and opaque constants, like every lemma before them (pins below);
until 2026-10-21 they also rested on the nine `native_decide` constants of the encrypt and decrypt refinements, which
they reach through `responder_first_frame_inner_succeeds` and `established_encrypt_outcomes`, kernel proofs since.

## Non-vacuity

No law is added, so `first_receipt_laws_model` already puts every law the statements take in one interpretation.
`first_send_receive_successor_reachable` exhibits, at the real constants under the reach's laws, one run (last-resort
path, empty plaintext) whose responder session passes the invariant and meets the ceilings.

## What it does not show

* That a receive keeps the invariant in general, or at any later message: only this first receive at the responder's
  prepared session is covered.
* The responder's reply (its `encrypt` at this session is `UnitLifecycleResponderReply`'s), the initiator's receipt of
  it (`UnitLifecycleResponderReplyReceipt`'s), a second message from the initiator, a second delivery of the same bytes
  (`UnitLifecycleResponderRepeatedFrame` takes it at this session), a tampered frame.
* The premises of the next decrypt that are not about the session: the next frame's chunk relation, `HonestChunk`
  (at `NoHeaderReceived` with a chunk held, a condition on the next header chunk), the draw and the boundary records.
* That the model session the successor refines holds only bytes the responder received: the relation is the receipt
  module's, at the view that attributes the received codeword.  The invariant and the ceilings are statements about
  the code's session and do not mention the view.
* That the real primitives meet the laws the receipt rests on (`AeadRoundTrip`, `DhAgreeContributory`,
  `DhAgreeSymmetric`), that ML-KEM decapsulation agrees on a run (`FirstKemAgrees`), or `PrekeyIdsDistinct` from
  `PrekeyStore::invariant`; the model's own `establishResponder` equality; the one-time path in a run.  The results list
  no compiler-trust axiom: the encrypt wrapper's nine `native_decide` constants are kernel proofs since 2026-10-21.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv bind2_eq_ok_inv bind3_eq_ok_inv)

namespace Tacenta.UnitLifecycleResponderSuccessor

/-! ## The success walk of `decrypt_ratchet` -/

/-- **What a successful `decrypt_ratchet` writes, and where its new ratchet key comes from**: the agreement is the
candidate `Braid::receive` returned on some message, the source after the call is what `random_secret` left, the
candidate key is `from_bytes` of the drawn value with public key `pkb` and bytes `new`, and the returned session is the
given one with the Triple and agreement replaced and, exactly when the Triple's sending key changed, the ratchet private
key replaced by the candidate.  Hypothesis-free. -/
theorem decrypt_ratchet_ok_parts {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (s : lifecycle.Session) (message : Slice U8) (rng : R) (v : alloc.vec.Vec U8)
    (s' : lifecycle.Session) (rng' : R)
    (h : lifecycle.Session.decrypt_ratchet rc crc s message rng =
      ok (core.result.Result.Ok v, s', rng')) :
    ∃ m x y bc a ck pkb new,
      tacenta_braid.Braid.receive s.braid m = ok (x, y, bc) ∧
      lifecycle.random_secret rc crc rng = ok (a, rng') ∧
      tacenta_boundary.dh.PrivateKey.from_bytes a = ok ck ∧
      tacenta_boundary.dh.PrivateKey.public_key ck = ok pkb ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok new ∧
      ((s'.triple.classical.dhs_pub ≠ s.triple.classical.dhs_pub ∧
          s' = { s with triple := s'.triple, braid := bc, ratchet_private := ck }) ∨
        (s'.triple.classical.dhs_pub = s.triple.classical.dhs_pub ∧
          s' = { s with triple := s'.triple, braid := bc })) := by
  unfold lifecycle.Session.decrypt_ratchet at h
  obtain ⟨fb, -, h⟩ := bind_eq_ok_inv h
  split at h
  · simp at h
  obtain ⟨r, -, h⟩ := bind_eq_ok_inv h
  rcases r with decoded | err
  swap
  · simp at h
  try dsimp only at h
  obtain ⟨m, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨⟨x, y, bc⟩, hrecv, h⟩ := bind_eq_ok_inv h
  try dsimp only at h
  obtain ⟨so, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨peer, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨o, -, h⟩ := bind_eq_ok_inv h
  rcases o with _ | secret
  · simp at h
  try dsimp only at h
  obtain ⟨dr, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨⟨a, rng1⟩, hrand, h⟩ := bind_eq_ok_inv h
  try dsimp only at h
  obtain ⟨ck, hck, h⟩ := bind_eq_ok_inv h
  obtain ⟨o1, -, h⟩ := bind_eq_ok_inv h
  rcases o1 with _ | secret1
  · simp at h
  try dsimp only at h
  obtain ⟨ds, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨before, hbefore, h⟩ := bind_eq_ok_inv h
  obtain ⟨hdr, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨pkb, hpkb, h⟩ := bind_eq_ok_inv h
  obtain ⟨new, hnew, h⟩ := bind_eq_ok_inv h
  obtain ⟨received, -, h⟩ := bind_eq_ok_inv h
  rcases received with ⟨tc, mk⟩ | err
  swap
  · simp at h
  try dsimp only at h
  obtain ⟨mk1, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨a1, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨t, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨keys, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨⟨enc, mac, iv⟩, -, h⟩ := bind_eq_ok_inv h
  try dsimp only at h
  obtain ⟨ad, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨r1, -, h⟩ := bind_eq_ok_inv h
  rcases r1 with value1 | e1
  swap
  · simp at h
  try dsimp only at h
  obtain ⟨a2, ha2, h⟩ := bind_eq_ok_inv h
  simp only [tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public, ok.injEq]
    at hbefore ha2
  subst hbefore ha2
  obtain ⟨e, he, hiff⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitT3.array_ne_val tc.classical.dhs_pub s.triple.classical.dhs_pub)
  rw [he] at h
  simp only [Aeneas.Std.bind_tc_ok] at h
  refine ⟨m, x, y, bc, a, ck, pkb, new, hrecv, ?_, hck, hpkb, hnew, ?_⟩
  · split at h <;> (simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, -, rfl⟩ := h; exact hrand)
  · split at h
    · rename_i hb
      simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact Or.inl ⟨hiff.mp hb, rfl⟩
    · rename_i hb
      simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      refine Or.inr ⟨?_, rfl⟩
      by_contra hne
      exact hb (hiff.mpr hne)

/-! ## The header decoder after the first chunk -/

/-- **`Braid::receive` at `NoHeaderReceived` leaves the decoder or adds one chunk to it**: if the returned agreement is
still waiting for the header, its decoder is the one given or the result of one `add_chunk` on it.  The state's clone
keeps the decoder (`erasureCloneAgrees`).  Hypothesis-free. -/
theorem braid_receive_noHeader (epoch : U64) (auth : tacenta_braid.Auth) (d : tacenta_erasure.Decoder)
    (m : tacenta_braid.Msg) (x : U64) (y : Option tacenta_braid.Output) (b' : tacenta_braid.Braid)
    (h : tacenta_braid.Braid.receive ⟨tacenta_braid.State.NoHeaderReceived epoch auth d⟩ m = ok (x, y, b'))
    (e' : U64) (a' : tacenta_braid.Auth) (d' : tacenta_erasure.Decoder)
    (hb : b'.state = tacenta_braid.State.NoHeaderReceived e' a' d') :
    d' = d ∨ ∃ c r, tacenta_erasure.Decoder.add_chunk d c = ok (r, d') := by
  unfold tacenta_braid.Braid.receive at h
  obtain ⟨st, hst, h⟩ := bind_eq_ok_inv h
  obtain ⟨⟨out, next⟩, hstep, h⟩ := bind_eq_ok_inv h
  have hnext : b'.state = next := by
    rcases out with _ | o
    · obtain ⟨i, -, h⟩ := bind_eq_ok_inv h
      simp only [ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.2]
    · obtain ⟨o1, -, h⟩ := bind_eq_ok_inv h
      simp only [ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.2]
  rw [hnext] at hb
  subst hb
  unfold tacenta_braid.State.Insts.CoreCloneClone.clone at hst
  obtain ⟨i, -, hst⟩ := bind_eq_ok_inv hst
  obtain ⟨a, -, hst⟩ := bind_eq_ok_inv hst
  obtain ⟨dd, hdd, hst⟩ := bind_eq_ok_inv hst
  have hdd' := Tacenta.UnitSatisfiabilityErasureAgrees.erasureCloneAgrees.2 d dd hdd
  rw [hdd'] at hst
  simp only [ok.injEq] at hst
  subst hst
  unfold tacenta_braid.Braid.step_receive at hstep
  obtain ⟨ep, -, hstep⟩ := bind_eq_ok_inv hstep
  dsimp only at hstep
  split at hstep
  · obtain ⟨b, -, hstep⟩ := bind_eq_ok_inv hstep
    split at hstep
    · split at hstep
      · simp only [ok.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, hstep⟩ := hstep
        cases hstep
        exact Or.inl rfl
      · rename_i c _
        obtain ⟨⟨r, hd1⟩, hadd, hstep⟩ := bind_eq_ok_inv hstep
        obtain ⟨o, -, hstep⟩ := bind_eq_ok_inv hstep
        split at hstep
        · simp only [ok.injEq, Prod.mk.injEq] at hstep
          obtain ⟨-, hstep⟩ := hstep
          cases hstep
          exact Or.inr ⟨c, r, hadd⟩
        · repeat' first
            | (replace hstep := bind_eq_ok_inv hstep; obtain ⟨_, _, hstep⟩ := hstep)
            | split at hstep
            | (simp only [ok.injEq, Prod.mk.injEq] at hstep; obtain ⟨-, hstep⟩ := hstep; cases hstep)
    · simp only [ok.injEq, Prod.mk.injEq] at hstep
      obtain ⟨-, hstep⟩ := hstep
      cases hstep
      exact Or.inl rfl
  · simp only [ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨-, hstep⟩ := hstep
    cases hstep
    exact Or.inl rfl

/-- The loop of `Decoder::invariant` over a decoder holding exactly one chunk returns its size, `needed`, chunk list
and `true` (the one index is distinct). -/
theorem one_chunk_loop (d : tacenta_erasure.Decoder) (c : tacenta_erasure.Chunk)
    (hv : d.«have».val = [c]) :
    tacenta_erasure.Decoder.invariant_loop d (Array.repeat 8192#usize 0#u8) true 0#usize
      ⦃ fun r => r = (d.size, d.needed, d.«have», true) ⦄ := by
  unfold tacenta_erasure.Decoder.invariant_loop
  apply loop.spec_decr_nat
    (measure := fun p => d.«have».val.length - p.2.2.val)
    (inv := fun p => (p.2.2.val = 0 ∧ p.2.1 = true ∧ p.1 = Array.repeat 8192#usize 0#u8) ∨
      (p.2.2.val = 1 ∧ p.2.1 = true))
  · rintro ⟨sn, dd, j⟩ hj
    simp only at hj ⊢
    unfold tacenta_erasure.Decoder.invariant_loop.body
    have hlen : d.«have».len.val = 1 := by simp [alloc.vec.Vec.len, hv]
    rcases hj with ⟨hj, h1, h2⟩ | ⟨hj, h1⟩
    · rw [h1, h2]
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
    · rw [h1]
      have hlt : ¬ j < d.«have».len := by scalar_tac
      simp only [hlt, if_false]
      step*
  · left; exact ⟨rfl, rfl, rfl⟩

/-- **A decoder holding at most one chunk passes `Decoder::invariant`**, when its `needed` is the chunk count of its
size, at most `MAX_CODEWORDS`, and not below the number of chunks held. -/
theorem decoder_invariant_small (d : tacenta_erasure.Decoder)
    (hcc : tacenta_erasure.chunk_count d.size = ok d.needed) (hle : d.needed.val ≤ 65536)
    (hlen : d.«have».val.length ≤ 1) (hn : d.«have».val.length ≤ d.needed.val) :
    tacenta_erasure.Decoder.invariant d = ok true := by
  have hloop : tacenta_erasure.Decoder.invariant_loop d (Array.repeat 8192#usize 0#u8) true 0#usize =
      ok (d.size, d.needed, d.«have», true) := by
    rcases hv : d.«have».val with _ | ⟨c, _ | ⟨c', rest⟩⟩
    · unfold tacenta_erasure.Decoder.invariant_loop
      rw [loop.eq_def]
      simp [tacenta_erasure.Decoder.invariant_loop.body, alloc.vec.Vec.len, hv]
    · obtain ⟨r, hr, hp⟩ := Std.WP.spec_imp_exists (one_chunk_loop d c hv)
      rw [hr, hp]
    · rw [hv] at hlen; simp at hlen
  unfold tacenta_erasure.Decoder.invariant
  dsimp only
  rw [hloop]
  have hm : tacenta_erasure.MAX_CODEWORDS.val = 65536 := by simp [tacenta_erasure.MAX_CODEWORDS]
  simp [hcc, hm, hle, hn, alloc.vec.Vec.len]

/-- `add_chunk` on a decoder holding no chunk keeps its size and `needed` and leaves at most one chunk, and no more
chunks than `needed`. -/
theorem add_chunk_fresh_have (d d' : tacenta_erasure.Decoder) (c : tacenta_erasure.Chunk) (r : Bool)
    (hv : d.«have».val = []) (h : tacenta_erasure.Decoder.add_chunk d c = ok (r, d')) :
    d'.size = d.size ∧ d'.needed = d.needed ∧ d'.«have».val.length ≤ 1 ∧
      d'.«have».val.length ≤ d.needed.val := by
  unfold tacenta_erasure.Decoder.add_chunk at h
  by_cases hge : alloc.vec.Vec.len d.«have» ≥ d.needed
  · simp only [hge, if_true, ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [hv]
  · simp only [hge, if_false] at h
    obtain ⟨⟨b, v⟩, hloop, h⟩ := bind_eq_ok_inv h
    simp at h
    obtain ⟨-, rfl⟩ := h
    unfold tacenta_erasure.Decoder.add_chunk_loop at hloop
    rw [loop.eq_def] at hloop
    simp only [tacenta_erasure.Decoder.add_chunk_loop.body, alloc.vec.Vec.len, hv] at hloop
    simp at hloop
    rcases hpush : alloc.vec.Vec.push d.«have» c with v1 | e | -
    all_goals (rw [hpush] at hloop; simp at hloop)
    obtain ⟨-, rfl⟩ := hloop
    have := Tacenta.UnitLifecycleEstablishResponder.vec_push_ok hpush
    rw [hv] at this
    have hlt : (0 : Nat) < d.needed.val := by
      simp only [alloc.vec.Vec.len, hv, ge_iff_le, not_le] at hge
      scalar_tac
    refine ⟨rfl, rfl, by simp [this], by simp [this]; omega⟩

open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts) in
/-- **The decoder the agreement holds after the first receive passes the Braid's checks**: for the prepare phase's
parts, every `NoHeaderReceived` state `Braid::receive` returns from the prepared agreement holds a decoder that passes
`Decoder::invariant` and is sized for the header and its MAC, under `DivCeilValue` and the header-length bound. -/
theorem received_decoder_checks (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (hhdr : Tacenta.SessionUnitBraidT1.HeaderLenTotal) {ourB : lifecycle.Identity}
    {storeB : lifecycle.PrekeyStore} {msg : Slice U8} (p : ResponderPreparedParts ourB storeB msg)
    (m : tacenta_braid.Msg) (x : U64) (y : Option tacenta_braid.Output) (bc : tacenta_braid.Braid)
    (hrecv : tacenta_braid.Braid.receive p.braid m = ok (x, y, bc))
    (e : U64) (a : tacenta_braid.Auth) (d' : tacenta_erasure.Decoder)
    (hb : bc.state = tacenta_braid.State.NoHeaderReceived e a d') :
    tacenta_erasure.Decoder.invariant d' = ok true ∧
      (do
        let i ← tacenta_kem.HEADER_LEN
        let i1 ← i + tacenta_braid.MAC_LEN
        tacenta_braid.decoder_sized d' i1) = ok true := by
  obtain ⟨auth, d, hd, hbraid⟩ := Tacenta.UnitLifecycleEstablishResponder.braid_responder_ok _ _ p.hBraid
  rw [hbraid] at hrecv
  obtain ⟨hdinv, hsized⟩ := Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_checks hdiv hhdr d hd
  rcases braid_receive_noHeader 1#u64 auth d m x y bc hrecv e a d' hb with rfl | ⟨c, r, hadd⟩
  · exact ⟨hdinv, hsized⟩
  obtain ⟨hv, n, needed, -, -, -, hcc, rfl⟩ := Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_ok d hd
  have hle := Tacenta.SessionUnitDecoderBound.invariant_true_needed_le _ hdinv
  obtain ⟨hs, hn, hl1, hln⟩ := add_chunk_fresh_have _ d' c r (by simp) hadd
  refine ⟨decoder_invariant_small d' (by rw [hs, hn]; exact hcc) (by rw [hn]; exact hle) hl1
    (by rw [hn]; exact hln), ?_⟩
  simpa [tacenta_braid.decoder_sized, tacenta_erasure.Decoder.impl.size, hs] using hsized

open Tacenta.UnitLifecycleEstablishInitiatorShape (singleton_length_le)

/-! ## The Triple after the first receive -/

/-- The sparse chain table after the first receive on the responder's side: the epoch-0 entry, sending chain at counter
0, receiving chain at counter 1, with the chain keys as arguments. -/
def receivedChains (c2 cr : Array U8 32#usize) : alloc.vec.Vec (U64 × tacenta_spqr.Chains) :=
  Tacenta.UnitHeadroomSatisfiable.vecOf
    [(0#u64, { send := some { ck := c2, n := 0#u64 }, receive := some { ck := cr, n := 1#u64 } })]
    (singleton_length_le _)

/-- The Triple state after the responder's first receive, with the keys as arguments: our new ratchet key `dhs`, the
peer's `dhr`, both classical chains, one message received and the clock at 1; the sparse table `receivedChains` at
epoch 0, both stores empty, direction `B2a`. -/
def receivedTriple (dhs dhr rk cks ckr prk c2 cr : Array U8 32#usize) : tacenta_triple.State :=
  { classical :=
      { dhs_pub := dhs, dhr_pub := some dhr, rk := rk, cks := some cks, ckr := some ckr,
        ns := 0#u32, nr := 1#u32, pn := 0#u32, skipped := alloc.vec.Vec.new tacenta_ratchet.SkippedKey,
        events := 1#u32, labels := tacenta_ratchet.LabelSet.Tacenta },
    post_quantum :=
      { rk := prk, epoch := 0#u64, chains := receivedChains c2 cr,
        skipped := alloc.vec.Vec.new tacenta_spqr.Skipped, direction := tacenta_spqr.Direction.B2a } }

open Tacenta.UnitLifecycleResponderFirstReceipt (receiverAfterFirst) in
/-- **The relation to the model's Triple after the first receive fixes the code's Triple up to its keys**: a Triple that
refines `receiverAfterFirst` is `receivedTriple` of some keys, whose sending key reads as the model's new public key and
whose peer key reads as the model's `a4`.  Hypothesis-free. -/
theorem triple_eq_received (ec prk k1 k2 a4 d dSend newPub : Model.State.Key) (t : tacenta_triple.State)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
      Tacenta.SessionUnitTripleT3.spqrAbs t (receiverAfterFirst ec prk k1 k2 a4 d dSend newPub)) :
    ∃ dhs dhr rk cks ckr prk' c2 cr, t = receivedTriple dhs dhr rk cks ckr prk' c2 cr ∧
      Tacenta.UnitLifecycleT3.arrayOf dhs = newPub ∧ Tacenta.UnitLifecycleT3.arrayOf dhr = a4 := by
  obtain ⟨hc, hq⟩ := hrel
  obtain ⟨⟨dhs, dhr, rk, cks, ckr, ns, nr, pn, sk, ev, lab⟩, ⟨prk', ep, ch, ssk, dir⟩⟩ := t
  simp [Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs, receiverAfterFirst] at hc hq
  obtain ⟨hdhs, ⟨a, rfl, hdhr⟩, -, ⟨cks', rfl, -⟩, ⟨ckr', rfl, -⟩, hns, hnr, hpn, hsk, hev⟩ := hc
  obtain ⟨-, hep, ⟨e0, ⟨bs, br⟩, hch, hab⟩, hssk, hdir⟩ := hq
  simp only [Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf,
    Prod.mk.injEq, Model.SparseRatchet.Chains.mk.injEq] at hab
  obtain ⟨ha, hbs, hbr⟩ := hab
  rcases bs with _ | ⟨sck, sn⟩
  · simp at hbs
  rcases br with _ | ⟨rck, rn⟩
  · simp at hbr
  simp only [Option.map_some, Option.some.injEq, Tacenta.SessionUnitSpqrT3.chainOf,
    Model.SparseRatchet.Chain.mk.injEq] at hbs hbr
  obtain ⟨-, hsn⟩ := hbs
  obtain ⟨-, hrn⟩ := hbr
  cases lab
  cases dir <;> simp [Tacenta.SessionUnitSpqrT3.directionOf] at hdir
  have hns' : ns = 0#u32 := UScalar.eq_of_val_eq (by simpa using hns)
  have hnr' : nr = 1#u32 := UScalar.eq_of_val_eq (by simpa using hnr)
  have hpn' : pn = 0#u32 := UScalar.eq_of_val_eq (by simpa using hpn)
  have hev' : ev = 1#u32 := UScalar.eq_of_val_eq (by simpa using hev)
  have hep' : ep = 0#u64 := UScalar.eq_of_val_eq (by simpa using hep)
  have ha' : e0 = 0#u64 := UScalar.eq_of_val_eq (by simpa using ha)
  have hsn' : sn = 0#u64 := UScalar.eq_of_val_eq (by simpa using hsn)
  have hrn' : rn = 1#u64 := UScalar.eq_of_val_eq (by simpa using hrn)
  subst hns' hnr' hpn' hev' hep' ha' hsn' hrn'
  have hsk' : sk = alloc.vec.Vec.new tacenta_ratchet.SkippedKey := Subtype.ext hsk
  have hssk' : ssk = alloc.vec.Vec.new tacenta_spqr.Skipped := Subtype.ext hssk
  have hch' : ch = receivedChains sck rck := Subtype.ext hch
  subst hsk' hssk' hch'
  exact ⟨dhs, a, rk, cks', ckr', prk', sck, rck, rfl, hdhs, hdhr⟩

/-- `Triple::invariant` of `receivedTriple`, given its two public keys are canonical. -/
theorem receivedTriple_invariant (dhs dhr rk cks ckr prk c2 cr : Array U8 32#usize)
    (hs : Tacenta.SessionUnitT1.canonicalX25519 dhs = true)
    (hr : Tacenta.SessionUnitT1.canonicalX25519 dhr = true) :
    tacenta_triple.State.invariant (receivedTriple dhs dhr rk cks ckr prk c2 cr) = ok true := by
  have h1 : tacenta_ratchet.State.invariant
      (receivedTriple dhs dhr rk cks ckr prk c2 cr).classical = ok true := by
    rw [Tacenta.SessionUnitRatchetImportInv.Ratchet.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [receivedTriple, alloc.vec.Vec.new, tacenta_ratchet.MAX_SKIPPED_STORE]
    · simp [receivedTriple, U32.max_eq]
    · simp [receivedTriple, alloc.vec.Vec.new]
    · simp [receivedTriple, alloc.vec.Vec.new]
    · simp [receivedTriple]
    · simpa [receivedTriple] using hs
    · simpa [receivedTriple] using hr
    · simp [receivedTriple, alloc.vec.Vec.new]
  have h2 : tacenta_spqr.State.invariant
      (receivedTriple dhs dhr rk cks ckr prk c2 cr).post_quantum = ok true := by
    rw [Tacenta.SessionUnitRatchetImportInv.Spqr.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [receivedTriple, alloc.vec.Vec.new, tacenta_spqr.MAX_SKIPPED_STORE]
    · simp [receivedTriple, receivedChains, Tacenta.UnitHeadroomSatisfiable.vecOf,
        core.num.U64.saturating_add, UScalar.saturating_add, tacenta_spqr.EPOCHS_KEPT, U64.max_eq]
      decide
    · simp [receivedTriple, receivedChains, Tacenta.UnitHeadroomSatisfiable.vecOf]
    · simp [receivedTriple, receivedChains, Tacenta.UnitHeadroomSatisfiable.vecOf]
    · simp [receivedTriple, alloc.vec.Vec.new]
    · simp [receivedTriple, alloc.vec.Vec.new]
  simp only [receivedTriple] at h1 h2
  unfold tacenta_triple.State.invariant
  simp [h1, h2, receivedTriple, tacenta_spqr.State.impl.direction,
    tacenta_ratchet.State.started_as_sender]

open Tacenta.UnitHeadroomInvariant (OptionEqU64Shape vec_ne_self array_ne_self)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid dhPublicValid_canonical
  dhPublicValid_valid identity_public_valid)
open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts curve_inputs_ok)

/-! ## The session after the first receive -/

/-- The session after the responder's first receive, from the prepare phase's parts: the given Triple, the agreement at
`NoHeaderReceived` epoch 1 with the given decoder, the given ratchet private key, every other field the prepared
session's. -/
def receivedSession {our : lifecycle.Identity} {store : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts our store msg) (t : tacenta_triple.State) (auth : tacenta_braid.Auth)
    (dec : tacenta_erasure.Decoder) (rp : tacenta_boundary.dh.PrivateKey) : lifecycle.Session :=
  { p.session with
    triple := t
    braid := ⟨tacenta_braid.State.NoHeaderReceived 1#u64 auth dec⟩
    ratchet_private := rp }

/-- `Session::structural_invariant` of `receivedSession` at a `receivedTriple`, when the ratchet private key's public
key bytes are the Triple's sending key: as at the prepared session, with the new keys. -/
theorem structural_received (hpub : DhPublicValid)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {our : lifecycle.Identity} {store : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts our store msg) (dhs dhr rk cks ckr prk c2 cr : Array U8 32#usize)
    (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder) (rp : tacenta_boundary.dh.PrivateKey)
    (pk : tacenta_boundary.dh.PublicKeyBytes)
    (hrp : tacenta_boundary.dh.PrivateKey.public_key rp = ok pk)
    (hpk : tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok dhs) :
    lifecycle.Session.structural_invariant
      (receivedSession p (receivedTriple dhs dhr rk cks ckr prk c2 cr) auth dec rp) = ok true := by
  obtain ⟨-, hvalid, hdecEph⟩ := curve_inputs_ok _ _ _ _ p.hCurve
  have hv := identity_public_valid hpub p.hOurPublic
  have heph := p.ephemeralCopy_eq
  unfold lifecycle.Session.structural_invariant
  simp [receivedSession, Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.session, heph,
    hrp, hpk, receivedTriple, tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public,
    array_ne_self, tacenta_braid.Braid.failed, tacenta_braid.Braid.is_initiator, tacenta_braid.State.epoch,
    lifecycle.Session.is_responder, p.hIdentityAd, vec_ne_self, tacenta_triple.State.direction,
    tacenta_spqr.State.impl.direction, hv, hvalid, hdecEph,
    tacenta_braid.Braid.epoch, tacenta_triple.State.epoch, tacenta_spqr.State.impl.epoch,
    tacenta_braid.Braid.state_tag, lift, tacenta_spqr.Direction.Insts.CoreCmpPartialEqDirection.eq]
  have h01 : U64.checked_add 0#u64 1#u64 = some 1#u64 := by decide
  rw [h01, hoeq]
  have hmod : (1#u64 % 2#u64 : Result U64) = ok 1#u64 := by
    obtain ⟨z, hz, hzv⟩ := Std.WP.spec_imp_exists (UScalar.rem_spec 1#u64 (y := 2#u64) (by decide))
    have hz1 : z = 1#u64 := by apply UScalar.eq_of_val_eq; simp at hzv ⊢; omega
    rw [hz, hz1]
  simp [hmod, tacenta_spqr.Direction.read_discriminant]

/-- **`Session::invariant` of `receivedSession`** at a `receivedTriple` whose peer key is canonical, whose sending key
is the ratchet private key's public key bytes, and whose decoder passes the Braid's two checks. -/
theorem received_invariant (hpub : DhPublicValid)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {our : lifecycle.Identity} {store : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts our store msg) (dhs dhr rk cks ckr prk c2 cr : Array U8 32#usize)
    (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder) (rp : tacenta_boundary.dh.PrivateKey)
    (pk : tacenta_boundary.dh.PublicKeyBytes)
    (hrp : tacenta_boundary.dh.PrivateKey.public_key rp = ok pk)
    (hpk : tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok dhs)
    (hdhr : Tacenta.SessionUnitT1.canonicalX25519 dhr = true)
    (hdinv : tacenta_erasure.Decoder.invariant dec = ok true)
    (hsized : (do
        let i ← tacenta_kem.HEADER_LEN
        let i1 ← i + tacenta_braid.MAC_LEN
        tacenta_braid.decoder_sized dec i1) = ok true) :
    lifecycle.Session.invariant
      (receivedSession p (receivedTriple dhs dhr rk cks ckr prk c2 cr) auth dec rp) = ok true := by
  unfold lifecycle.Session.invariant
  rw [structural_received hpub hoeq p dhs dhr rk cks ckr prk c2 cr auth dec rp pk hrp hpk]
  simp only [Aeneas.Std.bind_tc_ok, if_true]
  unfold lifecycle.Session.leaf_invariants
  have hs := dhPublicValid_canonical hpub hrp hpk
  simp only [receivedSession]
  rw [receivedTriple_invariant _ _ _ _ _ _ _ _ hs hdhr]
  simp only [Aeneas.Std.bind_tc_ok, if_true, tacenta_braid.Braid.invariant]
  simp [hdinv]
  exact hsized

open Tacenta.UnitLifecycleT3 (DhView DhCodecOf arrayOf SessionRefines)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf)
open Tacenta.UnitLifecycleEstablishResponder (responderModelOf)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstReceiptSession)

/-! ## From the relation and the walk -/

/-- **The session a successful inner receive returns at the prepared session, when it refines `firstReceiptSession`**:
it is `receivedSession` of the parts at a `receivedTriple` whose peer key is `a4`, with a ratchet private key whose
public key bytes are the Triple's sending key, and a decoder that passes the Braid's two checks.  Under `DivCeilValue`,
the header-length bound, the responder's oracle record and the view's codec relation, and the per-run premise that the
responder's trace holds the draw. -/
theorem first_receipt_successor_shape (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (hhdr : Tacenta.SessionUnitBraidT1.HeaderLenTotal) {E : Type} (rcB : rand_core_1.RngCore E)
    (crcB : rand_core_1.CryptoRng E) {dh : DhView} (codec : DhCodecOf dh)
    {traceB : E → List Model.Lifecycle.Key} {oracleB : Model.Lifecycle.Oracle}
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB) {K : Model.Braid.Kem}
    {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts ourB storeB msg) (rngB : E) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (rngB' : E)
    (hinner : lifecycle.Session.decrypt_ratchet rcB crcB p.session p.message rngB =
      ok (core.result.Result.Ok ptB, sB', rngB'))
    (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk) (ec prk k1 k2 d dSend : Model.State.Key)
    (a4 : Array U8 32#usize)
    (hrel : SessionRefines dh K sB'
      (firstReceiptSession (responderModelOf dh p) secret rcv ec prk k1 k2 (arrayOf a4) d dSend
        (oracleB.dhPublic dB) dB)) :
    ∃ (dhs rk cks ckr prk' c2 cr : Array U8 32#usize) (auth : tacenta_braid.Auth)
      (dec : tacenta_erasure.Decoder) (rp : tacenta_boundary.dh.PrivateKey)
      (pk : tacenta_boundary.dh.PublicKeyBytes),
      sB' = receivedSession p (receivedTriple dhs a4 rk cks ckr prk' c2 cr) auth dec rp ∧
      tacenta_boundary.dh.PrivateKey.public_key rp = ok pk ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok dhs ∧
      tacenta_erasure.Decoder.invariant dec = ok true ∧
      (do
        let i ← tacenta_kem.HEADER_LEN
        let i1 ← i + tacenta_braid.MAC_LEN
        tacenta_braid.decoder_sized dec i1) = ok true := by
  obtain ⟨m, x, y, bc, a, ck, pkb, new, hrecv, hrand, hck, hpkb, hnew, hcases⟩ :=
    decrypt_ratchet_ok_parts rcB crcB p.session p.message rngB ptB sB' rngB' hinner
  -- the Triple, from the relation
  obtain ⟨dhs, dhr, rk, cks, ckr, prk', c2, cr, ht, hdhs, hdhr⟩ :=
    triple_eq_received ec prk k1 k2 (arrayOf a4) d dSend (oracleB.dhPublic dB) sB'.triple hrel.triple
  have hdhr' : dhr = a4 := Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes hdhr
  subst hdhr'
  -- the candidate's public bytes are the Triple's new sending key
  obtain ⟨value, rng'', hval, hvd, -⟩ := oracleOfB.random32 rngB dB restB hdrawB
  rw [hrand] at hval
  simp only [ok.injEq, Prod.mk.injEq] at hval
  obtain ⟨rfl, -⟩ := hval
  obtain ⟨k', hk', hkv⟩ := codec.privateFromBytes a
  rw [hck] at hk'
  cases hk'
  obtain ⟨pk', hpk', hpkv⟩ := oracleOfB.dhPublic ck
  rw [hpkb] at hpk'
  cases hpk'
  obtain ⟨bytes, hbytes, hbv⟩ := codec.asBytes pkb
  rw [hnew] at hbytes
  cases hbytes
  have hdn : dhs = new := by
    apply Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes
    have : arrayOf dhs = arrayOf new := by rw [hdhs, ← hvd, ← hkv, ← hpkv, hbv]
    exact this
  subst hdn
  -- the Braid: the relation fixes its constructor and epoch, the code walk its decoder
  have hb := hrel.braid
  simp only [firstReceiptSession] at hb
  have hbc : sB'.braid = bc := by
    rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> (rw [h])
  rcases hst : sB'.braid.state with _ | _ | _ | _ | _ | ⟨e, auth, dec⟩ | _ | _ | _ | _ | _ | _
  all_goals (rw [hst] at hb; try (simp [Tacenta.SessionUnitBraidT3.StateRefines] at hb; done))
  obtain ⟨he, -, -, -⟩ := hb
  have he' : e = 1#u64 := UScalar.eq_of_val_eq (by simpa using he)
  subst he'
  rw [hbc] at hst
  obtain ⟨hdinv, hsized⟩ := received_decoder_checks hdiv hhdr p m x y bc hrecv 1#u64 auth dec hst
  have hbr : bc = ⟨tacenta_braid.State.NoHeaderReceived 1#u64 auth dec⟩ := by
    cases bc; simp only at hst; rw [hst]
  obtain ⟨rk0, prk0, c10, c20, htrip⟩ := Tacenta.UnitLifecycleEstablishResponder.init_receiver_ok _ _ _ p.hTriple
  rcases hcases with ⟨-, hs'⟩ | ⟨hsame, hs'⟩
  · refine ⟨dhs, rk, cks, ckr, prk', c2, cr, auth, dec, ck, pkb, ?_, hpkb, hnew, hdinv, hsized⟩
    rw [hs', ht, hbr]
    rfl
  · have hd0 : dhs = p.ratchetBytes := by
      rw [ht] at hsame
      simpa [receivedTriple, Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.session, htrip,
        Tacenta.UnitLifecycleEstablishResponder.responderTriple] using hsame
    subst hd0
    refine ⟨p.ratchetBytes, rk, cks, ckr, prk', c2, cr, auth, dec, p.ratchetPrivate, p.ratchetPublic, ?_,
      by rw [p.ratchetPrivate_eq]; exact p.hRatchetPublic, p.hRatchetBytes, hdinv, hsized⟩
    rw [hs', ht, hbr]
    rfl

/-- **All four counter ceilings hold at `receivedSession`** of a `receivedTriple`: classical clock 1, sparse epoch 0,
chain counters 0 and 1, agreement epoch 1.  Hypothesis-free. -/
theorem received_counterHeadroom {our : lifecycle.Identity} {store : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts our store msg) (dhs dhr rk cks ckr prk c2 cr : Array U8 32#usize)
    (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder) (rp : tacenta_boundary.dh.PrivateKey) :
    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
      (receivedSession p (receivedTriple dhs dhr rk cks ckr prk c2 cr) auth dec rp) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [receivedSession, receivedTriple, U32.max_eq]
  · simp [receivedSession, receivedTriple, U64.max_eq]
  · intro q hq ch hch
    simp [receivedSession, receivedTriple, receivedChains, Tacenta.UnitHeadroomSatisfiable.vecOf] at hq
    subst hq
    rcases hch with h | h <;> (simp at h; subst h; simp [U64.max_eq])
  · simp only [receivedSession, Tacenta.SessionUnitBraidT1.State.epoch_val]
    scalar_tac

/-- **`Session::invariant` and the four ceilings at the session a successful inner receive returns at the prepared
session**, when that session refines `firstReceiptSession` with a canonical peer ratchet key: under the hypotheses of
`first_receipt_successor_shape`, `DhPublicValid` and `OptionEqU64Shape`. -/
theorem first_receipt_successor_facts (hpub : DhPublicValid)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (hhdr : Tacenta.SessionUnitBraidT1.HeaderLenTotal) {E : Type} (rcB : rand_core_1.RngCore E)
    (crcB : rand_core_1.CryptoRng E) {dh : DhView} (codec : DhCodecOf dh)
    {traceB : E → List Model.Lifecycle.Key} {oracleB : Model.Lifecycle.Oracle}
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB) {K : Model.Braid.Kem}
    {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts ourB storeB msg) (rngB : E) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (rngB' : E)
    (hinner : lifecycle.Session.decrypt_ratchet rcB crcB p.session p.message rngB =
      ok (core.result.Result.Ok ptB, sB', rngB'))
    (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk) (ec prk k1 k2 d dSend : Model.State.Key)
    (a4 : Array U8 32#usize) (ha4 : Tacenta.SessionUnitT1.canonicalX25519 a4 = true)
    (hrel : SessionRefines dh K sB'
      (firstReceiptSession (responderModelOf dh p) secret rcv ec prk k1 k2 (arrayOf a4) d dSend
        (oracleB.dhPublic dB) dB)) :
    lifecycle.Session.invariant sB' = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' := by
  obtain ⟨dhs, rk, cks, ckr, prk', c2, cr, auth, dec, rp, pk, rfl, hrp, hpk, hdinv, hsized⟩ :=
    first_receipt_successor_shape hdiv hhdr rcB crcB codec oracleOfB p rngB dB restB hdrawB ptB sB' rngB'
      hinner secret rcv ec prk k1 k2 d dSend a4 hrel
  exact ⟨received_invariant hpub hoeq p dhs a4 rk cks ckr prk' c2 cr auth dec rp pk hrp hpk ha4 hdinv hsized,
    received_counterHeadroom p dhs a4 rk cks ckr prk' c2 cr auth dec rp⟩

section Comp
variable {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
  {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}

open Tacenta.UnitLifecycleT3 (vecOf sliceOf modelChunkOf modelCodewordOf CodewordViewSendOf)
open Tacenta.UnitLifecycleEstablishInitiatorShape (establishedModelOf)
open Tacenta.UnitLifecycleEstablishedEncrypt (firstFrame initialWire)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees StoreRefusal responder_first_frame_prepares)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptRatchetAgreements)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstKey DhAgreeContributory AeadRoundTrip
  parts_of_first_frame responder_first_frame_inner_succeeds establish_responder_commit_of_inner)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)

/-! ## At the session `establish_responder` returns -/

/-- **The session `establish_responder` returns on the initiator's first frame passes `Session::invariant` and meets the
four ceilings**: under the hypotheses of `responder_first_frame_succeeds` without the store bound, at every return of
the call that is `Ok (sB', ptB)`, `sB'` refines `firstReceiptSession` (as in that theorem), passes the invariant and
meets `CounterHeadroom`.  No compiler-trust axiom (the pin): the nine `native_decide` constants of the decrypt refinement, inherited until 2026-10-21, are kernel proofs. -/
theorem responder_first_frame_successor [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type}
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
    (q : InitiatorSecretParts rc crc our bundle) (pending : Model.Lifecycle.PendingInitial)
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
  obtain ⟨ec, dSend, ptB0, sB0, rngB0, -, -, hinner, -, -, hrel⟩ :=
    responder_first_frame_inner_succeeds rcB crcB contracts hpub hsym hcon haead hoeq codec view oracleA hsealA
      traceB oracleB oracleOfB agreements q plaintext hroom src hsrc c hcw hsend p h3 h5 hsp hop h8 rngB
      htraceB dB restB hdrawB
  obtain ⟨storeB0, -, hout⟩ := establish_responder_commit_of_inner rcB crcB p rngB ptB0 sB0 rngB0 hinner _ hcallB
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at hout
  obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ := hout
  have ha4 := dhPublicValid_canonical hpub q.hRatchetPublic q.hRatchetBytes
  exact ⟨p, ec, dSend, hrel, first_receipt_successor_facts hpub hoeq contracts.divCeilValue
    contracts.decrypt.braid.headerLen rcB crcB codec oracleOfB p rngB dB restB hdrawB _ _ _ hinner
    _ _ _ _ _ _ _ _ q.ratchetBytes ha4 hrel⟩

open Tacenta.UnitLifecycleResponderFirstReceipt (headerSource established_triple_first first_send_key)
open Tacenta.UnitLifecycleEstablishInitiatorShape (InitiatorOutputParts)
open Tacenta.UnitLifecycleT3 (OracleOf BraidSendRefinementContracts TripleSendRefinementContracts KemView) in
/-- **Every session-side premise of the next `decrypt` refinement holds at the responder's session after the
initiator's first send**: under the hypotheses of `initiator_first_send_responder_receives` without the store bound,
at every successful return `(Ok (sB', ptB), storeB', rngB')` of `establish_responder` on the bytes the initiator's
first `encrypt` emitted, `sB'` refines `firstReceiptSession` (at the header source of the initiator's key generation at
its two draws), passes `Session::invariant` and meets `CounterHeadroom`.  No compiler-trust axiom (the pin):
the nine `native_decide` constants of the encrypt and decrypt refinements, inherited until 2026-10-21, are kernel proofs. -/
theorem initiator_first_send_responder_successor_hypotheses [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
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
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
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
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB')) :
    ∃ (p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes)) (ec : Array U8 32#usize)
      (dSend : Model.Lifecycle.Key) (dk ekSeed ekVector : Model.Braid.Bytes),
      oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector) ∧
      SessionRefines dh oracleB.braidKem sB'
        (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret)
          ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
          (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
          (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) ∧
      lifecycle.Session.invariant sB' = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' := by
  obtain ⟨output, hcall', hdr, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes rc
    crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen
    hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h plaintext hroom rng htrace d1 d2 rest hdraws
  rw [hcall] at hcall'
  cases hcall'
  rcases hcases with ⟨-, hres, -⟩ | ⟨dk, ekSeed, ekVector, hkg, bytes', hres, -, -, tripleNext, messageKey,
    chunk, encoder, pending, a, ⟨header, hsendM⟩, hbraidA, hnc, hpend, hwire, -⟩
  · cases hres
  simp only [core.result.Result.Ok.injEq] at hres
  subst hres
  subst hq
  -- the message key is the first key of the initiator's chains
  have hmk : messageKey = firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend) := by
    rw [established_triple_first dh q.toInitiatorOutputParts, first_send_key] at hsendM
    simp only [Except.ok.injEq, Prod.mk.injEq] at hsendM
    exact hsendM.2.2.symm
  -- the chunk is the first chunk of the header source
  have ha : a = Tacenta.SessionUnitBraidT3.AuthOf q.auth := by
    simp only [establishedModelOf, InitiatorOutputParts.session,
      Tacenta.UnitLifecycleEstablishInitiatorShape.unsampledModelOf, Model.Braid.BraidState.keysUnsampled.injEq]
      at hbraidA
    exact hbraidA.2.symm
  subst ha
  have hchunk : chunk = ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed
      ekVector, 0⟩ := by
    simp only [Model.Braid.encode, Model.Braid.Encoder.nextChunk, Prod.mk.injEq] at hnc
    rw [← hnc.1]
    rfl
  obtain ⟨hs32, -, hhl⟩ := hsizes _ _ _ _ hkg
  have hsrc : (headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector).length =
      Model.Braid.headerSize + Model.Braid.macSize := by
    simp [headerSource, Model.Braid.Auth.macHdr, Model.Kdf.hmac_length, Model.Kdf.hashLen, hs32, hhl,
      Model.Braid.headerSize, Model.Braid.macSize]
  obtain ⟨-, -, c, -, -, hc0, hcw, -⟩ := Tacenta.UnitHeldKemWitness.held_encoder contracts.divCeilValue
    agreements.erasure _ (by rw [hsrc]; rfl)
  have hmc : modelChunkOf (headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed
      ekVector) c = ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩ := by
    simp [modelChunkOf, hc0]
  have hsend := codewordView.send (establishedModelOf dh q.session).braid _ c hcw
  rw [hmk, hchunk, ← hmc] at hwire
  obtain ⟨p, ec, dSend, hrel, hinv, hhead'⟩ := responder_first_frame_successor rcB crcB contracts hpub hsym hcon
    haead hrt hct hbound hoeq codec view oracle oracleOf.aeadSeal traceB oracleB oracleOfB agreements q pending
    hpend plaintext (by omega) _ hsrc c hcw hsend (alloc.vec.Vec.deref bytes) hwire ourB storeB hpublish hidentity
    hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB
  rw [hmc] at hrel
  exact ⟨p, ec, dSend, dk, ekSeed, ekVector, hkg, hrel, hinv, hhead'⟩

open Tacenta.UnitLifecycleT3 (OracleOf BraidSendRefinementContracts TripleSendRefinementContracts KemView) in
/-- **`Session::invariant` at the responder's session after the initiator's first send**: the invariant conjunct of
`initiator_first_send_responder_successor_hypotheses`, under its hypotheses.  Its axioms are that theorem's (the pin). -/
theorem initiator_first_send_responder_successor_admissible [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
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
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
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
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB')) :
    lifecycle.Session.invariant sB' = ok true := by
  obtain ⟨-, -, -, -, -, -, -, -, hinv, hhead'⟩ :=
    initiator_first_send_responder_successor_hypotheses rc crc trace dh kem view oracle braid triple aead dhCodec
      oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h
      q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall rcB crcB contracts hpub hsym hcon haead
      hrt hoeq traceB oracleB oracleOfB agreements ourB storeB hpublish hidentity hdistinct hkem rngB htraceB dB restB
      hdrawB ptB sB' storeB' rngB' hcallB
  exact hinv

open Tacenta.UnitLifecycleT3 (OracleOf BraidSendRefinementContracts TripleSendRefinementContracts KemView) in
/-- **The four counter ceilings at the responder's session after the initiator's first send**: the `CounterHeadroom`
conjunct of `initiator_first_send_responder_successor_hypotheses`, under its hypotheses.
Its axioms are that theorem's (the pin). -/
theorem initiator_first_send_responder_successor_counterHeadroom [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
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
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
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
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB')) :
    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' := by
  obtain ⟨-, -, -, -, -, -, -, -, hinv, hhead'⟩ :=
    initiator_first_send_responder_successor_hypotheses rc crc trace dh kem view oracle braid triple aead dhCodec
      oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h
      q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall rcB crcB contracts hpub hsym hcon haead
      hrt hoeq traceB oracleB oracleOfB agreements ourB storeB hpublish hidentity hdistinct hkem rngB htraceB dB restB
      hdrawB ptB sB' storeB' rngB' hcallB
  exact hhead'

end Comp

section Reach
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptRatchetAgreements)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitLifecycleResponderFirstFrame (FirstFrameSuccessShape InitiatorSecretParts DhAgreeSymmetric)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory AeadRoundTrip first_send_receive_reachable)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)
/-! ## The reach -/

open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleEstablishedEncrypt (EncryptExtraLaws emptyPlaintext) in
/-- **The reach of the receipt module, with the responder's session admissible**: under the laws of
`first_send_receive_reachable`, for every initiator identity and every 64-byte source at whose bytes the model's key
generation answers, there is a run from `publish` through the establishment and a first send of the empty plaintext to
a successful `establish_responder` whose session passes `Session::invariant` and meets `CounterHeadroom`.  It applies
`initiator_first_send_responder_successor_hypotheses` to that run.  Last-resort path only.  No compiler-trust axiom (the pin). -/
theorem first_send_receive_successor_reachable (K : Model.Braid.Kem) (dh : DhView)
    (kem : Tacenta.UnitLifecycleT3.KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (X : EncryptExtraLaws K dh kem) (RA : Nonempty (ResponderAxiom Interp.real byteRng))
    (hsym : DhAgreeSymmetric) (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (FS : FirstFrameSuccessShape Interp.real tacenta_boundary.kem.KeyPair.public_key
      @alloc.vec.Vec.is_empty)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K)
    (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (ourA : lifecycle.Identity) (seed : List Std.U8) (hseed : seed.length = 64)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle)
      (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (bytes : alloc.vec.Vec Std.U8)
      (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity)
      (storeB : lifecycle.PrekeyStore) (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8)
      (storeB' : lifecycle.PrekeyStore) (rngB' : List Std.U8),
      oracle.braidKem = K ∧
      lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext seed =
        ok (core.result.Result.Ok bytes, s', rng') ∧
      lifecycle.PrekeyStore.publish storeB = ok bundle ∧
      lifecycle.establish_responder byteRng byteCrc ourB storeB (alloc.vec.Vec.deref bytes) seed =
        ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
      lifecycle.Session.invariant sB' = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' := by
  obtain ⟨oracle, bundle, rng0, rng1, q, bytes, s', rng', ourB, storeB, sB', ptB, storeB', rngB', hK, H, hcall,
    hpublish, hidentity, hdistinct, hkem, -, oracleOfB, htraceB, -, -, hcallB, -⟩ :=
    first_send_receive_reachable K dh kem L A S hpub hct X RA hsym hrt FS hsizes hcon haead ourA seed hseed hkg
  obtain ⟨contracts⟩ := Tacenta.UnitSatisfiabilityRecords.responder_contracts_of_axiom_base byteRng RA L.laws
  obtain ⟨inst⟩ := H.derivedKeys
  subst hK
  obtain ⟨oracle0, bundle1, s1, rng11, hK0, H1⟩ :=
    Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable
      oracle.braidKem dh L A S hpub hct ourA
  have ag : DecryptRatchetAgreements oracle.braidKem :=
    hK0 ▸ (H1 Tacenta.UnitLifecycleRepair.witnessView).agreements
  obtain ⟨d1, d2, rest2, hdrB⟩ : ∃ d1 d2 rest2, byteTrace seed = d1 :: d2 :: rest2 := by
    have := Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega)
    exact ⟨_, _, _, this⟩
  obtain ⟨-, -, -, -, -, -, -, -, hinv, hhead⟩ := initiator_first_send_responder_successor_hypotheses byteRng
    byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec
    H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes
    H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session H.established q rfl
    emptyPlaintext H.room seed H.trace_eq _ _ _ (Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega))
    bytes s' rng' hcall byteRng byteCrc contracts hpub hsym hcon haead hrt L.optionEq byteTrace oracle oracleOfB ag
    ourB storeB hpublish hidentity hdistinct hkem seed htraceB d1 (d2 :: rest2) hdrB ptB sB' storeB' rngB' hcallB
  exact ⟨oracle, bundle, q, bytes, s', rng', ourB, storeB, sB', ptB, storeB', rngB', rfl, hcall, hpublish,
    hcallB, hinv, hhead⟩

end Reach

end Tacenta.UnitLifecycleResponderSuccessor

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.decrypt_ratchet_ok_parts' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSuccessor.decrypt_ratchet_ok_parts

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.braid_receive_noHeader' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSuccessor.braid_receive_noHeader

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.one_chunk_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSuccessor.one_chunk_loop

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.decoder_invariant_small' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSuccessor.decoder_invariant_small

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.add_chunk_fresh_have' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSuccessor.add_chunk_fresh_have

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.received_decoder_checks' depends on axioms: [propext,
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
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
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
#print axioms Tacenta.UnitLifecycleResponderSuccessor.received_decoder_checks

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.triple_eq_received' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSuccessor.triple_eq_received

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.receivedTriple_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSuccessor.receivedTriple_invariant

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.structural_received' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSuccessor.structural_received

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.received_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSuccessor.received_invariant

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.first_receipt_successor_shape' depends on axioms: [propext,
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
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
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
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSuccessor.first_receipt_successor_shape

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.received_counterHeadroom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
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
#print axioms Tacenta.UnitLifecycleResponderSuccessor.received_counterHeadroom

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.first_receipt_successor_facts' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSuccessor.first_receipt_successor_facts

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.responder_first_frame_successor' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSuccessor.responder_first_frame_successor

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.initiator_first_send_responder_successor_hypotheses' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSuccessor.initiator_first_send_responder_successor_hypotheses

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.initiator_first_send_responder_successor_admissible' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSuccessor.initiator_first_send_responder_successor_admissible

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.initiator_first_send_responder_successor_counterHeadroom' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSuccessor.initiator_first_send_responder_successor_counterHeadroom

/--
info: 'Tacenta.UnitLifecycleResponderSuccessor.first_send_receive_successor_reachable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSuccessor.first_send_receive_successor_reachable

set_option pp.deepTerms true
set_option pp.proofs.withType true

/--
info: @Tacenta.UnitLifecycleResponderSuccessor.decrypt_ratchet_ok_parts : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (message : Slice U8) (rng : R) (v : alloc.vec.Vec U8)
  (s' : lifecycle.Session) (rng' : R),
  lifecycle.Session.decrypt_ratchet rc crc s message rng = ok (core.result.Result.Ok v, s', rng') →
    ∃ m x y bc a ck pkb new,
      s.braid.receive m = ok (x, y, bc) ∧
        lifecycle.random_secret rc crc rng = ok (a, rng') ∧
          tacenta_boundary.dh.PrivateKey.from_bytes a = ok ck ∧
            ck.public_key = ok pkb ∧
              pkb.as_bytes = ok new ∧
                (s'.triple.classical.dhs_pub ≠ s.triple.classical.dhs_pub ∧
                    s' =
                      { triple := s'.triple, braid := bc, ratchet_private := ck, identity_ad := s.identity_ad,
                        our_identity_public := s.our_identity_public, peer_identity_public := s.peer_identity_public,
                        pending_initial := s.pending_initial, established_ephemeral := s.established_ephemeral } ∨
                  s'.triple.classical.dhs_pub = s.triple.classical.dhs_pub ∧
                    s' =
                      { triple := s'.triple, braid := bc, ratchet_private := s.ratchet_private,
                        identity_ad := s.identity_ad, our_identity_public := s.our_identity_public,
                        peer_identity_public := s.peer_identity_public, pending_initial := s.pending_initial,
                        established_ephemeral := s.established_ephemeral })
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.decrypt_ratchet_ok_parts

/--
info: Tacenta.UnitLifecycleResponderSuccessor.braid_receive_noHeader : ∀ (epoch : U64) (auth : tacenta_braid.Auth)
  (d : tacenta_erasure.Decoder) (m : tacenta_braid.Msg) (x : U64) (y : Option tacenta_braid.Output)
  (b' : tacenta_braid.Braid),
  { state := tacenta_braid.State.NoHeaderReceived epoch auth d }.receive m = ok (x, y, b') →
    ∀ (e' : U64) (a' : tacenta_braid.Auth) (d' : tacenta_erasure.Decoder),
      b'.state = tacenta_braid.State.NoHeaderReceived e' a' d' → d' = d ∨ ∃ c r, d.add_chunk c = ok (r, d')
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.braid_receive_noHeader

/--
info: Tacenta.UnitLifecycleResponderSuccessor.one_chunk_loop : ∀ (d : tacenta_erasure.Decoder) (c : tacenta_erasure.Chunk),
  ↑d.have = [c] →
    d.invariant_loop (Array.repeat 8192#usize 0#u8) true 0#usize ⦃ r => r = (d.size, d.needed, d.have, true) ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.one_chunk_loop

/--
info: Tacenta.UnitLifecycleResponderSuccessor.decoder_invariant_small : ∀ (d : tacenta_erasure.Decoder),
  tacenta_erasure.chunk_count d.size = ok d.needed →
    ↑d.needed ≤ 65536 → (↑d.have).length ≤ 1 → (↑d.have).length ≤ ↑d.needed → d.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.decoder_invariant_small

/--
info: Tacenta.UnitLifecycleResponderSuccessor.add_chunk_fresh_have : ∀ (d d' : tacenta_erasure.Decoder)
  (c : tacenta_erasure.Chunk) (r : Bool),
  ↑d.have = [] →
    d.add_chunk c = ok (r, d') →
      d'.size = d.size ∧ d'.needed = d.needed ∧ (↑d'.have).length ≤ 1 ∧ (↑d'.have).length ≤ ↑d.needed
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.add_chunk_fresh_have

/--
info: Tacenta.UnitLifecycleResponderSuccessor.received_decoder_checks : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  Tacenta.SessionUnitBraidT1.HeaderLenTotal →
    ∀ {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
      (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg) (m : tacenta_braid.Msg)
      (x : U64) (y : Option tacenta_braid.Output) (bc : tacenta_braid.Braid),
      p.braid.receive m = ok (x, y, bc) →
        ∀ (e : U64) (a : tacenta_braid.Auth) (d' : tacenta_erasure.Decoder),
          bc.state = tacenta_braid.State.NoHeaderReceived e a d' →
            d'.invariant = ok true ∧
              (do
                  let i ← tacenta_kem.HEADER_LEN
                  let i1 ← i + tacenta_braid.MAC_LEN
                  tacenta_braid.decoder_sized d' i1) =
                ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.received_decoder_checks

/--
info: Tacenta.UnitLifecycleResponderSuccessor.triple_eq_received : ∀ (ec prk k1 k2 a4 d dSend newPub : Model.State.Key)
  (t : tacenta_triple.State),
  Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs t
      (Tacenta.UnitLifecycleResponderFirstReceipt.receiverAfterFirst ec prk k1 k2 a4 d dSend newPub) →
    ∃ dhs dhr rk cks ckr prk' c2 cr,
      t = Tacenta.UnitLifecycleResponderSuccessor.receivedTriple dhs dhr rk cks ckr prk' c2 cr ∧
        Tacenta.UnitLifecycleT3.arrayOf dhs = newPub ∧ Tacenta.UnitLifecycleT3.arrayOf dhr = a4
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.triple_eq_received

/--
info: Tacenta.UnitLifecycleResponderSuccessor.receivedTriple_invariant : ∀
  (dhs dhr rk cks ckr prk c2 cr : Std.Array U8 32#usize),
  Tacenta.SessionUnitT1.canonicalX25519 dhs = true →
    Tacenta.SessionUnitT1.canonicalX25519 dhr = true →
      (Tacenta.UnitLifecycleResponderSuccessor.receivedTriple dhs dhr rk cks ckr prk c2 cr).invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.receivedTriple_invariant

/--
info: Tacenta.UnitLifecycleResponderSuccessor.structural_received : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
  Tacenta.UnitHeadroomInvariant.OptionEqU64Shape @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
    ∀ {our : lifecycle.Identity} {store : lifecycle.PrekeyStore} {msg : Slice U8}
      (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg)
      (dhs dhr rk cks ckr prk c2 cr : Std.Array U8 32#usize) (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder)
      (rp : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
      rp.public_key = ok pk →
        pk.as_bytes = ok dhs →
          (Tacenta.UnitLifecycleResponderSuccessor.receivedSession p
                (Tacenta.UnitLifecycleResponderSuccessor.receivedTriple dhs dhr rk cks ckr prk c2 cr) auth dec
                rp).structural_invariant =
            ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.structural_received

/--
info: Tacenta.UnitLifecycleResponderSuccessor.received_invariant : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
  Tacenta.UnitHeadroomInvariant.OptionEqU64Shape @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
    ∀ {our : lifecycle.Identity} {store : lifecycle.PrekeyStore} {msg : Slice U8}
      (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg)
      (dhs dhr rk cks ckr prk c2 cr : Std.Array U8 32#usize) (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder)
      (rp : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
      rp.public_key = ok pk →
        pk.as_bytes = ok dhs →
          Tacenta.SessionUnitT1.canonicalX25519 dhr = true →
            dec.invariant = ok true →
              (do
                    let i ← tacenta_kem.HEADER_LEN
                    let i1 ← i + tacenta_braid.MAC_LEN
                    tacenta_braid.decoder_sized dec i1) =
                  ok true →
                (Tacenta.UnitLifecycleResponderSuccessor.receivedSession p
                      (Tacenta.UnitLifecycleResponderSuccessor.receivedTriple dhs dhr rk cks ckr prk c2 cr) auth dec
                      rp).invariant =
                  ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.received_invariant

/--
info: Tacenta.UnitLifecycleResponderSuccessor.first_receipt_successor_shape : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  Tacenta.SessionUnitBraidT1.HeaderLenTotal →
    ∀ {E : Type} (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E) {dh : Tacenta.UnitLifecycleT3.DhView},
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        ∀ {traceB : E → List Model.Lifecycle.Key} {oracleB : Model.Lifecycle.Oracle},
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
            ∀ {K : Model.Braid.Kem} {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
              (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg) (rngB : E)
              (dB : Model.Lifecycle.Key) (restB : List Model.Lifecycle.Key),
              traceB rngB = dB :: restB →
                ∀ (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (rngB' : E),
                  lifecycle.Session.decrypt_ratchet rcB crcB p.session p.message rngB =
                      ok (core.result.Result.Ok ptB, sB', rngB') →
                    ∀ (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk)
                      (ec prk k1 k2 d dSend : Model.State.Key) (a4 : Std.Array U8 32#usize),
                      Tacenta.UnitLifecycleT3.SessionRefines dh K sB'
                          (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                            (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) secret rcv ec prk k1 k2
                            (Tacenta.UnitLifecycleT3.arrayOf a4) d dSend (oracleB.dhPublic dB) dB) →
                        ∃ dhs rk cks ckr prk' c2 cr auth dec rp pk,
                          sB' =
                              Tacenta.UnitLifecycleResponderSuccessor.receivedSession p
                                (Tacenta.UnitLifecycleResponderSuccessor.receivedTriple dhs a4 rk cks ckr prk' c2 cr)
                                auth dec rp ∧
                            rp.public_key = ok pk ∧
                              pk.as_bytes = ok dhs ∧
                                dec.invariant = ok true ∧
                                  (do
                                      let i ← tacenta_kem.HEADER_LEN
                                      let i1 ← i + tacenta_braid.MAC_LEN
                                      tacenta_braid.decoder_sized dec i1) =
                                    ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.first_receipt_successor_shape

/--
info: @Tacenta.UnitLifecycleResponderSuccessor.received_counterHeadroom : ∀ {our : lifecycle.Identity}
  {store : lifecycle.PrekeyStore} {msg : Slice U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg)
  (dhs dhr rk cks ckr prk c2 cr : Std.Array U8 32#usize) (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder)
  (rp : tacenta_boundary.dh.PrivateKey),
  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
    (Tacenta.UnitLifecycleResponderSuccessor.receivedSession p
      (Tacenta.UnitLifecycleResponderSuccessor.receivedTriple dhs dhr rk cks ckr prk c2 cr) auth dec rp)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.received_counterHeadroom

/--
info: Tacenta.UnitLifecycleResponderSuccessor.first_receipt_successor_facts : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
  Tacenta.UnitHeadroomInvariant.OptionEqU64Shape @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
    Tacenta.SessionUnitDecoderBound.DivCeilValue →
      Tacenta.SessionUnitBraidT1.HeaderLenTotal →
        ∀ {E : Type} (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
          {dh : Tacenta.UnitLifecycleT3.DhView},
          Tacenta.UnitLifecycleT3.DhCodecOf dh →
            ∀ {traceB : E → List Model.Lifecycle.Key} {oracleB : Model.Lifecycle.Oracle},
              Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
                ∀ {K : Model.Braid.Kem} {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
                  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg) (rngB : E)
                  (dB : Model.Lifecycle.Key) (restB : List Model.Lifecycle.Key),
                  traceB rngB = dB :: restB →
                    ∀ (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (rngB' : E),
                      lifecycle.Session.decrypt_ratchet rcB crcB p.session p.message rngB =
                          ok (core.result.Result.Ok ptB, sB', rngB') →
                        ∀ (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk)
                          (ec prk k1 k2 d dSend : Model.State.Key) (a4 : Std.Array U8 32#usize),
                          Tacenta.SessionUnitT1.canonicalX25519 a4 = true →
                            Tacenta.UnitLifecycleT3.SessionRefines dh K sB'
                                (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                  (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) secret rcv ec prk k1
                                  k2 (Tacenta.UnitLifecycleT3.arrayOf a4) d dSend (oracleB.dhPublic dB) dB) →
                              sB'.invariant = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.first_receipt_successor_facts

/--
info: @Tacenta.UnitLifecycleResponderSuccessor.responder_first_frame_successor : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
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
                                ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle)
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
#check @Tacenta.UnitLifecycleResponderSuccessor.responder_first_frame_successor

/--
info: @Tacenta.UnitLifecycleResponderSuccessor.initiator_first_send_responder_successor_hypotheses : ∀
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
                                                                Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                                                                  Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                                                                      @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                                                                    ∀ (traceB : F → List Model.Lifecycle.Key)
                                                                      (oracleB : Model.Lifecycle.Oracle),
                                                                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf
                                                                          rcB crcB dh traceB oracleB →
                                                                        Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                            oracleB.braidKem →
                                                                          ∀ (ourB : lifecycle.Identity)
                                                                            (storeB : lifecycle.PrekeyStore),
                                                                            storeB.publish = ok bundleA →
                                                                              ourB.public = ok storeB.identity_public →
                                                                                Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                                    storeB →
                                                                                  Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                                      storeB bundleA.kem_prekey_id
                                                                                      q.kemCiphertext q.kemSecret →
                                                                                    ∀ (rngB : F),
                                                                                      traceB rngB = oracleB.draws →
                                                                                        ∀ (dB : Model.Lifecycle.Key)
                                                                                          (restB :
                                                                                            List Model.Lifecycle.Key),
                                                                                          traceB rngB = dB :: restB →
                                                                                            ∀ (ptB : alloc.vec.Vec U8)
                                                                                              (sB' : lifecycle.Session)
                                                                                              (storeB' :
                                                                                                lifecycle.PrekeyStore)
                                                                                              (rngB' : F),
                                                                                              lifecycle.establish_responder
                                                                                                    rcB crcB ourB storeB
                                                                                                    bytes.deref rngB =
                                                                                                  ok
                                                                                                    (core.result.Result.Ok
                                                                                                        (sB', ptB),
                                                                                                      storeB', rngB') →
                                                                                                ∃ p ec dSend dk ekSeed
                                                                                                  ekVector,
                                                                                                  oracle.braidKem.keyGen
                                                                                                        (Model.Lifecycle.braidRandomness
                                                                                                          (d1 ++ d2)) =
                                                                                                      some
                                                                                                        (dk, ekSeed,
                                                                                                          ekVector) ∧
                                                                                                    Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                        dh
                                                                                                        oracleB.braidKem
                                                                                                        sB'
                                                                                                        (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                                                          (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                                            dh p)
                                                                                                          (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                            p.braidSecret)
                                                                                                          {
                                                                                                            source :=
                                                                                                              Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                oracle.braidKem
                                                                                                                (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                  q.auth)
                                                                                                                ekSeed
                                                                                                                ekVector,
                                                                                                            index := 0 }
                                                                                                          (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                            ec)
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
                                                                                                          dSend
                                                                                                          (oracleB.dhPublic
                                                                                                            dB)
                                                                                                          dB) ∧
                                                                                                      sB'.invariant =
                                                                                                          ok true ∧
                                                                                                        Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                                          sB'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.initiator_first_send_responder_successor_hypotheses

/--
info: @Tacenta.UnitLifecycleResponderSuccessor.initiator_first_send_responder_successor_admissible : ∀
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
                                                                Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                                                                  Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                                                                      @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                                                                    ∀ (traceB : F → List Model.Lifecycle.Key)
                                                                      (oracleB : Model.Lifecycle.Oracle),
                                                                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf
                                                                          rcB crcB dh traceB oracleB →
                                                                        Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                            oracleB.braidKem →
                                                                          ∀ (ourB : lifecycle.Identity)
                                                                            (storeB : lifecycle.PrekeyStore),
                                                                            storeB.publish = ok bundleA →
                                                                              ourB.public = ok storeB.identity_public →
                                                                                Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                                    storeB →
                                                                                  Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                                      storeB bundleA.kem_prekey_id
                                                                                      q.kemCiphertext q.kemSecret →
                                                                                    ∀ (rngB : F),
                                                                                      traceB rngB = oracleB.draws →
                                                                                        ∀ (dB : Model.Lifecycle.Key)
                                                                                          (restB :
                                                                                            List Model.Lifecycle.Key),
                                                                                          traceB rngB = dB :: restB →
                                                                                            ∀ (ptB : alloc.vec.Vec U8)
                                                                                              (sB' : lifecycle.Session)
                                                                                              (storeB' :
                                                                                                lifecycle.PrekeyStore)
                                                                                              (rngB' : F),
                                                                                              lifecycle.establish_responder
                                                                                                    rcB crcB ourB storeB
                                                                                                    bytes.deref rngB =
                                                                                                  ok
                                                                                                    (core.result.Result.Ok
                                                                                                        (sB', ptB),
                                                                                                      storeB', rngB') →
                                                                                                sB'.invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.initiator_first_send_responder_successor_admissible

/--
info: @Tacenta.UnitLifecycleResponderSuccessor.initiator_first_send_responder_successor_counterHeadroom : ∀
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
                                                                Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                                                                  Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                                                                      @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                                                                    ∀ (traceB : F → List Model.Lifecycle.Key)
                                                                      (oracleB : Model.Lifecycle.Oracle),
                                                                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf
                                                                          rcB crcB dh traceB oracleB →
                                                                        Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                            oracleB.braidKem →
                                                                          ∀ (ourB : lifecycle.Identity)
                                                                            (storeB : lifecycle.PrekeyStore),
                                                                            storeB.publish = ok bundleA →
                                                                              ourB.public = ok storeB.identity_public →
                                                                                Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                                    storeB →
                                                                                  Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                                      storeB bundleA.kem_prekey_id
                                                                                      q.kemCiphertext q.kemSecret →
                                                                                    ∀ (rngB : F),
                                                                                      traceB rngB = oracleB.draws →
                                                                                        ∀ (dB : Model.Lifecycle.Key)
                                                                                          (restB :
                                                                                            List Model.Lifecycle.Key),
                                                                                          traceB rngB = dB :: restB →
                                                                                            ∀ (ptB : alloc.vec.Vec U8)
                                                                                              (sB' : lifecycle.Session)
                                                                                              (storeB' :
                                                                                                lifecycle.PrekeyStore)
                                                                                              (rngB' : F),
                                                                                              lifecycle.establish_responder
                                                                                                    rcB crcB ourB storeB
                                                                                                    bytes.deref rngB =
                                                                                                  ok
                                                                                                    (core.result.Result.Ok
                                                                                                        (sB', ptB),
                                                                                                      storeB', rngB') →
                                                                                                Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                                  sB'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.initiator_first_send_responder_successor_counterHeadroom

/--
info: Tacenta.UnitLifecycleResponderSuccessor.first_send_receive_successor_reachable : ∀ (K : Model.Braid.Kem)
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
              Nonempty
                  (Tacenta.UnitSatisfiabilityJoint.ResponderAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
                    Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
                Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                  Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                    Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape
                        Tacenta.UnitSatisfiabilityJoint.Interp.real tacenta_boundary.kem.KeyPair.public_key
                        @alloc.vec.Vec.is_empty →
                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K →
                        Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                          Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                            ∀ (ourA : lifecycle.Identity) (seed : List U8),
                              seed.length = 64 →
                                K.keyGen
                                      (Model.Lifecycle.braidRandomness (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠
                                    none →
                                  ∃ oracle bundle q bytes s' rng' ourB storeB sB' ptB storeB' rngB',
                                    oracle.braidKem = K ∧
                                      lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc q.session
                                            Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed =
                                          ok (core.result.Result.Ok bytes, s', rng') ∧
                                        storeB.publish = ok bundle ∧
                                          lifecycle.establish_responder Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourB storeB bytes.deref
                                                seed =
                                              ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
                                            sB'.invariant = ok true ∧
                                              Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSuccessor.first_send_receive_successor_reachable

/--
info: def Tacenta.UnitLifecycleResponderSuccessor.receivedChains : Std.Array U8 32#usize →
  Std.Array U8 32#usize → alloc.vec.Vec (U64 × tacenta_spqr.Chains) :=
fun c2 cr =>
  Tacenta.UnitHeadroomSatisfiable.vecOf
    [(0#u64, { send := some { ck := c2, n := 0#u64 }, receive := some { ck := cr, n := 1#u64 } })]
    (⋯ :
      [(0#u64, { send := some { ck := c2, n := 0#u64 }, receive := some { ck := cr, n := 1#u64 } })].length ≤
        4294967295)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderSuccessor.receivedChains

/--
info: def Tacenta.UnitLifecycleResponderSuccessor.receivedTriple : Std.Array U8 32#usize →
  Std.Array U8 32#usize →
    Std.Array U8 32#usize →
      Std.Array U8 32#usize →
        Std.Array U8 32#usize →
          Std.Array U8 32#usize → Std.Array U8 32#usize → Std.Array U8 32#usize → tacenta_triple.State :=
fun dhs dhr rk cks ckr prk c2 cr =>
  {
    classical :=
      { dhs_pub := dhs, dhr_pub := some dhr, rk := rk, cks := some cks, ckr := some ckr, ns := 0#u32, nr := 1#u32,
        pn := 0#u32, skipped := alloc.vec.Vec.new tacenta_ratchet.SkippedKey, events := 1#u32,
        labels := tacenta_ratchet.LabelSet.Tacenta },
    post_quantum :=
      { rk := prk, epoch := 0#u64, chains := Tacenta.UnitLifecycleResponderSuccessor.receivedChains c2 cr,
        skipped := alloc.vec.Vec.new tacenta_spqr.Skipped, direction := tacenta_spqr.Direction.B2a } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderSuccessor.receivedTriple

/--
info: def Tacenta.UnitLifecycleResponderSuccessor.receivedSession : {our : lifecycle.Identity} →
  {store : lifecycle.PrekeyStore} →
    {msg : Slice U8} →
      Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg →
        tacenta_triple.State →
          tacenta_braid.Auth → tacenta_erasure.Decoder → tacenta_boundary.dh.PrivateKey → lifecycle.Session :=
fun {our} {store} {msg} p t auth dec rp =>
  have __src := p.session;
  { triple := t, braid := { state := tacenta_braid.State.NoHeaderReceived 1#u64 auth dec }, ratchet_private := rp,
    identity_ad := __src.identity_ad, our_identity_public := __src.our_identity_public,
    peer_identity_public := __src.peer_identity_public, pending_initial := __src.pending_initial,
    established_ephemeral := __src.established_ephemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderSuccessor.receivedSession
