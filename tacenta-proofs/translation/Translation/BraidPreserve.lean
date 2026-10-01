import Translation.BraidPreserveDecoder

/-!
# The Braid keeps the two premises its receive theorems take

`BraidT1.lean` and `BraidT3.lean` prove `step_receive` and `receive` panic-free and refining
`Model.Braid` for a state with `State.ct1_bounded` (the stored ciphertext is at most 4096 bytes),
and on the session unit also `State.decoders_bounded` (every erasure decoder needs at most
`MAX_CODEWORDS` chunks).  `CLAIMS.md` recorded that no theorem showed a send or a receive keeps
either.  This file shows it.

## What is proved

`State.sized` is the clause set: `ct1_bounded`; `Good 4096` for the decoder that `HeaderSent` holds,
the clause `ct1_bounded` needs before it is closed under the transitions (the decoder that makes
`ct1` is sized for at most 4096 bytes); and `Good 4128` for each other decoder a state holds, which
on the session unit carries the `needed` bound of `decoders_bounded`.  For every successful step:

* `Braid.step_send_sized`, `Braid.step_receive_sized`: a state with `sized` is carried to one with
  `sized`;
* `State.clone_sized`: so is its clone;
* `Braid.send_sized`, `Braid.receive_sized`, `Braid.commit_sized`: the same for the three entry
  points;
* `Braid.initiator_sized`, `Braid.responder_sized`: the two constructors build one;
* `Braid.Run.sized`: so every Braid a run reaches from states that have it, by any number of
  `send` (with an RNG that answers) and `receive`, has it.  `Braid.Constructed.sized` says the
  constructors' Braids are such states, and `State.sized_ct1_bounded` that `sized` gives
  `ct1_bounded`.

## Hypotheses

Every hypothesis is one `BraidT1.lean` already takes or the one law below, and each is a statement
about what an opaque operation returns, never that a step returns.  The theorems are about the
steps that do.

* `Ct1LenTotal`, `Ct2LenTotal`, `HeaderLenTotal`, `EkVectorLenTotal`: the KEM length constants are
  at most 4096.  The real ones are 1408 (`CT1_LEN`), 160 (`CT2_LEN`), 64 (`HEADER_LEN`) and 1536
  (`EK_VECTOR_LEN`).  They bound the decoders and `ct1`.
* `Encapsulate1Total` with `RngTotal rc`: `encapsulate1` returns a `ct1` of at most 4096 bytes.
  Used by `step_send_sized` and what is built on it only.
* `Laws` (`BraidPreserveDecoder.lean`): a decoder `Decoder::new(m)` builds never returns a message
  longer than `m`.  The real `Decoder::message` ends in `truncate(size)`.  On the session unit the
  statement is a different one (`SessionUnitBraidPreserveDecoder.Laws`: `Vec::truncate` returns at
  most `n` elements, and `usize::div_ceil` has its value) and this file's text is the same.
  `BraidPreserveWitness.lean` and `SessionUnitBraidPreserveFacts.lean` show each has a model.

## What this does not say

* It does not say a step returns.  `BraidT1` does, for a state with `ct1_bounded` (and on the
  unit `decoders_bounded`), and `sized` now supplies those premises for every Braid a run reaches.
* `sized` is not `Braid::invariant`.  It holds none of the clauses the receive theorems do not use:
  the exact lengths of `header`, `ct1` and `ek_vector`, the encoders' sizes, `epoch >= 1`, the key
  pair's validity.  On the standalone translation a decoded Braid is not shown to have it, because
  `Decoder::invariant` and `Decoder::size` are opaque there; the session unit shows it
  (`SessionUnitBraidPreserveFacts`).
* The epoch headroom premise of the refinements (`epoch + 1 < u64::MAX`) is not a clause here.
-/

open Aeneas Aeneas.Std Result
open tacenta_braid
open Tacenta.BraidT1
open Tacenta.BraidPreserveDecoder

namespace Tacenta.BraidPreserve


/-- A step that ended in `ok (message, state)` ended in the state: the pair is injective.  Used with
`obtain rfl := ok_pair_snd h` to replace the result state by the one the step names; the match on a
tuple that the translation leaves in `h` is reduced by unification. -/
theorem ok_pair_snd {α β : Type} {a a' : α} {b b' : β}
    (h : (ok (a, b) : Result (α × β)) = ok (a', b')) : b = b' := by
  simp only [ok.injEq, Prod.mk.injEq] at h
  exact h.2

/-- A bind that returned tells us its left-hand side returned. -/
theorem bind_ok_inv {α β : Type} {x : Result α} {f : α → Result β} {r : β}
    (h : (do let v ← x; f v) = ok r) : ∃ v, x = ok v ∧ f v = ok r := by
  cases x with
  | ok v => exact ⟨v, rfl, h⟩
  | fail e => simp at h
  | div => simp at h

/-- **The clauses the Braid keeps.**  `ct1` is at most 4096 bytes wherever a state holds one, and every
erasure decoder a state holds is `Good`: its messages are at most `n` bytes (4096 for the `ct1`
decoder, 4128 for the others), and on the session unit it needs at most `MAX_CODEWORDS` chunks.

It gives `State.ct1_bounded` and, on the unit, `State.decoders_bounded` (`sized_ct1_bounded`,
`SessionUnitBraidPreserveFacts.sized_decoders_bounded`), and adds one clause neither has: the decoder
that makes `ct1` is sized for at most 4096 bytes.  Without it the two are not closed under
`step_receive`: `HeaderSent` with a `ct1` decoder sized for 4097 bytes meets both, and the chunk
that completes it makes a `ct1` of 4097 bytes.  `Braid::invariant` does state it
(`decoder_sized(ct1_dec, CT1_LEN)`), so a decoded Braid meets `sized` on the session unit. -/
def State.sized : State → Prop
  | .KeysUnsampled _ _ => True
  | .KeysSampled _ _ _ _ => True
  | .HeaderSent _ _ _ ct1_dec _ => Good 4096 ct1_dec
  | .Ct1Received _ _ _ ct1 _ => ct1.length ≤ 4096
  | .EkSentCt1Received _ _ _ ct1 ct2_dec => ct1.length ≤ 4096 ∧ Good 4128 ct2_dec
  | .NoHeaderReceived _ _ hdr_dec => Good 4128 hdr_dec
  | .HeaderReceived _ _ _ ek_dec => Good 4128 ek_dec
  | .Ct1Sampled _ _ _ _ ct1 _ ek_dec => ct1.length ≤ 4096 ∧ Good 4128 ek_dec
  | .EkReceivedCt1Sampled _ _ _ ct1 _ _ => ct1.length ≤ 4096
  | .Ct1Acknowledged _ _ _ _ ct1 ek_dec => ct1.length ≤ 4096 ∧ Good 4128 ek_dec
  | .Ct2Sampled _ _ _ => True
  | .Failed => True

/-- A length constant that returns a value at most 4096. -/
theorem len_le {c : Result Usize} (h : ∃ v, c = ok v ∧ v.val ≤ 4096) {i : Usize}
    (hi : c = ok i) : i.val ≤ 4096 := by
  obtain ⟨v, hv, hle⟩ := h
  rw [hv] at hi
  cases hi
  exact hle

/-- Adding the 32-byte MAC length to a length of at most 4096 gives at most 4128. -/
theorem add_mac_le {i i1 : Usize} (hi : i.val ≤ 4096) (h : i + MAC_LEN = ok i1) :
    i1.val ≤ 4128 := by
  have h1 := UScalar.add_equiv i MAC_LEN
  rw [h] at h1
  have hm : MAC_LEN.val = 32 := by simp [MAC_LEN]
  omega

/-- The responder's decoder is good. -/
theorem hdr_decoder_good (hl : Laws) (hhdrlen : HeaderLenTotal) {d : tacenta_erasure.Decoder}
    (h : hdr_decoder = ok d) : Good 4128 d := by
  unfold hdr_decoder at h
  obtain ⟨i, hi, h⟩ := bind_ok_inv h
  obtain ⟨i1, hi1, h⟩ := bind_ok_inv h
  exact Good.new hl h (add_mac_le (len_le hhdrlen hi) hi1) (by omega)

/-- A decoder sized by `EK_VECTOR_LEN` is good. -/
theorem ek_decoder_good (hl : Laws) (hekveclen : EkVectorLenTotal) {i : Usize}
    {d : tacenta_erasure.Decoder} (hi : tacenta_kem.EK_VECTOR_LEN = ok i)
    (h : tacenta_erasure.Decoder.new i = ok d) : Good 4128 d :=
  Good.new hl h (le_trans (len_le hekveclen hi) (by omega)) (by omega)

/-- `finish_encaps` returns a state that carries no clause. -/
theorem finish_encaps_sized {epoch : U64} {auth : Auth} {encaps : tacenta_kem.EncapsState}
    {ct1 ek_vector : Slice U8} {s : State} (h : finish_encaps epoch auth encaps ct1 ek_vector = ok s) :
    State.sized s := by
  unfold finish_encaps at h
  obtain ⟨r, hr, h⟩ := bind_ok_inv h
  rcases r with c | e
  · simp only at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    simp only [ok.injEq] at h
    subst h
    trivial
  · simp only [ok.injEq] at h
    subst h
    trivial

/-- **A successful `step_receive` keeps the clauses.**  Every transition: a decoder only ever
takes a chunk (`Good.add`), a new decoder is `Decoder::new` on a protocol constant (`Good.new`), and
the one new `ct1` is the message of a `Good 4096` decoder (`Good.msg`).  The hypotheses are about
the returned values of the constants and decoders, and none says a step returns: this is about
the steps that do. -/
theorem Braid.step_receive_sized (hl : Laws) (hct1len : Ct1LenTotal) (hct2len : Ct2LenTotal)
    (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal)
    (self : Braid) (state : State) (msg : Msg) (out : Option Output) (s' : State)
    (h : Braid.step_receive self state msg = ok (out, s')) (hs : State.sized state) :
    State.sized s' := by
  unfold Braid.step_receive at h
  rcases state with
    ⟨epoch1, auth⟩ | ⟨epoch1, auth, kp, hdr_enc⟩ | ⟨epoch1, auth, kp, ct1_dec, ek_enc⟩
    | ⟨epoch1, auth, kp, ct1, ek_enc⟩ | ⟨epoch1, auth, kp, ct1, ct2_dec⟩
    | ⟨epoch1, auth, hdr_dec⟩ | ⟨epoch1, auth, header, ek_dec⟩
    | ⟨epoch1, auth, header, encaps, ct1, ct1_enc, ek_dec⟩
    | ⟨epoch1, auth, encaps, ct1, ek_vector, ct1_enc⟩
    | ⟨epoch1, auth, header, encaps, ct1, ek_dec⟩ | ⟨epoch1, auth, ct2_enc⟩ | -
  · -- KeysUnsampled
    simp only [State.epoch, bind_tc_ok] at h
    obtain rfl := ok_pair_snd h
    exact hs
  · -- KeysSampled: a ct1 chunk starts the ct1 decoder, `Decoder::new(CT1_LEN)` plus the chunk.
    simp only [State.epoch, bind_tc_ok] at h
    split at h
    · obtain ⟨b, hb, h⟩ := bind_ok_inv h
      split at h
      · split at h
        · obtain rfl := ok_pair_snd h; exact hs
        · obtain ⟨i, hi, h⟩ := bind_ok_inv h
          obtain ⟨d0, hnew, h⟩ := bind_ok_inv h
          obtain ⟨⟨b2, d1⟩, hadd, h⟩ := bind_ok_inv h
          obtain ⟨v, hv, h⟩ := bind_ok_inv h
          obtain ⟨ek, hek, h⟩ := bind_ok_inv h
          obtain rfl := ok_pair_snd h
          exact Good.add (Good.new hl hnew (len_le hct1len hi) (by omega)) hadd
      · obtain rfl := ok_pair_snd h; exact hs
    · obtain rfl := ok_pair_snd h; exact hs
  · -- HeaderSent: the ct1 decoder takes the chunk, and a completed message is `ct1`.
    simp only [State.epoch, bind_tc_ok] at h
    split at h
    · obtain ⟨b, hb, h⟩ := bind_ok_inv h
      split at h
      · split at h
        · obtain rfl := ok_pair_snd h; exact hs
        · obtain ⟨⟨b2, d1⟩, hadd, h⟩ := bind_ok_inv h
          obtain ⟨o, ho, h⟩ := bind_ok_inv h
          rcases o with _ | ct1'
          · obtain rfl := ok_pair_snd h; exact Good.add hs hadd
          · obtain rfl := ok_pair_snd h; exact Good.msg hl (Good.add hs hadd) ho
      · obtain rfl := ok_pair_snd h; exact hs
    · obtain rfl := ok_pair_snd h; exact hs
  · -- Ct1Received: a ct2 chunk starts the ct2 decoder, `Decoder::new(CT2_LEN + MAC_LEN)`.
    simp only [State.epoch, bind_tc_ok] at h
    split at h
    · obtain ⟨b, hb, h⟩ := bind_ok_inv h
      split at h
      · split at h
        · obtain rfl := ok_pair_snd h; exact hs
        · obtain ⟨i, hi, h⟩ := bind_ok_inv h
          obtain ⟨i1, hi1, h⟩ := bind_ok_inv h
          obtain ⟨d0, hnew, h⟩ := bind_ok_inv h
          obtain ⟨⟨b2, d1⟩, hadd, h⟩ := bind_ok_inv h
          obtain rfl := ok_pair_snd h
          exact ⟨hs, Good.add (Good.new hl hnew (add_mac_le (len_le hct2len hi) hi1)
            (by omega)) hadd⟩
      · obtain rfl := ok_pair_snd h; exact hs
    · obtain rfl := ok_pair_snd h; exact hs
  · -- EkSentCt1Received: the decoder takes the chunk; a complete, well-framed message ends in
    -- `Failed` or in `NoHeaderReceived` with a fresh `hdr_decoder`.
    simp only [State.epoch, bind_tc_ok] at h
    split at h
    · obtain ⟨b, hb, h⟩ := bind_ok_inv h
      split at h
      · split at h
        · obtain rfl := ok_pair_snd h; exact hs
        · obtain ⟨⟨b2, d1⟩, hadd, h⟩ := bind_ok_inv h
          obtain ⟨o, ho, h⟩ := bind_ok_inv h
          rcases o with _ | framed
          · obtain rfl := ok_pair_snd h; exact ⟨hs.1, Good.add hs.2 hadd⟩
          · repeat' first
              | (obtain ⟨_, _, h⟩ := bind_ok_inv h)
              | split at h
              | (obtain rfl := ok_pair_snd h
                 first | trivial | exact hdr_decoder_good hl hhdrlen ‹_›)
      · obtain rfl := ok_pair_snd h; exact hs
    · obtain rfl := ok_pair_snd h; exact hs
  · -- NoHeaderReceived: the header decoder takes the chunk; a complete, authenticated header
    -- starts the `ek_vector` decoder, `Decoder::new(EK_VECTOR_LEN)`.
    simp only [State.epoch, bind_tc_ok] at h
    split at h
    · obtain ⟨b, hb, h⟩ := bind_ok_inv h
      split at h
      · split at h
        · obtain rfl := ok_pair_snd h; exact hs
        · obtain ⟨⟨b2, d1⟩, hadd, h⟩ := bind_ok_inv h
          obtain ⟨o, ho, h⟩ := bind_ok_inv h
          rcases o with _ | framed
          · obtain rfl := ok_pair_snd h; exact Good.add hs hadd
          · repeat' first
              | (obtain ⟨_, _, h⟩ := bind_ok_inv h)
              | split at h
              | (obtain rfl := ok_pair_snd h
                 first | trivial | exact ek_decoder_good hl hekveclen ‹_› ‹_›)
      · obtain rfl := ok_pair_snd h; exact hs
    · obtain rfl := ok_pair_snd h; exact hs
  · -- HeaderReceived: nothing happens.
    simp only [State.epoch, bind_tc_ok] at h
    obtain rfl := ok_pair_snd h
    exact hs
  · -- Ct1Sampled
    simp only [State.epoch, bind_tc_ok] at h
    obtain ⟨relevant, hrel, h⟩ := bind_ok_inv h
    split at h
    · split at h
      · obtain rfl := ok_pair_snd h; exact hs
      · obtain ⟨acked, hack, h⟩ := bind_ok_inv h
        obtain ⟨⟨b2, d1⟩, hadd, h⟩ := bind_ok_inv h
        obtain ⟨o, ho, h⟩ := bind_ok_inv h
        rcases o with _ | ekv
        · dsimp only at h
          split at h
          · obtain rfl := ok_pair_snd h; exact ⟨hs.1, Good.add hs.2 hadd⟩
          · obtain rfl := ok_pair_snd h; exact ⟨hs.1, Good.add hs.2 hadd⟩
        · dsimp only at h
          obtain ⟨b, hb, h⟩ := bind_ok_inv h
          split at h
          · split at h
            · obtain ⟨s4, hs4, h⟩ := bind_ok_inv h
              obtain rfl := ok_pair_snd h
              exact finish_encaps_sized hs4
            · obtain rfl := ok_pair_snd h; exact hs.1
          · obtain rfl := ok_pair_snd h; trivial
    · obtain rfl := ok_pair_snd h; exact hs
  · -- EkReceivedCt1Sampled
    simp only [State.epoch, bind_tc_ok] at h
    split at h
    · obtain ⟨b, hb, h⟩ := bind_ok_inv h
      split at h
      · obtain ⟨s2, hs2, h⟩ := bind_ok_inv h
        obtain rfl := ok_pair_snd h
        exact finish_encaps_sized hs2
      · obtain rfl := ok_pair_snd h; exact hs
    · obtain rfl := ok_pair_snd h; exact hs
  · -- Ct1Acknowledged
    simp only [State.epoch, bind_tc_ok] at h
    split at h
    · obtain ⟨b, hb, h⟩ := bind_ok_inv h
      split at h
      · split at h
        · obtain rfl := ok_pair_snd h; exact hs
        · obtain ⟨⟨b2, d1⟩, hadd, h⟩ := bind_ok_inv h
          obtain ⟨o, ho, h⟩ := bind_ok_inv h
          rcases o with _ | ekv
          · obtain rfl := ok_pair_snd h; exact ⟨hs.1, Good.add hs.2 hadd⟩
          · dsimp only at h
            obtain ⟨b1, hb1, h⟩ := bind_ok_inv h
            split at h
            · obtain ⟨s4, hs4, h⟩ := bind_ok_inv h
              obtain rfl := ok_pair_snd h
              exact finish_encaps_sized hs4
            · obtain rfl := ok_pair_snd h; trivial
      · obtain rfl := ok_pair_snd h; exact hs
    · obtain rfl := ok_pair_snd h; exact hs
  · -- Ct2Sampled
    simp only [State.epoch, bind_tc_ok] at h
    repeat' first
      | (obtain ⟨_, _, h⟩ := bind_ok_inv h)
      | split at h
      | (obtain rfl := ok_pair_snd h; trivial)
  · -- Failed
    simp only [State.epoch, bind_tc_ok] at h
    obtain rfl := ok_pair_snd h
    trivial


/-- The same for a send step, whose result is `((message, output, state), rng)`. -/
theorem ok_send_state {α β γ δ : Type} {a a' : α} {b b' : β} {c c' : γ} {d d' : δ}
    (h : (ok ((a, b, c), d) : Result ((α × β × γ) × δ)) = ok ((a', b', c'), d')) : c = c' := by
  simp only [ok.injEq, Prod.mk.injEq] at h
  exact h.1.2.2

/-- The state a handed-back step returns is the one it was given. -/
theorem state_back_eq {st s : State} (h : state_back st = ok s) : s = st := by
  unfold state_back at h
  simp only [ok.injEq] at h
  exact h.symm

/-- **A successful `step_send` keeps the clauses.**  Only `HeaderReceived` makes a `ct1`, with
`encapsulate1`, and `Encapsulate1Total` caps what it returns at 4096 bytes.  Every other transition
moves the decoders and `ct1` unchanged and only advances an encoder. -/
theorem Braid.step_send_sized {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (hrng : RngTotal rc) (hencaps1 : Encapsulate1Total)
    (self : Braid) (state : State) (rng : R) {m : Msg} {out : Option Output} {s' : State}
    {rng' : R}
    (h : Braid.step_send rc crc self state rng = ok ((m, out, s'), rng'))
    (hs : State.sized state) : State.sized s' := by
  unfold Braid.step_send at h
  rcases state with
    ⟨epoch, auth⟩ | ⟨epoch, auth, kp, hdr_enc⟩ | ⟨epoch, auth, kp, ct1_dec, ek_enc⟩
    | ⟨epoch, auth, kp, ct1, ek_enc⟩ | ⟨epoch, auth, kp, ct1, ct2_dec⟩
    | ⟨epoch, auth, hdr_dec⟩ | ⟨epoch, auth, header, ek_dec⟩
    | ⟨epoch, auth, header, encaps, ct1, ct1_enc, ek_dec⟩
    | ⟨epoch, auth, encaps, ct1, ek_vector, ct1_enc⟩
    | ⟨epoch, auth, header, encaps, ct1, ek_dec⟩ | ⟨epoch, auth, ct2_enc⟩ | -
  · -- KeysUnsampled: a fresh key pair, or `Failed`; neither carries a clause.
    try dsimp only at h
    obtain ⟨⟨r, rng1⟩, hg, h⟩ := bind_ok_inv h
    rcases r with kp | e
    all_goals
      try dsimp only at h
      repeat' first
        | (obtain ⟨_, _, h⟩ := bind_ok_inv h)
        | split at h
        | (obtain rfl := ok_send_state h; trivial)
  · -- KeysSampled: only the encoder moves.
    try dsimp only at h
    repeat' first
      | (obtain ⟨_, _, h⟩ := bind_ok_inv h)
      | split at h
      | (obtain rfl := ok_send_state h; exact hs)
  · -- HeaderSent: only the encoder moves; the ct1 decoder is handed on as it is.
    try dsimp only at h
    repeat' first
      | (obtain ⟨_, _, h⟩ := bind_ok_inv h)
      | split at h
      | (obtain rfl := ok_send_state h; exact hs)
  · -- Ct1Received: only the encoder moves.
    try dsimp only at h
    repeat' first
      | (obtain ⟨_, _, h⟩ := bind_ok_inv h)
      | split at h
      | (obtain rfl := ok_send_state h; exact hs)
  · -- EkSentCt1Received: the state is handed back.
    try dsimp only at h
    obtain ⟨s2, hb, h⟩ := bind_ok_inv h
    obtain ⟨m2, hm, h⟩ := bind_ok_inv h
    obtain rfl := ok_send_state h
    rw [state_back_eq hb]
    exact hs
  · -- NoHeaderReceived
    try dsimp only at h
    obtain ⟨s2, hb, h⟩ := bind_ok_inv h
    obtain ⟨m2, hm, h⟩ := bind_ok_inv h
    obtain rfl := ok_send_state h
    rw [state_back_eq hb]
    exact hs
  · -- HeaderReceived: `ct1` is what `encapsulate1` returned, and is within the bound the KEM
    -- assumption `Encapsulate1Total` states for it.
    try dsimp only at h
    obtain ⟨⟨r, rng1⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨⟨r', rng1'⟩, hr', hcap⟩ := hencaps1 rc crc header.deref rng hrng
    rw [hr] at hr'
    simp only [ok.injEq, Prod.mk.injEq] at hr'
    obtain ⟨rfl, rfl⟩ := hr'
    rcases r with ⟨encaps', ct1', raw1⟩ | e
    · try dsimp only at h
      have hct1 : ct1'.length ≤ 4096 := hcap encaps' ct1' raw1 rfl
      repeat' first
        | (obtain ⟨_, _, h⟩ := bind_ok_inv h)
        | split at h
        | (obtain rfl := ok_send_state h; exact ⟨hct1, hs⟩)
    · try dsimp only at h
      repeat' first
        | (obtain ⟨_, _, h⟩ := bind_ok_inv h)
        | split at h
        | (obtain rfl := ok_send_state h; trivial)
  · -- Ct1Sampled: only the encoder moves.
    try dsimp only at h
    repeat' first
      | (obtain ⟨_, _, h⟩ := bind_ok_inv h)
      | split at h
      | (obtain rfl := ok_send_state h; exact hs)
  · -- EkReceivedCt1Sampled: only the encoder moves.
    try dsimp only at h
    repeat' first
      | (obtain ⟨_, _, h⟩ := bind_ok_inv h)
      | split at h
      | (obtain rfl := ok_send_state h; exact hs)
  · -- Ct1Acknowledged: the state is handed back.
    try dsimp only at h
    obtain ⟨s2, hb, h⟩ := bind_ok_inv h
    obtain ⟨m2, hm, h⟩ := bind_ok_inv h
    obtain rfl := ok_send_state h
    rw [state_back_eq hb]
    exact hs
  · -- Ct2Sampled
    try dsimp only at h
    repeat' first
      | (obtain ⟨_, _, h⟩ := bind_ok_inv h)
      | split at h
      | (obtain rfl := ok_send_state h; trivial)
  · -- Failed
    try dsimp only at h
    obtain ⟨m2, hm, h⟩ := bind_ok_inv h
    obtain rfl := ok_send_state h
    trivial

/-- A `Vec<u8>` clone is the vector itself. -/
theorem vecU8_clone_eq {v v' : alloc.vec.Vec U8}
    (h : alloc.vec.CloneVec.clone core.clone.CloneU8 v = ok v') : v = v' := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (vecU8_clone_no_panic v)
  rw [hr] at h
  cases h
  exact hp

/-- **Cloning a state keeps the clauses.**  A vector clones to itself, and a decoder clone is one
of the steps `Good` is closed under. -/
theorem State.clone_sized {self r : State} (h : State.Insts.CoreCloneClone.clone self = ok r)
    (hs : State.sized self) : State.sized r := by
  unfold State.Insts.CoreCloneClone.clone at h
  rcases self with
    ⟨epoch, auth⟩ | ⟨epoch, auth, kp, hdr_enc⟩ | ⟨epoch, auth, kp, ct1_dec, ek_enc⟩
    | ⟨epoch, auth, kp, ct1, ek_enc⟩ | ⟨epoch, auth, kp, ct1, ct2_dec⟩
    | ⟨epoch, auth, hdr_dec⟩ | ⟨epoch, auth, header, ek_dec⟩
    | ⟨epoch, auth, header, encaps, ct1, ct1_enc, ek_dec⟩
    | ⟨epoch, auth, encaps, ct1, ek_vector, ct1_enc⟩
    | ⟨epoch, auth, header, encaps, ct1, ek_dec⟩ | ⟨epoch, auth, ct2_enc⟩ | -
  · -- KeysUnsampled
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    simp only [ok.injEq] at h
    subst h
    trivial
  · -- KeysSampled
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    simp only [ok.injEq] at h
    subst h
    trivial
  · -- HeaderSent
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨d, hd, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    simp only [ok.injEq] at h
    subst h
    exact Good.clone hs hd
  · -- Ct1Received
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨v, hv, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    simp only [ok.injEq] at h
    subst h
    rw [← vecU8_clone_eq hv]
    exact hs
  · -- EkSentCt1Received
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨v, hv, h⟩ := bind_ok_inv h
    obtain ⟨d, hd, h⟩ := bind_ok_inv h
    simp only [ok.injEq] at h
    subst h
    rw [← vecU8_clone_eq hv]
    exact ⟨hs.1, Good.clone hs.2 hd⟩
  · -- NoHeaderReceived
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨d, hd, h⟩ := bind_ok_inv h
    simp only [ok.injEq] at h
    subst h
    exact Good.clone hs hd
  · -- HeaderReceived
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨d, hd, h⟩ := bind_ok_inv h
    simp only [ok.injEq] at h
    subst h
    exact Good.clone hs hd
  · -- Ct1Sampled
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨v1, hv1, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨d, hd, h⟩ := bind_ok_inv h
    simp only [ok.injEq] at h
    subst h
    rw [← vecU8_clone_eq hv1]
    exact ⟨hs.1, Good.clone hs.2 hd⟩
  · -- EkReceivedCt1Sampled
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨v, hv, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    simp only [ok.injEq] at h
    subst h
    rw [← vecU8_clone_eq hv]
    exact hs
  · -- Ct1Acknowledged
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨v1, hv1, h⟩ := bind_ok_inv h
    obtain ⟨d, hd, h⟩ := bind_ok_inv h
    simp only [ok.injEq] at h
    subst h
    rw [← vecU8_clone_eq hv1]
    exact ⟨hs.1, Good.clone hs.2 hd⟩
  · -- Ct2Sampled
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    simp only [ok.injEq] at h
    subst h
    trivial
  · -- Failed
    simp only [ok.injEq] at h
    subst h
    trivial

/-- A Braid satisfies the clauses when its state does. -/
def Braid.sized (b : Braid) : Prop := State.sized b.state

/-- The two clauses of `BraidT1` follow from `sized`. -/
theorem State.sized_ct1_bounded {s : State} (h : State.sized s) : State.ct1_bounded s := by
  rcases s with _|_|_|_|_|_|_|_|_|_|_|_ <;> simp_all [State.sized, State.ct1_bounded]

/-- **`send` keeps the clauses.** -/
theorem Braid.send_sized {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (hrng : RngTotal rc) (hencaps1 : Encapsulate1Total)
    (self : Braid) (rng : R) {msg : Msg} {ep : U64} {out : Option Output} {next : Braid} {rng' : R}
    (h : Braid.send rc crc self rng = ok ((msg, ep, out, next), rng'))
    (hs : Braid.sized self) : Braid.sized next := by
  unfold Braid.send at h
  obtain ⟨st, hc, h⟩ := bind_ok_inv h
  obtain ⟨⟨⟨m1, o1, n1⟩, rng1⟩, hstep, h⟩ := bind_ok_inv h
  obtain ⟨i, hi, h⟩ := bind_ok_inv h
  change ok ((_, _, _, _), _) = ok ((_, _, _, _), _) at h
  simp only [ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, -, -, rfl⟩, -⟩ := h
  exact Braid.step_send_sized rc crc hrng hencaps1 self st rng hstep (State.clone_sized hc hs)

/-- **`receive` keeps the clauses.** -/
theorem Braid.receive_sized (hl : Laws) (hct1len : Ct1LenTotal) (hct2len : Ct2LenTotal)
    (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal)
    (self : Braid) (msg : Msg) {ep : U64} {out : Option Output} {next : Braid}
    (h : Braid.receive self msg = ok (ep, out, next)) (hs : Braid.sized self) :
    Braid.sized next := by
  unfold Braid.receive at h
  obtain ⟨st, hc, h⟩ := bind_ok_inv h
  obtain ⟨⟨o, n1⟩, hstep, h⟩ := bind_ok_inv h
  have hn : State.sized n1 :=
    Braid.step_receive_sized hl hct1len hct2len hhdrlen hekveclen self st msg o n1 hstep
      (State.clone_sized hc hs)
  rcases o with _ | o'
  · try dsimp only at h
    obtain ⟨i, hi, h⟩ := bind_ok_inv h
    change ok (_, _, _) = ok (_, _, _) at h
    simp only [ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact hn
  · try dsimp only at h
    obtain ⟨o1, ho1, h⟩ := bind_ok_inv h
    change ok (_, _, _) = ok (_, _, _) at h
    simp only [ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact hn

/-- `commit` adopts the candidate. -/
theorem Braid.commit_sized {self next r : Braid} (h : Braid.commit self next = ok r)
    (hs : Braid.sized next) : Braid.sized r := by
  unfold Braid.commit at h
  simp only [ok.injEq] at h
  subst h
  exact hs

/-- A freshly built initiator satisfies the clauses: it holds no decoder and no `ct1`. -/
theorem Braid.initiator_sized {secret : Slice U8} {b : Braid} (h : Braid.initiator secret = ok b) :
    Braid.sized b := by
  unfold Braid.initiator at h
  obtain ⟨a, ha, h⟩ := bind_ok_inv h
  simp only [ok.injEq] at h
  subst h
  trivial

/-- A freshly built responder satisfies the clauses: its one decoder is `hdr_decoder`. -/
theorem Braid.responder_sized (hl : Laws) (hhdrlen : HeaderLenTotal) {secret : Slice U8}
    {b : Braid} (h : Braid.responder secret = ok b) : Braid.sized b := by
  unfold Braid.responder at h
  obtain ⟨a, ha, h⟩ := bind_ok_inv h
  obtain ⟨d, hd, h⟩ := bind_ok_inv h
  simp only [ok.injEq] at h
  subst h
  exact hdr_decoder_good hl hhdrlen hd

/-- The Braids a run of the crate can reach from the ones `Base` names: by `send` with an RNG
that answers, and by `receive`.  Adopting a candidate (`commit`) changes nothing. -/
inductive Braid.Run (Base : Braid → Prop) : Braid → Prop
  | base {b : Braid} : Base b → Braid.Run Base b
  | send {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
      (hrng : RngTotal rc) {self : Braid} {rng : R} {msg : Msg} {ep : U64}
      {out : Option Output} {next : Braid} {rng' : R} :
      Braid.Run Base self → Braid.send rc crc self rng = ok ((msg, ep, out, next), rng') →
      Braid.Run Base next
  | receive {self : Braid} {msg : Msg} {ep : U64} {out : Option Output} {next : Braid} :
      Braid.Run Base self → Braid.receive self msg = ok (ep, out, next) → Braid.Run Base next

/-- **Every Braid a run reaches from states that satisfy the clauses satisfies them.** -/
theorem Braid.Run.sized (hl : Laws) (hct1len : Ct1LenTotal) (hct2len : Ct2LenTotal)
    (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal) (hencaps1 : Encapsulate1Total)
    {Base : Braid → Prop} (hbase : ∀ b, Base b → Braid.sized b) {b : Braid}
    (hr : Braid.Run Base b) : Braid.sized b := by
  induction hr with
  | base hb => exact hbase _ hb
  | send hrng _ hsend ih =>
    exact Braid.send_sized _ _ hrng hencaps1 _ _ hsend ih
  | receive _ hrecv ih =>
    exact Braid.receive_sized hl hct1len hct2len hhdrlen hekveclen _ _ hrecv ih

/-- The constructors' Braids. -/
def Braid.Constructed (b : Braid) : Prop :=
  (∃ secret, Braid.initiator secret = ok b) ∨ (∃ secret, Braid.responder secret = ok b)

theorem Braid.Constructed.sized (hl : Laws) (hhdrlen : HeaderLenTotal) {b : Braid}
    (h : Braid.Constructed b) : Braid.sized b := by
  rcases h with ⟨secret, h⟩ | ⟨secret, h⟩
  · exact Braid.initiator_sized h
  · exact Braid.responder_sized hl hhdrlen h


/-! ## The theorems are not empty

A statement about every state a run reaches is empty if no state is reached.  The constructors do
return (`BraidT1`'s `initiator_no_panic`, `responder_no_panic`), so `Braid.Run Braid.Constructed`
has members, and a `send` from one of them returns (`send_no_panic`), so it has members that are
not constructor outputs. -/

/-- An initiator exists, and it is a Braid the run closure starts from. -/
theorem Braid.Run.exists_initiator (hkdf : HkdfSha256Total) (hz : ZeroizingArrayRoundTrip)
    (secret : Slice U8) : ∃ b, Braid.Run Braid.Constructed b := by
  obtain ⟨b, hb, -⟩ := WP.spec_imp_exists (Braid.initiator_no_panic hkdf hz secret)
  exact ⟨b, Braid.Run.base (Or.inl ⟨secret, hb⟩)⟩

/-- A responder exists, and it is a Braid the run closure starts from. -/
theorem Braid.Run.exists_responder (hkdf : HkdfSha256Total) (hz : ZeroizingArrayRoundTrip)
    (hdnew : DecoderNewTotal) (hhdrlen : HeaderLenTotal) (secret : Slice U8) :
    ∃ b, Braid.Run Braid.Constructed b := by
  obtain ⟨b, hb, -⟩ := WP.spec_imp_exists (Braid.responder_no_panic hkdf hz hdnew hhdrlen secret)
  exact ⟨b, Braid.Run.base (Or.inr ⟨secret, hb⟩)⟩

/-- **A Braid the run closure reaches by a `send`, not by a constructor, exists.** -/
theorem Braid.Run.exists_send {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (hrng : RngTotal rc)
    (henc : EncoderCloneTotal) (hdec : DecoderCloneTotal)
    (hkp : KeyPairCloneTotal) (hes : EncapsStateCloneTotal) (hgen : KeyPairGenerateTotal)
    (hhdr : KeyPairHeaderTotal) (hmac : HmacSha256Total) (henew : EncoderNewTotal)
    (henext : EncoderNextChunkTotal) (hkdf : HkdfSha256Total) (hencaps1 : Encapsulate1Total)
    (hz : ZeroizingArrayRoundTrip) (hzz : ArrayZeroizeTotal) (hrf : RangeFullIndexTotal)
    (secret : Slice U8) (rng : R) :
    ∃ b b', Braid.Run Braid.Constructed b ∧ Braid.Run Braid.Constructed b' ∧
      ∃ msg ep out rng', Braid.send rc crc b rng = ok ((msg, ep, out, b'), rng') := by
  obtain ⟨b, hb, -⟩ := WP.spec_imp_exists (Braid.initiator_no_panic hkdf hz secret)
  have hrun : Braid.Run Braid.Constructed b := Braid.Run.base (Or.inl ⟨secret, hb⟩)
  obtain ⟨⟨⟨msg, ep, out, b'⟩, rng'⟩, hs, -⟩ := WP.spec_imp_exists
    (Braid.send_no_panic rc crc hrng henc hdec hkp hes hgen hhdr hmac henew henext hkdf hencaps1
      hz hzz hrf b rng)
  exact ⟨b, b', hrun, Braid.Run.send hrng hrun hs, msg, ep, out, rng', hs⟩

end Tacenta.BraidPreserve

/-! ## Axiom pins

The axiom base of each result, held by the build. -/

/--
info: 'Tacenta.BraidPreserve.Braid.step_send_sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_erasure.Decoder.add_chunk,
 tacenta_erasure.Decoder.message,
 tacenta_erasure.Encoder.new,
 tacenta_erasure.Encoder.next_chunk,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_erasure.Decoder.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.BraidPreserve.Braid.step_send_sized

/--
info: 'Tacenta.BraidPreserve.Braid.step_receive_sized' depends on axioms: [propext,
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
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 tacenta_erasure.Decoder.add_chunk,
 tacenta_erasure.Decoder.message,
 tacenta_erasure.Decoder.new,
 tacenta_erasure.Encoder.new,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_erasure.Decoder.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.BraidPreserve.Braid.step_receive_sized

/--
info: 'Tacenta.BraidPreserve.State.clone_sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_erasure.Decoder.add_chunk,
 tacenta_erasure.Decoder.message,
 tacenta_erasure.Decoder.Insts.CoreCloneClone.clone,
 tacenta_erasure.Encoder.Insts.CoreCloneClone.clone,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.BraidPreserve.State.clone_sized

/--
info: 'Tacenta.BraidPreserve.Braid.send_sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_erasure.Decoder.add_chunk,
 tacenta_erasure.Decoder.message,
 tacenta_erasure.Encoder.new,
 tacenta_erasure.Encoder.next_chunk,
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
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.BraidPreserve.Braid.send_sized

/--
info: 'Tacenta.BraidPreserve.Braid.receive_sized' depends on axioms: [propext,
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
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 tacenta_erasure.Decoder.add_chunk,
 tacenta_erasure.Decoder.message,
 tacenta_erasure.Decoder.new,
 tacenta_erasure.Encoder.new,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
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
#print axioms Tacenta.BraidPreserve.Braid.receive_sized

/--
info: 'Tacenta.BraidPreserve.Braid.commit_sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_erasure.Decoder.add_chunk,
 tacenta_erasure.Decoder.message,
 tacenta_erasure.Decoder.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.BraidPreserve.Braid.commit_sized

/--
info: 'Tacenta.BraidPreserve.Braid.initiator_sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
 tacenta_kdf.hkdf_sha256,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 zeroize.Zeroizing,
 tacenta_erasure.Decoder.add_chunk,
 tacenta_erasure.Decoder.message,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_erasure.Decoder.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.BraidPreserve.Braid.initiator_sized

/--
info: 'Tacenta.BraidPreserve.Braid.responder_sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
 tacenta_kdf.hkdf_sha256,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 zeroize.Zeroizing,
 tacenta_erasure.Decoder.add_chunk,
 tacenta_erasure.Decoder.message,
 tacenta_erasure.Decoder.new,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_erasure.Decoder.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.BraidPreserve.Braid.responder_sized

/--
info: 'Tacenta.BraidPreserve.Braid.Run.sized' depends on axioms: [propext,
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
#print axioms Tacenta.BraidPreserve.Braid.Run.sized

/--
info: 'Tacenta.BraidPreserve.Braid.Constructed.sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
 tacenta_kdf.hkdf_sha256,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 zeroize.Zeroizing,
 tacenta_erasure.Decoder.add_chunk,
 tacenta_erasure.Decoder.message,
 tacenta_erasure.Decoder.new,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_erasure.Decoder.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.BraidPreserve.Braid.Constructed.sized

/--
info: 'Tacenta.BraidPreserve.State.sized_ct1_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_erasure.Decoder.add_chunk,
 tacenta_erasure.Decoder.message,
 tacenta_erasure.Decoder.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.BraidPreserve.State.sized_ct1_bounded

/--
info: 'Tacenta.BraidPreserve.Braid.Run.exists_initiator' depends on axioms: [propext,
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
#print axioms Tacenta.BraidPreserve.Braid.Run.exists_initiator

/--
info: 'Tacenta.BraidPreserve.Braid.Run.exists_responder' depends on axioms: [propext,
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
#print axioms Tacenta.BraidPreserve.Braid.Run.exists_responder

/--
info: 'Tacenta.BraidPreserve.Braid.Run.exists_send' depends on axioms: [propext,
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
#print axioms Tacenta.BraidPreserve.Braid.Run.exists_send

/-! ## Statement pins

The axiom pins hold the constants a result depends on and not what it says.  These hold the
statements of the results below while they are present; no gate requires a statement pin to exist. -/

/--
info: Tacenta.BraidPreserve.Braid.step_send_sized {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
  (hrng : RngTotal rc) (hencaps1 : Encapsulate1Total) (self : Braid) (state : State) (rng : R) {m : Msg}
  {out : Option Output} {s' : State} {rng' : R} (h : Braid.step_send rc crc self state rng = ok ((m, out, s'), rng'))
  (hs : Tacenta.BraidPreserve.State.sized state) : Tacenta.BraidPreserve.State.sized s'
-/
#guard_msgs in
#check Tacenta.BraidPreserve.Braid.step_send_sized

/--
info: Tacenta.BraidPreserve.Braid.step_receive_sized (hl : Laws) (hct1len : Ct1LenTotal) (hct2len : Ct2LenTotal)
  (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal) (self : Braid) (state : State) (msg : Msg)
  (out : Option Output) (s' : State) (h : self.step_receive state msg = ok (out, s'))
  (hs : Tacenta.BraidPreserve.State.sized state) : Tacenta.BraidPreserve.State.sized s'
-/
#guard_msgs in
#check Tacenta.BraidPreserve.Braid.step_receive_sized

/--
info: Tacenta.BraidPreserve.Braid.send_sized {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
  (hrng : RngTotal rc) (hencaps1 : Encapsulate1Total) (self : Braid) (rng : R) {msg : Msg} {ep : U64}
  {out : Option Output} {next : Braid} {rng' : R} (h : Braid.send rc crc self rng = ok ((msg, ep, out, next), rng'))
  (hs : Tacenta.BraidPreserve.Braid.sized self) : Tacenta.BraidPreserve.Braid.sized next
-/
#guard_msgs in
#check Tacenta.BraidPreserve.Braid.send_sized

/--
info: Tacenta.BraidPreserve.Braid.receive_sized (hl : Laws) (hct1len : Ct1LenTotal) (hct2len : Ct2LenTotal)
  (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal) (self : Braid) (msg : Msg) {ep : U64} {out : Option Output}
  {next : Braid} (h : self.receive msg = ok (ep, out, next)) (hs : Tacenta.BraidPreserve.Braid.sized self) :
  Tacenta.BraidPreserve.Braid.sized next
-/
#guard_msgs in
#check Tacenta.BraidPreserve.Braid.receive_sized

/--
info: Tacenta.BraidPreserve.Braid.Run.sized (hl : Laws) (hct1len : Ct1LenTotal) (hct2len : Ct2LenTotal)
  (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal) (hencaps1 : Encapsulate1Total) {Base : Braid → Prop}
  (hbase : ∀ (b : Braid), Base b → Tacenta.BraidPreserve.Braid.sized b) {b : Braid}
  (hr : Tacenta.BraidPreserve.Braid.Run Base b) : Tacenta.BraidPreserve.Braid.sized b
-/
#guard_msgs in
#check Tacenta.BraidPreserve.Braid.Run.sized

/--
info: Tacenta.BraidPreserve.Braid.Run.exists_initiator (hkdf : HkdfSha256Total) (hz : ZeroizingArrayRoundTrip)
  (secret : Slice U8) : ∃ b, Tacenta.BraidPreserve.Braid.Run Tacenta.BraidPreserve.Braid.Constructed b
-/
#guard_msgs in
#check Tacenta.BraidPreserve.Braid.Run.exists_initiator

/--
info: Tacenta.BraidPreserve.Braid.Run.exists_responder (hkdf : HkdfSha256Total) (hz : ZeroizingArrayRoundTrip)
  (hdnew : DecoderNewTotal) (hhdrlen : HeaderLenTotal) (secret : Slice U8) :
  ∃ b, Tacenta.BraidPreserve.Braid.Run Tacenta.BraidPreserve.Braid.Constructed b
-/
#guard_msgs in
#check Tacenta.BraidPreserve.Braid.Run.exists_responder

/--
info: Tacenta.BraidPreserve.Braid.Run.exists_send {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
  (hrng : RngTotal rc) (henc : EncoderCloneTotal) (hdec : DecoderCloneTotal) (hkp : KeyPairCloneTotal)
  (hes : EncapsStateCloneTotal) (hgen : KeyPairGenerateTotal) (hhdr : KeyPairHeaderTotal) (hmac : HmacSha256Total)
  (henew : EncoderNewTotal) (henext : EncoderNextChunkTotal) (hkdf : HkdfSha256Total) (hencaps1 : Encapsulate1Total)
  (hz : ZeroizingArrayRoundTrip) (hzz : ArrayZeroizeTotal) (hrf : RangeFullIndexTotal) (secret : Slice U8) (rng : R) :
  ∃ b b',
    Tacenta.BraidPreserve.Braid.Run Tacenta.BraidPreserve.Braid.Constructed b ∧
      Tacenta.BraidPreserve.Braid.Run Tacenta.BraidPreserve.Braid.Constructed b' ∧
        ∃ msg ep out rng', Braid.send rc crc b rng = ok ((msg, ep, out, b'), rng')
-/
#guard_msgs in
#check Tacenta.BraidPreserve.Braid.Run.exists_send

/--
info: Tacenta.BraidPreserve.State.clone_sized {self r : State} (h : State.Insts.CoreCloneClone.clone self = ok r)
  (hs : Tacenta.BraidPreserve.State.sized self) : Tacenta.BraidPreserve.State.sized r
-/
#guard_msgs in
#check Tacenta.BraidPreserve.State.clone_sized

/--
info: Tacenta.BraidPreserve.Braid.commit_sized {self next r : Braid} (h : self.commit next = ok r)
  (hs : Tacenta.BraidPreserve.Braid.sized next) : Tacenta.BraidPreserve.Braid.sized r
-/
#guard_msgs in
#check Tacenta.BraidPreserve.Braid.commit_sized

/--
info: Tacenta.BraidPreserve.Braid.initiator_sized {secret : Slice U8} {b : Braid} (h : Braid.initiator secret = ok b) :
  Tacenta.BraidPreserve.Braid.sized b
-/
#guard_msgs in
#check Tacenta.BraidPreserve.Braid.initiator_sized

/--
info: Tacenta.BraidPreserve.Braid.responder_sized (hl : Laws) (hhdrlen : HeaderLenTotal) {secret : Slice U8} {b : Braid}
  (h : Braid.responder secret = ok b) : Tacenta.BraidPreserve.Braid.sized b
-/
#guard_msgs in
#check Tacenta.BraidPreserve.Braid.responder_sized

/--
info: Tacenta.BraidPreserve.Braid.Constructed.sized (hl : Laws) (hhdrlen : HeaderLenTotal) {b : Braid}
  (h : Tacenta.BraidPreserve.Braid.Constructed b) : Tacenta.BraidPreserve.Braid.sized b
-/
#guard_msgs in
#check Tacenta.BraidPreserve.Braid.Constructed.sized

/--
info: Tacenta.BraidPreserve.State.sized_ct1_bounded {s : State} (h : Tacenta.BraidPreserve.State.sized s) :
  State.ct1_bounded s
-/
#guard_msgs in
#check Tacenta.BraidPreserve.State.sized_ct1_bounded

/-! ## Definition pins

The definitions that carry the claim.  A change to a clause, a constructor or a law fails the
build while its pin is present; no gate requires a definition pin to exist. -/

/--
info: def Tacenta.BraidPreserve.State.sized : State → Prop :=
fun x =>
  match x with
  | State.KeysUnsampled a a_1 => True
  | State.KeysSampled a a_1 a_2 a_3 => True
  | State.HeaderSent a a_1 a_2 ct1_dec a_3 => Good 4096 ct1_dec
  | State.Ct1Received a a_1 a_2 ct1 a_3 => ct1.length ≤ 4096
  | State.EkSentCt1Received a a_1 a_2 ct1 ct2_dec => ct1.length ≤ 4096 ∧ Good 4128 ct2_dec
  | State.NoHeaderReceived a a_1 hdr_dec => Good 4128 hdr_dec
  | State.HeaderReceived a a_1 a_2 ek_dec => Good 4128 ek_dec
  | State.Ct1Sampled a a_1 a_2 a_3 ct1 a_4 ek_dec => ct1.length ≤ 4096 ∧ Good 4128 ek_dec
  | State.EkReceivedCt1Sampled a a_1 a_2 ct1 a_3 a_4 => ct1.length ≤ 4096
  | State.Ct1Acknowledged a a_1 a_2 a_3 ct1 ek_dec => ct1.length ≤ 4096 ∧ Good 4128 ek_dec
  | State.Ct2Sampled a a_1 a_2 => True
  | State.Failed => True
-/
#guard_msgs in
#print Tacenta.BraidPreserve.State.sized

/--
info: def Tacenta.BraidPreserve.Braid.sized : Braid → Prop :=
fun b => Tacenta.BraidPreserve.State.sized b.state
-/
#guard_msgs in
#print Tacenta.BraidPreserve.Braid.sized

/--
info: inductive Tacenta.BraidPreserve.Braid.Run : (Braid → Prop) → Braid → Prop
number of parameters: 1
constructors:
Tacenta.BraidPreserve.Braid.Run.base : ∀ {Base : Braid → Prop} {b : Braid},
  Base b → Tacenta.BraidPreserve.Braid.Run Base b
Tacenta.BraidPreserve.Braid.Run.send : ∀ {Base : Braid → Prop} {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R},
  RngTotal rc →
    ∀ {self : Braid} {rng : R} {msg : Msg} {ep : U64} {out : Option Output} {next : Braid} {rng' : R},
      Tacenta.BraidPreserve.Braid.Run Base self →
        Braid.send rc crc self rng = ok ((msg, ep, out, next), rng') → Tacenta.BraidPreserve.Braid.Run Base next
Tacenta.BraidPreserve.Braid.Run.receive : ∀ {Base : Braid → Prop} {self : Braid} {msg : Msg} {ep : U64}
  {out : Option Output} {next : Braid},
  Tacenta.BraidPreserve.Braid.Run Base self →
    self.receive msg = ok (ep, out, next) → Tacenta.BraidPreserve.Braid.Run Base next
-/
#guard_msgs in
#print Tacenta.BraidPreserve.Braid.Run

/--
info: def Tacenta.BraidPreserve.Braid.Constructed : Braid → Prop :=
fun b => (∃ secret, Braid.initiator secret = ok b) ∨ ∃ secret, Braid.responder secret = ok b
-/
#guard_msgs in
#print Tacenta.BraidPreserve.Braid.Constructed
