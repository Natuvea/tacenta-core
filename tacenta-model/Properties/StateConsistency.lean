/-
Properties.StateConsistency: what each operation does to the state, and what it
leaves alone.

The ratchet's counters are what order messages. A header names the chain a
message came from and its position in that chain, and a receiver uses those to
decide whether a message is next, early, or already seen. If a counter advanced
by two, or an operation quietly moved one it had no business touching, the
ordering would be wrong in a way no round-trip test would notice: messages would
still decrypt, in the wrong order or not at all, depending on the peer.

So these are the small statements. Each says either "this advances by exactly
one" or "this leaves that alone", and together they are why the header's three
fields mean what the specification says they mean.

Nothing here needs an adversary. These are properties of the model's own
transitions, which is why this file could be written before the ones that do.
-/
import Model.Ratchet

namespace Properties.StateConsistency

open Model.State Model.Ratchet

/-! ## Sending

The simplest transition, and the one the others are measured against: one step
of the sending chain, one message number, nothing else. -/

/-- Sending fails exactly when there is no sending chain, and for no other
reason. A party that has not yet taken its first ratchet step has none. -/
theorem send_none_iff (st : State) : send st = none ↔ st.cks = none := by
  constructor
  · intro h
    cases hc : st.cks with
    | none => rfl
    | some ck => rw [send, hc] at h; exact absurd h (by simp)
  · intro h; rw [send, h]

/-- A send advances the message number by exactly one. -/
theorem send_advances_ns (st st' : State) (h : Header) (mk : Key)
    (hs : send st = some (st', h, mk)) : st'.ns = st.ns + 1 := by
  unfold send at hs
  split at hs
  · exact absurd hs (by simp)
  · -- The result is a triple, so the equality has to be split before the
    -- components can be substituted.
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, -, -⟩ := hs
    rfl

/-- The header carries the position *before* the step, not after.

    Off by one here and every receiver is a message ahead of the sender, which
    is the kind of error that still decrypts the first message. -/
theorem send_header_is_pre_state (st st' : State) (h : Header) (mk : Key)
    (hs : send st = some (st', h, mk)) :
    h.n = st.ns ∧ h.pn = st.pn ∧ h.dh = st.dhsPub := by
  unfold send at hs
  split at hs
  · exact absurd hs (by simp)
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl, -⟩ := hs
    exact ⟨rfl, rfl, rfl⟩

/-- Sending touches the sending chain and the message number, and nothing else.

    In particular it leaves the receiving side and the skipped-key store alone,
    which is what makes a conversation's two directions independent. -/
theorem send_preserves_the_rest (st st' : State) (h : Header) (mk : Key)
    (hs : send st = some (st', h, mk)) :
    st'.nr = st.nr ∧ st'.pn = st.pn ∧ st'.rk = st.rk ∧ st'.ckr = st.ckr
      ∧ st'.skipped = st.skipped ∧ st'.dhsPub = st.dhsPub
      ∧ st'.dhrPub = st.dhrPub ∧ st'.events = st.events := by
  unfold send at hs
  split at hs
  · exact absurd hs (by simp)
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, -, -⟩ := hs
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The Diffie-Hellman step

The one transition that moves both counters at once, and the only place the
previous chain's length is recorded. -/

/-- A ratchet step files the old sending count as the previous chain's length
and starts both counters again.

    `pn` is what tells a receiver how much of the *old* chain it may still be
    owed, so recording the wrong one strands messages that were in flight. -/
theorem dhRatchet_resets_counters (st : State) (h : Header) (d1 d2 p : Key) :
    (dhRatchet st h d1 d2 p).pn = st.ns
      ∧ (dhRatchet st h d1 d2 p).ns = 0
      ∧ (dhRatchet st h d1 d2 p).nr = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- A ratchet step adopts the peer's key from the header, and leaves the stored
skipped keys and the clock alone. Skipping happens before the step, deliberately:
those keys belong to the chain being left. -/
theorem dhRatchet_takes_header_key (st : State) (h : Header) (d1 d2 p : Key) :
    (dhRatchet st h d1 d2 p).dhrPub = some h.dh
      ∧ (dhRatchet st h d1 d2 p).skipped = st.skipped
      ∧ (dhRatchet st h d1 d2 p).events = st.events :=
  ⟨rfl, rfl, rfl⟩

/-! ## Skipping -/

/-- A successful skip leaves the receiving counter where it was or further on,
never behind. A counter that went backwards would re-derive keys already used. -/
theorem skipMessageKeys_nr_monotone (st st' : State) (upto : Nat)
    (h : skipMessageKeys st upto = some st') : st.nr ≤ st'.nr := by
  unfold skipMessageKeys at h
  split at h
  · split at h
    · injection h with h'; subst h'; exact Nat.le_refl _
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · injection h with h'
          subst h'
          -- The first guard rejected `upto ≤ nr`, so the new counter is past
          -- the old one. State the goal at the counter rather than at a record
          -- projection, which arithmetic cannot see through.
          show st.nr ≤ upto
          omega
  · injection h with h'; subst h'; exact Nat.le_refl _

/-- Skipping does not touch the sending side. The two directions advance
independently, and this is half of why. -/
theorem skipMessageKeys_preserves_sending (st st' : State) (upto : Nat)
    (h : skipMessageKeys st upto = some st') :
    st'.ns = st.ns ∧ st'.cks = st.cks ∧ st'.pn = st.pn := by
  unfold skipMessageKeys at h
  split at h
  · split at h
    · injection h with h'; subst h'; exact ⟨rfl, rfl, rfl⟩
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · injection h with h'; subst h'; exact ⟨rfl, rfl, rfl⟩
  · injection h with h'; subst h'; exact ⟨rfl, rfl, rfl⟩

/-! ## Receiving

Every accepted receive counts one message, whichever path it took. That count is
what the store's expiry is measured in, so a path that forgot to count would let
keys outlive their interval. -/

/-- Ageing the store counts exactly one message. -/
theorem ageStore_counts_one (st : State) : (ageStore st).events = st.events + 1 := rfl

/-- Ageing touches the clock and the store, and nothing else: not the chains,
not the counters, not the root key. -/
theorem ageStore_preserves_the_rest (st : State) :
    (ageStore st).ns = st.ns ∧ (ageStore st).nr = st.nr
      ∧ (ageStore st).rk = st.rk ∧ (ageStore st).cks = st.cks
      ∧ (ageStore st).ckr = st.ckr ∧ (ageStore st).pn = st.pn :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Taking a stored key removes that key and leaves every counter alone.

    A stored key belongs to a position already passed, so using it must not move
    the chain: a counter records where the *chain* is, not which message was last
    read. -/
theorem trySkipped_preserves_counters (st : State) (h : Header) (r : State × Key)
    (ht : trySkipped st h = some r) :
    r.1.ns = st.ns ∧ r.1.nr = st.nr ∧ r.1.cks = st.cks ∧ r.1.ckr = st.ckr
      ∧ r.1.events = st.events := by
  unfold trySkipped at ht
  split at ht
  · injection ht with ht'
    subst ht'
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact absurd ht (by simp)

end Properties.StateConsistency
