/-
Proofs.MemorySafety: the state stays bounded, over any sequence of operations.

Two things share this name and only one of them is here.

**No panic, no out-of-bounds access.** That is tier T1, proved against the
translated Rust in `tacenta-proofs/translation/Translation/T1.lean`, in a
separate package because it needs Mathlib through the Aeneas library. It is not
restated here and cannot be imported here. `CLAIMS.md` records it.

**Nothing grows without limit.** That is a property of the model, and it is what
this file proves. The distinction matters: code can be free of panics and still
be made to consume every byte a machine has, which is a denial of service rather
than a memory-safety violation and is no less effective for it.

The per-call bound was already proved, in `Proofs.RatchetCorrectness`: one skip
leaves the store within the cap, given it started there. It is stated in exactly
the form an induction wants -- premise and conclusion the same shape -- which is
why this file is short. What that does not say
is that a *sequence* of operations keeps it there, and a peer does not send one
message. So the statement here is inductive: the bound holds after any number of
steps of any kind, from any start that respects it.
-/
import Proofs.RatchetCorrectness
import Model.Ratchet

namespace Proofs.MemorySafety

open Model.State Model.Ratchet

/-! ## What a peer can make happen

Every transition the model offers, as a relation. A peer chooses the messages and
therefore drives these, in any order and as often as it likes -- which is exactly
why the bound has to survive sequences rather than single calls. -/

inductive Step : State → State → Prop where
  /-- Skipping forward, on a header that asked for it. -/
  | skip {st st' upto} : skipMessageKeys st upto = some st' → Step st st'
  /-- Taking a stored key. -/
  | took {st st' h mk} : trySkipped st h = some (st', mk) → Step st st'
  /-- Counting a received message and dropping what expired. -/
  | aged {st} : Step st (ageStore st)
  /-- Sending. -/
  | sent {st st' h mk} : send st = some (st', h, mk) → Step st st'
  /-- A ratchet step. -/
  | ratcheted {st h d1 d2 p} : Step st (dhRatchet st h d1 d2 p)

/-- Any number of steps. -/
inductive Reachable : State → State → Prop where
  | refl {st} : Reachable st st
  | step {a b c} : Reachable a b → Step b c → Reachable a c

/-! ## The invariant

The store is the only part of the state whose size a peer influences. Everything
else is fixed-width: a handful of keys and counters. -/

/-- The bound survives one step of any kind. -/
theorem step_preserves_bound {st st' : State}
    (h : st.skipped.length ≤ maxSkippedStore) (hs : Step st st') :
    st'.skipped.length ≤ maxSkippedStore := by
  cases hs with
  | skip hsk =>
    exact Proofs.RatchetCorrectness.skipMessageKeys_store_bounded _ _ _ h hsk
  | took ht =>
    -- Taking a stored key filters the store, and a filter never grows a list.
    unfold trySkipped at ht
    split at ht
    · injection ht with ht'
      -- The result is a pair, so the equality splits before it substitutes.
      simp only [Prod.mk.injEq] at ht'
      obtain ⟨rfl, -⟩ := ht'
      simp only
      exact Nat.le_trans (List.length_filter_le _ _) h
    · exact absurd ht (by simp)
  | aged =>
    -- Ageing filters the store, and a filter never grows a list.
    simp only [ageStore]
    exact Nat.le_trans (List.length_filter_le _ _) h
  | sent hsd =>
    unfold send at hsd
    split at hsd
    · exact absurd hsd (by simp)
    · split at hsd
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsd
        obtain ⟨rfl, -, -⟩ := hsd
        exact h
      · exact absurd hsd (by simp)
  | ratcheted => exact h

/-- **So it survives any sequence.** Whatever a peer does, in whatever order and
however many times, the skipped-key store stays within its cap.

    This is the statement that matters, and it is stronger than the per-call
    bound in a way that is easy to miss: a bound that holds for one call and not
    for a sequence bounds nothing, because a peer sends more than one message. -/
theorem reachable_stays_bounded {init st : State}
    (h : init.skipped.length ≤ maxSkippedStore) (hr : Reachable init st) :
    st.skipped.length ≤ maxSkippedStore := by
  induction hr with
  | refl => exact h
  | step _ hs ih => exact step_preserves_bound ih hs

/-- A fresh session starts with an empty store, so every state a session can
reach is bounded. The premise of the theorem above, discharged. -/
theorem a_session_stays_bounded {sk pub : Key} {labels : LabelSet} {st : State}
    (hr : Reachable (initReceiver sk pub labels) st) :
    st.skipped.length ≤ maxSkippedStore :=
  reachable_stays_bounded (by simp [initReceiver]) hr

/-! ## What is not covered

**The rest of the state is fixed-width**, so nothing else here can grow: the
keys are keys and the counters are counters. That is true by inspection of the
structure rather than by a theorem, and it is worth saying only because a reader
may wonder why the store gets all the attention.

**Counters can still run out.** The model's operations refuse a step past a
counter's ceiling, as the core does (ratchet.md, Sending and receiving;
`Model.Ratchet.send_ns_le`, `Model.Ratchet.receive_events_lt`), so a chain whose
counter reaches its ceiling goes no further. It is not a memory-safety question
but it is the other way a long-lived session ends badly.

**Nothing here is about the implementation.** No panic and no out-of-bounds
access is T1, in another package, against the translated Rust. -/

end Proofs.MemorySafety
