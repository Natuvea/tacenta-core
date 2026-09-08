/-
Proofs.ErrorHandling: each rejection is exactly the one specified, and each is
reachable.

Two failure modes matter for a guard, and they pull in opposite directions. A
guard that rejects too little lets a peer exhaust memory. A guard that rejects
too much lets a peer deny service to a conversation that was working. Testing
finds neither reliably: a test supplies inputs it thought of, and a guard's
error is in the inputs nobody thought of.

So the statements here are *iff*. Not "this input is rejected" but "these inputs
and no others". That is the form that catches a bound which is off by one in
either direction.

The second half is smaller and still worth having: every rejection is reachable.
A guard that can never fire is either wrong or describes a condition that has
moved, and either way it is misleading to the next reader.
-/
import Model.Ratchet

namespace Proofs.ErrorHandling

open Model.State Model.Ratchet

/-! ## Skipping forward

The guard a hostile peer meets first: a header claims a message number, and
serving it means deriving and storing every key in between. -/

/-- Skipping is refused exactly when there is a receiving chain, the request is
ahead of the cursor, and it would breach one of the two bounds.

    Stated as an equivalence deliberately. The right-hand side is the
    specification's condition written out, so anything the implementation
    rejects beyond it, or fails to reject within it, is a difference this
    theorem cannot survive. -/
theorem skipMessageKeys_none_iff (st : State) (upto : Nat) :
    skipMessageKeys st upto = none
      ↔ (∃ ck, st.ckr = some ck) ∧ (∃ dhr, st.dhrPub = some dhr)
        ∧ st.nr < upto
        ∧ (st.nr + maxSkip < upto
            ∨ maxSkippedStore < st.skipped.length + (upto - st.nr)) := by
  unfold skipMessageKeys
  cases hck : st.ckr with
  | none => simp
  | some ck =>
    cases hdhr : st.dhrPub with
    | none => simp
    | some dhr =>
      simp only [hck, hdhr]
      by_cases h1 : upto ≤ st.nr
      · simp [h1, Nat.not_lt.mpr h1]
      · simp only [h1, if_false]
        by_cases h2 : upto > st.nr + maxSkip
        · simp [h2, Nat.lt_of_not_le h1]
        · simp only [h2, if_false]
          by_cases h3 : st.skipped.length + (upto - st.nr) > maxSkippedStore
          · simp [h3, Nat.lt_of_not_le h1]
          · simp only [h3, if_false]
            simp only [Nat.not_lt] at h2 h3
            simp [Nat.lt_of_not_le h1, Nat.not_lt.mpr h2, Nat.not_lt.mpr h3]

/-- Skipping with no receiving chain **succeeds**, as a no-op.

    Worth pinning because it is a decision rather than an accident, and reads as
    an oversight otherwise. A party that has not taken its first ratchet step has
    no chain to skip on, and nothing to store; refusing here would reject the
    very first message of a session. The error, if there is one, surfaces at
    `receive`, which needs a receiving chain and says so. -/
theorem skipMessageKeys_no_chain_is_a_noop (st : State) (upto : Nat)
    (h : st.ckr = none) : skipMessageKeys st upto = some st := by
  unfold skipMessageKeys
  rw [h]

/-! ## Both bounds are reachable

A guard that cannot fire is misleading. These are witnesses: concrete states and
requests that meet each rejection, so neither bound is decorative. -/

private def ck0 : Key := List.replicate 32 0x01
private def dh0 : Key := List.replicate 32 0x0a

/-- A state with a receiving chain, a cursor at zero, and a store of `n`
entries, all under a ratchet key the skip will not replace. -/
private def loaded (n : Nat) : State :=
  { initReceiver ck0 dh0 .tacenta with
      ckr := some ck0, dhrPub := some dh0,
      skipped := (List.range n).map (fun i => (dh0, 1000000 + i, 0, ck0)) }

/-- The per-chain bound fires: a request further ahead than `maxSkip`. -/
example : skipMessageKeys (loaded 0) (maxSkip + 1) = none := by native_decide

/-- One short of it does not. The bound is where it says it is. -/
example : (skipMessageKeys (loaded 0) maxSkip).isSome := by native_decide

/-- The total bound fires on a request the per-chain bound would allow, which is
the case the two bounds exist separately to cover. -/
example :
    skipMessageKeys (loaded (maxSkippedStore - 10)) 100 = none := by native_decide

/-- And a request that fits under both is served. -/
example : (skipMessageKeys (loaded 10) 10).isSome := by native_decide

/-! ## A refusal leaves nothing behind

The model returns an `Option`, so a refused operation yields no state at all
rather than a damaged one. That is structural rather than clever, and it is the
property that makes the bounds above worth having: a peer who trips one has
moved the receiver not at all. -/

theorem refused_skip_yields_no_state (st : State) (upto : Nat)
    (h : skipMessageKeys st upto = none) :
    ∀ st', skipMessageKeys st upto ≠ some st' := by
  intro st'
  rw [h]
  simp

end Proofs.ErrorHandling
