/-
Proofs.KeyErasure: a key that has been used is gone from the state.

There are two senses of a key being gone and only one of them is visible here.

**Out of the state.** After a stored key is used, the state no longer holds it,
so it cannot be served again. That is a property of the transitions and it is
what this file proves.

**Out of memory.** Whether the bytes are overwritten is a property of the
running program, not of the model, and the model has no memory to speak of. The
core carries erasing destructors for the ratchet state and the stored keys, and
`tacenta-spec/protocol/key-deletion.md` records what they do and do not cover --
including that the translation ignores `Drop` entirely, so *the erasure is
invisible to the proofs*. Nothing in this file changes that, and nothing in this
file should be read as covering it.

The first sense is worth proving on its own. A one-time key that survives its
use is a one-time key in name only, and that is the shape of defect a store
documented as a map but accumulating like a list would carry.
-/
import Model.Ratchet

namespace Proofs.KeyErasure

open Model.State Model.Ratchet

/-! ## A stored key is used once

`trySkipped` returns a stored key and removes it in the same step. These say the
removal is complete: nothing matching remains, so a second attempt finds
nothing. -/

/-- After a stored key is taken, no entry for that ratchet key and number
remains. -/
theorem trySkipped_removes_the_entry (st : State) (h : Header) (r : State × Key)
    (ht : trySkipped st h = some r) :
    ∀ e ∈ r.1.skipped, ¬(e.1 = h.dh ∧ e.2.1 = h.n) := by
  unfold trySkipped at ht
  split at ht
  · injection ht with ht'
    subst ht'
    intro e he
    simp only [List.mem_filter, Bool.not_eq_true', Bool.and_eq_false_iff,
      beq_eq_false_iff_ne] at he
    rintro ⟨h1, h2⟩
    rcases he.2 with hk | hk
    · exact hk h1
    · exact hk h2
  · exact absurd ht (by simp)

/-- So the same key cannot be served twice: a second attempt finds nothing.

    This is the property that makes a stored key one-use, and it is what stops a
    replayed message being decrypted a second time from the store. -/
theorem trySkipped_is_once (st : State) (h : Header) (r : State × Key)
    (ht : trySkipped st h = some r) : trySkipped r.1 h = none := by
  have hgone := trySkipped_removes_the_entry st h r ht
  unfold trySkipped
  cases hf : r.1.skipped.find? (fun x => x.1 == h.dh && x.2.1 == h.n) with
  | none => rfl
  | some e =>
    have hmem := List.find?_some hf
    have hin := List.mem_of_find?_eq_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hmem
    exact absurd hmem (hgone e hin)

/-! ## Expiry removes what it claims to

The store's other exit. Ageing drops every entry past the cap, so a key that has
outlived the interval is not merely unreachable but absent. -/

theorem ageStore_drops_the_expired (st : State) :
    ∀ e ∈ (ageStore st).skipped,
      st.events + 1 - e.2.2.1 < Model.State.maxSkippedAge := by
  intro e he
  simp only [ageStore, List.mem_filter, decide_eq_true_eq] at he
  exact he.2

/-- And ageing never adds. Together with the above, the store after a step holds
a subset of what it held, minus everything expired. -/
theorem ageStore_only_removes (st : State) :
    ∀ e ∈ (ageStore st).skipped, e ∈ st.skipped := by
  intro e he
  simp only [ageStore, List.mem_filter] at he
  exact he.1

end Proofs.KeyErasure
