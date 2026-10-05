/-!
# Removal that moves the last entry into the slot

`PrekeyStore::take_one_time` and `take_one_time_kem` delete a consumed one-time prekey by zeroizing
it, swapping it with the last entry of its list and popping the now-dead tail slot (the
shipping code names this shape and why in `lifecycle.rs`; it is not `Vec::swap_remove`, which leaves
a live copy of the moved secret beyond the new length). `session-persistence.md`, Prekey store, says
that the order of the one-time lists is meaningful and that consuming an entry moves the last entry
into its place.

The model used an order-preserving `filter` for this removal until `GAP-REGISTER.md` row `E2E-03`
recorded that the two differ, for a list without repeats such as a store's, whenever the consumed
entry is neither the last nor the one before it. `swapRemove` is the removal the page and the code
describe.
-/

namespace Model

/-- Remove the first entry satisfying `p`: the last entry moves into its slot and the list is one
shorter. A list with no such entry is unchanged. The code removes the first entry with the
identifier; the store invariant makes identifiers unique, so first and only coincide. -/
def swapRemove {α : Type} (p : α → Bool) (l : List α) : List α :=
  match l.findIdx? p, l.getLast? with
  | some i, some last => (l.set i last).dropLast
  | _, _ => l

/-! `swapRemove` is structural: a view of the entries may be mapped through
    the removal as long as it preserves the predicate.  Lifecycle refinement
    uses this to transport the generated KEM vector mutation into the model's
    byte-view list. -/
theorem map_swapRemove {α β : Type} (f : α → β) (p : α → Bool) (q : β → Bool)
    (l : List α) (hp : ∀ x, q (f x) = p x) :
    (swapRemove p l).map f = swapRemove q (l.map f) := by
  simp only [swapRemove, List.findIdx?_map]
  have hpfun : (q ∘ f) = p := by
    funext x
    exact hp x
  rw [hpfun]
  cases hfind : l.findIdx? p with
  | none => simp
  | some i =>
    cases hlast : l.getLast? with
    | none => simp [hlast]
    | some last =>
      simp [hlast, List.map_set, List.map_dropLast]

theorem swapRemove_of_no_match {α : Type} (p : α → Bool) (l : List α)
    (h : l.findIdx? p = none) : swapRemove p l = l := by
  simp [swapRemove, h]

/-- A removal shortens the list by one. -/
theorem swapRemove_length_of_match {α : Type} (p : α → Bool) (l : List α) (i : Nat)
    (h : l.findIdx? p = some i) : (swapRemove p l).length + 1 = l.length := by
  have hi : i < l.length := by
    have := List.findIdx?_eq_some_iff_findIdx_eq.mp h
    exact this.1
  have hne : l ≠ [] := by
    intro hl
    subst hl
    simp at hi
  obtain ⟨last, hlast⟩ : ∃ last, l.getLast? = some last := by
    cases hg : l.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hne
    | some last => exact ⟨last, rfl⟩
  simp only [swapRemove, h, hlast, List.length_dropLast, List.length_set]
  omega

/-- The consumed entry is not the last one: the last entry takes its slot, which an
order-preserving removal would not do. -/
example : swapRemove (fun x => x == 1) [1, 2, 3, 4] = [4, 2, 3] := by decide

/-- The consumed entry is the last one, or the one before it: the two removals agree. -/
example : swapRemove (fun x => x == 4) [1, 2, 3, 4] = [1, 2, 3] := by decide
example : swapRemove (fun x => x == 3) [1, 2, 3, 4] = [1, 2, 4] := by decide

/-- The order-preserving removal the model used, for comparison with the example above. -/
example : [1, 2, 3, 4].filter (fun x => !(x == 1)) = [2, 3, 4] := by decide

end Model
