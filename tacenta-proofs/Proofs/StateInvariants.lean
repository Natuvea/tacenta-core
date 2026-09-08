/-
Proofs.StateInvariants: invariants the model maintains across its operations
(proof tier T2).

At present one invariant, and it is the one the skipped-key store's whole
representation rests on: no two entries share a ratchet key and message number.
The store is documented as a *map* from that pair to a message key, both the
model's lookup and the Rust core's rely on it, and storing replaces rather
than accumulates so that it holds. A peer that leaves a ratchet key and
returns to it is the sequence an accumulating store fails on: one pair holds
two keys and the second can never be found.

`tacenta-model/Properties/Invariants.lean` pins that sequence as a regression
test. This file proves the general statement, which is what the T3 refinement of
the lookup needs: the lookup can only be related to the model's when at most one
entry matches, and something has to establish that rather than assume it.
-/
import Proofs.RatchetCorrectness

namespace Proofs.StateInvariants

open Model.State
open Proofs.RatchetCorrectness

/-- No two entries share a ratchet key and message number. -/
def StoreIsMap (l : List (Key × Nat × Nat × Key)) : Prop :=
  l.Pairwise fun a b => ¬(a.1 = b.1 ∧ a.2.1 = b.2.1)

/-! ## What chain derivation numbers its keys

The numbers run from `start` and are consecutive, so they are distinct and they
stay inside the half-open range the caller asked for. Both facts come from
`deriveChain_get`, which already says entry `i` is numbered `start + i`. -/

theorem deriveChain_num_ge (ck : Key) (start c : Nat) :
    ∀ x ∈ (deriveChain ck start c).2, start ≤ x.1 := by
  induction c generalizing ck start with
  | zero => simp [deriveChain]
  | succ c ih =>
    intro x hx
    show start ≤ x.1
    have : (deriveChain ck start (c + 1)).2
        = (start, (kdfCk ck).2) :: (deriveChain (kdfCk ck).1 (start + 1) c).2 := rfl
    rw [this, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.le_refl _
    · exact Nat.le_of_succ_le (ih (kdfCk ck).1 (start + 1) x hx)

theorem deriveChain_num_lt (ck : Key) (start c : Nat) :
    ∀ x ∈ (deriveChain ck start c).2, x.1 < start + c := by
  induction c generalizing ck start with
  | zero => simp [deriveChain]
  | succ c ih =>
    intro x hx
    have : (deriveChain ck start (c + 1)).2
        = (start, (kdfCk ck).2) :: (deriveChain (kdfCk ck).1 (start + 1) c).2 := rfl
    rw [this, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have := ih (kdfCk ck).1 (start + 1) x hx
      omega

/-- The numbers are pairwise distinct, which is what makes a derived batch a map
on its own. -/
theorem deriveChain_nodup (ck : Key) (start c : Nat) :
    (deriveChain ck start c).2.Pairwise fun a b => a.1 ≠ b.1 := by
  induction c generalizing ck start with
  | zero => simp [deriveChain]
  | succ c ih =>
    have heq : (deriveChain ck start (c + 1)).2
        = (start, (kdfCk ck).2) :: (deriveChain (kdfCk ck).1 (start + 1) c).2 := rfl
    rw [heq, List.pairwise_cons]
    refine ⟨?_, ih (kdfCk ck).1 (start + 1)⟩
    intro b hb
    have := deriveChain_num_ge (kdfCk ck).1 (start + 1) c b hb
    omega

/-! ## Storing preserves the invariant -/

/-- A successful skip leaves the store a map, given it was one.

Three things have to hold together: what survives the replacement is still a
map, the newly derived batch is one on its own, and the two do not collide. The
third is what the replacement exists for, and it is why the model filters before
appending rather than simply appending. -/
theorem skipMessageKeys_preserves_map (st : State) (upto : Nat) (st' : State)
    (hpre : StoreIsMap st.skipped)
    (h : skipMessageKeys st upto = some st') :
    StoreIsMap st'.skipped := by
  unfold skipMessageKeys at h
  split at h
  · rename_i ck dhr _ _
    split at h
    · injection h with h'; subst h'; exact hpre
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · injection h with h'
          subst h'
          simp only [StoreIsMap]
          rw [List.pairwise_append]
          refine ⟨?_, ?_, ?_⟩
          · exact hpre.filter _
          · -- the derived batch: all share `dhr`, and their numbers are distinct
            have hnd := deriveChain_nodup ck st.nr (upto - st.nr)
            refine List.Pairwise.map _ ?_ hnd
            intro a b hab
            simp only
            rintro ⟨-, hn⟩
            exact hab hn
          · -- no collision: what survived was outside the replaced range, and
            -- everything derived is inside it
            intro a ha b hb
            simp only [List.mem_filter] at ha
            simp only [List.mem_map] at hb
            obtain ⟨hamem, hakeep⟩ := ha
            obtain ⟨y, hy, rfl⟩ := hb
            simp only [Bool.not_eq_true', Bool.and_eq_false_iff,
              beq_eq_false_iff_ne, decide_eq_false_iff_not] at hakeep
            intro ⟨hdh, hn⟩
            have hlo := deriveChain_num_ge ck st.nr (upto - st.nr) y hy
            have hhi := deriveChain_num_lt ck st.nr (upto - st.nr) y hy
            simp only at hdh hn
            rcases hakeep with hk | hk
            · rcases hk with hk | hk
              · exact hk hdh
              · omega
            · omega
  · injection h with h'; subst h'; exact hpre

/-- Ageing the store preserves the invariant. Expiry only removes entries, and
removing entries cannot create a collision. Stated because the refinement of the
lookup depends on the store being a map at every point, and `ageStore` runs at
the end of every accepted receive. -/
theorem ageStore_preserves_map (st : State) (hpre : StoreIsMap st.skipped) :
    StoreIsMap (ageStore st).skipped := by
  simpa [ageStore, StoreIsMap] using hpre.filter _

end Proofs.StateInvariants
