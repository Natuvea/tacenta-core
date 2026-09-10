import Translation.T3
import Translation.SpqrT3
import Translation.BraidT3

/-!
# The numeric preconditions are satisfiable, and one of them once was not

`Translation/Satisfiability.lean` witnesses the *boundary* hypotheses: the
`Vec` operations, the `zeroize` wrapper, the derived-keys model. It exhibits an
implementation for each, and for several also proves that the over-broad
version of the same hypothesis admits none. That is a real guard, and it has
never covered the other family of hypothesis in this tree: the **numeric
preconditions** a `no_panic` or `refines` theorem carries about a state's
sizes and counters.

That gap is not hypothetical. `receive`'s store precondition asked, until
2026-09-10, that the store's length plus the whole `u32` range fit a `usize`.
Aeneas models `usize` at the platform width, so on a 32-bit target the two
ranges coincide and the hypothesis said "the store holds at most zero keys".
It was satisfied by no state at all, which made every theorem carrying it
vacuous on a platform this workspace compiles for. It sat in `LIMITATIONS.md`
for months described as a genuine constraint. Nothing checked it, because
nothing was pointed at this family.

This file points something at it. For each *shape* of numeric precondition the
tree uses -- there are six, spread over about thirty theorems -- it exhibits a
value satisfying the shape at either platform width. A shape that stops being
satisfiable fails here.

## What a witness here does and does not say

It says the hypothesis is not vacuous: some state meets it, so a theorem
carrying it is not true for empty reasons.

It does **not** say every state a session can reach meets it. That is a
different and stronger claim, it is false for one of the six, and conflating
the two is how the defect above survived. `clock_headroom_satisfiable` below is
witnessed, and `clock_headroom_excludes_parked_clock` shows the state the
ratchet reaches after `2^32` accepted receives fails it. Both are true; only
the first is what a witness establishes. Where the stronger claim does hold,
`Translation/ImportInv.lean` is where it is proved, from the crate's own
`invariant()`, and `CLAIMS.md` says which preconditions have that treatment.

`Std.Usize.bounds_eq` gives `Usize.max = U32.max ∨ Usize.max = U64.max`, so
every proof here splits on the two widths rather than assuming the wider one.
That split is the whole point: the defect was invisible on the machine the
proofs were written on.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.PreconditionWitness

/-! ## The two store bounds -/

/-- Shape 1, the skipped-key store's room: carried by
`T1.skip_message_keys_no_panic`, `SpqrT1.receive_no_panic`,
`T3.receive_refines` and others. Satisfiable at either width by an empty
store. -/
theorem skip_room_satisfiable :
    ∃ n : Nat, n + tacenta_ratchet.MAX_SKIP.val ≤ Usize.max := by
  refine ⟨0, ?_⟩
  have h := Std.Usize.bounds_eq
  simp only [tacenta_ratchet.MAX_SKIP]
  rcases h with h | h <;> simp [h] <;> scalar_tac

/-- Shape 2, the same bound taken at the larger of the store's length and its
cap: carried by `T1.receive_no_panic` and `T3.receive_refines`. Satisfiable at
either width, and by *every* store, since the left side is a constant. -/
theorem store_bound_satisfiable :
    ∃ n : Nat, max n tacenta_ratchet.MAX_SKIPPED_STORE.val
      + tacenta_ratchet.MAX_SKIP.val ≤ Usize.max := by
  refine ⟨0, ?_⟩
  have h := Std.Usize.bounds_eq
  simp only [tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_SKIP]
  rcases h with h | h <;> simp [h] <;> scalar_tac

/-- The shape `store_bound_satisfiable` replaced, refuted rather than
described. On the branch where `usize` is the narrower of the two widths -- a
32-bit target -- the hypothesis demands the whole address space as slack, so no
store meets it, the empty one included.

This is the defect corrected on 2026-09-10, kept as a theorem so that
reintroducing the shape fails here instead of passing as a strong-looking
precondition. -/
theorem old_store_bound_unsatisfiable_at_32 (h32 : Usize.max = U32.max) :
    ¬ ∃ n : Nat, max n tacenta_ratchet.MAX_SKIPPED_STORE.val
        + U32.max ≤ Usize.max := by
  rintro ⟨n, hn⟩
  have hms : tacenta_ratchet.MAX_SKIPPED_STORE.val = 2000 := by
    simp [tacenta_ratchet.MAX_SKIPPED_STORE]
  rw [hms, h32] at hn
  have hge : (2000 : Nat) ≤ max n 2000 := Nat.le_max_right n 2000
  have : (2000 : Nat) + U32.max ≤ U32.max :=
    le_trans (Nat.add_le_add_right hge _) hn
  omega

/-! ## The chain table, the counters, and the Braid's label -/

/-- Shape 3, the sparse ratchet's chain table having room for the epochs a
step may add: carried at `+ 0`, `+ 1` and `+ 2` across `SpqrT1` and `SpqrT3`.
The widest of the three is witnessed, so the other two follow. -/
theorem chain_room_satisfiable :
    ∃ n : Nat, n + 2 < Usize.max := by
  refine ⟨0, ?_⟩
  have h := Std.Usize.bounds_eq
  rcases h with h | h <;> simp [h] <;> scalar_tac

/-- Shape 4, the sparse ratchet's skipped store: the same bound as shape 1 but
against that crate's own `MAX_SKIP`, which is a `u64` where the classical
ratchet's is a `u32`. Stated separately because they are different constants
of different types, and a reader checking one should not have to assume the
other. -/
theorem spqr_skip_room_satisfiable :
    ∃ n : Nat, n + tacenta_spqr.MAX_SKIP.val ≤ Usize.max := by
  refine ⟨0, ?_⟩
  have h := Std.Usize.bounds_eq
  simp only [tacenta_spqr.MAX_SKIP]
  rcases h with h | h <;> simp [h] <;> scalar_tac

/-- Shape 5, the epoch counter having a step left. Satisfiable, and unlike the
shapes above it is **not** satisfied by every state a session reaches. -/
theorem epoch_room_satisfiable : ∃ e : Nat, e < U64.max := by
  refine ⟨0, ?_⟩
  scalar_tac

/-- Shape 6, the Braid's label plus the derivation's fixed suffix. -/
theorem label_room_satisfiable : ∃ n : Nat, n + 64 ≤ Usize.max := by
  refine ⟨0, ?_⟩
  have h := Std.Usize.bounds_eq
  rcases h with h | h <;> simp [h] <;> scalar_tac

/-! ## Satisfiable is not the same as always satisfied

The clock headroom is the precondition where the difference bites, and the
pair below is the point of this file. -/

/-- The refinement of `receive` asks for a step of room on the skipped-key
store's clock. Some state has it. -/
theorem clock_headroom_satisfiable :
    ∃ e : Std.U32, e.val + 1 < U32.max := by
  refine ⟨0#u32, ?_⟩
  scalar_tac

/-- And the parked clock does not. `age_store` clamps the counter to
`MAX_EVENTS`, one below the ceiling, and a session reaches that after `2^32`
accepted receives; the state is ordinary, satisfies the crate's `invariant()`
and decodes. So no invariant can supply this premise and none is asked to: it
stays with the caller, which `CLAIMS.md` says where the theorem is listed.

A witness says the hypothesis is not vacuous. It does not say the hypothesis
holds of every state, and for this one it does not. Keeping both facts here,
next to each other, is what stops the weaker reading being mistaken for the
stronger. -/
theorem clock_headroom_excludes_parked_clock :
    ¬ (tacenta_ratchet.MAX_EVENTS.val + 1 < U32.max) := by
  simp only [tacenta_ratchet.MAX_EVENTS]
  scalar_tac

end Tacenta.PreconditionWitness
