import Translation.TacentaRatchet

/-!
# Why one precondition shape is refused, and what a witness does not show

Until 2026-09-10, `receive`'s store precondition asked that the skipped store's
length plus the whole `u32` range fit a `usize`. Aeneas models `usize` at the
platform width, so on a 32-bit target the two ranges coincide and the
hypothesis demanded a store with no keys in it. Every theorem carrying it was
vacuous there, on a platform this workspace compiles for, while the
documentation called it a genuine constraint.

The general form is a bound `x + A.max ≤ B.max` (or `<`) where `A` is at least
as wide as `B` on some target. On that target the hypothesis forces `x` to zero,
so it describes no state that has ever done anything. The class is refused
mechanically, across every first-party Lean file, by
`tooling/check-precondition-shapes.py`. That script, not this
file, is what stops the shape coming back.

This file is the justification for the script's rule, kept as proof rather than
prose. The two theorems below are the only places the shape may appear, and the
script allow-lists them by name and only while each still takes the 32-bit
width as a hypothesis, so neither can be quietly turned into a precondition.

## What this file does not do

An earlier version claimed to witness every numeric precondition in the tree
by exhibiting a satisfying value for "six shapes". A cold read counted 144
bound hypotheses on 96 theorems in 54 shapes, and found that the witnesses were
connected to none of them: nothing compared a witness's statement with any
theorem's hypothesis, so a theorem could carry the old shape beside the file
and still build. Those witnesses are gone. Satisfiability of the tree's numeric
preconditions *in general* is not established here or anywhere else.

What is established, and where:

* The dangerous class above is refused by rule in every file, by the script.
* The store bounds the classical ratchet's `receive` carries are satisfied by
  **every** state the crate's decoder accepts, which is far stronger than a
  witness: `Ratchet.inv_gives_store_bound` and `Ratchet.store_plus_skip_fits`
  in `Translation/ImportInv.lean`. The sparse ratchet's room bounds have the
  same treatment there (`Spqr.inv_gives_chain_room`,
  `Spqr.inv_gives_skip_room`).
* The rest of the 54 shapes are unexamined, and `LIMITATIONS.md` says so.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.PreconditionShapes

/-! ## The refuted shape, in both of the forms it took -/

/-- The form `receive_no_panic` and `T3.receive_refines` carried, taken at the
larger of the store's length and its cap. On a 32-bit target no store meets it,
the empty one included, because the left side is at least `2000 + U32.max`.

`h32` takes the narrower branch of `Std.Usize.bounds_eq` as a hypothesis rather
than deriving it from the platform, which is the strongest form this can be
stated in: `System.Platform.numBits` is opaque, and the implication is exactly
"on a 32-bit target". -/
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

/-- The form four other theorems carried: `T1.skip_message_keys_no_panic`,
`T1.skip_message_keys_bound`, `T3.skip_message_keys_refines` and
`T3.receive_tail_refines`. This one is not unsatisfiable at 32 bits, and saying
it was would be the kind of overstatement the file exists to correct: the empty
store meets it. What it does is force the store to be empty, so it says nothing
about any store that has ever held a key. -/
theorem old_skip_bound_forces_empty_at_32 (h32 : Usize.max = U32.max) :
    ∀ n : Nat, n + U32.max ≤ Usize.max → n = 0 := by
  intro n hn
  rw [h32] at hn
  omega

/-! ## Satisfiable is not the same as satisfied by every state -/

/-- The refinement of `receive` asks for a step of room on the skipped-key
store's clock. Some state has it. -/
theorem clock_headroom_satisfiable :
    ∃ e : Std.U32, e.val + 1 < U32.max := by
  refine ⟨0#u32, ?_⟩
  scalar_tac

/-- And the parked clock does not. `age_store` clamps the counter to
`MAX_EVENTS`, one below the ceiling; the crate's `invariant()` needs only
`events < u32::MAX`, so the parked clock passes it and decodes. A session
reaches it after `2^32 - 2` accepted receives.

Neither theorem implies the other and both are true. A witness says a
hypothesis is not vacuous; it does not say every reachable state meets it, and
for this one that stronger claim is false. The epoch step on the sparse
ratchet's refinement, `epoch + 1 < u64::MAX`, is another instance of the same
thing: `LIMITATIONS.md` records `epoch = u64::MAX - 1` as an ordinary state. -/
theorem clock_headroom_excludes_parked_clock :
    ¬ (tacenta_ratchet.MAX_EVENTS.val + 1 < U32.max) := by
  simp only [tacenta_ratchet.MAX_EVENTS]
  scalar_tac

end Tacenta.PreconditionShapes
