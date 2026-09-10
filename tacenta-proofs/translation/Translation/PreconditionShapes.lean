import Translation.TacentaRatchet

/-!
# Why one precondition shape is refused, and what a witness does not show

Until 2026-09-10, `receive`'s store precondition asked that the skipped store's
length plus the whole `u32` range fit a `usize`. Aeneas models `usize` at the
platform width, so on a 32-bit target the two ranges coincide and the
hypothesis demanded a store with no keys in it. Every theorem carrying it was
vacuous there, on a platform this workspace compiles for, while the
documentation called it a genuine constraint.

The general form compares an additive term that is one integer type's maximum
`A` with a bound that is another's maximum `B`, where `A` is at least `B` on
some target. On that target the bound forces what it constrains to zero, so it
describes no state that has ever done anything.

`tooling/check-precondition-shapes.py` is a tripwire for a handful of textual
forms of that class. It is not a guarantee. Its docstring lists the forms it
catches, the forms review found it misses, and the legitimate code it refuses,
and those lists are the claim.

This file is not scanned by that script. It holds the two refutations below,
which state the refused shape on purpose, and the script checks only that both
are still present by name. It does not check what they say. An earlier version
tried to excuse them by name and binder instead, and review found five ways to
smuggle an ordinary precondition past that, so the exclusion is explicit and
claims only what it does.

## What this file does not do

An earlier version claimed to witness every numeric precondition in the tree
through "six shapes". A cold read counted some 140 bound hypotheses on some 95
theorems, in about 54 shapes, and found that the six covered under half of
them. It also found the witnesses connected to none of them: nothing compared a
witness with any theorem's hypothesis, so a theorem could carry the old shape
beside the file and still build. Those witnesses are gone. Satisfiability of
the tree's numeric preconditions *in general* is not established here or
anywhere else.

What is established, and where:

* The forms the script's docstring lists trip it in every file it scans.
* The store bounds the classical ratchet's `receive` carries are satisfied by
  **every** state the crate's decoder accepts, which is far stronger than a
  witness: `Ratchet.inv_gives_store_bound` and `Ratchet.store_plus_skip_fits`
  in `Translation/ImportInv.lean`. The sparse ratchet's room bounds have the
  same treatment there (`Spqr.inv_gives_chain_room`,
  `Spqr.inv_gives_skip_room`).
* The rest of the tree's numeric preconditions are unexamined, and
  `LIMITATIONS.md` says so.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.PreconditionShapes

/-! ## The refuted shape, in both of the forms it took -/

/-- The form carried, taken at the larger of the store's length and its cap, by
`T1.receive_no_panic` and its copy on the three-leaf unit, by
`T3.receive_refines`, `TripleT3.receive_refines` and
`UnitTripleT1.State.receive_no_panic`, and by two assumption bundles,
`RatchetAgreesFor` and `RatchetReceiveTotal`. On a 32-bit target no store meets
it, the empty one included, because the left side is at least `2000 + U32.max`.
`ImportInv.lean` carried it twice more: in full, as the conclusion of
`Ratchet.inv_gives_store_bound`, and in a closed spelling, the constant part
passed in as `hplat`, which is false at 32 bits and is the `n = 0` case of this.

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

/-- The form six other theorems carried: `T1.skip_message_keys_no_panic`,
`T1.skip_message_keys_bound`, their two copies on the three-leaf unit,
`T3.skip_message_keys_refines` and `T3.receive_tail_refines`. This one is not
unsatisfiable at 32 bits, and saying it was would be the kind of overstatement
the file exists to correct: the empty store meets it. What it does is force the
store to be empty, so it says nothing about any store that has ever held a key.
-/
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
