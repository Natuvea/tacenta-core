import Translation.TacentaRatchet
open Aeneas Aeneas.Std
namespace Tacenta.PreconditionShapes
-- The allow-listed name kept, the 32-bit hypothesis dropped, and the shape
-- turned into an ordinary precondition. This must not be excused.
theorem old_store_bound_unsatisfiable_at_32 (n : Nat)
    (hs : max n tacenta_ratchet.MAX_SKIPPED_STORE.val + U32.max ≤ Usize.max) : True := trivial
theorem old_skip_bound_forces_empty_at_32 (h32 : Usize.max = U32.max) :
    ∀ n : Nat, n + U32.max ≤ Usize.max → n = 0 := by
  intro n hn; rw [h32] at hn; omega
end Tacenta.PreconditionShapes
