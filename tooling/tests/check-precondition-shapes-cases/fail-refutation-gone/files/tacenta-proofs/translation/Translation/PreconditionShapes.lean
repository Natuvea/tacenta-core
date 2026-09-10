import Translation.TacentaRatchet
open Aeneas Aeneas.Std
namespace Tacenta.PreconditionShapes
theorem old_skip_bound_forces_empty_at_32 (h32 : Usize.max = U32.max) :
    ∀ n : Nat, n + U32.max ≤ Usize.max → n = 0 := by
  intro n hn; rw [h32] at hn; omega
end Tacenta.PreconditionShapes
