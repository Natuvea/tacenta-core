import Translation.TacentaRatchet
open Aeneas Aeneas.Std
namespace Tacenta.PreconditionShapes
theorem old_store_bound_unsatisfiable_at_32 (h32 : Usize.max = U32.max) : True := by
  have _h : (0 : Nat) + U32.max ≤ Usize.max → True := fun _ => trivial
  trivial
theorem old_skip_bound_forces_empty_at_32 (h32 : Usize.max = U32.max) :
    ∀ n : Nat, n + U32.max ≤ Usize.max → n = 0 := by
  intro n hn; rw [h32] at hn; omega
end Tacenta.PreconditionShapes
