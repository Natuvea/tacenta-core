import Translation.TacentaRatchet
open Aeneas Aeneas.Std
namespace Tacenta.PreconditionShapes
-- Both refutations removed. The rule would then stand with no proof behind it.
theorem clock_headroom_satisfiable : ∃ e : Std.U32, e.val + 1 < U32.max := by
  refine ⟨0#u32, ?_⟩; scalar_tac
end Tacenta.PreconditionShapes
