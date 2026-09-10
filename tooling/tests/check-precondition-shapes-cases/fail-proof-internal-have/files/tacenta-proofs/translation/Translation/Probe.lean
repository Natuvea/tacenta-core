import Translation.TacentaRatchet
open Aeneas Aeneas.Std
theorem t (s : Nat) : True := by
  have _h : s + U32.max ≤ Usize.max → True := fun _ => trivial
  trivial
