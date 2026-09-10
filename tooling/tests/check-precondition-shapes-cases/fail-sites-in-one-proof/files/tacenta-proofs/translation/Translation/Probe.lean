import Translation.TacentaRatchet
open Aeneas Aeneas.Std
theorem t (a b c d : Nat) : True := by
  have h1 : a + U32.max ≤ Usize.max → True := fun _ => trivial
  have h2 : b + U32.max ≤ Usize.max → True := fun _ => trivial
  have h3 : c + U32.max ≤ Usize.max → True := fun _ => trivial
  have h4 : d + U32.max ≤ Usize.max → True := fun _ => trivial
  trivial
