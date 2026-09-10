import Translation.TacentaRatchet
open Aeneas Aeneas.Std
theorem t (s : Nat)
    (hplat : 2000 + U32.max ≤ Usize.max) :
    max s 2000 + U32.max ≤ Usize.max := by
  omega
