import Translation.TacentaRatchet
open Aeneas Aeneas.Std
structure R where
  «end» : Nat
  «have» : Nat
theorem t (r : R) (a b : Nat) (hr : r.«end» = r.«have»)
    (h1 : Usize.max ≥ a + U32.max)
    (h2 : Usize.max ≥ b + U32.max) : True := trivial
