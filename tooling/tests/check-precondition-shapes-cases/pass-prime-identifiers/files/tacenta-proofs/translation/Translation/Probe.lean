import Translation.TacentaRatchet
open Aeneas Aeneas.Std
theorem t (s' : Nat) (h' : s' + tacenta_ratchet.MAX_SKIP.val ≤ Usize.max) : True := trivial
