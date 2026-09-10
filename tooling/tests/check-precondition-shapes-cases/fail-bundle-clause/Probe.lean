import Translation.TacentaRatchet
open Aeneas Aeneas.Std
def Bundle : Prop :=
  ∀ s : Nat, s + U32.max ≤ Usize.max → True
