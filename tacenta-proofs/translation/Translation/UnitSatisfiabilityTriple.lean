import Translation.UnitTripleT3

/-!
# Satisfiability of the Triple Ratchet's `zeroize`-wrapper hypotheses, on the unit

`Translation/UnitTripleT3.lean` restates the Triple Ratchet's refinement about the
three-leaf translation unit. It takes two hypotheses about the `zeroize` wrapper:
`Tacenta.UnitT1.ZeroizingTotal`, that the constructor and projection both
return, and its own `ZeroizingRoundTrips`, that the round trip holds and the
projection returns on every wrapper. Both are stated at the sixty-four-byte
width `split_secret` wraps at.

This file does for those two what `Translation/Satisfiability.lean` does for the
leaves' hypotheses. Each is stated as a shape over an arbitrary wrapper and an
arbitrary pair of functions at the two axioms' types. The hypothesis is shown to
be exactly that shape at the axioms, by `Iff.rfl`, so the two cannot drift. And
the transparent wrapper -- `W Z := Z`, both functions the identity -- satisfies
it. Consistency is all this establishes: the theorems downstream are not proofs
of `False`.

It lives on the unit's side for the same reason the refinement does. The unit's
translation cannot share a Lean environment with the leaves', so the witnesses
in `Satisfiability.lean` cannot be imported here, and these constants are the
unit's, not any leaf's.

`ZeroizingRoundTrips` needs its own witness rather than borrowing the sparse
copy's. It is strictly stronger than `Tacenta.UnitSpqrT3.ZeroizingRoundTrips64`,
which lacks the second conjunct, so the two are different propositions and a
witness for the weaker one would not cover it.

No over-strong shape is refuted, for the reason `Satisfiability.lean` gives: a
round trip has no natural stronger form the identity wrapper would not still
satisfy.
-/

namespace Tacenta.UnitSatisfiabilityTriple

open Aeneas Aeneas.Std Result

/-- The type of `tacenta_triple_unit.zeroize.Zeroizing.new`, at a wrapper `W`. -/
abbrev TripleZeroizingNewFn (W : Type → Type) :=
  {Z : Type} → tacenta_triple_unit.zeroize.Zeroize Z → Z → Result (W Z)

/-- The type of `tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref`,
at a wrapper `W`. -/
abbrev TripleZeroizingDerefFn (W : Type → Type) :=
  {Z : Type} → tacenta_triple_unit.zeroize.Zeroize Z → W Z → Result Z

/-- The shape of `TripleT1.ZeroizingTotal`: constructor and projection both
return, at the sixty-four-byte width. -/
def ZeroizingTotal {W : Type → Type}
    (new : TripleZeroizingNewFn W) (deref : TripleZeroizingDerefFn W) : Prop :=
  ∀ inst : tacenta_triple_unit.zeroize.Zeroize (Array Std.U8 64#usize),
    (∀ z, ∃ r, new inst z = ok r) ∧
    (∀ z, ∃ r, deref inst z = ok r)

/-- The shape of `TripleT3.ZeroizingRoundTrips`: the round trip, and the
projection total on every wrapper (the conjunct that lets it subsume
`ZeroizingTotal`, `ZeroizingRoundTrips.total`). -/
def ZeroizingRoundTrips {W : Type → Type}
    (new : TripleZeroizingNewFn W) (deref : TripleZeroizingDerefFn W) : Prop :=
  ∀ inst : tacenta_triple_unit.zeroize.Zeroize (Array Std.U8 64#usize),
    (∀ z, ∃ w, new inst z = ok w ∧ deref inst w = ok z) ∧
    (∀ w, ∃ z, deref inst w = ok z)

theorem ZeroizingTotal_is :
    Tacenta.UnitT1.ZeroizingTotal ↔
      ZeroizingTotal (W := tacenta_triple_unit.zeroize.Zeroizing)
        @tacenta_triple_unit.zeroize.Zeroizing.new
        @tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref :=
  Iff.rfl

theorem ZeroizingRoundTrips_is :
    Tacenta.UnitTripleT3.ZeroizingRoundTrips ↔
      ZeroizingRoundTrips (W := tacenta_triple_unit.zeroize.Zeroizing)
        @tacenta_triple_unit.zeroize.Zeroizing.new
        @tacenta_triple_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref :=
  Iff.rfl

/-- The transparent wrapper, at the Triple Ratchet's copy of the `Zeroize`
trait. -/
def tripleZeroizingNewWitness : TripleZeroizingNewFn (fun Z => Z) :=
  fun {_Z} _inst z => ok z

def tripleZeroizingDerefWitness : TripleZeroizingDerefFn (fun Z => Z) :=
  fun {_Z} _inst w => ok w

theorem zeroizing_round_trips_satisfiable :
    ∃ (W : Type → Type) (new : TripleZeroizingNewFn W) (deref : TripleZeroizingDerefFn W),
      ZeroizingRoundTrips new deref :=
  ⟨fun Z => Z, @tripleZeroizingNewWitness, @tripleZeroizingDerefWitness,
    fun _ => ⟨fun z => ⟨z, rfl, rfl⟩, fun w => ⟨w, rfl⟩⟩⟩

theorem zeroizing_total_satisfiable :
    ∃ (W : Type → Type) (new : TripleZeroizingNewFn W) (deref : TripleZeroizingDerefFn W),
      ZeroizingTotal new deref :=
  ⟨fun Z => Z, @tripleZeroizingNewWitness, @tripleZeroizingDerefWitness,
    fun _ => ⟨fun z => ⟨z, rfl⟩, fun w => ⟨w, rfl⟩⟩⟩

end Tacenta.UnitSatisfiabilityTriple
