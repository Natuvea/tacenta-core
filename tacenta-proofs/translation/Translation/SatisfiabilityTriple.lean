import Translation.TripleT3

/-!
# Satisfiability of the Triple Ratchet's `zeroize`-wrapper hypotheses

The Triple Ratchet half of `Translation/Satisfiability.lean`. `TripleT1.lean`'s
`ZeroizingTotal` and `TripleT3.lean`'s `ZeroizingRoundTrips` are that crate's
own copies of the wrapper hypotheses (`SpqrT1.lean`'s counting rule: the
axioms are `tacenta_triple`'s constants, not the ratchet's), at the one
sixty-four-byte width `split_secret` wraps at. They cannot be witnessed in
`Satisfiability.lean` because `TacentaTriple` and `TacentaRatchet` both define
`instDiscriminantRatchetErrorIsize`, the same limit `lakefile.toml` records, so
the Triple modules cannot share an environment with `T3`; this file is in the
`Translation.*` glob and is imported by `Translation/AxiomAuditTriple.lean`,
which is how it is built and audited.

As there: each hypothesis is stated as a shape over an arbitrary wrapper and an
arbitrary pair of functions at the two axioms' types, the hypothesis is shown
to be exactly that shape at the axioms (`Iff.rfl`, so the two cannot drift),
and the transparent wrapper -- `W Z := Z`, both functions the identity --
satisfies it. Consistency is all this establishes: the theorems downstream are
not proofs of `False`. No over-strong shape is refuted, for the reason
`Satisfiability.lean` gives: a round trip has no natural stronger form the
identity wrapper would not still satisfy.
-/

namespace Tacenta.SatisfiabilityTriple

open Aeneas Aeneas.Std Result

/-- The type of `tacenta_triple.zeroize.Zeroizing.new`, at a wrapper `W`. -/
abbrev TripleZeroizingNewFn (W : Type → Type) :=
  {Z : Type} → tacenta_triple.zeroize.Zeroize Z → Z → Result (W Z)

/-- The type of `tacenta_triple.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref`,
at a wrapper `W`. -/
abbrev TripleZeroizingDerefFn (W : Type → Type) :=
  {Z : Type} → tacenta_triple.zeroize.Zeroize Z → W Z → Result Z

/-- The shape of `TripleT1.ZeroizingTotal`: constructor and projection both
return, at the sixty-four-byte width. -/
def ZeroizingTotal {W : Type → Type}
    (new : TripleZeroizingNewFn W) (deref : TripleZeroizingDerefFn W) : Prop :=
  ∀ inst : tacenta_triple.zeroize.Zeroize (Array Std.U8 64#usize),
    (∀ z, ∃ r, new inst z = ok r) ∧
    (∀ z, ∃ r, deref inst z = ok r)

/-- The shape of `TripleT3.ZeroizingRoundTrips`: the round trip, and the
projection total on every wrapper (the conjunct that lets it subsume
`ZeroizingTotal`, `ZeroizingRoundTrips.total`). -/
def ZeroizingRoundTrips {W : Type → Type}
    (new : TripleZeroizingNewFn W) (deref : TripleZeroizingDerefFn W) : Prop :=
  ∀ inst : tacenta_triple.zeroize.Zeroize (Array Std.U8 64#usize),
    (∀ z, ∃ w, new inst z = ok w ∧ deref inst w = ok z) ∧
    (∀ w, ∃ z, deref inst w = ok z)

theorem ZeroizingTotal_is :
    Tacenta.TripleT1.ZeroizingTotal ↔
      ZeroizingTotal (W := tacenta_triple.zeroize.Zeroizing)
        @tacenta_triple.zeroize.Zeroizing.new
        @tacenta_triple.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref :=
  Iff.rfl

theorem ZeroizingRoundTrips_is :
    Tacenta.TripleT3.ZeroizingRoundTrips ↔
      ZeroizingRoundTrips (W := tacenta_triple.zeroize.Zeroizing)
        @tacenta_triple.zeroize.Zeroizing.new
        @tacenta_triple.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref :=
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

end Tacenta.SatisfiabilityTriple
