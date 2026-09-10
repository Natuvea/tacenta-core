import Translation.SpqrT3
import Translation.T3
import Translation.BraidT3
import Translation.SessionT3
import Translation.ErasureT1

/-!
# Satisfiability of the leaves' opaque-boundary hypotheses

Every `Vec` operation Aeneas does not model reaches the translation as an
axiom, as do the `zeroize` wrapper's constructor and projection, and the
T1/T3 files assume what they need about them as a named `Prop`
(`VecAppendTotal`, `VecRemoveAgrees`, `ZeroizingRoundTrips96`,
`ZeroizingArrayRoundTrip`, `T3.ZeroizingRoundTrips80`, ...), or as a class
(`T1.DerivedKeysModel`), and so are the key-derivation agreements (`T3.HmacAgrees`,
`T3.HkdfAgrees`, `SpqrT3.SpqrHkdfAgrees`, `SessionT3.HkdfAgrees` and the Braid's
two), `OptionCloneTotal`, and the few more the last section lists, some of them
only by derivation from a witnessed agreement. The three-leaf unit's copies of these, and the Triple
Ratchet's own, have their witnesses in `Translation/UnitSatisfiabilityTriple.lean`,
since `TacentaTripleUnit` cannot be imported alongside `TacentaRatchet`. A
hypothesis of that kind carries
a risk the rest of the proof cannot see: if it is **refutable** -- if no
function at all could satisfy it -- then every theorem taking it is provable
from `False`, and the kernel will happily check it.

This file is the check against that. For each hypothesis it states the
*shape* as a predicate on an arbitrary function of the axiom's type, shows
the current hypothesis is exactly that shape applied to the axiom
(`Iff.rfl`, so the two cannot drift), and exhibits a concrete function
satisfying it, so the hypothesis is consistent: at least one model of that
hypothesis makes it true. Alongside each `Vec` hypothesis it also states the natural over-strong
shape -- an `append` with no length guard, a `remove` with no index guard --
and proves that **no** function satisfies it, so the guards on the
hypotheses are shown to be necessary rather than merely cautious. An edit
that makes a hypothesis unsatisfiable breaks the witness here.

Consistency is all this establishes. Nothing here says the axiom Aeneas
generated *is* the witness; it says the theorems downstream are not proofs
of `False`. For `Vec::remove` the witness happens to be the real operation's
own behaviour -- the element in range, a panic otherwise -- because the
hypotheses are stated under the index guard and so ask for nothing the real
operation does not do; for `append` and `retain` it is one model among
several.
-/

namespace Tacenta.Satisfiability

open Aeneas Aeneas.Std Result

/-! ## `Vec::append` -/

/-- The type of `tacenta_spqr.alloc.vec.Vec.append`. -/
abbrev AppendFn :=
  {T : Type} → (A : Type) → alloc.vec.Vec T → alloc.vec.Vec T →
    Result (alloc.vec.Vec T × alloc.vec.Vec T)

/-- The shape of `SpqrT1.VecAppendTotal`. -/
def AppendTotal (f : AppendFn) : Prop :=
  ∀ {T : Type} (A : Type) (v w : alloc.vec.Vec T),
    v.length + w.length ≤ Usize.max →
    ∃ r, f A v w = ok r ∧ r.1.length = v.length + w.length

/-- The shape of `SpqrT3.VecAppendAgrees`. -/
def AppendAgrees (f : AppendFn) : Prop :=
  ∀ {T : Type} (A : Type) (v w : alloc.vec.Vec T),
    v.length + w.length ≤ Usize.max →
    ∃ r, f A v w = ok r ∧ r.1.val = v.val ++ w.val

/-- The over-strong shape: `VecAppendTotal` with no length guard. -/
def AppendTotalUnguarded (f : AppendFn) : Prop :=
  ∀ {T : Type} (A : Type) (v w : alloc.vec.Vec T),
    ∃ r, f A v w = ok r ∧ r.1.length = v.length + w.length

theorem VecAppendTotal_is :
    Tacenta.SpqrT1.VecAppendTotal ↔ AppendTotal @tacenta_spqr.alloc.vec.Vec.append :=
  Iff.rfl

theorem VecAppendAgrees_is :
    Tacenta.SpqrT3.VecAppendAgrees ↔ AppendAgrees @tacenta_spqr.alloc.vec.Vec.append :=
  Iff.rfl

/-- Concatenate when the result fits, fail otherwise -- which is what the real
`Vec::append` does at the capacity boundary (it aborts). -/
def appendWitness : AppendFn := fun {_T} _A v w =>
  if h : v.val.length + w.val.length ≤ Usize.max then
    ok (⟨v.val ++ w.val, by simpa using h⟩, w)
  else fail .panic

theorem appendWitness_agrees : AppendAgrees @appendWitness := by
  intro T A v w hlen
  simp only [alloc.vec.Vec.length] at hlen
  exact ⟨(⟨v.val ++ w.val, by simpa using hlen⟩, w), by simp [appendWitness, hlen], rfl⟩

theorem append_agrees_satisfiable : ∃ f : AppendFn, AppendAgrees f :=
  ⟨@appendWitness, appendWitness_agrees⟩

theorem append_total_satisfiable : ∃ f : AppendFn, AppendTotal f := by
  refine ⟨@appendWitness, fun A v w hlen => ?_⟩
  obtain ⟨r, hr, hv⟩ := appendWitness_agrees A v w hlen
  exact ⟨r, hr, by simp [alloc.vec.Vec.length, hv]⟩

theorem usize_max_pos : 0 < Usize.max := by
  simp [Usize.max, Usize.numBits]
  cases System.Platform.numBits_eq <;> simp_all

/-- Why the guard: two vectors already at `Usize.max` have no concatenation
inside Aeneas's `Vec`, so the unguarded shape has no model at all. -/
theorem append_total_unguarded_unsatisfiable : ¬ ∃ f : AppendFn, AppendTotalUnguarded f := by
  rintro ⟨f, hf⟩
  let full : alloc.vec.Vec Unit := ⟨List.replicate Usize.max (), by simp⟩
  obtain ⟨r, -, hlen⟩ := hf Unit full full
  have hr := r.1.property
  simp only [alloc.vec.Vec.length, full, List.length_replicate] at hlen
  have := usize_max_pos
  omega

/-! ## `Vec::remove` -/

/-- The type of both crates' `alloc.vec.Vec.remove`. -/
abbrev RemoveFn :=
  {T : Type} → (A : Type) → alloc.vec.Vec T → Usize → Result (T × alloc.vec.Vec T)

/-- The shape of `T1.VecRemoveTotal` and `SpqrT1.VecRemoveTotal`: under the
index guard, the operation returns with that index erased. -/
def RemoveTotal (f : RemoveFn) : Prop :=
  ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T) (i : Usize), i.val < v.val.length →
    ∃ r, f A v i = ok r ∧ r.2.val = v.val.eraseIdx i.val

/-- The shape of `SpqrT3.VecRemoveAgrees`: the same, naming the element
removed, which the guard makes well-defined without an `Inhabited` bound. -/
def RemoveAgrees (f : RemoveFn) : Prop :=
  ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T) (i : Usize) (h : i.val < v.val.length),
    ∃ r, f A v i = ok r ∧ r.1 = v.val[i.val]'h ∧ r.2.val = v.val.eraseIdx i.val

/-- The over-strong shape: `VecRemoveTotal` at every index, guard or no guard.
This is the shape the hypotheses used to have with an `[Inhabited T]` bound
in place of the guard; the bound is gone because the guard does its work
(below), and the shape is kept, unguarded and unbounded, as the record of
why one of the two is needed. No `!`-indexed variant of `RemoveAgrees` is
refuted any more: under the guard the removed element is `v.val[i.val]`
outright, and there is no out-of-range value to name through `default`. -/
def RemoveTotalUnguarded (f : RemoveFn) : Prop :=
  ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T) (i : Usize),
    ∃ r, f A v i = ok r ∧ r.2.val = v.val.eraseIdx i.val

theorem T1_VecRemoveTotal_is :
    Tacenta.T1.VecRemoveTotal ↔ RemoveTotal @tacenta_ratchet.alloc.vec.Vec.remove :=
  Iff.rfl

theorem SpqrT1_VecRemoveTotal_is :
    Tacenta.SpqrT1.VecRemoveTotal ↔ RemoveTotal @tacenta_spqr.alloc.vec.Vec.remove :=
  Iff.rfl

theorem VecRemoveAgrees_is :
    Tacenta.SpqrT3.VecRemoveAgrees ↔ RemoveAgrees @tacenta_spqr.alloc.vec.Vec.remove :=
  Iff.rfl

theorem length_eraseIdx_le_max {T : Type} (v : alloc.vec.Vec T) (i : Nat) :
    (v.val.eraseIdx i).length ≤ Usize.max :=
  le_trans (List.length_eraseIdx_le _ _) v.property

/-- In range: the element at the index and the shortened vector. Out of
range: a panic. This is what Rust's `Vec::remove` does, so the witness is
not a toy: the guarded shapes ask for exactly the real operation's behaviour
and nothing past it. -/
def removeWitness : RemoveFn := fun {_T} _A v i =>
  if h : i.val < v.val.length then
    ok (v.val[i.val], ⟨v.val.eraseIdx i.val, length_eraseIdx_le_max v i.val⟩)
  else fail .panic

theorem removeWitness_agrees : RemoveAgrees @removeWitness := by
  intro T A v i h
  exact ⟨(v.val[i.val], ⟨v.val.eraseIdx i.val, length_eraseIdx_le_max v i.val⟩),
    by simp [removeWitness, h], rfl, rfl⟩

theorem remove_agrees_satisfiable : ∃ f : RemoveFn, RemoveAgrees f :=
  ⟨@removeWitness, removeWitness_agrees⟩

theorem remove_total_satisfiable : ∃ f : RemoveFn, RemoveTotal f := by
  refine ⟨@removeWitness, fun A v i h => ?_⟩
  obtain ⟨r, hr, -, hv⟩ := removeWitness_agrees A v i h
  exact ⟨r, hr, hv⟩

/-- Why the guard: at an empty element type and an empty vector, an
unguarded existential has nothing to offer, so the unguarded shape has no
model at all. Under the guard the case does not arise, since an empty vector
has no in-range index. -/
theorem remove_total_unguarded_unsatisfiable : ¬ ∃ f : RemoveFn, RemoveTotalUnguarded f := by
  rintro ⟨f, hf⟩
  obtain ⟨r, -, -⟩ := hf Unit (alloc.vec.Vec.new Empty) 0#usize
  exact r.1.elim

/-! ## `Vec::retain` -/

/-- The type of `tacenta_spqr.alloc.vec.Vec.retain` (binder order as Aeneas
generated it: the closure's type parameter comes after `A`). -/
abbrev RetainFn :=
  {T : Type} → (A : Type) → {F : Type} → core.ops.function.FnMut F T Bool →
    alloc.vec.Vec T → F → Result (alloc.vec.Vec T)

/-- The shape of `SpqrT1.VecRetainTotal`. -/
def RetainTotal (f : RetainFn) : Prop :=
  ∀ {T F : Type} (A : Type) (inst : core.ops.function.FnMut F T Bool)
    (v : alloc.vec.Vec T) (g : F),
    ∃ r, f A inst v g = ok r ∧ r.length ≤ v.length ∧ ∀ x ∈ r.val, x ∈ v.val

/-- The shape of `SpqrT3.VecRetainAgrees`. -/
def RetainAgrees (f : RetainFn) : Prop :=
  ∀ {T F : Type} (A : Type) (inst : core.ops.function.FnMut F T Bool)
    (v : alloc.vec.Vec T) (g : F) (p : T → Bool)
    (_hp : ∀ x, inst.call_mut g x = ok (p x, g)),
    ∃ r, f A inst v g = ok r ∧ r.val = v.val.filter p

theorem VecRetainTotal_is :
    Tacenta.SpqrT1.VecRetainTotal ↔ RetainTotal @tacenta_spqr.alloc.vec.Vec.retain :=
  Iff.rfl

theorem VecRetainAgrees_is :
    Tacenta.SpqrT3.VecRetainAgrees ↔ RetainAgrees @tacenta_spqr.alloc.vec.Vec.retain :=
  Iff.rfl

theorem length_filter_le_max {T : Type} (p : T → Bool) (v : alloc.vec.Vec T) :
    (v.val.filter p).length ≤ Usize.max :=
  le_trans (List.length_filter_le _ _) v.property

open Classical in
/-- When the closure is a pure predicate that leaves its state alone -- the
only kind `VecRetainAgrees` speaks about -- filter by it; otherwise keep
everything, which `VecRetainTotal` permits. Classical, because recovering the
predicate from the closure is a choice. -/
noncomputable def retainWitness : RetainFn := fun {T} _A {_F} inst v g =>
  if h : ∃ p : T → Bool, ∀ x, inst.call_mut g x = ok (p x, g) then
    ok ⟨v.val.filter (Classical.choose h), length_filter_le_max _ v⟩
  else ok v

theorem retainWitness_agrees : RetainAgrees @retainWitness := by
  intro T F A inst v g p hp
  have h : ∃ p : T → Bool, ∀ x, inst.call_mut g x = ok (p x, g) := ⟨p, hp⟩
  refine ⟨⟨v.val.filter (Classical.choose h), length_filter_le_max _ v⟩,
    by simp [retainWitness, h], ?_⟩
  apply List.filter_congr
  intro x _
  have := Classical.choose_spec h x
  rw [hp x] at this
  exact (Prod.mk.inj (Result.ok.inj this)).1.symm

theorem retain_agrees_satisfiable : ∃ f : RetainFn, RetainAgrees f :=
  ⟨@retainWitness, retainWitness_agrees⟩

theorem retain_total_satisfiable : ∃ f : RetainFn, RetainTotal f := by
  refine ⟨@retainWitness, ?_⟩
  intro T F A inst v g
  by_cases h : ∃ p : T → Bool, ∀ x, inst.call_mut g x = ok (p x, g)
  · exact ⟨⟨v.val.filter (Classical.choose h), length_filter_le_max _ v⟩,
      by simp [retainWitness, h], List.length_filter_le _ _,
      fun _ hx => List.mem_of_mem_filter hx⟩
  · exact ⟨v, by simp [retainWitness, h], le_refl _, fun _ hx => hx⟩

/-! ## The `zeroize` wrapper

`SpqrT3.lean`'s `ZeroizingRoundTrips96`/`ZeroizingRoundTrips64` speak about
two axioms at once -- the wrapper's constructor and its projection -- and about
an opaque wrapper *type*, so the shape is stated over an arbitrary wrapper `W`
and an arbitrary pair of functions at the two axioms' types, with the width
left free so one witness covers both hypotheses. The witness is the transparent
wrapper: `W Z := Z`, and both functions the identity. That is also why no
over-strong shape is refuted here: a round trip has no natural stronger form
the identity wrapper would not still satisfy. -/

/-- The type of `tacenta_spqr.zeroize.Zeroizing.new`, at a wrapper `W`. -/
abbrev ZeroizingNewFn (W : Type → Type) :=
  {Z : Type} → tacenta_spqr.zeroize.Zeroize Z → Z → Result (W Z)

/-- The type of `tacenta_spqr.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref`,
at a wrapper `W`. -/
abbrev ZeroizingDerefFn (W : Type → Type) :=
  {Z : Type} → tacenta_spqr.zeroize.Zeroize Z → W Z → Result Z

/-- The shape of `SpqrT3.ZeroizingRoundTrips96` and `ZeroizingRoundTrips64`,
at a width `N`. -/
def ZeroizingRoundTrips (N : Usize) {W : Type → Type}
    (new : ZeroizingNewFn W) (deref : ZeroizingDerefFn W) : Prop :=
  ∀ inst : tacenta_spqr.zeroize.Zeroize (Array Std.U8 N),
    ∀ z, ∃ w, new inst z = ok w ∧ deref inst w = ok z

theorem ZeroizingRoundTrips96_is :
    Tacenta.SpqrT3.ZeroizingRoundTrips96 ↔
      ZeroizingRoundTrips 96#usize (W := tacenta_spqr.zeroize.Zeroizing)
        @tacenta_spqr.zeroize.Zeroizing.new
        @tacenta_spqr.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref :=
  Iff.rfl

theorem ZeroizingRoundTrips64_is :
    Tacenta.SpqrT3.ZeroizingRoundTrips64 ↔
      ZeroizingRoundTrips 64#usize (W := tacenta_spqr.zeroize.Zeroizing)
        @tacenta_spqr.zeroize.Zeroizing.new
        @tacenta_spqr.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref :=
  Iff.rfl

/-- The transparent wrapper: wrapping is the identity. -/
def zeroizingNewWitness : ZeroizingNewFn (fun Z => Z) := fun {_Z} _inst z => ok z

/-- The transparent wrapper: reading back is the identity. -/
def zeroizingDerefWitness : ZeroizingDerefFn (fun Z => Z) := fun {_Z} _inst w => ok w

theorem zeroizing_round_trips_satisfiable (N : Usize) :
    ∃ (W : Type → Type) (new : ZeroizingNewFn W) (deref : ZeroizingDerefFn W),
      ZeroizingRoundTrips N new deref :=
  ⟨fun Z => Z, @zeroizingNewWitness, @zeroizingDerefWitness, fun _ z => ⟨z, rfl, rfl⟩⟩

/-! ## The Braid's `zeroize` touches: the wrapper, the wipe, and the full-range index

`BraidT1.lean`'s `ZeroizingArrayRoundTrip`, `ArrayZeroizeTotal` and
`RangeFullIndexTotal` are that crate's own copies of three axioms the
translation could not see into: the `zeroize` wrapper's constructor and
projection (the round trip above, but at every width at once rather than at
two fixed ones), the in-place wipe of a fixed-size array, and the `RangeFull`
slice index the Aeneas library does not model. Each has the transparent
model: the identity wrapper again, a wipe that hands its array back (the
hypothesis says nothing about the value, since the source discards what the
wipe leaves behind), and the index that returns the slice it was given. No
over-strong shape is refuted here for the same reason as above: none of the
three has a natural stronger form the transparent model would not still
satisfy. -/

section BraidZeroize

/-- The type of `tacenta_braid.zeroize.Zeroizing.new`, at a wrapper `W`. -/
abbrev BraidZeroizingNewFn (W : Type → Type) :=
  {Z : Type} → tacenta_braid.zeroize.Zeroize Z → Z → Result (W Z)

/-- The type of `tacenta_braid.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref`,
at a wrapper `W`. -/
abbrev BraidZeroizingDerefFn (W : Type → Type) :=
  {Z : Type} → tacenta_braid.zeroize.Zeroize Z → W Z → Result Z

/-- The shape of `BraidT1.ZeroizingArrayRoundTrip`: the round trip at every
width. -/
def ZeroizingArrayRoundTrip {W : Type → Type}
    (new : BraidZeroizingNewFn W) (deref : BraidZeroizingDerefFn W) : Prop :=
  ∀ (N : Usize) (inst : tacenta_braid.zeroize.Zeroize (Array Std.U8 N)) (a : Array Std.U8 N),
    ∃ z, new inst a = ok z ∧ deref inst z = ok a

theorem ZeroizingArrayRoundTrip_is :
    Tacenta.BraidT1.ZeroizingArrayRoundTrip ↔
      ZeroizingArrayRoundTrip (W := tacenta_braid.zeroize.Zeroizing)
        @tacenta_braid.zeroize.Zeroizing.new
        @tacenta_braid.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref :=
  Iff.rfl

/-- The transparent wrapper, at the Braid's copy of the `Zeroize` trait. -/
def braidZeroizingNewWitness : BraidZeroizingNewFn (fun Z => Z) := fun {_Z} _inst z => ok z

def braidZeroizingDerefWitness : BraidZeroizingDerefFn (fun Z => Z) := fun {_Z} _inst w => ok w

theorem zeroizing_array_round_trip_satisfiable :
    ∃ (W : Type → Type) (new : BraidZeroizingNewFn W) (deref : BraidZeroizingDerefFn W),
      ZeroizingArrayRoundTrip new deref :=
  ⟨fun Z => Z, @braidZeroizingNewWitness, @braidZeroizingDerefWitness,
    fun _ _ a => ⟨a, rfl, rfl⟩⟩

/-- The type of `tacenta_braid.Array.Insts.ZeroizeZeroize.zeroize`. -/
abbrev ArrayZeroizeFn :=
  {Z : Type} → {N : Usize} → tacenta_braid.zeroize.Zeroize Z → Array Z N → Result (Array Z N)

/-- The shape of `BraidT1.ArrayZeroizeTotal`. -/
def ArrayZeroizeTotal (f : ArrayZeroizeFn) : Prop :=
  ∀ (N : Usize) (inst : tacenta_braid.zeroize.Zeroize Std.U8) (a : Array Std.U8 N),
    ∃ r, f (N := N) inst a = ok r

theorem ArrayZeroizeTotal_is :
    Tacenta.BraidT1.ArrayZeroizeTotal ↔
      ArrayZeroizeTotal @tacenta_braid.Array.Insts.ZeroizeZeroize.zeroize :=
  Iff.rfl

/-- A wipe that returns its input: the hypothesis asks only that the wipe
return, and says nothing about what it leaves behind. -/
def arrayZeroizeWitness : ArrayZeroizeFn := fun {_Z} {_N} _inst a => ok a

theorem array_zeroize_total_satisfiable : ∃ f : ArrayZeroizeFn, ArrayZeroizeTotal f :=
  ⟨@arrayZeroizeWitness, fun _ _ a => ⟨a, rfl⟩⟩

/-- The type of the Braid's `RangeFull` slice index. -/
abbrev RangeFullIndexFn :=
  {T : Type} → tacenta_braid.core.ops.range.RangeFull → Slice T → Result (Slice T)

/-- The shape of `BraidT1.RangeFullIndexTotal`. -/
def RangeFullIndexTotal (f : RangeFullIndexFn) : Prop :=
  ∀ (s : Slice Std.U8), f () s = ok s

theorem RangeFullIndexTotal_is :
    Tacenta.BraidT1.RangeFullIndexTotal ↔
      RangeFullIndexTotal
        @tacenta_braid.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index :=
  Iff.rfl

/-- `s[..]` is `s`. -/
def rangeFullIndexWitness : RangeFullIndexFn := fun {_T} _r s => ok s

theorem range_full_index_total_satisfiable : ∃ f : RangeFullIndexFn, RangeFullIndexTotal f :=
  ⟨@rangeFullIndexWitness, fun _ => rfl⟩

end BraidZeroize

/-! ## The classical ratchet's derived-keys wrapper, `T1.DerivedKeysModel`

`T1.lean`'s `DerivedKeysModel` is a class rather than a `Prop`: it carries
the contents function the store loop reads a length back out of, together
with the three equations relating the wrapper's constructor, projection and
mutable projection to it (`CLAIMS.md`'s T1 entry says why totality alone was
not enough). The risk is the same -- an instance nobody could build makes
every theorem taking one vacuous -- so the shape is stated over an arbitrary
wrapper `W`, an arbitrary contents function, and an arbitrary triple of
functions at the three axioms' types. The class holds data, so `Iff.rfl` on
the class itself is not available; `DerivedKeysModel_is` is the corresponding
equivalence, that an instance exists exactly when some contents function
satisfies the shape at the axioms. The transparent wrapper satisfies it:
`W Z := Z`, contents the identity, `new` and `deref` the identity, and
`deref_mut` returning the value together with the identity as the way to put
one back. -/

section DerivedKeys

/-- The one type the classical ratchet wraps its derived keys at. -/
abbrev DerivedKeys := alloc.vec.Vec (Std.U32 × Array Std.U8 32#usize)

/-- The types of `tacenta_ratchet.zeroize.Zeroizing.new`, its `deref`, and its
`deref_mut`, at a wrapper `W`. -/
abbrev RatchetZeroizingNewFn (W : Type → Type) :=
  {Z : Type} → tacenta_ratchet.zeroize.Zeroize Z → Z → Result (W Z)

abbrev RatchetZeroizingDerefFn (W : Type → Type) :=
  {Z : Type} → tacenta_ratchet.zeroize.Zeroize Z → W Z → Result Z

abbrev RatchetZeroizingDerefMutFn (W : Type → Type) :=
  {Z : Type} → tacenta_ratchet.zeroize.Zeroize Z → W Z → Result (Z × (Z → W Z))

/-- The shape of `T1.DerivedKeysModel`'s three equations, at a contents
function. -/
def DerivedKeysShape {W : Type → Type} (contents : W DerivedKeys → DerivedKeys)
    (new : RatchetZeroizingNewFn W) (deref : RatchetZeroizingDerefFn W)
    (deref_mut : RatchetZeroizingDerefMutFn W) : Prop :=
  (∀ (inst : tacenta_ratchet.zeroize.Zeroize DerivedKeys) (v : DerivedKeys),
    new inst v ⦃ fun z => contents z = v ⦄) ∧
  (∀ (inst : tacenta_ratchet.zeroize.Zeroize DerivedKeys) (z : W DerivedKeys),
    deref inst z ⦃ fun v => v = contents z ⦄) ∧
  (∀ (inst : tacenta_ratchet.zeroize.Zeroize DerivedKeys) (z : W DerivedKeys),
    deref_mut inst z ⦃ fun p => p.1 = contents z ∧ ∀ v', contents (p.2 v') = v' ⦄)

theorem DerivedKeysModel_is :
    Nonempty Tacenta.T1.DerivedKeysModel ↔
      ∃ contents, DerivedKeysShape (W := tacenta_ratchet.zeroize.Zeroizing) contents
        @tacenta_ratchet.zeroize.Zeroizing.new
        @tacenta_ratchet.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        @tacenta_ratchet.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut :=
  ⟨fun ⟨m⟩ => ⟨m.contents, m.new, m.deref, m.deref_mut⟩,
   fun ⟨c, hn, hd, hm⟩ => ⟨⟨c, hn, hd, hm⟩⟩⟩

/-- The transparent wrapper, at the ratchet's copy of the `Zeroize` trait. -/
def ratchetZeroizingNewWitness : RatchetZeroizingNewFn (fun Z => Z) :=
  fun {_Z} _inst z => ok z

def ratchetZeroizingDerefWitness : RatchetZeroizingDerefFn (fun Z => Z) :=
  fun {_Z} _inst w => ok w

def ratchetZeroizingDerefMutWitness : RatchetZeroizingDerefMutFn (fun Z => Z) :=
  fun {_Z} _inst w => ok (w, id)

theorem derived_keys_model_satisfiable :
    ∃ (W : Type → Type) (contents : W DerivedKeys → DerivedKeys)
      (new : RatchetZeroizingNewFn W) (deref : RatchetZeroizingDerefFn W)
      (deref_mut : RatchetZeroizingDerefMutFn W),
      DerivedKeysShape contents new deref deref_mut :=
  ⟨fun Z => Z, id, @ratchetZeroizingNewWitness, @ratchetZeroizingDerefWitness,
    @ratchetZeroizingDerefMutWitness,
    fun _ _ => by simp [ratchetZeroizingNewWitness],
    fun _ _ => by simp [ratchetZeroizingDerefWitness],
    fun _ _ => by simp [ratchetZeroizingDerefMutWitness]⟩

end DerivedKeys

/-! ## The classical ratchet's `zeroize` round trips, `T3.ZeroizingRoundTrips` and `ZeroizingRoundTrips80`

`T3.lean`'s two round-trip hypotheses, at the sixty-four-byte root-key width
and the eighty-byte `message_keys` width, carry a second conjunct the sparse
ratchet's do not: the projection is total on *every* wrapper, not only on one
the constructor built, which is what lets each subsume `T1.ZeroizingTotal`
(`ZeroizingRoundTrips.total`). So the shape is the round trip together with
that totality, at the ratchet's own copies of the constructor and projection
(`SpqrT1.lean`'s counting rule again), with the width left free so one witness
covers both. The transparent wrapper satisfies both conjuncts. -/

section RatchetZeroize

/-- The shape of `T3.ZeroizingRoundTrips` and `T3.ZeroizingRoundTrips80`, at
a width `N`. -/
def ZeroizingRoundTripsTotal (N : Usize) {W : Type → Type}
    (new : RatchetZeroizingNewFn W) (deref : RatchetZeroizingDerefFn W) : Prop :=
  ∀ inst : tacenta_ratchet.zeroize.Zeroize (Array Std.U8 N),
    (∀ z, ∃ w, new inst z = ok w ∧ deref inst w = ok z) ∧
    (∀ w, ∃ z, deref inst w = ok z)

theorem T3_ZeroizingRoundTrips_is :
    Tacenta.T3.ZeroizingRoundTrips ↔
      ZeroizingRoundTripsTotal 64#usize (W := tacenta_ratchet.zeroize.Zeroizing)
        @tacenta_ratchet.zeroize.Zeroizing.new
        @tacenta_ratchet.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref :=
  Iff.rfl

theorem T3_ZeroizingRoundTrips80_is :
    Tacenta.T3.ZeroizingRoundTrips80 ↔
      ZeroizingRoundTripsTotal 80#usize (W := tacenta_ratchet.zeroize.Zeroizing)
        @tacenta_ratchet.zeroize.Zeroizing.new
        @tacenta_ratchet.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref :=
  Iff.rfl

theorem zeroizing_round_trips_total_satisfiable (N : Usize) :
    ∃ (W : Type → Type) (new : RatchetZeroizingNewFn W) (deref : RatchetZeroizingDerefFn W),
      ZeroizingRoundTripsTotal N new deref :=
  ⟨fun Z => Z, @ratchetZeroizingNewWitness, @ratchetZeroizingDerefWitness,
    fun _ => ⟨fun z => ⟨z, rfl, rfl⟩, fun w => ⟨w, rfl⟩⟩⟩

end RatchetZeroize

/-! ## The Braid's T3 boundary: over-strong shapes, and why they are not used

`BraidT3.lean`'s erasure and KEM hypotheses each have a natural stronger
statement that no implementation satisfies. This section keeps those shapes
as local copies and refutes them, so that the reasons for the weaker
statements stay checked:

- **The header split.** A `KemAgreesFor K` or `ValidateEkAgrees K` that
  quantified over every split of a header into `ekSeed ++ hek` would be
  refuted by any `K` whose `encaps1` or `hashEk` reads the split -- the
  model's own `toyKem` included -- since the real operation returns one
  value. The hypotheses fix the seed at 32 bytes, which is where the model
  itself splits.
- **Unbounded fuel.** An `EncoderRefines` demanding `EncoderSim n` for every
  `n` is false of every encoder, since a chunk index is a `u16`. The
  hypothesis demands it only while the model's position leaves room, and
  stepping requires the encoder live (`EncodersLive`, a precondition of
  `step_send_refines`).
- **One real answer, many model sources.** A `DecoderSim` quantifying over
  every model chunk sharing a real chunk's index asks one total real
  `message` (`DecoderMessageTotal`) for two different answers. `DecoderSim m`
  is parameterised by the message the decoder is collecting, and relates
  only codewords of `m`.

`DecoderMessageLenAgrees` needs no witness: the model's `Decoder.message`
checks the length, and the statement is the theorem
`Model.Braid.Decoder.message_length`.

The model of the erasure hypotheses lives in its own module,
`Translation/ErasureWitness.lean` (a Reed-Solomon code over `GF(2^256)`,
built from Mathlib, with `erasureAgrees_iff` tying the concrete hypothesis to
the shape it satisfies); it is a separate file because it is the one place
the translation package reaches for Mathlib's field theory. -/

section BraidRefutations

open Tacenta.BraidT3 tacenta_braid

/-- An RNG that answers `fill_bytes` by handing the buffer back untouched,
enough to instantiate the `∀ {R}` clauses and to satisfy the `RngTotal`
premise they carry. -/
def dummyRng : rand_core_1.RngCore Unit where
  next_u32 _ := fail .panic
  next_u64 _ := fail .panic
  fill_bytes r buf := ok (r, buf)
  try_fill_bytes _ _ := fail .panic

def dummyCryptoRng : rand_core_1.CryptoRng Unit := {}

theorem dummyRng_total : Tacenta.BraidT1.RngTotal dummyRng :=
  fun r buf => ⟨(r, buf), rfl⟩

/-- The over-strong `encaps1` clause of `KemAgreesFor`: every split of the header. -/
def KemEncaps1AgreesUnsplit (K : Model.Braid.Kem) : Prop :=
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
      (header : Slice Std.U8) (rng : R), Tacenta.BraidT1.RngTotal rc →
    ∃ es ct1raw ssraw rng' rand',
      tacenta_kem.encapsulate1 rc crc header rng =
        ok (core.result.Result.Ok (es, ct1raw, ssraw), rng') ∧
      (∀ ekSeed hek : Bytes, sliceOf header = ekSeed ++ hek →
        (K.encaps1 rand' ekSeed hek).2.1 = vecOf ct1raw ∧
        (K.encaps1 rand' ekSeed hek).2.2 = keyOf ssraw)

/-- At the model's toy KEM: the empty header has one split, `[] ++ []`,
under which the shared secret is `[]`, against a 32-byte `Array`. -/
theorem kemEncaps1_unsplit_toyKem_refutable : ¬ KemEncaps1AgreesUnsplit Model.Braid.toyKem := by
  intro henc
  obtain ⟨es, ct1, ss, rng', rand', -, hsplit⟩ :=
    henc dummyRng dummyCryptoRng ⟨[], by simp⟩ () dummyRng_total
  obtain ⟨-, hss⟩ := hsplit [] [] rfl
  have := congrArg List.length hss
  simp [keyOf, Model.Braid.toyKem, ss.property] at this

/-- The over-strong `ValidateEkAgrees`: every split of the header. -/
def ValidateEkAgreesUnsplit (K : Model.Braid.Kem) : Prop :=
  ∀ (header ekVector : Slice Std.U8) (ekSeed hek : Bytes),
    sliceOf header = ekSeed ++ hek →
    ∃ r, tacenta_kem.validate_ek header ekVector = ok r ∧
      (r = true ↔ K.hashEk ekSeed (sliceOf ekVector) = hek)

/-- The validation check, at the toy KEM: a header of 32 zero bytes
splits as `[] ++ hdr` (the hash of `[]` and `[]` is 32 zero bytes, so the
check must say `true`) and as `hdr ++ []` (no hash is empty, so it must say
`false`), and it says one thing. -/
theorem validateEk_unsplit_toyKem_refutable : ¬ ValidateEkAgreesUnsplit Model.Braid.toyKem := by
  intro h
  let hdr : Slice Std.U8 := ⟨List.replicate 32 0#u8, by
    simp [Usize.max, Usize.numBits]; cases System.Platform.numBits_eq <;> simp_all⟩
  have hs : sliceOf hdr = List.replicate 32 0 := by
    simp [sliceOf, hdr, Tacenta.BraidT3.u8]
  obtain ⟨r₁, h₁, hi₁⟩ := h hdr ⟨[], by simp⟩ [] (List.replicate 32 0) (by simp [hs])
  obtain ⟨r₂, h₂, hi₂⟩ := h hdr ⟨[], by simp⟩ (List.replicate 32 0) [] (by simp [hs])
  rw [h₁] at h₂
  cases h₂
  have t₁ : r₁ = true := hi₁.mpr (by simp [Model.Braid.toyKem, sliceOf])
  have t₂ : r₁ ≠ true := fun hr => by
    have := hi₂.mp hr
    simp [Model.Braid.toyKem] at this
  exact t₂ t₁

/-- The over-strong `EncoderRefines`: every number of steps. -/
def EncoderRefinesUnbounded (real : tacenta_braid.tacenta_erasure.Encoder) (model : Model.Braid.Encoder) : Prop :=
  ∀ n, EncoderSim n real model

theorem encoderSim_index_bound (n : Nat) (real : tacenta_braid.tacenta_erasure.Encoder) (src : List UInt8)
    (k : Nat) (h : EncoderSim (n + 1) real ⟨src, k⟩) : k ≤ 65535 := by
  obtain ⟨chunk, -, -, hidx, -⟩ := h
  have := chunk.index.hmax
  simp [Model.Braid.Encoder.nextChunk] at hidx
  simp at this
  omega

theorem encoderSim_step (real : tacenta_braid.tacenta_erasure.Encoder) (src : List UInt8) (k : Nat)
    (h : EncoderRefinesUnbounded real ⟨src, k⟩) :
    ∃ real', EncoderRefinesUnbounded real' ⟨src, k + 1⟩ := by
  obtain ⟨chunk, real', hnext, -, -⟩ := h 1
  refine ⟨real', fun n => ?_⟩
  obtain ⟨chunk', real'', hnext', -, hsim⟩ := h (n + 1)
  rw [hnext] at hnext'
  cases hnext'
  simpa [Model.Braid.Encoder.nextChunk] using hsim

/-- Walk a fresh encoder 65,536 steps; the next chunk's index does not fit a
`u16`. So no real encoder satisfies the unbounded shape, for any model
encoder at all. -/
theorem encoderRefines_unbounded_refutable (real : tacenta_braid.tacenta_erasure.Encoder) (src : List UInt8) :
    ¬ EncoderRefinesUnbounded real ⟨src, 0⟩ := by
  intro hsim
  have key : ∀ k, ∃ real, EncoderRefinesUnbounded real ⟨src, k⟩ := by
    intro k
    induction k with
    | zero => exact ⟨real, hsim⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      exact encoderSim_step r src k hr
  obtain ⟨r, hr⟩ := key 65536
  have := encoderSim_index_bound 0 r src 65536 (hr 1)
  omega

/-- The over-strong `DecoderSim`: every model chunk with the real chunk's index. -/
def DecoderSimAllSources : Nat → tacenta_braid.tacenta_erasure.Decoder → Model.Braid.Decoder → Prop
  | 0, _, _ => True
  | n + 1, real, model =>
    (∀ (chunk : tacenta_braid.tacenta_erasure.Chunk) (advanced : Bool) (real' : tacenta_braid.tacenta_erasure.Decoder),
      tacenta_braid.tacenta_erasure.Decoder.add_chunk real chunk = ok (advanced, real') →
      ∀ modelChunk : Model.Braid.Chunk, modelChunk.index = chunk.index.val →
        DecoderSimAllSources n real' (model.addChunk modelChunk)) ∧
    (∀ msg, tacenta_braid.tacenta_erasure.Decoder.message real = ok msg →
      msg.map vecOf = model.message)

/-- One real chunk, two model sources, one total `message`. Stated for a
fresh 32-byte decoder that satisfies the over-strong shape for two steps. -/
theorem decoderSim_allSources_refutable (real0 : tacenta_braid.tacenta_erasure.Decoder)
    (hsim : DecoderSimAllSources 2 real0 (Model.Braid.Decoder.new 32))
    (hdadd : Tacenta.BraidT1.DecoderAddChunkTotal)
    (hdmsg : Tacenta.BraidT1.DecoderMessageTotal) : False := by
  let c : tacenta_braid.tacenta_erasure.Chunk := ⟨0#u16, ⟨List.replicate 32 0#u8, by simp⟩⟩
  obtain ⟨⟨adv, real1⟩, hadd⟩ := hdadd real0 c
  obtain ⟨hstep, -⟩ := hsim
  let mc1 : Model.Braid.Chunk := ⟨List.replicate 32 1, 0⟩
  let mc2 : Model.Braid.Chunk := ⟨List.replicate 32 2, 0⟩
  have hs1 := hstep c adv real1 hadd mc1 rfl
  have hs2 := hstep c adv real1 hadd mc2 rfl
  obtain ⟨msg, hmsg⟩ := hdmsg real1
  have e1 := hs1.2 msg hmsg
  have e2 := hs2.2 msg hmsg
  have m1 : ((Model.Braid.Decoder.new 32).addChunk mc1).message
      = some (List.replicate 32 1) := by decide
  have m2 : ((Model.Braid.Decoder.new 32).addChunk mc2).message
      = some (List.replicate 32 2) := by decide
  rw [m1] at e1
  rw [m2] at e2
  rw [e1] at e2
  simp at e2

end BraidRefutations

/-! ## HMAC and HKDF agreement, and `Option`'s clone

The classical ratchet and the Braid each declare their own opaque `hmac_sha256`
and `hkdf_sha256`, and the sparse ratchet and the session their own `hkdf_sha256`,
by the per-crate counting rule `SpqrT1.lean` describes, and the refinements take
an agreement hypothesis about each. The classical ratchet, the sparse ratchet and
the Braid each declare an opaque `Option` clone, and the sparse ratchet's and the
Braid's theorems take a hypothesis about theirs. The model's HMAC always returns a hash-length tag and
its HKDF exactly the requested length (`Model.Kdf.hmac_length`,
`Model.Kdf.hkdf_length`), so returning the model's bytes as an array is a model
of every agreement; the identity is a model of `OptionCloneTotal`. The shapes are
stated with `T3.lean`'s `keyOf` and `sliceOf`. The other crates' copies have the
same bodies, so each hypothesis is its shape by `Iff.rfl`, and each constant is
named by the `_is` theorem for its crate. -/

section KdfAndOptionClone

/-- The type of each crate's `tacenta_kdf.hmac_sha256`. -/
abbrev HmacFn := Slice Std.U8 → Slice Std.U8 → Result (Array Std.U8 32#usize)

/-- The type of each crate's `tacenta_kdf.hkdf_sha256`. -/
abbrev HkdfFn :=
  (N : Usize) → Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Result (Array Std.U8 N)

/-- The shape of `T3.HmacAgrees` and `BraidT3.BraidHmacAgrees`. -/
def HmacShape (f : HmacFn) : Prop :=
  ∀ key data, ∃ r, f key data = ok r ∧
    Tacenta.T3.keyOf r = Model.Kdf.hmac (Tacenta.T3.sliceOf key) (Tacenta.T3.sliceOf data)

/-- The shape of `T3.HkdfAgrees`, `SpqrT3.SpqrHkdfAgrees` and
`BraidT3.BraidHkdfAgrees`. -/
def HkdfShape (f : HkdfFn) : Prop :=
  ∀ N key salt info, N.val ≤ 8160 → ∃ r, f N key salt info = ok r ∧
    Tacenta.T3.keyOf r = Model.Kdf.hkdf (Tacenta.T3.sliceOf key)
      (Tacenta.T3.sliceOf salt) (Tacenta.T3.sliceOf info) N.val

/-- The shape of `SessionT3.HkdfAgrees`: a Hoare triple at the one width the
session derives. -/
def Hkdf32Shape (f : HkdfFn) : Prop :=
  ∀ (salt ikm info : Slice Std.U8),
    f 32#usize salt ikm info ⦃ fun r =>
      Tacenta.T3.keyOf r = Model.Kdf.hkdf (Tacenta.T3.sliceOf salt)
        (Tacenta.T3.sliceOf ikm) (Tacenta.T3.sliceOf info) 32 ⦄

theorem T3_HmacAgrees_is :
    Tacenta.T3.HmacAgrees ↔ HmacShape @tacenta_ratchet.tacenta_kdf.hmac_sha256 :=
  Iff.rfl

theorem T3_HkdfAgrees_is :
    Tacenta.T3.HkdfAgrees ↔ HkdfShape @tacenta_ratchet.tacenta_kdf.hkdf_sha256 :=
  Iff.rfl

theorem SpqrHkdfAgrees_is :
    Tacenta.SpqrT3.SpqrHkdfAgrees ↔ HkdfShape @tacenta_spqr.tacenta_kdf.hkdf_sha256 :=
  Iff.rfl

theorem SessionT3_HkdfAgrees_is :
    Tacenta.SessionT3.HkdfAgrees ↔ Hkdf32Shape @tacenta_session.tacenta_kdf.hkdf_sha256 :=
  Iff.rfl

theorem BraidHkdfAgrees_is :
    Tacenta.BraidT3.BraidHkdfAgrees ↔ HkdfShape @tacenta_braid.tacenta_kdf.hkdf_sha256 :=
  Iff.rfl

theorem BraidHmacAgrees_is :
    Tacenta.BraidT3.BraidHmacAgrees ↔ HmacShape @tacenta_braid.tacenta_kdf.hmac_sha256 :=
  Iff.rfl

/-- A model byte as a translated one. -/
def toU8 (x : UInt8) : Std.U8 := ⟨x.toBitVec⟩

theorem u8_toU8 (x : UInt8) : Tacenta.T3.u8 (toU8 x) = x := by
  show UInt8.ofNat x.toBitVec.toNat = x
  simp

def hmacWitness : HmacFn := fun key data =>
  ok ⟨(Model.Kdf.hmac (Tacenta.T3.sliceOf key) (Tacenta.T3.sliceOf data)).map toU8,
    by simp [Model.Kdf.hmac_length, Model.Kdf.hashLen]⟩

def hkdfWitness : HkdfFn := fun N key salt info =>
  ok ⟨(Model.Kdf.hkdf (Tacenta.T3.sliceOf key) (Tacenta.T3.sliceOf salt)
      (Tacenta.T3.sliceOf info) N.val).map toU8, by simp [Model.Kdf.hkdf_length]⟩

theorem hmac_agrees_satisfiable : ∃ f, HmacShape f :=
  ⟨hmacWitness, fun key data =>
    ⟨_, rfl, by simp [Tacenta.T3.keyOf, Function.comp_def, u8_toU8]⟩⟩

theorem hkdf_agrees_satisfiable : ∃ f, HkdfShape f :=
  ⟨hkdfWitness, fun N key salt info _ =>
    ⟨_, rfl, by simp [Tacenta.T3.keyOf, Function.comp_def, u8_toU8]⟩⟩

theorem hkdf32_agrees_satisfiable : ∃ f, Hkdf32Shape f :=
  ⟨hkdfWitness, fun salt ikm info => by
    simp [hkdfWitness, Tacenta.T3.keyOf, Function.comp_def, u8_toU8]⟩

/-- The type of each crate's `core.option.Option.Insts.CoreCloneClone.clone`. -/
abbrev OptionCloneFn := {T : Type} → core.clone.Clone T → Option T → Result (Option T)

/-- The shape of `SpqrT1.OptionCloneTotal` and `BraidT1.OptionCloneTotal`. -/
def OptionCloneShape (f : OptionCloneFn) : Prop :=
  ∀ {T : Type} (inst : core.clone.Clone T) (o : Option T),
    (∀ x, o = some x → inst.clone x ⦃ fun y => y = x ⦄) → f inst o ⦃ fun o' => o' = o ⦄

theorem SpqrT1_OptionCloneTotal_is :
    Tacenta.SpqrT1.OptionCloneTotal ↔
      OptionCloneShape @tacenta_spqr.core.option.Option.Insts.CoreCloneClone.clone :=
  Iff.rfl

theorem BraidT1_OptionCloneTotal_is :
    Tacenta.BraidT1.OptionCloneTotal ↔
      OptionCloneShape @tacenta_braid.core.option.Option.Insts.CoreCloneClone.clone :=
  Iff.rfl

theorem option_clone_satisfiable : ∃ f, OptionCloneShape f :=
  ⟨fun _ o => ok o, fun _ _ _ => by simp⟩

end KdfAndOptionClone

/-! ## Hypotheses that share a constant, witnessed together

The witnesses above take one hypothesis at a time. Where one theorem takes two
hypotheses about the same opaque constants, that is not enough to show they hold
together. Two groups of hypotheses about the same wrapper constants do:

* `T1.receive_no_panic` takes `T1.ZeroizingTotal` and `T1.DerivedKeysModel`, and
  `T3.receive_refines` takes `T3.ZeroizingRoundTrips` and `T1.DerivedKeysModel`
  (as do their decoded-state corollaries in `ImportInv.lean`), all about the
  classical ratchet's `zeroize.Zeroizing` constructor and projections.
  `T3.ZeroizingRoundTrips80` is about the same constants. `ratchet_zeroizing_joint_is`
  and `ratchet_zeroizing_joint_satisfiable` take all four at once.
* `SpqrT3.send_refines` and `receive_refines` take `ZeroizingRoundTrips96` and
  `ZeroizingRoundTrips64`, both about the sparse ratchet's wrapper.
  `spqr_zeroizing_joint_satisfiable` takes both at once.

The transparent wrapper models each group.

A third group is about translated functions rather than opaque constants.
`SpqrT1.receive_no_panic` and `ImportInv`'s `Spqr.decoded_receive_no_panic` take
`SpqrT1.KdfRkTotal`, `KdfCkTotal` and `ZeroizeTotal`, and `kdf_rk` and `kdf_ck`
both reach the sparse ratchet's `hkdf_sha256` and wrapper. Those two totalities
are not witnessed here. They follow from `SpqrHkdfAgrees` and the two round trips
(`SpqrHkdfAgrees.kdfRkTotal`/`kdfCkTotal` in `SpqrT3.lean`), which are witnessed,
the round trips jointly; `ZeroizeTotal` constrains a constant none of those
mentions, and that the separate witnesses combine is an argument in this comment,
not one Lean checks. -/

section JointWrappers

/-- The shape of `T1.ZeroizingTotal`: the classical ratchet's wrapper constructor
and projection both return, at sixty-four bytes. -/
def RatchetZeroizingTotal {W : Type → Type}
    (new : RatchetZeroizingNewFn W) (deref : RatchetZeroizingDerefFn W) : Prop :=
  ∀ inst : tacenta_ratchet.zeroize.Zeroize (Array Std.U8 64#usize),
    (∀ z, ∃ r, new inst z = ok r) ∧ (∀ z, ∃ r, deref inst z = ok r)

/-- Every hypothesis about the classical ratchet's wrapper, at once. -/
def RatchetZeroizingJoint {W : Type → Type} (contents : W DerivedKeys → DerivedKeys)
    (new : RatchetZeroizingNewFn W) (deref : RatchetZeroizingDerefFn W)
    (deref_mut : RatchetZeroizingDerefMutFn W) : Prop :=
  RatchetZeroizingTotal new deref ∧ ZeroizingRoundTripsTotal 64#usize new deref ∧
    ZeroizingRoundTripsTotal 80#usize new deref ∧
    DerivedKeysShape contents new deref deref_mut

theorem ratchet_zeroizing_joint_is :
    (Tacenta.T1.ZeroizingTotal ∧ Tacenta.T3.ZeroizingRoundTrips ∧
      Tacenta.T3.ZeroizingRoundTrips80 ∧ Nonempty Tacenta.T1.DerivedKeysModel) ↔
    ∃ contents, RatchetZeroizingJoint (W := tacenta_ratchet.zeroize.Zeroizing) contents
      @tacenta_ratchet.zeroize.Zeroizing.new
      @tacenta_ratchet.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      @tacenta_ratchet.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut :=
  ⟨fun ⟨a, b, c, ⟨m⟩⟩ => ⟨m.contents, a, b, c, m.new, m.deref, m.deref_mut⟩,
   fun ⟨k, a, b, c, hn, hd, hm⟩ => ⟨a, b, c, ⟨⟨k, hn, hd, hm⟩⟩⟩⟩

theorem ratchet_zeroizing_joint_satisfiable :
    ∃ (W : Type → Type) (contents : W DerivedKeys → DerivedKeys)
      (new : RatchetZeroizingNewFn W) (deref : RatchetZeroizingDerefFn W)
      (deref_mut : RatchetZeroizingDerefMutFn W),
      RatchetZeroizingJoint contents new deref deref_mut := by
  refine ⟨fun Z => Z, id, @ratchetZeroizingNewWitness, @ratchetZeroizingDerefWitness,
    @ratchetZeroizingDerefMutWitness, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ => ⟨fun z => ⟨z, rfl⟩, fun w => ⟨w, rfl⟩⟩
  · exact fun _ => ⟨fun z => ⟨z, rfl, rfl⟩, fun w => ⟨w, rfl⟩⟩
  · exact fun _ => ⟨fun z => ⟨z, rfl, rfl⟩, fun w => ⟨w, rfl⟩⟩
  all_goals intros; simp [ratchetZeroizingNewWitness, ratchetZeroizingDerefWitness,
    ratchetZeroizingDerefMutWitness]

theorem spqr_zeroizing_joint_is :
    (Tacenta.SpqrT3.ZeroizingRoundTrips96 ∧ Tacenta.SpqrT3.ZeroizingRoundTrips64) ↔
      (ZeroizingRoundTrips 96#usize (W := tacenta_spqr.zeroize.Zeroizing)
          @tacenta_spqr.zeroize.Zeroizing.new
          @tacenta_spqr.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref ∧
        ZeroizingRoundTrips 64#usize (W := tacenta_spqr.zeroize.Zeroizing)
          @tacenta_spqr.zeroize.Zeroizing.new
          @tacenta_spqr.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref) :=
  Iff.rfl

theorem spqr_zeroizing_joint_satisfiable :
    ∃ (W : Type → Type) (new : ZeroizingNewFn W) (deref : ZeroizingDerefFn W),
      ZeroizingRoundTrips 96#usize new deref ∧ ZeroizingRoundTrips 64#usize new deref :=
  ⟨fun Z => Z, @zeroizingNewWitness, @zeroizingDerefWitness,
    fun _ z => ⟨z, rfl, rfl⟩, fun _ z => ⟨z, rfl, rfl⟩⟩

end JointWrappers

/-! ## The rest of the leaves' opaque boundary

Five more hypotheses leaf theorems take about opaque constants, each about a
constant no other hypothesis witnessed here constrains:

* `SpqrT1.ZeroizeTotal`, that the sparse ratchet's array wipe returns, at any
  element type, width and instance;
* `SessionT1.HkdfTotal`, that the session's HKDF returns within RFC 5869's bound.
  `SessionT3.HkdfAgrees` does not imply it, being fixed at thirty-two bytes, so it
  needs its own witness, and `session_hkdf_satisfiable` gives one model of both;
* `SessionT1.ZeroizingModel`, the session's transparent-container model of its
  `zeroize` wrapper over a byte vector, taken beside those HKDF hypotheses but
  about different constants;
* `ErasureT1.DivCeilTotal` and `ErasureT1.TruncateTotal`, that the erasure
  crate's `usize::div_ceil`, for a nonzero divisor, and `Vec::truncate` return.

Six more are not witnessed directly but follow from witnessed hypotheses by named
theorems: `T1.HmacTotal` and `T1.HkdfTotal` from `T3.lean`'s agreements, the
Braid's `HkdfSha256Total` and `HmacSha256Total` from `BraidT3.lean`'s, and
`SpqrT1.KdfRkTotal` and `KdfCkTotal` from `SpqrHkdfAgrees` and the sparse
ratchet's round trips (`SpqrHkdfAgrees.kdfRkTotal`/`kdfCkTotal` in
`SpqrT3.lean`). -/

section RemainingLeafBoundary

/-- The type of `tacenta_spqr.Array.Insts.ZeroizeZeroize.zeroize`. -/
abbrev SpqrArrayZeroizeFn :=
  {Z : Type} → {N : Usize} → tacenta_spqr.zeroize.Zeroize Z → Array Z N → Result (Array Z N)

/-- The shape of `SpqrT1.ZeroizeTotal`. -/
def SpqrArrayZeroizeTotal (f : SpqrArrayZeroizeFn) : Prop :=
  ∀ {Z : Type} {N : Usize} (inst : tacenta_spqr.zeroize.Zeroize Z) (a : Array Z N),
    ∃ r, f inst a = ok r

theorem SpqrT1_ZeroizeTotal_is :
    Tacenta.SpqrT1.ZeroizeTotal ↔
      SpqrArrayZeroizeTotal @tacenta_spqr.Array.Insts.ZeroizeZeroize.zeroize :=
  Iff.rfl

theorem spqr_array_zeroize_total_satisfiable : ∃ f, SpqrArrayZeroizeTotal f :=
  ⟨fun _ a => ok a, fun _ a => ⟨a, rfl⟩⟩

/-- The shape of `SessionT1.HkdfTotal`. -/
def HkdfTotalShape (f : HkdfFn) : Prop :=
  ∀ (N : Usize) (salt ikm info : Slice Std.U8), N.val ≤ 8160 → ∃ r, f N salt ikm info = ok r

theorem SessionT1_HkdfTotal_is :
    Tacenta.SessionT1.HkdfTotal ↔ HkdfTotalShape @tacenta_session.tacenta_kdf.hkdf_sha256 :=
  Iff.rfl

/-- One model of both of the session's HKDF hypotheses at once. -/
theorem session_hkdf_satisfiable : ∃ f, HkdfTotalShape f ∧ Hkdf32Shape f :=
  ⟨hkdfWitness, fun _ _ _ _ _ => ⟨_, rfl⟩, fun salt ikm info => by
    simp [hkdfWitness, Tacenta.T3.keyOf, Function.comp_def, u8_toU8]⟩

/-- The one type the session wraps. -/
abbrev SessionBytes := alloc.vec.Vec Std.U8

abbrev SessionZeroizingNewFn (W : Type → Type) :=
  {Z : Type} → tacenta_session.zeroize.Zeroize Z → Z → Result (W Z)

abbrev SessionZeroizingDerefFn (W : Type → Type) :=
  {Z : Type} → tacenta_session.zeroize.Zeroize Z → W Z → Result Z

abbrev SessionZeroizingDerefMutFn (W : Type → Type) :=
  {Z : Type} → tacenta_session.zeroize.Zeroize Z → W Z → Result (Z × (Z → W Z))

/-- The shape of `SessionT1.ZeroizingModel`'s three equations, at a contents
function. -/
def SessionZeroizingShape {W : Type → Type} (contents : W SessionBytes → SessionBytes)
    (new : SessionZeroizingNewFn W) (deref : SessionZeroizingDerefFn W)
    (deref_mut : SessionZeroizingDerefMutFn W) : Prop :=
  (∀ (inst : tacenta_session.zeroize.Zeroize SessionBytes) (v : SessionBytes),
    new inst v ⦃ fun z => contents z = v ⦄) ∧
  (∀ (inst : tacenta_session.zeroize.Zeroize SessionBytes) (z : W SessionBytes),
    deref inst z ⦃ fun v => v = contents z ⦄) ∧
  (∀ (inst : tacenta_session.zeroize.Zeroize SessionBytes) (z : W SessionBytes),
    deref_mut inst z ⦃ fun p => p.1 = contents z ∧ ∀ v', contents (p.2 v') = v' ⦄)

theorem SessionT1_ZeroizingModel_is :
    Nonempty Tacenta.SessionT1.ZeroizingModel ↔
      ∃ contents, SessionZeroizingShape (W := tacenta_session.zeroize.Zeroizing) contents
        @tacenta_session.zeroize.Zeroizing.new
        @tacenta_session.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        @tacenta_session.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut :=
  ⟨fun ⟨m⟩ => ⟨m.contents, m.new, m.deref, m.deref_mut⟩,
   fun ⟨c, hn, hd, hm⟩ => ⟨⟨c, hn, hd, hm⟩⟩⟩

theorem session_zeroizing_model_satisfiable :
    ∃ (W : Type → Type) (contents : W SessionBytes → SessionBytes)
      (new : SessionZeroizingNewFn W) (deref : SessionZeroizingDerefFn W)
      (deref_mut : SessionZeroizingDerefMutFn W),
      SessionZeroizingShape contents new deref deref_mut := by
  refine ⟨fun Z => Z, id, fun _ z => ok z, fun _ w => ok w, fun _ w => ok (w, id), ?_, ?_, ?_⟩
  all_goals intros; simp

/-- The type of `tacenta_erasure.core.num.Usize.div_ceil`. -/
abbrev DivCeilFn := Std.Usize → Std.Usize → Result Std.Usize

/-- The shape of `ErasureT1.DivCeilTotal`. -/
def DivCeilTotalShape (f : DivCeilFn) : Prop :=
  ∀ a b : Std.Usize, b.val ≠ 0 → ∃ r, f a b = ok r

theorem ErasureT1_DivCeilTotal_is :
    Tacenta.ErasureT1.DivCeilTotal ↔ DivCeilTotalShape tacenta_erasure.core.num.Usize.div_ceil :=
  Iff.rfl

theorem div_ceil_total_satisfiable : ∃ f, DivCeilTotalShape f :=
  ⟨fun a _ => ok a, fun a _ _ => ⟨a, rfl⟩⟩

/-- The type of `tacenta_erasure.alloc.vec.Vec.truncate`. -/
abbrev TruncateFn :=
  {T : Type} → (A : Type) → alloc.vec.Vec T → Std.Usize → Result (alloc.vec.Vec T)

/-- The shape of `ErasureT1.TruncateTotal`. -/
def TruncateTotalShape (f : TruncateFn) : Prop :=
  ∀ (v : alloc.vec.Vec Std.U8) (n : Std.Usize), ∃ r, f Global v n = ok r

theorem ErasureT1_TruncateTotal_is :
    Tacenta.ErasureT1.TruncateTotal ↔ TruncateTotalShape @tacenta_erasure.alloc.vec.Vec.truncate :=
  Iff.rfl

theorem truncate_total_satisfiable : ∃ f, TruncateTotalShape f :=
  ⟨fun _ v _ => ok v, fun v _ => ⟨v, rfl⟩⟩

end RemainingLeafBoundary

end Tacenta.Satisfiability
