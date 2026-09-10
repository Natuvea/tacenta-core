import Translation.UnitTripleT3

/-!
# Satisfiability on the unit: the Triple's `zeroize` hypotheses and the inner boundary

`Translation/UnitTripleT3.lean` restates the Triple Ratchet's refinement about the
three-leaf translation unit, and its discharged theorems take the boundary the
inner refinements take, restated about the unit's constants.
`Translation/Satisfiability.lean` witnesses the leaves' copies of most of those
hypotheses, but it is about the leaves' constants and cannot share a Lean
environment with the unit, so it says nothing about these. This file witnesses
the unit's own, in the same style. Each hypothesis is shown to be exactly a shape
at the unit's constants -- by `Iff.rfl`, except the joint wrapper group, whose
`Nonempty` conjunct needs an explicit equivalence -- and a model of that shape is
exhibited.
Consistency is all this establishes: the theorems downstream are not proofs of
`False`.

## The Triple's own two hypotheses

`UnitTripleT3.lean` states `ZeroizingRoundTrips` for `split_secret`'s
sixty-four-byte wrapper, and `UnitTripleT1.lean` takes `UnitT1.ZeroizingTotal`.
On the unit the first is `UnitT3.ZeroizingRoundTrips` itself
(`ZeroizingRoundTrips_is_classical`, by `Iff.rfl`): the Triple and the classical
ratchet wrap the same width with the same constants. So its witness is also a
witness for that inner hypothesis. It is strictly stronger than
`UnitSpqrT3.ZeroizingRoundTrips64`, which lacks the second conjunct.

## Hypotheses that share a constant

On the leaves the classical and sparse ratchets' hypotheses constrain different
constants, though one ratchet's can share one: `T3.lean` takes both
`ZeroizingRoundTrips` and `T1.DerivedKeysModel`, about one wrapper, and
`Satisfiability.lean` witnesses those together. On the unit the sharing also
crosses ratchets, and a witness for each hypothesis on its own would not show
they hold together:

* `UnitT3.ZeroizingRoundTrips`, `UnitSpqrT3.ZeroizingRoundTrips96` and
  `ZeroizingRoundTrips64`, `UnitTripleT3.ZeroizingRoundTrips` and
  `UnitT1.DerivedKeysModel` all constrain the one `zeroize.Zeroizing` family.
  `zeroizing_joint_satisfiable` witnesses all five at once.
* `UnitT1.VecRemoveTotal` and `UnitSpqrT3.VecRemoveAgrees` both constrain
  `alloc.vec.Vec.remove`. `vec_remove_joint_satisfiable` witnesses both.

The other witnessed hypotheses, `UnitT3.HmacAgrees`, `UnitT3.HkdfAgrees` (which
`UnitSpqrT3.SpqrHkdfAgrees` and `UnitTripleT3.TripleHkdfAgrees` are, by `Iff.rfl`),
`UnitSpqrT3.VecAppendAgrees`, `UnitSpqrT3.VecRetainAgrees`,
`UnitSpqrT1.OptionCloneTotal` and the general `UnitSpqrT1.ZeroizeTotal`, each
constrain a constant no other hypothesis here mentions. That their separate
witnesses combine is an argument about independent opaque constants, made in this
comment and not checked by Lean.

## Coverage

Together these cover every boundary hypothesis the two discharged theorems take.
The two `example`s at the end check that against the theorems themselves: each
applies one theorem to exactly the hypotheses witnessed here, in its signature's
order, up to the state relation. A boundary hypothesis added to the theorem ahead
of that point, or replaced by a proposition these are not, stops this file
building.

## The leaves' copies

The leaves' copies of these hypotheses are witnessed in `Satisfiability.lean`,
about the leaves' own constants, the shared-wrapper ones jointly.

No over-strong shape is refuted here. `Satisfiability.lean` keeps the refutations
of the unguarded `Vec` shapes, and the unit's hypotheses carry the same guards.
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

/-- The shape of `UnitT1.ZeroizingTotal`: constructor and projection both
return, at the sixty-four-byte width. -/
def ZeroizingTotal {W : Type → Type}
    (new : TripleZeroizingNewFn W) (deref : TripleZeroizingDerefFn W) : Prop :=
  ∀ inst : tacenta_triple_unit.zeroize.Zeroize (Array Std.U8 64#usize),
    (∀ z, ∃ r, new inst z = ok r) ∧
    (∀ z, ∃ r, deref inst z = ok r)

/-- The shape of `UnitTripleT3.ZeroizingRoundTrips`: the round trip, and the
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

/-- On the unit the Triple's round trip is the classical ratchet's: the same
constants, at the same width. -/
theorem ZeroizingRoundTrips_is_classical :
    Tacenta.UnitTripleT3.ZeroizingRoundTrips ↔ Tacenta.UnitT3.ZeroizingRoundTrips :=
  Iff.rfl

/-- The transparent wrapper, at the unit's copy of the `Zeroize` trait. -/
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

section InnerBoundary

open tacenta_triple_unit

/-! ## The `zeroize.Zeroizing` family, jointly -/

/-- The type of `zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut`, at a
wrapper `W`. -/
abbrev ZeroizingDerefMutFn (W : Type → Type) :=
  {Z : Type} → zeroize.Zeroize Z → W Z → Result (Z × (Z → W Z))

/-- The vector of derived keys `UnitT1.DerivedKeysModel` speaks about. -/
abbrev DerivedKeys := alloc.vec.Vec (U32 × Array U8 32#usize)

/-- The round trip alone, at width `N`: the shape of
`UnitSpqrT3.ZeroizingRoundTrips96` and `ZeroizingRoundTrips64`. -/
def RoundTrip (N : Usize) {W : Type → Type}
    (new : TripleZeroizingNewFn W) (deref : TripleZeroizingDerefFn W) : Prop :=
  ∀ inst : zeroize.Zeroize (Array U8 N), ∀ z, ∃ w, new inst z = ok w ∧ deref inst w = ok z

/-- The shape of `UnitT1.DerivedKeysModel`'s three laws, at a contents map. -/
def DerivedKeysShape {W : Type → Type} (contents : W DerivedKeys → DerivedKeys)
    (new : TripleZeroizingNewFn W) (deref : TripleZeroizingDerefFn W)
    (dm : ZeroizingDerefMutFn W) : Prop :=
  (∀ (inst : zeroize.Zeroize DerivedKeys) (v : DerivedKeys),
    new inst v ⦃ fun z => contents z = v ⦄) ∧
  (∀ (inst : zeroize.Zeroize DerivedKeys) (z : W DerivedKeys),
    deref inst z ⦃ fun v => v = contents z ⦄) ∧
  (∀ (inst : zeroize.Zeroize DerivedKeys) (z : W DerivedKeys),
    dm inst z ⦃ fun p => p.1 = contents z ∧ ∀ v', contents (p.2 v') = v' ⦄)

/-- Every hypothesis about the wrapper family the discharged theorems take, at
once: the sixty-four-byte round trip with total projection (the classical
ratchet's and the Triple's, which are one proposition), the sparse ratchet's two
round trips, and the derived-keys model. -/
def ZeroizingJoint {W : Type → Type} (contents : W DerivedKeys → DerivedKeys)
    (new : TripleZeroizingNewFn W) (deref : TripleZeroizingDerefFn W)
    (dm : ZeroizingDerefMutFn W) : Prop :=
  ZeroizingRoundTrips new deref ∧ RoundTrip 96#usize new deref ∧
    RoundTrip 64#usize new deref ∧ DerivedKeysShape contents new deref dm

theorem zeroizing_joint_is :
    (Tacenta.UnitT3.ZeroizingRoundTrips ∧ Tacenta.UnitSpqrT3.ZeroizingRoundTrips96 ∧
      Tacenta.UnitSpqrT3.ZeroizingRoundTrips64 ∧ Tacenta.UnitTripleT3.ZeroizingRoundTrips ∧
      Nonempty Tacenta.UnitT1.DerivedKeysModel) ↔
    ∃ contents, ZeroizingJoint (W := zeroize.Zeroizing) contents
      @zeroize.Zeroizing.new @zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      @zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut :=
  ⟨fun ⟨a, b, c, _, ⟨m⟩⟩ => ⟨m.contents, a, b, c, m.new, m.deref, m.deref_mut⟩,
   fun ⟨k, a, b, c, hn, hd, hm⟩ => ⟨a, b, c, a, ⟨⟨k, hn, hd, hm⟩⟩⟩⟩

theorem zeroizing_joint_satisfiable :
    ∃ (W : Type → Type) (contents : W DerivedKeys → DerivedKeys)
      (new : TripleZeroizingNewFn W) (deref : TripleZeroizingDerefFn W)
      (dm : ZeroizingDerefMutFn W), ZeroizingJoint contents new deref dm := by
  refine ⟨fun Z => Z, id, fun _ z => ok z, fun _ w => ok w, fun _ w => ok (w, id), ?_⟩
  refine ⟨fun _ => ⟨fun z => ⟨z, rfl, rfl⟩, fun w => ⟨w, rfl⟩⟩,
    fun _ z => ⟨z, rfl, rfl⟩, fun _ z => ⟨z, rfl, rfl⟩, ?_, ?_, ?_⟩
  all_goals intros; simp

/-! ## `Vec::remove`, jointly -/

/-- The type of `alloc.vec.Vec.remove`. -/
abbrev RemoveFn :=
  {T : Type} → (A : Type) → alloc.vec.Vec T → Usize → Result (T × alloc.vec.Vec T)

/-- The classical ratchet's `VecRemoveTotal` and the sparse ratchet's
`VecRemoveAgrees`, which on the unit are about the one `remove`. -/
def RemoveJoint (f : RemoveFn) : Prop :=
  (∀ {T : Type} (A : Type) (v : alloc.vec.Vec T) (i : Usize), i.val < v.val.length →
    ∃ r, f A v i = ok r ∧ r.2.val = v.val.eraseIdx i.val) ∧
  (∀ {T : Type} (A : Type) (v : alloc.vec.Vec T) (i : Usize) (h : i.val < v.val.length),
    ∃ r, f A v i = ok r ∧ r.1 = v.val[i.val]'h ∧ r.2.val = v.val.eraseIdx i.val)

theorem vec_remove_joint_is :
    (Tacenta.UnitT1.VecRemoveTotal ∧ Tacenta.UnitSpqrT3.VecRemoveAgrees) ↔
      RemoveJoint @alloc.vec.Vec.remove :=
  Iff.rfl

/-- What the real `Vec::remove` does: the element and the rest when the index is
in range, a panic otherwise. -/
def removeWitness : RemoveFn := fun {_T} _A v i =>
  if h : i.val < v.val.length then
    ok (v.val[i.val], ⟨v.val.eraseIdx i.val, le_trans (List.length_eraseIdx_le _ _) v.property⟩)
  else fail .panic

theorem vec_remove_joint_satisfiable : ∃ f, RemoveJoint f := by
  refine ⟨@removeWitness, fun A v i h => ?_, fun A v i h => ?_⟩
  · exact ⟨(v.val[i.val], ⟨v.val.eraseIdx i.val, le_trans (List.length_eraseIdx_le _ _) v.property⟩),
      by simp [removeWitness, h], rfl⟩
  · exact ⟨(v.val[i.val], ⟨v.val.eraseIdx i.val, le_trans (List.length_eraseIdx_le _ _) v.property⟩),
      by simp [removeWitness, h], rfl, rfl⟩

/-! ## `Vec::append` -/

/-- The type of `alloc.vec.Vec.append`. -/
abbrev AppendFn :=
  {T : Type} → (A : Type) → alloc.vec.Vec T → alloc.vec.Vec T →
    Result (alloc.vec.Vec T × alloc.vec.Vec T)

/-- The shape of `UnitSpqrT3.VecAppendAgrees`. -/
def AppendAgrees (f : AppendFn) : Prop :=
  ∀ {T : Type} (A : Type) (v w : alloc.vec.Vec T),
    v.length + w.length ≤ Usize.max →
    ∃ r, f A v w = ok r ∧ r.1.val = v.val ++ w.val

theorem VecAppendAgrees_is :
    Tacenta.UnitSpqrT3.VecAppendAgrees ↔ AppendAgrees @alloc.vec.Vec.append :=
  Iff.rfl

/-- Concatenate when the result fits, fail otherwise, as the real `Vec::append`
does at the capacity boundary. -/
def appendWitness : AppendFn := fun {_T} _A v w =>
  if h : v.val.length + w.val.length ≤ Usize.max then
    ok (⟨v.val ++ w.val, by simpa using h⟩, w)
  else fail .panic

theorem append_agrees_satisfiable : ∃ f : AppendFn, AppendAgrees f := by
  refine ⟨@appendWitness, fun A v w hlen => ?_⟩
  simp only [alloc.vec.Vec.length] at hlen
  exact ⟨(⟨v.val ++ w.val, by simpa using hlen⟩, w), by simp [appendWitness, hlen], rfl⟩

/-! ## `Vec::retain` -/

/-- The type of `alloc.vec.Vec.retain`. -/
abbrev RetainFn :=
  {T : Type} → (A : Type) → {F : Type} → core.ops.function.FnMut F T Bool →
    alloc.vec.Vec T → F → Result (alloc.vec.Vec T)

/-- The shape of `UnitSpqrT3.VecRetainAgrees`. -/
def RetainAgrees (f : RetainFn) : Prop :=
  ∀ {T F : Type} (A : Type) (inst : core.ops.function.FnMut F T Bool)
    (v : alloc.vec.Vec T) (g : F) (p : T → Bool)
    (_hp : ∀ x, inst.call_mut g x = ok (p x, g)),
    ∃ r, f A inst v g = ok r ∧ r.val = v.val.filter p

theorem VecRetainAgrees_is :
    Tacenta.UnitSpqrT3.VecRetainAgrees ↔ RetainAgrees @alloc.vec.Vec.retain :=
  Iff.rfl

theorem length_filter_le_max {T : Type} (p : T → Bool) (v : alloc.vec.Vec T) :
    (v.val.filter p).length ≤ Usize.max :=
  le_trans (List.length_filter_le _ _) v.property

open Classical in
/-- When the closure is a pure predicate that leaves its state alone, filter by
it; otherwise keep everything. Classical, because recovering the predicate from
the closure is a choice. -/
noncomputable def retainWitness : RetainFn := fun {T} _A {_F} inst v g =>
  if h : ∃ p : T → Bool, ∀ x, inst.call_mut g x = ok (p x, g) then
    ok ⟨v.val.filter (Classical.choose h), length_filter_le_max _ v⟩
  else ok v

theorem retain_agrees_satisfiable : ∃ f : RetainFn, RetainAgrees f := by
  refine ⟨@retainWitness, ?_⟩
  intro T F A inst v g p hp
  have h : ∃ p : T → Bool, ∀ x, inst.call_mut g x = ok (p x, g) := ⟨p, hp⟩
  refine ⟨⟨v.val.filter (Classical.choose h), length_filter_le_max _ v⟩,
    by simp [retainWitness, h], ?_⟩
  apply List.filter_congr
  intro x _
  have := Classical.choose_spec h x
  rw [hp x] at this
  exact (Prod.mk.inj (Result.ok.inj this)).1.symm

/-! ## `Option`'s clone -/

/-- The type of `core.option.Option.Insts.CoreCloneClone.clone`. -/
abbrev OptionCloneFn := {T : Type} → core.clone.Clone T → Option T → Result (Option T)

/-- The shape of `UnitSpqrT1.OptionCloneTotal`. -/
def OptionCloneShape (f : OptionCloneFn) : Prop :=
  ∀ {T : Type} (inst : core.clone.Clone T) (o : Option T),
    (∀ x, o = some x → inst.clone x ⦃ fun y => y = x ⦄) → f inst o ⦃ fun o' => o' = o ⦄

theorem OptionCloneTotal_is :
    Tacenta.UnitSpqrT1.OptionCloneTotal ↔
      OptionCloneShape @core.option.Option.Insts.CoreCloneClone.clone :=
  Iff.rfl

theorem option_clone_satisfiable : ∃ f, OptionCloneShape f :=
  ⟨fun _ o => ok o, fun _ _ _ => by simp⟩

/-! ## The general array `zeroize` -/

/-- The type of `Array.Insts.ZeroizeZeroize.zeroize`. -/
abbrev ArrayZeroizeFn :=
  {Z : Type} → {N : Usize} → zeroize.Zeroize Z → Array Z N → Result (Array Z N)

/-- The shape of `UnitSpqrT1.ZeroizeTotal`, which quantifies over the element
type, the width and the instance. -/
def ArrayZeroizeTotal (f : ArrayZeroizeFn) : Prop :=
  ∀ {Z : Type} {N : Usize} (inst : zeroize.Zeroize Z) (a : Array Z N), ∃ r, f inst a = ok r

theorem ZeroizeTotal_is :
    Tacenta.UnitSpqrT1.ZeroizeTotal ↔ ArrayZeroizeTotal @Array.Insts.ZeroizeZeroize.zeroize :=
  Iff.rfl

theorem array_zeroize_total_satisfiable : ∃ f, ArrayZeroizeTotal f :=
  ⟨fun {_Z} {_N} _inst a => ok a, fun _ a => ⟨a, rfl⟩⟩

end InnerBoundary

/-! ## HMAC and HKDF agreement

The model's HMAC always returns a hash-length tag and its HKDF exactly the
requested length (`Model.Kdf.hmac_length`, `Model.Kdf.hkdf_length`), so returning
the model's bytes as an array is a model of each agreement. -/

/-- The type of `tacenta_triple_unit.tacenta_kdf.hmac_sha256`. -/
abbrev HmacFn := Slice Std.U8 → Slice Std.U8 → Result (Array Std.U8 32#usize)

/-- The type of `tacenta_triple_unit.tacenta_kdf.hkdf_sha256`. -/
abbrev HkdfFn :=
  (N : Usize) → Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Result (Array Std.U8 N)

/-- The shape of `UnitT3.HmacAgrees`. -/
def HmacShape (f : HmacFn) : Prop :=
  ∀ key data, ∃ r, f key data = ok r ∧
    Tacenta.UnitT3.keyOf r = Model.Kdf.hmac (Tacenta.UnitT3.sliceOf key) (Tacenta.UnitT3.sliceOf data)

/-- The shape of `UnitT3.HkdfAgrees`. -/
def HkdfShape (f : HkdfFn) : Prop :=
  ∀ N key salt info, N.val ≤ 8160 → ∃ r, f N key salt info = ok r ∧
    Tacenta.UnitT3.keyOf r = Model.Kdf.hkdf (Tacenta.UnitT3.sliceOf key)
      (Tacenta.UnitT3.sliceOf salt) (Tacenta.UnitT3.sliceOf info) N.val

theorem HmacAgrees_is :
    Tacenta.UnitT3.HmacAgrees ↔ HmacShape @tacenta_triple_unit.tacenta_kdf.hmac_sha256 :=
  Iff.rfl

theorem HkdfAgrees_is :
    Tacenta.UnitT3.HkdfAgrees ↔ HkdfShape @tacenta_triple_unit.tacenta_kdf.hkdf_sha256 :=
  Iff.rfl

/-- The sparse ratchet's and the Triple's HKDF agreements are the classical one. -/
theorem SpqrHkdfAgrees_is_classical :
    Tacenta.UnitSpqrT3.SpqrHkdfAgrees ↔ Tacenta.UnitT3.HkdfAgrees :=
  Iff.rfl

theorem TripleHkdfAgrees_is_classical :
    Tacenta.UnitTripleT3.TripleHkdfAgrees ↔ Tacenta.UnitT3.HkdfAgrees :=
  Iff.rfl

/-- A model byte as a translated one. -/
def toU8 (x : UInt8) : Std.U8 := ⟨x.toBitVec⟩

theorem u8_toU8 (x : UInt8) : Tacenta.UnitT3.u8 (toU8 x) = x := by
  show UInt8.ofNat x.toBitVec.toNat = x
  simp

def hmacWitness : HmacFn := fun key data =>
  ok ⟨(Model.Kdf.hmac (Tacenta.UnitT3.sliceOf key) (Tacenta.UnitT3.sliceOf data)).map toU8,
    by simp [Model.Kdf.hmac_length, Model.Kdf.hashLen]⟩

def hkdfWitness : HkdfFn := fun N key salt info =>
  ok ⟨(Model.Kdf.hkdf (Tacenta.UnitT3.sliceOf key) (Tacenta.UnitT3.sliceOf salt)
      (Tacenta.UnitT3.sliceOf info) N.val).map toU8, by simp [Model.Kdf.hkdf_length]⟩

theorem hmac_agrees_satisfiable : ∃ f, HmacShape f :=
  ⟨hmacWitness, fun key data =>
    ⟨_, rfl, by simp [Tacenta.UnitT3.keyOf, Function.comp_def, u8_toU8]⟩⟩

theorem hkdf_agrees_satisfiable : ∃ f, HkdfShape f :=
  ⟨hkdfWitness, fun N key salt info _ =>
    ⟨_, rfl, by simp [Tacenta.UnitT3.keyOf, Function.comp_def, u8_toU8]⟩⟩

/-! ## Coverage, checked against the discharged theorems -/

example (hmac : Tacenta.UnitT3.HmacAgrees) (hkdf : Tacenta.UnitT3.HkdfAgrees)
    (hzr : Tacenta.UnitT3.ZeroizingRoundTrips) (hvr : Tacenta.UnitT1.VecRemoveTotal)
    [Tacenta.UnitT1.DerivedKeysModel]
    (hz96 : Tacenta.UnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.UnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.UnitSpqrT3.VecRetainAgrees) (happ : Tacenta.UnitSpqrT3.VecAppendAgrees)
    (hrm : Tacenta.UnitSpqrT3.VecRemoveAgrees) (hzs : Tacenta.UnitSpqrT1.ZeroizeTotal)
    (hopt : Tacenta.UnitSpqrT1.OptionCloneTotal)
    {s : tacenta_triple_unit.tacenta_triple.State} {m : Model.Triple.State}
    (hrel : Tacenta.UnitTripleT3.StateRefines Tacenta.UnitTripleT3.ratchetAbs
      Tacenta.UnitTripleT3.spqrAbs s m) :=
  Tacenta.UnitTripleT3.send_refines_discharged hmac hkdf hzr hvr hz96 hz64 hret happ hrm
    hzs hopt hrel

example (hmac : Tacenta.UnitT3.HmacAgrees) (hkdf : Tacenta.UnitT3.HkdfAgrees)
    (hzr : Tacenta.UnitT3.ZeroizingRoundTrips) (hvr : Tacenta.UnitT1.VecRemoveTotal)
    [Tacenta.UnitT1.DerivedKeysModel]
    (hz96 : Tacenta.UnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.UnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.UnitSpqrT3.VecRetainAgrees) (happ : Tacenta.UnitSpqrT3.VecAppendAgrees)
    (hrm : Tacenta.UnitSpqrT3.VecRemoveAgrees) (hzs : Tacenta.UnitSpqrT1.ZeroizeTotal)
    (hopt : Tacenta.UnitSpqrT1.OptionCloneTotal)
    {s : tacenta_triple_unit.tacenta_triple.State} {m : Model.Triple.State}
    (hrel : Tacenta.UnitTripleT3.StateRefines Tacenta.UnitTripleT3.ratchetAbs
      Tacenta.UnitTripleT3.spqrAbs s m) :=
  Tacenta.UnitTripleT3.receive_refines_discharged hmac hkdf hzr hvr hz96 hz64 hret happ hrm
    hzs hopt hrel

end Tacenta.UnitSatisfiabilityTriple
