import Translation.UnitSatisfiabilityJoint

/-!
# Why three contract fields are stated at the unit's instances

`SessionUnitSpqrT1.ZeroizeTotal`, `SessionUnitBraidT1.ArrayZeroizeTotal` and the `Vec::zeroize`
conjunct of `SessionUnitSpqrT1.VecRetainTotal` used to say that `Array::zeroize` and `Vec::zeroize`
return for **every** instance record `inst : Zeroize Z`.  The real functions call `inst.zeroize` on
each element, and a `Zeroize` record whose field fails (a panicking implementation) is a legal Lean
term.  The Lean constants are opaque, so nothing in Lean refuted those general forms, and the joint
model satisfied them; but the real functions satisfy them only for instances whose `zeroize`
returns, so they were stronger than the code supports.  The fields are now stated at the instances
the unit passes: `Array::zeroize` at the blanket `u8` instance on 32-byte arrays, and
`Vec::zeroize` at the chain table, the sparse skipped-key store and the classical one
(`UnitSatisfiabilityJoint.SpqrZeroizeShape`, `ArrayZeroizeShape`, `VecRetainAxiomShape`).

This module keeps the general forms (`*UnscopedShape`) as the record of why the fields moved:

* `zeroize_failure_propagation_conflicts`, `braid_zeroize_failure_propagation_conflicts` and
  `vec_zeroize_failure_propagation_conflicts`: no interpretation satisfies a general form and also
  has the operation propagate the failure of a failing instance, which is what the real function
  does.
* `spqrZeroize_of_unscoped`, `arrayZeroize_of_unscoped`, `vecRetainAxiom_of_unscoped`: each general
  form implies the field as now stated, over every interpretation, so the restatement only weakens
  what the records assume.
* `Interp.faithful` implements `Array::zeroize`, `Vec::zeroize` and the pair `Zeroize` as the crate
  does (zeroize each element in order, fail if an element fails; `Vec::zeroize` leaves an empty
  vector).  `faithful_propagates` and `faithful_vec_propagates` show it propagates failures,
  `faithful_refutes_unscoped` that it refutes the general form, and
  `faithful_satisfies_all_axiom_shapes` that it satisfies every axiom-level shape of the joint
  model, the three restated fields among them.

None of this shows that the real functions return at the unit's instances; that stays an
assumption (`LIMITATIONS.md`).  No proof module imports this one; `AxiomAuditSessionUnit.lean`
imports it so that the environment audit covers it.
-/

namespace Tacenta.UnitSatisfiabilityZeroizeScope

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitSatisfiabilityJoint

section ScopedZeroize

/-- Zeroize each element in order, stopping at the first failure. -/
def mapZ {Z : Type} (inst : zeroize.Zeroize Z) : List Z → Result (List Z)
  | [] => ok []
  | x :: xs => do
    let y ← inst.zeroize x
    let ys ← mapZ inst xs
    ok (y :: ys)

theorem mapZ_length {Z : Type} (inst : zeroize.Zeroize Z) :
    ∀ (l l' : List Z), mapZ inst l = ok l' → l'.length = l.length
  | [], l', h => by
    simp only [mapZ, ok.injEq] at h
    subst h; rfl
  | x :: xs, l', h => by
    simp only [mapZ] at h
    cases hx : inst.zeroize x with
    | ok y =>
      rw [hx] at h
      simp only [Aeneas.Std.bind_tc_ok] at h
      cases hxs : mapZ inst xs with
      | ok ys =>
        rw [hxs] at h
        simp only [Aeneas.Std.bind_tc_ok, ok.injEq] at h
        subst h
        simp [mapZ_length inst xs ys hxs]
      | fail e => rw [hxs] at h; simp at h
      | div => rw [hxs] at h; simp at h
    | fail e => rw [hx] at h; simp at h
    | div => rw [hx] at h; simp at h

theorem mapZ_total {Z : Type} (inst : zeroize.Zeroize Z)
    (h : ∀ x, ∃ y, inst.zeroize x = ok y) : ∀ l : List Z, ∃ l', mapZ inst l = ok l'
  | [] => ⟨[], rfl⟩
  | x :: xs => by
    obtain ⟨y, hy⟩ := h x
    obtain ⟨ys, hys⟩ := mapZ_total inst h xs
    exact ⟨y :: ys, by simp [mapZ, hy, hys]⟩

def arrayZeroizeImpl {Z : Type} {N : Usize} (inst : zeroize.Zeroize Z) (a : Array Z N) :
    Result (Array Z N) :=
  match h : mapZ inst a.val with
  | ok l => ok ⟨l, by rw [mapZ_length inst _ _ h]; exact a.property⟩
  | fail e => fail e
  | div => div

def vecZeroizeImpl {Z : Type} (inst : zeroize.Zeroize Z) (v : alloc.vec.Vec Z) :
    Result (alloc.vec.Vec Z) :=
  match mapZ inst v.val with
  | ok _ => ok (alloc.vec.Vec.new Z)
  | fail e => fail e
  | div => div

/-- The pair `Zeroize` as the crate implements it: zeroize the two components in order. -/
def pairZeroizeImpl {A B : Type} (a : zeroize.Zeroize A) (b : zeroize.Zeroize B) (x : A × B) :
    Result (A × B) := do
  let y ← a.zeroize x.1
  let z ← b.zeroize x.2
  ok (y, z)

def Interp.faithful : Interp :=
  { Interp.model with
    arrayZeroize := @arrayZeroizeImpl
    vecZeroize := @vecZeroizeImpl
    pairZeroize := @pairZeroizeImpl }

/-! ### The general forms the fields had -/

/-- The general form of `SessionUnitSpqrT1.ZeroizeTotal` before it was restated. -/
def SpqrZeroizeUnscopedShape (I : Interp) : Prop :=
  ∀ {Z : Type} {N : Usize} (inst : zeroize.Zeroize Z) (a : Array Z N),
    ∃ r, I.arrayZeroize inst a = ok r

/-- The general form of `SessionUnitBraidT1.ArrayZeroizeTotal` before it was restated. -/
def ArrayZeroizeUnscopedShape (I : Interp) : Prop :=
  ∀ (N : Usize) (inst : zeroize.Zeroize U8) (a : Array U8 N),
    ∃ r, I.arrayZeroize (N := N) inst a = ok r

/-- The general form of the `Vec::zeroize` conjunct of `SessionUnitSpqrT1.VecRetainTotal` before
it was restated. -/
def VecZeroizeUnscopedShape (I : Interp) : Prop :=
  ∀ {T : Type} (inst : zeroize.Zeroize T) (v : alloc.vec.Vec T), ∃ r, I.vecZeroize inst v = ok r

/-- The general forms imply the restated fields: the restatement weakens the records. -/
theorem spqrZeroize_of_unscoped (I : Interp) (h : SpqrZeroizeUnscopedShape I) :
    SpqrZeroizeShape I := fun a => h _ a

theorem arrayZeroize_of_unscoped (I : Interp) (h : ArrayZeroizeUnscopedShape I) :
    ArrayZeroizeShape I := fun a => h _ _ a

theorem vecRetainAxiom_of_unscoped (I : Interp)
    (hc : ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T), ∃ r, I.vecCapacity A v = ok r)
    (h : VecZeroizeUnscopedShape I) : VecRetainAxiomShape I :=
  ⟨hc, fun v => h _ v, fun v => h _ v, fun v => h _ v⟩

/-- The statements with a premise: the operation returns at an instance whose `zeroize` returns on
every element.  The faithful interpretation satisfies them. -/
def ArrayZeroizeScopedShape (I : Interp) : Prop :=
  ∀ {Z : Type} {N : Usize} (inst : zeroize.Zeroize Z),
    (∀ x, ∃ y, inst.zeroize x = ok y) → ∀ a : Array Z N, ∃ r, I.arrayZeroize inst a = ok r

def VecZeroizeScopedShape (I : Interp) : Prop :=
  ∀ {Z : Type} (inst : zeroize.Zeroize Z),
    (∀ x, ∃ y, inst.zeroize x = ok y) → ∀ v : alloc.vec.Vec Z, ∃ r, I.vecZeroize inst v = ok r

/-- The blanket `Zeroize` impl (`*self = Default::default()`) returns, at the three scalar types the
code instantiates it at. -/
def BlanketZeroizeTotalShape (I : Interp) : Prop :=
  (∀ x : U8, ∃ y, I.blanketZeroize U8.Insts.ZeroizeDefaultIsZeroes x = ok y) ∧
  (∀ x : U32, ∃ y, I.blanketZeroize U32.Insts.ZeroizeDefaultIsZeroes x = ok y) ∧
  (∀ x : U64, ∃ y, I.blanketZeroize U64.Insts.ZeroizeDefaultIsZeroes x = ok y)

/-- What the real `Array::zeroize` does with a failing element. -/
def ArrayZeroizePropagatesFailure (I : Interp) : Prop :=
  ∀ {Z : Type} (inst : zeroize.Zeroize Z) (a : Array Z 1#usize) (x : Z),
    a.val = [x] → inst.zeroize x = fail Error.panic →
    I.arrayZeroize inst a = fail Error.panic

/-- What the real `Vec::zeroize` does with a failing element. -/
def VecZeroizePropagatesFailure (I : Interp) : Prop :=
  ∀ {Z : Type} (inst : zeroize.Zeroize Z) (v : alloc.vec.Vec Z) (x : Z),
    v.val = [x] → inst.zeroize x = fail Error.panic →
    I.vecZeroize inst v = fail Error.panic

/-- The general `Array::zeroize` form implies the scoped one. -/
theorem arrayZeroizeScoped_of_total (I : Interp) (h : SpqrZeroizeUnscopedShape I) :
    ArrayZeroizeScopedShape I := fun inst _ a => h inst a

/-! ### The clashes -/

/-- The general form of `ZeroizeTotal` cannot hold in an interpretation that propagates the
failure of a failing instance, which is what the real function does. -/
theorem zeroize_failure_propagation_conflicts (I : Interp) (h : SpqrZeroizeUnscopedShape I)
    (law : ArrayZeroizePropagatesFailure I) : False := by
  let inst : zeroize.Zeroize Unit := ⟨fun _ => fail Error.panic⟩
  let a : Array Unit 1#usize := Array.repeat 1#usize ()
  have ha : a.val = [()] := by simp [a]
  obtain ⟨r, hr⟩ := h inst a
  have := law inst a () ha rfl
  rw [hr] at this
  cases this

/-- The same for the general form of the Braid's `ArrayZeroizeTotal`, with a failing `Zeroize U8`. -/
theorem braid_zeroize_failure_propagation_conflicts (I : Interp) (h : ArrayZeroizeUnscopedShape I)
    (law : ArrayZeroizePropagatesFailure I) : False := by
  let inst : zeroize.Zeroize U8 := ⟨fun _ => fail Error.panic⟩
  let a : Array U8 1#usize := Array.repeat 1#usize 0#u8
  have ha : a.val = [0#u8] := by simp [a]
  obtain ⟨r, hr⟩ := h 1#usize inst a
  have := law inst a 0#u8 ha rfl
  rw [hr] at this
  cases this

/-- The same for the general form of the `Vec::zeroize` conjunct. -/
theorem vec_zeroize_failure_propagation_conflicts (I : Interp) (h : VecZeroizeUnscopedShape I)
    (law : VecZeroizePropagatesFailure I) : False := by
  let inst : zeroize.Zeroize Unit := ⟨fun _ => fail Error.panic⟩
  let v : alloc.vec.Vec Unit := ⟨[()], by scalar_tac⟩
  obtain ⟨r, hr⟩ := h inst v
  have := law inst v () rfl rfl
  rw [hr] at this
  cases this

/-! ### The faithful interpretation -/

theorem faithful_arrayZeroizeScoped : ArrayZeroizeScopedShape Interp.faithful := by
  intro Z N inst htot a
  obtain ⟨l, hl⟩ := mapZ_total inst htot a.val
  refine ⟨⟨l, by rw [mapZ_length inst _ _ hl]; exact a.property⟩, ?_⟩
  show arrayZeroizeImpl inst a = _
  unfold arrayZeroizeImpl
  split
  · rename_i l' h'
    rw [hl] at h'
    cases h'
    rfl
  · rename_i e h'; rw [hl] at h'; cases h'
  · rename_i h'; rw [hl] at h'; cases h'

theorem faithful_vecZeroizeScoped : VecZeroizeScopedShape Interp.faithful := by
  intro Z inst htot v
  obtain ⟨l, hl⟩ := mapZ_total inst htot v.val
  refine ⟨alloc.vec.Vec.new Z, ?_⟩
  show vecZeroizeImpl inst v = _
  unfold vecZeroizeImpl
  rw [hl]

theorem faithful_propagates : ArrayZeroizePropagatesFailure Interp.faithful := by
  intro Z inst a x ha hf
  show arrayZeroizeImpl inst a = _
  unfold arrayZeroizeImpl
  split
  · rename_i l h'
    rw [ha] at h'
    simp [mapZ, hf] at h'
  · rename_i e h'
    rw [ha] at h'
    simp [mapZ, hf] at h'
    rw [h']
  · rename_i h'
    rw [ha] at h'
    simp [mapZ, hf] at h'

theorem faithful_vec_propagates : VecZeroizePropagatesFailure Interp.faithful := by
  intro Z inst v x hv hf
  show vecZeroizeImpl inst v = _
  unfold vecZeroizeImpl
  rw [hv]
  simp [mapZ, hf]

theorem faithful_blanketTotal : BlanketZeroizeTotalShape Interp.faithful :=
  ⟨fun x => ⟨x, rfl⟩, fun x => ⟨x, rfl⟩, fun x => ⟨x, rfl⟩⟩

/-- The general form does not hold in the faithful interpretation. -/
theorem faithful_refutes_unscoped : ¬ SpqrZeroizeUnscopedShape Interp.faithful := fun h =>
  zeroize_failure_propagation_conflicts _ h faithful_propagates

theorem faithful_array_u8_total {N : Usize} (a : Array U8 N) :
    ∃ r, Interp.faithful.arrayZeroize (Interp.faithful.blanket U8.Insts.ZeroizeDefaultIsZeroes) a
      = ok r :=
  faithful_arrayZeroizeScoped _ (fun x => ⟨x, rfl⟩) a

theorem faithful_SpqrZeroize : SpqrZeroizeShape Interp.faithful :=
  fun a => faithful_array_u8_total a

theorem faithful_ArrayZeroize : ArrayZeroizeShape Interp.faithful :=
  fun a => faithful_array_u8_total a

theorem faithful_chainZeroize_total (c : tacenta_spqr.Chain) :
    ∃ r, Interp.faithful.chainZeroize c = ok r := by
  obtain ⟨r, hr⟩ := faithful_array_u8_total c.ck
  exact ⟨_, by unfold Interp.chainZeroize; rw [hr]; rfl⟩

theorem faithful_chainsZeroize_total (c : tacenta_spqr.Chains) :
    ∃ r, Interp.faithful.chainsZeroize c = ok r := by
  rcases c with ⟨send, receive⟩
  unfold Interp.chainsZeroize
  have hA : ∀ {T : Type} (o : Option T),
      Interp.faithful.optionAsMut o = ok (o, fun x => x) := fun _ => rfl
  simp only [hA, bind_tc_ok]
  cases send with
  | none =>
    cases receive with
    | none => exact ⟨_, rfl⟩
    | some ch =>
      obtain ⟨r, hr⟩ := faithful_chainZeroize_total ch
      exact ⟨_, by simp [hr]; rfl⟩
  | some ch =>
    obtain ⟨r, hr⟩ := faithful_chainZeroize_total ch
    cases receive with
    | none => exact ⟨_, by simp [hr]; rfl⟩
    | some ch' =>
      obtain ⟨r', hr'⟩ := faithful_chainZeroize_total ch'
      exact ⟨_, by simp [hr, hr']; rfl⟩

theorem faithful_VecRetainAxiom : VecRetainAxiomShape Interp.faithful := by
  have hB32 : ∀ x : U32, Interp.faithful.blanketZeroize U32.Insts.ZeroizeDefaultIsZeroes x = ok x :=
    fun _ => rfl
  have hB64 : ∀ x : U64, Interp.faithful.blanketZeroize U64.Insts.ZeroizeDefaultIsZeroes x = ok x :=
    fun _ => rfl
  refine ⟨model_VecRetainAxiom.1, ?_, ?_, ?_⟩
  · refine faithful_vecZeroizeScoped _ ?_
    rintro ⟨e, c⟩
    obtain ⟨r, hr⟩ := faithful_chainsZeroize_total c
    refine ⟨(e, r), ?_⟩
    simp only [Interp.chainTableInst, Interp.pairInst, Interp.blanket]
    show pairZeroizeImpl _ _ (e, c) = _
    simp only [pairZeroizeImpl, hB64, hr, bind_tc_ok]
  · refine faithful_vecZeroizeScoped _ ?_
    intro x
    obtain ⟨r, hr⟩ := faithful_array_u8_total x.key
    refine ⟨{ x with key := r }, ?_⟩
    simp only [Interp.skippedInst, hr, bind_tc_ok]
  · refine faithful_vecZeroizeScoped _ ?_
    intro x
    obtain ⟨r1, hr1⟩ := faithful_array_u8_total x.dh
    obtain ⟨r2, hr2⟩ := faithful_array_u8_total x.key
    refine ⟨{ dh := r1, n := x.n, stored_at := x.stored_at, key := r2 }, ?_⟩
    simp only [Interp.skippedKeyInst, hr1, hr2, hB32, bind_tc_ok]

def faithful_ZeroizingModel (Z : Type) : ZeroizingModelShape Interp.faithful Z where
  contents z := z
  new _ _ := by simp [Interp.faithful, Interp.model]
  deref _ _ := by simp [Interp.faithful, Interp.model]
  deref_mut _ _ := by simp [Interp.faithful, Interp.model]

theorem faithful_Faithful : FaithfulShape Interp.faithful :=
  { pop_nil := model_Faithful.pop_nil, pop_snoc := model_Faithful.pop_snoc,
    truncate := model_Faithful.truncate, divCeil := model_Faithful.divCeil,
    asMut := model_Faithful.asMut, capacity := model_Faithful.capacity }

theorem faithful_StdLaws : StdLaws Interp.faithful :=
  stdLaws_of_faithful Interp.faithful faithful_Faithful (fun x => ⟨x, rfl⟩)

/-- Every axiom-level shape of the joint model holds in the faithful interpretation, the three
restated fields among them, together with the propagation of a failing element by `Array::zeroize`
and `Vec::zeroize`. -/
theorem faithful_satisfies_all_axiom_shapes :
    DhCodecShape Interp.faithful ∧
    DhIdentityShape Interp.faithful ∧
    DhAgreeShape Interp.faithful ∧
    KemEncapsulateShape Interp.faithful ∧
    KemDecapsulateShape Interp.faithful ∧
    XeddsaVerifyShape Interp.faithful ∧
    AeadOpenShape Interp.faithful ∧
    AeadSealBoundedShape Interp.faithful ∧
    MessageKeyMaterialRoundTripShape Interp.faithful ∧
    VecPopShape Interp.faithful ∧
    HkdfShape Interp.faithful ∧
    HmacShape Interp.faithful ∧
    ZeroizingTotalShape Interp.faithful ∧
    SpqrZeroizeShape Interp.faithful ∧
    VecRetainAxiomShape Interp.faithful ∧
    OptionCloneShape Interp.faithful ∧
    Ct1LenShape Interp.faithful ∧
    Ct2LenShape Interp.faithful ∧
    HeaderLenShape Interp.faithful ∧
    EkVectorLenShape Interp.faithful ∧
    KeyPairEkVectorShape Interp.faithful ∧
    KeyPairHeaderShape Interp.faithful ∧
    KeyPairDecapsulateShape Interp.faithful ∧
    KeyPairCloneShape Interp.faithful ∧
    EncapsStateCloneShape Interp.faithful ∧
    ValidateEkShape Interp.faithful ∧
    KeyPairGenerateShape Interp.faithful ∧
    Encapsulate1Shape Interp.faithful ∧
    Encapsulate2Shape Interp.faithful ∧
    ZeroizingArrayRoundTripShape Interp.faithful ∧
    ArrayZeroizeShape Interp.faithful ∧
    RangeFullIndexShape Interp.faithful ∧
    Nonempty (ZeroizingModelShape Interp.faithful SessionZ) ∧
    Nonempty (ZeroizingModelShape Interp.faithful DerivedZ) ∧
    DivCeilValueShape Interp.faithful ∧ FaithfulShape Interp.faithful ∧ StdLaws Interp.faithful ∧
    ArrayZeroizeScopedShape Interp.faithful ∧ VecZeroizeScopedShape Interp.faithful ∧
    BlanketZeroizeTotalShape Interp.faithful ∧
    ArrayZeroizePropagatesFailure Interp.faithful ∧ VecZeroizePropagatesFailure Interp.faithful :=
  ⟨model_DhCodec, model_DhIdentity, model_DhAgree, model_KemEncapsulate, model_KemDecapsulate,
    model_XeddsaVerify, model_AeadOpen, model_AeadSealBounded, model_MessageKeyMaterialRoundTrip,
    model_VecPop, model_Hkdf, model_Hmac, model_ZeroizingTotal, faithful_SpqrZeroize,
    faithful_VecRetainAxiom, model_OptionClone, model_Ct1Len, model_Ct2Len, model_HeaderLen,
    model_EkVectorLen, model_KeyPairEkVector, model_KeyPairHeader, model_KeyPairDecapsulate,
    model_KeyPairClone, model_EncapsStateClone, model_ValidateEk, model_KeyPairGenerate,
    model_Encapsulate1, model_Encapsulate2, model_ZeroizingArrayRoundTrip, faithful_ArrayZeroize,
    model_RangeFullIndex, ⟨faithful_ZeroizingModel SessionZ⟩, ⟨faithful_ZeroizingModel DerivedZ⟩,
    model_DivCeilValue, faithful_Faithful, faithful_StdLaws, faithful_arrayZeroizeScoped,
    faithful_vecZeroizeScoped, faithful_blanketTotal, faithful_propagates, faithful_vec_propagates⟩

end ScopedZeroize


end Tacenta.UnitSatisfiabilityZeroizeScope

/-! ## Axiom pins

The axiom bases of the results above, held by the build.  A list names the constants that occur in
the statement of a result, not assumptions its proof makes. -/

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.zeroize_failure_propagation_conflicts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.zeroize_failure_propagation_conflicts

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.braid_zeroize_failure_propagation_conflicts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.braid_zeroize_failure_propagation_conflicts

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.vec_zeroize_failure_propagation_conflicts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.vec_zeroize_failure_propagation_conflicts

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.faithful_propagates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.faithful_propagates

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.faithful_vec_propagates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.faithful_vec_propagates

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.faithful_refutes_unscoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.faithful_refutes_unscoped

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.faithful_satisfies_all_axiom_shapes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.faithful_satisfies_all_axiom_shapes

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.spqrZeroize_of_unscoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.spqrZeroize_of_unscoped

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.arrayZeroize_of_unscoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.arrayZeroize_of_unscoped

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.vecRetainAxiom_of_unscoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.vecRetainAxiom_of_unscoped

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.arrayZeroizeScoped_of_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.arrayZeroizeScoped_of_total

/-! ## Statement pins

The three contract fields as now stated, printed in full, so that a change to the instance, the width
or the conjuncts fails the build here. -/

/--
info: def Tacenta.SessionUnitSpqrT1.ZeroizeTotal : Prop :=
∀ (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  ∃ r,
    tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize
        (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U8.Insts.ZeroizeDefaultIsZeroes) a =
      Aeneas.Std.Result.ok r
-/
#guard_msgs in
#print Tacenta.SessionUnitSpqrT1.ZeroizeTotal

/--
info: def Tacenta.SessionUnitSpqrT1.VecRetainTotal : Prop :=
(∀ {T : Type} (A : Type) (v : Aeneas.Std.alloc.vec.Vec T),
    ∃ r, tacenta_session_unit.alloc.vec.Vec.capacity A v = Aeneas.Std.Result.ok r) ∧
  ((∀ (v : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.U64 × tacenta_session_unit.tacenta_spqr.Chains)),
        ∃ r,
          tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
              (tacenta_session_unit.Pair.Insts.ZeroizeZeroize
                (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U64.Insts.ZeroizeDefaultIsZeroes)
                tacenta_session_unit.tacenta_spqr.Chains.Insts.ZeroizeZeroize)
              v =
            Aeneas.Std.Result.ok r) ∧
      (∀ (v : Aeneas.Std.alloc.vec.Vec tacenta_session_unit.tacenta_spqr.Skipped),
          ∃ r,
            tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
                tacenta_session_unit.tacenta_spqr.Skipped.Insts.ZeroizeZeroize v =
              Aeneas.Std.Result.ok r) ∧
        ∀ (v : Aeneas.Std.alloc.vec.Vec tacenta_session_unit.tacenta_ratchet.SkippedKey),
          ∃ r,
            tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
                tacenta_session_unit.tacenta_ratchet.SkippedKey.Insts.ZeroizeZeroize v =
              Aeneas.Std.Result.ok r) ∧
    Tacenta.SessionUnitSpqrT1.SetChainsLoopTotal ∧
      Tacenta.SessionUnitSpqrT1.ClearChainsLoop0Total ∧ Tacenta.SessionUnitSpqrT1.ClearSkippedLoopTotal
-/
#guard_msgs in
#print Tacenta.SessionUnitSpqrT1.VecRetainTotal

/--
info: def Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal : Prop :=
∀ (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  ∃ r,
    tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize
        (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U8.Insts.ZeroizeDefaultIsZeroes) a =
      Aeneas.Std.Result.ok r
-/
#guard_msgs in
#print Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal
