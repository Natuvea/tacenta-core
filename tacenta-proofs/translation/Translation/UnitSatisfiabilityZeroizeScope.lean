import Translation.UnitSatisfiabilityJoint

/-!
# Three fields that quantify over every `Zeroize` record

`SessionUnitSpqrT1.ZeroizeTotal`, `SessionUnitBraidT1.ArrayZeroizeTotal` and the `Vec::zeroize`
conjunct of `SessionUnitSpqrT1.VecRetainTotal` say that `Array::zeroize` and `Vec::zeroize`
return for **every** instance record `inst : Zeroize Z`.  The real functions call `inst.zeroize`
on each element, and a `Zeroize` record whose field fails (a panicking implementation) is a legal
Lean term.  The Lean constants are opaque, so nothing in Lean refutes the three fields, and the
joint model of `UnitSatisfiabilityJoint.lean` satisfies them: they are consistent.  The point is
what the crate does: the real functions satisfy them only for instances whose `zeroize` returns, so
the fields are stronger than the code supports.  `Zeroizing::new` and `deref` never call
`inst.zeroize`, so the `Zeroizing` fields do not have this problem.

`zeroize_failure_propagation_conflicts` proves the clash: no interpretation can satisfy
`ZeroizeTotal` and also have `Array::zeroize` propagate the failure of a failing instance, which
is what the real function does.  The scoped statements below are the ones the real functions
satisfy.  The second model, `Interp.faithful`, implements `Array::zeroize` and `Vec::zeroize` as
the crate does (zeroize each element in order, fail if an element fails; `Vec::zeroize` leaves an
empty vector), and satisfies the scoped statements together with every other shape.

This module changes no record and no theorem.  It is the evidence for the recommendation in
`LIMITATIONS.md`, and no proof module imports it; `AxiomAuditSessionUnit.lean` imports it so that
the environment audit covers it.
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

def Interp.faithful : Interp :=
  { Interp.model with arrayZeroize := @arrayZeroizeImpl, vecZeroize := @vecZeroizeImpl }

/-- Proposed replacement for `SessionUnitSpqrT1.ZeroizeTotal` and
`SessionUnitBraidT1.ArrayZeroizeTotal`. -/
def ArrayZeroizeScopedShape (I : Interp) : Prop :=
  ∀ {Z : Type} {N : Usize} (inst : zeroize.Zeroize Z),
    (∀ x, ∃ y, inst.zeroize x = ok y) → ∀ a : Array Z N, ∃ r, I.arrayZeroize inst a = ok r

/-- Proposed replacement for the `Vec::zeroize` conjunct of
`SessionUnitSpqrT1.VecRetainTotal`. -/
def VecZeroizeScopedShape (I : Interp) : Prop :=
  ∀ {Z : Type} (inst : zeroize.Zeroize Z),
    (∀ x, ∃ y, inst.zeroize x = ok y) → ∀ v : alloc.vec.Vec Z, ∃ r, I.vecZeroize inst v = ok r

/-- The one new field the scoped statements need: the blanket `Zeroize` impl
(`*self = Default::default()`) returns, at the three scalar types the code
instantiates it at. -/
def BlanketZeroizeTotalShape (I : Interp) : Prop :=
  (∀ x : U8, ∃ y, I.blanketZeroize U8.Insts.ZeroizeDefaultIsZeroes x = ok y) ∧
  (∀ x : U32, ∃ y, I.blanketZeroize U32.Insts.ZeroizeDefaultIsZeroes x = ok y) ∧
  (∀ x : U64, ∃ y, I.blanketZeroize U64.Insts.ZeroizeDefaultIsZeroes x = ok y)

/-- What the real `Array::zeroize` does with a failing element. -/
def ArrayZeroizePropagatesFailure (I : Interp) : Prop :=
  ∀ {Z : Type} (inst : zeroize.Zeroize Z) (a : Array Z 1#usize) (x : Z),
    a.val = [x] → inst.zeroize x = fail Error.panic →
    I.arrayZeroize inst a = fail Error.panic

/-- The unscoped field implies the scoped one. -/
theorem arrayZeroizeScoped_of_total (I : Interp) (h : SpqrZeroizeShape I) :
    ArrayZeroizeScopedShape I := fun inst _ a => h inst a


/-- The minimal replacement, stated at the one instance the translated code
passes to `Array::zeroize`.  No quantification over instance records, no new
premise beyond the operation itself. -/
def ArrayZeroizeBlanketU8Shape (I : Interp) : Prop :=
  ∀ (N : Usize) (a : Array U8 N),
    ∃ r, I.arrayZeroize (N := N) (I.blanket U8.Insts.ZeroizeDefaultIsZeroes) a = ok r

theorem ArrayZeroizeBlanketU8_is :
    (∀ (N : Usize) (a : Array U8 N),
      ∃ r, Array.Insts.ZeroizeZeroize.zeroize (N := N)
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a = ok r) ↔
      ArrayZeroizeBlanketU8Shape Interp.real := Iff.rfl

theorem ArrayZeroizeScoped_is :
    (∀ {Z : Type} {N : Usize} (inst : zeroize.Zeroize Z),
      (∀ x, ∃ y, inst.zeroize x = ok y) →
      ∀ a : Array Z N, ∃ r, Array.Insts.ZeroizeZeroize.zeroize inst a = ok r) ↔
      ArrayZeroizeScopedShape Interp.real := Iff.rfl

theorem VecZeroizeScoped_is :
    (∀ {Z : Type} (inst : zeroize.Zeroize Z),
      (∀ x, ∃ y, inst.zeroize x = ok y) →
      ∀ v : alloc.vec.Vec Z, ∃ r, alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst v = ok r) ↔
      VecZeroizeScopedShape Interp.real := Iff.rfl

/-- The unscoped field implies the minimal one. -/
theorem arrayZeroizeBlanketU8_of_total (I : Interp) (h : ArrayZeroizeShape I) :
    ArrayZeroizeBlanketU8Shape I := fun N a => h N (I.blanket U8.Insts.ZeroizeDefaultIsZeroes) a

/-- The clash: `ZeroizeTotal` cannot hold in an interpretation that propagates
the failure of a failing instance, which is what the real function does. -/
theorem zeroize_failure_propagation_conflicts (I : Interp) (h : SpqrZeroizeShape I)
    (law : ArrayZeroizePropagatesFailure I) : False := by
  let inst : zeroize.Zeroize Unit := ⟨fun _ => fail Error.panic⟩
  let a : Array Unit 1#usize := Array.repeat 1#usize ()
  have ha : a.val = [()] := by simp [a]
  obtain ⟨r, hr⟩ := h inst a
  have := law inst a () ha rfl
  rw [hr] at this
  cases this

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

theorem faithful_blanketTotal : BlanketZeroizeTotalShape Interp.faithful :=
  ⟨fun x => ⟨x, rfl⟩, fun x => ⟨x, rfl⟩, fun x => ⟨x, rfl⟩⟩

/-- Proposed replacement for `SessionUnitSpqrT1.ZeroizeTotal` and
`SessionUnitBraidT1.ArrayZeroizeTotal`, over the real constants. -/
def ArrayZeroizeU8Total : Prop :=
  ∀ (N : Usize) (a : Array U8 N),
    ∃ r, Array.Insts.ZeroizeZeroize.zeroize (N := N)
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a = ok r

theorem ArrayZeroizeU8Total_is :
    ArrayZeroizeU8Total ↔ ArrayZeroizeBlanketU8Shape Interp.real := Iff.rfl

theorem ArrayZeroizeU8Total_of_spqr (h : Tacenta.SessionUnitSpqrT1.ZeroizeTotal) :
    ArrayZeroizeU8Total := fun _ a => h (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a

theorem ArrayZeroizeU8Total_of_braid (h : Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal) :
    ArrayZeroizeU8Total := fun N a => h N (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a

/-- One of the two instances at which the proofs apply the `Vec::zeroize` conjunct of
`SessionUnitSpqrT1.VecRetainTotal`: the chain table, `Vec<(u64, Chains)>`.  It mentions the
translated `Chains::zeroize`, whose totality is then a fact to prove about the translation
rather than a premise about every instance record.  A replacement for the conjunct needs this
statement and `VecZeroizeSkippedTotal`: the conjunct is also applied to the skipped-key store,
and a replacement with the chain table alone makes `skip_message_keys_no_panic` stop building
(measured, see `LIMITATIONS.md`). -/
def VecZeroizeChainsTotal : Prop :=
  ∀ v : alloc.vec.Vec (U64 × tacenta_spqr.Chains),
    ∃ r, alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
      (Pair.Insts.ZeroizeZeroize
        (zeroize.Zeroize.Blanket U64.Insts.ZeroizeDefaultIsZeroes)
        tacenta_spqr.Chains.Insts.ZeroizeZeroize) v = ok r

theorem VecZeroizeChainsTotal_of_vecRetain (h : Tacenta.SessionUnitSpqrT1.VecRetainTotal) :
    VecZeroizeChainsTotal := fun v => h.2.1 _ v

/-- The other instance: the sparse ratchet's skipped-key store, `Vec<Skipped>`.  It mentions the
translated `Skipped::zeroize`, which wipes the key with `Array::zeroize` at `Blanket U8`. -/
def VecZeroizeSkippedTotal : Prop :=
  ∀ v : alloc.vec.Vec tacenta_spqr.Skipped,
    ∃ r, alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
      tacenta_spqr.Skipped.Insts.ZeroizeZeroize v = ok r

theorem VecZeroizeSkippedTotal_of_vecRetain (h : Tacenta.SessionUnitSpqrT1.VecRetainTotal) :
    VecZeroizeSkippedTotal := fun v => h.2.1 _ v

theorem model_ArrayZeroizeBlanketU8 : ArrayZeroizeBlanketU8Shape Interp.model :=
  fun _ _ => ⟨_, rfl⟩

theorem faithful_ArrayZeroizeBlanketU8 : ArrayZeroizeBlanketU8Shape Interp.faithful := by
  intro N a
  exact faithful_arrayZeroizeScoped _ (fun x => ⟨x, rfl⟩) a

/-- The unscoped field does not hold in the faithful interpretation. -/
theorem faithful_refutes_unscoped : ¬ SpqrZeroizeShape Interp.faithful := fun h =>
  zeroize_failure_propagation_conflicts _ h faithful_propagates


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

/-- Everything except the three over-strong fields holds in the faithful
interpretation too; the scoped statements take their place. -/
theorem faithful_satisfies_rest :
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
    RangeFullIndexShape Interp.faithful ∧
    (∀ {T : Type} (A : Type) (v : alloc.vec.Vec T), ∃ r, Interp.faithful.vecCapacity A v = ok r) ∧
    ArrayZeroizeScopedShape Interp.faithful ∧ VecZeroizeScopedShape Interp.faithful ∧
    BlanketZeroizeTotalShape Interp.faithful ∧ ArrayZeroizeBlanketU8Shape Interp.faithful ∧
    ArrayZeroizePropagatesFailure Interp.faithful ∧
    Nonempty (ZeroizingModelShape Interp.faithful SessionZ) ∧
    Nonempty (ZeroizingModelShape Interp.faithful DerivedZ) ∧
    DivCeilValueShape Interp.faithful ∧ FaithfulShape Interp.faithful ∧ StdLaws Interp.faithful :=
  ⟨model_DhCodec, model_DhIdentity, model_DhAgree, model_KemEncapsulate, model_KemDecapsulate, model_XeddsaVerify, model_AeadOpen, model_AeadSealBounded, model_MessageKeyMaterialRoundTrip, model_VecPop, model_Hkdf, model_Hmac, model_ZeroizingTotal, model_OptionClone, model_Ct1Len, model_Ct2Len, model_HeaderLen, model_EkVectorLen, model_KeyPairEkVector, model_KeyPairHeader, model_KeyPairDecapsulate, model_KeyPairClone, model_EncapsStateClone, model_ValidateEk, model_KeyPairGenerate, model_Encapsulate1, model_Encapsulate2, model_ZeroizingArrayRoundTrip, model_RangeFullIndex,
    model_VecRetainAxiom.1, faithful_arrayZeroizeScoped, faithful_vecZeroizeScoped,
    faithful_blanketTotal, faithful_ArrayZeroizeBlanketU8, faithful_propagates,
    ⟨faithful_ZeroizingModel SessionZ⟩, ⟨faithful_ZeroizingModel DerivedZ⟩, model_DivCeilValue, faithful_Faithful, faithful_StdLaws⟩

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
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.faithful_propagates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.faithful_propagates

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.faithful_refutes_unscoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.faithful_refutes_unscoped

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.faithful_satisfies_rest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.faithful_satisfies_rest

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.ArrayZeroizeU8Total_of_spqr' depends on axioms: [propext,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.ArrayZeroizeU8Total_of_spqr

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.ArrayZeroizeU8Total_of_braid' depends on axioms: [propext,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.ArrayZeroizeU8Total_of_braid

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.VecZeroizeChainsTotal_of_vecRetain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.VecZeroizeChainsTotal_of_vecRetain

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.arrayZeroizeScoped_of_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.arrayZeroizeScoped_of_total

/--
info: 'Tacenta.UnitSatisfiabilityZeroizeScope.VecZeroizeSkippedTotal_of_vecRetain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityZeroizeScope.VecZeroizeSkippedTotal_of_vecRetain
