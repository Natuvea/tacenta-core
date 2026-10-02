import Translation.T3
import Translation.RatchetCodecT1
import Translation.SatisfiabilitySpqrLaws

/-!
# The classical ratchet's removal helper, from laws about opaque constants

`T1.RemoveSkippedAtTotal` is a hypothesis of the leaf classical ratchet's refinement and
panic-freedom theorems. It is a statement about `tacenta_ratchet.remove_skipped_at`, a function the
translation defines (a swap loop, a wipe of the removed entry, `Vec::pop`), not about an opaque
constant. The witness `Satisfiability.lean` keeps for it is bridged by `Iff.rfl` to a shape applied
to the defined function; that shape is satisfiable for any function and says nothing about the
body. This module proves the hypothesis from three laws about the opaque constants the body
reaches (`ratchetRemoveSkippedAtTotal`):

* `LawPop` (`Vec::pop` of a non-empty vector returns the vector without its last element), the law
  of `SatisfiabilitySpqrLaws.lean` restated for this crate's own `pop` constant;
* `LawBlanketU32` (the blanket `Zeroize` implementation returns at `u32`);
* `ArrZU8` (the array wipe returns at the byte instance, at every length).

Each law is tied to the statement about the real constant by `Iff.rfl` (`LawBlanketU32_is`,
`ArrZU8_is`) and shown satisfiable by shape (`blanket_satisfiable`, `arrZU8_satisfiable`). They are
on constants that no other hypothesis of the classical theorems mentions, so adding them to a model
of the others costs nothing, and the same module ties the hypothesis `RatchetCodecT1.ZeroizingVecTotal`
to a shape and shows it satisfiable (it had no witness).

The laws are assumptions about standard-library and `zeroize` operations, tested against the real
functions only by reading. Nothing here shows that the real functions satisfy them. The proof of the
specification of `remove_skipped_at` is the session unit's (`UnitSatisfiabilityRatchet.lean`) under
the leaf's constants, and is generic in the platform width.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open tacenta_ratchet

noncomputable section

namespace Tacenta.SatisfiabilityRatchetLaws

open Tacenta.SatisfiabilitySpqrLaws (rotLoop rotLoop_spec)

/-- **`LawPop`.**  `Vec::pop` on a non-empty vector returns the vector without its last element.
This is all the removal helper needs of `pop`; the real operation also returns the element and
handles the empty vector. The classical crate's `pop` is a different constant from the sparse
crate's (each translation declares its own), so the law is restated here. -/
def LawPop : Prop :=
  ∀ (T : Type) (v : alloc.vec.Vec T), v.val ≠ [] →
    ∃ o w, alloc.vec.Vec.pop Global v = ok (o, w) ∧ w.val = v.val.dropLast


/-- The array wipe returns at the byte-array instance, the one instance the ratchet's removal
helper uses. Scoped to that instance (the leaf has no `ZeroizeTotal` hypothesis for this
constant, so the law is stated here at the width-polymorphic byte instance). -/
def ArrZU8 : Prop :=
  ∀ {N : Usize} (a : Array U8 N),
    ∃ r, Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a = ok r

theorem ratchet_loop_eq : @tacenta_ratchet.remove_skipped_at_loop = @rotLoop tacenta_ratchet.SkippedKey := rfl

/-- **`LawBlanketU32`.**  The `Zeroize` blanket implementation returns at `u32`. No theorem
hypothesis states it. -/
def LawBlanketU32 : Prop :=
  ∀ x : U32, ∃ r, zeroize.Zeroize.Blanket.zeroize U32.Insts.ZeroizeDefaultIsZeroes x = ok r


theorem skippedKey_zeroize_spec (hZ : ArrZU8) (hB : LawBlanketU32)
    (s : tacenta_ratchet.SkippedKey) :
    tacenta_ratchet.SkippedKey.Insts.ZeroizeZeroize.zeroize s ⦃ fun _ => True ⦄ := by
  unfold tacenta_ratchet.SkippedKey.Insts.ZeroizeZeroize.zeroize
  obtain ⟨r1, h1⟩ := hZ s.dh
  obtain ⟨r2, h2⟩ := hB s.n
  obtain ⟨r3, h3⟩ := hB s.stored_at
  obtain ⟨r4, h4⟩ := hZ s.key
  simp [h1, h2, h3, h4]


/-- The classical ratchet's `remove_skipped_at`, at an in-range index. -/
theorem ratchet_remove_skipped_at_spec (hZ : ArrZU8)
    (hB : LawBlanketU32) (hP : LawPop)
    (v : alloc.vec.Vec tacenta_ratchet.SkippedKey) (i : Usize) (hi : i.val < v.val.length) :
    tacenta_ratchet.remove_skipped_at v i ⦃ fun r =>
      r.1 = (v.val[i.val]'hi).key ∧ r.2.val = v.val.eraseIdx i.val ⦄ := by
  unfold tacenta_ratchet.remove_skipped_at
  rw [ratchet_loop_eq]
  step with rotLoop_spec v i hi as ⟨v1, i1, hv1, hi1⟩
  have hL : (v.val.eraseIdx i.val).length = v.val.length - 1 := by
    simp [List.length_eraseIdx, hi]
  have hlen1 : v1.val.length = v.val.length := by
    rw [hv1]; simp; omega
  have hb : i1.val < v1.val.length := by omega
  have hget : v1.val[i1.val]'hb = v.val[i.val]'hi := by
    simp only [hv1]
    rw [List.getElem_append_right (by omega)]
    simp [hi1, hL]
  step with alloc.vec.Vec.index_usize_spec v1 i1 hb as ⟨x, hx⟩
  step with alloc.vec.Vec.index_mut_usize_spec v1 i1 hb as ⟨x', back, hx', hback⟩
  step with skippedKey_zeroize_spec hZ hB as ⟨s2⟩
  have hne : (back s2).val ≠ [] := by
    intro h
    have h0 : (back s2).val.length = 0 := by rw [h]; rfl
    rw [hback, alloc.vec.Vec.set_val_eq, List.length_set] at h0
    omega
  obtain ⟨o, w, hw1, hw2⟩ := hP _ (back s2) hne
  rw [hw1]
  simp only [bind_tc_ok]
  refine ⟨by rw [hx, hget], ?_⟩
  rw [hw2, hback]
  simp only [alloc.vec.Vec.set_val_eq, hv1]
  have : i1.val = (v.val.eraseIdx i.val).length := by rw [hi1, hL]
  rw [this, List.set_append_right _ _ (by omega)]
  simp



/-- `T1.RemoveSkippedAtTotal`, from the pop law, the array zeroize law and the `u32`
blanket zeroize law. -/
theorem ratchetRemoveSkippedAtTotal (hZ : ArrZU8)
    (hB : LawBlanketU32) (hP : LawPop) : Tacenta.T1.RemoveSkippedAtTotal := by
  intro A v i hi
  obtain ⟨r, hr, h1, h2⟩ := Std.WP.spec_imp_exists (ratchet_remove_skipped_at_spec hZ hB hP v i hi)
  exact ⟨r, hr, h1, h2⟩




/-! ## The laws the classical removal helper needs are satisfiable -/

abbrev PopFn := {T : Type} → Type → alloc.vec.Vec T → Result (Option T × alloc.vec.Vec T)

def PopShape (f : PopFn) : Prop :=
  ∀ (T : Type) (v : alloc.vec.Vec T), v.val ≠ [] →
    ∃ o w, f Global v = ok (o, w) ∧ w.val = v.val.dropLast

theorem LawPop_is : LawPop ↔ PopShape @alloc.vec.Vec.pop := Iff.rfl

def popWitness : PopFn := fun {_T} _ v =>
  ok (v.val.getLast?, ⟨v.val.dropLast, by have := v.property; rw [List.length_dropLast]; omega⟩)

theorem pop_satisfiable : ∃ f : PopFn, PopShape f :=
  ⟨@popWitness, fun _ _ _ => ⟨_, _, rfl, rfl⟩⟩

abbrev BlanketFn := {Z : Type} → zeroize.DefaultIsZeroes Z → Z → Result Z

def BlanketU32Shape (f : BlanketFn) : Prop :=
  ∀ x : U32, ∃ r, f U32.Insts.ZeroizeDefaultIsZeroes x = ok r

theorem LawBlanketU32_is :
    LawBlanketU32 ↔ BlanketU32Shape @zeroize.Zeroize.Blanket.zeroize := Iff.rfl

theorem blanket_satisfiable : ∃ f : BlanketFn, BlanketU32Shape f :=
  ⟨fun _ x => ok x, fun x => ⟨x, rfl⟩⟩

abbrev ArrayZeroizeFn :=
  {Z : Type} → {N : Usize} → zeroize.Zeroize Z → Std.Array Z N → Result (Std.Array Z N)

/-- `ArrZU8` over an arbitrary function: the byte-instance wipe returns. -/
def ArrZU8Shape (f : ArrayZeroizeFn) : Prop :=
  ∀ {N : Usize} (a : Std.Array U8 N),
    ∃ r, f (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a = ok r

theorem ArrZU8_is : ArrZU8 ↔ ArrZU8Shape @Array.Insts.ZeroizeZeroize.zeroize := Iff.rfl

theorem arrZU8_satisfiable : ∃ f : ArrayZeroizeFn, ArrZU8Shape f :=
  ⟨fun _ a => ok a, fun a => ⟨a, rfl⟩⟩

/-- `RatchetCodecT1.ZeroizingVecTotal`. -/
abbrev ZNewFn (W : Type → Type) := {Z : Type} → zeroize.Zeroize Z → Z → Result (W Z)

def ZeroizingVecShape {W : Type → Type} (new : ZNewFn W) : Prop :=
  ∀ (inst : zeroize.Zeroize (alloc.vec.Vec U8)) (v : alloc.vec.Vec U8), ∃ z, new inst v = ok z

theorem RatchetCodec_ZeroizingVecTotal_is :
    Tacenta.RatchetCodecT1.ZeroizingVecTotal ↔
      ZeroizingVecShape (W := zeroize.Zeroizing) @zeroize.Zeroizing.new := Iff.rfl

theorem zeroizing_vec_satisfiable : ∃ (W : Type → Type) (new : ZNewFn W), ZeroizingVecShape new :=
  ⟨fun Z => Z, fun _ z => ok z, fun _ v => ⟨v, rfl⟩⟩

/-- The three laws are on three different constants, so one assignment satisfies all of them. -/
theorem ratchet_laws_jointly_satisfiable :
    ∃ (pop : PopFn) (blanket : BlanketFn) (arrZ : ArrayZeroizeFn),
      PopShape pop ∧ BlanketU32Shape blanket ∧ ArrZU8Shape arrZ :=
  ⟨@popWitness, fun _ x => ok x, fun _ a => ok a,
    fun _ _ _ => ⟨_, _, rfl, rfl⟩, fun x => ⟨x, rfl⟩, fun a => ⟨a, rfl⟩⟩

end Tacenta.SatisfiabilityRatchetLaws

end

/--
info: 'Tacenta.SatisfiabilityRatchetLaws.ratchetRemoveSkippedAtTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.pop,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.SatisfiabilityRatchetLaws.ratchetRemoveSkippedAtTotal

/--
info: Tacenta.SatisfiabilityRatchetLaws.ratchetRemoveSkippedAtTotal (hZ : Tacenta.SatisfiabilityRatchetLaws.ArrZU8)
  (hB : Tacenta.SatisfiabilityRatchetLaws.LawBlanketU32) (hP : Tacenta.SatisfiabilityRatchetLaws.LawPop) :
  Tacenta.T1.RemoveSkippedAtTotal
-/
#guard_msgs in
#check Tacenta.SatisfiabilityRatchetLaws.ratchetRemoveSkippedAtTotal

/--
info: 'Tacenta.SatisfiabilityRatchetLaws.LawPop_is' depends on axioms: [propext, alloc.vec.Vec.pop]
-/
#guard_msgs in
#print axioms Tacenta.SatisfiabilityRatchetLaws.LawPop_is

/--
info: Tacenta.SatisfiabilityRatchetLaws.LawPop_is :
  Tacenta.SatisfiabilityRatchetLaws.LawPop ↔ Tacenta.SatisfiabilityRatchetLaws.PopShape @alloc.vec.Vec.pop
-/
#guard_msgs in
#check Tacenta.SatisfiabilityRatchetLaws.LawPop_is

/--
info: 'Tacenta.SatisfiabilityRatchetLaws.LawBlanketU32_is' depends on axioms: [propext, zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.SatisfiabilityRatchetLaws.LawBlanketU32_is

/--
info: Tacenta.SatisfiabilityRatchetLaws.LawBlanketU32_is :
  Tacenta.SatisfiabilityRatchetLaws.LawBlanketU32 ↔
    Tacenta.SatisfiabilityRatchetLaws.BlanketU32Shape @zeroize.Zeroize.Blanket.zeroize
-/
#guard_msgs in
#check Tacenta.SatisfiabilityRatchetLaws.LawBlanketU32_is

/--
info: 'Tacenta.SatisfiabilityRatchetLaws.ArrZU8_is' depends on axioms: [propext,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.SatisfiabilityRatchetLaws.ArrZU8_is

/--
info: Tacenta.SatisfiabilityRatchetLaws.ArrZU8_is :
  Tacenta.SatisfiabilityRatchetLaws.ArrZU8 ↔
    Tacenta.SatisfiabilityRatchetLaws.ArrZU8Shape @Array.Insts.ZeroizeZeroize.zeroize
-/
#guard_msgs in
#check Tacenta.SatisfiabilityRatchetLaws.ArrZU8_is

/--
info: 'Tacenta.SatisfiabilityRatchetLaws.RatchetCodec_ZeroizingVecTotal_is' depends on axioms: [propext,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new]
-/
#guard_msgs in
#print axioms Tacenta.SatisfiabilityRatchetLaws.RatchetCodec_ZeroizingVecTotal_is

/--
info: Tacenta.SatisfiabilityRatchetLaws.RatchetCodec_ZeroizingVecTotal_is :
  Tacenta.RatchetCodecT1.ZeroizingVecTotal ↔ Tacenta.SatisfiabilityRatchetLaws.ZeroizingVecShape @zeroize.Zeroizing.new
-/
#guard_msgs in
#check Tacenta.SatisfiabilityRatchetLaws.RatchetCodec_ZeroizingVecTotal_is

/--
info: 'Tacenta.SatisfiabilityRatchetLaws.zeroizing_vec_satisfiable' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.SatisfiabilityRatchetLaws.zeroizing_vec_satisfiable

/--
info: Tacenta.SatisfiabilityRatchetLaws.zeroizing_vec_satisfiable :
  ∃ W new, Tacenta.SatisfiabilityRatchetLaws.ZeroizingVecShape fun {Z} => new
-/
#guard_msgs in
#check Tacenta.SatisfiabilityRatchetLaws.zeroizing_vec_satisfiable

/--
info: 'Tacenta.SatisfiabilityRatchetLaws.pop_satisfiable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SatisfiabilityRatchetLaws.pop_satisfiable

/--
info: Tacenta.SatisfiabilityRatchetLaws.pop_satisfiable : ∃ f, Tacenta.SatisfiabilityRatchetLaws.PopShape fun {T} => f
-/
#guard_msgs in
#check Tacenta.SatisfiabilityRatchetLaws.pop_satisfiable

/--
info: 'Tacenta.SatisfiabilityRatchetLaws.blanket_satisfiable' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.SatisfiabilityRatchetLaws.blanket_satisfiable

/--
info: Tacenta.SatisfiabilityRatchetLaws.blanket_satisfiable :
  ∃ f, Tacenta.SatisfiabilityRatchetLaws.BlanketU32Shape fun {Z} => f
-/
#guard_msgs in
#check Tacenta.SatisfiabilityRatchetLaws.blanket_satisfiable

/--
info: 'Tacenta.SatisfiabilityRatchetLaws.arrZU8_satisfiable' depends on axioms: [propext, zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.SatisfiabilityRatchetLaws.arrZU8_satisfiable

/--
info: Tacenta.SatisfiabilityRatchetLaws.arrZU8_satisfiable :
  ∃ f, Tacenta.SatisfiabilityRatchetLaws.ArrZU8Shape fun {Z} {N} => f
-/
#guard_msgs in
#check Tacenta.SatisfiabilityRatchetLaws.arrZU8_satisfiable

/--
info: 'Tacenta.SatisfiabilityRatchetLaws.ratchet_laws_jointly_satisfiable' depends on axioms: [propext,
 Quot.sound,
 zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.SatisfiabilityRatchetLaws.ratchet_laws_jointly_satisfiable

/--
info: Tacenta.SatisfiabilityRatchetLaws.ratchet_laws_jointly_satisfiable :
  ∃ pop blanket arrZ,
    (Tacenta.SatisfiabilityRatchetLaws.PopShape fun {T} => pop) ∧
      (Tacenta.SatisfiabilityRatchetLaws.BlanketU32Shape fun {Z} => blanket) ∧
        Tacenta.SatisfiabilityRatchetLaws.ArrZU8Shape fun {Z} {N} => arrZ
-/
#guard_msgs in
#check Tacenta.SatisfiabilityRatchetLaws.ratchet_laws_jointly_satisfiable

/--
info: def Tacenta.SatisfiabilityRatchetLaws.ArrZU8 : Prop :=
∀ {N : Usize} (a : Std.Array U8 N),
  ∃ r, Array.Insts.ZeroizeZeroize.zeroize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a = ok r
-/
#guard_msgs in
#print Tacenta.SatisfiabilityRatchetLaws.ArrZU8

/--
info: def Tacenta.SatisfiabilityRatchetLaws.LawBlanketU32 : Prop :=
∀ (x : U32), ∃ r, zeroize.Zeroize.Blanket.zeroize U32.Insts.ZeroizeDefaultIsZeroes x = ok r
-/
#guard_msgs in
#print Tacenta.SatisfiabilityRatchetLaws.LawBlanketU32

/--
info: def Tacenta.SatisfiabilityRatchetLaws.LawPop : Prop :=
∀ (T : Type) (v : alloc.vec.Vec T), ↑v ≠ [] → ∃ o w, alloc.vec.Vec.pop Global v = ok (o, w) ∧ ↑w = (↑v).dropLast
-/
#guard_msgs in
#print Tacenta.SatisfiabilityRatchetLaws.LawPop
