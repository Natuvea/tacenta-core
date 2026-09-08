import Translation.TacentaErasure
import Translation.ErasureT1
import Model.Polynomial

/-!
# T3: refinement of the erasure code against its model

T1 says the translated crate cannot fail. The model's theorems say the erasure
code recovers a lost codeword exactly, which is `Model.Polynomial.unisolvence`.
Neither says the two compute the same thing, and until they are connected the
proved theorem is about a Lean definition rather than about the code that ships.

Thirty-eight model-generated vectors check the two agree at sample points. This
file is for the rest of the inputs.

The field arithmetic is closed: `add`, `clmul`, `reduce` and `mul` each compute
what the model says for every input. The decoder above them is not, and the
closing section says what that would take.

## The shapes differ, and the relation absorbs it

A field element is `Std.U16` on one side and `BitVec 16` on the other. The
translation carries Aeneas's bounded scalars; the model carries bitvectors,
because that is what `bv_decide` reasons about. One conversion, used everywhere.

## What this tier does not close

Nothing is opaque here. Unlike the ratchet's refinement, which rests on a stated
agreement between an axiomatised HMAC and the model's, this crate has no
primitives to assume: it is arithmetic and indexing, and both sides are visible.
The two boundary axioms T1 needed, `usize::div_ceil` and `Vec::truncate`, are
about totality rather than value, and nothing below depends on what they return.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.ErasureT3

open tacenta_erasure

/-! ## Carrying a field element across -/

/-- One translated field element as a model element. -/
def elemOf (x : Std.U16) : Model.Gf65536.Elem := x.bv

@[simp] theorem elemOf_def (x : Std.U16) : elemOf x = x.bv := rfl

/-! ## Addition

The whole of it: both sides are xor, and the conversion commutes with it. -/

theorem add_refines (a b : Std.U16) :
    gf.add a b ⦃ r => elemOf r = Model.Gf65536.add (elemOf a) (elemOf b) ⦄ := by
  unfold gf.add
  simp only [Model.Gf65536.add, elemOf_def]
  simp

/-! ## The carry-less product

The Rust loops sixteen times; the model writes sixteen terms out. Relating them
means unrolling, once per bit. -/

/-- The product accumulated over the low `n` bits.

The loop carries a partial result and the model writes a finished one, so
neither can be rewritten into the other directly. This names the partial form,
so the loop has an invariant to preserve and the model has something to be the
sixteenth case of. -/
def clmulUpto (b : BitVec 16) (x : BitVec 32) : Nat → BitVec 32
  | 0 => 0#32
  | n + 1 =>
    clmulUpto b x n ^^^ (if (b >>> n) &&& 1#16 == 1#16 then x <<< n else 0#32)

/-- One more bit. Stated so the loop's invariant can step without unfolding the
whole recursion, which does not terminate under `simp`. -/
theorem clmulUpto_succ (b : BitVec 16) (x : BitVec 32) (n : Nat) :
    clmulUpto b x (n + 1)
      = clmulUpto b x n ^^^ (if (b >>> n) &&& 1#16 == 1#16 then x <<< n else 0#32) :=
  rfl

/-- Sixteen bits in, the partial form is the model's. Sixteen unfoldings on one
side and none on the other, which is what `decide` is for on a goal this
concrete. -/
theorem clmulUpto_sixteen (a b : BitVec 16) :
    clmulUpto b (a.zeroExtend 32) 16 = Model.Gf65536.clmul a b := by
  simp only [clmulUpto, Model.Gf65536.clmul]
  bv_decide

/-- The loop computes the partial product, and at sixteen that is the model's.

The invariant is the obvious one and the only one that works: the accumulator
holds `clmulUpto` at the bit the counter has reached. The measure is how far the
counter still has to climb, which is T1's. -/
theorem clmul_loop_refines (b : Std.U16) (x : Std.U32) (acc : Std.U32) (i : Std.U32)
    (hi : i.val ≤ 16) (hacc : acc.bv = clmulUpto b.bv x.bv i.val) :
    gf.clmul_loop b x acc i ⦃ r => r.bv = clmulUpto b.bv x.bv 16 ⦄ := by
  unfold gf.clmul_loop
  apply loop.spec_decr_nat
    (measure := fun p => 16 - (Prod.snd p).val)
    (inv := fun p =>
      (Prod.snd p).val ≤ 16 ∧ (Prod.fst p).bv = clmulUpto b.bv x.bv (Prod.snd p).val)
  · rintro ⟨a, n⟩ ⟨hle, heq⟩
    simp only [] at hle heq
    unfold gf.clmul_loop.body
    simp only []
    split
    · step*
      split
      · next hb =>
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        have hbv : b.bv >>> n.val &&& 1#16 = 1#16 := by
          have h := (U16.eq_equiv_bv_eq _ _).mp hb
          rw [i2_post2, i1_post2] at h
          simpa using h
        rw [i3_post, clmulUpto_succ, ← heq, hbv]
        simp only [beq_self_eq_true, if_true]
        rw [← x_post2]
        simp
      · next hb =>
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        have hbv : ¬ (b.bv >>> n.val &&& 1#16 = 1#16) := by
          intro hc
          apply hb
          rw [U16.eq_equiv_bv_eq, i2_post2, i1_post2]
          simpa using hc
        rw [i3_post, clmulUpto_succ, ← heq]
        simp [hbv]
    · have h16 : n.val = 16 := by scalar_tac
      rw [h16] at heq
      simp [heq]
  · exact ⟨hi, hacc⟩

theorem clmul_refines (a b : Std.U16) :
    gf.clmul a b ⦃ r => r.bv = Model.Gf65536.clmul (elemOf a) (elemOf b) ⦄ := by
  unfold gf.clmul
  step
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists
    (clmul_loop_refines b x 0#u32 0#u32 (by scalar_tac) (by rfl))
  rw [hr]
  step*
  have hcast : U32.bv (UScalar.cast UScalarTy.U32 a) = (elemOf a).zeroExtend 32 := rfl
  rw [hpost, x_post, hcast]
  exact clmulUpto_sixteen (elemOf a) (elemOf b)

/-! ## The reduction

The same shape as the product and mirrored: the Rust walks a counter *down*
from thirty-one, and the model writes sixteen folds out. What differs is that
the direction makes the partial form count folds rather than bits, so the
invariant relates the counter to `31 - i` rather than to `i`. -/

/-- The reduction applied at bits thirty-one down to `32 - n`, which is `n`
folds. Counting folds rather than bit positions is what keeps the recursion
going the same way the model's `let` chain does, while the loop goes the other
way. -/
def reduceUpto (v : BitVec 32) : Nat → BitVec 32
  | 0 => v
  | n + 1 => Model.Gf65536.redAt (reduceUpto v n) (31 - n)

/-- One more fold. Same purpose as `clmulUpto_succ`: a step the loop can take
without the definition reaching a simp set. -/
theorem reduceUpto_succ (v : BitVec 32) (n : Nat) :
    reduceUpto v (n + 1) = Model.Gf65536.redAt (reduceUpto v n) (31 - n) := rfl

/-- Sixteen folds in, truncated, the partial form is the model's reduction. -/
theorem reduceUpto_sixteen (v : BitVec 32) :
    (reduceUpto v 16).truncate 16 = Model.Gf65536.reduce v := rfl

/-- The reduction's loop computes the partial form, and at fifteen it has done
all sixteen folds.

The lower bound in the invariant is not decoration. Without it the exit could
be at any counter below sixteen, and the post-condition names a fixed number of
folds. -/
theorem reduce_loop_refines (v0 : BitVec 32) (v : Std.U32) (i : Std.U32)
    (hlo : 15 ≤ i.val) (hhi : i.val ≤ 31) (hv : v.bv = reduceUpto v0 (31 - i.val)) :
    gf.reduce_loop v i ⦃ r => r.bv = reduceUpto v0 16 ⦄ := by
  unfold gf.reduce_loop
  apply loop.spec_decr_nat
    (measure := fun p => (Prod.snd p).val)
    (inv := fun p =>
      15 ≤ (Prod.snd p).val ∧ (Prod.snd p).val ≤ 31 ∧
        (Prod.fst p).bv = reduceUpto v0 (31 - (Prod.snd p).val))
  · rintro ⟨w, n⟩ ⟨hn15, hn31, hw⟩
    simp only [] at hn15 hn31 hw
    unfold gf.reduce_loop.body
    simp only []
    split
    · step*
      split
      · next hb =>
        step*
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        have hstep : 31 - i3.val = (31 - n.val) + 1 := by scalar_tac
        have hback : 31 - (31 - n.val) = n.val := by scalar_tac
        rw [hstep, reduceUpto_succ, hback, ← hw]
        have hbit := (U32.eq_equiv_bv_eq _ _).mp hb
        rw [i2_post2, i1_post2] at hbit
        simp only [Model.Gf65536.redAt]
        split
        · simp only [UScalar.bv_xor, x_post2]
          have hred : gf.REDUCER.bv = 69643#32 := by simp [gf.REDUCER]
          rw [hred]
          congr 1
          scalar_tac
        · next hc => exact absurd (by simpa using hbit) (by simpa using hc)
      · next hb =>
        step*
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        have hstep : 31 - i3.val = (31 - n.val) + 1 := by scalar_tac
        have hback : 31 - (31 - n.val) = n.val := by scalar_tac
        rw [hstep, reduceUpto_succ, hback, ← hw]
        simp only [Model.Gf65536.redAt]
        split
        · next hc =>
          exact absurd (by rw [U32.eq_equiv_bv_eq, i2_post2, i1_post2]; simpa using hc) hb
        · rfl
    · have h15 : n.val = 15 := by scalar_tac
      rw [h15] at hw
      simp [hw]
  · exact ⟨hlo, hhi, hv⟩

theorem reduce_refines (v : Std.U32) :
    gf.reduce v ⦃ r => elemOf r = Model.Gf65536.reduce v.bv ⦄ := by
  unfold gf.reduce
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists
    (reduce_loop_refines v.bv v 31#u32 (by scalar_tac) (by scalar_tac) (by rfl))
  rw [hr]
  step*
  have hcast : U16.bv (UScalar.cast UScalarTy.U16 r) = r.bv.truncate 16 := rfl
  simp only [elemOf_def, hcast, hpost]
  exact reduceUpto_sixteen v.bv

/-- Multiplication refines the model's, which is the point of the two above. -/
theorem mul_refines (a b : Std.U16) :
    gf.mul a b ⦃ r => elemOf r = Model.Gf65536.mul (elemOf a) (elemOf b) ⦄ := by
  unfold gf.mul
  obtain ⟨p, hp, hpp⟩ := Std.WP.spec_imp_exists (clmul_refines a b)
  rw [hp]
  show gf.reduce p ⦃ r => elemOf r = Model.Gf65536.mul (elemOf a) (elemOf b) ⦄
  obtain ⟨r, hr, hrp⟩ := Std.WP.spec_imp_exists (reduce_refines p)
  rw [hr]
  simp only [WP.spec_ok]
  rw [hrp, hpp]
  rfl

/-! ## What is pinned

The field arithmetic rests on the kernel's axioms and one more. `bv_decide`
reflects through native evaluation, and `clmulUpto_sixteen` is the single place
this file reaches for it: sixteen unfoldings against an unrolled expression is
what a SAT-backed decision procedure is for, and doing it by hand would be
sixteen near-identical cases proving nothing extra.

Pinned here for the same reason the model layer's base is pinned. If a proof
below starts resting on something new, this fails rather than being noticed by
whoever greps for it next. -/

/--
info: 'Tacenta.ErasureT3.mul_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 clmulUpto_sixteen._native.bv_decide.ax_1_8]
-/
#guard_msgs in
#print axioms Tacenta.ErasureT3.mul_refines

/-! ## Where this stops

The field is done: `add`, `clmul`, `reduce` and `mul` each compute what the
model says, for every input rather than at the thirty-eight sampled points.

What is not done is the distance from there to `unisolvence`. That theorem is
about interpolation over the field, and reaching it means refining
`interpolate`, the chunk helpers, and both entry points of the decoder, each of
which walks a slice rather than a fixed sixteen bits. The loops are longer and
the invariants are about lengths and positions rather than about bits, so the
shape proved here does not carry over directly, though the method does: name
the partial form, step it, and land the whole at the end.

Two things learned here are worth not rediscovering. `1#32` and `(1 : BitVec 32)`
are different terms to `rw` and to `simp only`, which is why the conditionals
below are opened with `split` on the model's own guard rather than by rewriting
with a hypothesis about the bit. And `step*` will happily consume a call this
file has a refinement for, leaving a bound variable with no post-condition; the
fix is to take the spec with `WP.spec_imp_exists` first and rewrite the call
away before stepping. -/

end Tacenta.ErasureT3
