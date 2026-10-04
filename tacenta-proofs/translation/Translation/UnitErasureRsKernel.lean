import Translation.UnitErasureRsDefs
import Translation.ErasureFieldBits

/-!
# The translated kernels of the unit's erasure coder compute their pure specifications

The unit's field arithmetic `tacenta_session_unit.tacenta_erasure.gf.{add,mul,inv}` refines
`Model.Gf65536`, and the three loop nests `weights`, `coefficients` and `evaluate` compute
`weightsSpec`, `coeffSpec` and `evalSpec` of `UnitErasureRsDefs.lean`, for every input slice
(`K_weights`, `K_coefficients`, `K_evaluate`).

The field part carries the argument of `ErasureT3.lean`, which is about the standalone crate's
constants, over to the unit's constants.  The partial forms `clmulUpto` and `reduceUpto` and their closing lemmas are pure
bitvector statements and are reused from `ErasureFieldBits.lean` unchanged, so this module calls no
solver itself.  Its axiom footprint is `propext`, `Classical.choice` and `Quot.sound`: the field
laws of `Model.Gf65536` and `Tacenta.ErasureT3.clmulUpto_sixteen` are kernel proofs.

`inv` is `pow a 65534` for nonzero `a`.  The translated square-and-multiply loop keeps
`acc * base ^ e` fixed (the model's `pow`), which is the model's halving recursion read one bit at
a time; it uses `Model.Gf65536.mul_assoc` and `mul_one`, not `mul_inv_cancel`.

The loop nests are proved with invariants over `List.range` prefixes: after `j` turns an inner
accumulator is the fold of `prodNe` over `List.range j`, after `i` turns an outer vector is the
first `i` entries of the specification, and the `evaluate` accumulator is the fold over the first
`i` products of `List.zipWith`.  No hypothesis is needed at either platform width: every counter
stays at most the slice length, and every pushed vector is shorter than the slice it is built
from, so `Vec.push` never meets `Usize.max`.

## What it does not show

* That the specification functions are the Lagrange interpolation of the model: that is
  `UnitErasureRsAlgebra.K_algebra`.
* Anything about the encoder or decoder loops that call these kernels.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit.tacenta_erasure

namespace Tacenta.UnitErasureRs.Kernel

open Tacenta.UnitErasureRs
open Tacenta.ErasureT3 (clmulUpto clmulUpto_succ clmulUpto_sixteen reduceUpto reduceUpto_succ
  reduceUpto_sixteen)

theorem eps_def (x : Std.U16) : eps x = x.bv := rfl

attribute [local simp] eps_def

/-! ## Field arithmetic of the unit -/

theorem gf_add_spec (a b : Std.U16) :
    gf.add a b ⦃ r => eps r = Model.Gf65536.add (eps a) (eps b) ⦄ := by
  unfold gf.add
  simp only [Model.Gf65536.add, eps_def]
  simp

theorem clmul_loop_spec (b : Std.U16) (x : Std.U32) (acc : Std.U32) (i : Std.U32)
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

theorem clmul_spec (a b : Std.U16) :
    gf.clmul a b ⦃ r => r.bv = Model.Gf65536.clmul (eps a) (eps b) ⦄ := by
  unfold gf.clmul
  step
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists
    (clmul_loop_spec b x 0#u32 0#u32 (by scalar_tac) (by rfl))
  rw [hr]
  step*
  have hcast : U32.bv (UScalar.cast UScalarTy.U32 a) = (eps a).zeroExtend 32 := rfl
  rw [hpost, x_post, hcast]
  exact clmulUpto_sixteen (eps a) (eps b)

theorem reduce_loop_spec (v0 : BitVec 32) (v : Std.U32) (i : Std.U32)
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

theorem reduce_spec (v : Std.U32) :
    gf.reduce v ⦃ r => eps r = Model.Gf65536.reduce v.bv ⦄ := by
  unfold gf.reduce
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists
    (reduce_loop_spec v.bv v 31#u32 (by scalar_tac) (by scalar_tac) (by rfl))
  rw [hr]
  step*
  have hcast : U16.bv (UScalar.cast UScalarTy.U16 r) = r.bv.truncate 16 := rfl
  simp only [eps_def, hcast, hpost]
  exact reduceUpto_sixteen v.bv

theorem gf_mul_spec (a b : Std.U16) :
    gf.mul a b ⦃ r => eps r = Model.Gf65536.mul (eps a) (eps b) ⦄ := by
  unfold gf.mul
  obtain ⟨p, hp, hpp⟩ := Std.WP.spec_imp_exists (clmul_spec a b)
  rw [hp]
  show gf.reduce p ⦃ r => eps r = Model.Gf65536.mul (eps a) (eps b) ⦄
  obtain ⟨r, hr, hrp⟩ := Std.WP.spec_imp_exists (reduce_spec p)
  rw [hr]
  simp only [WP.spec_ok]
  rw [hrp, hpp]
  rfl

/-! ## Exponentiation and inversion -/

/-- One step of the model's halving recursion, for a positive exponent. -/
theorem model_pow_pos (b : Model.Gf65536.Elem) (e : Nat) (he : 0 < e) :
    Model.Gf65536.pow b e =
      if e % 2 = 0 then Model.Gf65536.pow (Model.Gf65536.mul b b) (e / 2)
      else Model.Gf65536.mul b (Model.Gf65536.pow (Model.Gf65536.mul b b) (e / 2)) := by
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  rw [Model.Gf65536.pow]
  simp

/-- The square-and-multiply loop keeps `acc * base ^ e` (the model's power) fixed. -/
theorem pow_loop_spec (base : Std.U16) (e : Std.U32) (acc : Std.U16) :
    gf.pow_loop base e acc ⦃ r =>
      eps r = Model.Gf65536.mul (eps acc) (Model.Gf65536.pow (eps base) e.val) ⦄ := by
  unfold gf.pow_loop
  apply loop.spec_decr_nat
    (measure := fun p => (Prod.fst (Prod.snd p)).val)
    (inv := fun p => Model.Gf65536.mul (eps (Prod.snd (Prod.snd p)))
        (Model.Gf65536.pow (eps (Prod.fst p)) (Prod.fst (Prod.snd p)).val) =
      Model.Gf65536.mul (eps acc) (Model.Gf65536.pow (eps base) e.val))
  · rintro ⟨b1, e1, a1⟩ hinv
    simp only [] at hinv
    unfold gf.pow_loop.body
    simp only []
    split
    · step*
      have hi : i.val = e1.val % 2 := by
        rw [i_post1]; simp [Nat.and_one_is_mod]
      have he1 : 0 < e1.val := by scalar_tac
      split
      · next h1 =>
        have hodd : e1.val % 2 = 1 := by rw [← hi, h1]; rfl
        step with gf_mul_spec as ⟨acc1, hacc1⟩
        step with gf_mul_spec as ⟨base1, hbase1⟩
        step as ⟨e2, he2⟩
        have he2' : e2.val = e1.val / 2 := by rw [he2, Nat.shiftRight_eq_div_pow]
        refine ⟨?_, by omega⟩
        rw [← hinv, hacc1, hbase1, he2', model_pow_pos (eps b1) e1.val he1, if_neg (by omega),
          Model.Gf65536.mul_assoc]
      · next h1 =>
        have heven : e1.val % 2 = 0 := by
          have : i.val ≠ 1 := fun h => h1 (UScalar.eq_of_val_eq (by simpa using h))
          omega
        step with gf_mul_spec as ⟨base1, hbase1⟩
        step as ⟨e2, he2⟩
        have he2' : e2.val = e1.val / 2 := by rw [he2, Nat.shiftRight_eq_div_pow]
        refine ⟨?_, by omega⟩
        rw [← hinv, hbase1, he2', model_pow_pos (eps b1) e1.val he1, if_pos heven]
    · have he1 : e1.val = 0 := by scalar_tac
      simp only [WP.spec_ok]
      rw [← hinv, he1, Model.Gf65536.pow]
      exact (Model.Gf65536.mul_one _).symm
  · rfl

theorem gf_inv_spec (a : Std.U16) :
    gf.inv a ⦃ r => eps r = Model.Gf65536.inv (eps a) ⦄ := by
  unfold gf.inv
  split
  · next h =>
    simp only [WP.spec_ok, h]
    rfl
  · next h =>
    have hne : eps a ≠ 0#16 := by
      intro hc; apply h
      exact (U16.eq_equiv_bv_eq _ _).mpr (by simpa using hc)
    obtain ⟨r, hr, hp⟩ := Std.WP.spec_imp_exists (pow_loop_spec a 65534#u32 1#u16)
    simp only [gf.pow, hr, WP.spec_ok]
    rw [hp]
    have h1 : eps 1#u16 = Model.Gf65536.one := rfl
    rw [h1, Model.Gf65536.inv, Model.Gf65536.one, Model.Gf65536.one_mul]
    simp only [eps_def] at hne
    simp [hne, Model.Gf65536.size]

/-! ## Shared facts about the specification functions -/

/-- The step function of `prodNe`'s fold. -/
def neStep (f : ℕ → E) (i : ℕ) (acc : E) (j : ℕ) : E :=
  if j = i then acc else Model.Gf65536.mul acc (f j)

theorem prodNe_eq (f : ℕ → E) (n i : ℕ) :
    prodNe f n i = (List.range n).foldl (neStep f i) Model.Gf65536.one := rfl

theorem foldl_range_succ (g : E → ℕ → E) (a : E) (j : ℕ) :
    (List.range (j + 1)).foldl g a = g ((List.range j).foldl g a) j := by
  rw [List.range_succ, List.foldl_append]
  rfl

theorem getD_map_eps (l : List Std.U16) (k : ℕ) (hk : k < l.length) :
    (l.map eps).getD k 0#16 = eps l[k] := by
  simp [List.getD_eq_getElem?_getD, hk]

/-! ## `weights` -/

/-- The denominator loop folds `prodNe` in index order. -/
theorem weights_inner_spec (nodes : Slice Std.U16) (n i : Std.Usize) (xi denom : Std.U16)
    (j : Std.Usize) (hn : n.val = nodes.val.length) (hj : j.val ≤ n.val)
    (hd : eps denom = (List.range j.val).foldl
      (neStep (fun k => Model.Gf65536.add (eps xi) ((nodes.val.map eps).getD k 0#16)) i.val)
      Model.Gf65536.one) :
    weights_loop0_loop0 nodes n i xi denom j ⦃ r =>
      eps r = prodNe (fun k => Model.Gf65536.add (eps xi) ((nodes.val.map eps).getD k 0#16))
        n.val i.val ⦄ := by
  unfold weights_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun p => n.val - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ n.val ∧ eps (Prod.fst p) = (List.range (Prod.snd p).val).foldl
      (neStep (fun k => Model.Gf65536.add (eps xi) ((nodes.val.map eps).getD k 0#16)) i.val)
      Model.Gf65536.one)
  · rintro ⟨d1, j1⟩ ⟨hj1, hd1⟩
    simp only [] at hj1 hd1
    unfold weights_loop0_loop0.body
    simp only []
    split
    · next hlt =>
      split
      · next hne =>
        have hne' : j1.val ≠ i.val := by simpa using hne
        step as ⟨v, hv⟩
        step with gf_add_spec as ⟨a2, ha2⟩
        step with gf_mul_spec as ⟨d2, hd2⟩
        step as ⟨j2, hj2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hd2, ha2, hj2, foldl_range_succ, ← hd1, neStep, if_neg hne',
          getD_map_eps _ _ (by scalar_tac), hv]
      · next hne =>
        have he : j1.val = i.val := by simpa using hne
        step as ⟨j2, hj2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hj2, foldl_range_succ, ← hd1, neStep, if_pos he]
    · next hge =>
      have : j1.val = n.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hd1, this, prodNe_eq]
  · exact ⟨hj, hd⟩

/-- The `k`-th weight of `weightsSpec`, as a function of the index. -/
def wAt (xs : List E) (k : ℕ) : E :=
  Model.Gf65536.inv (prodNe (fun j => Model.Gf65536.add (xs.getD k 0#16) (xs.getD j 0#16))
    xs.length k)

/-- The weight loop pushes the weights in index order. -/
theorem weights_outer_spec (nodes : Slice Std.U16) (n : Std.Usize) (w : alloc.vec.Vec Std.U16)
    (i : Std.Usize) (hn : n.val = nodes.val.length) (hi : i.val ≤ n.val)
    (hw : w.val.map eps = (List.range i.val).map (wAt (nodes.val.map eps))) :
    weights_loop0 nodes n w i ⦃ r => r.val.map eps = weightsSpec (nodes.val.map eps) ⦄ := by
  unfold weights_loop0
  apply loop.spec_decr_nat
    (measure := fun p => n.val - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ n.val ∧
      (Prod.fst p).val.map eps = (List.range (Prod.snd p).val).map (wAt (nodes.val.map eps)))
  · rintro ⟨w1, i1⟩ ⟨hi1, hw1⟩
    simp only [] at hi1 hw1
    have hlen : w1.val.length = i1.val := by
      have := congrArg List.length hw1
      simpa using this
    unfold weights_loop0.body
    simp only []
    split
    · next hlt =>
      step as ⟨xi, hxi⟩
      step with weights_inner_spec nodes n i1 xi 1#u16 0#usize hn (by scalar_tac) rfl
        as ⟨denom, hdenom⟩
      step with gf_inv_spec as ⟨v, hv⟩
      step as ⟨w2, hw2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hw2, List.map_append, hw1, hi2, List.range_succ, List.map_append]
      congr 1
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      rw [hv, hdenom, wAt, List.length_map, ← hn, getD_map_eps _ _ (by scalar_tac), hxi]
    · next hge =>
      have : i1.val = n.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hw1, this, hn]
      unfold weightsSpec wAt
      simp only [List.length_map]
  · exact ⟨hi, hw⟩

theorem K_weights (s : Slice Std.U16) :
    weights s ⦃ w => w.val.map eps = weightsSpec (s.val.map eps) ⦄ := by
  unfold weights
  exact weights_outer_spec s (Slice.len s) _ 0#usize (by simp) (by scalar_tac) rfl

/-! ## `coefficients` -/

/-- The numerator loop folds `prodNe` in index order. -/
theorem coefficients_inner_spec (nodes : Slice Std.U16) (x : Std.U16) (n i : Std.Usize)
    (num : Std.U16) (j : Std.Usize) (hn : n.val = nodes.val.length) (hj : j.val ≤ n.val)
    (hd : eps num = (List.range j.val).foldl
      (neStep (fun k => Model.Gf65536.add (eps x) ((nodes.val.map eps).getD k 0#16)) i.val)
      Model.Gf65536.one) :
    coefficients_loop0_loop0 nodes x n i num j ⦃ r =>
      eps r = prodNe (fun k => Model.Gf65536.add (eps x) ((nodes.val.map eps).getD k 0#16))
        n.val i.val ⦄ := by
  unfold coefficients_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun p => n.val - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ n.val ∧ eps (Prod.fst p) = (List.range (Prod.snd p).val).foldl
      (neStep (fun k => Model.Gf65536.add (eps x) ((nodes.val.map eps).getD k 0#16)) i.val)
      Model.Gf65536.one)
  · rintro ⟨d1, j1⟩ ⟨hj1, hd1⟩
    simp only [] at hj1 hd1
    unfold coefficients_loop0_loop0.body
    simp only []
    split
    · next hlt =>
      split
      · next hne =>
        have hne' : j1.val ≠ i.val := by simpa using hne
        step as ⟨v, hv⟩
        step with gf_add_spec as ⟨a2, ha2⟩
        step with gf_mul_spec as ⟨d2, hd2⟩
        step as ⟨j2, hj2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hd2, ha2, hj2, foldl_range_succ, ← hd1, neStep, if_neg hne',
          getD_map_eps _ _ (by scalar_tac), hv]
      · next hne =>
        have he : j1.val = i.val := by simpa using hne
        step as ⟨j2, hj2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hj2, foldl_range_succ, ← hd1, neStep, if_pos he]
    · next hge =>
      have : j1.val = n.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hd1, this, prodNe_eq]
  · exact ⟨hj, hd⟩

/-- The guarded read of a weight: a missing weight reads as zero. -/
theorem weight_read_spec (ws : Slice Std.U16) (i : Std.Usize) :
    (if i < Slice.len ws then Slice.index_usize ws i else ok 0#u16) ⦃ r =>
      eps r = (ws.val.map eps).getD i.val 0#16 ⦄ := by
  split
  · next h =>
    step as ⟨v, hv⟩
    rw [getD_map_eps _ _ (by scalar_tac), hv]
  · next h =>
    simp only [WP.spec_ok]
    have : ws.val.length ≤ i.val := by scalar_tac
    simp [List.getD_eq_getElem?_getD, this]

/-- The `k`-th coefficient of `coeffSpec`, as a function of the index. -/
def cAt (xs ws : List E) (x : E) (k : ℕ) : E :=
  Model.Gf65536.mul (ws.getD k 0#16)
    (prodNe (fun j => Model.Gf65536.add x (xs.getD j 0#16)) xs.length k)

/-- The coefficient loop pushes the coefficients in index order. -/
theorem coefficients_outer_spec (nodes ws : Slice Std.U16) (x : Std.U16) (n : Std.Usize)
    (c : alloc.vec.Vec Std.U16) (i : Std.Usize) (hn : n.val = nodes.val.length)
    (hi : i.val ≤ n.val)
    (hc : c.val.map eps = (List.range i.val).map (cAt (nodes.val.map eps) (ws.val.map eps) (eps x))) :
    coefficients_loop0 nodes ws x n c i ⦃ r =>
      r.val.map eps = coeffSpec (nodes.val.map eps) (ws.val.map eps) (eps x) ⦄ := by
  unfold coefficients_loop0
  apply loop.spec_decr_nat
    (measure := fun p => n.val - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ n.val ∧
      (Prod.fst p).val.map eps =
        (List.range (Prod.snd p).val).map (cAt (nodes.val.map eps) (ws.val.map eps) (eps x)))
  · rintro ⟨c1, i1⟩ ⟨hi1, hc1⟩
    simp only [] at hi1 hc1
    have hlen : c1.val.length = i1.val := by
      have := congrArg List.length hc1
      simpa using this
    unfold coefficients_loop0.body
    simp only []
    split
    · next hlt =>
      step with coefficients_inner_spec nodes x n i1 1#u16 0#usize hn (by scalar_tac) rfl
        as ⟨num, hnum⟩
      step with weight_read_spec ws i1 as ⟨wi, hwi⟩
      step with gf_mul_spec as ⟨v, hv⟩
      step as ⟨c2, hc2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hc2, List.map_append, hc1, hi2, List.range_succ, List.map_append]
      congr 1
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      rw [hv, hnum, hwi, cAt, List.length_map, ← hn]
    · next hge =>
      have : i1.val = n.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hc1, this, hn]
      unfold coeffSpec cAt
      simp only [List.length_map]
  · exact ⟨hi, hc⟩

theorem K_coefficients (s sw : Slice Std.U16) (x : Std.U16) :
    coefficients s sw x ⦃ c => c.val.map eps = coeffSpec (s.val.map eps) (sw.val.map eps) (eps x) ⦄ := by
  unfold coefficients
  exact coefficients_outer_spec s sw x (Slice.len s) _ 0#usize (by simp) (by scalar_tac) rfl

/-! ## `evaluate` -/

/-- The accumulation loop folds the products in index order, skipping positions past the end
of `vals`. -/
theorem evaluate_loop_spec (coeffs vals : Slice Std.U16) (acc : Std.U16) (i : Std.Usize)
    (hi : i.val ≤ coeffs.val.length)
    (hacc : eps acc = ((List.zipWith Model.Gf65536.mul (coeffs.val.map eps)
      (vals.val.map eps)).take i.val).foldl Model.Gf65536.add Model.Gf65536.zero) :
    evaluate_loop coeffs vals acc i ⦃ r =>
      eps r = evalSpec (coeffs.val.map eps) (vals.val.map eps) ⦄ := by
  unfold evaluate_loop
  apply loop.spec_decr_nat
    (measure := fun p => coeffs.val.length - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ coeffs.val.length ∧
      eps (Prod.fst p) = ((List.zipWith Model.Gf65536.mul (coeffs.val.map eps)
        (vals.val.map eps)).take (Prod.snd p).val).foldl Model.Gf65536.add Model.Gf65536.zero)
  · rintro ⟨a1, i1⟩ ⟨hi1, ha1⟩
    simp only [] at hi1 ha1
    unfold evaluate_loop.body
    simp only []
    split
    · next hlt =>
      have hlt' : i1.val < coeffs.val.length := by scalar_tac
      split
      · next hlt2 =>
        have hlt2' : i1.val < vals.val.length := by scalar_tac
        step as ⟨c, hc⟩
        step as ⟨v, hv⟩
        step with gf_mul_spec as ⟨p, hp⟩
        step with gf_add_spec as ⟨a2, ha2⟩
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [ha2, hp, ha1, hi2, List.take_add_one, List.foldl_append, List.getElem?_zipWith,
          List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hlt',
          List.getElem?_eq_getElem hlt2', hc, hv]
        rfl
      · next hge2 =>
        have hge2' : vals.val.length ≤ i1.val := by scalar_tac
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [ha1, hi2, List.take_add_one, List.foldl_append, List.getElem?_zipWith,
          List.getElem?_map, List.getElem?_map, List.getElem?_eq_none hge2']
        simp
    · next hge =>
      have : i1.val = coeffs.val.length := by scalar_tac
      simp only [WP.spec_ok]
      rw [ha1, this, evalSpec, List.take_of_length_le]
      simp
  · exact ⟨hi, hacc⟩

theorem K_evaluate (s sv : Slice Std.U16) :
    evaluate s sv ⦃ r => eps r = evalSpec (s.val.map eps) (sv.val.map eps) ⦄ := by
  unfold evaluate
  exact evaluate_loop_spec s sv 0#u16 0#usize (by scalar_tac) rfl

end Tacenta.UnitErasureRs.Kernel
