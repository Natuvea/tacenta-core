import Translation.UnitErasureRsDefs
import Model.Polynomial

/-!
# The algebra of the erasure coder's kernels

`K_algebra`: for distinct nodes, the Lagrange evaluation the translated kernels compute
(`weightsSpec`, `coeffSpec`, `evalSpec` of `UnitErasureRsDefs.lean`) is the model's interpolant
`Model.Polynomial.interp`.  It is a statement about pure functions of `Model.Gf65536` and does not
mention the translated code.

The route:

* `lprod` is the product of a list in the field (a right fold of `mul` from `one`).
* `prodNe_eq_lprod`: the kernels' positional product `prodNe`, which skips the position `i`, is
  the product over the node list with its `i`-th entry erased.
* `weight_eq_lprod_filter`: the model's `weight`, which skips nodes equal to `xj` by value, is
  the product over the node list with those nodes filtered out; for distinct nodes and
  `xj = xs[i]` that filtered list is the list with its `i`-th entry erased
  (`filter_ne_getElem_eq_eraseIdx`).
* `lprod_map_mul` and `lprod_map_inv` split the product of the factors
  `(x + xk) * inv (xj + xk)` into a product of numerators times the inverse of a product of
  denominators; `inv_mul'` holds for every pair of elements, zero included, because `inv 0 = 0`.
* `foldl_add_eq_foldr` and `combine_eq_foldr` put the two sums in the same order, since `add` is
  associative and commutative with unit `zero`.

Distinctness of the nodes is used in one place only, `filter_ne_getElem_eq_eraseIdx`.

## What it does not show

* That the translated kernels compute the specification functions: that is
  `UnitErasureRsKernel.lean`.
* The field laws it calls.  They come from `Model.Gf65536` (`mul_inv_cancel`, `add_assoc`,
  `add_zero`, `mul_one`, `mul_assoc`), which the kernel proves, so the axiom footprint of `K_algebra`
  is `propext`, `Classical.choice` and `Quot.sound`.  This module adds no axiom.
-/

namespace Tacenta.UnitErasureRs.Algebra

open Model.Gf65536 (mul add inv one zero)
open Tacenta.UnitErasureRs (E prodNe weightsSpec coeffSpec evalSpec)

/-! ## Field facts -/

/-- `inv` of a nonzero element is the unique right inverse. -/
theorem inv_unique' {a b : E} (ha : a ≠ 0#16) (h : mul a b = one) : inv a = b := by
  have h1 : mul (inv a) (mul a b) = mul (inv a) one := by rw [h]
  rw [← Model.Gf65536.mul_assoc, Model.Gf65536.inv_mul_cancel a ha] at h1
  simp only [one, Model.Gf65536.one_mul, Model.Gf65536.mul_one] at h1
  exact h1.symm

theorem inv_zero' : inv (0#16 : E) = 0#16 := by
  simp [inv]

theorem inv_one' : inv one = one := by
  have := Model.Gf65536.mul_inv_cancel one (by decide)
  simpa [one, Model.Gf65536.one_mul] using this

/-- A product of nonzero elements is nonzero. -/
theorem mul_ne_zero' {a b : E} (ha : a ≠ 0#16) (hb : b ≠ 0#16) : mul a b ≠ 0#16 := by
  intro h
  exact hb (Model.Gf65536.eq_zero_of_mul_eq_zero ha h)

/-- Rearranging a product of four factors. -/
theorem mul_mul_mul_comm' (a b c d : E) : mul (mul a b) (mul c d) = mul (mul a c) (mul b d) := by
  rw [Model.Gf65536.mul_assoc, ← Model.Gf65536.mul_assoc b c d, Model.Gf65536.mul_comm b c,
    Model.Gf65536.mul_assoc c b d, ← Model.Gf65536.mul_assoc]

/-- `inv` is multiplicative, for every pair of elements: when either is zero both sides are
zero because `inv 0 = 0`. -/
theorem inv_mul' (a b : E) : inv (mul a b) = mul (inv a) (inv b) := by
  by_cases ha : a = 0#16
  · subst ha; rw [Model.Gf65536.zero_mul, inv_zero', Model.Gf65536.zero_mul]
  by_cases hb : b = 0#16
  · subst hb; rw [Model.Gf65536.mul_zero, inv_zero', Model.Gf65536.mul_zero]
  apply inv_unique' (mul_ne_zero' ha hb)
  rw [mul_mul_mul_comm', Model.Gf65536.mul_inv_cancel a ha, Model.Gf65536.mul_inv_cancel b hb]
  simp only [one, Model.Gf65536.mul_one]

/-! ## Products over lists -/

/-- The product of a list of field elements. -/
def lprod (l : List E) : E := l.foldr mul one

@[simp] theorem lprod_nil : lprod [] = one := rfl

@[simp] theorem lprod_cons (a : E) (l : List E) : lprod (a :: l) = mul a (lprod l) := rfl

theorem lprod_map_mul {α : Type} (l : List α) (f g : α → E) :
    lprod (l.map fun a => mul (f a) (g a)) = mul (lprod (l.map f)) (lprod (l.map g)) := by
  induction l with
  | nil => simp only [List.map_nil, lprod_nil, one, Model.Gf65536.mul_one]
  | cons a l ih => simp only [List.map_cons, lprod_cons, ih, mul_mul_mul_comm']

theorem lprod_map_inv {α : Type} (l : List α) (f : α → E) :
    lprod (l.map fun a => inv (f a)) = inv (lprod (l.map f)) := by
  induction l with
  | nil => simp only [List.map_nil, lprod_nil, inv_one']
  | cons a l ih => simp only [List.map_cons, lprod_cons, ih, inv_mul']

/-- The kernels' left fold that skips position `i`, from an accumulator. -/
theorem foldl_skip_eq (f : ℕ → E) (i : ℕ) (l : List ℕ) (a : E) :
    l.foldl (fun acc j => if j = i then acc else mul acc (f j)) a =
      mul a (lprod ((l.filter fun j => decide (j ≠ i)).map f)) := by
  induction l generalizing a with
  | nil =>
    simp only [List.foldl_nil, List.filter_nil, List.map_nil, lprod_nil, one,
      Model.Gf65536.mul_one]
  | cons j l ih =>
    rw [List.foldl_cons, ih, List.filter_cons]
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, Model.Gf65536.mul_assoc]

/-- `prodNe` as a product over the positions other than `i`. -/
theorem prodNe_eq_filter (f : ℕ → E) (n i : ℕ) :
    prodNe f n i = lprod (((List.range n).filter fun j => decide (j ≠ i)).map f) := by
  unfold prodNe
  rw [foldl_skip_eq]
  simp only [one, Model.Gf65536.one_mul]

theorem map_getD_range (xs : List E) :
    (List.range xs.length).map (fun j => xs.getD j 0#16) = xs := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem xs 0#16 h2

/-- The positions other than `i`, read through the list, are the list with its `i`-th entry
erased. -/
theorem filter_range_map_getD (xs : List E) (i : ℕ) :
    ((List.range xs.length).filter fun j => decide (j ≠ i)).map (fun j => xs.getD j 0#16) =
      xs.eraseIdx i := by
  induction xs generalizing i with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
    cases i with
    | zero =>
      have hf : ((List.range t.length).filter ((fun j => decide (j ≠ 0)) ∘ Nat.succ)) =
          List.range t.length := by
        apply List.filter_eq_self.mpr
        intro j _
        simp
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, hf,
        List.map_map, List.eraseIdx_cons_zero]
      have : ((fun j => (a :: t).getD j 0#16) ∘ Nat.succ) = fun j => t.getD j 0#16 := by
        funext j; simp
      rw [this, map_getD_range]
    | succ i =>
      have hf : ((List.range t.length).filter ((fun j => decide (j ≠ i + 1)) ∘ Nat.succ)) =
          (List.range t.length).filter (fun j => decide (j ≠ i)) := by
        apply List.filter_congr
        intro j _
        simp
      simp only [ne_eq, Nat.zero_ne_add_one, not_false_eq_true, decide_true, if_true, hf,
        List.map_cons, List.map_map, List.eraseIdx_cons_succ, List.getD_cons_zero]
      have : ((fun j => (a :: t).getD j 0#16) ∘ Nat.succ) = fun j => t.getD j 0#16 := by
        funext j; simp
      rw [this]
      congr 1
      exact ih i

/-- **The kernels' positional product** is the product over the node list with the `i`-th
entry erased. -/
theorem prodNe_eq_lprod (xs : List E) (g : E → E) (i : ℕ) :
    prodNe (fun j => g (xs.getD j 0#16)) xs.length i = lprod ((xs.eraseIdx i).map g) := by
  rw [prodNe_eq_filter, ← filter_range_map_getD xs i, List.map_map]
  rfl

/-! ## The model's weight as a product -/

/-- One factor of the model's Lagrange weight of node `xj` at `x`. -/
def term (xj x xk : E) : E := mul (add x xk) (inv (add xj xk))

/-- `weight` skips by value: it is the product over the nodes different from `xj`. -/
theorem weight_eq_lprod_filter (xs : List E) (xj x : E) :
    Model.Polynomial.weight xs xj x =
      lprod ((xs.filter fun xk => decide (xk ≠ xj)).map (term xj x)) := by
  induction xs with
  | nil => rfl
  | cons xk xs ih =>
    rw [Model.Polynomial.weight_cons, List.filter_cons]
    by_cases h : xk = xj
    · simp only [h, if_true, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        if_false, ih]
    · simp only [h, if_false, ne_eq, not_false_eq_true, decide_true, if_true, List.map_cons,
        lprod_cons, ih, term]
      exact Model.Gf65536.mul_comm _ _

/-- For distinct nodes, skipping the value `xs[i]` is skipping the position `i`. -/
theorem filter_ne_getElem_eq_eraseIdx (xs : List E) (hnd : xs.Nodup) (i : ℕ)
    (hi : i < xs.length) :
    (xs.filter fun xk => decide (xk ≠ xs[i])) = xs.eraseIdx i := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨ha, ht⟩ := hnd
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, List.filter_cons, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true, if_false, List.eraseIdx_cons_zero]
      apply List.filter_eq_self.mpr
      intro b hb
      simp only [decide_eq_true_eq]
      intro e
      exact ha (e ▸ hb)
    | succ i =>
      have hi' : i < t.length := by simpa using hi
      have hne : a ≠ t[i] := by
        intro e
        exact ha (e ▸ List.getElem_mem hi')
      simp only [List.getElem_cons_succ, List.filter_cons, ne_eq, hne, not_false_eq_true,
        decide_true, if_true, List.eraseIdx_cons_succ]
      congr 1
      exact ih ht i hi'

/-- **The coefficient the kernels compute at node `i` is the model's weight of that node.** -/
theorem coeff_eq_weight (xs : List E) (hnd : xs.Nodup) (x : E) (i : ℕ) (hi : i < xs.length) :
    mul (inv (prodNe (fun j => add (xs.getD i 0#16) (xs.getD j 0#16)) xs.length i))
        (prodNe (fun j => add x (xs.getD j 0#16)) xs.length i) =
      Model.Polynomial.weight xs xs[i] x := by
  rw [List.getD_eq_getElem xs 0#16 hi,
    prodNe_eq_lprod xs (fun b => add xs[i] b) i, prodNe_eq_lprod xs (fun b => add x b) i,
    weight_eq_lprod_filter, filter_ne_getElem_eq_eraseIdx xs hnd i hi]
  unfold term
  rw [lprod_map_mul, lprod_map_inv]
  exact Model.Gf65536.mul_comm _ _

/-! ## The sums -/

/-- A left fold of `add` from `a` is `a` plus the right fold from `zero`. -/
theorem foldl_add_eq (l : List E) (a : E) :
    l.foldl add a = add a (l.foldr add zero) := by
  induction l generalizing a with
  | nil => simp only [List.foldl_nil, List.foldr_nil, Model.Gf65536.add_zero]
  | cons b l ih => rw [List.foldl_cons, ih, List.foldr_cons, Model.Gf65536.add_assoc]

theorem foldl_add_eq_foldr (l : List E) : l.foldl add zero = l.foldr add zero := by
  rw [foldl_add_eq, Model.Gf65536.add_comm, Model.Gf65536.add_zero]

/-- The model's `combine` as a right fold of `add` over its terms. -/
theorem combine_eq_foldr (xs : List E) (pts : List (E × E)) (x : E) :
    Model.Polynomial.combine xs pts x =
      (pts.map fun p => mul p.2 (Model.Polynomial.weight xs p.1 x)).foldr add zero := by
  induction pts with
  | nil => rfl
  | cons p pts ih =>
    rw [Model.Polynomial.combine_cons, ih, List.map_cons, List.foldr_cons, Model.Gf65536.add_comm]

/-! ## The theorem -/

/-- **The algebra of the kernels.**  For distinct nodes, the Lagrange evaluation the kernels
compute is the model's interpolant. -/
theorem K_algebra (xs ys : List E) (x : E) (hnd : xs.Nodup) (hl : ys.length = xs.length) :
    evalSpec (coeffSpec xs (weightsSpec xs) x) ys = Model.Polynomial.interp (xs.zip ys) x := by
  unfold evalSpec Model.Polynomial.interp
  rw [List.map_fst_zip (by omega), combine_eq_foldr, foldl_add_eq_foldr]
  congr 1
  apply List.ext_getElem
  · simp [coeffSpec, hl]
  · intro k h1 h2
    have hk : k < xs.length := by simpa [hl] using h2
    have hky : k < ys.length := by omega
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_zip, coeffSpec,
      List.getElem_range]
    have hw : (weightsSpec xs).getD k 0#16 =
        inv (prodNe (fun j => add (xs.getD k 0#16) (xs.getD j 0#16)) xs.length k) := by
      rw [List.getD_eq_getElem _ _ (by simpa [weightsSpec] using hk)]
      simp [weightsSpec]
    rw [hw, coeff_eq_weight xs hnd x k hk]
    exact Model.Gf65536.mul_comm _ _

end Tacenta.UnitErasureRs.Algebra
