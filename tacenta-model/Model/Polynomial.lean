/-
Model.Polynomial: polynomials over GF(2^16), and evaluating them.

The layer between the field and the erasure code. The published ML-KEM Braid
specification says the chunking is "implemented using polynomial interpolation
over a finite field, and the number of distinct codewords is equal to the size of
the underlying field" -- so a chunk is a polynomial evaluated at a point, and
decoding is recovering the polynomial from enough points.

Everything here rests on `Model.Gf65536` being a field, which it is: additive
laws, commutativity, distributivity and associativity proved, inverses checked
exhaustively. Every argument below depends on that.
-/
import Model.Gf65536

namespace Model.Polynomial

open Model.Gf65536

/-- A polynomial, as its coefficients from the constant term up.

    A list rather than a function, so it stays in the executable and provable
    subset the rest of this model uses. Trailing zeros are permitted: two lists
    that differ only by them denote the same polynomial and evaluate the same,
    which is proved below rather than assumed. -/
abbrev Poly := List Elem

/-- Evaluate by Horner's rule: fewest multiplications, and the shape that makes
    the proofs below fold rather than expand. -/
def eval (p : Poly) (x : Elem) : Elem :=
  p.foldr (fun c acc => add c (mul acc x)) zero

@[simp] theorem eval_nil (x : Elem) : eval [] x = zero := rfl

@[simp] theorem eval_cons (c : Elem) (p : Poly) (x : Elem) :
    eval (c :: p) x = add c (mul (eval p x) x) := rfl

/-- The zero polynomial evaluates to zero, however many zeros it is written
with. This is what makes trailing zeros harmless. -/
theorem eval_zeros (n : Nat) (x : Elem) : eval (List.replicate n zero) x = zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate, eval_cons, ih]
    simp only [zero, mul, reduce, redAt, clmul, add]
    bv_decide

/-! ## Evaluation is linear

The property the whole erasure code rests on: a codeword of a sum is the sum of
the codewords. It is what lets a decoder subtract one polynomial from another and
reason about the difference, and it is where the field's distributivity is
actually used. -/

/-- Adding polynomials coefficient by coefficient, padding the shorter one. -/
def addP : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => add a b :: addP p q

/-- Evaluation carries addition of polynomials to addition in the field.

    The proof is distributivity and the additive laws, applied at each
    coefficient. Nothing else is going on, but nothing else *could* go on until
    those laws existed. -/
theorem eval_addP (p q : Poly) (x : Elem) :
    eval (addP p q) x = add (eval p x) (eval q x) := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => simp only [addP, eval_nil]; simp only [zero, add]; bv_decide
    | cons b q =>
      simp only [addP, eval_nil, eval_cons]
      simp only [zero, add]
      bv_decide
  | cons a p ih =>
    cases q with
    | nil =>
      simp only [addP, eval_nil, eval_cons]
      simp only [zero, add]
      bv_decide
    | cons b q =>
      simp only [addP, eval_cons, ih]
      -- (a + b) + (P + Q)·x  =  (a + P·x) + (b + Q·x)
      simp only [add, mul_distrib_right]
      bv_decide

/-! ## Scaling

The other half of linearity: a codeword of a scaled polynomial is the scaled
codeword. Together with the above, evaluation is a linear map from polynomials to
the field, which is the statement an erasure code needs. -/

def scaleP (s : Elem) : Poly → Poly
  | [] => []
  | a :: p => mul s a :: scaleP s p

theorem eval_scaleP (s : Elem) (p : Poly) (x : Elem) :
    eval (scaleP s p) x = mul s (eval p x) := by
  induction p with
  | nil => simp only [scaleP, eval_nil]; simp only [zero]; exact (mul_zero s).symm
  | cons a p ih =>
    simp only [scaleP, eval_cons, ih, mul_assoc]
    -- s·a + s·(P·x) = s·(a + P·x): distributivity, read right to left.
    simp only [add]
    exact (mul_distrib s a (mul (eval p x) x)).symm

/-! ## Multiplication

The operation this file spent its first half avoiding.

Decoding needs the interpolant's *value*, so evaluation was enough, and the note
at the end of this file said what that left open: unisolvence, the claim that any
`k` codewords determine the message rather than merely reproducing themselves.
That needs a factor theorem, a factor theorem needs division by a linear factor,
and division needs multiplication to state what it undoes.

So this is the bottom of that stack. -/

def mulP : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => addP (scaleP a q) (zero :: mulP p q)

/-- **Evaluation is multiplicative.** The other half of the ring structure, and
the one that makes a factorisation say something about values. -/
theorem eval_mulP (p q : Poly) (x : Elem) :
    eval (mulP p q) x = mul (eval p x) (eval q x) := by
  induction p with
  | nil => simp only [mulP, eval_nil]; simp only [zero]; exact (zero_mul _).symm
  | cons a p ih =>
    simp only [mulP, eval_addP, eval_scaleP, eval_cons, ih, add, zero]
    rw [mul_distrib_right]
    have hz : ∀ y : Elem, (0#16 : Elem) ^^^ y = y := by intro y; bv_decide
    rw [hz]
    -- (P·Q)·x = (P·x)·Q, by associativity and commutativity.
    have hswap : mul (mul (eval p x) (eval q x)) x = mul (mul (eval p x) x) (eval q x) := by
      rw [mul_assoc, mul_comm (eval q x) x, ← mul_assoc]
    rw [hswap]

/-! ## Division by a linear factor

Synthetic division, written on the ascending coefficient list the rest of this
file uses. Dividing `p` by `X + a` gives a quotient and a constant remainder, and
in characteristic two `X + a` is also `X - a`, so this is division by the linear
factor whose root is `a`.

The recursion is the usual one read from the other end. Writing `p = c + X·p'`
and `p' = (X + a)·q' + r'`:

    c + X·p'  =  (X + a)·(X·q' + r') + (a·r' + c)

so the quotient gains `r'` as its new lowest coefficient and the remainder is
`c + a·r'`. -/

def synDiv (a : Elem) : Poly → Poly × Elem
  | [] => ([], zero)
  | c :: p =>
    let r := (synDiv a p).2
    (r :: (synDiv a p).1, add c (mul a r))

/-- **The remainder is the value.** Half of the factor theorem already: `a` is a
root exactly when the division comes out exact. -/
theorem synDiv_rem (a : Elem) (p : Poly) : (synDiv a p).2 = eval p a := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [synDiv, eval_cons, ih]
    rw [mul_comm]

/-- The xor rearrangement the division identity ends in, stated over abstract
values so a solver sees a handful of atoms rather than a nest of products. That
distinction is the governing rule for this field: a solver settles statements
mentioning one product and none mentioning two. -/
private theorem xor_shuffle (c u v w : Elem) :
    c ^^^ (u ^^^ v) = ((w ^^^ v) ^^^ u) ^^^ (c ^^^ w) := by bv_decide

/-- **The division identity.** `p = (X + a)·q + r`, stated at a value because
that is the form every use of it takes. -/
theorem eval_synDiv (a : Elem) (p : Poly) (x : Elem) :
    eval p x = add (mul (add a x) (eval (synDiv a p).1 x)) (synDiv a p).2 := by
  induction p with
  | nil =>
    simp only [synDiv, eval_nil, zero, mul_zero, add]
    bv_decide
  | cons c p ih =>
    simp only [synDiv, eval_cons]
    rw [ih]
    simp only [add]
    -- Distribute everywhere, so both sides are sums of the same four products.
    simp only [mul_distrib_right, mul_distrib]
    -- Left-associate every product, so the two sides name the same atoms rather
    -- than two spellings of each.
    simp only [← mul_assoc]
    rw [mul_comm (synDiv a p).2 x]
    clear ih
    -- `mul` stays folded, so the solver sees four atoms rather than a field.
    bv_decide

/-- **The factor theorem.** A root factors out.

Immediate from the two above, and it is the statement the whole detour through
multiplication and division was for: if `a` is a root of `p`, then `p` is
`(X + a)` times something, so `p` vanishes wherever that something does and
nowhere else. -/
theorem factor (a : Elem) (p : Poly) (h : eval p a = zero) (x : Elem) :
    eval p x = mul (add a x) (eval (synDiv a p).1 x) := by
  rw [eval_synDiv a p x, synDiv_rem, h, add_zero]

/-- The quotient is a list as long as the polynomial, and its top coefficient is
always zero. That is what says the degree actually dropped, which the list length
alone does not. -/
theorem synDiv_len (a : Elem) (p : Poly) : (synDiv a p).1.length = p.length := by
  induction p with
  | nil => rfl
  | cons c p ih => simp only [synDiv, List.length_cons, ih]

/-! ## Degree

The number of coefficients that matter, which is not the number stored. A list
may carry trailing zeros, and `eval_zeros` already says they change nothing; this
counts what is left when they are ignored.

Zero for the zero polynomial however it is written, and otherwise one more than
the degree in the usual sense. Counting *coefficients* rather than the exponent
avoids a subtraction that would have to saturate at the zero polynomial. -/

def deg : Poly → Nat
  | [] => 0
  | c :: p => if deg p = 0 && c == zero then 0 else deg p + 1

@[simp] theorem deg_nil : deg [] = 0 := rfl

theorem deg_cons (c : Elem) (p : Poly) :
    deg (c :: p) = if deg p = 0 && c == zero then 0 else deg p + 1 := rfl

/-- A polynomial with no significant coefficients is the zero function. -/
theorem eval_of_deg_zero {p : Poly} (h : deg p = 0) (x : Elem) : eval p x = zero := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    rw [deg_cons] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      rw [eval_cons, ih hc.1, hc.2]
      simp only [zero, mul, add, reduce, redAt, clmul]
      bv_decide
    · omega

/-- Dividing a polynomial that is already the zero function leaves one. -/
theorem synDiv_deg_zero (a : Elem) {p : Poly} (h : deg p = 0) :
    deg (synDiv a p).1 = 0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    rw [deg_cons] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      simp only [synDiv, deg_cons, ih hc.1, synDiv_rem, eval_of_deg_zero hc.1]
      simp
    · omega

/-- A polynomial with exactly one significant coefficient is a nonzero constant,
so it vanishes nowhere.

The fact the exact degree below turns on: it is what rules out the quotient's
leading coefficient collapsing to zero. -/
theorem eval_of_deg_one {p : Poly} (h : deg p = 1) (x : Elem) : eval p x ≠ zero := by
  cases p with
  | nil => simp at h
  | cons c p =>
    rw [deg_cons] at h
    split at h
    · omega
    · rename_i hne
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and] at hne
      have hp : deg p = 0 := by omega
      have hc : c ≠ zero := hne hp
      have hz : mul zero x = zero := zero_mul x
      rw [eval_cons, eval_of_deg_zero hp, hz, add_zero]
      exact hc

/-- **The exact degree.** Dividing by a linear factor lowers it by exactly one.

The inequality was enough to make an induction terminate and not enough to make
the counting argument work, because it left open a collapse to zero that the
finite field makes possible in general. This rules it out: the quotient's leading
coefficient is the tail's value at the node, and a tail of degree one is a
nonzero constant, which vanishes nowhere. -/
theorem synDiv_deg_exact (a : Elem) (p : Poly) :
    deg (synDiv a p).1 = deg p - 1 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    by_cases hp : deg p = 0
    · have hr : (synDiv a p).2 = zero := by
        rw [synDiv_rem]; exact eval_of_deg_zero hp a
      have hq : deg (synDiv a p).1 = 0 := by rw [ih, hp]
      simp only [synDiv, hr, deg_cons, hq, hp]
      by_cases hc : c = zero <;> simp [hc]
    · have hcp : deg (c :: p) = deg p + 1 := by rw [deg_cons]; simp [hp]
      by_cases h1 : deg p = 1
      · have hr : (synDiv a p).2 ≠ zero := by
          rw [synDiv_rem]; exact eval_of_deg_one h1 a
        have hq : deg (synDiv a p).1 = 0 := by rw [ih, h1]
        simp only [synDiv, deg_cons, hq, hcp, h1]
        simp [hr]
      · have hq : deg (synDiv a p).1 = deg p - 1 := ih
        have hd : deg p - 1 ≠ 0 := by omega
        simp only [synDiv, deg_cons, hcp, hq]
        rw [if_neg (by simp [hd])]
        omega

/-- **Division by a linear factor lowers the degree.**

The lemma the counting argument was missing. The list does not get shorter, and
this says the part of it that matters does. -/
theorem synDiv_deg (a : Elem) {p : Poly} (h : deg p ≠ 0) :
    deg (synDiv a p).1 < deg p := by
  induction p with
  | nil => simp at h
  | cons c p ih =>
    by_cases hp : deg p = 0
    · -- The tail is already the zero function, so the quotient is too, and the
      -- head must be nonzero or the whole thing would have degree zero.
      have hc : c ≠ zero := by
        intro e
        rw [deg_cons, hp, e] at h
        simp at h
      have hcp : deg (c :: p) = 1 := by
        rw [deg_cons, hp]; simp [hc]
      have hr : (synDiv a p).2 = zero := by
        rw [synDiv_rem]; exact eval_of_deg_zero hp a
      have hq0 : deg (synDiv a p).1 = 0 := synDiv_deg_zero a hp
      simp only [synDiv, hr]
      rw [deg_cons, hq0, hcp]
      simp
    · -- The tail already has a significant coefficient, so both sides gain one
      -- and the inductive gap survives.
      have hlt := ih hp
      have hcp : deg (c :: p) = deg p + 1 := by
        rw [deg_cons]; simp [hp]
      have hq : deg ((synDiv a p).2 :: (synDiv a p).1) ≤ deg (synDiv a p).1 + 1 := by
        rw [deg_cons]; split <;> omega
      simp only [synDiv]
      omega

/-- Adding cannot raise the degree. Needed to form the difference of two
polynomials and know it is no bigger than either. -/
theorem deg_addP (p q : Poly) : deg (addP p q) ≤ max (deg p) (deg q) := by
  induction p generalizing q with
  | nil => simp [addP]
  | cons a p ih =>
    cases q with
    | nil => simp [addP]
    | cons b q =>
      have hpq := ih q
      have hz : add zero zero = zero := add_zero zero
      simp only [addP, deg_cons]
      split
      · omega
      · rename_i hne
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and] at hne
        split <;> rename_i h1 <;> split <;> rename_i h2 <;>
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1 h2 <;>
          first
            | omega
            | (exfalso
               have : deg (addP p q) = 0 := by omega
               exact hne this (by rw [h1.2, h2.2]; exact hz))

/-! ## Linear factors

A Lagrange basis is a product of linear factors over a constant, so building one
as a polynomial needs multiplication by `(c + X)` and nothing more general.
Written directly rather than through `mulP` because the direct form is the one
the degree argument wants: `p·(c + X) = c·p + X·p`, and `X·p` is `p` with a zero
pushed underneath it. -/

def mulLin (c : Elem) (p : Poly) : Poly := addP (scaleP c p) (zero :: p)

theorem eval_mulLin (c : Elem) (p : Poly) (x : Elem) :
    eval (mulLin c p) x = mul (add c x) (eval p x) := by
  simp only [mulLin, eval_addP, eval_scaleP, eval_cons]
  simp only [add, zero]
  rw [mul_distrib_right]
  have hz : ∀ y : Elem, (0#16 : Elem) ^^^ y = y := by intro y; bv_decide
  rw [hz, mul_comm x (eval p x)]

/-! ## Counting roots

The argument the degree machinery was for. A polynomial with significant
coefficients has fewer roots than it has of them.

Stated with an explicit bound on the degree so the recursion is structural on a
natural number rather than well-founded on the polynomial, which keeps it in the
subset the rest of this development stays in. -/

theorem roots_lt_deg : ∀ (n : Nat) (p : Poly) (rs : List Elem),
    deg p ≤ n → deg p ≠ 0 → rs.Nodup → (∀ r ∈ rs, eval p r = zero) →
    rs.length < deg p := by
  intro n
  induction n with
  | zero => intro p rs hle h _ _; omega
  | succ n ih =>
    intro p rs hle h hnd hroots
    cases rs with
    | nil => simpa using Nat.pos_of_ne_zero h
    | cons r rs' =>
      have hr : eval p r = zero := hroots r (by simp)
      have hdq : deg (synDiv r p).1 = deg p - 1 := synDiv_deg_exact r p
      -- Degree one would mean a nonzero constant, which has no roots at all, so
      -- the quotient still has a significant coefficient.
      have hp2 : deg p ≠ 1 := by
        intro e
        exact eval_of_deg_one e r hr
      have hqne : deg (synDiv r p).1 ≠ 0 := by rw [hdq]; omega
      -- Every other root of `p` is a root of the quotient, because the factor it
      -- was divided by does not vanish there and the field has no zero divisors.
      have hq : ∀ s ∈ rs', eval (synDiv r p).1 s = zero := by
        intro s hs
        have hps : eval p s = zero := hroots s (by simp [hs])
        have hne : s ≠ r := by
          intro e
          subst e
          exact (List.nodup_cons.mp hnd).1 hs
        have hfac := factor r p hr s
        rw [hps] at hfac
        have hrs : add r s ≠ 0#16 := add_ne_zero_of_ne (fun e => hne e.symm)
        exact eq_zero_of_mul_eq_zero hrs hfac.symm
      have hrec := ih (synDiv r p).1 rs' (by omega) hqne (List.nodup_cons.mp hnd).2 hq
      simp only [List.length_cons]
      omega

/-- **Two polynomials that agree at enough points agree everywhere.**

The statement the erasure code's guarantee rests on, and the reason the whole
detour through multiplication, division, degree and root counting was taken.

"Enough" is: as many distinct points as either polynomial has significant
coefficients. Their difference then has at least that many roots and at most that
degree, and the counting bound leaves it no choice but to be the zero function.

In characteristic two the difference is the sum, which is why no subtraction
appears. -/
theorem eval_eq_of_agree (p q : Poly) (xs : List Elem)
    (hnd : xs.Nodup)
    (hdp : deg p ≤ xs.length) (hdq : deg q ≤ xs.length)
    (hagree : ∀ s ∈ xs, eval p s = eval q s) (x : Elem) :
    eval p x = eval q x := by
  have hroots : ∀ s ∈ xs, eval (addP p q) s = zero := by
    intro s hs
    rw [eval_addP, hagree s hs]
    exact add_self _
  have hd : deg (addP p q) ≤ xs.length :=
    Nat.le_trans (deg_addP p q) (Nat.max_le.mpr ⟨hdp, hdq⟩)
  have hzero : deg (addP p q) = 0 := by
    rcases Nat.eq_zero_or_pos (deg (addP p q)) with h | h
    · exact h
    · have hne : deg (addP p q) ≠ 0 := by omega
      have hlt := roots_lt_deg xs.length (addP p q) xs hd hne hnd hroots
      omega
  have := eval_of_deg_zero hzero x
  rw [eval_addP] at this
  -- `eval p x ^^^ eval q x = 0` forces the two values equal.
  simp only [add, zero] at this
  exact (xor_eq_zero_iff _ _).mp this

/-! ## How the pieces fit

The chain from here to the erasure code's guarantee, in the order it was built:

- `eval_mulP`, `mulLin`: evaluation is multiplicative, so a factorisation says
  something about values.
- `synDiv`, `synDiv_rem`, `eval_synDiv`, `factor`: a root factors out.
- `deg`, `synDiv_deg_exact`: a degree that counts what matters, and drops by
  exactly one when a linear factor is divided out. The *exact* drop rather than
  the inequality, because over a finite field vanishing everywhere is not being
  the zero polynomial, and the inequality left that collapse open.
- `roots_lt_deg`: a polynomial has fewer roots than significant coefficients.
- `eval_eq_of_agree`: two polynomials agreeing at enough points agree
  everywhere.
- `basisP`, `interpP`, `eval_interpP`, `deg_interpP`: the Lagrange interpolant
  written as a polynomial, so it can be one of those two.
- `unisolvence`: the interpolant through enough points on a message polynomial
  *is* that polynomial, everywhere. -/

/-! ## Lagrange interpolation

Reed-Solomon decoding is interpolation: from enough surviving `(x, y)` pairs,
recover the value the encoding polynomial takes at the points that were lost.

What a decoder needs is that **value**, not the polynomial's coefficients. So
interpolation is defined here as an evaluation directly, and polynomial
multiplication never has to exist at all. The coefficient form would need it,
along with proofs that it distributes and associates. That is not a
shortcut taken to save proof effort; it is the operation the decoder performs.

Subtraction never appears, because this field has characteristic two: `a - b`
and `a + b` are the same value, and both are `xor`. -/

/-- The Lagrange weight of node `xj` at `x`: the product over the other nodes
`xk` of `(x - xk) / (xj - xk)`.

Nodes equal to `xj` are skipped **by value**. That is what lets the two lemmas
below hold with as few hypotheses as they do. -/
def weight (xs : List Elem) (xj x : Elem) : Elem :=
  xs.foldr
    (fun xk acc =>
      if xk = xj then acc
      else mul acc (mul (add x xk) (inv (add xj xk))))
    one

theorem weight_nil (xj x : Elem) : weight [] xj x = one := rfl

theorem weight_cons (xk : Elem) (xs : List Elem) (xj x : Elem) :
    weight (xk :: xs) xj x =
      (if xk = xj then weight xs xj x
       else mul (weight xs xj x) (mul (add x xk) (inv (add xj xk)))) := rfl

/-- **A node's own weight is one.**

Every factor that survives the skip is `d / d` for a nonzero `d`, which is where
`mul_inv_cancel`, and so the irreducibility of the reduction polynomial, is
actually spent. No distinctness hypothesis is needed: a repeated node is skipped
along with the original. -/
theorem weight_self (xs : List Elem) (xj : Elem) : weight xs xj xj = one := by
  induction xs with
  | nil => rfl
  | cons xk xs ih =>
    rw [weight_cons]
    by_cases h : xk = xj
    · rw [if_pos h]; exact ih
    · rw [if_neg h, ih]
      have hne : add xj xk ≠ 0#16 := add_ne_zero_of_ne (fun e => h e.symm)
      rw [mul_inv_cancel _ hne]
      simp only [one]
      exact mul_one 1#16

/-- **Every other node's weight vanishes at a node.**

The factor contributed by `xi` itself is `(xi - xi) = 0`, and a zero factor
annihilates the product regardless of where in it the zero appears. -/
theorem weight_of_mem_ne (xs : List Elem) (xj xi : Elem)
    (hmem : xi ∈ xs) (hne : xi ≠ xj) : weight xs xj xi = zero := by
  induction xs with
  | nil => cases hmem
  | cons xk xs ih =>
    rw [weight_cons]
    rcases List.mem_cons.mp hmem with h | h
    · have hxk : xk ≠ xj := by rw [← h]; exact hne
      rw [if_neg hxk, ← h, add_self]
      simp only [zero, zero_mul, mul_zero]
    · rw [ih h]
      by_cases hxk : xk = xj
      · rw [if_pos hxk]
      · rw [if_neg hxk]; simp only [zero, zero_mul]

/-! ### The interpolated value

`combine` carries the node list as a separate parameter from the point list, so
that the induction below can consume the points without disturbing the nodes the
weights are taken over. `interp` is the case where they agree. -/

def combine (xs : List Elem) (pts : List (Elem × Elem)) (x : Elem) : Elem :=
  pts.foldr (fun p acc => add acc (mul p.2 (weight xs p.1 x))) zero

theorem combine_cons (xs : List Elem) (p : Elem × Elem)
    (pts : List (Elem × Elem)) (x : Elem) :
    combine xs (p :: pts) x = add (combine xs pts x) (mul p.2 (weight xs p.1 x)) :=
  rfl

/-- The interpolant of a set of points, evaluated at `x`. -/
def interp (pts : List (Elem × Elem)) (x : Elem) : Elem :=
  combine (pts.map Prod.fst) pts x

/-- A sum every one of whose nodes misses `xi` contributes nothing there. -/
theorem combine_eq_zero (xs : List Elem) (pts : List (Elem × Elem)) (xi : Elem)
    (hxi : xi ∈ xs) (h : ∀ p ∈ pts, p.1 ≠ xi) : combine xs pts xi = zero := by
  induction pts with
  | nil => rfl
  | cons p pts ih =>
    rw [combine_cons, ih (fun q hq => h q (List.mem_cons_of_mem _ hq)),
        weight_of_mem_ne xs p.1 xi hxi (fun e => h p (List.mem_cons_self ..) e.symm)]
    simp only [zero, mul_zero, add]
    bv_decide

/-- **The delta property: interpolation reproduces the data it was given.**

This is the statement Reed-Solomon decoding rests on. Distinctness of the nodes
is exactly the hypothesis that makes it true. With a repeated node two terms
both survive, and their sum is the xor of two payloads rather than either
one. -/
theorem combine_at (xs : List Elem) (xi yi : Elem) (hxi : xi ∈ xs) :
    ∀ pts : List (Elem × Elem), (xi, yi) ∈ pts → (pts.map Prod.fst).Nodup →
      combine xs pts xi = yi := by
  intro pts
  induction pts with
  | nil => intro hmem _; cases hmem
  | cons p pts ih =>
    intro hmem hnd
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hp, hnd'⟩ := hnd
    rw [combine_cons]
    rcases List.mem_cons.mp hmem with h | h
    · -- This point *is* the one asked about: it survives, the rest vanish.
      subst h
      have hzero : combine xs pts xi = zero := by
        refine combine_eq_zero xs pts xi hxi ?_
        intro q hq e
        have hq' : q.1 ∈ pts.map Prod.fst := List.mem_map_of_mem hq
        rw [e] at hq'
        exact hp hq'
      rw [hzero, weight_self]
      simp only [one, zero, mul_one, add]
      bv_decide
    · -- Some later point is the one asked about: this term vanishes.
      have hne : xi ≠ p.1 := by
        intro e
        exact hp (by rw [← e]; exact List.mem_map_of_mem h)
      rw [ih h hnd', weight_of_mem_ne xs p.1 xi hxi hne]
      simp only [zero, mul_zero, add]
      bv_decide

/-- The delta property in the form a decoder states it. -/
theorem interp_eq (pts : List (Elem × Elem)) (xi yi : Elem)
    (hmem : (xi, yi) ∈ pts) (hnd : (pts.map Prod.fst).Nodup) :
    interp pts xi = yi :=
  combine_at (pts.map Prod.fst) xi yi (List.mem_map_of_mem hmem) pts hmem hnd

/-! ## The interpolant as a polynomial

`interp` is a sum of Lagrange weights, which is a function of `x` built from the
points. To put it on one side of `eval_eq_of_agree` it has to be a polynomial.
These build it, with exactly the recursion `weight` and `combine` use, so the
evaluation laws are structural rather than clever. -/

/-- The Lagrange basis for node `xj`, as a polynomial. Mirrors `weight`. -/
def basisP (xs : List Elem) (xj : Elem) : Poly :=
  xs.foldr
    (fun xk acc =>
      if xk = xj then acc
      else scaleP (inv (add xj xk)) (mulLin xk acc))
    [one]

theorem basisP_nil (xj : Elem) : basisP [] xj = [one] := rfl

theorem basisP_cons (xk : Elem) (xs : List Elem) (xj : Elem) :
    basisP (xk :: xs) xj =
      (if xk = xj then basisP xs xj
       else scaleP (inv (add xj xk)) (mulLin xk (basisP xs xj))) := rfl

/-- **The basis polynomial evaluates to the weight.** -/
theorem eval_basisP (xs : List Elem) (xj x : Elem) :
    eval (basisP xs xj) x = weight xs xj x := by
  induction xs with
  | nil =>
    simp only [basisP_nil, weight_nil, eval_cons, eval_nil]
    simp only [zero, one]
    have : mul 0#16 x = 0#16 := zero_mul x
    rw [this]
    simp only [add]
    bv_decide
  | cons xk xs ih =>
    rw [basisP_cons, weight_cons]
    by_cases h : xk = xj
    · rw [if_pos h, if_pos h]; exact ih
    · rw [if_neg h, if_neg h, eval_scaleP, eval_mulLin, ih]
      -- d·(a·w) = w·(a·d), which is all the rearrangement this needs.
      have key : ∀ d a w : Elem, mul d (mul a w) = mul w (mul a d) := by
        intro d a w
        rw [mul_comm a d, ← mul_assoc]
        exact mul_comm _ _
      rw [add_comm xk x]
      exact key _ _ _

/-- The interpolant as a polynomial, with the node list carried separately for
the same reason `combine` carries it: so the induction can consume the points
without disturbing the nodes the bases are taken over. -/
def combineP (xs : List Elem) (pts : List (Elem × Elem)) : Poly :=
  pts.foldr (fun p acc => addP acc (scaleP p.2 (basisP xs p.1))) []

def interpP (pts : List (Elem × Elem)) : Poly := combineP (pts.map Prod.fst) pts

theorem eval_combineP (xs : List Elem) (pts : List (Elem × Elem)) (x : Elem) :
    eval (combineP xs pts) x = combine xs pts x := by
  induction pts with
  | nil => rfl
  | cons p ps ih =>
    simp only [combineP, combine, List.foldr_cons, eval_addP, eval_scaleP,
      eval_basisP] at *
    rw [ih]

/-- **The polynomial evaluates to the interpolant**, which is the translation
`eval_eq_of_agree` was waiting for. -/
theorem eval_interpP (pts : List (Elem × Elem)) (x : Elem) :
    eval (interpP pts) x = interp pts x :=
  eval_combineP _ _ x

/-! ### Its degree

The bound `eval_eq_of_agree` needs. Each piece is mechanical; the one that
matters is that a basis skips its own node, which is what keeps the count at the
number of points rather than one more. -/

theorem deg_scaleP (s : Elem) (p : Poly) : deg (scaleP s p) ≤ deg p := by
  induction p with
  | nil => simp [scaleP]
  | cons a p ih =>
    have hsz : mul s zero = zero := mul_zero s
    simp only [scaleP, deg_cons]
    split <;> rename_i h1 <;> split <;> rename_i h2 <;>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1 h2 <;>
      first
        | omega
        | (exfalso
           apply h1
           refine ⟨by omega, ?_⟩
           rw [h2.2]; exact hsz)

theorem deg_mulLin (c : Elem) (p : Poly) : deg (mulLin c p) ≤ deg p + 1 := by
  have h := deg_addP (scaleP c p) (zero :: p)
  have h1 := deg_scaleP c p
  have h2 : deg (zero :: p) ≤ deg p + 1 := by rw [deg_cons]; split <;> omega
  simp only [mulLin]
  omega

/-- Without knowing the node is among them, one more than the count. -/
theorem deg_basisP_weak (xs : List Elem) (xj : Elem) :
    deg (basisP xs xj) ≤ xs.length + 1 := by
  induction xs with
  | nil => simp only [basisP_nil, deg_cons, deg_nil]; split <;> omega
  | cons xk xs ih =>
    rw [basisP_cons]
    split
    · simp only [List.length_cons]; omega
    · have h1 := deg_scaleP (inv (add xj xk)) (mulLin xk (basisP xs xj))
      have h2 := deg_mulLin xk (basisP xs xj)
      simp only [List.length_cons]
      omega

/-- **A basis skips its own node**, so its degree is the number of points rather
than one more. This is the whole reason the bound comes out where it needs to. -/
theorem deg_basisP {xs : List Elem} {xj : Elem} (h : xj ∈ xs) :
    deg (basisP xs xj) ≤ xs.length := by
  induction xs with
  | nil => cases h
  | cons xk xs ih =>
    rw [basisP_cons]
    by_cases hk : xk = xj
    · rw [if_pos hk]
      have := deg_basisP_weak xs xj
      simp only [List.length_cons]; omega
    · rw [if_neg hk]
      have hmem : xj ∈ xs := by
        rcases List.mem_cons.mp h with e | e
        · exact absurd e.symm hk
        · exact e
      have h1 := deg_scaleP (inv (add xj xk)) (mulLin xk (basisP xs xj))
      have h2 := deg_mulLin xk (basisP xs xj)
      have h3 := ih hmem
      simp only [List.length_cons]
      omega

theorem deg_combineP (xs : List Elem) (pts : List (Elem × Elem))
    (h : ∀ p ∈ pts, p.1 ∈ xs) : deg (combineP xs pts) ≤ xs.length := by
  induction pts with
  | nil => simp [combineP]
  | cons p ps ih =>
    simp only [combineP, List.foldr_cons] at *
    have hrec := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hb := deg_basisP (h p (List.mem_cons_self ..))
    have hs := deg_scaleP p.2 (basisP xs p.1)
    have := deg_addP
      (List.foldr (fun p acc => addP acc (scaleP p.2 (basisP xs p.1))) [] ps)
      (scaleP p.2 (basisP xs p.1))
    omega

theorem deg_interpP (pts : List (Elem × Elem)) : deg (interpP pts) ≤ pts.length := by
  have h := deg_combineP (pts.map Prod.fst) pts (fun p hp => List.mem_map_of_mem hp)
  simpa [interpP] using h

/-! ## Unisolvence

The erasure code's central guarantee, and the end of the chain this file has been
building.

Given a message polynomial and enough distinct points on it, the interpolant
through those points *is* that polynomial, everywhere. Not merely at the points
it was handed, which is `interp_eq` and is much weaker: recovering a **lost**
symbol means evaluating at a node the decoder never saw, and that is what this
licenses. -/

theorem unisolvence (p : Poly) (pts : List (Elem × Elem)) (x : Elem)
    (hnd : (pts.map Prod.fst).Nodup)
    (hdeg : deg p ≤ pts.length)
    (hpts : ∀ pt ∈ pts, pt.2 = eval p pt.1) :
    interp pts x = eval p x := by
  rw [← eval_interpP]
  refine eval_eq_of_agree (interpP pts) p (pts.map Prod.fst) hnd ?_ ?_ ?_ x
  · simpa using deg_interpP pts
  · simpa using hdeg
  · intro s hs
    obtain ⟨pt, hpt, rfl⟩ := List.mem_map.mp hs
    rw [eval_interpP]
    rw [interp_eq pts pt.1 pt.2 (by simpa using hpt) hnd]
    exact hpts pt hpt

/-- **What it means for the erasure code.** A codeword the decoder never received
is recovered exactly, not merely consistently.

`interp_eq` says the interpolant reproduces the points it was given, which a
lookup table would also satisfy. This says it agrees with the message polynomial
at every node, including the ones whose codewords were destroyed. -/
theorem recovers_lost (p : Poly) (pts : List (Elem × Elem)) (lost : Elem)
    (hnd : (pts.map Prod.fst).Nodup)
    (hdeg : deg p ≤ pts.length)
    (hpts : ∀ pt ∈ pts, pt.2 = eval p pt.1) :
    interp pts lost = eval p lost :=
  unisolvence p pts lost hnd hdeg hpts

/-! ### A concrete erasure

The delta property says interpolation reproduces the points it was handed. On its
own that is weak: it would be satisfied by a definition that ignored the
polynomial entirely and did table lookup. The claim an erasure code makes is
larger: the surviving symbols determine the *lost* ones.

Below is that claim on one concrete instance, checked by evaluation: a degree-two
message, five symbols, two of them destroyed, recovered from the remaining three.
The general theorem is `unisolvence` above; these remain as executable checks
that the definitions compute what it describes. -/

private def testMsg : Poly := [5#16, 3#16, 8#16]

private def survivors : List (Elem × Elem) :=
  [(2#16, eval testMsg 2#16), (4#16, eval testMsg 4#16), (5#16, eval testMsg 5#16)]

/-- The symbol at node 1 was destroyed. It comes back. -/
example : interp survivors 1#16 = eval testMsg 1#16 := by native_decide

/-- So does the symbol at node 3. -/
example : interp survivors 3#16 = eval testMsg 3#16 := by native_decide

/-- And the survivors themselves are unchanged, which is the delta property
arriving again by a different route. -/
example : interp survivors 4#16 = eval testMsg 4#16 := by native_decide

/-! ## What is proved here

`interp_eq` is proved for all inputs, and so is the recovery of *lost* symbols.

The general statement is **unisolvence**: if `p` has degree below `k` and `pts`
are `k` points on `p` with distinct nodes, then `interp pts x = eval p x` for
every `x`.

`unisolvence` proves it, and `recovers_lost` states what it means for the code: a
codeword the decoder never received is recovered exactly, not merely
consistently. `interp_eq` alone would be satisfied by a lookup table; this is
not. The concrete instances above are not the evidence; they are executable
checks that the definitions compute what the theorems describe. -/

end Model.Polynomial
