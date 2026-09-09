/-
Model.Gf65536: arithmetic in GF(2^16), the field the erasure coding is defined
over, written from the published ML-KEM Braid specification pinned in the
conformance manifest, Section 2.2.

This is the bottom of the post-quantum ratchet's stack and the only part of it
that is pure mathematics. The agreement sends encapsulation keys and ciphertexts
far too large for one message, so they travel as a stream of chunks produced by
a Reed-Solomon code, and that code is polynomial interpolation over this field.

Nothing here is secret. The values encoded are public key material and public
ciphertext, so unlike every other primitive in this repository there is no
constant-time obligation, and the operations may branch on their inputs.
-/

import Std.Tactic.BVDecide

namespace Model.Gf65536

/-- An element of the field: sixteen bits, read as a polynomial over GF(2) whose
    coefficients are the bits.

    A `BitVec` rather than a `Nat`, so that the operations below are a circuit a
    solver can see. That is not presentation: it is what makes distributivity
    provable for every input rather than sampled.

    Note that `xtime` and `mul` spell `BitVec 16` out rather than writing `Elem`.
    That is not style. Through the abbreviation the solver does not recognise the
    shifts as bitvector operations, abstracts them as opaque, and reports a
    spurious counterexample -- which reads exactly like a real one. Measured, and
    written here because the next person to tidy those signatures will undo a
    theorem. -/
abbrev Elem := BitVec 16

/-- The field's size, and the number of distinct codewords the erasure code can
    produce before it must repeat. The specification names that consequence
    directly: an attacker who blocks all but a repeated codeword prevents the
    agreement from advancing without having to block everything. -/
def size : Nat := 65536

/-- The reduction polynomial, `x^16 + x^12 + x^3 + x + 1`.

    **Ours, not the specification's.** The published document fixes the field at
    GF(2^16) and does not fix which irreducible polynomial defines it. Two
    implementations that choose differently compute different products and
    cannot decode each other's chunks, so this is wire-sensitive in exactly the
    way the derivation labels are, and is recorded in the conformance manifest
    rather than settled here. -/
def reducer : Nat := 0x1100B

/-- The reduction's low sixteen bits, which is what a carry-out folds back in:
    the `x^16` term is exactly the bit that left. -/
def reducerLow : Elem := 0x100B#16

/-! ## Addition

Addition of polynomials over GF(2) is coefficient-wise addition modulo two,
which is exclusive or. It is its own inverse, so subtraction is the same
operation, which is why nothing below ever needs one. -/

def add (a b : Elem) : Elem := a ^^^ b

def zero : Elem := 0#16
def one : Elem := 1#16

/-! ## Multiplication

Multiply the polynomials and reduce modulo the polynomial above. Carried out one
bit at a time: the accumulator takes a copy of the running term wherever the
multiplier has a set bit, and the running term doubles each step, folding in the
reduction whenever doubling would carry past sixteen bits. -/

/-! ### Multiplication, in two halves

Split deliberately, and the split is what makes the laws provable.

An implementation would interleave these: multiply one bit and reduce, sixteen
times, keeping everything in sixteen bits. That is the same function and it is
the wrong shape for a proof. Interleaved, the solver settles distributivity
but not commutativity, because the symmetry is buried under a reduction chain
it cannot see past.

Split, commutativity needs no solver at all and distributivity decomposes into
two easy halves. Nothing outside this file depends on which form is used, and
`Translation.ErasureT3` relates `tacenta-erasure`'s interleaved arithmetic to
this form, so the model takes the form its proofs can use. That is the same
choice made for the ratchet's `receive` and the bundle's optional field. -/

/-- The carry-less product: sixteen shifted copies, XORed, into thirty-two bits
    so nothing is lost. No reduction here at all.

    Commutativity of *this* is what commutativity of the field reduces to, and
    it is easy precisely because there is no reduction in the way. -/
def clmul (a b : BitVec 16) : BitVec 32 :=
  let x := a.zeroExtend 32
  (if b &&& 1 == 1 then x else 0)
  ^^^ (if (b >>> 1) &&& 1 == 1 then x <<< 1 else 0)
  ^^^ (if (b >>> 2) &&& 1 == 1 then x <<< 2 else 0)
  ^^^ (if (b >>> 3) &&& 1 == 1 then x <<< 3 else 0)
  ^^^ (if (b >>> 4) &&& 1 == 1 then x <<< 4 else 0)
  ^^^ (if (b >>> 5) &&& 1 == 1 then x <<< 5 else 0)
  ^^^ (if (b >>> 6) &&& 1 == 1 then x <<< 6 else 0)
  ^^^ (if (b >>> 7) &&& 1 == 1 then x <<< 7 else 0)
  ^^^ (if (b >>> 8) &&& 1 == 1 then x <<< 8 else 0)
  ^^^ (if (b >>> 9) &&& 1 == 1 then x <<< 9 else 0)
  ^^^ (if (b >>> 10) &&& 1 == 1 then x <<< 10 else 0)
  ^^^ (if (b >>> 11) &&& 1 == 1 then x <<< 11 else 0)
  ^^^ (if (b >>> 12) &&& 1 == 1 then x <<< 12 else 0)
  ^^^ (if (b >>> 13) &&& 1 == 1 then x <<< 13 else 0)
  ^^^ (if (b >>> 14) &&& 1 == 1 then x <<< 14 else 0)
  ^^^ (if (b >>> 15) &&& 1 == 1 then x <<< 15 else 0)

/-- Fold the reduction polynomial in at bit `i`, when that bit is set. -/
def redAt (v : BitVec 32) (i : Nat) : BitVec 32 :=
  if (v >>> i) &&& 1 == 1 then v ^^^ (0x1100B#32 <<< (i - 16)) else v

/-- Reduce a thirty-two bit polynomial modulo the field's, highest bit first.
    Order matters: folding at a bit changes lower bits, so a pass upward would
    revisit what it had already cleared. -/
def reduce (v : BitVec 32) : BitVec 16 :=
  let v := redAt v 31; let v := redAt v 30; let v := redAt v 29; let v := redAt v 28
  let v := redAt v 27; let v := redAt v 26; let v := redAt v 25; let v := redAt v 24
  let v := redAt v 23; let v := redAt v 22; let v := redAt v 21; let v := redAt v 20
  let v := redAt v 19; let v := redAt v 18; let v := redAt v 17; let v := redAt v 16
  v.truncate 16

/-- Multiplication in the field: multiply, then reduce. -/
def mul (a b : BitVec 16) : BitVec 16 := reduce (clmul a b)

/-- Doubling, which inversion's square-and-multiply uses. -/
def xtime (a : BitVec 16) : BitVec 16 := mul a 2#16

/-- Exponentiation by squaring. Written this way rather than as repeated
    multiplication because inversion raises to the power `size - 2`: the naive
    form is sixty-five thousand multiplications per inverse, and the exhaustive
    check below performs one inverse for every element in the field. -/
def pow (a : Elem) : Nat → Elem
  | 0 => one
  | n + 1 =>
    let half := pow (mul a a) ((n + 1) / 2)
    if (n + 1) % 2 == 0 then half else mul a half
decreasing_by simp_wf; omega

/-- The multiplicative inverse, by Fermat's little theorem: the group of nonzero
    elements has order `size - 1`, so `a ^ (size - 2)` inverts `a`.

    Zero has no inverse and is returned unchanged; every caller checks for zero
    first, and the exhaustive check below is stated over nonzero elements only. -/
def inv (a : Elem) : Elem := if a == 0 then 0 else pow a (size - 2)

/-! ## What is established

**All of it, for every input.** The additive laws, commutativity, distributivity
on both sides, and associativity. This is a field, proved, not assumed.

**Except the inverses, which are established by exhaustion.** Every nonzero
element has the inverse `inv` returns, all sixty-five thousand five hundred and
thirty-five of them. That doubles as an irreducibility check on the reduction
polynomial: a reducible one would leave some nonzero element a zero divisor with
no inverse for any implementation to return. A reducible polynomial fails this
check.

## How, because the shape is the whole difficulty

The shape of the associativity proof follows a single rule: **a solver settles
statements mentioning one product, and none mentioning two.** Timeout length
does not move it, nor fixing a factor to a constant, nor its own normalisation
for associative-commutative operators.

So nothing here asks it about two. Every solver call in this file has a single
product with the other factor a constant, and the general laws are assembled
from those by linearity:

- multiplication is split into a carry-less product and a separate reduction, so
  commutativity is the product's own symmetry and needs no solver at all;
- distributivity decomposes into two linear halves seen one at a time;
- doubling commutes with multiplication -- proved for sixteen constant factors,
  then extended to all of them because both sides are linear;
- multiplying by a basis element is doubling repeated, so associativity with a
  basis third factor is that lemma applied that many times;
- and linearity in the third factor gives the general statement.

`linear_ext` is the piece that makes the pattern work: a linear map is
determined by its values on the sixteen basis elements. It is worth reaching for
whenever a statement over this field is true but out of a solver's reach.

The route through the multiplicative group -- two is a generator, so every
nonzero element is a power of it -- is unnecessary.
-/

/-! ### Addition

Settled symbolically rather than by enumeration. A `decide` over pairs of
sixteen-bit values is `2 ^ 32` cases and does not terminate in any useful time;
`bv_decide` hands the same statement to a solver, which settles it for every
input at once. The distinction is worth writing down. -/

theorem add_comm (a b : Elem) : add a b = add b a := by
  simp only [add]; bv_decide

theorem add_assoc (a b c : Elem) : add (add a b) c = add a (add b c) := by
  simp only [add]; bv_decide

theorem add_zero (a : Elem) : add a zero = a := by
  simp only [add, zero]; bv_decide

/-- Addition is its own inverse, which is why nothing in this file subtracts. -/
theorem add_self (a : Elem) : add a a = zero := by
  simp only [add, zero]; bv_decide

/-! ### The multiplicative laws

Two of the three, and each is easy only because of the split above.

**Commutativity needs no solver.** The product is symmetric, and reducing a
symmetric thing preserves the symmetry, so it is congruence and nothing more.
The same statement over the interleaved form is out of the solver's reach.

**Distributivity decomposes.** Each half is linear on its own and each is easy
to settle alone; composing them means the solver never sees both at once. Stated
over the interleaved form it was provable too, but only just, and only because
that form happens to suit it. -/

theorem clmul_comm (a b : BitVec 16) : clmul a b = clmul b a := by
  simp only [clmul]
  bv_decide

theorem mul_comm (a b : BitVec 16) : mul a b = mul b a := by
  simp only [mul, clmul_comm]

/-- The product is linear in its second argument. -/
theorem clmul_linear (a b c : BitVec 16) :
    clmul a (b ^^^ c) = clmul a b ^^^ clmul a c := by
  simp only [clmul]
  bv_decide

/-- The reduction is linear: a chain of conditional exclusive ors is one. -/
theorem reduce_linear (u v : BitVec 32) :
    reduce (u ^^^ v) = reduce u ^^^ reduce v := by
  simp only [reduce, redAt]
  bv_decide

theorem mul_distrib (a b c : BitVec 16) :
    mul a (b ^^^ c) = mul a b ^^^ mul a c := by
  simp only [mul, clmul_linear, reduce_linear]

/-- And on the other side, from commutativity. -/
theorem mul_distrib_right (a b c : BitVec 16) :
    mul (a ^^^ b) c = mul a c ^^^ mul b c := by
  rw [mul_comm, mul_distrib, mul_comm c a, mul_comm c b]


/-! ### Associativity

The last law, and the one whose shape matters most. The obstacle is never the
mathematics -- associativity holds on all four thousand and ninety-six
single-bit triples -- but that a solver settles statements mentioning one
product and none mentioning two.

So nothing below ever asks it about two. Every solver call here has a single
product with the other factor a constant, and the general statement is assembled
from those by linearity. -/

/-- Doubling in closed form, so the solver sees a shift and a fold rather than a
product. -/
theorem xtime_eq (a : BitVec 16) :
    xtime a = (a <<< 1) ^^^ (if a >>> 15 == 1#16 then 0x100B#16 else 0#16) := by
  simp only [xtime, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_zero (a : BitVec 16) : mul a 0#16 = 0#16 := by
  simp only [mul, reduce, redAt, clmul]
  bv_decide

theorem zero_mul (a : BitVec 16) : mul 0#16 a = 0#16 := by
  rw [mul_comm]; exact mul_zero a

theorem mul_one (a : BitVec 16) : mul a 1#16 = a := by
  simp only [mul, reduce, redAt, clmul]
  bv_decide

theorem one_mul (a : BitVec 16) : mul 1#16 a = a := by
  rw [mul_comm]; exact mul_one a

/-- Doubling is linear: a shift and a conditional fold both are. -/
theorem xtime_linear (u v : BitVec 16) : xtime (u ^^^ v) = xtime u ^^^ xtime v := by
  simp only [xtime_eq]
  bv_decide

theorem xtime_zero : xtime 0#16 = 0#16 := by
  simp only [xtime_eq]
  bv_decide

/-! Sixteen basis cases. Each has one product and a constant factor, which is
exactly the shape a solver handles. -/

theorem xtime_mul_basis_0 (b : BitVec 16) :
    xtime (mul (1#16 <<< 0) b) = mul (1#16 <<< 0) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_1 (b : BitVec 16) :
    xtime (mul (1#16 <<< 1) b) = mul (1#16 <<< 1) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_2 (b : BitVec 16) :
    xtime (mul (1#16 <<< 2) b) = mul (1#16 <<< 2) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_3 (b : BitVec 16) :
    xtime (mul (1#16 <<< 3) b) = mul (1#16 <<< 3) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_4 (b : BitVec 16) :
    xtime (mul (1#16 <<< 4) b) = mul (1#16 <<< 4) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_5 (b : BitVec 16) :
    xtime (mul (1#16 <<< 5) b) = mul (1#16 <<< 5) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_6 (b : BitVec 16) :
    xtime (mul (1#16 <<< 6) b) = mul (1#16 <<< 6) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_7 (b : BitVec 16) :
    xtime (mul (1#16 <<< 7) b) = mul (1#16 <<< 7) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_8 (b : BitVec 16) :
    xtime (mul (1#16 <<< 8) b) = mul (1#16 <<< 8) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_9 (b : BitVec 16) :
    xtime (mul (1#16 <<< 9) b) = mul (1#16 <<< 9) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_10 (b : BitVec 16) :
    xtime (mul (1#16 <<< 10) b) = mul (1#16 <<< 10) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_11 (b : BitVec 16) :
    xtime (mul (1#16 <<< 11) b) = mul (1#16 <<< 11) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_12 (b : BitVec 16) :
    xtime (mul (1#16 <<< 12) b) = mul (1#16 <<< 12) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_13 (b : BitVec 16) :
    xtime (mul (1#16 <<< 13) b) = mul (1#16 <<< 13) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_14 (b : BitVec 16) :
    xtime (mul (1#16 <<< 14) b) = mul (1#16 <<< 14) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem xtime_mul_basis_15 (b : BitVec 16) :
    xtime (mul (1#16 <<< 15) b) = mul (1#16 <<< 15) (xtime b) := by
  simp only [xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

/-- A value as the exclusive or of its set bits. -/
def decomp (a : BitVec 16) : BitVec 16 :=
  (if (a >>> 0) &&& 1 == 1 then 1#16 <<< 0 else 0)
  ^^^ (if (a >>> 1) &&& 1 == 1 then 1#16 <<< 1 else 0)
  ^^^ (if (a >>> 2) &&& 1 == 1 then 1#16 <<< 2 else 0)
  ^^^ (if (a >>> 3) &&& 1 == 1 then 1#16 <<< 3 else 0)
  ^^^ (if (a >>> 4) &&& 1 == 1 then 1#16 <<< 4 else 0)
  ^^^ (if (a >>> 5) &&& 1 == 1 then 1#16 <<< 5 else 0)
  ^^^ (if (a >>> 6) &&& 1 == 1 then 1#16 <<< 6 else 0)
  ^^^ (if (a >>> 7) &&& 1 == 1 then 1#16 <<< 7 else 0)
  ^^^ (if (a >>> 8) &&& 1 == 1 then 1#16 <<< 8 else 0)
  ^^^ (if (a >>> 9) &&& 1 == 1 then 1#16 <<< 9 else 0)
  ^^^ (if (a >>> 10) &&& 1 == 1 then 1#16 <<< 10 else 0)
  ^^^ (if (a >>> 11) &&& 1 == 1 then 1#16 <<< 11 else 0)
  ^^^ (if (a >>> 12) &&& 1 == 1 then 1#16 <<< 12 else 0)
  ^^^ (if (a >>> 13) &&& 1 == 1 then 1#16 <<< 13 else 0)
  ^^^ (if (a >>> 14) &&& 1 == 1 then 1#16 <<< 14 else 0)
  ^^^ (if (a >>> 15) &&& 1 == 1 then 1#16 <<< 15 else 0)

theorem decomp_eq (a : BitVec 16) : decomp a = a := by
  simp only [decomp]
  bv_decide

/-- **A linear map is determined by its values on the sixteen basis elements.**

    The bridge from the cases above to a general statement, and the piece that
    was missing. Everything after it is assembly. -/
theorem linear_ext {f g : BitVec 16 → BitVec 16}
    (hf : ∀ u v, f (u ^^^ v) = f u ^^^ f v)
    (hg : ∀ u v, g (u ^^^ v) = g u ^^^ g v)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hb : ∀ i : Nat, i < 16 → f (1#16 <<< i) = g (1#16 <<< i)) :
    ∀ a, f a = g a := by
  intro a
  rw [← decomp_eq a]
  simp only [decomp, hf, hg, apply_ite f, apply_ite g, hf0, hg0]
  rw [hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hb 3 (by omega),
      hb 4 (by omega), hb 5 (by omega), hb 6 (by omega), hb 7 (by omega),
      hb 8 (by omega), hb 9 (by omega), hb 10 (by omega), hb 11 (by omega),
      hb 12 (by omega), hb 13 (by omega), hb 14 (by omega), hb 15 (by omega)]

/-- **Doubling commutes with multiplication**, for every pair. Assembled from the
sixteen basis cases by linearity in the first factor. -/
theorem xtime_mul (a b : BitVec 16) : xtime (mul a b) = mul a (xtime b) := by
  refine linear_ext (f := fun x => xtime (mul x b)) (g := fun x => mul x (xtime b))
    ?_ ?_ ?_ ?_ ?_ a
  · intro u v; simp only [mul_distrib_right, xtime_linear]
  · intro u v; simp only [mul_distrib_right]
  · show xtime (mul 0#16 b) = 0#16
    simp only [zero_mul, xtime_zero]
  · show mul 0#16 (xtime b) = 0#16
    simp only [zero_mul]
  · -- `interval_cases` is Mathlib's and this package does without it, so the
    -- sixteen cases are matched by hand.
    intro i hi
    match i, hi with
    | 0, _ => exact xtime_mul_basis_0 b
    | 1, _ => exact xtime_mul_basis_1 b
    | 2, _ => exact xtime_mul_basis_2 b
    | 3, _ => exact xtime_mul_basis_3 b
    | 4, _ => exact xtime_mul_basis_4 b
    | 5, _ => exact xtime_mul_basis_5 b
    | 6, _ => exact xtime_mul_basis_6 b
    | 7, _ => exact xtime_mul_basis_7 b
    | 8, _ => exact xtime_mul_basis_8 b
    | 9, _ => exact xtime_mul_basis_9 b
    | 10, _ => exact xtime_mul_basis_10 b
    | 11, _ => exact xtime_mul_basis_11 b
    | 12, _ => exact xtime_mul_basis_12 b
    | 13, _ => exact xtime_mul_basis_13 b
    | 14, _ => exact xtime_mul_basis_14 b
    | 15, _ => exact xtime_mul_basis_15 b
    | (n + 16), h => exact absurd h (by omega)


/-! ### From doubling to associativity

`mul x (1 <<< k)` is doubling done `k` times, so associativity with a basis
third factor is the doubling lemma applied `k` times. Linearity in the third
factor then gives the general statement. -/

/-- Doubling, iterated. -/
def xtIter : Nat → BitVec 16 → BitVec 16
  | 0, a => a
  | n + 1, a => xtime (xtIter n a)

/-- Iterated doubling commutes with multiplication, by iterating the lemma. -/
theorem xtIter_mul (k : Nat) (a b : BitVec 16) :
    xtIter k (mul a b) = mul a (xtIter k b) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [xtIter, ih, xtime_mul]

/-! Sixteen more one-product calls: multiplying by a basis element is doubling
that many times. -/

theorem mul_pow_0 (x : BitVec 16) : mul x (1#16 <<< 0) = xtIter 0 x := by
  simp only [xtIter, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_1 (x : BitVec 16) : mul x (1#16 <<< 1) = xtIter 1 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_2 (x : BitVec 16) : mul x (1#16 <<< 2) = xtIter 2 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_3 (x : BitVec 16) : mul x (1#16 <<< 3) = xtIter 3 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_4 (x : BitVec 16) : mul x (1#16 <<< 4) = xtIter 4 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_5 (x : BitVec 16) : mul x (1#16 <<< 5) = xtIter 5 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_6 (x : BitVec 16) : mul x (1#16 <<< 6) = xtIter 6 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_7 (x : BitVec 16) : mul x (1#16 <<< 7) = xtIter 7 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_8 (x : BitVec 16) : mul x (1#16 <<< 8) = xtIter 8 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_9 (x : BitVec 16) : mul x (1#16 <<< 9) = xtIter 9 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_10 (x : BitVec 16) : mul x (1#16 <<< 10) = xtIter 10 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_11 (x : BitVec 16) : mul x (1#16 <<< 11) = xtIter 11 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_12 (x : BitVec 16) : mul x (1#16 <<< 12) = xtIter 12 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_13 (x : BitVec 16) : mul x (1#16 <<< 13) = xtIter 13 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_14 (x : BitVec 16) : mul x (1#16 <<< 14) = xtIter 14 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

theorem mul_pow_15 (x : BitVec 16) : mul x (1#16 <<< 15) = xtIter 15 x := by
  simp only [xtIter, xtime_eq, mul, reduce, redAt, clmul]
  bv_decide

/-- **Associativity.** The last field law.

    Assembled entirely from statements a solver could settle -- each with one
    product and a constant factor -- joined by linearity. No call anywhere below
    mentions two products; a formulation that does is beyond the solver. -/
theorem mul_assoc (a b c : BitVec 16) : mul (mul a b) c = mul a (mul b c) := by
  refine linear_ext (f := fun x => mul (mul a b) x) (g := fun x => mul a (mul b x))
    ?_ ?_ ?_ ?_ ?_ c
  · intro u v; simp only [mul_distrib]
  · intro u v; simp only [mul_distrib]
  · show mul (mul a b) 0#16 = 0#16
    simp only [mul_zero]
  · show mul a (mul b 0#16) = 0#16
    simp only [mul_zero]
  · intro i hi
    have key : ∀ k, mul (mul a b) (1#16 <<< k) = xtIter k (mul a b) → 
        mul b (1#16 <<< k) = xtIter k b →
        mul (mul a b) (1#16 <<< k) = mul a (mul b (1#16 <<< k)) := by
      intro k h1 h2
      rw [h1, h2, xtIter_mul]
    match i, hi with
    | 0, _ => exact key 0 (mul_pow_0 _) (mul_pow_0 _)
    | 1, _ => exact key 1 (mul_pow_1 _) (mul_pow_1 _)
    | 2, _ => exact key 2 (mul_pow_2 _) (mul_pow_2 _)
    | 3, _ => exact key 3 (mul_pow_3 _) (mul_pow_3 _)
    | 4, _ => exact key 4 (mul_pow_4 _) (mul_pow_4 _)
    | 5, _ => exact key 5 (mul_pow_5 _) (mul_pow_5 _)
    | 6, _ => exact key 6 (mul_pow_6 _) (mul_pow_6 _)
    | 7, _ => exact key 7 (mul_pow_7 _) (mul_pow_7 _)
    | 8, _ => exact key 8 (mul_pow_8 _) (mul_pow_8 _)
    | 9, _ => exact key 9 (mul_pow_9 _) (mul_pow_9 _)
    | 10, _ => exact key 10 (mul_pow_10 _) (mul_pow_10 _)
    | 11, _ => exact key 11 (mul_pow_11 _) (mul_pow_11 _)
    | 12, _ => exact key 12 (mul_pow_12 _) (mul_pow_12 _)
    | 13, _ => exact key 13 (mul_pow_13 _) (mul_pow_13 _)
    | 14, _ => exact key 14 (mul_pow_14 _) (mul_pow_14 _)
    | 15, _ => exact key 15 (mul_pow_15 _) (mul_pow_15 _)
    | (n + 16), h => exact absurd h (by omega)

/-! ### Identities, and the reduction itself -/

example : ∀ a : Elem, mul a one = a := by native_decide

example : ∀ a : Elem, mul one a = a := by native_decide

example : ∀ a : Elem, mul a zero = zero := by native_decide

/-- Two fixed points on the reduction, because a wrong reduction step is the
mistake this implementation is most likely to contain and it would not show up
in the identity checks above. -/
example : xtime 0x8000#16 = 0x100B#16 := by native_decide

example : xtime 0x4000#16 = 0x8000#16 := by native_decide

example : mul 2#16 0x8000#16 = 0x100B#16 := by native_decide

/-- **Every nonzero element has an inverse, and `inv` returns it.** All of them.
This is the fact interpolation needs, and it is also what says the reduction
polynomial is irreducible.

    A theorem rather than an example, because interpolation has to *use* it: a
    Lagrange basis divides by the difference of two distinct points, and that
    division is only a division if this holds. -/
theorem mul_inv_cancel : ∀ a : Elem, a ≠ 0#16 → mul a (inv a) = one := by
  native_decide

/-- The same, the other way round, from commutativity. -/
theorem inv_mul_cancel (a : Elem) (h : a ≠ 0#16) : mul (inv a) a = one := by
  rw [mul_comm]; exact mul_inv_cancel a h

/-- In this field subtraction is addition, so two values differ exactly when
their sum is nonzero. What a Lagrange denominator needs. -/
theorem xor_eq_zero_iff (a b : Elem) : a ^^^ b = 0#16 ↔ a = b := by bv_decide

theorem add_ne_zero_of_ne {a b : Elem} (h : a ≠ b) : add a b ≠ 0#16 := by
  simp only [add]
  intro hz
  exact h ((xor_eq_zero_iff a b).mp hz)


/-- **No zero divisors**, which is what "field" buys beyond "ring" and what a
root-counting argument spends. Immediate from invertibility, and worth naming
because the argument that needs it is far from here. -/
theorem eq_zero_of_mul_eq_zero {a b : Elem} (ha : a ≠ 0#16) (h : mul a b = 0#16) :
    b = 0#16 := by
  have h1 : mul (inv a) (mul a b) = mul (inv a) 0#16 := by rw [h]
  rw [← mul_assoc, inv_mul_cancel a ha, mul_zero] at h1
  simpa only [one, one_mul] using h1


end Model.Gf65536
