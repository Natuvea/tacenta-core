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

namespace Model.Gf65536

/-- An element of the field: sixteen bits, read as a polynomial over GF(2) whose
    coefficients are the bits.

    A `BitVec` rather than a `Nat`, so that the operations below are bit
    operations: their laws are settled one bit at a time, and the kernel evaluates
    them on closed values. That is what makes the laws provable for every input
    rather than sampled.

    Note that `xtime` and `mul` spell `BitVec 16` out rather than writing `Elem`.
    That is left as it was, so that no statement changes. While the laws were
    settled by a solver it was not style: through the abbreviation the solver did
    not recognise the shifts as bitvector operations and reported spurious
    counterexamples. -/
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
    way the derivation labels are, and is recorded in
    `tacenta-spec/CONSTANTS.md` and specified in
    `tacenta-spec/protocol/mlkem-braid.md` rather than settled here. -/
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
the wrong shape for a proof. Interleaved, the symmetry of the product is buried
under a reduction chain.

Split, commutativity is the product's own symmetry, with no reduction in the way,
and distributivity decomposes into two linear halves. Nothing outside this file depends on which form is used, and
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
    form is sixty-five thousand multiplications per inverse. -/
def pow (a : Elem) : Nat → Elem
  | 0 => one
  | n + 1 =>
    let half := pow (mul a a) ((n + 1) / 2)
    if (n + 1) % 2 == 0 then half else mul a half
decreasing_by simp_wf; omega

/-- The multiplicative inverse, by Fermat's little theorem: the group of nonzero
    elements has order `size - 1`, so `a ^ (size - 2)` inverts `a`.

    Zero has no inverse and is returned unchanged; every caller checks for zero
    first, and the inverse law below is stated over nonzero elements only. -/
def inv (a : Elem) : Elem := if a == 0 then 0 else pow a (size - 2)

/-! ## What is established

**All of it, for every input, and checked by the kernel.** The additive laws,
commutativity, distributivity on both sides, associativity, and an inverse for
every nonzero element. This is a field, proved, not assumed. Nothing in this file
rests on a solver or on compiled evaluation.

**The inverses** are established through the multiplicative group: two has order
exactly `size - 1`, which is a closed computation, so its powers are all of the
nonzero elements, and every nonzero element is then an explicit power of two
whose inverse `inv` returns. That doubles as an irreducibility check on the
reduction polynomial: a reducible one would leave some nonzero element a zero
divisor with no inverse for any implementation to return.

## How

Every law is a statement about sixteen-bit values, and enumerating them is out
of reach: `2 ^ 16` cases for one variable and `2 ^ 32` for two, at about two
milliseconds in the kernel for each evaluation of even a sixteen-term bit
expression, and a `decide` over a sixteen-bit variable exhausted memory before it
finished. What works is structure. The operations here are linear over GF(2), meaning they
commute with exclusive or, in each argument separately, and a law about all
values then follows from the law on the sixteen basis elements `1 <<< i`:

- `decomp_eq` and `linear_ext_w`: a linear map is determined by its values on
  the basis elements. A law between two maps that are linear in one argument is
  reduced to sixteen closed cases, which the kernel evaluates directly;
- the carry-less product is linear in each argument (`clmul_linear`,
  `clmul_linear_left`), by writing each of its sixteen terms as a conditional
  that is linear in its condition and then rearranging exclusive ors.
  Commutativity is the sixteen by sixteen closed cases on pairs of basis
  elements, by linearity in each argument in turn;
- the reduction is linear because each of its sixteen folds is (`redAt_linear`);
- multiplication is split into a carry-less product and a separate reduction,
  so distributivity decomposes into two linear halves;
- doubling commutes with multiplication, proved for the sixteen basis factors
  and extended to all of them because both sides are linear;
- multiplying by a basis element is doubling repeated, so associativity with a
  basis third factor is that lemma applied that many times, and linearity in the
  third factor gives the general statement.

Exclusive-or arithmetic over a few values is settled one bit at a time: `ext`,
then a case on each of the bits involved. -/

/-! ### Addition

Addition is exclusive or, so its laws are the exclusive-or laws of `BitVec`. -/

theorem add_comm (a b : Elem) : add a b = add b a := by
  simp only [add]; exact BitVec.xor_comm a b

theorem add_assoc (a b c : Elem) : add (add a b) c = add a (add b c) := by
  simp only [add]; exact BitVec.xor_assoc a b c

theorem add_zero (a : Elem) : add a zero = a := by
  simp only [add, zero]; exact BitVec.xor_zero

/-- Addition is its own inverse, which is why nothing in this file subtracts. -/
theorem add_self (a : Elem) : add a a = zero := by
  simp only [add, zero]; exact BitVec.xor_self

/-! ### A linear map is determined by its values on the basis

Everything after this rests on one fact, and on the closed cases the kernel
evaluates. A value is the exclusive or of its set bits (`decomp_eq`), so two
maps that commute with exclusive or and agree on the sixteen single-bit values
agree everywhere. -/

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

/-- The bit of a shifted value that a mask of one keeps. -/
private theorem shift_and_one_iff (a : BitVec 16) (j : Nat) :
    ((a >>> j) &&& 1#16 = 1#16) ↔ a.getLsbD j = true := by
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  simp
  cases h : a.getLsbD j <;> simp [BitVec.ofBool]

private theorem and_one_iff (a : BitVec 16) : (a &&& 1#16 = 1#16) ↔ a.getLsbD 0 = true := by
  simpa using shift_and_one_iff a 0

/-- A conditional value, read at one bit. -/
private theorem ite_bit (c : Prop) [Decidable c] (X : BitVec 16) (i : Nat) (hi : i < 16) :
    (if c then X else 0#16)[i] = (decide c && X[i]) := by
  by_cases h : c <;> simp [h]

theorem decomp_eq (a : BitVec 16) : decomp a = a := by
  simp only [decomp]
  ext i hi
  simp only [BitVec.getElem_xor]
  match i, hi with
  | 0, _ => simp [ite_bit, and_one_iff]
  | 1, _ => simp [ite_bit, and_one_iff]
  | 2, _ => simp [ite_bit, and_one_iff]
  | 3, _ => simp [ite_bit, and_one_iff]
  | 4, _ => simp [ite_bit, and_one_iff]
  | 5, _ => simp [ite_bit, and_one_iff]
  | 6, _ => simp [ite_bit, and_one_iff]
  | 7, _ => simp [ite_bit, and_one_iff]
  | 8, _ => simp [ite_bit, and_one_iff]
  | 9, _ => simp [ite_bit, and_one_iff]
  | 10, _ => simp [ite_bit, and_one_iff]
  | 11, _ => simp [ite_bit, and_one_iff]
  | 12, _ => simp [ite_bit, and_one_iff]
  | 13, _ => simp [ite_bit, and_one_iff]
  | 14, _ => simp [ite_bit, and_one_iff]
  | 15, _ => simp [ite_bit, and_one_iff]
  | n + 16, h => exact absurd h (by omega)

/-- **A linear map is determined by its values on the sixteen basis elements.**

    The bridge from the cases below to a general statement. The target may be any
    width, which the carry-less product (thirty-two bits) needs. -/
theorem linear_ext_w {w : Nat} {f g : BitVec 16 → BitVec w}
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

/-- The sixteen-bit case of `linear_ext_w`. -/
theorem linear_ext {f g : BitVec 16 → BitVec 16}
    (hf : ∀ u v, f (u ^^^ v) = f u ^^^ f v)
    (hg : ∀ u v, g (u ^^^ v) = g u ^^^ g v)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hb : ∀ i : Nat, i < 16 → f (1#16 <<< i) = g (1#16 <<< i)) :
    ∀ a, f a = g a :=
  linear_ext_w hf hg hf0 hg0 hb

/-! ### The carry-less product

Linear in each argument. Each of its sixteen terms is a conditional on one bit of
the multiplier, and a conditional is linear in its condition and in its value. -/

/-- A mask of one keeps a bit, so a masked value is zero or one. -/
private theorem and_one_01 (y : BitVec 16) : y &&& (1 : BitVec 16) = 0 ∨ y &&& (1 : BitVec 16) = 1 := by
  rcases Nat.mod_two_eq_zero_or_one y.toNat with h | h
  · left; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, Nat.and_one_is_mod, h]
  · right; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, Nat.and_one_is_mod, h]

private theorem and_xor_r {w : Nat} (u v z : BitVec w) :
    (u ^^^ v) &&& z = (u &&& z) ^^^ (v &&& z) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_xor]
  cases u[i] <;> cases v[i] <;> cases z[i] <;> rfl

private theorem term_lin (b c : BitVec 16) (i : Nat) (X : BitVec 32) :
    (if ((b ^^^ c) >>> i) &&& 1 == 1 then X else 0)
      = (if (b >>> i) &&& 1 == 1 then X else 0) ^^^ (if (c >>> i) &&& 1 == 1 then X else 0) := by
  have h : ((b ^^^ c) >>> i) &&& (1 : BitVec 16)
      = ((b >>> i) &&& (1 : BitVec 16)) ^^^ ((c >>> i) &&& (1 : BitVec 16)) := by
    rw [BitVec.ushiftRight_xor_distrib, and_xor_r]
  rw [h]
  rcases and_one_01 (b >>> i) with h1 | h1 <;> rcases and_one_01 (c >>> i) with h2 | h2 <;>
    rw [h1, h2] <;> simp

private theorem term_lin0 (b c : BitVec 16) (X : BitVec 32) :
    (if ((b ^^^ c) &&& 1 == 1) then X else 0)
      = (if b &&& 1 == 1 then X else 0) ^^^ (if c &&& 1 == 1 then X else 0) := by
  have h := term_lin b c 0 X
  simpa using h

/-- The product is linear in its second argument. -/
theorem clmul_linear (a b c : BitVec 16) :
    clmul a (b ^^^ c) = clmul a b ^^^ clmul a c := by
  simp only [clmul, term_lin0, term_lin]
  ac_rfl

private theorem ite_xor_split (c : Prop) [Decidable c] (X Y : BitVec 32) :
    (if c then X ^^^ Y else 0) = (if c then X else 0) ^^^ (if c then Y else 0) := by
  by_cases h : c <;> simp [h]

/-- And in its first. -/
theorem clmul_linear_left (u v b : BitVec 16) :
    clmul (u ^^^ v) b = clmul u b ^^^ clmul v b := by
  simp only [clmul, BitVec.setWidth_xor, BitVec.shiftLeft_xor_distrib, ite_xor_split]
  ac_rfl

/-- **Commutativity of the product**, which is what commutativity of the field reduces
to. Linear in each argument, so it is enough on pairs of basis elements. -/
theorem clmul_comm (a b : BitVec 16) : clmul a b = clmul b a := by
  have basis : ∀ i, i < 16 → ∀ j, j < 16 →
      clmul (1#16 <<< j) (1#16 <<< i) = clmul (1#16 <<< i) (1#16 <<< j) := by decide +kernel
  have step : ∀ i, i < 16 → ∀ a, clmul a (1#16 <<< i) = clmul (1#16 <<< i) a := by
    intro i hi
    refine linear_ext_w (f := fun a => clmul a (1#16 <<< i)) (g := fun a => clmul (1#16 <<< i) a)
      ?_ ?_ ?_ ?_ ?_
    · intro u v; exact clmul_linear_left u v _
    · intro u v; exact clmul_linear _ u v
    · simp [clmul]
    · simp [clmul]
    · intro j hj; exact basis i hi j hj
  refine linear_ext_w (f := fun b => clmul a b) (g := fun b => clmul b a) ?_ ?_ ?_ ?_ ?_ b
  · intro u v; exact clmul_linear a u v
  · intro u v; exact clmul_linear_left u v a
  · simp [clmul]
  · simp [clmul]
  · intro i hi; exact step i hi a

theorem mul_comm (a b : BitVec 16) : mul a b = mul b a := by
  simp only [mul, clmul_comm]

/-! ### The reduction

Linear: each of the sixteen folds adds the reduction polynomial when one bit is set, and the bit
of a sum is the sum of the bits. -/

private theorem and_one_01_32 (y : BitVec 32) : y &&& (1 : BitVec 32) = 0 ∨ y &&& (1 : BitVec 32) = 1 := by
  rcases Nat.mod_two_eq_zero_or_one y.toNat with h | h
  · left; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, Nat.and_one_is_mod, h]
  · right; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, Nat.and_one_is_mod, h]

/-- One fold of the reduction is linear. -/
theorem redAt_linear (u v : BitVec 32) (i : Nat) :
    redAt (u ^^^ v) i = redAt u i ^^^ redAt v i := by
  unfold redAt
  have h : ((u ^^^ v) >>> i) &&& (1 : BitVec 32)
      = ((u >>> i) &&& (1 : BitVec 32)) ^^^ ((v >>> i) &&& (1 : BitVec 32)) := by
    rw [BitVec.ushiftRight_xor_distrib, and_xor_r]
  rw [h]
  generalize (0x1100B#32 <<< (i - 16)) = c
  rcases and_one_01_32 (u >>> i) with h1 | h1 <;> rcases and_one_01_32 (v >>> i) with h2 | h2 <;>
    rw [h1, h2] <;> simp <;>
    (ext j hj; simp only [BitVec.getElem_xor]; cases u[j] <;> cases v[j] <;> cases c[j] <;> rfl)

/-- The reduction is linear: a chain of conditional exclusive ors is one. -/
theorem reduce_linear (u v : BitVec 32) :
    reduce (u ^^^ v) = reduce u ^^^ reduce v := by
  simp only [reduce, redAt_linear]
  simp [BitVec.setWidth_xor]

/-- **Distributivity decomposes.** Each half is linear on its own. -/
theorem mul_distrib (a b c : BitVec 16) :
    mul a (b ^^^ c) = mul a b ^^^ mul a c := by
  simp only [mul, clmul_linear, reduce_linear]

/-- And on the other side, from commutativity. -/
theorem mul_distrib_right (a b c : BitVec 16) :
    mul (a ^^^ b) c = mul a c ^^^ mul b c := by
  rw [mul_comm, mul_distrib, mul_comm c a, mul_comm c b]

/-! ### Zero, one and doubling -/

theorem mul_zero (a : BitVec 16) : mul a 0#16 = 0#16 := by
  simp [mul, clmul, reduce, redAt]

theorem zero_mul (a : BitVec 16) : mul 0#16 a = 0#16 := by
  rw [mul_comm]; exact mul_zero a

theorem mul_one (a : BitVec 16) : mul a 1#16 = a := by
  have basis : ∀ i, i < 16 → mul (1#16 <<< i) 1#16 = 1#16 <<< i := by decide +kernel
  exact linear_ext (f := fun a => mul a 1#16) (g := fun a => a)
    (fun u v => mul_distrib_right u v 1#16) (fun _ _ => rfl) (zero_mul 1#16) rfl basis a

theorem one_mul (a : BitVec 16) : mul 1#16 a = a := by
  rw [mul_comm]; exact mul_one a

/-- Doubling is linear, as multiplication by two. -/
theorem xtime_linear (u v : BitVec 16) : xtime (u ^^^ v) = xtime u ^^^ xtime v :=
  mul_distrib_right u v 2#16

theorem xtime_zero : xtime 0#16 = 0#16 := zero_mul 2#16

/-- A value shifted down fifteen places is zero or one. -/
private theorem shr15_01 (y : BitVec 16) : y >>> 15 = 0 ∨ y >>> 15 = 1 := by
  have h : y.toNat / 2 ^ 15 < 2 := by
    have := y.isLt
    omega
  rcases (by omega : y.toNat / 2 ^ 15 = 0 ∨ y.toNat / 2 ^ 15 = 1) with h0 | h1
  · left; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h0]
  · right; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h1]

/-- The closed form of doubling, as a function. -/
private def xtimeRhs (a : BitVec 16) : BitVec 16 :=
  (a <<< 1) ^^^ (if a >>> 15 == 1#16 then 0x100B#16 else 0#16)

/-- Doubling in closed form, so a shift and a fold take the place of a product. -/
theorem xtime_eq (a : BitVec 16) :
    xtime a = (a <<< 1) ^^^ (if a >>> 15 == 1#16 then 0x100B#16 else 0#16) := by
  have basis : ∀ i, i < 16 → xtime (1#16 <<< i) = xtimeRhs (1#16 <<< i) := by
    decide +kernel
  have hlin : ∀ u v, xtimeRhs (u ^^^ v) = xtimeRhs u ^^^ xtimeRhs v := by
    intro u v
    unfold xtimeRhs
    have h : (u ^^^ v) >>> 15 = u >>> 15 ^^^ v >>> 15 := BitVec.ushiftRight_xor_distrib u v 15
    rw [h, BitVec.shiftLeft_xor_distrib]
    rcases shr15_01 u with h1 | h1 <;> rcases shr15_01 v with h2 | h2 <;> rw [h1, h2] <;>
      simp <;> first
        | ac_rfl
        | (generalize u <<< 1 = p; generalize v <<< 1 = q; generalize (0x100B#16 : BitVec 16) = c
           ext j hj; simp only [BitVec.getElem_xor]
           cases p[j] <;> cases q[j] <;> cases c[j] <;> rfl)
  exact linear_ext (f := xtime) (g := xtimeRhs) xtime_linear hlin xtime_zero (by decide +kernel) basis a

/-! Sixteen basis cases. Each has a constant factor `1 <<< i`; the kernel evaluates the
sixteen by sixteen closed cases once, and linearity in the other argument does the rest. -/

private theorem xtime_mul_basis_gen (i : Nat) (hi : i < 16) (b : BitVec 16) :
    xtime (mul (1#16 <<< i) b) = mul (1#16 <<< i) (xtime b) := by
  have basis : ∀ i, i < 16 → ∀ j, j < 16 →
      xtime (mul (1#16 <<< i) (1#16 <<< j)) = mul (1#16 <<< i) (xtime (1#16 <<< j)) := by
    decide +kernel
  refine linear_ext (f := fun b => xtime (mul (1#16 <<< i) b))
    (g := fun b => mul (1#16 <<< i) (xtime b)) ?_ ?_ ?_ ?_ ?_ b
  · intro u v; simp only [mul_distrib, xtime_linear]
  · intro u v; simp only [mul_distrib, xtime_linear]
  · show xtime (mul (1#16 <<< i) 0#16) = 0#16
    simp only [mul_zero, xtime_zero]
  · show mul (1#16 <<< i) (xtime 0#16) = 0#16
    simp only [xtime_zero, mul_zero]
  · intro j hj; exact basis i hi j hj

theorem xtime_mul_basis_0 (b : BitVec 16) :
    xtime (mul (1#16 <<< 0) b) = mul (1#16 <<< 0) (xtime b) :=
  xtime_mul_basis_gen 0 (by omega) b

theorem xtime_mul_basis_1 (b : BitVec 16) :
    xtime (mul (1#16 <<< 1) b) = mul (1#16 <<< 1) (xtime b) :=
  xtime_mul_basis_gen 1 (by omega) b

theorem xtime_mul_basis_2 (b : BitVec 16) :
    xtime (mul (1#16 <<< 2) b) = mul (1#16 <<< 2) (xtime b) :=
  xtime_mul_basis_gen 2 (by omega) b

theorem xtime_mul_basis_3 (b : BitVec 16) :
    xtime (mul (1#16 <<< 3) b) = mul (1#16 <<< 3) (xtime b) :=
  xtime_mul_basis_gen 3 (by omega) b

theorem xtime_mul_basis_4 (b : BitVec 16) :
    xtime (mul (1#16 <<< 4) b) = mul (1#16 <<< 4) (xtime b) :=
  xtime_mul_basis_gen 4 (by omega) b

theorem xtime_mul_basis_5 (b : BitVec 16) :
    xtime (mul (1#16 <<< 5) b) = mul (1#16 <<< 5) (xtime b) :=
  xtime_mul_basis_gen 5 (by omega) b

theorem xtime_mul_basis_6 (b : BitVec 16) :
    xtime (mul (1#16 <<< 6) b) = mul (1#16 <<< 6) (xtime b) :=
  xtime_mul_basis_gen 6 (by omega) b

theorem xtime_mul_basis_7 (b : BitVec 16) :
    xtime (mul (1#16 <<< 7) b) = mul (1#16 <<< 7) (xtime b) :=
  xtime_mul_basis_gen 7 (by omega) b

theorem xtime_mul_basis_8 (b : BitVec 16) :
    xtime (mul (1#16 <<< 8) b) = mul (1#16 <<< 8) (xtime b) :=
  xtime_mul_basis_gen 8 (by omega) b

theorem xtime_mul_basis_9 (b : BitVec 16) :
    xtime (mul (1#16 <<< 9) b) = mul (1#16 <<< 9) (xtime b) :=
  xtime_mul_basis_gen 9 (by omega) b

theorem xtime_mul_basis_10 (b : BitVec 16) :
    xtime (mul (1#16 <<< 10) b) = mul (1#16 <<< 10) (xtime b) :=
  xtime_mul_basis_gen 10 (by omega) b

theorem xtime_mul_basis_11 (b : BitVec 16) :
    xtime (mul (1#16 <<< 11) b) = mul (1#16 <<< 11) (xtime b) :=
  xtime_mul_basis_gen 11 (by omega) b

theorem xtime_mul_basis_12 (b : BitVec 16) :
    xtime (mul (1#16 <<< 12) b) = mul (1#16 <<< 12) (xtime b) :=
  xtime_mul_basis_gen 12 (by omega) b

theorem xtime_mul_basis_13 (b : BitVec 16) :
    xtime (mul (1#16 <<< 13) b) = mul (1#16 <<< 13) (xtime b) :=
  xtime_mul_basis_gen 13 (by omega) b

theorem xtime_mul_basis_14 (b : BitVec 16) :
    xtime (mul (1#16 <<< 14) b) = mul (1#16 <<< 14) (xtime b) :=
  xtime_mul_basis_gen 14 (by omega) b

theorem xtime_mul_basis_15 (b : BitVec 16) :
    xtime (mul (1#16 <<< 15) b) = mul (1#16 <<< 15) (xtime b) :=
  xtime_mul_basis_gen 15 (by omega) b

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

/-! Multiplying by a basis element is doubling that many times: linear in the other factor,
so the sixteen by sixteen closed cases settle it. -/

private theorem xtIter_linear (k : Nat) (u v : BitVec 16) :
    xtIter k (u ^^^ v) = xtIter k u ^^^ xtIter k v := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [xtIter, ih, xtime_linear]

private theorem xtIter_zero (k : Nat) : xtIter k 0#16 = 0#16 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [xtIter, ih, xtime_zero]

private theorem mul_pow_gen (i : Nat) (hi : i < 16) (x : BitVec 16) :
    mul x (1#16 <<< i) = xtIter i x := by
  have basis : ∀ i, i < 16 → ∀ j, j < 16 →
      mul (1#16 <<< j) (1#16 <<< i) = xtIter i (1#16 <<< j) := by decide +kernel
  refine linear_ext (f := fun x => mul x (1#16 <<< i)) (g := fun x => xtIter i x)
    (fun u v => mul_distrib_right u v _) (fun u v => xtIter_linear i u v)
    (zero_mul _) (xtIter_zero i) (fun j hj => basis i hi j hj) x

theorem mul_pow_0 (x : BitVec 16) : mul x (1#16 <<< 0) = xtIter 0 x :=
  mul_pow_gen 0 (by omega) x

theorem mul_pow_1 (x : BitVec 16) : mul x (1#16 <<< 1) = xtIter 1 x :=
  mul_pow_gen 1 (by omega) x

theorem mul_pow_2 (x : BitVec 16) : mul x (1#16 <<< 2) = xtIter 2 x :=
  mul_pow_gen 2 (by omega) x

theorem mul_pow_3 (x : BitVec 16) : mul x (1#16 <<< 3) = xtIter 3 x :=
  mul_pow_gen 3 (by omega) x

theorem mul_pow_4 (x : BitVec 16) : mul x (1#16 <<< 4) = xtIter 4 x :=
  mul_pow_gen 4 (by omega) x

theorem mul_pow_5 (x : BitVec 16) : mul x (1#16 <<< 5) = xtIter 5 x :=
  mul_pow_gen 5 (by omega) x

theorem mul_pow_6 (x : BitVec 16) : mul x (1#16 <<< 6) = xtIter 6 x :=
  mul_pow_gen 6 (by omega) x

theorem mul_pow_7 (x : BitVec 16) : mul x (1#16 <<< 7) = xtIter 7 x :=
  mul_pow_gen 7 (by omega) x

theorem mul_pow_8 (x : BitVec 16) : mul x (1#16 <<< 8) = xtIter 8 x :=
  mul_pow_gen 8 (by omega) x

theorem mul_pow_9 (x : BitVec 16) : mul x (1#16 <<< 9) = xtIter 9 x :=
  mul_pow_gen 9 (by omega) x

theorem mul_pow_10 (x : BitVec 16) : mul x (1#16 <<< 10) = xtIter 10 x :=
  mul_pow_gen 10 (by omega) x

theorem mul_pow_11 (x : BitVec 16) : mul x (1#16 <<< 11) = xtIter 11 x :=
  mul_pow_gen 11 (by omega) x

theorem mul_pow_12 (x : BitVec 16) : mul x (1#16 <<< 12) = xtIter 12 x :=
  mul_pow_gen 12 (by omega) x

theorem mul_pow_13 (x : BitVec 16) : mul x (1#16 <<< 13) = xtIter 13 x :=
  mul_pow_gen 13 (by omega) x

theorem mul_pow_14 (x : BitVec 16) : mul x (1#16 <<< 14) = xtIter 14 x :=
  mul_pow_gen 14 (by omega) x

theorem mul_pow_15 (x : BitVec 16) : mul x (1#16 <<< 15) = xtIter 15 x :=
  mul_pow_gen 15 (by omega) x

/-- **Associativity.** The last field law.

    Assembled from statements with one product and a constant factor, joined by
    linearity. No step below mentions two products at once. -/
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

example : ∀ a : Elem, mul a one = a := fun a => mul_one a

example : ∀ a : Elem, mul one a = a := fun a => one_mul a

example : ∀ a : Elem, mul a zero = zero := fun a => mul_zero a

/-- Two fixed points on the reduction, because a wrong reduction step is the
mistake this implementation is most likely to contain and it would not show up
in the identity checks above. -/
example : xtime 0x8000#16 = 0x100B#16 := by decide +kernel

example : xtime 0x4000#16 = 0x8000#16 := by decide +kernel

example : mul 2#16 0x8000#16 = 0x100B#16 := by decide +kernel

/-! ### Inverses, through the multiplicative group

Every nonzero element is a power of `2#16`, and `2#16` has order `65535`, so
raising any nonzero element to `65534` gives its inverse. The kernel checks this
without enumerating the field: five closed powers of `2#16` are evaluated, and
the rest is the algebra above, a greatest common divisor argument, and a
pigeonhole count over a list it never builds. -/

/-- Powers by repeated multiplication, the definition the algebra below reasons
about. `pow` computes the same function by squaring. -/
def natPow (a : Elem) : Nat → Elem
  | 0 => one
  | k + 1 => mul a (natPow a k)

theorem natPow_add (a : Elem) (m n : Nat) :
    natPow a (m + n) = mul (natPow a m) (natPow a n) := by
  induction m with
  | zero => simp only [Nat.zero_add, natPow, one, one_mul]
  | succ m ih =>
    rw [Nat.add_right_comm]
    simp only [natPow, ih, mul_assoc]

theorem natPow_one_base (k : Nat) : natPow one k = one := by
  induction k with
  | zero => rfl
  | succ k ih => rw [natPow, ih]; exact mul_one one

theorem natPow_mul (a : Elem) (m n : Nat) :
    natPow a (m * n) = natPow (natPow a m) n := by
  induction n with
  | zero => simp only [Nat.mul_zero, natPow]
  | succ n ih =>
    rw [Nat.mul_add_one, natPow_add, ih]
    simp only [natPow]
    exact mul_comm _ _

/-- One squaring step: the identity both square-and-multiply definitions follow. -/
theorem natPow_halve (a : Elem) (n : Nat) :
    natPow a n = if n % 2 == 0 then natPow (mul a a) (n / 2)
      else mul a (natPow (mul a a) (n / 2)) := by
  have hsq : natPow a 2 = mul a a := by simp only [natPow, one, mul_one]
  rw [← hsq, ← natPow_mul]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp only [h]
    simp only [BEq.rfl, if_true]
    congr 1
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rw [h, if_neg (by decide), show (2 * k + 1) / 2 = k by omega]
    rfl

theorem pow_eq_natPow (n : Nat) : ∀ a : Elem, pow a n = natPow a n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro a
    cases n with
    | zero => rw [pow.eq_1]; rfl
    | succ n =>
      rw [pow.eq_2, natPow_halve a (n + 1), ih ((n + 1) / 2) (by omega)]

/-- Square-and-multiply with explicit fuel, so that the kernel can evaluate it on
closed arguments. -/
def powF : Nat → Elem → Nat → Elem
  | 0, _, _ => one
  | f + 1, a, n => if n == 0 then one else
      let half := powF f (mul a a) (n / 2)
      if n % 2 == 0 then half else mul a half

theorem powF_eq (f : Nat) :
    ∀ (a : Elem) (n : Nat), n < 2 ^ f → powF f a n = natPow a n := by
  induction f with
  | zero =>
    intro a n h
    have : n = 0 := by simp only [Nat.pow_zero] at h; omega
    subst this
    rfl
  | succ f ih =>
    intro a n h
    by_cases hn : n = 0
    · subst hn; rfl
    · rw [natPow_halve a n, ← ih (mul a a) (n / 2) (by rw [Nat.pow_succ] at h; omega)]
      simp only [powF]
      rw [if_neg (by simpa using hn)]

/-- The five closed facts, each evaluated by the kernel through `powF`. With the
order bound below they say `2#16` has order exactly `65535 = 3 * 5 * 17 * 257`:
the other four exponents are `65535 / 3`, `/ 5`, `/ 17` and `/ 257`. -/
theorem gen_order : natPow 2#16 65535 = one := by
  rw [← powF_eq 20 _ _ (by decide)]; decide +kernel

theorem gen_ne_21845 : natPow 2#16 21845 ≠ one := by
  rw [← powF_eq 20 _ _ (by decide)]; decide +kernel

theorem gen_ne_13107 : natPow 2#16 13107 ≠ one := by
  rw [← powF_eq 20 _ _ (by decide)]; decide +kernel

theorem gen_ne_3855 : natPow 2#16 3855 ≠ one := by
  rw [← powF_eq 20 _ _ (by decide)]; decide +kernel

theorem gen_ne_255 : natPow 2#16 255 ≠ one := by
  rw [← powF_eq 20 _ _ (by decide)]; decide +kernel

/-- The exponents at which a power of `a` is one are closed under the remainder,
so under the greatest common divisor. -/
theorem natPow_mod_of_one (a : Elem) {m n : Nat} (hm : natPow a m = one)
    (hn : natPow a n = one) : natPow a (n % m) = one := by
  have h1 : natPow a (m * (n / m)) = one := by rw [natPow_mul, hm, natPow_one_base]
  have h2 : natPow a n = mul (natPow a (n % m)) (natPow a (m * (n / m))) := by
    rw [← natPow_add, Nat.mod_add_div n m]
  rw [h1, hn] at h2
  exact (h2.trans (mul_one _)).symm

theorem natPow_gcd_of_one (a : Elem) (m n : Nat) :
    natPow a m = one → natPow a n = one → natPow a (Nat.gcd m n) = one := by
  refine Nat.gcd.induction (P := fun m n =>
    natPow a m = one → natPow a n = one → natPow a (Nat.gcd m n) = one) m n ?_ ?_
  · intro n _ hn
    rw [Nat.gcd_zero_left]
    exact hn
  · intro m n _ ih hm hn
    rw [Nat.gcd_rec]
    exact ih (natPow_mod_of_one a hm hn) hm

/-- Every proper divisor of `65535 = 3 * 5 * 17 * 257` divides `65535 / p` for
one of its four prime factors `p`. Two kernel checks of 256 cases each: one
of a divisor and its cofactor is below 256. -/
theorem dvd_maximal_divisor (e : Nat) (he : e ∣ 65535) (hlt : e < 65535) :
    e ∣ 21845 ∨ e ∣ 13107 ∨ e ∣ 3855 ∨ e ∣ 255 := by
  have small : ∀ e, e < 256 → 65535 % e = 0 →
      (21845 % e = 0 ∨ 13107 % e = 0 ∨ 3855 % e = 0 ∨ 255 % e = 0 ∨ e = 0) := by
    decide +kernel
  have large : ∀ c, c < 256 → 2 ≤ c → 65535 % c = 0 →
      (21845 % (65535 / c) = 0 ∨ 13107 % (65535 / c) = 0 ∨
        3855 % (65535 / c) = 0 ∨ 255 % (65535 / c) = 0) := by
    decide +kernel
  obtain ⟨c, hc⟩ := he
  have hc0 : 0 < c := by
    cases c with
    | zero => omega
    | succ c => omega
  have hc1 : c ≠ 1 := by
    intro h1; subst h1; omega
  by_cases hs : e < 256
  · rcases small e hs (Nat.mod_eq_zero_of_dvd ⟨c, hc⟩) with h | h | h | h | h
    · exact Or.inl (Nat.dvd_of_mod_eq_zero h)
    · exact Or.inr (Or.inl (Nat.dvd_of_mod_eq_zero h))
    · exact Or.inr (Or.inr (Or.inl (Nat.dvd_of_mod_eq_zero h)))
    · exact Or.inr (Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero h)))
    · subst h; omega
  · have hcs : c < 256 := by
      refine Nat.lt_of_not_le (fun hle => ?_)
      have := Nat.mul_le_mul (Nat.le_of_not_lt hs) hle
      omega
    have hdiv : 65535 / c = e := Nat.div_eq_of_eq_mul_left hc0 hc
    have hmod : 65535 % c = 0 := Nat.mod_eq_zero_of_dvd ⟨e, by rw [hc, Nat.mul_comm]⟩
    rcases large c hcs (by omega) hmod with h | h | h | h <;> rw [hdiv] at h
    · exact Or.inl (Nat.dvd_of_mod_eq_zero h)
    · exact Or.inr (Or.inl (Nat.dvd_of_mod_eq_zero h))
    · exact Or.inr (Or.inr (Or.inl (Nat.dvd_of_mod_eq_zero h)))
    · exact Or.inr (Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero h)))

/-- `2#16` has multiplicative order exactly `65535`: no smaller positive power
of it is one. -/
theorem gen_order_min (d : Nat) (h0 : 0 < d) (hd : d < 65535) : natPow 2#16 d ≠ one := by
  intro h
  have hg := natPow_gcd_of_one 2#16 d 65535 h gen_order
  have up : ∀ m, Nat.gcd d 65535 ∣ m → natPow 2#16 m = one := by
    intro m ⟨k, hk⟩
    rw [hk, natPow_mul, hg, natPow_one_base]
  rcases dvd_maximal_divisor (Nat.gcd d 65535) (Nat.gcd_dvd_right d 65535)
      (Nat.lt_of_le_of_lt (Nat.gcd_le_left 65535 h0) hd) with h1 | h1 | h1 | h1
  · exact gen_ne_21845 (up _ h1)
  · exact gen_ne_13107 (up _ h1)
  · exact gen_ne_3855 (up _ h1)
  · exact gen_ne_255 (up _ h1)

theorem gen_mul_cofactor (k : Nat) (hk : k ≤ 65535) :
    mul (natPow 2#16 k) (natPow 2#16 (65535 - k)) = one := by
  rw [← natPow_add, Nat.add_sub_cancel' hk, gen_order]

theorem gen_ne_zero (k : Nat) (hk : k ≤ 65535) : natPow 2#16 k ≠ 0#16 := by
  intro h
  have h1 := gen_mul_cofactor k hk
  rw [h, zero_mul] at h1
  exact absurd h1 (by decide)

/-- The first `65535` powers of `2#16` are distinct. -/
theorem gen_inj (i j : Nat) (hij : i < j) (hj : j < 65535) :
    natPow 2#16 i ≠ natPow 2#16 j := by
  intro h
  apply gen_order_min (j - i) (by omega) (by omega)
  have e1 : natPow 2#16 j = mul (natPow 2#16 i) (natPow 2#16 (j - i)) := by
    rw [← natPow_add, Nat.add_sub_cancel' (Nat.le_of_lt hij)]
  have e2 : mul (natPow 2#16 (65535 - i)) (natPow 2#16 i) = one := by
    rw [mul_comm]; exact gen_mul_cofactor i (by omega)
  calc natPow 2#16 (j - i)
      = mul (mul (natPow 2#16 (65535 - i)) (natPow 2#16 i)) (natPow 2#16 (j - i)) := by
        rw [e2]; exact (one_mul _).symm
    _ = mul (natPow 2#16 (65535 - i)) (natPow 2#16 j) := by rw [mul_assoc, ← e1]
    _ = one := by rw [← h, e2]

/-- A duplicate-free list of naturals below `n` has at most `n` entries. -/
theorem nodup_length_le (n : Nat) : ∀ l : List Nat, l.Nodup → (∀ x ∈ l, x < n) →
    l.length ≤ n := by
  induction n with
  | zero =>
    intro l _ hl
    cases l with
    | nil => exact Nat.le_refl 0
    | cons x t => exact absurd (hl x (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | succ n ih =>
    intro l hnd hl
    by_cases hn : n ∈ l
    · have h1 := ih (l.erase n) (hnd.erase n) (by
        intro x hx
        have h2 := (List.Nodup.mem_erase_iff hnd).mp hx
        have := hl x h2.2
        omega)
      rw [List.length_erase_of_mem hn] at h1
      omega
    · have h1 := ih l hnd (by
        intro x hx
        have := hl x hx
        have : x ≠ n := fun e => hn (e ▸ hx)
        omega)
      omega

/-- The pigeonhole step: a duplicate-free list of exactly `n` naturals below `n`
contains every natural below `n`. -/
theorem nodup_full (n : Nat) : ∀ l : List Nat, l.Nodup → (∀ x ∈ l, x < n) →
    l.length = n → ∀ y, y < n → y ∈ l := by
  induction n with
  | zero => intro _ _ _ _ y hy; exact absurd hy (Nat.not_lt_zero _)
  | succ n ih =>
    intro l hnd hl hlen y hy
    by_cases hn : n ∈ l
    · by_cases hyn : y = n
      · subst hyn; exact hn
      · have h1 := ih (l.erase n) (hnd.erase n) (by
          intro x hx
          have h2 := (List.Nodup.mem_erase_iff hnd).mp hx
          have := hl x h2.2
          omega) (by rw [List.length_erase_of_mem hn]; omega) y (by omega)
        exact List.mem_of_mem_erase h1
    · exfalso
      have h1 := nodup_length_le n l hnd (by
        intro x hx
        have := hl x hx
        have : x ≠ n := fun e => hn (e ▸ hx)
        omega)
      omega

/-- Every nonzero element is a power of `2#16`. -/
theorem gen_surj (a : Elem) (ha : a ≠ 0#16) : ∃ k, k < 65535 ∧ natPow 2#16 k = a := by
  have hnd : (0 :: (List.range 65535).map (fun k => (natPow 2#16 k).toNat)).Nodup := by
    rw [List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
      exact gen_ne_zero k (Nat.le_of_lt (List.mem_range.mp hk)) (BitVec.eq_of_toNat_eq he)
    · unfold List.Nodup
      rw [List.pairwise_map]
      refine List.Pairwise.imp_of_mem (fun {i j} _ hj hij => ?_) List.pairwise_lt_range
      intro he
      exact gen_inj i j hij (List.mem_range.mp hj) (BitVec.eq_of_toNat_eq he)
  have hb : ∀ x ∈ (0 :: (List.range 65535).map (fun k => (natPow 2#16 k).toNat)),
      x < 65536 := by
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · omega
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp h
      exact (natPow 2#16 k).isLt
  have hlen : (0 :: (List.range 65535).map (fun k => (natPow 2#16 k).toNat)).length
      = 65536 := by
    -- `rw`, not `simp only`: the proof `simp only` builds here made the kernel
    -- unfold `List.range 65535`, which took seven to eleven seconds.
    rw [List.length_cons, List.length_map, List.length_range]
  rcases List.mem_cons.mp (nodup_full 65536 _ hnd hb hlen a.toNat a.isLt) with h | h
  · exact absurd (BitVec.eq_of_toNat_eq h) ha
  · obtain ⟨k, hk, he⟩ := List.mem_map.mp h
    exact ⟨k, List.mem_range.mp hk, BitVec.eq_of_toNat_eq he⟩


/-- **Every nonzero element has an inverse, and `inv` returns it.** All of them.
This is the fact interpolation needs, and it is also what says the reduction
polynomial is irreducible.

    A theorem rather than an example, because interpolation has to *use* it: a
    Lagrange basis divides by the difference of two distinct points, and that
    division is only a division if this holds. -/
theorem mul_inv_cancel : ∀ a : Elem, a ≠ 0#16 → mul a (inv a) = one := by
  intro a ha
  obtain ⟨k, _, rfl⟩ := gen_surj a ha
  have hinv : inv (natPow 2#16 k) = pow (natPow 2#16 k) 65534 := by
    simp only [inv, size]
    rw [if_neg (by simpa using ha)]
  rw [hinv, pow_eq_natPow, ← natPow_mul, ← natPow_add,
    show k + k * 65534 = 65535 * k by omega, natPow_mul, gen_order, natPow_one_base]

/-- The same, the other way round, from commutativity. -/
theorem inv_mul_cancel (a : Elem) (h : a ≠ 0#16) : mul (inv a) a = one := by
  rw [mul_comm]; exact mul_inv_cancel a h

/-- In this field subtraction is addition, so two values differ exactly when
their sum is nonzero. What a Lagrange denominator needs. -/
theorem xor_eq_zero_iff (a b : Elem) : a ^^^ b = 0#16 ↔ a = b := by
  constructor
  · intro h
    have h2 := congrArg (fun x => x ^^^ b) h
    simpa [BitVec.xor_assoc] using h2
  · rintro rfl
    exact BitVec.xor_self

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
