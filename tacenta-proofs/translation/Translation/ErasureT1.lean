import Translation.TacentaErasure

/-!
# T1: panic-freedom of the erasure code's field arithmetic

A function is panic-free when it never returns `fail`: no arithmetic overflow, no
shift past a word, no out-of-bounds index.

This is the crate where the claim is worth most. A decoder consumes codewords an
attacker supplies, and every index and length in it is computed from what they
sent. It is also the crate where the claim is cheapest, because it has **no
dependencies at all** and so no trusted boundary: the theorems below carry no
hypotheses, where the ratchet's carry three.

## What is covered here

All of it. The field arithmetic, interpolation, the chunk helpers, and both
public entry points of each of the encoder and the decoder.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.ErasureT1

open tacenta_erasure

/-- Panic-freedom in the weakest-precondition form the loop lemma uses, matching
`Tacenta.T1.NoPanic` next door. -/
abbrev NoPanic {α : Type} (e : Result α) : Prop := e ⦃ fun _ => True ⦄

theorem noPanic_iff {α : Type} (e : Result α) : NoPanic e ↔ ∃ r, e = ok r := by
  cases e <;> simp [NoPanic]

/-- Addition is a xor and cannot fail. Stated because a reader should not have to
take even that on trust. -/
@[step]
theorem add_no_panic (a b : U16) : gf.add a b ⦃ fun _ => True ⦄ := by
  unfold gf.add; simp

/-- The carry-less product's loop cannot fail.

Three fallible steps, and the guard `i < 16` is what makes each total: shifting
`b` right by `i`, shifting `x` left by `i`, and incrementing `i`. The measure is
how far `i` still has to climb. -/
@[step]
theorem clmul_loop_no_panic (b : U16) (x : U32) (acc : U32) (i : U32)
    (h : i.val ≤ 16) :
    gf.clmul_loop b x acc i ⦃ fun _ => True ⦄ := by
  unfold gf.clmul_loop
  apply loop.spec_decr_nat
    (measure := fun p => 16 - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ 16)
  · rintro ⟨a1, i1⟩ hinv
    unfold gf.clmul_loop.body
    simp only []
    split <;> [skip; simp]
    step*
    split <;> step*
  · exact h

@[step]
theorem clmul_no_panic (a b : U16) : gf.clmul a b ⦃ fun _ => True ⦄ := by
  unfold gf.clmul
  step*

/-- The reduction's loop cannot fail.

The guard is `i >= 16`, and it is doing more work than it looks. It stands
between `i - 16` and an underflow, between `i - 1` and an underflow, and it
bounds the shift `REDUCER <<< (i - 16)` to fifteen places, which is what keeps a
seventeen-bit constant inside a thirty-two-bit word. The measure is `i` itself,
which the body decrements on every turn it takes. -/
@[step]
theorem reduce_loop_no_panic (v : U32) (i : U32) (h : i.val ≤ 31) :
    gf.reduce_loop v i ⦃ fun _ => True ⦄ := by
  unfold gf.reduce_loop
  apply loop.spec_decr_nat
    (measure := fun p => (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ 31)
  · rintro ⟨v1, i1⟩ hinv
    unfold gf.reduce_loop.body
    simp only []
    split <;> [skip; simp]
    step*
    split <;> step*
  · exact h

@[step]
theorem reduce_no_panic (v : U32) : gf.reduce v ⦃ fun _ => True ⦄ := by
  unfold gf.reduce
  step*

/-- **Multiplication cannot fail, for any pair of field elements.**

The statement the rest of the crate leans on: every weight in an interpolation
is a product, and there are `k^2` of them per lane. -/
@[step]
theorem mul_no_panic (a b : U16) : gf.mul a b ⦃ fun _ => True ⦄ := by
  unfold gf.mul
  step*

/-- Exponentiation cannot fail.

Its only fallible steps are two multiplications, both already total, and a shift
by one. The measure is the exponent, which halves on every turn, so the loop
cannot run forever either. -/
@[step]
theorem pow_loop_no_panic (base : U16) (e : U32) (acc : U16) :
    gf.pow_loop base e acc ⦃ fun _ => True ⦄ := by
  unfold gf.pow_loop
  apply loop.spec_decr_nat
    (measure := fun p => (Prod.fst (Prod.snd p)).val)
    (inv := fun _ => True)
  · rintro ⟨b1, e1, a1⟩ _
    unfold gf.pow_loop.body
    simp only []
    split <;> [skip; simp]
    step*
    split <;> step* <;> simp_all <;> scalar_tac
  · trivial

@[step]
theorem pow_no_panic (a : U16) (n : U32) : gf.pow a n ⦃ fun _ => True ⦄ := by
  unfold gf.pow; exact pow_loop_no_panic _ _ _

/-- **Inversion cannot fail**, which is what an interpolation weight divides by.

Zero is returned unchanged rather than raised, so there is no precondition here
at all: the caller's obligation is that the value is nonzero if the result is to
mean anything, and that is a correctness question rather than a panic one. -/
@[step]
theorem inv_no_panic (a : U16) : gf.inv a ⦃ fun _ => True ⦄ := by
  unfold gf.inv
  step*

/-! ## Chunk arithmetic

The two helpers everything else is built from. -/

/-- The one thing in this crate that is not this crate's.

`usize::div_ceil` is a core library function, and Charon does not inline it, so
the translation carries it as an axiom and cannot see that it is total. It is,
and for a reason worth stating: the obvious hand-written form `(size + 31) / 32`
overflows near `usize::MAX`, which is exactly why the standard library provides
this and why the Rust uses it.

Named rather than left implicit, and it is the only assumption anywhere in this
file. It is also a different kind of boundary from the ratchet's: that one wraps
a cryptographic primitive we chose to trust, this one is arithmetic the toolchain
happens not to see through. -/
def DivCeilTotal : Prop :=
  ∀ a b, b.val ≠ 0 → ∃ r, core.num.Usize.div_ceil a b = ok r

/-- The chunk count cannot fail, given that: its one divisor is the constant
`CHUNK_BYTES`, thirty-two, and the premise is discharged from the literal. -/
@[step]
theorem chunk_count_no_panic (hdc : DivCeilTotal) (size : Usize) :
    chunk_count size ⦃ fun _ => True ⦄ := by
  unfold chunk_count
  obtain ⟨r, hr⟩ := hdc size CHUNK_BYTES (by simp only [global_simps]; scalar_tac)
  simp [hr]

/-- Reading a field element out of a chunk cannot fail, for any lane below
sixteen.

The hypothesis is the real content. A chunk is thirty-two bytes and a lane is
two, so `2 * j` and `2 * j + 1` are in range exactly when `j < 16`. Every caller
in this crate loops to `LANES`, which is that bound, and this is where it has to
be discharged rather than assumed. -/
@[step]
theorem lane_no_panic (data : Array U8 32#usize) (j : Usize) (h : j.val < 16) :
    lane data j ⦃ fun _ => True ⦄ := by
  unfold lane
  step*

/-! ## Interpolation

The decoder's arithmetic core, and the only place in the crate with a nested
loop. Both loops index a slice, and the bound in both cases is the same
quantity: the node count the caller passed. -/

/-- The weight loop cannot fail.

It multiplies and inverts, both already total, and indexes `nodes` at `j` under
the guard `j < n`. So the hypothesis is that `n` does not exceed the slice, which
is what makes the guard a bound rather than a hope. -/
@[step]
theorem interpolate_inner_no_panic (nodes : Slice U16) (x : U16) (n i : Usize)
    (xi weight : U16) (j : Usize) (hn : n.val ≤ nodes.val.length) :
    interpolate_loop0_loop0 nodes x n i xi weight j ⦃ fun _ => True ⦄ := by
  unfold interpolate_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun p => n.val - (Prod.snd p).val)
    (inv := fun _ => True)
  · rintro ⟨w1, j1⟩ _
    unfold interpolate_loop0_loop0.body
    simp only []
    split <;> [skip; simp]
    step*
    split <;> step*
  · trivial

/-- The accumulation loop cannot fail. Same bound, and the read from `vals` is a
`get` returning an option, so a short `vals` contributes nothing rather than
failing. -/
@[step]
theorem interpolate_outer_no_panic (nodes vals : Slice U16) (x : U16) (n : Usize)
    (acc : U16) (i : Usize) (hn : n.val ≤ nodes.val.length) :
    interpolate_loop0 nodes vals x n acc i ⦃ fun _ => True ⦄ := by
  unfold interpolate_loop0
  apply loop.spec_decr_nat
    (measure := fun p => n.val - (Prod.snd p).val)
    (inv := fun _ => True)
  · rintro ⟨a1, i1⟩ _
    unfold interpolate_loop0.body
    simp only []
    split <;> [skip; simp]
    step*
    split <;> step*
  · trivial

/-- **Interpolation cannot fail, for any inputs at all.**

No hypothesis: the node count is read from the slice, so the bound the two loops
need holds by construction rather than by assumption. `vals` may be any length,
because it is read through `get`.

That is the theorem worth having about this function. It is called once per lost
chunk per lane with nodes an attacker chose, and its inner loop runs `k` times
for each of `k` outer turns. -/
@[step]
theorem interpolate_no_panic (nodes vals : Slice U16) (x : U16) :
    interpolate nodes vals x ⦃ fun _ => True ⦄ := by
  unfold interpolate
  step*

/-! ## The barycentric form

`interpolate` above is the specification, and the encoder and decoder no
longer call it on the hot path: `weights` computes the
inverted denominators once per node set, `coefficients` the Lagrange
coefficients once per target, and `evaluate` the sum for one lane. Same loop
shapes as `interpolate`'s two, plus one push per node in the first two, so the
obligations are the ones already met above with the room bound the node loops
of `next_chunk` and `message` carry.

None of the three needs a hypothesis. The pushes are bounded because the vector
starts empty and gains one element per node, and a slice never holds more than
`Usize.max` elements. -/

/-- The denominator loop cannot fail: index under the guard, add, multiply. -/
@[step]
theorem weights_inner_no_panic (nodes : Slice U16) (n i : Usize) (xi denom : U16)
    (j : Usize) (hn : n.val ≤ nodes.val.length) :
    weights_loop0_loop0 nodes n i xi denom j ⦃ fun _ => True ⦄ := by
  unfold weights_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun p => n.val - (Prod.snd p).val)
    (inv := fun _ => True)
  · rintro ⟨d1, j1⟩ _
    unfold weights_loop0_loop0.body
    simp only []
    split <;> [skip; simp]
    step*
    split <;> step*
  · trivial

/-- The weight loop cannot fail. One push per node, so the invariant is that the
vector has grown by at most the number of turns taken. -/
theorem weights_outer_no_panic (nodes : Slice U16) (n : Usize) (w : alloc.vec.Vec U16)
    (i : Usize) (hn : n.val ≤ nodes.val.length)
    (hw : w.val.length + n.val ≤ Usize.max) :
    weights_loop0 nodes n w i ⦃ fun _ => True ⦄ := by
  unfold weights_loop0
  apply loop.spec_decr_nat
    (measure := fun p => n.val - (Prod.snd p).val)
    (inv := fun p =>
      (Prod.fst p).val.length + i.val ≤ w.val.length + (Prod.snd p).val)
  · rintro ⟨w1, i1⟩ hinv
    simp only [] at hinv
    unfold weights_loop0.body
    simp only []
    split <;> [skip; simp]
    step*; simp_all; scalar_tac
  · simp

/-- **Computing the weights cannot fail, for any node set.** -/
@[step]
theorem weights_no_panic (nodes : Slice U16) :
    weights nodes ⦃ fun _ => True ⦄ := by
  unfold weights
  step*
  exact weights_outer_no_panic _ _ _ _ (by simp)
    (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]; scalar_tac)

/-- The numerator loop cannot fail: the same shape as the denominator loop. -/
@[step]
theorem coefficients_inner_no_panic (nodes : Slice U16) (x : U16) (n i : Usize)
    (num : U16) (j : Usize) (hn : n.val ≤ nodes.val.length) :
    coefficients_loop0_loop0 nodes x n i num j ⦃ fun _ => True ⦄ := by
  unfold coefficients_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun p => n.val - (Prod.snd p).val)
    (inv := fun _ => True)
  · rintro ⟨m1, j1⟩ _
    unfold coefficients_loop0_loop0.body
    simp only []
    split <;> [skip; simp]
    step*
    split <;> step*
  · trivial

/-- The coefficient loop cannot fail. The read from `weights` is guarded by its
own length, so a short weight vector contributes zero rather than failing. -/
theorem coefficients_outer_no_panic (nodes weights1 : Slice U16) (x : U16) (n : Usize)
    (c : alloc.vec.Vec U16) (i : Usize) (hn : n.val ≤ nodes.val.length)
    (hc : c.val.length + n.val ≤ Usize.max) :
    coefficients_loop0 nodes weights1 x n c i ⦃ fun _ => True ⦄ := by
  unfold coefficients_loop0
  apply loop.spec_decr_nat
    (measure := fun p => n.val - (Prod.snd p).val)
    (inv := fun p =>
      (Prod.fst p).val.length + i.val ≤ c.val.length + (Prod.snd p).val)
  · rintro ⟨c1, i1⟩ hinv
    simp only [] at hinv
    unfold coefficients_loop0.body
    simp only []
    split <;> [skip; simp]
    step*
    split <;> step* <;> simp_all <;> scalar_tac
  · simp

/-- **Computing the coefficients cannot fail, for any inputs.** -/
@[step]
theorem coefficients_no_panic (nodes weights1 : Slice U16) (x : U16) :
    coefficients nodes weights1 x ⦃ fun _ => True ⦄ := by
  unfold coefficients
  step*
  exact coefficients_outer_no_panic _ _ _ _ _ _ (by simp)
    (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]; scalar_tac)

/-- The accumulation cannot fail: both reads are guarded by their slice's own
length. -/
@[step]
theorem evaluate_loop_no_panic (coeffs vals : Slice U16) (acc : U16) (i : Usize) :
    evaluate_loop coeffs vals acc i ⦃ fun _ => True ⦄ := by
  unfold evaluate_loop
  apply loop.spec_decr_nat
    (measure := fun p => coeffs.val.length - (Prod.snd p).val)
    (inv := fun _ => True)
  · rintro ⟨a1, i1⟩ _
    unfold evaluate_loop.body
    simp only []
    split <;> [skip; simp]
    step*
    split <;> step*
  · trivial

/-- **Evaluating cannot fail, for any inputs.** -/
@[step]
theorem evaluate_no_panic (coeffs vals : Slice U16) :
    evaluate coeffs vals ⦃ fun _ => True ⦄ := by
  unfold evaluate
  exact evaluate_loop_no_panic _ _ _ _

/-! ## The decoder's entry point

`add_chunk` is the function an attacker reaches directly: it takes a codeword off
the wire and decides whether to keep it. Its fallible steps are the index into
the held codewords, the counter increment, and the push that stores a new one. -/

/-- The duplicate scan cannot fail.

It walks the codewords already held, comparing indices. The index is guarded by
the loop condition; the increment is bounded because the counter never passes the
length; and the push at the end is the one step that needs a hypothesis, because
a `Vec` cannot grow past `Usize.max`. The measure is how much of the vector is
left to scan. -/
@[step]
theorem add_chunk_loop_no_panic (v : alloc.vec.Vec Chunk) (chunk : Chunk)
    (i : Usize) (hlen : v.val.length < Usize.max) :
    Decoder.add_chunk_loop v chunk i ⦃ fun _ => True ⦄ := by
  unfold Decoder.add_chunk_loop
  apply loop.spec_decr_nat
    (measure := fun j => v.val.length - (j : Usize).val)
    (inv := fun _ => True)
  · rintro j _
    unfold Decoder.add_chunk_loop.body
    simp only []
    split
    · step*
    · step*
  · trivial

/-- **Taking a codeword off the wire cannot fail.**

The one hypothesis is that the decoder is not already holding `Usize.max`
codewords, which nothing in this crate can produce: `add_chunk` refuses once the
count reaches `needed`, and `needed` is a chunk count derived from a message
length. Stating it rather than deriving it keeps the theorem about this function
instead of about the whole decoder's history. -/
theorem add_chunk_no_panic (self : Decoder) (chunk : Chunk)
    (h : self.«have».val.length < Usize.max) :
    NoPanic (Decoder.add_chunk self chunk) := by
  unfold NoPanic Decoder.add_chunk
  step*

/-- Asking whether the message is ready cannot fail.

Worth a line because the model asks it differently. `Model.Braid`'s decoder
compares `chunks.length * chunkBytes` against the message size, and that product
is a multiplication this crate would have to prove cannot overflow. The Rust
compares against a chunk count computed once at construction, which is the same
question with no arithmetic in it. -/
@[step]
theorem has_message_no_panic (self : Decoder) :
    Decoder.has_message self ⦃ fun _ => True ⦄ := by
  unfold Decoder.has_message; simp

/-! ## The encoder

`next_chunk` produces one codeword. Below `k` it copies a stored chunk; above it
it interpolates every lane, which is where the arithmetic proved above is spent.
-/

/-- Building the node list cannot fail, given room to push. -/
@[step]
theorem next_chunk_nodes_no_panic (k : Usize) (nodes : alloc.vec.Vec U16) (s : Usize)
    (h : nodes.val.length + k.val < Usize.max) :
    Encoder.next_chunk_loop0 k nodes s ⦃ fun _ => True ⦄ := by
  unfold Encoder.next_chunk_loop0
  apply loop.spec_decr_nat
    (measure := fun p => k.val - (Prod.snd p).val)
    (inv := fun p =>
      (Prod.fst p).val.length + (k.val - (Prod.snd p).val) ≤ nodes.val.length + k.val)
  · rintro ⟨n1, s1⟩ hinv
    unfold Encoder.next_chunk_loop0.body
    simp only []
    split <;> [skip; simp]
    step*; simp_all; scalar_tac
  · simp

/-- The lane-value loop cannot fail.

It gathers one field element from each stored chunk. The index into the chunk
vector is guarded, `lane` needs the lane below sixteen, and the push needs room.
Same measure and same invariant shape as the node loop above. -/
@[step]
theorem next_chunk_vals_no_panic (v : alloc.vec.Vec (Array U8 32#usize)) (k j : Usize)
    (vals : alloc.vec.Vec U16) (s : Usize)
    (hj : j.val < 16) (h : vals.val.length + k.val < Usize.max) :
    Encoder.next_chunk_loop1_loop0 v k j vals s ⦃ fun _ => True ⦄ := by
  unfold Encoder.next_chunk_loop1_loop0
  apply loop.spec_decr_nat
    (measure := fun p => k.val - (Prod.snd p).val)
    (inv := fun p =>
      (Prod.fst p).val.length + (k.val - (Prod.snd p).val) ≤ vals.val.length + k.val)
  · rintro ⟨w1, s1⟩ hinv
    unfold Encoder.next_chunk_loop1_loop0.body
    simp only []
    split <;> [skip; simp]
    step*
    split <;> step* <;> simp_all <;> scalar_tac
  · simp

/-- The lane loop cannot fail.

Sixteen turns, each one gathering the lane's values, evaluating them against the
precomputed coefficients, and writing two bytes into the output chunk. The two
writes are where the lane bound is spent a second time: `2 * j` and `2 * j + 1`
are inside a thirty-two byte array exactly when `j < 16`, which is what `LANES`
is. -/
@[step]
theorem next_chunk_lanes_no_panic (v : alloc.vec.Vec (Array U8 32#usize))
    (k : Usize) (c : alloc.vec.Vec U16)
    (out : Array U8 32#usize) (j : Usize)
    (hk : k.val < Usize.max) (hj : j.val ≤ 16) :
    Encoder.next_chunk_loop1 v k c out j ⦃ fun _ => True ⦄ := by
  unfold Encoder.next_chunk_loop1
  apply loop.spec_decr_nat
    (measure := fun p => 16 - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ 16)
  · rintro ⟨o1, j1⟩ hinv
    unfold Encoder.next_chunk_loop1.body
    simp only [LANES, CHUNK_BYTES]
    step*
    simp_all [alloc.vec.Vec.with_capacity]
  · exact hj

/-- The counter guard, as arithmetic.

The encoder stops rather than wrapping: `exhausted` is set at `u16::MAX` and the
increment happens only on the other branch. Bridging "not equal to the maximum"
to "one more still fits" needs the injectivity of the value projection, which is
why it is a lemma rather than a step inside the proof below. -/
private theorem u16_succ_ok {x : U16} (h : ¬x = core.num.U16.MAX) :
    x.val + 1 ≤ U16.max := by
  have hne : x.val ≠ U16.max := by
    intro e
    exact h (UScalar.eq_of_val_eq (by simpa [core.num.U16.MAX, U16.max, U16.rMax, U16.numBits] using e))
  scalar_tac

/-- **Producing a codeword cannot fail.**

Below `k` it copies a stored chunk and above it interpolates every lane. The
counter is a `u16` and its increment is guarded against the maximum, which is
what the `exhausted` flag exists for: the stream stops rather than wrapping to an
index it has already used.

The one hypothesis is that the encoder holds fewer than `Usize.max` chunks, which
a message shorter than memory cannot produce. -/
theorem next_chunk_no_panic (self : Encoder)
    (h : self.chunks.val.length < Usize.max) :
    NoPanic (Encoder.next_chunk self) := by
  have hlen : (self.chunks.len).val < Usize.max := by
    rw [alloc.vec.Vec.len_val]; exact h
  have hcap : (alloc.vec.Vec.with_capacity U16 self.chunks.len).val.length
      + (self.chunks.len).val < Usize.max := by
    simp only [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, List.length_nil,
      Nat.zero_add]
    exact hlen
  unfold NoPanic Encoder.next_chunk
  step* <;> first
    | exact next_chunk_nodes_no_panic _ _ _ hcap
    | exact weights_no_panic _
    | exact coefficients_no_panic _ _ _
    | exact next_chunk_lanes_no_panic _ _ _ _ _ hlen (by simp)
    | exact u16_succ_ok (by assumption)

/-! ## The decoder's reconstruction

`Decoder.message` rebuilds the padded message: for each target position, either a
codeword arrived at it directly or every lane is interpolated. Four nested loops,
and each one's obligations are the shapes already met above. -/

/-- Gathering the node list cannot fail. -/
@[step]
theorem message_nodes_no_panic (k : Usize) (v : alloc.vec.Vec Chunk)
    (nodes : alloc.vec.Vec U16) (i : Usize)
    (h : nodes.val.length + k.val < Usize.max) :
    Decoder.message_loop0 k v nodes i ⦃ fun _ => True ⦄ := by
  unfold Decoder.message_loop0
  apply loop.spec_decr_nat
    (measure := fun p => k.val - (Prod.snd p).val)
    (inv := fun p =>
      (Prod.fst p).val.length + (k.val - (Prod.snd p).val) ≤ nodes.val.length + k.val)
  · rintro ⟨n1, i1⟩ hinv
    unfold Decoder.message_loop0.body
    simp only []
    split <;> [skip; simp]
    step*
    split <;> step* <;> simp_all <;> scalar_tac
  · simp

/-- The search for a codeword that landed on the target cannot fail. It only
reads, so it needs no room. -/
@[step]
theorem message_direct_no_panic (k : Usize) (v : alloc.vec.Vec Chunk)
    (target : U16) (direct : Option Chunk) (i : Usize) :
    Decoder.message_loop1_loop0 k v target direct i ⦃ fun _ => True ⦄ := by
  unfold Decoder.message_loop1_loop0
  apply loop.spec_decr_nat
    (measure := fun p => k.val - (Prod.snd p).val)
    (inv := fun _ => True)
  · rintro ⟨d1, i1⟩ _
    unfold Decoder.message_loop1_loop0.body
    simp only []
    split <;> [skip; simp]
    step*
    (split <;> step*); split <;> step*
  · trivial

/-- Gathering one lane's values across the held codewords cannot fail. -/
@[step]
theorem message_vals_no_panic (k : Usize) (v : alloc.vec.Vec Chunk) (j : Usize)
    (vals : alloc.vec.Vec U16) (i : Usize)
    (hj : j.val < 16) (h : vals.val.length + k.val < Usize.max) :
    Decoder.message_loop1_loop1_loop0 k v j vals i ⦃ fun _ => True ⦄ := by
  unfold Decoder.message_loop1_loop1_loop0
  apply loop.spec_decr_nat
    (measure := fun p => k.val - (Prod.snd p).val)
    (inv := fun p =>
      (Prod.fst p).val.length + (k.val - (Prod.snd p).val) ≤ vals.val.length + k.val)
  · rintro ⟨w1, i1⟩ hinv
    unfold Decoder.message_loop1_loop1_loop0.body
    simp only []
    split <;> [skip; simp]
    step*
    split <;> step* <;> simp_all <;> scalar_tac
  · simp

/-- Evaluating every lane of one target cannot fail.

Two pushes per lane, sixteen lanes, so the output needs thirty-two bytes of room
beyond what it holds. The coefficients arrive precomputed (`c`), so the lane's
arithmetic is one `evaluate`. -/
@[step]
theorem message_lanes_no_panic (k : Usize) (v : alloc.vec.Vec Chunk)
    (out : alloc.vec.Vec U8) (c : alloc.vec.Vec U16) (j : Usize)
    (hk : k.val < Usize.max) (hj : j.val ≤ 16)
    (hout : out.val.length + 32 < Usize.max) :
    Decoder.message_loop1_loop1 k v out c j
      ⦃ r => r.val.length ≤ out.val.length + 2 * (16 - j.val) ⦄ := by
  unfold Decoder.message_loop1_loop1
  apply loop.spec_decr_nat
    (measure := fun p => 16 - (Prod.snd p).val)
    (inv := fun p =>
      (Prod.snd p).val ≤ 16 ∧
      (Prod.fst p).val.length + 2 * (16 - (Prod.snd p).val)
        ≤ out.val.length + 2 * (16 - j.val))
  · rintro ⟨o1, j1⟩ hinv
    obtain ⟨hj1, hlen⟩ := hinv
    simp only [] at hj1 hlen
    unfold Decoder.message_loop1_loop1.body
    simp only [LANES, CHUNK_BYTES]
    step*
    all_goals (try simp_all [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
    all_goals omega
  · exact ⟨hj, Nat.le_refl _⟩

/-- A chunk viewed as a slice is thirty-two bytes.

The fact the target loop's arithmetic turns on, and the one that was missing:
`Array.to_slice` keeps the list, and an `Array α 32` carries its length in its
type. Without this the loop knows the output grew and not by how much. -/
@[simp]
theorem array32_length (a : Array U8 32#usize) : a.val.length = 32 := a.property

@[simp]
theorem to_slice_length_32 (a : Array U8 32#usize) :
    (Array.to_slice a).val.length = 32 := by
  simp only [Array.to_slice]
  exact a.property

/-- Copying a slice into a vector cannot fail, given room.

This looked like a boundary and is not. `Vec::extend_from_slice` clones the slice
through a `Clone` instance, and for a byte that instance is concrete and
reducible: cloning is the identity. So the library's own `Slice.clone_spec`
applies and the obligation reduces to the length bound, with no assumption
needed.

Worth the paragraph because an opaque-looking trait method is not necessarily
opaque, and assuming one that is not would add an assumption that does not have
to exist. -/
theorem extend_u8_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s
      ⦃ r => r.val = v.val ++ s.val ⦄ := by
  have hc : ∀ x ∈ s.val, core.clone.CloneU8.clone x = ok x := by
    intro x _; simp
  unfold alloc.vec.Vec.extend_from_slice
  rw [dif_pos (by simpa using h)]
  obtain ⟨s', hok, heq⟩ := WP.spec_imp_exists (Slice.clone_spec hc)
  split
  · rename_i s'' hm
    rw [hok] at hm
    cases hm
    simp [← heq]
  · rename_i e hm
    rw [hok] at hm
    cases hm
  · rename_i hm
    rw [hok] at hm
    cases hm

/-- The same, in the shape the decoder actually presents.

Stated over an arbitrary slice with its length as a side condition rather than
over a chunk, because `step*` matches a lemma's conclusion and discharges its
hypotheses; a hypothesis that also appears in the conclusion is neither. By the
time the target loop reaches its copy, `Array.to_slice` has been unfolded into an
anonymous constructor, so a lemma phrased over `to_slice` does not match either.

Gives the length directly, which is what the loop's invariant needs. -/
@[step]
theorem extend_slice32_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (hs32 : s.val.length = 32)
    (h : v.val.length + 32 ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s
      ⦃ r => r.val.length = v.val.length + 32 ⦄ := by
  have hlen : v.length + s.length ≤ Usize.max := by
    simp only [alloc.vec.Vec.length, Slice.length, hs32]
    exact h
  refine WP.spec_mono (extend_u8_spec v s hlen) ?_
  intro r hr
  simp [hr, hs32]

/-- Reconstructing every target position cannot fail.

The invariant counts what has been written rather than what is left, which is
what keeps a subtraction out of it: after `t` targets the output holds at most
`32 * t` bytes, and one target still to do leaves room for thirty-two more. -/
@[step]
theorem message_targets_no_panic (k : Usize) (v : alloc.vec.Vec Chunk)
    (nodes : alloc.vec.Vec U16) (out : alloc.vec.Vec U8) (w : alloc.vec.Vec U16)
    (t : Usize)
    (hk : 32 * k.val < Usize.max)
    (hstart : out.val.length ≤ 32 * t.val) :
    Decoder.message_loop1 k v nodes out w t ⦃ fun _ => True ⦄ := by
  unfold Decoder.message_loop1
  apply loop.spec_decr_nat
    (measure := fun p => k.val - (Prod.snd p).val)
    (inv := fun p => (Prod.fst p).val.length ≤ 32 * (Prod.snd p).val)
  · rintro ⟨o1, t1⟩ hinv
    simp only [] at hinv
    unfold Decoder.message_loop1.body
    simp only []
    split
    · rename_i hlt
      have htk : t1.val < k.val := by scalar_tac
      have hroom1 : o1.val.length + 32 ≤ Usize.max := by omega
      step*
      all_goals
        (try simp_all [Array.to_slice])
      all_goals omega
    · simp
  · exact hstart

/-- The second boundary in this crate, and a real one.

`Vec::truncate` is not modelled by the translation at all: it arrives as an
axiom, so nothing can be said about it, including that it returns. Dropping
elements off the end of a vector cannot fail, and that is stated here rather than
assumed silently.

Like `DivCeilTotal` this is the toolchain not seeing through something rather
than a primitive we chose to trust, and it guards no secret. Unlike the `Clone`
instance behind `extend_from_slice`, which looked like a boundary and was not,
this one is opaque in the strongest sense: there is no definition to unfold. -/
def TruncateTotal : Prop :=
  ∀ (v : alloc.vec.Vec U8) (n : Usize),
    ∃ r, alloc.vec.Vec.truncate Global v n = ok r

/-- **Reconstructing the message cannot fail.**

Two hypotheses, both true of anything this crate can build: the chunk count fits
a `usize`, and the padded message does too. Stating them keeps the theorem about
this function rather than about the decoder's whole history.

The second is why `Decoder.message` reserves its output at the message length
rather than at `needed * CHUNK_BYTES`: that product overflows for a decoder
built at `usize::MAX`. -/
theorem message_no_panic (htr : TruncateTotal) (self : Decoder)
    (hneed : self.needed.val < Usize.max)
    (hroom : 32 * self.needed.val < Usize.max) :
    NoPanic (Decoder.message self) := by
  have hcap : (alloc.vec.Vec.with_capacity U16 self.needed).val.length
      + self.needed.val < Usize.max := by
    simp only [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, List.length_nil,
      Nat.zero_add]
    exact hneed
  have hout : (alloc.vec.Vec.with_capacity U8 self.size).val.length
      ≤ 32 * (0#usize : Usize).val := by
    simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
  unfold NoPanic Decoder.message
  step*
  all_goals
    (rename_i out1 _
     obtain ⟨r, hr⟩ := htr out1 self.size
     rw [hr]
     trivial)

/-! ## Nothing is open

Every coding function in this crate is proved panic-free: the field arithmetic,
interpolation and its barycentric form (`weights`, `coefficients`,
`evaluate`), the chunk helpers, both of the encoder's public entry points
and both of the decoder's. The persistence codecs (`to_bytes`, `from_bytes`) and
the constructors carry no theorem; CLAIMS.md lists them.

Two assumptions, and the axiom lists say which theorems carry them.
`DivCeilTotal` and `TruncateTotal` are both the toolchain not seeing through a
core library function rather than a primitive we chose to trust, and neither
guards a secret. `next_chunk_no_panic` carries neither: it rests on `propext`,
`Classical.choice` and `Quot.sound` and nothing else.

A third looks like a boundary and is not. The `Clone` instance behind
`extend_from_slice` is concrete and reducible for a byte, so `extend_u8_spec`
proves what would otherwise have to be assumed. Worth remembering: an
opaque-looking trait method is not necessarily opaque, and assuming one that is
not weakens every theorem downstream of it for nothing. -/

/-! ## The axiom audit, enforced rather than asserted

The two entry points an attacker's codewords drive, pinned. `next_chunk` rests
on Lean's three standard axioms and nothing else: the crate has no opaque
primitive of its own. `message` adds the one library call the translation does
not see through, `Vec::truncate`, which arrives as an axiom and is the
`TruncateTotal` hypothesis the theorem carries. A change that made either rest
on anything further fails here. -/

/-- info: 'Tacenta.ErasureT1.next_chunk_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ErasureT1.next_chunk_no_panic

/-- info: 'Tacenta.ErasureT1.message_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound, alloc.vec.Vec.truncate] -/
#guard_msgs in
#print axioms Tacenta.ErasureT1.message_no_panic
