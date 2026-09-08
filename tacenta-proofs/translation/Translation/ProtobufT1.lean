import Translation.TacentaProtobuf

/-!
# T1 for the wire parser: totality on attacker-chosen bytes

The first item of the verified-core contract: **every byte string
within the declared outer limit returns `Ok` or `Err`, and never fails.**

This is the tier that matters most here and the one it is easiest to be glib
about. Every other verified zone in this repository parses something a peer
produced under a protocol; this one parses whatever arrives. A panic on the
receive path is a remote denial of service, and the input is chosen by whoever
wants to cause it.

## Why the bounded varint is the whole difficulty

`Reader.varint` is a loop over attacker bytes with a shift that grows, an
accumulator that grows, and an early exit. Three fallible operations per turn:
reading a byte, shifting by a value that must stay below the word width, and
adding. Each is total only because of a guard, and none of the guards is
decorative:

- `taken < MAX_VARINT_BYTES` bounds the loop, so the shift cannot run away.
- `shift >= 32` is checked before the shift, which is what keeps `checked_shl`
  from being the thing that saves us rather than the thing that confirms it.
- the accumulate is `checked_add`, so a crafted sequence overflows into an error
  rather than into a wrong value.

The measure is how far `taken` still has to climb, which is the same shape as
the erasure crate's `clmul` loop, and for the same reason: a fixed trip count
with an early exit.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.ProtobufT1

open tacenta_protobuf

/-- Panic-freedom in the weakest-precondition form the loop lemma uses. -/
abbrev NoPanic {α : Type} (e : Result α) : Prop := e ⦃ fun _ => True ⦄

/-- Reading one byte cannot fail.

The bounds check is what makes the index total, and the `checked_add` on the
cursor is what makes the advance total. Both are in the source so that the
answer to what happens at `usize::MAX` is not "the input cannot be that long",
which is a fact about a caller rather than about this function. -/
@[step]
theorem byte_no_panic (r : Reader) : Reader.byte r ⦃ fun _ => True ⦄ := by
  unfold Reader.byte
  step* <;> simp_all <;> scalar_tac

/-- The bounded varint loop cannot fail, from any starting counter within the
bound.

The invariant is the bound itself. Everything else the loop does to its
accumulator is already total by construction: the guard on `shift` precedes the
shift, and the addition is checked. -/
@[step]
theorem varint_loop_no_panic
    (r : Reader) (value shift : U32) (taken : Usize) (h : taken.val ≤ MAX_VARINT_BYTES.val) :
    Reader.varint_loop r value shift taken ⦃ fun _ => True ⦄ := by
  unfold Reader.varint_loop
  apply loop.spec_decr_nat
    (measure := fun p => MAX_VARINT_BYTES.val - (Prod.snd (Prod.snd (Prod.snd p))).val)
    (inv := fun p => (Prod.snd (Prod.snd (Prod.snd p))).val ≤ MAX_VARINT_BYTES.val)
  · rintro ⟨r1, value1, shift1, taken1⟩ hinv
    unfold Reader.varint_loop.body
    simp only []
    split <;> [skip; simp]
    step*
    repeat' (split <;> step*)
    all_goals simp_all
    all_goals scalar_tac
  · exact h

/-- And therefore `varint` itself, which enters the loop at zero. -/
@[step]
theorem varint_no_panic (r : Reader) : Reader.varint r ⦃ fun _ => True ⦄ := by
  unfold Reader.varint
  step* <;> first
    | exact varint_loop_no_panic _ _ _ _ (by scalar_tac)
    | simp

/-- Interpreting a tag cannot fail: pure arithmetic on a value already read.

Provable in one line, which is the whole argument for the split it required.
Reading and interpreting were one function, and a totality proof then had to
carry the varint loop through every branch of the interpretation. That is not
hard, it is large, and the elaborator ran out of budget before the mathematics
ran out of content. -/
@[step]
theorem decode_tag_no_panic (raw : U32) : decode_tag raw ⦃ fun _ => True ⦄ := by
  unfold decode_tag
  step* <;> simp

/-- And `tag` itself: a varint, then the interpretation, each already proved. -/
@[step]
theorem tag_no_panic (r : Reader) : Reader.tag r ⦃ fun _ => True ⦄ := by
  unfold Reader.tag
  step* <;> simp

/-! ## The functions that allocate

`length_delimited` and `slice_of` are the only two that copy, and copying under
an attacker-chosen length is the reason the outer limit exists. Both check the
span against what was actually received *before* allocating, so the allocation
can never exceed the input, and both are loops whose totality needs that check
stated as an invariant rather than assumed. -/

/-- Constructing a reader cannot fail. -/
@[step]
theorem new_no_panic (bytes : alloc.vec.Vec U8) :
    Reader.new bytes ⦃ fun _ => True ⦄ := by
  unfold Reader.new
  step* <;> simp

/-- How much is left.

The `at > len` branch is unreachable in this crate, because every advance keeps
the cursor inside the buffer. It is in the source anyway: a subtraction that is
total only because of a fact about other functions is a subtraction waiting for
one of them to change.

Stated with its **value**, not merely as total. A `fun _ => True` spec here
loses the one fact the caller needs -- `length_delimited` compares its length
against this and then has nothing to compare with -- and that omission is the
single most recurring cause of a stalled proof in this repository.

Note the subtraction is `Nat`, so the `at > len` branch and the ordinary one
have the same answer: zero. -/
@[step]
theorem remaining_spec (r : Reader) :
    Reader.remaining r ⦃ fun n => n.val = r.bytes.length - r.at.val ⦄ := by
  unfold Reader.remaining
  step* <;> simp_all <;> scalar_tac

/-- The copy loop of `slice_of` cannot fail.

Three fallible operations per turn and one invariant covering all three: the
index is in bounds because the cursor has not passed the end and the end is
inside the slice, and the push cannot overflow the output's length because the
output has never grown past the cursor. -/
@[step]
theorem slice_of_loop_no_panic
    (e : Usize) (bytes : Slice U8) (out : alloc.vec.Vec U8) (i : Usize)
    (h1 : i.val ≤ e.val) (h2 : e.val ≤ max bytes.length i.val)
    (h3 : out.length ≤ i.val) :
    Raw.slice_of_loop e bytes out i ⦃ fun _ => True ⦄ := by
  unfold Raw.slice_of_loop
  apply loop.spec_decr_nat
    (measure := fun p => e.val - p.2.val)
    (inv := fun p => p.2.val ≤ e.val ∧ p.1.length ≤ p.2.val ∧
      e.val ≤ max bytes.length p.2.val)
  · rintro ⟨out1, i1⟩ ⟨hi, ho, hb⟩
    unfold Raw.slice_of_loop.body
    simp only []
    split <;> [skip; simp]
    step*
    all_goals (try simp_all)
    all_goals scalar_tac
  · exact ⟨h1, h3, h2⟩

/-- And the copy loop of `length_delimited`, which is the same loop over a
vector rather than a slice. -/
theorem length_delimited_loop_no_panic
    (v : alloc.vec.Vec U8) (e : Usize) (out : alloc.vec.Vec U8) (i : Usize)
    (h1 : i.val ≤ e.val) (h2 : e.val ≤ max v.length i.val)
    (h3 : out.length ≤ i.val) :
    Reader.length_delimited_loop v e out i ⦃ fun _ => True ⦄ := by
  unfold Reader.length_delimited_loop
  apply loop.spec_decr_nat
    (measure := fun p => e.val - p.2.val)
    (inv := fun p => p.2.val ≤ e.val ∧ p.1.length ≤ p.2.val ∧
      e.val ≤ max v.length p.2.val)
  · rintro ⟨out1, i1⟩ ⟨hi, ho, hb⟩
    unfold Reader.length_delimited_loop.body
    simp only []
    split <;> [skip; simp]
    step*
    all_goals (try simp_all)
    all_goals scalar_tac
  · exact ⟨h1, h3, h2⟩

/-- And therefore `length_delimited` itself.

The precondition the loop needs is exactly what the function checks before
entering it, which is the point: `end > self.bytes.len()` is refused, so the
loop is entered only in the state its invariant describes. -/
@[step]
theorem length_delimited_no_panic (r : Reader) :
    Reader.length_delimited r ⦃ fun _ => True ⦄ := by
  unfold Reader.length_delimited
  step* <;> first
    | (step with length_delimited_loop_no_panic <;> first | scalar_tac | simp_all)
    | scalar_tac
    | simp_all

/-- And `slice_of`. -/
@[step]
theorem slice_of_no_panic (raw : Raw) (bytes : Slice U8) :
    Raw.slice_of raw bytes ⦃ fun _ => True ⦄ := by
  unfold Raw.slice_of
  step* <;> first
    | exact slice_of_loop_no_panic _ _ _ _ (by scalar_tac) (by scalar_tac)
        (by simp; scalar_tac)
    | scalar_tac
    | simp_all

/-! ## The field set

Message-level rather than field-level, and the only part of the profile's own
declared limits that anything enforces. -/

/-- A fresh field set cannot fail to be made. -/
@[step]
theorem fieldset_new_no_panic : FieldSet.new ⦃ fun _ => True ⦄ := by
  unfold FieldSet.new
  step* <;> simp

/-- The scan cannot fail: the bound is rechecked every turn, so the index is
never out of range however the vector got its length. -/
theorem contains_loop_no_panic (fs : FieldSet) (field : U32) (i : Usize) :
    FieldSet.contains_loop fs field i ⦃ fun _ => True ⦄ := by
  unfold FieldSet.contains_loop
  apply loop.spec_decr_nat
    (measure := fun p => fs.seen.length - p.val)
    (inv := fun _ => True)
  · rintro i1 _
    unfold FieldSet.contains_loop.body
    simp only []
    split <;> [skip; simp]
    step*
    all_goals (try simp_all)
    all_goals scalar_tac
  · trivial

@[step]
theorem contains_no_panic (fs : FieldSet) (field : U32) :
    FieldSet.contains fs field ⦃ fun _ => True ⦄ :=
  contains_loop_no_panic fs field 0#usize

/-- And admitting a field.

The push is total because of the line above it: the profile's field limit is
well below the word, so a set that has room by `MAX_FIELDS` has room by the
allocator too. The limit is declared in the source and read here. -/
@[step]
theorem admit_no_panic (fs : FieldSet) (field : U32) :
    FieldSet.admit fs field ⦃ fun _ => True ⦄ := by
  unfold FieldSet.admit
  step* <;> first
    | scalar_tac
    | simp_all

/-! ## The message parse

The composition, and the one that took a refactor rather than a tactic. -/

/-- Reading one field cannot fail.

Its own function rather than the loop's body, which is what makes this
provable at all: with the per-turn work inlined, Charon joined the five field
branches by returning every local they might write -- a seven-wide tuple bound
with a pure `let (a, b, ..) := x` that no stepping tactic enters. One state
struct makes each join a single value, and the whole translated crate now has
no such binding in it. -/
@[step]
theorem one_field_no_panic (st : Parse) : one_field st ⦃ fun _ => True ⦄ := by
  unfold one_field
  step*
  repeat' (split <;> (try step*))
  all_goals (try simp_all)
  all_goals (try scalar_tac)

/-- The parse loop cannot fail.

The measure is the turn counter, not the reader. That is deliberate in the
source: bounding by `MAX_FIELDS` makes termination structural, where bounding by
what is left would need a separate argument that reading a tag always advances
the cursor -- true, but a second thing to prove and a second thing to keep
true. -/
theorem parse_ratchet_body_loop_no_panic (st : Parse) (turns : Usize)
    (h : turns.val ≤ MAX_FIELDS.val) :
    parse_ratchet_body_loop st turns ⦃ fun _ => True ⦄ := by
  unfold parse_ratchet_body_loop
  apply loop.spec_decr_nat
    (measure := fun p => MAX_FIELDS.val - p.2.val)
    (inv := fun p => p.2.val ≤ MAX_FIELDS.val)
  · rintro ⟨stA, turnsA⟩ hinv
    unfold parse_ratchet_body_loop.body
    simp only []
    step*
    repeat' (split <;> (try step*))
    all_goals (try simp_all)
    all_goals (try scalar_tac)
  · exact h

/-- And the whole parse: every byte string within the outer limit yields a
message or a refusal, and never a failure. -/
@[step]
theorem parse_ratchet_body_no_panic (bytes : alloc.vec.Vec U8) :
    parse_ratchet_body bytes ⦃ fun _ => True ⦄ := by
  unfold parse_ratchet_body
  step* <;> first
    | (step with parse_ratchet_body_loop_no_panic <;> first | scalar_tac | simp_all)
    | scalar_tac
    | simp_all
  repeat' (split <;> (try step*))
  all_goals (try simp_all)
  all_goals (try scalar_tac)

/-! ## The prekey envelope

Eight fields rather than five, one of them optional, and no trailing
authenticator. Same shapes as the ratchet parse, which is the point: the state
struct and the per-turn function were chosen so a second message type would not
need a second discovery. -/

@[step]
theorem one_envelope_field_no_panic (st : EnvelopeParse) :
    one_envelope_field st ⦃ fun _ => True ⦄ := by
  unfold one_envelope_field
  step*
  repeat' (split <;> (try step*))
  all_goals (try simp_all)
  all_goals (try scalar_tac)

theorem parse_prekey_body_loop_no_panic (st : EnvelopeParse) (turns : Usize)
    (h : turns.val ≤ MAX_FIELDS.val) :
    parse_prekey_body_loop st turns ⦃ fun _ => True ⦄ := by
  unfold parse_prekey_body_loop
  apply loop.spec_decr_nat
    (measure := fun p => MAX_FIELDS.val - p.2.val)
    (inv := fun p => p.2.val ≤ MAX_FIELDS.val)
  · rintro ⟨stA, turnsA⟩ hinv
    unfold parse_prekey_body_loop.body
    simp only []
    step*
    repeat' (split <;> (try step*))
    all_goals (try simp_all)
    all_goals (try scalar_tac)
  · exact h

@[step]
theorem parse_prekey_body_no_panic (bytes : alloc.vec.Vec U8) :
    parse_prekey_body bytes ⦃ fun _ => True ⦄ := by
  unfold parse_prekey_body
  step* <;> first
    | (step with parse_prekey_body_loop_no_panic <;> first | scalar_tac | (try simp_all))
    | scalar_tac
    | (try simp_all)
  repeat' (split <;> (try step*))
  all_goals (try simp_all)
  all_goals (try scalar_tac)

/-! ## Emitting

The other direction. Less exposed than the reader -- it is fed our own values,
not an attacker's -- but it is in the same crate and under the same rule.

**The writer is bounded because the reader is.** A `Vec` push can fail at the
allocator, so an encoder that pushed unconditionally would be total only because
of a fact about its callers, and that shape is avoided here. `push_bounded` refuses at `MAX_MESSAGE_LEN`, which makes
every function below total on its own terms and refuses exactly what the reader
would refuse to read back. -/

@[step]
theorem push_bounded_no_panic (bytes : alloc.vec.Vec U8) (b : U8) :
    push_bounded bytes b ⦃ fun _ => True ⦄ := by
  unfold push_bounded
  step* <;> first | scalar_tac | simp_all

@[step]
theorem varint_step_no_panic (st : VarintOut) : varint_step st ⦃ fun _ => True ⦄ := by
  unfold varint_step
  step*
  repeat' (first | (split <;> (try step*)) | (try step*))
  all_goals (try simp_all)
  all_goals (try scalar_tac)

theorem encode_varint_loop_no_panic (st : VarintOut) (turns : Usize)
    (h : turns.val ≤ MAX_VARINT_BYTES.val) :
    encode_varint_loop st turns ⦃ fun _ => True ⦄ := by
  unfold encode_varint_loop
  apply loop.spec_decr_nat
    (measure := fun p => MAX_VARINT_BYTES.val - p.2.val)
    (inv := fun p => p.2.val ≤ MAX_VARINT_BYTES.val)
  · rintro ⟨stA, turnsA⟩ hinv
    unfold encode_varint_loop.body
    simp only []
    step*
    repeat' (split <;> (try step*))
    all_goals (try simp_all)
    all_goals (try scalar_tac)
  · exact h

@[step]
theorem encode_varint_no_panic (bytes : alloc.vec.Vec U8) (value : U32) :
    encode_varint bytes value ⦃ fun _ => True ⦄ := by
  unfold encode_varint
  step* <;> first
    | (step with encode_varint_loop_no_panic <;> first | scalar_tac | (try simp_all))
    | scalar_tac
    | (try simp_all)
  repeat' (split <;> (try step*))
  all_goals (try simp_all)

@[step]
theorem wire_code_no_panic (wire : WireType) : wire_code wire ⦃ fun _ => True ⦄ := by
  match wire with
  | .Varint => unfold wire_code; step* <;> (try simp_all)
  | .LengthDelimited => unfold wire_code; step* <;> (try simp_all)

@[step]
theorem encode_tag_no_panic (bytes : alloc.vec.Vec U8) (field : U32) (wire : WireType) :
    encode_tag bytes field wire ⦃ fun _ => True ⦄ := by
  unfold encode_tag
  step*
  repeat' (split <;> (try step*))
  all_goals (try simp_all)
  all_goals (try scalar_tac)

@[step]
theorem copy_step_no_panic (st : CopyOut) (value : Slice U8) :
    copy_step st value ⦃ fun _ => True ⦄ := by
  unfold copy_step
  step*
  repeat' (split <;> (try step*))
  all_goals (try simp_all)
  all_goals (try scalar_tac)

theorem encode_length_delimited_loop_no_panic
    (value : Slice U8) (st : CopyOut) (turns : Usize)
    (h : turns.val ≤ MAX_MESSAGE_LEN.val) :
    encode_length_delimited_loop value st turns ⦃ fun _ => True ⦄ := by
  unfold encode_length_delimited_loop
  apply loop.spec_decr_nat
    (measure := fun p => MAX_MESSAGE_LEN.val - p.2.val)
    (inv := fun p => p.2.val ≤ MAX_MESSAGE_LEN.val)
  · rintro ⟨stA, turnsA⟩ hinv
    unfold encode_length_delimited_loop.body
    simp only []
    step*
    repeat' (split <;> (try step*))
    all_goals (try simp_all)
    all_goals (try scalar_tac)
  · exact h

@[step]
theorem encode_length_delimited_no_panic (bytes : alloc.vec.Vec U8) (value : Slice U8) :
    encode_length_delimited bytes value ⦃ fun _ => True ⦄ := by
  unfold encode_length_delimited
  step* <;> first
    | (step with encode_length_delimited_loop_no_panic <;>
        first | scalar_tac | (try simp_all))
    | scalar_tac
    | (try simp_all)
  repeat' (split <;> (try step*))
  all_goals (try simp_all)

@[step]
theorem encode_ratchet_body_no_panic (body : RatchetBody) :
    encode_ratchet_body body ⦃ fun _ => True ⦄ := by
  unfold encode_ratchet_body
  step*
  repeat' (split <;> (try step*))
  all_goals (try simp_all)
  all_goals (try scalar_tac)

/-! ## What this tier does and does not establish

**Does.** Every byte string within `MAX_MESSAGE_LEN` drives these functions to an
`Ok` or an `Err` and never to a failure. That is contract item 1 of the verified-core contract, for the reader primitives the codec is built from.

**Does not.** Anything about what the accepted bytes *mean*. Sound decoding,
round trip, canonical emission, raw-byte fidelity and composed refinement are
items 3 through 7, they are the point of putting this crate inside the verified
core, and none of them is here yet.

## What the proof needs from the source, which is the transferable part

The source is written in the form the proofs can use, and none of what follows
is a style preference: every item is also better code. The first four serve
this tier; the last two serve the refinement in `ProtobufT3.lean` and are
recorded here because they belong with the others.

`u32::checked_shl` reaches the translation as an **axiom**: Aeneas does not model
it. Proving totality through it would mean assuming the most exposed parser in
the engine returns, which is the assumption a wire-parser proof exists to
avoid. A varint is base-128, so a running checked factor is the same
arithmetic in an operation the toolchain models.

Division and remainder rather than `raw >> 3` and `raw & 7`, which translate
but reason expensively. A tag is a field number times eight plus a three-bit
wire type, so division and remainder are the definition rather than a
substitute.

Reading a tag is split from interpreting one. Together, the totality proof would
have to carry the varint loop through every branch of the interpretation and
would exhaust the elaborator; apart, each half is a line.

And the wire type is tested by three comparisons rather than a
`match wire { 0 => .., 2 => .., _ => .. }` on a scalar. A match on integer
literals translates to a form the elaborator
case-splits expensively, and that is what stands between a three-comparison
function and its one-line proof. The arithmetic is never the difficulty; the
form is.

Then, for the refinement rather than for totality:

`b % 128` and `b < 128` rather than `b & 0x7f` and `b & 0x80 == 0`. Both forms
translate, and both are total; the masks cannot be related to the model, because
the decision procedure for bit vectors cannot see through the translation's
scalar wrapper
and the model has no reason to speak in masks. The seven low bits of a varint
byte *are* its value modulo 128, and the continuation bit *is* whether it
reaches 128, so this is the definition rather than a substitute.

And the minimality test is `factor > 1` rather than `taken > 1`. They are the
same test -- the place value is one exactly on the first byte -- but the
latter would make the refinement carry `factor = 128 ^ taken` as a side
condition through every branch, which is arithmetic that linear reasoning
cannot follow. Testing the value the model already receives leaves `taken` as
nothing but the loop bound.

Writing code in the form the proofs can use is the recurring pattern across
this repository, and its shape does not vary: **the arithmetic is never the
difficulty, the form is.** The crate translates with **no axioms at all**,
and `tag_refines` rests on nothing beyond `propext`, `Classical.choice` and
`Quot.sound`. -/

end Tacenta.ProtobufT1
