import Translation.TacentaProtobuf
import Translation.ProtobufT1
import Model.Protobuf

/-!
# T3 for the wire parser: the translated reader computes what the model says

Contract item 3 of the verified-core design. T1 says the reader cannot
fail; this says what it does.

The distinction matters more here than anywhere else in this repository. A
parser that never panics and returns the wrong field has done its job by T1's
standard and defeated the protocol by every other standard, and the fields this
one returns select ratchet keys.

## The relation

Two shapes to bridge and both differences are deliberate.

A `Reader` carries owned bytes and a cursor; the model carries the bytes not yet
read. So `remaining` is the bridge, and it is a definition rather than a
coincidence: the model was written knowing the Rust would look like this.

A translated function returns `Result (core.result.Result α ProtoError × Reader)`
where the model returns `Option (α × List UInt8)`. The outer `Result` is
Aeneas's failure, which T1 has already ruled out; the inner one is the parser's
own refusal, and that is what corresponds to the model's `none`.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.ProtobufT3

open tacenta_protobuf

/-! ## Carrying values across -/

/-- One byte across the boundary.

Aeneas carries `Std.U8`, a bounded scalar with a bitvector inside; the model
carries `UInt8`, because `Model.Messages` does and a second byte type in the
model would be worse than a conversion here. -/
def byteOf (b : Std.U8) : UInt8 := UInt8.ofNat b.val

/-- The width bound the translation states, in the form the model states it.

`U32.checked_mul` reports failure as `2 ^ U32.numBits - 1 < _`, and
`Model.Protobuf.maxU32` is the literal. They are the same number, and until they
are syntactically the same number no guard in the model lines up with any guard
in the code. -/
@[simp] theorem u32_bound : (2:Nat) ^ U32.numBits - 1 = Model.Protobuf.maxU32 := by
  simp [U32.numBits, Model.Protobuf.maxU32]

/-- A converted byte has the scalar's value.

The only fact needed about the conversion, and it is one line because the source
stopped using bit masks. `b & 0x7f` and `b & 0x80 == 0` had to be related to
`% 128` and `< 128` through a bitvector decision procedure that could not see
through Aeneas's scalar wrapper; the source now says what it means, so there is
nothing to relate. That is the fifth time a proof has been unblocked by writing
the arithmetic rather than a bit-level substitute for it. -/
@[simp] theorem byteOf_toNat (b : Std.U8) : (byteOf b).toNat = b.val := by
  simp [byteOf]

/-- The bytes a reader has not consumed. The model's whole state. -/
def remaining (r : Reader) : List UInt8 :=
  (r.bytes.val.drop r.at.val).map byteOf

/-- The model's wire type for a translated one. -/
def wireOf : WireType → Model.Protobuf.WireType
  | WireType.Varint => Model.Protobuf.WireType.varint
  | WireType.LengthDelimited => Model.Protobuf.WireType.lengthDelimited

/-! ## Interpreting a tag

The function with no loop and no reader, taken first on purpose: it fixes the
shape of the relation while the content is small enough that a failure is
obviously the statement's fault rather than the proof's. -/

/-- Interpreting a tag agrees with the model, for every value.

`decode_tag` is three comparisons over a division and a remainder, and the model
is the same three comparisons. The proof is `bv_decide`-free and `native_decide`-
free: both sides reduce, so the kernel settles it. -/
@[step]
theorem decode_tag_refines (raw : U32) :
    decode_tag raw ⦃ fun res =>
      match res with
      | core.result.Result.Ok t =>
        Model.Protobuf.decodeTag raw.val = some (t.field.val, wireOf t.wire)
      | core.result.Result.Err _ => Model.Protobuf.decodeTag raw.val = none ⦄ := by
  unfold decode_tag Model.Protobuf.decodeTag
  step*
  repeat' split
  all_goals simp_all [Model.Protobuf.maxFieldNumber, wireOf, MAX_FIELD_NUMBER]
  all_goals scalar_tac

/-! ## Reading one byte

The smallest step, and the one every later proof rests on: after a successful
read the model's remaining list is the tail of what it was. -/

theorem byte_refines (r : Reader) :
    Reader.byte r ⦃ fun (res, r') =>
      match res with
      | core.result.Result.Ok b =>
        remaining r = byteOf b :: remaining r'
      | core.result.Result.Err _ => remaining r = [] ⦄ := by
  unfold Reader.byte
  step*
  all_goals simp_all [remaining]
  all_goals rw [List.drop_eq_getElem_cons (by simp; scalar_tac)]
  all_goals simp

/-! ## The varint loop

The one with content. `Model.Protobuf.varintFrom` threads a fuel, a factor and
an accumulator because this loop carries a `taken`, a `factor` and a `value`,
and the relation below is the statement that those three are the same three.

`goal` is what the model says about the bytes the loop started on, and it does
not move. The invariant says that at every turn, the model applied to the
current state still says exactly that -- which is what makes the loop's progress
a rearrangement of the model's recursion rather than a separate computation to
be compared at the end. -/

theorem varint_loop_refines (r : Reader) (value factor : U32) (taken : Usize)
    (goal : Option (Nat × List UInt8))
    (hb : taken.val ≤ MAX_VARINT_BYTES.val)
    (hg : Model.Protobuf.varintFrom (MAX_VARINT_BYTES.val - taken.val)
            factor.val value.val (remaining r) = goal) :
    Reader.varint_loop r value factor taken ⦃ fun (res, r') =>
      match res with
      | core.result.Result.Ok v => goal = some (v.val, remaining r')
      | core.result.Result.Err _ => goal = none ⦄ := by
  unfold Reader.varint_loop
  apply loop.spec_decr_nat
    (measure := fun p => MAX_VARINT_BYTES.val - p.2.2.2.val)
    (inv := fun p =>
      p.2.2.2.val ≤ MAX_VARINT_BYTES.val ∧
      Model.Protobuf.varintFrom (MAX_VARINT_BYTES.val - p.2.2.2.val)
        p.2.2.1.val p.2.1.val (remaining p.1) = goal)
  · rintro ⟨r1, value1, factor1, taken1⟩ ⟨hb1, hg1⟩
    unfold Reader.varint_loop.body
    simp only []
    split
    · step with byte_refines as ⟨res, r2, hrel⟩
      cases res with
      | Err e =>
        -- The reader is empty, and so is the model's byte list.
        simp only [] at hrel
        step*
        simp_all [Model.Protobuf.varintFrom_nil]
      | Ok b =>
        -- The model's list is this byte followed by what the reader has left,
        -- so one unfolding of `varintFrom` lines its guards up with the loop's.
        simp only [] at hrel
        rw [hrel] at hg1
        rw [show MAX_VARINT_BYTES.val - taken1.val
              = (MAX_VARINT_BYTES.val - taken1.val - 1) + 1 by
              simp_all [MAX_VARINT_BYTES]; scalar_tac] at hg1
        rw [Model.Protobuf.varintFrom] at hg1
        simp only [byteOf_toNat] at hg1
        step*
        all_goals simp_all [Model.Protobuf.maxU32, MAX_VARINT_BYTES, U32.max]
        -- Each of the model's two accumulation guards is decided by the
        -- `checked_` fact the translation supplies for the matching operation,
        -- so they are resolved rather than case-split: the two descriptions are
        -- not choosing independently, which is the whole content of the tier.
        all_goals (first
          | (rw [if_pos (show 4294967295 < b.val % 128 * factor1.val by omega)] at hg1;
             try simp_all)
          | (rw [if_neg (show ¬ (4294967295 < b.val % 128 * factor1.val) by omega),
                 if_pos (show 4294967295 < value1.val + b.val % 128 * factor1.val by omega)]
               at hg1; try simp_all)
          | (rw [if_neg (show ¬ (4294967295 < b.val % 128 * factor1.val) by omega),
                 if_neg (show ¬ (4294967295 < value1.val + b.val % 128 * factor1.val) by omega)]
               at hg1; try simp_all))
        -- The remaining guards are the minimality test and the two branch
        -- conditions, and each is likewise already decided.
        all_goals (try subst cf_post)
        all_goals (try simp_all)
        all_goals (repeat first
          | rw [if_neg (by omega)] at hg1
          | rw [if_pos (by omega)] at hg1)
        all_goals (try simp_all)
        -- The continuation: what the loop still has to do is what the model
        -- still has to do, one byte shorter. The only gap is that the loop
        -- counts its bound down as `5 - (taken + 1)` and the model's fuel
        -- arrives as `4 - taken`, which is the same number.
        all_goals (first
          | omega
          | (refine ⟨?_, by omega⟩; convert hg1 using 2 <;> omega)
          | (refine ⟨?_, by omega⟩; convert hg1 using 3 <;> omega))
    · -- taken is at the bound: the model has no fuel left, so it agrees.
      simp_all [MAX_VARINT_BYTES]
      simp only [Model.Protobuf.varintFrom] at hg1
      first | exact hg1.symm | exact hg1
  · exact ⟨hb, hg⟩

/-- And therefore `varint` itself, which enters the loop at the model's origin:
no bytes taken, place value one, nothing accumulated. -/
@[step]
theorem varint_refines (r : Reader) :
    Reader.varint r ⦃ fun (res, r') =>
      match res with
      | core.result.Result.Ok v =>
        Model.Protobuf.varint (remaining r) = some (v.val, remaining r')
      | core.result.Result.Err _ => Model.Protobuf.varint (remaining r) = none ⦄ := by
  unfold Reader.varint
  exact varint_loop_refines r 0#u32 1#u32 0#usize _ (by scalar_tac)
    (by simp [Model.Protobuf.varint, Model.Protobuf.maxVarintBytes, MAX_VARINT_BYTES])

/-! ## Reading a tag

The composition, and the first place the two halves are used together. Nothing
new is proved here; that it is short is the point of having split the function
in the first place. -/

@[step]
theorem tag_refines (r : Reader) :
    Reader.tag r ⦃ fun (res, r') =>
      match res with
      | core.result.Result.Ok t =>
        Model.Protobuf.tag (remaining r) = some ((t.field.val, wireOf t.wire), remaining r')
      | core.result.Result.Err _ => Model.Protobuf.tag (remaining r) = none ⦄ := by
  unfold Reader.tag Model.Protobuf.tag
  step with varint_refines as ⟨res, r2, hv⟩
  cases res with
  | Err e => simp only [] at hv; step*; try simp_all
  | Ok raw =>
    simp only [] at hv
    step
    simp only [cf_post]
    step with decode_tag_refines as ⟨res2, hd⟩
    cases res2 with
    | Err e => simp_all
    | Ok t => simp_all

/-! ## Copying a length-delimited field

Item 4. The loop copies a span out of the buffer one byte at a time, and the
model takes a prefix of what is left, so the relation is that those are the same
list -- established a byte at a time, in step with the loop.

`goalList` is the span the loop was asked for and does not move. What the
invariant says is that at every turn, the bytes already copied plus the bytes
still to copy are still exactly it. -/

/-- One turn of a copy, on the model's side.

Taking `k + 1` from position `i` is that byte followed by taking `k` from the
next, which is the whole content of the loop's step. -/
theorem take_drop_step (M : List UInt8) (i k : Nat) (h : i < M.length) :
    (M.drop i).take (k + 1) = M[i] :: (M.drop (i + 1)).take k := by
  rw [List.drop_eq_getElem_cons h, List.take_succ_cons]

theorem length_delimited_loop_refines
    (v : alloc.vec.Vec U8) (e : Usize) (out : alloc.vec.Vec U8) (i : Usize)
    (h1 : i.val ≤ e.val) (h2 : e.val ≤ max v.length i.val)
    (h3 : out.length ≤ i.val) :
    Reader.length_delimited_loop v e out i ⦃ fun res =>
      res.val.map byteOf
        = out.val.map byteOf
            ++ ((v.val.map byteOf).drop i.val).take (e.val - i.val) ⦄ := by
  unfold Reader.length_delimited_loop
  apply loop.spec_decr_nat
    (measure := fun p => e.val - p.2.val)
    (inv := fun p => p.2.val ≤ e.val ∧ p.1.length ≤ p.2.val ∧
      e.val ≤ max v.length p.2.val ∧
      p.1.val.map byteOf ++ ((v.val.map byteOf).drop p.2.val).take (e.val - p.2.val)
        = out.val.map byteOf ++ ((v.val.map byteOf).drop i.val).take (e.val - i.val))
  · rintro ⟨outA, iA⟩ ⟨hi, ho, hb, hrel⟩
    unfold Reader.length_delimited_loop.body
    simp only []
    split
    · step*
      all_goals (try simp_all)
      all_goals (first
        | scalar_tac
        | (refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
           -- What is still to copy is this byte and then the rest of it.
           rw [← hrel,
               show e.val - iA.val = (e.val - (iA.val + 1)) + 1 from by scalar_tac,
               take_drop_step _ _ _ (by simp; scalar_tac)]
           simp))
    · simp_all
  · exact ⟨h1, h3, h2, rfl⟩

/-- And therefore the field itself.

The length is attacker-chosen, so the interesting agreement is on refusal: the
model refuses when the length exceeds what is left, and the code refuses when
`at + len` leaves the buffer. Those are the same condition, including when the
addition overflows -- a length that large exceeds anything that could remain. -/
@[step]
theorem length_delimited_refines (r : Reader) :
    Reader.length_delimited r ⦃ fun (res, r') =>
      match res with
      | core.result.Result.Ok out =>
        Model.Protobuf.lengthDelimited (remaining r)
          = some (out.val.map byteOf, remaining r')
      | core.result.Result.Err _ =>
        Model.Protobuf.lengthDelimited (remaining r) = none ⦄ := by
  unfold Reader.length_delimited Model.Protobuf.lengthDelimited
  step with varint_refines as ⟨res, r1, hv⟩
  cases res with
  | Err e => simp only [] at hv; step*; try simp_all
  | Ok lenv =>
    simp only [] at hv
    step
    simp only [cf_post]
    step*
    all_goals (try (step with length_delimited_loop_refines))
    all_goals simp_all [remaining]
    -- The overflow branch is unreachable now that the length is checked against
    -- what is left, and the loop's bound follows from the same check.
    all_goals scalar_tac

/-! ## The field set

Message-level, and the part of item 5 that does not depend on which fields the
profile has. Both bounds it enforces are declared in the Rust and read here. -/

/-- The field numbers a set holds, as the model holds them. -/
def fieldsOf (fs : FieldSet) : List Nat := fs.seen.val.map (fun x => x.val)

theorem contains_loop_refines (fs : FieldSet) (field : U32) (i : Usize)
    (goal : Bool)
    (h : i.val ≤ (fieldsOf fs).length)
    (hg : Model.Protobuf.seenFrom ((fieldsOf fs).length - i.val)
            ((fieldsOf fs).drop i.val) field.val = goal) :
    FieldSet.contains_loop fs field i ⦃ fun res => res = goal ⦄ := by
  unfold FieldSet.contains_loop
  apply loop.spec_decr_nat
    (measure := fun p => (fieldsOf fs).length - p.val)
    (inv := fun p => p.val ≤ (fieldsOf fs).length ∧
      Model.Protobuf.seenFrom ((fieldsOf fs).length - p.val)
        ((fieldsOf fs).drop p.val) field.val = goal)
  · rintro iA ⟨hi, hrel⟩
    unfold FieldSet.contains_loop.body
    simp only []
    split
    · -- A byte of the scan: unfold the model one element to match it.
      rw [show (fieldsOf fs).length - iA.val
            = ((fieldsOf fs).length - iA.val - 1) + 1 from by
            simp_all [fieldsOf]; scalar_tac,
          List.drop_eq_getElem_cons (by simp [fieldsOf]; scalar_tac)] at hrel
      rw [Model.Protobuf.seenFrom] at hrel
      step*
      all_goals (try simp_all [fieldsOf])
      all_goals (first
        | scalar_tac
        | (rw [show fs.seen.val.length - (iA.val + 1)
                 = fs.seen.val.length - iA.val - 1 from by omega]
           exact ⟨by scalar_tac, hrel, by scalar_tac⟩))
    · simp_all [fieldsOf, Model.Protobuf.seenFrom]
  · exact ⟨h, hg⟩

/-- And therefore `contains`, which starts the scan at the front. -/
@[step]
theorem contains_refines (fs : FieldSet) (field : U32) :
    FieldSet.contains fs field ⦃ fun res =>
      res = Model.Protobuf.seen (fieldsOf fs) field.val ⦄ :=
  contains_loop_refines fs field 0#usize _ (by simp) (by simp [Model.Protobuf.seen])

/-- Admitting a field agrees with the model, including on both refusals.

The error case says two things, and the second is the one worth having: **a
refused set is the set it came in with.** That was structural while `admit` took
`self` by value, and by-value did not survive the parse loop, because Aeneas has
no early return inside a loop and a moved set is gone by the time the loop ends.
So it is proved instead, which is the stronger form anyway: a structural
argument holds until someone changes the signature, and this one holds. -/
@[step]
theorem admit_refines (fs : FieldSet) (field : U32) :
    FieldSet.admit fs field ⦃ fun (e, fs') =>
      match e with
      | none =>
        Model.Protobuf.admit (fieldsOf fs) field.val = some (fieldsOf fs')
      | some _ =>
        Model.Protobuf.admit (fieldsOf fs) field.val = none ∧
        fieldsOf fs' = fieldsOf fs ⦄ := by
  unfold FieldSet.admit Model.Protobuf.admit
  step with contains_refines as ⟨b, hb⟩
  step*
  all_goals simp_all [fieldsOf, Model.Protobuf.maxFields, MAX_FIELDS]

/-! ## The message parse

The composition. Everything below rests on the refinements above being
registered as step lemmas: without that, stepping through this function uses the
T1 specs, which say only that nothing fails, and the values are lost -- which is
the single most recurring cause of a stalled proof in this repository. -/

/-- A reader with bytes left has a non-empty remainder.

The model's loop stops on an empty list where the code's stops on a cursor at
the end, and this is the one fact that makes those the same condition. -/
@[simp] theorem remaining_isEmpty (r : Reader) :
    (remaining r).isEmpty = decide (r.bytes.val.length ≤ r.at.val) := by
  rw [Bool.eq_iff_iff]
  simp [remaining, List.isEmpty_iff, List.drop_eq_nil_iff]

/-- A parse state, as the model holds it. -/
def stateOf (st : Parse) : Model.Protobuf.ParseState :=
  { rest := remaining st.reader
    seen := fieldsOf st.seen
    ratchetKey := st.ratchet_key.val.map byteOf
    counter := st.counter.val
    previousCounter := st.previous_counter.val
    ciphertext := st.ciphertext.val.map byteOf
    pq := st.pq.val.map byteOf
    refused := st.error.isSome }

-- Large rather than deep: five field branches, each with a wire-type check and
-- a sub-parse, and the default budget does not cover the case split. Raised
-- rather than split further, because splitting `one_field` in the source to suit
-- the elaborator would undo the shape that made the loop provable at all.
set_option maxHeartbeats 1000000 in
/-- Reading one field agrees with the model.

Two statements, because the refusal path cannot promise more than it has. When
the model refuses, the code refuses, and nothing else about the state is
claimed: the reader has consumed whatever the failing sub-parse consumed, and
the model records no partial progress. When it does not refuse, the whole state
agrees. That is enough, because the loop stops at the first refusal and the
message is thrown away. -/
@[step]
theorem one_field_refines (st : Parse) :
    one_field st ⦃ fun st' =>
      st'.error.isSome = (Model.Protobuf.oneField (stateOf st)).refused ∧
      ((Model.Protobuf.oneField (stateOf st)).refused = false →
        stateOf st' = Model.Protobuf.oneField (stateOf st)) ⦄ := by
  unfold one_field Model.Protobuf.oneField
  step*
  repeat' (split <;> (try step*))
  all_goals (try simp_all [stateOf, fieldsOf, Model.Protobuf.fieldRatchetKey,
    Model.Protobuf.fieldCounter, Model.Protobuf.fieldPreviousCounter,
    Model.Protobuf.fieldCiphertext, Model.Protobuf.fieldPq,
    FIELD_RATCHET_KEY, FIELD_COUNTER, FIELD_PREVIOUS_COUNTER,
    FIELD_CIPHERTEXT, FIELD_PQ, wireOf])

/-! ## The whole message

`one_field_refines` is proved: reading one field computes what
`Model.Protobuf.oneField` says. This section takes the loop over it, and
`parse_ratchet_body` itself, the rest of the way.

The loop's invariant has to be a disjunction: while nothing is refused the
whole state agrees, and once something is, only the fact of refusal can be
carried, because the reader has consumed whatever the failing sub-parse
consumed and the model records no partial progress.

The invariant is stated against turns *taken* rather than fuel *remaining*,
so that it composes. `Model.Protobuf.parseFrom_add` (running the fold for `n`
turns and then `m` more is the same as `n + m` at once) lets the invariant say
"the model, run for exactly as many turns as the code has taken so far,
agrees with the real state" -- true by `rfl` at the start (zero turns taken),
and preserved by `one_field_refines`'s own two-part postcondition applied to
one more turn, without needing to case on whether that turn is the one that
refuses. `parseFrom_refused` and `parseFrom_stuck` (a refused or
nothing-left state is a fixed point, so extra fuel changes nothing) turn this
into the theorem's own claim at each of the loop's three exit points. -/

theorem parse_ratchet_body_loop_refines (st : Parse) (turns : Usize)
    (h : turns.val ≤ MAX_FIELDS.val) :
    parse_ratchet_body_loop st turns ⦃ fun y =>
      (stateOf y).refused =
        (Model.Protobuf.parseFrom (MAX_FIELDS.val - turns.val) (stateOf st)).refused ∧
      ((stateOf y).refused = false →
        stateOf y = Model.Protobuf.parseFrom (MAX_FIELDS.val - turns.val) (stateOf st)) ⦄ := by
  unfold parse_ratchet_body_loop
  apply loop.spec_decr_nat
    (measure := fun p => MAX_FIELDS.val - p.2.val)
    (inv := fun p =>
      turns.val ≤ p.2.val ∧ p.2.val ≤ MAX_FIELDS.val ∧
      (stateOf p.1).refused =
        (Model.Protobuf.parseFrom (p.2.val - turns.val) (stateOf st)).refused ∧
      ((stateOf p.1).refused = false →
        stateOf p.1 = Model.Protobuf.parseFrom (p.2.val - turns.val) (stateOf st)))
  · rintro ⟨stA, turnsA⟩ ⟨hturn0, hturn, hflag, heq⟩
    unfold parse_ratchet_body_loop.body
    simp only []
    -- Once fuel runs out or the state is already stopped, more fuel changes
    -- nothing: this is `parseFrom_stuck`/`parseFrom_refused` lifted through
    -- `parseFrom_add`, and it is what closes every exit from the loop.
    have hfix : ∀ n : Nat, Model.Protobuf.parseFrom n
        (Model.Protobuf.parseFrom (turnsA.val - turns.val) (stateOf st)) =
        Model.Protobuf.parseFrom (turnsA.val - turns.val) (stateOf st) →
      Model.Protobuf.parseFrom (turnsA.val - turns.val + n) (stateOf st) =
        Model.Protobuf.parseFrom (turnsA.val - turns.val) (stateOf st) := by
      intro n hn
      rw [Model.Protobuf.parseFrom_add]
      exact hn
    split
    · split
      · -- error.isNone: step the reader, then split on remaining
        rename_i hns
        step with Tacenta.ProtobufT1.remaining_spec
        have hnotRefused : (stateOf stA).refused = false := by
          unfold stateOf
          simp only [core.option.Option.is_none] at hns
          cases hc : stA.error with
          | none => rfl
          | some _ => rw [hc] at hns; simp at hns
        have hEqSt : stateOf stA = Model.Protobuf.parseFrom (turnsA.val - turns.val) (stateOf st) :=
          heq hnotRefused
        split
        · -- i > 0: continue
          rename_i hipos
          have hNotEmpty : (stateOf stA).rest.isEmpty = false := by
            simp only [stateOf, remaining_isEmpty]
            simp only [decide_eq_false_iff_not]
            scalar_tac
          step with one_field_refines
          step
          have hstep : Model.Protobuf.parseFrom (turns1.val - turns.val) (stateOf st)
              = Model.Protobuf.oneField (stateOf stA) := by
            have h1 : Model.Protobuf.parseFrom 1 (stateOf stA) = Model.Protobuf.oneField (stateOf stA) := by
              unfold Model.Protobuf.parseFrom
              simp [hnotRefused, hNotEmpty, Model.Protobuf.parseFrom]
            rw [show turns1.val - turns.val = (turnsA.val - turns.val) + 1 from by scalar_tac,
              Model.Protobuf.parseFrom_add, ← hEqSt]
            exact h1
          refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, by scalar_tac⟩
          · rw [hstep]; exact st1_post1
          · intro hr
            rw [hstep]
            exact st1_post2 (st1_post1.symm.trans hr)
        · -- i = 0: done, remaining exhausted
          rename_i hizero
          have hEmpty : (stateOf stA).rest.isEmpty = true := by
            simp only [stateOf, remaining_isEmpty]
            simp only [decide_eq_true_eq]
            scalar_tac
          have hfinish := hfix (MAX_FIELDS.val - turnsA.val)
            (by rw [← hEqSt]; exact Model.Protobuf.parseFrom_stuck _ _ hEmpty)
          rw [show turnsA.val - turns.val + (MAX_FIELDS.val - turnsA.val) = MAX_FIELDS.val - turns.val
            from by scalar_tac] at hfinish
          rw [hfinish, ← hEqSt]
          exact ⟨by rw [hnotRefused], fun _ => rfl⟩
      · -- error.isSome: done, already stopped
        rename_i hns
        have hrefused : (stateOf stA).refused = true := by
          simp only [stateOf, core.option.Option.is_none] at hns ⊢
          cases hc : stA.error with
          | none => simp [hc] at hns
          | some _ => rfl
        have hrefusedM : (Model.Protobuf.parseFrom (turnsA.val - turns.val) (stateOf st)).refused
            = true := hflag.symm.trans hrefused
        have hfinish := hfix (MAX_FIELDS.val - turnsA.val)
          (Model.Protobuf.parseFrom_refused _ _ hrefusedM)
        rw [show turnsA.val - turns.val + (MAX_FIELDS.val - turnsA.val) = MAX_FIELDS.val - turns.val
          from by scalar_tac] at hfinish
        rw [hfinish]
        exact ⟨hflag, fun hc => absurd hc (by rw [hrefused]; decide)⟩
    · have hturnsAeq : turnsA.val = MAX_FIELDS.val := by scalar_tac
      rw [hturnsAeq] at hflag heq
      exact ⟨hflag, heq⟩
  · refine ⟨le_refl _, h, ?_, ?_⟩
    · simp [Model.Protobuf.parseFrom]
    · simp [Model.Protobuf.parseFrom]

/-- The whole ratchet message: `parse_ratchet_body` computes what
`Model.Protobuf.parseRatchetBody` says, on both the accepted message and every
refusal -- the length bound, the loop (via `parse_ratchet_body_loop_refines`),
leftover bytes, and each of the five missing-field checks, `FieldSet.contains`
matched against the model's `seen` through `contains_refines`. No boundary
assumption anywhere in this proof, unlike every other T3 effort in this
project: this crate has none, and `#print axioms` on this theorem confirms it
rests on nothing beyond `propext`, `Classical.choice`, `Quot.sound`. -/
theorem parse_ratchet_body_refines (bytes : alloc.vec.Vec Std.U8) :
    parse_ratchet_body bytes ⦃ fun res =>
      match res with
      | core.result.Result.Ok rb =>
        Model.Protobuf.parseRatchetBody (bytes.val.map byteOf) =
          some { ratchetKey := rb.ratchet_key.val.map byteOf,
                 counter := rb.counter.val,
                 previousCounter := rb.previous_counter.val,
                 ciphertext := rb.ciphertext.val.map byteOf,
                 pq := rb.pq.val.map byteOf }
      | core.result.Result.Err _ =>
        Model.Protobuf.parseRatchetBody (bytes.val.map byteOf) = none ⦄ := by
  unfold parse_ratchet_body Model.Protobuf.parseRatchetBody
  unfold Reader.new
  simp only []
  split
  · -- Reader.new refuses on length: the model refuses on length too.
    have hlen : (List.map byteOf bytes.val).length > Model.Protobuf.maxMessageLen := by
      simp only [List.length_map, Model.Protobuf.maxMessageLen, ← Aeneas.Std.alloc.vec.Vec.len_val]
      have hM : MAX_MESSAGE_LEN.val = 16384 := by unfold MAX_MESSAGE_LEN; rfl
      scalar_tac
    step*
  · have hlen : ¬ (List.map byteOf bytes.val).length > Model.Protobuf.maxMessageLen := by
      simp only [List.length_map, Model.Protobuf.maxMessageLen, ← Aeneas.Std.alloc.vec.Vec.len_val]
      have hM : MAX_MESSAGE_LEN.val = 16384 := by unfold MAX_MESSAGE_LEN; rfl
      scalar_tac
    simp only [hlen, if_neg, not_false_iff]
    unfold FieldSet.new
    have hinit : stateOf { reader := { bytes := bytes, «at» := 0#usize }, seen := { seen := alloc.vec.Vec.new U32 }, ratchet_key := alloc.vec.Vec.new U8, counter := 0#u32, previous_counter := 0#u32, ciphertext := alloc.vec.Vec.new U8, pq := alloc.vec.Vec.new U8, error := none } = Model.Protobuf.initial (bytes.val.map byteOf) := by
      simp [stateOf, remaining, fieldsOf, Model.Protobuf.initial]
    step with parse_ratchet_body_loop_refines { reader := { bytes := bytes, «at» := 0#usize }, seen := { seen := alloc.vec.Vec.new U32 }, ratchet_key := alloc.vec.Vec.new U8, counter := 0#u32, previous_counter := 0#u32, ciphertext := alloc.vec.Vec.new U8, pq := alloc.vec.Vec.new U8, error := none } 0#usize (by scalar_tac)
    have hmf : MAX_FIELDS.val = Model.Protobuf.maxFields := by
      simp [Model.Protobuf.maxFields, MAX_FIELDS]
    simp only [Nat.sub_zero, hinit, hmf] at r_post1 r_post2
    cases hc : r.error with
    | none =>
      simp only []
      have hnotRefused2 : (stateOf r).refused = false := by simp [stateOf, hc]
      have hEq : stateOf r = Model.Protobuf.parseFrom Model.Protobuf.maxFields
          (Model.Protobuf.initial (bytes.val.map byteOf)) := r_post2 hnotRefused2
      step with Tacenta.ProtobufT1.remaining_spec
      have hEmptyIff : (stateOf r).rest.isEmpty = decide (r.reader.bytes.val.length ≤ r.reader.at.val) := by
        simp only [stateOf, remaining_isEmpty]
      split
      · -- leftover bytes: real refuses with TooLong, model refuses too.
        rename_i hipos
        have hNotEmpty : (Model.Protobuf.parseFrom Model.Protobuf.maxFields
            (Model.Protobuf.initial (bytes.val.map byteOf))).rest.isEmpty = false := by
          rw [← hEq, hEmptyIff]
          simp only [decide_eq_false_iff_not]
          scalar_tac
        simp [hNotEmpty]
      · -- nothing left over: proceed to the field-presence checks.
        rename_i hizero
        have hEmpty : (Model.Protobuf.parseFrom Model.Protobuf.maxFields
            (Model.Protobuf.initial (bytes.val.map byteOf))).rest.isEmpty = true := by
          rw [← hEq, hEmptyIff]
          simp only [decide_eq_true_eq]
          scalar_tac
        simp only [hEmpty, Bool.not_true]
        have hQmaxNotRefused : (Model.Protobuf.parseFrom Model.Protobuf.maxFields
            (Model.Protobuf.initial (bytes.val.map byteOf))).refused = false :=
          r_post1.symm.trans hnotRefused2
        simp only [hQmaxNotRefused, Bool.false_eq_true, if_neg, not_false_iff]
        have hseen : fieldsOf r.seen = (Model.Protobuf.parseFrom Model.Protobuf.maxFields
            (Model.Protobuf.initial (bytes.val.map byteOf))).seen := by
          rw [show fieldsOf r.seen = (stateOf r).seen from rfl, hEq]
        have hf1 : FIELD_RATCHET_KEY.val = Model.Protobuf.fieldRatchetKey := by
          simp [Model.Protobuf.fieldRatchetKey, FIELD_RATCHET_KEY]
        have hf2 : FIELD_COUNTER.val = Model.Protobuf.fieldCounter := by
          simp [Model.Protobuf.fieldCounter, FIELD_COUNTER]
        have hf3 : FIELD_PREVIOUS_COUNTER.val = Model.Protobuf.fieldPreviousCounter := by
          simp [Model.Protobuf.fieldPreviousCounter, FIELD_PREVIOUS_COUNTER]
        have hf4 : FIELD_CIPHERTEXT.val = Model.Protobuf.fieldCiphertext := by
          simp [Model.Protobuf.fieldCiphertext, FIELD_CIPHERTEXT]
        have hf5 : FIELD_PQ.val = Model.Protobuf.fieldPq := by
          simp [Model.Protobuf.fieldPq, FIELD_PQ]
        step with contains_refines
        rw [hseen, hf1] at b_post
        split
        · rename_i hb
          have hb_true : Model.Protobuf.seen (Model.Protobuf.parseFrom Model.Protobuf.maxFields
              (Model.Protobuf.initial (bytes.val.map byteOf))).seen Model.Protobuf.fieldRatchetKey = true :=
            b_post.symm.trans hb
          simp only [hb_true, Bool.true_and]
          step with contains_refines
          rw [hseen, hf2] at b1_post
          split
          · rename_i hb1
            have hb1_true : Model.Protobuf.seen (Model.Protobuf.parseFrom Model.Protobuf.maxFields
                (Model.Protobuf.initial (bytes.val.map byteOf))).seen Model.Protobuf.fieldCounter = true :=
              b1_post.symm.trans hb1
            simp only [hb1_true, Bool.true_and]
            step with contains_refines
            rw [hseen, hf3] at b2_post
            split
            · rename_i hb2
              have hb2_true : Model.Protobuf.seen (Model.Protobuf.parseFrom Model.Protobuf.maxFields
                  (Model.Protobuf.initial (bytes.val.map byteOf))).seen Model.Protobuf.fieldPreviousCounter = true :=
                b2_post.symm.trans hb2
              simp only [hb2_true, Bool.true_and]
              step with contains_refines
              rw [hseen, hf4] at b3_post
              split
              · rename_i hb3
                have hb3_true : Model.Protobuf.seen (Model.Protobuf.parseFrom Model.Protobuf.maxFields
                    (Model.Protobuf.initial (bytes.val.map byteOf))).seen Model.Protobuf.fieldCiphertext = true :=
                  b3_post.symm.trans hb3
                simp only [hb3_true, Bool.true_and]
                step with contains_refines
                rw [hseen, hf5] at b4_post
                split
                · rename_i hb4
                  have hb4_true : Model.Protobuf.seen (Model.Protobuf.parseFrom Model.Protobuf.maxFields
                      (Model.Protobuf.initial (bytes.val.map byteOf))).seen Model.Protobuf.fieldPq = true :=
                    b4_post.symm.trans hb4
                  simp only [hb4_true, Bool.not_true]
                  refine congrArg some ?_
                  simp [← hEq, stateOf]
                · rename_i hb4
                  have hb4_false : Model.Protobuf.seen (Model.Protobuf.parseFrom Model.Protobuf.maxFields
                      (Model.Protobuf.initial (bytes.val.map byteOf))).seen Model.Protobuf.fieldPq = false := by
                    simp only [Bool.not_eq_true] at hb4
                    rw [← b4_post, hb4]
                  simp [hb4_false]
              · rename_i hb3
                have hb3_false : Model.Protobuf.seen (Model.Protobuf.parseFrom Model.Protobuf.maxFields
                    (Model.Protobuf.initial (bytes.val.map byteOf))).seen Model.Protobuf.fieldCiphertext = false := by
                  simp only [Bool.not_eq_true] at hb3
                  rw [← b3_post, hb3]
                simp [hb3_false]
            · rename_i hb2
              have hb2_false : Model.Protobuf.seen (Model.Protobuf.parseFrom Model.Protobuf.maxFields
                  (Model.Protobuf.initial (bytes.val.map byteOf))).seen Model.Protobuf.fieldPreviousCounter = false := by
                simp only [Bool.not_eq_true] at hb2
                rw [← b2_post, hb2]
              simp [hb2_false]
          · rename_i hb1
            have hb1_false : Model.Protobuf.seen (Model.Protobuf.parseFrom Model.Protobuf.maxFields
                (Model.Protobuf.initial (bytes.val.map byteOf))).seen Model.Protobuf.fieldCounter = false := by
              simp only [Bool.not_eq_true] at hb1
              rw [← b1_post, hb1]
            simp [hb1_false]
        · rename_i hb
          have hb_false : Model.Protobuf.seen (Model.Protobuf.parseFrom Model.Protobuf.maxFields
              (Model.Protobuf.initial (bytes.val.map byteOf))).seen Model.Protobuf.fieldRatchetKey = false := by
            simp only [Bool.not_eq_true] at hb
            rw [← b_post, hb]
          simp [hb_false]
    | some e =>
      have hrefused : (stateOf r).refused = true := by
        simp only [stateOf, hc]
        rfl
      rw [r_post1.symm.trans hrefused]
      simp

/-! ## The prekey envelope, the other half of item 5

Same technique, a different message shape. `EnvelopeParse` nests a `body`
field rather than carrying its fields flat the way `Parse` does, and one of
its eight fields, `prekey_id`, is optional -- the only optional field in
either message type -- and is deliberately excluded from the missing-field
check, since a bundle with no one-time prekey omits it and the external
profile omits it from well-formed messages. Everything else
below mirrors the ratchet-message proofs above closely enough that the loop
proof in particular carries over almost line for line, once stated against
`Model.PrekeyBody`'s and `Model.EnvelopeParseState`'s own turns-taken
invariant rather than reusing `Model.Protobuf.parseFrom`: that fold, and its
fixed-point/composition lemmas, already ship and are depended on, so a
second, directly-analogous fold over the envelope's own state costs less
than generalizing the first one would. -/

/-- The envelope parse, as the model holds it. Nests `body` to match
`EnvelopeParse`'s own shape. -/
def envelopeStateOf (st : EnvelopeParse) : Model.Protobuf.EnvelopeParseState :=
  { rest := remaining st.reader
    seen := fieldsOf st.seen
    body := { prekeyId := st.body.prekey_id.map (fun v => v.val)
              baseKey := st.body.base_key.val.map byteOf
              identityKey := st.body.identity_key.val.map byteOf
              message := st.body.message.val.map byteOf
              registrationId := st.body.registration_id.val
              signedPrekeyId := st.body.signed_prekey_id.val
              pqPrekeyId := st.body.pq_prekey_id.val
              kem := st.body.kem.val.map byteOf }
    refused := st.error.isSome }

-- Eight field branches rather than five, same reason the ratchet-message
-- proof needed the budget raised: the default does not cover the case split.
set_option maxHeartbeats 4000000 in
/-- Reading one envelope field agrees with the model. Same two-part shape as
`one_field_refines`, one clause per field, `prekeyId` included via the same
`some`-wrapping the real code uses -- nothing here treats the optional field
specially, since `oneEnvelopeField` on the model side already does not. -/
theorem oneEnvelopeField_refines (st : EnvelopeParse) :
    one_envelope_field st ⦃ fun st' =>
      st'.error.isSome = (Model.Protobuf.oneEnvelopeField (envelopeStateOf st)).refused ∧
      ((Model.Protobuf.oneEnvelopeField (envelopeStateOf st)).refused = false →
        envelopeStateOf st' = Model.Protobuf.oneEnvelopeField (envelopeStateOf st)) ⦄ := by
  unfold one_envelope_field Model.Protobuf.oneEnvelopeField
  step*
  repeat' (split <;> (try step*))
  all_goals (try simp_all [envelopeStateOf, fieldsOf,
    Model.Protobuf.fieldPrekeyId, Model.Protobuf.fieldBaseKey, Model.Protobuf.fieldIdentityKey,
    Model.Protobuf.fieldMessage, Model.Protobuf.fieldRegistrationId, Model.Protobuf.fieldSignedPrekeyId,
    Model.Protobuf.fieldPqPrekeyId, Model.Protobuf.fieldKem,
    FIELD_PREKEY_ID, FIELD_BASE_KEY, FIELD_IDENTITY_KEY, FIELD_MESSAGE,
    FIELD_REGISTRATION_ID, FIELD_SIGNED_PREKEY_ID, FIELD_PQ_PREKEY_ID, FIELD_KEM, wireOf])

/-- The envelope loop, against `Model.Protobuf.envelopeParseFrom`. Identical
proof shape to `parse_ratchet_body_loop_refines`: state the invariant against
turns taken, not fuel remaining, and `envelopeParseFrom_add` plus the two
fixed-point lemmas close every exit the same way. -/
theorem parse_prekey_body_loop_refines (st : EnvelopeParse) (turns : Usize)
    (h : turns.val ≤ MAX_FIELDS.val) :
    parse_prekey_body_loop st turns ⦃ fun y =>
      (envelopeStateOf y).refused =
        (Model.Protobuf.envelopeParseFrom (MAX_FIELDS.val - turns.val) (envelopeStateOf st)).refused ∧
      ((envelopeStateOf y).refused = false →
        envelopeStateOf y = Model.Protobuf.envelopeParseFrom (MAX_FIELDS.val - turns.val) (envelopeStateOf st)) ⦄ := by
  unfold parse_prekey_body_loop
  apply loop.spec_decr_nat
    (measure := fun p => MAX_FIELDS.val - p.2.val)
    (inv := fun p =>
      turns.val ≤ p.2.val ∧ p.2.val ≤ MAX_FIELDS.val ∧
      (envelopeStateOf p.1).refused =
        (Model.Protobuf.envelopeParseFrom (p.2.val - turns.val) (envelopeStateOf st)).refused ∧
      ((envelopeStateOf p.1).refused = false →
        envelopeStateOf p.1 = Model.Protobuf.envelopeParseFrom (p.2.val - turns.val) (envelopeStateOf st)))
  · rintro ⟨stA, turnsA⟩ ⟨hturn0, hturn, hflag, heq⟩
    unfold parse_prekey_body_loop.body
    simp only []
    have hfix : ∀ n : Nat, Model.Protobuf.envelopeParseFrom n
        (Model.Protobuf.envelopeParseFrom (turnsA.val - turns.val) (envelopeStateOf st)) =
        Model.Protobuf.envelopeParseFrom (turnsA.val - turns.val) (envelopeStateOf st) →
      Model.Protobuf.envelopeParseFrom (turnsA.val - turns.val + n) (envelopeStateOf st) =
        Model.Protobuf.envelopeParseFrom (turnsA.val - turns.val) (envelopeStateOf st) := by
      intro n hn
      rw [Model.Protobuf.envelopeParseFrom_add]
      exact hn
    split
    · split
      · -- error.isNone: step the reader, then split on remaining
        rename_i hns
        step with Tacenta.ProtobufT1.remaining_spec
        have hnotRefused : (envelopeStateOf stA).refused = false := by
          unfold envelopeStateOf
          simp only [core.option.Option.is_none] at hns
          cases hc : stA.error with
          | none => rfl
          | some _ => rw [hc] at hns; simp at hns
        have hEqSt : envelopeStateOf stA =
            Model.Protobuf.envelopeParseFrom (turnsA.val - turns.val) (envelopeStateOf st) :=
          heq hnotRefused
        split
        · -- i > 0: continue
          rename_i hipos
          have hNotEmpty : (envelopeStateOf stA).rest.isEmpty = false := by
            simp only [envelopeStateOf, remaining_isEmpty]
            simp only [decide_eq_false_iff_not]
            scalar_tac
          step with oneEnvelopeField_refines
          step
          have hstep : Model.Protobuf.envelopeParseFrom (turns1.val - turns.val) (envelopeStateOf st)
              = Model.Protobuf.oneEnvelopeField (envelopeStateOf stA) := by
            have h1 : Model.Protobuf.envelopeParseFrom 1 (envelopeStateOf stA)
                = Model.Protobuf.oneEnvelopeField (envelopeStateOf stA) := by
              unfold Model.Protobuf.envelopeParseFrom
              simp [hnotRefused, hNotEmpty, Model.Protobuf.envelopeParseFrom]
            rw [show turns1.val - turns.val = (turnsA.val - turns.val) + 1 from by scalar_tac,
              Model.Protobuf.envelopeParseFrom_add, ← hEqSt]
            exact h1
          refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, by scalar_tac⟩
          · rw [hstep]; exact st1_post1
          · intro hr
            rw [hstep]
            exact st1_post2 (st1_post1.symm.trans hr)
        · -- i = 0: done, remaining exhausted
          rename_i hizero
          have hEmpty : (envelopeStateOf stA).rest.isEmpty = true := by
            simp only [envelopeStateOf, remaining_isEmpty]
            simp only [decide_eq_true_eq]
            scalar_tac
          have hfinish := hfix (MAX_FIELDS.val - turnsA.val)
            (by rw [← hEqSt]; exact Model.Protobuf.envelopeParseFrom_stuck _ _ hEmpty)
          rw [show turnsA.val - turns.val + (MAX_FIELDS.val - turnsA.val) = MAX_FIELDS.val - turns.val
            from by scalar_tac] at hfinish
          rw [hfinish, ← hEqSt]
          exact ⟨by rw [hnotRefused], fun _ => rfl⟩
      · -- error.isSome: done, already stopped
        rename_i hns
        have hrefused : (envelopeStateOf stA).refused = true := by
          simp only [envelopeStateOf, core.option.Option.is_none] at hns ⊢
          cases hc : stA.error with
          | none => simp [hc] at hns
          | some _ => rfl
        have hrefusedM : (Model.Protobuf.envelopeParseFrom (turnsA.val - turns.val)
            (envelopeStateOf st)).refused = true := hflag.symm.trans hrefused
        have hfinish := hfix (MAX_FIELDS.val - turnsA.val)
          (Model.Protobuf.envelopeParseFrom_refused _ _ hrefusedM)
        rw [show turnsA.val - turns.val + (MAX_FIELDS.val - turnsA.val) = MAX_FIELDS.val - turns.val
          from by scalar_tac] at hfinish
        rw [hfinish]
        exact ⟨hflag, fun hc => absurd hc (by rw [hrefused]; decide)⟩
    · have hturnsAeq : turnsA.val = MAX_FIELDS.val := by scalar_tac
      rw [hturnsAeq] at hflag heq
      exact ⟨hflag, heq⟩
  · refine ⟨le_refl _, h, ?_, ?_⟩
    · simp [Model.Protobuf.envelopeParseFrom]
    · simp [Model.Protobuf.envelopeParseFrom]

/-- The whole prekey envelope: `parse_prekey_body` computes what
`Model.Protobuf.parsePrekeyBody` says, on both the accepted message and every
refusal -- the length bound, the eight-field loop, leftover bytes (an
envelope has no trailing authenticator, so this checks the same way the
ratchet message's does), and each of the seven missing-field refusals
(`prekeyId` excluded, per its own optional-field note above). No boundary
assumption here either. -/
theorem parse_prekey_body_refines (bytes : alloc.vec.Vec Std.U8) :
    parse_prekey_body bytes ⦃ fun res =>
      match res with
      | core.result.Result.Ok rb =>
        Model.Protobuf.parsePrekeyBody (bytes.val.map byteOf) =
          some { prekeyId := rb.prekey_id.map (fun v => v.val),
                 baseKey := rb.base_key.val.map byteOf,
                 identityKey := rb.identity_key.val.map byteOf,
                 message := rb.message.val.map byteOf,
                 registrationId := rb.registration_id.val,
                 signedPrekeyId := rb.signed_prekey_id.val,
                 pqPrekeyId := rb.pq_prekey_id.val,
                 kem := rb.kem.val.map byteOf }
      | core.result.Result.Err _ =>
        Model.Protobuf.parsePrekeyBody (bytes.val.map byteOf) = none ⦄ := by
  unfold parse_prekey_body Model.Protobuf.parsePrekeyBody
  unfold Reader.new
  simp only []
  split
  · -- Reader.new refuses on length: the model refuses on length too.
    have hlen : (List.map byteOf bytes.val).length > Model.Protobuf.maxMessageLen := by
      simp only [List.length_map, Model.Protobuf.maxMessageLen, ← Aeneas.Std.alloc.vec.Vec.len_val]
      have hM : MAX_MESSAGE_LEN.val = 16384 := by unfold MAX_MESSAGE_LEN; rfl
      scalar_tac
    step*
  · have hlen : ¬ (List.map byteOf bytes.val).length > Model.Protobuf.maxMessageLen := by
      simp only [List.length_map, Model.Protobuf.maxMessageLen, ← Aeneas.Std.alloc.vec.Vec.len_val]
      have hM : MAX_MESSAGE_LEN.val = 16384 := by unfold MAX_MESSAGE_LEN; rfl
      scalar_tac
    simp only [hlen, if_neg, not_false_iff]
    unfold FieldSet.new
    have hinit : envelopeStateOf { reader := { bytes := bytes, «at» := 0#usize }, seen := { seen := alloc.vec.Vec.new U32 }, body := { prekey_id := none, base_key := alloc.vec.Vec.new U8, identity_key := alloc.vec.Vec.new U8, message := alloc.vec.Vec.new U8, registration_id := 0#u32, signed_prekey_id := 0#u32, pq_prekey_id := 0#u32, kem := alloc.vec.Vec.new U8 }, error := none } = Model.Protobuf.initialEnvelope (bytes.val.map byteOf) := by
      simp [envelopeStateOf, remaining, fieldsOf, Model.Protobuf.initialEnvelope]
    step with parse_prekey_body_loop_refines { reader := { bytes := bytes, «at» := 0#usize }, seen := { seen := alloc.vec.Vec.new U32 }, body := { prekey_id := none, base_key := alloc.vec.Vec.new U8, identity_key := alloc.vec.Vec.new U8, message := alloc.vec.Vec.new U8, registration_id := 0#u32, signed_prekey_id := 0#u32, pq_prekey_id := 0#u32, kem := alloc.vec.Vec.new U8 }, error := none } 0#usize (by scalar_tac)
    have hmf : MAX_FIELDS.val = Model.Protobuf.maxFields := by
      simp [Model.Protobuf.maxFields, MAX_FIELDS]
    simp only [Nat.sub_zero, hinit, hmf] at r_post1 r_post2
    cases hc : r.error with
    | none =>
      simp only []
      have hnotRefused2 : (envelopeStateOf r).refused = false := by simp [envelopeStateOf, hc]
      have hEq : envelopeStateOf r = Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
          (Model.Protobuf.initialEnvelope (bytes.val.map byteOf)) := r_post2 hnotRefused2
      step with Tacenta.ProtobufT1.remaining_spec
      have hEmptyIff : (envelopeStateOf r).rest.isEmpty
          = decide (r.reader.bytes.val.length ≤ r.reader.at.val) := by
        simp only [envelopeStateOf, remaining_isEmpty]
      split
      · -- leftover bytes: real refuses with TooLong, model refuses too.
        rename_i hipos
        have hNotEmpty : (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
            (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).rest.isEmpty = false := by
          rw [← hEq, hEmptyIff]
          simp only [decide_eq_false_iff_not]
          scalar_tac
        simp [hNotEmpty]
      · -- nothing left over: proceed to the field-presence checks.
        rename_i hizero
        have hEmpty : (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
            (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).rest.isEmpty = true := by
          rw [← hEq, hEmptyIff]
          simp only [decide_eq_true_eq]
          scalar_tac
        simp only [hEmpty, Bool.not_true]
        have hQmaxNotRefused : (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
            (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).refused = false :=
          r_post1.symm.trans hnotRefused2
        simp only [hQmaxNotRefused, Bool.false_eq_true, if_neg, not_false_iff]
        have hseen : fieldsOf r.seen = (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
            (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen := by
          rw [show fieldsOf r.seen = (envelopeStateOf r).seen from rfl, hEq]
        have hf1 : FIELD_BASE_KEY.val = Model.Protobuf.fieldBaseKey := by
          simp [Model.Protobuf.fieldBaseKey, FIELD_BASE_KEY]
        have hf2 : FIELD_IDENTITY_KEY.val = Model.Protobuf.fieldIdentityKey := by
          simp [Model.Protobuf.fieldIdentityKey, FIELD_IDENTITY_KEY]
        have hf3 : FIELD_MESSAGE.val = Model.Protobuf.fieldMessage := by
          simp [Model.Protobuf.fieldMessage, FIELD_MESSAGE]
        have hf4 : FIELD_REGISTRATION_ID.val = Model.Protobuf.fieldRegistrationId := by
          simp [Model.Protobuf.fieldRegistrationId, FIELD_REGISTRATION_ID]
        have hf5 : FIELD_SIGNED_PREKEY_ID.val = Model.Protobuf.fieldSignedPrekeyId := by
          simp [Model.Protobuf.fieldSignedPrekeyId, FIELD_SIGNED_PREKEY_ID]
        have hf6 : FIELD_PQ_PREKEY_ID.val = Model.Protobuf.fieldPqPrekeyId := by
          simp [Model.Protobuf.fieldPqPrekeyId, FIELD_PQ_PREKEY_ID]
        have hf7 : FIELD_KEM.val = Model.Protobuf.fieldKem := by
          simp [Model.Protobuf.fieldKem, FIELD_KEM]
        step with contains_refines
        rw [hseen, hf1] at b_post
        split
        · rename_i hb
          have hb_true : Model.Protobuf.seen (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
              (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen
              Model.Protobuf.fieldBaseKey = true := b_post.symm.trans hb
          simp only [hb_true, Bool.true_and]
          step with contains_refines
          rw [hseen, hf2] at b1_post
          split
          · rename_i hb1
            have hb1_true : Model.Protobuf.seen (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
                (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen
                Model.Protobuf.fieldIdentityKey = true := b1_post.symm.trans hb1
            simp only [hb1_true, Bool.true_and]
            step with contains_refines
            rw [hseen, hf3] at b2_post
            split
            · rename_i hb2
              have hb2_true : Model.Protobuf.seen (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
                  (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen
                  Model.Protobuf.fieldMessage = true := b2_post.symm.trans hb2
              simp only [hb2_true, Bool.true_and]
              step with contains_refines
              rw [hseen, hf4] at b3_post
              split
              · rename_i hb3
                have hb3_true : Model.Protobuf.seen (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
                    (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen
                    Model.Protobuf.fieldRegistrationId = true := b3_post.symm.trans hb3
                simp only [hb3_true, Bool.true_and]
                step with contains_refines
                rw [hseen, hf5] at b4_post
                split
                · rename_i hb4
                  have hb4_true : Model.Protobuf.seen (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
                      (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen
                      Model.Protobuf.fieldSignedPrekeyId = true := b4_post.symm.trans hb4
                  simp only [hb4_true, Bool.true_and]
                  step with contains_refines
                  rw [hseen, hf6] at b5_post
                  split
                  · rename_i hb5
                    have hb5_true : Model.Protobuf.seen (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
                        (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen
                        Model.Protobuf.fieldPqPrekeyId = true := b5_post.symm.trans hb5
                    simp only [hb5_true, Bool.true_and]
                    step with contains_refines
                    rw [hseen, hf7] at b6_post
                    split
                    · rename_i hb6
                      have hb6_true : Model.Protobuf.seen (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
                          (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen
                          Model.Protobuf.fieldKem = true := b6_post.symm.trans hb6
                      simp only [hb6_true, Bool.not_true]
                      refine congrArg some ?_
                      simp [← hEq, envelopeStateOf]
                    · rename_i hb6
                      have hb6_false : Model.Protobuf.seen (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
                          (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen
                          Model.Protobuf.fieldKem = false := by
                        simp only [Bool.not_eq_true] at hb6
                        rw [← b6_post, hb6]
                      simp [hb6_false]
                  · rename_i hb5
                    have hb5_false : Model.Protobuf.seen (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
                        (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen
                        Model.Protobuf.fieldPqPrekeyId = false := by
                      simp only [Bool.not_eq_true] at hb5
                      rw [← b5_post, hb5]
                    simp [hb5_false]
                · rename_i hb4
                  have hb4_false : Model.Protobuf.seen (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
                      (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen
                      Model.Protobuf.fieldSignedPrekeyId = false := by
                    simp only [Bool.not_eq_true] at hb4
                    rw [← b4_post, hb4]
                  simp [hb4_false]
              · rename_i hb3
                have hb3_false : Model.Protobuf.seen (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
                    (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen
                    Model.Protobuf.fieldRegistrationId = false := by
                  simp only [Bool.not_eq_true] at hb3
                  rw [← b3_post, hb3]
                simp [hb3_false]
            · rename_i hb2
              have hb2_false : Model.Protobuf.seen (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
                  (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen
                  Model.Protobuf.fieldMessage = false := by
                simp only [Bool.not_eq_true] at hb2
                rw [← b2_post, hb2]
              simp [hb2_false]
          · rename_i hb1
            have hb1_false : Model.Protobuf.seen (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
                (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen
                Model.Protobuf.fieldIdentityKey = false := by
              simp only [Bool.not_eq_true] at hb1
              rw [← b1_post, hb1]
            simp [hb1_false]
        · rename_i hb
          have hb_false : Model.Protobuf.seen (Model.Protobuf.envelopeParseFrom Model.Protobuf.maxFields
              (Model.Protobuf.initialEnvelope (bytes.val.map byteOf))).seen
              Model.Protobuf.fieldBaseKey = false := by
            simp only [Bool.not_eq_true] at hb
            rw [← b_post, hb]
          simp [hb_false]
    | some e =>
      have hrefused : (envelopeStateOf r).refused = true := by
        simp only [envelopeStateOf, hc]
        rfl
      rw [r_post1.symm.trans hrefused]
      simp

/-! ## What this rests on

Checked rather than asserted, and checked for the two a caller actually uses. -/

/--
info: 'Tacenta.ProtobufT3.tag_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.ProtobufT3.tag_refines

/--
info: 'Tacenta.ProtobufT3.length_delimited_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.ProtobufT3.length_delimited_refines

/--
info: 'Tacenta.ProtobufT3.admit_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.ProtobufT3.admit_refines

/-! ## Where this stops, and what it is waiting on

**Proved.** `byte`, `varint`, `decode_tag`, `tag` and `length_delimited`: what
the reader returns from any byte string is what `Model.Protobuf` says it
returns, and what it refuses is what the model refuses. That is items 3 and 4 of
the verified-core contract.

**Not proved.** Canonical emission and raw-byte fidelity, items 6 and 7
(`LIMITATIONS.md`).

## Why `length_delimited` asks the specification's question

`length_delimited` refuses on `len > self.remaining()`, and the model refuses
on `len > rest.length`; stated that way the two agree unconditionally and no
reader invariant has to be threaded anywhere. Refusing on
`at + len > bytes.len()` instead would agree **only while the cursor is
inside the buffer**, which is a fact about every other method rather than
about this one, and the refinement would then hold because of who the callers
are rather than because of what the function does.

## Why the tier is worth having

Two properties of the model are visible only from the relation, not from
either side alone.

Varints are accumulated under a checked bound rather than in `Nat`. A model
computing in `Nat` would accept thirty-five-bit values the Rust refuses,
describing a decoder **more permissive than the one that ships**. That is the
dangerous direction: a stricter model fails loudly, a looser one licenses a
false statement about which byte strings are accepted.

And the bound is checked on a running total, as the Rust checks it, rather
than on suffix totals: the two forms agree on every answer while disagreeing
at every intermediate state, and the relation is stated on states.

T1 would not ask about either: a decoder that returns the wrong field never
panics doing it. Nor would the thirteen worked examples in the model or the
five tests in the crate, unless one had a case in the range where the two
descriptions part. That is the argument for item 3 stated concretely. -/


/-! The message-level theorems, pinned the same way: the per-field step, the
loop and the whole message, for both message types. Each rests on the three
standard axioms alone, which is what "no boundary assumption anywhere in
either message's proof" means as a build fact rather than a sentence. -/

/-- info: 'Tacenta.ProtobufT3.one_field_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ProtobufT3.one_field_refines

/-- info: 'Tacenta.ProtobufT3.parse_ratchet_body_loop_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ProtobufT3.parse_ratchet_body_loop_refines

/-- info: 'Tacenta.ProtobufT3.parse_ratchet_body_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ProtobufT3.parse_ratchet_body_refines

/-- info: 'Tacenta.ProtobufT3.oneEnvelopeField_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ProtobufT3.oneEnvelopeField_refines

/-- info: 'Tacenta.ProtobufT3.parse_prekey_body_loop_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ProtobufT3.parse_prekey_body_loop_refines

/-- info: 'Tacenta.ProtobufT3.parse_prekey_body_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ProtobufT3.parse_prekey_body_refines

end Tacenta.ProtobufT3
