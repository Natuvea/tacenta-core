import Translation.TacentaWire

/-!
# T1 for the ratchet-message decoder: totality on the bytes a peer sent

`decode_message` is the first code a ratchet message's bytes reach on the live
receive path, and `decode_composite` is all of its parsing. **Every byte string
returns `Ok` or `Err`, and neither function can fail.** There is no
precondition, because the input is whatever arrived.

The decoder is fixed-width, so the argument is one length check. Once
`bytes.len() >= COMPOSITE_LEN` holds, every index and range the function reads
is inside the input; before it, nothing is read. The one loop, `or_bytes`, reads
a range its caller has already bounded, and its body has no early exit.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.WireT1

open tacenta_wire

/-- The header width is the constant the source computes. -/
@[step]
theorem composite_len_spec : COMPOSITE_LEN ⦃ fun n => n.val = 102 ⦄ := by
  unfold COMPOSITE_LEN
  simp only [CHUNK_BYTES]
  step*

/-- Reading eight big-endian bytes cannot fail when they are inside the input. -/
@[step]
theorem be64_at_no_panic (bytes : Slice U8) (at1 : Usize)
    (h : at1.val + 8 ≤ bytes.length) :
    be64_at bytes at1 ⦃ fun _ => True ⦄ := by
  unfold be64_at
  step*
  all_goals simp_all [Slice.length, Array.repeat]

/-- The padding loop cannot fail over a range inside the input. -/
@[step]
theorem or_bytes_loop_no_panic (bytes : Slice U8) (from1 len : Usize) (acc : U8)
    (i : Usize) (hb : from1.val + len.val ≤ bytes.length) (hi : i.val ≤ len.val) :
    or_bytes_loop bytes from1 len acc i ⦃ fun _ => True ⦄ := by
  unfold or_bytes_loop
  apply loop.spec_decr_nat
    (measure := fun p => len.val - p.2.val)
    (inv := fun p => p.2.val ≤ len.val)
  · rintro ⟨acc1, i1⟩ hi1
    unfold or_bytes_loop.body
    simp only []
    split <;> [skip; simp]
    step*
  · exact hi

/-- Every arm of the agreement-type match returns. Stated as an equation and
split there: the literal byte patterns do not split inside a triple, and
stepping through them unfolded exhausts the heartbeat budget. -/
theorem from_byte_ok (b : U8) : ∃ o, AgreementType.from_byte b = ok o := by
  unfold AgreementType.from_byte
  split <;> exact ⟨_, rfl⟩

/-- Reading the agreement type cannot fail. -/
@[step]
theorem from_byte_no_panic (b : U8) :
    AgreementType.from_byte b ⦃ fun _ => True ⦄ := by
  obtain ⟨o, h⟩ := from_byte_ok b
  rw [h]
  simp

/-- **Decoding a composite header cannot fail, for every byte string.** -/
@[step]
theorem decode_composite_no_panic (bytes : Slice U8) :
    decode_composite bytes ⦃ fun _ => True ⦄ := by
  unfold decode_composite
  simp only [CHUNK_BYTES]
  step*
  all_goals simp_all [Slice.length, Array.repeat]

/-- **Decoding a ratchet message cannot fail, for every byte string.**

The translation takes the decoded pair apart with a pure `let (header, rest)`,
which `step*` does not enter on a pair variable, so the pair is taken apart here
and the copy of the ciphertext stepped after it. -/
@[step]
theorem decode_message_no_panic (bytes : Slice U8) :
    decode_message bytes ⦃ fun _ => True ⦄ := by
  unfold decode_message
  step*
  all_goals (obtain ⟨header, rest⟩ := p; step*)

/-! ## The initial (prekey) message decoder

`decode_initial` computes each field's end with `span_end` before reading
anything, and every read is at a position that check has bounded. So its
totality is `span_end`'s specification, stated in full here because the
refinement needs both of its outcomes. -/

/-- `span_end` returns where the span ends exactly when it fits, and nothing
exactly when it does not. An addition that would overflow `usize` does not fit
either, since no slice is that long. -/
@[step]
theorem span_end_spec (bytes : Slice U8) (at1 n : Usize) :
    span_end bytes at1 n ⦃ o => match o with
      | none => bytes.length < at1.val + n.val
      | some e => e.val = at1.val + n.val ∧ e.val ≤ bytes.length ⦄ := by
  unfold span_end
  step*

/-- Four big-endian bytes cannot fail to read when they are inside the input. -/
@[step]
theorem be32_at_no_panic (bytes : Slice U8) (at1 : Usize) (h : at1.val + 4 ≤ bytes.length) :
    be32_at bytes at1 ⦃ fun _ => True ⦄ := by
  unfold be32_at
  step*

/-- **Decoding an initial message cannot fail, for every byte string.** -/
@[step]
theorem decode_initial_no_panic (bytes : Slice U8) :
    decode_initial bytes ⦃ fun _ => True ⦄ := by
  unfold decode_initial
  step*

-- The axiom audit, enforced rather than asserted: both entry points rest on the
-- kernel's three axioms and nothing else. The decoder calls no opaque operation,
-- so no boundary assumption and no `native_decide` reaches either. A proof that
-- starts trusting something new fails here.
/-- info: 'Tacenta.WireT1.decode_composite_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.WireT1.decode_composite_no_panic

/-- info: 'Tacenta.WireT1.decode_message_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.WireT1.decode_message_no_panic

/-- info: 'Tacenta.WireT1.decode_initial_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.WireT1.decode_initial_no_panic

end Tacenta.WireT1
