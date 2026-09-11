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

/-! ## The canonicity check on a curve key

`is_canonical_x25519` decides whether thirty-two bytes are a curve key's
canonical encoding (message-format.md, Curve public keys). It is the same
function as `tacenta-session`'s, repeated because this crate has no
dependencies, and these are `Translation.SessionT1`'s lemmas about it restated
against this crate's translation: the check's value is proved, not only that it
returns, because the refinement proofs need the value. -/

theorem array32_length (a : Array U8 32#usize) : a.val.length = 32 := by
  simp

/-- Whether every byte of `k` from index `i` up to, not including, thirty-one is
`0xff`: what the canonicity check's loop computes from its cursor onward. -/
def allFFFrom (k : Array U8 32#usize) (i : Nat) : Bool :=
  (List.range' i (31 - i)).all (fun j => (k.val[j]!).val == 255)

theorem allFFFrom_step (k : Array U8 32#usize) (i : Nat) (h : i < 31) :
    allFFFrom k i = (((k.val[i]!).val == 255) && allFFFrom k (i + 1)) := by
  unfold allFFFrom
  have hn : 31 - i = (31 - (i + 1)) + 1 := by omega
  rw [hn, List.range'_succ]
  simp [List.all_cons]

theorem allFFFrom_end (k : Array U8 32#usize) : allFFFrom k 31 = true := by
  simp [allFFFrom]

/-- The predicate `is_canonical_x25519` decides: bit 255 clear, and not the
pattern of a value at least p = 2^255 - 19, which is a last byte of `0x7f`,
thirty bytes of `0xff`, and a first byte of at least `0xed`. -/
def canonicalX25519 (k : Array U8 32#usize) : Bool :=
  decide ((k.val[31]!).val < 128) &&
    !(decide (k.val[31]! = 127#u8) && allFFFrom k 1 && decide (237 ≤ (k.val[0]!).val))

/-- The canonicity check's loop returns the flag it was given, cleared if any
byte from its cursor up to thirty-one is not `0xff`. -/
theorem is_canonical_x25519_loop_spec (k : Array U8 32#usize) (b : Bool) (i : Usize)
    (hi : i.val ≤ 31) :
    is_canonical_x25519_loop k b i ⦃ fun r => r = (b && allFFFrom k i.val) ⦄ := by
  unfold is_canonical_x25519_loop
  apply loop.spec_decr_nat
    (measure := fun x => 31 - (Prod.snd x).val)
    (inv := fun x => (Prod.snd x).val ≤ 31 ∧
      ((Prod.fst x) && allFFFrom k (Prod.snd x).val) = (b && allFFFrom k i.val))
  · rintro ⟨b1, j⟩ ⟨hj, hacc⟩
    simp only at hj hacc ⊢
    simp only [is_canonical_x25519_loop.body]
    by_cases hlt : j.val < 31
    · have hb : j.val < k.val.length := by rw [array32_length k]; omega
      have hstep := allFFFrom_step k j.val hlt
      simp only [getElem!_pos k.val j.val hb] at hstep
      -- The byte under the cursor decides whether the flag survives, and the
      -- tail from the next index carries the rest of the conjunction.
      by_cases hff : (k.val[j.val]'hb).val = 255
      · have h2 : allFFFrom k j.val = allFFFrom k (j.val + 1) := by simp [hstep, hff]
        rw [h2] at hacc
        step*
        all_goals (try split)
        all_goals (try step*)
      · have h2 : allFFFrom k j.val = false := by simp [hstep, hff]
        rw [h2, Bool.and_false] at hacc
        step*
        all_goals (try split)
        all_goals (try step*)
        all_goals (try simp_all)
        all_goals (try scalar_tac)
    · have hj31 : j.val = 31 := by omega
      rw [hj31, allFFFrom_end, Bool.and_true] at hacc
      step*
  · exact ⟨hi, rfl⟩

/-- The canonicity check computes exactly `canonicalX25519`. -/
@[step]
theorem is_canonical_x25519_spec (k : Array U8 32#usize) :
    is_canonical_x25519 k ⦃ fun r => r = canonicalX25519 k ⦄ := by
  unfold is_canonical_x25519 canonicalX25519
  have h31 : 31 < k.val.length := by rw [array32_length k]; omega
  have h0 : 0 < k.val.length := by rw [array32_length k]; omega
  simp only [getElem!_pos k.val 31 h31, getElem!_pos k.val 0 h0]
  have hl := is_canonical_x25519_loop_spec k true 1#usize (by simp)
  simp only [Bool.true_and] at hl
  by_cases h128 : (k.val[31]'h31).val < 128
  · by_cases h127 : k.val[31]'h31 = 127#u8
    · all_goals repeat' (first | simp only [WP.spec_ok] | (step with hl) | step | split)
      all_goals (try simp_all)
    · all_goals repeat' (first | simp only [WP.spec_ok] | (step with hl) | step | split)
      all_goals (try simp_all)
      all_goals (try scalar_tac)
  · all_goals repeat' (first | simp only [WP.spec_ok] | (step with hl) | step | split)
    all_goals (try simp_all)

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

/-- **Decoding an initial message cannot fail, for every byte string.**

The two curve-byte reads, at offset 2 and at the identity's end, are bounded by
the two keys' `span_end` checks; `EC_LEN` is unfolded first so that those
bounds are numbers `step*` can use. The same checks bound the two thirty-two-byte
copies the canonicity checks read, `bytes[3..35]` and `bytes[36..68]`, and what
is left after `step*` is that each copy's source and destination have the same
length, which the `span_end` postconditions give. -/
@[step]
theorem decode_initial_no_panic (bytes : Slice U8) :
    decode_initial bytes ⦃ fun _ => True ⦄ := by
  unfold decode_initial
  simp only [EC_LEN]
  step*
  -- The `span_end` results are named by `o = some end1` and `o1 = some end2`;
  -- substituting them lets their postconditions give the ends' values.
  all_goals (subst_vars; simp_all [Slice.length, Array.repeat])

/-! ## The prekey bundle decoder

`decode_bundle` bounds its fixed prefix with one length check and every later
field with `span_end`, so its totality is the same argument again. The one
optional field is decided by `one_time_prekey_at`, over thirty-three bytes its
caller has already bounded. -/

/-- Deciding the one-time prekey's field cannot fail when its thirty-three bytes
are inside the input. -/
@[step]
theorem one_time_prekey_at_no_panic (bytes : Slice U8) (at1 : Usize) (h : at1.val + 33 ≤ bytes.length) :
    one_time_prekey_at bytes at1 ⦃ fun _ => True ⦄ := by
  unfold one_time_prekey_at
  step*
  all_goals simp_all [Slice.length, Array.repeat]

/-- **Decoding a prekey bundle cannot fail, for every byte string.** -/
@[step]
theorem decode_bundle_no_panic (bytes : Slice U8) :
    decode_bundle bytes ⦃ fun _ => True ⦄ := by
  unfold decode_bundle
  simp only [BUNDLE_KEM_AT]
  step*
  all_goals simp_all [Slice.length, Array.repeat]

-- The axiom audit, enforced rather than asserted: every entry point rests on the
-- kernel's three axioms and nothing else. The decoder calls no opaque operation,
-- so no boundary assumption and no `native_decide` reaches any of them. A proof that
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

/-- info: 'Tacenta.WireT1.decode_bundle_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.WireT1.decode_bundle_no_panic

end Tacenta.WireT1
