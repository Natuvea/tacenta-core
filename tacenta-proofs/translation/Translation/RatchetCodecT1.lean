import Translation.ImportInv
import Translation.SessionT1

/-!
# T1 for the Double Ratchet's persistence codec: decoding stored state cannot fail

`State::from_bytes` parses what a storage layer wrote and hands back a state
the ratchet then runs on. `Translation/ImportInv.lean` proves what a state it
returns satisfies; it says nothing about whether the decoder can panic on the
way. This file proves it cannot: every byte string decodes to an `Ok` or an
`Err`.

## The one precondition

`bytes.length + 72 ≤ Usize.max`. The skipped-key loop computes where the next
72-byte entry would end before it checks that end against the input, and
Aeneas models a slice as anything up to `Usize.max` long, so on a slice within
72 bytes of that ceiling the addition itself would overflow. No Rust slice is
that long: a slice is at most `isize::MAX` bytes, half the `usize` range on
every target, so the hypothesis holds of every buffer a caller can pass. It is
a constant beside `Usize.max`, not another integer type's maximum, so it forces
nothing to zero on a 32-bit target (see `PreconditionShapes.lean`).
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.RatchetCodecT1

open tacenta_ratchet
open Tacenta.ImportInv (slice_index_eq)
open Tacenta.ImportInv.Ratchet (invariant_eq fixed_len_eq optional_key_len_eq skipped_encoded_len_eq)

/-- Thirty-two bytes read at `pos` cannot fail when they are inside the input. -/
@[local step]
theorem read_key_no_panic (v : Slice U8) (pos : Usize) (h : pos.val + 32 ≤ v.length) :
    read_key v pos ⦃ fun _ => True ⦄ := by
  unfold read_key
  step*
  scalar_tac

/-- Four bytes read at `pos` cannot fail when they are inside the input. -/
@[local step]
theorem read_u32_no_panic (v : Slice U8) (pos : Usize) (h : pos.val + 4 ≤ v.length) :
    read_u32 v pos ⦃ fun _ => True ⦄ := by
  unfold read_u32
  step*
  all_goals scalar_tac

/-- The absent key's padding scan cannot fail over thirty-two bytes inside the
input. -/
@[local step]
theorem read_optional_key_loop_no_panic (bytes : Slice U8) (pos : Usize) (clean : Bool) (i : Usize)
    (h : pos.val + 33 ≤ bytes.length) (hi : i.val ≤ pos.val + 33) :
    read_optional_key_loop bytes pos clean i ⦃ fun _ => True ⦄ := by
  unfold read_optional_key_loop
  apply loop.spec_decr_nat
    (measure := fun p => pos.val + 33 - p.2.val)
    (inv := fun p => p.2.val ≤ pos.val + 33)
  · rintro ⟨c, j⟩ hj
    unfold read_optional_key_loop.body
    simp only at hj ⊢
    step*
    all_goals (try (split <;> step*))
  · exact hi

/-- An optional key cannot fail to read when its thirty-three bytes are inside
the input. -/
@[local step]
theorem read_optional_key_no_panic (bytes : Slice U8) (pos : Usize) (h : pos.val + 33 ≤ bytes.length) :
    read_optional_key bytes pos ⦃ fun _ => True ⦄ := by
  have hlt : pos.val < bytes.val.length := by simp only [Slice.length] at h; omega
  unfold read_optional_key
  rw [slice_index_eq bytes pos _ (List.getElem?_eq_getElem hlt)]
  simp only [bind_tc_ok]
  split <;> step*

/-- Reading the label set cannot fail. Stated with both outcomes named, so the
decoder's `match` on it splits: with a bare `True` the stepping tactic cannot
tell the arms apart. -/
theorem label_from_byte_eq (b : U8) :
    ∃ o, LabelSet.from_byte b = ok o ∧ (o = none ∨ o = some LabelSet.Tacenta) := by
  unfold LabelSet.from_byte
  split <;> simp

@[local step]
theorem label_from_byte_spec (b : U8) :
    LabelSet.from_byte b ⦃ fun o => o = none ∨ o = some LabelSet.Tacenta ⦄ := by
  obtain ⟨o, h, ho⟩ := label_from_byte_eq b
  rw [h]
  simpa using ho

/-- One skipped entry's seventy-two bytes cannot fail to decode. -/
@[local step]
theorem skipped_decode_no_panic (bytes : Slice U8) : SkippedKey.decode bytes ⦃ fun _ => True ⦄ := by
  unfold SkippedKey.decode
  simp only [skipped_encoded_len_eq, bind_tc_ok]
  step*
  all_goals simp_all [Slice.length, Array.repeat]

/-- Decoding the entry at `pos` cannot fail, and returns one only when its
seventy-two bytes are inside the input. -/
@[local step]
theorem decode_skipped_entry_spec (bytes : Slice U8) (pos : Usize) (h : pos.val + 72 ≤ Usize.max) :
    decode_skipped_entry bytes pos ⦃ fun o => match o with
      | some _ => pos.val + 72 ≤ bytes.length
      | none => True ⦄ := by
  unfold decode_skipped_entry
  simp only [skipped_encoded_len_eq, bind_tc_ok]
  step*
  all_goals (split <;> first | trivial | scalar_tac)

/-- The skipped-key loop cannot fail. The invariant is that the cursor stays
inside the input, so the next entry's end fits a `usize`, and that the entries
collected plus the iterations still to come fit a `Vec`; the measure is the
iterations left. -/
@[local step]
theorem from_bytes_loop_no_panic (bytes : Slice U8) (iter : core.ops.range.Range Usize) (pos : Usize)
    (skipped : alloc.vec.Vec SkippedKey) (ok1 : Bool)
    (hroom : bytes.length + 72 ≤ Usize.max) (hpos : pos.val ≤ bytes.length)
    (hlen : skipped.val.length + (iter.end.val - iter.start.val) ≤ Usize.max) :
    State.from_bytes_loop 72#usize iter bytes pos skipped ok1 ⦃ fun _ => True ⦄ := by
  unfold State.from_bytes_loop
  apply loop.spec_decr_nat
    (measure := fun x => x.1.end.val - x.1.start.val)
    (inv := fun x => x.2.1.val ≤ bytes.length ∧
      x.2.2.1.val.length + (x.1.end.val - x.1.start.val) ≤ Usize.max)
  · rintro ⟨it, p, sk, b⟩ ⟨hp, hl⟩
    simp only at hp hl ⊢
    unfold State.from_bytes_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step*
      all_goals (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩)
    · step*
  · exact ⟨hpos, hlen⟩

/-- The final check cannot fail: `invariant` computes `InvB`. -/
@[local step]
theorem invariant_no_panic (s : State) : State.invariant s ⦃ fun _ => True ⦄ := by
  rw [invariant_eq]
  simp

/-- **Decoding stored state cannot fail, for every byte string** a Rust slice
can hold. -/
theorem from_bytes_no_panic (bytes : Slice U8) (hroom : bytes.length + 72 ≤ Usize.max) :
    State.from_bytes bytes ⦃ fun _ => True ⦄ := by
  unfold State.from_bytes
  simp only [fixed_len_eq, optional_key_len_eq, skipped_encoded_len_eq, bind_tc_ok]
  all_goals repeat' (first | simp only [WP.spec_ok] | step | split)
  all_goals (rcases hr : r with v | e <;> simp only [])
  all_goals repeat' (first | simp only [WP.spec_ok] | step | split)
  all_goals (rcases hr1 : r1 with v1 | e1 <;> simp only [])
  all_goals repeat' (first | simp only [WP.spec_ok] | step | split)
  all_goals (rcases hr2 : r2 with v2 | e2 <;> simp only [])
  all_goals repeat' (first | simp only [WP.spec_ok] | step | split)


/-! ## Encoding

`State::to_bytes` writes a fixed 185-byte prefix and seventy-two bytes per
skipped key into one buffer, then wraps it in the `zeroize` crate's
`Zeroizing`. The appends use the library's modelled `extend_from_slice`, whose
specification `Translation/SessionT1.lean` proves; the wrapper is an external
crate the translation sees only as a declaration, so its returning is the one
assumption, `ZeroizingVecTotal`. The precondition is that the buffer fits a
`usize`. -/

/-- The `zeroize` crate's wrapper returns on a byte vector. The same kind of
assumption as `T1.lean`'s `ZeroizingTotal`, at the type `to_bytes` wraps. -/
def ZeroizingVecTotal : Prop :=
  ∀ (inst : zeroize.Zeroize (alloc.vec.Vec U8)) (v : alloc.vec.Vec U8),
    ∃ z, zeroize.Zeroizing.new inst v = ok z

@[local step]
theorem label_to_byte_no_panic (l : LabelSet) : LabelSet.to_byte l ⦃ fun _ => True ⦄ := by
  unfold LabelSet.to_byte
  simp

/-- An optional key appends thirty-three bytes. -/
@[local step]
theorem push_optional_key_spec (out : alloc.vec.Vec U8) (key : Option (Array U8 32#usize))
    (h : out.val.length + 33 ≤ Usize.max) :
    push_optional_key out key ⦃ fun w => w.val.length = out.val.length + 33 ⦄ := by
  unfold push_optional_key
  rcases hk : key with _ | k <;> simp only [] <;> step*
  all_goals (try simp_all [Array.to_slice, Array.repeat])

/-- A skipped key appends seventy-two bytes. -/
@[local step]
theorem encode_into_spec (sk : SkippedKey) (out : alloc.vec.Vec U8)
    (h : out.val.length + 72 ≤ Usize.max) :
    SkippedKey.encode_into sk out ⦃ fun w => w.val.length = out.val.length + 72 ⦄ := by
  unfold SkippedKey.encode_into
  step*
  all_goals (try simp_all [Array.to_slice])
  all_goals scalar_tac

/-- The skipped-key loop appends seventy-two bytes per key still to write. -/
@[local step]
theorem to_bytes_loop_spec (v : alloc.vec.Vec SkippedKey) (out : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ v.val.length) (h : out.val.length + 72 * (v.val.length - i.val) ≤ Usize.max) :
    State.to_bytes_loop v out i ⦃ fun w => w.val.length = out.val.length + 72 * (v.val.length - i.val) ⦄ := by
  unfold State.to_bytes_loop
  apply loop.spec_decr_nat
    (measure := fun p => v.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ v.val.length ∧
      p.1.val.length + 72 * (v.val.length - p.2.val) = out.val.length + 72 * (v.val.length - i.val))
  · rintro ⟨o, j⟩ ⟨hj, heq⟩
    simp only at hj heq ⊢
    unfold State.to_bytes_loop.body
    step*
    all_goals (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩)
  · exact ⟨hi, rfl⟩

theorem zeroizing_vec_new_no_panic (hz : ZeroizingVecTotal)
    (inst : zeroize.Zeroize (alloc.vec.Vec U8)) (v : alloc.vec.Vec U8) :
    zeroize.Zeroizing.new inst v ⦃ fun _ => True ⦄ := by
  obtain ⟨z, h⟩ := hz inst v
  rw [h]
  simp

/-- **Encoding a state cannot fail** when its buffer fits a `usize`, given that
the `zeroize` wrapper returns. -/
theorem to_bytes_no_panic (hz : ZeroizingVecTotal) (s : State)
    (hroom : 185 + 72 * s.skipped.val.length ≤ Usize.max) :
    State.to_bytes s ⦃ fun _ => True ⦄ := by
  unfold State.to_bytes
  simp only [fixed_len_eq, skipped_encoded_len_eq, bind_tc_ok, alloc.vec.Vec.with_capacity]
  step*
  all_goals first | exact zeroizing_vec_new_no_panic hz _ _ | skip
  all_goals (try simp_all [Array.to_slice])
  all_goals scalar_tac

/-- The precondition holds of every state `from_bytes` returns: its store is at
most `MAX_SKIPPED_STORE`, 2000 keys, so the buffer is at most 144,185 bytes,
which fits a `usize` on either target Aeneas models. -/
theorem to_bytes_no_panic_of_inv (hz : ZeroizingVecTotal) (s : State)
    (hinv : Tacenta.ImportInv.Ratchet.Inv s) :
    State.to_bytes s ⦃ fun _ => True ⦄ := by
  apply to_bytes_no_panic hz s
  have hb := hinv.store_bound
  have h := Std.Usize.bounds_eq
  simp only [MAX_SKIPPED_STORE] at hb
  rcases h with h | h <;> simp [h] <;> scalar_tac

-- The axiom audit, enforced rather than asserted. The decoder rests on the
-- kernel's three axioms and nothing else. The encoder's base adds the `zeroize`
-- crate's declarations the translation cannot see inside -- the wrapper type,
-- its constructor and the two instances it reaches -- which `ZeroizingVecTotal`
-- is the hypothesis about. A proof that starts trusting something new fails
-- here.
/-- info: 'Tacenta.RatchetCodecT1.from_bytes_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.RatchetCodecT1.from_bytes_no_panic

/--
info: 'Tacenta.RatchetCodecT1.to_bytes_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 zeroize.Zeroize.Blanket.zeroize,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.RatchetCodecT1.to_bytes_no_panic

/--
info: 'Tacenta.RatchetCodecT1.to_bytes_no_panic_of_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 zeroize.Zeroize.Blanket.zeroize,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.RatchetCodecT1.to_bytes_no_panic_of_inv

end Tacenta.RatchetCodecT1
