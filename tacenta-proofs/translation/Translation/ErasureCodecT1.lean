import Translation.ErasureT1

/-!
# T1 for the erasure coder's persistence codecs: restoring a coder cannot fail

`tacenta-erasure`'s `Encoder` and `Decoder` each persist a stream in progress
through a `to_bytes`/`from_bytes` pair, which the Braid calls. This file proves
all four return: every byte string decodes to `Some` or `None`, and every coder
encodes when its buffer fits a `usize`.

## Preconditions and assumptions

- The decoders take `bytes.length + 32 ≤ Usize.max` (`Encoder`) and
  `bytes.length + 34 ≤ Usize.max` (`Decoder`). Each loop computes where the next
  entry would end before it compares that end with the input, and Aeneas models
  a slice as anything up to `Usize.max` long. No Rust slice is that long.
- `Decoder::from_bytes` ends in `invariant`, which calls `chunk_count`, which
  calls `usize::div_ceil`, a declaration the translation cannot see inside. So
  it takes `ErasureT1`'s `DivCeilTotal`, and its pin lists
  `core.num.Usize.div_ceil`.
- The encoders take `7 + 32 * chunks ≤ Usize.max` and
  `20 + 34 * have ≤ Usize.max`. Each ends by asserting the buffer came out as
  long as `encoded_len` said, so the proofs carry exact lengths.
- Neither encoder wraps its buffer in `Zeroizing` -- these bytes are not
  secret -- so no `zeroize` assumption appears.

The translation duplicates `Encoder::from_bytes`'s decode loop and
`Encoder::to_bytes`'s encode loop into both arms of a branch on the exhausted
flag, so each carries two identical specifications.

These are the erasure crate's own translation. In the Braid's translation the
same four functions appear only as opaque declarations, so nothing here reaches
the Braid's calls to them: a proof about the Braid's codec would still have to
assume they return.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.ErasureCodecT1

open tacenta_erasure
open Tacenta.ErasureT1 (DivCeilTotal chunk_count_no_panic)

/-! ## Encoder -/

@[local step]
theorem enc_invariant_no_panic (e : Encoder) : Encoder.invariant e ⦃ fun _ => True ⦄ := by
  unfold Encoder.invariant
  step*

@[local step]
theorem enc_from_bytes_loop0_no_panic (bytes : Slice U8) (iter : core.ops.range.Range Usize)
    (pos : Usize) (chunks : alloc.vec.Vec (Array U8 32#usize)) (ok1 : Bool)
    (hroom : bytes.length + 32 ≤ Usize.max) (hpos : pos.val ≤ bytes.length)
    (hlen : chunks.val.length + (iter.end.val - iter.start.val) ≤ Usize.max) :
    Encoder.from_bytes_loop0 iter bytes pos chunks ok1 ⦃ fun _ => True ⦄ := by
  unfold Encoder.from_bytes_loop0
  apply loop.spec_decr_nat
    (measure := fun x => x.1.end.val - x.1.start.val)
    (inv := fun x => x.2.1.val ≤ bytes.length ∧
      x.2.2.1.val.length + (x.1.end.val - x.1.start.val) ≤ Usize.max)
  · rintro ⟨it, p, cs, b⟩ ⟨hp, hl⟩
    simp only at hp hl ⊢
    unfold Encoder.from_bytes_loop0.body
    simp only [CHUNK_BYTES]
    by_cases hlt : it.start.val < it.end.val
    · step*
      all_goals (try simp_all [Slice.length, Array.repeat])
      all_goals (refine ⟨by scalar_tac, by scalar_tac⟩)
    · step*
  · exact ⟨hpos, hlen⟩

@[local step]
theorem enc_from_bytes_loop1_no_panic (bytes : Slice U8) (iter : core.ops.range.Range Usize)
    (pos : Usize) (chunks : alloc.vec.Vec (Array U8 32#usize)) (ok1 : Bool)
    (hroom : bytes.length + 32 ≤ Usize.max) (hpos : pos.val ≤ bytes.length)
    (hlen : chunks.val.length + (iter.end.val - iter.start.val) ≤ Usize.max) :
    Encoder.from_bytes_loop1 iter bytes pos chunks ok1 ⦃ fun _ => True ⦄ := by
  unfold Encoder.from_bytes_loop1
  apply loop.spec_decr_nat
    (measure := fun x => x.1.end.val - x.1.start.val)
    (inv := fun x => x.2.1.val ≤ bytes.length ∧
      x.2.2.1.val.length + (x.1.end.val - x.1.start.val) ≤ Usize.max)
  · rintro ⟨it, p, cs, b⟩ ⟨hp, hl⟩
    simp only at hp hl ⊢
    unfold Encoder.from_bytes_loop1.body
    simp only [CHUNK_BYTES]
    by_cases hlt : it.start.val < it.end.val
    · step*
      all_goals (try simp_all [Slice.length, Array.repeat])
      all_goals (refine ⟨by scalar_tac, by scalar_tac⟩)
    · step*
  · exact ⟨hpos, hlen⟩

theorem encoder_from_bytes_no_panic (bytes : Slice U8) (hroom : bytes.length + 32 ≤ Usize.max) :
    Encoder.from_bytes bytes ⦃ fun _ => True ⦄ := by
  unfold Encoder.from_bytes
  simp only [CHUNK_BYTES]
  all_goals repeat' (first | simp only [WP.spec_ok] | step | split)
  all_goals (try simp_all [Slice.length, Array.repeat])

/-! ## Decoder -/

@[local step]
theorem dec_invariant_loop_no_panic (self : Decoder) (seen : Array U8 8192#usize) (distinct : Bool)
    (i : Usize) (hi : i.val ≤ self.«have».val.length) :
    Decoder.invariant_loop self seen distinct i ⦃ fun _ => True ⦄ := by
  unfold Decoder.invariant_loop
  apply loop.spec_decr_nat
    (measure := fun p => self.«have».val.length - p.2.2.val)
    (inv := fun p => p.2.2.val ≤ self.«have».val.length)
  · rintro ⟨sn, d, j⟩ hj
    simp only at hj ⊢
    unfold Decoder.invariant_loop.body
    step*
    all_goals (try (split <;> step*))
  · exact hi

@[local step]
theorem dec_invariant_no_panic (hdc : DivCeilTotal) (self : Decoder) :
    Decoder.invariant self ⦃ fun _ => True ⦄ := by
  unfold Decoder.invariant
  all_goals repeat' (first | simp only [WP.spec_ok] | step | (step with chunk_count_no_panic hdc) | split)

@[local step]
theorem dec_from_bytes_loop_no_panic (i : Usize) (bytes : Slice U8) (iter : core.ops.range.Range Usize)
    (pos : Usize) (have1 : alloc.vec.Vec Chunk) (ok1 : Bool) (hi : i.val = 34)
    (hroom : bytes.length + 34 ≤ Usize.max) (hpos : pos.val ≤ bytes.length)
    (hlen : have1.val.length + (iter.end.val - iter.start.val) ≤ Usize.max) :
    Decoder.from_bytes_loop i iter bytes pos have1 ok1 ⦃ fun _ => True ⦄ := by
  unfold Decoder.from_bytes_loop
  apply loop.spec_decr_nat
    (measure := fun x => x.1.end.val - x.1.start.val)
    (inv := fun x => x.2.1.val ≤ bytes.length ∧
      x.2.2.1.val.length + (x.1.end.val - x.1.start.val) ≤ Usize.max)
  · rintro ⟨it, p, hv, b⟩ ⟨hp, hl⟩
    simp only at hp hl ⊢
    unfold Decoder.from_bytes_loop.body
    simp only [CHUNK_BYTES]
    by_cases hlt : it.start.val < it.end.val
    · step*
      all_goals (try simp_all [Slice.length, Array.repeat])
      all_goals (refine ⟨by scalar_tac, by scalar_tac⟩)
    · step*
  · exact ⟨hpos, hlen⟩

theorem decoder_from_bytes_no_panic (hdc : DivCeilTotal) (bytes : Slice U8)
    (hroom : bytes.length + 34 ≤ Usize.max) :
    Decoder.from_bytes bytes ⦃ fun _ => True ⦄ := by
  unfold Decoder.from_bytes
  simp only [CHUNK_BYTES]
  all_goals repeat' (first | simp only [WP.spec_ok] | step | (step with dec_invariant_no_panic hdc) | split)
  all_goals (try simp_all [Slice.length, Array.repeat])
  -- The `u64` bound on a stored `size` is `MAX_CODEWORDS * CHUNK_BYTES`, a
  -- `usize` product; `MAX_CODEWORDS` is irreducible, so unfold it to show the
  -- product fits.
  all_goals (try (simp only [MAX_CODEWORDS]; scalar_tac))


/-! ## Encoding -/

attribute [local step] Tacenta.ErasureT1.extend_u8_spec

@[local step]
theorem enc_to_bytes_loop0_spec (v : alloc.vec.Vec (Array U8 32#usize)) (out : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ v.val.length) (h : out.val.length + 32 * (v.val.length - i.val) ≤ Usize.max) :
    Encoder.to_bytes_loop0 v out i ⦃ fun w => w.val.length = out.val.length + 32 * (v.val.length - i.val) ⦄ := by
  unfold Encoder.to_bytes_loop0
  apply loop.spec_decr_nat
    (measure := fun p => v.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ v.val.length ∧
      p.1.val.length + 32 * (v.val.length - p.2.val) = out.val.length + 32 * (v.val.length - i.val))
  · rintro ⟨o, j⟩ ⟨hj, heq⟩
    simp only at hj heq ⊢
    unfold Encoder.to_bytes_loop0.body
    step*
    all_goals (try simp_all [Array.to_slice])
    all_goals first | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩) | scalar_tac
  · exact ⟨hi, rfl⟩

@[local step]
theorem enc_to_bytes_loop1_spec (v : alloc.vec.Vec (Array U8 32#usize)) (out : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ v.val.length) (h : out.val.length + 32 * (v.val.length - i.val) ≤ Usize.max) :
    Encoder.to_bytes_loop1 v out i ⦃ fun w => w.val.length = out.val.length + 32 * (v.val.length - i.val) ⦄ := by
  unfold Encoder.to_bytes_loop1
  apply loop.spec_decr_nat
    (measure := fun p => v.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ v.val.length ∧
      p.1.val.length + 32 * (v.val.length - p.2.val) = out.val.length + 32 * (v.val.length - i.val))
  · rintro ⟨o, j⟩ ⟨hj, heq⟩
    simp only at hj heq ⊢
    unfold Encoder.to_bytes_loop1.body
    step*
    all_goals (try simp_all [Array.to_slice])
    all_goals first | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩) | scalar_tac
  · exact ⟨hi, rfl⟩

@[local step]
theorem dec_to_bytes_loop_spec (v : alloc.vec.Vec Chunk) (out : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ v.val.length) (h : out.val.length + 34 * (v.val.length - i.val) ≤ Usize.max) :
    Decoder.to_bytes_loop v out i ⦃ fun w => w.val.length = out.val.length + 34 * (v.val.length - i.val) ⦄ := by
  unfold Decoder.to_bytes_loop
  apply loop.spec_decr_nat
    (measure := fun p => v.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ v.val.length ∧
      p.1.val.length + 34 * (v.val.length - p.2.val) = out.val.length + 34 * (v.val.length - i.val))
  · rintro ⟨o, j⟩ ⟨hj, heq⟩
    simp only at hj heq ⊢
    unfold Decoder.to_bytes_loop.body
    step*
    all_goals (try simp_all [Array.to_slice])
    all_goals first | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩) | scalar_tac
  · exact ⟨hi, rfl⟩

@[local step]
theorem enc_encoded_len_spec (e : Encoder) (h : 7 + 32 * e.chunks.val.length ≤ Usize.max) :
    Encoder.encoded_len e ⦃ fun r => r.val = 7 + 32 * e.chunks.val.length ⦄ := by
  unfold Encoder.encoded_len
  simp only [CHUNK_BYTES]
  step*

@[local step]
theorem dec_encoded_len_spec (d : Decoder) (h : 20 + 34 * d.«have».val.length ≤ Usize.max) :
    Decoder.encoded_len d ⦃ fun r => r.val = 20 + 34 * d.«have».val.length ⦄ := by
  unfold Decoder.encoded_len
  simp only [CHUNK_BYTES]
  step*

theorem encoder_to_bytes_no_panic (e : Encoder) (hroom : 7 + 32 * e.chunks.val.length ≤ Usize.max) :
    Encoder.to_bytes e ⦃ fun _ => True ⦄ := by
  unfold Encoder.to_bytes
  simp only [alloc.vec.Vec.with_capacity]
  all_goals repeat' (first | simp only [WP.spec_ok] | step | split)
  all_goals (try simp_all [Array.to_slice])
  all_goals (try scalar_tac)

theorem decoder_to_bytes_no_panic (d : Decoder) (hroom : 20 + 34 * d.«have».val.length ≤ Usize.max) :
    Decoder.to_bytes d ⦃ fun _ => True ⦄ := by
  unfold Decoder.to_bytes
  simp only [alloc.vec.Vec.with_capacity]
  all_goals repeat' (first | simp only [WP.spec_ok] | step | split)
  all_goals (try simp_all [Array.to_slice])
  all_goals (try scalar_tac)

/-- info: 'Tacenta.ErasureCodecT1.encoder_from_bytes_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ErasureCodecT1.encoder_from_bytes_no_panic

-- The axiom audit, enforced rather than asserted. Three of the four rest on the
-- kernel's three axioms alone; the decoder's base adds `usize::div_ceil`, which
-- `DivCeilTotal` is the hypothesis about. A proof that starts trusting
-- something new fails here.
/--
info: 'Tacenta.ErasureCodecT1.decoder_from_bytes_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.ErasureCodecT1.decoder_from_bytes_no_panic

/-- info: 'Tacenta.ErasureCodecT1.encoder_to_bytes_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ErasureCodecT1.encoder_to_bytes_no_panic

/-- info: 'Tacenta.ErasureCodecT1.decoder_to_bytes_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.ErasureCodecT1.decoder_to_bytes_no_panic

end Tacenta.ErasureCodecT1
