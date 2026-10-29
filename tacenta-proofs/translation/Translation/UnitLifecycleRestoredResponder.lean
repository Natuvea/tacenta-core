import Translation.UnitLifecycleEncryptCompose

/-!
# The responder's session after its first receipt, exported, imported and continued

`UnitLifecycleRestoredSession` proves the round trip `Session::export` then `Session::import` for the shape an
established initiator session has (agreement at `KeysUnsampled`, a pending initial message, no established ephemeral),
and `restored_established_continues` for that side only.  This module proves it for the responder: the session
`establish_responder` returns on the initiator's first frame, whose agreement waits for the header with an erasure
decoder holding at most one chunk, with no pending initial message and an established ephemeral.  Since `import`
returns that session itself, every field equal, every result about it holds of the restored copy; no relation for a
restored decoder is needed.

## What it shows

* The decoder's codec (`decEnc`, `dec_to_bytes_spec`, `dec_from_bytes_of`, with the loop lemmas): `Decoder::to_bytes`
  of a decoder holding at most one chunk writes `decEnc`, and `Decoder::from_bytes` of those bytes returns the decoder,
  when it passes `Decoder::invariant` and its sizes are within the format's caps.
* The agreement's codec while it waits for the header (`braidEncNH`, `braid_to_bytes_nh_spec`, `decode_state_nh_of`,
  `braid_from_bytes_nh_of`), with the length-prefix helpers of the Braid (`braid_push_len_prefixed_spec`,
  `braid_take_len_prefixed_of`).
* The session's codec at the responder's shape (`CodecShapeR`, `sessionEncR`, `export_spec_R`,
  `import_unchecked_spec_R`, `export_import_of_shape_R`): for every session of that shape that passes
  `Session::invariant`, `import` of the exported bytes accepts and returns the session itself.
* At the responder's session: `Session::structural_invariant` fixes an established ephemeral to 33 bytes
  (`established_len_of_structural`, with `decode_ec_none_of_len`); the decoder the agreement holds after the first
  receipt holds at most one chunk (`received_decoder_small`, `first_receipt_successor_shape_small`, the existing walk
  with that fact kept); a decoder that passes `Decoder::invariant` is for at most `32 · MAX_CODEWORDS` bytes
  (`invariant_size_le`, under `DivCeilValue`); the session has the shape (`received_codecShapeR`) and room for every
  `j` operations with `j + 3 < u32::MAX` (`received_counterRoom`).
* `first_receipt_successor_round_trip`, `responder_first_frame_restored`, `initiator_first_send_responder_restored`:
  **at every successful return of `establish_responder` on the initiator's first frame, the session it returns
  refines `firstReceiptSession`, passes `Session::invariant`, meets the ceilings, has that budget, and the bytes
  `export` writes for it are accepted by `import`, which returns that session itself**, under the hypotheses of
  `responder_first_frame_successor` (resp. `initiator_first_send_responder_successor_hypotheses`) and four laws of the
  round trip.
* `responder_first_frame_restored_encrypt`: **restore then continue on the responder's side**: every session `import`
  accepts those bytes with is that session, and the public `encrypt` there refines the model's step at
  `firstReceiptSession` and leaves a session that passes the invariant with room for `k` operations
  (`encrypt_refines_keeps_invariant` of `UnitLifecycleEncryptCompose`).
* `first_send_restored_reachable`: a run at the real constants, under the reach's laws and the four laws of the round
  trip, from `publish` through the first send to a successful `establish_responder` whose session survives the round
  trip as itself.

## The laws and premises

No new law.  The round trip takes the five laws of the initiator's round trip (`ZeroizingVecRoundTrip`,
`OptionBranchSome`, `VecAsSlice`, `DhPrivateBytesRoundTrip`, `DhPublicBytesRoundTrip`), with `DivCeilValue` and
`DhCodecTotal` (fields of the responder's contracts).  The receipt's hypotheses are those of
`responder_first_frame_successor`, among them `DecryptOracleOf`, whose AEAD open clause is false of the shipping AEAD by
reading at long lengths (row `AEAD-LENGTH-CONTRACTS`), and `AeadRoundTrip`; the continuation with `encrypt` adds the
encrypt boundary records, among them `AeadSealBounded` and `OracleOf` (likewise false by reading).  So, as stated,
these results say nothing about the shipping code at any length until those contracts are repaired.  The
continuation takes an encrypt oracle whose Braid KEM is the receipt's (`hK`).  The round-trip statements list the
compiler-trust axiom every export and import statement carries (the `toStr` bound of `export`'s panic message).

## Non-vacuity

`first_send_restored_reachable` exhibits a run (last-resort path, empty plaintext) at the real constants under the
reach's laws and the four laws of the round trip, all of which hold together in `Interp.modelFirstReceipt`
(`first_receipt_laws_model`): consistency in a model, not exhibition of the shipping code.  The continuation with
`encrypt` is not exhibited on that run here.

## What it does not show

* A responder session at a later state (after its reply, after a second receipt, at any state holding a key pair, an
  encapsulation state or an encoder), a decoder holding more than one chunk, or stored skipped keys: the codec shape
  here is the first receipt's.
* `Session::clone`, or a copy restored from bytes the session did not write.
* The continuation with `encrypt` on a run: the reach exhibits the round trip only.
* The continuation with `decrypt` as a theorem (its session-side premises, the relation, the invariant and the
  ceilings, hold at the restored copy because it is the same session; the frame's chunk relation and draw are the
  caller's).
* That the real primitives meet the boundary records or the laws; the AEAD contracts are false of the shipping AEAD
  by reading at long lengths.
* That `Session::invariant` says a session is reachable: it is a predicate on fields.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv)

namespace Tacenta.UnitLifecycleRestoredResponder

open Tacenta.UnitLifecycleSessionCodec
open Tacenta.UnitLifecycleSendPreserve (CounterRoom)
open Tacenta.UnitLifecycleEncryptPreserve (SendInvariantLaws)
open Tacenta.UnitLifecycleSessionRoundTrip (slice_ne_self session_invariant_leaves)

def be16 (x : U16) : List U8 := (core.num.U16.to_be_bytes x).val
theorem be16_length (x : U16) : (be16 x).length = 2 := (core.num.U16.to_be_bytes x).property

/-- The bytes a chunk takes in a decoder's encoding: its index, big-endian, then its 32 data bytes. -/
def chunkEnc (c : tacenta_erasure.Chunk) : List U8 := be16 c.index ++ c.data.val

theorem chunkEnc_length (c : tacenta_erasure.Chunk) : (chunkEnc c).length = 34 := by
  simp [chunkEnc, be16_length]

/-- The bytes `Decoder::to_bytes` writes for a decoder holding at most one chunk. -/
def decEnc (d : tacenta_erasure.Decoder) : List U8 :=
  be64 (UScalar.cast .U64 d.size) ++ (be64 (UScalar.cast .U64 d.needed) ++
    (be32 (UScalar.cast .U32 (alloc.vec.Vec.len d.«have»)) ++ d.«have».val.flatMap chunkEnc))

theorem dec_to_bytes_loop_empty (v : alloc.vec.Vec tacenta_erasure.Chunk) (out : alloc.vec.Vec U8)
    (hv : v.val = []) : tacenta_erasure.Decoder.to_bytes_loop v out 0#usize ⦃ w => w = out ⦄ := by
  unfold tacenta_erasure.Decoder.to_bytes_loop
  rw [loop.eq_def]
  simp [tacenta_erasure.Decoder.to_bytes_loop.body, alloc.vec.Vec.len, hv]

theorem dec_to_bytes_loop_one (v : alloc.vec.Vec tacenta_erasure.Chunk) (out : alloc.vec.Vec U8)
    (c : tacenta_erasure.Chunk) (hv : v.val = [c]) (h : out.val.length + 34 ≤ Usize.max) :
    tacenta_erasure.Decoder.to_bytes_loop v out 0#usize ⦃ w => w.val = out.val ++ chunkEnc c ⦄ := by
  unfold tacenta_erasure.Decoder.to_bytes_loop
  apply loop.spec_decr_nat
    (measure := fun p => 1 - p.2.val)
    (inv := fun p => (p.2.val = 0 ∧ p.1 = out) ∨ (p.2.val = 1 ∧ p.1.val = out.val ++ chunkEnc c))
  · rintro ⟨o, j⟩ hinv
    simp only at hinv ⊢
    unfold tacenta_erasure.Decoder.to_bytes_loop.body
    have hlen : v.len = 1#usize := by
      rw [UScalar.eq_equiv]; simp [alloc.vec.Vec.len, hv]
    rcases hinv with ⟨hj, ho⟩ | ⟨hj, ho⟩
    · subst ho
      have hj0 : j = 0#usize := by rw [UScalar.eq_equiv]; simpa using hj
      subst hj0
      have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice tacenta_erasure.Chunk)
          v 0#usize = ok c :=
        Tacenta.SessionUnitRatchetImportInv.vec_index_eq _ _ _ (by simp [hv])
      simp only [hlen, hidx]
      step*
      all_goals (try simp_all [Array.to_slice, chunkEnc, be16, core.num.U16.to_be_bytes])
      all_goals (try scalar_tac)
    · simp only [hlen]
      step*
  · exact Or.inl ⟨by simp, rfl⟩

@[local step]
theorem dec_encoded_len_spec (d : tacenta_erasure.Decoder) (hl : d.«have».val.length ≤ 1) :
    tacenta_erasure.Decoder.encoded_len d ⦃ r => r.val = 20 + 34 * d.«have».val.length ⦄ := by
  unfold tacenta_erasure.Decoder.encoded_len
  step*
  all_goals (simp_all [alloc.vec.Vec.len, tacenta_erasure.CHUNK_BYTES]; try scalar_tac)

@[local step]
theorem dec_to_bytes_spec (d : tacenta_erasure.Decoder) (hl : d.«have».val.length ≤ 1) :
    tacenta_erasure.Decoder.to_bytes d ⦃ v => v.val = decEnc d ⦄ := by
  unfold tacenta_erasure.Decoder.to_bytes
  step with dec_encoded_len_spec d hl as ⟨len, hlen⟩
  simp only [alloc.vec.Vec.with_capacity]
  have hlenv : d.«have».len.val = d.«have».val.length := by simp [alloc.vec.Vec.len]
  rcases hv : d.«have».val with _ | ⟨c, _ | ⟨c', rest⟩⟩
  · step*
    · simp only [out2_post, out1_post, s_post, s1_post, s2_post, Array.to_slice, a_post, a1_post, a2_post]
      simp; scalar_tac
    step with dec_to_bytes_loop_empty _ _ hv as ⟨out4, hout4⟩
    rw [hout4]
    have hl3 : (alloc.vec.Vec.len out3).val = 20 := by
      simp only [alloc.vec.Vec.len, out3_post, out2_post, out1_post, s_post, s1_post, s2_post, Array.to_slice,
        a_post, a1_post, a2_post]; simp
    have : alloc.vec.Vec.len out3 = len := by
      rw [UScalar.eq_equiv, hl3, hlen, hv]; rfl
    simp only [this, massert, if_true, bind_tc_ok]
    simp only [WP.spec_ok]
    simp only [out3_post, out2_post, out1_post, s_post, s1_post, s2_post, Array.to_slice, a_post, a1_post, a2_post,
      i_post, i1_post, i3_post, decEnc, be64, be32, core.num.U64.to_be_bytes, core.num.U32.to_be_bytes, hv,
      List.flatMap_nil, List.append_nil, List.nil_append, List.append_assoc]
  · step*
    · simp only [out2_post, out1_post, s_post, s1_post, s2_post, Array.to_slice, a_post, a1_post, a2_post]
      simp; scalar_tac
    step with dec_to_bytes_loop_one _ _ c hv as ⟨out4, hout4⟩
    · simp only [out3_post, out2_post, out1_post, s_post, s1_post, s2_post, Array.to_slice, a_post, a1_post,
        a2_post]; simp; scalar_tac
    have hl4 : (alloc.vec.Vec.len out4).val = 54 := by
      simp only [alloc.vec.Vec.len, hout4, out3_post, out2_post, out1_post, s_post, s1_post, s2_post,
        Array.to_slice, a_post, a1_post, a2_post]; simp [chunkEnc_length]
    have : alloc.vec.Vec.len out4 = len := by
      rw [UScalar.eq_equiv, hl4, hlen, hv]; rfl
    simp only [this, massert, if_true, bind_tc_ok]
    simp only [WP.spec_ok]
    simp only [hout4, out3_post, out2_post, out1_post, s_post, s1_post, s2_post, Array.to_slice, a_post, a1_post,
      a2_post, i_post, i1_post, i3_post, decEnc, be64, be32, core.num.U64.to_be_bytes, core.num.U32.to_be_bytes,
      hv, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.append_assoc]
  · rw [hv] at hl; simp at hl

theorem from_be16 (x : U16) (a : Array U8 2#usize) (h : a.val = be16 x) :
    core.num.U16.from_be_bytes a = x := by
  have hl : (List.map U8.bv a.val) = x.bv.toBEBytes := by
    rw [h]; simp [be16, core.num.U16.to_be_bytes]
  obtain ⟨xb⟩ := x
  simp only [core.num.U16.from_be_bytes]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_cast, fromBEBytes_toNat_congr hl, fromBEBytes_toBEBytes_toNat (by decide)]

theorem dec_from_bytes_loop_empty (bytes : Slice U8) (pos : Usize) (v : alloc.vec.Vec tacenta_erasure.Chunk)
    (b : Bool) :
    tacenta_erasure.Decoder.from_bytes_loop 34#usize { start := 0#usize, «end» := 0#usize } bytes pos v b
      ⦃ r => r = (pos, v, b) ⦄ := by
  unfold tacenta_erasure.Decoder.from_bytes_loop
  apply loop.spec_decr_nat
    (measure := fun _ => 0)
    (inv := fun p => p.1.end.val ≤ p.1.start.val ∧ p.2 = (pos, v, b))
  · rintro ⟨⟨st, en⟩, pos', v', b'⟩ ⟨h1, h2⟩
    simp only at h1 h2
    simp only [tacenta_erasure.Decoder.from_bytes_loop.body]
    step*
  · exact ⟨by simp, rfl⟩

theorem dec_from_bytes_loop_one (bytes : Slice U8) (pos : Usize) (c : tacenta_erasure.Chunk) (rest : List U8)
    (h : bytes.val.drop pos.val = chunkEnc c ++ rest)
    (v : alloc.vec.Vec tacenta_erasure.Chunk) (hv : v.val = []) :
    tacenta_erasure.Decoder.from_bytes_loop 34#usize { start := 0#usize, «end» := 1#usize } bytes pos v true
      ⦃ r => r.1.val = pos.val + 34 ∧ r.2.1.val = [c] ∧ r.2.2 = true ⦄ := by
  have hl := length_of_drop h (by rw [chunkEnc_length]; decide)
  rw [chunkEnc_length] at hl
  have hidx : bytes.val.drop pos.val = be16 c.index ++ (c.data.val ++ rest) := by
    rw [h]; simp [chunkEnc]
  have hdat : bytes.val.drop (pos.val + 2) = c.data.val ++ rest := by
    have := drop_next hidx; rwa [be16_length] at this
  unfold tacenta_erasure.Decoder.from_bytes_loop
  apply loop.spec_decr_nat
    (measure := fun p => 1 - p.1.start.val)
    (inv := fun p => p.1.end = 1#usize ∧ p.2.2.2 = true ∧
      ((p.1.start.val = 0 ∧ p.2.1 = pos ∧ p.2.2.1 = v) ∨
       (p.1.start.val = 1 ∧ p.2.1.val = pos.val + 34 ∧ p.2.2.1.val = [c])))
  · rintro ⟨⟨st, en⟩, p', ch, ok'⟩ ⟨hend, hok, hcase⟩
    simp only at hend hok hcase ⊢
    unfold tacenta_erasure.Decoder.from_bytes_loop.body
    rcases hcase with ⟨hs, hp, hc⟩ | ⟨hs, hp, hc⟩
    · subst hp hc
      step*
      · have hcb : tacenta_erasure.CHUNK_BYTES.val = 32 := by simp [tacenta_erasure.CHUNK_BYTES]
        have := bytes.property
        scalar_tac
      · exfalso
        rename_i hlt
        have hcb : tacenta_erasure.CHUNK_BYTES.val = 32 := by simp [tacenta_erasure.CHUNK_BYTES]
        have hlen : bytes.len.val = bytes.val.length := by simp [Slice.len]
        scalar_tac
      · rw [s1_post2, i2_post]; simp [Slice.length, s_post1]
      · rw [s4_post2, i4_post, i2_post]; simp [Slice.length, s3_post1, tacenta_erasure.CHUNK_BYTES]
      · have hst : st = 0#usize := by rw [UScalar.eq_equiv]; simpa using hs
        subst hst
        rw [hend] at o_post1 o_post2
        rw [if_pos (by scalar_tac)] at o_post1
        have hs1 : s1.val = be16 c.index := by
          rw [s1_post1, i2_post]; exact slice_of_drop hidx (by rw [be16_length])
        have hb : (to_slice_mut_back s2).val = be16 c.index := by
          rw [s_post2, s2_post, Array.from_slice_val _ _ (by rw [hs1, be16_length]; simp), hs1]
        have hi5 : i5 = c.index := by
          rw [← from_be16 c.index _ hb, UScalar.eq_equiv_bv_eq]; exact i5_post
        have hd : to_slice_mut_back1 s5 = c.data := by
          rw [s3_post2, s5_post]
          exact from_slice_eq _ _ _ (by
            rw [s4_post1, i4_post, i2_post]
            exact slice_of_drop hdat (by simp [tacenta_erasure.CHUNK_BYTES]))
        refine ⟨o_post2, hok, Or.inr ⟨by simp [o_post1.2], pos1_post, ?_⟩, by simp [o_post1.2]⟩
        rw [have2_post, hv, hi5, hd]
        rfl
    · step*
  · exact ⟨rfl, rfl, Or.inl ⟨by simp, rfl, rfl⟩⟩

theorem decEnc_length (d : tacenta_erasure.Decoder) (hl : d.«have».val.length ≤ 1) :
    (decEnc d).length = 20 + 34 * d.«have».val.length := by
  rcases hv : d.«have».val with _ | ⟨c, _ | ⟨c', rest⟩⟩
  · simp [decEnc, hv, be64_length, be32_length]
  · simp [decEnc, hv, be64_length, be32_length, chunkEnc_length]
  · rw [hv] at hl; simp at hl

theorem cast_u64_usize_val (x : Usize) : (UScalar.cast UScalarTy.U64 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  have := x.hBounds
  have h := Usize.bounds_eq
  have : x.val < 2 ^ 64 := by
    rcases h with h | h <;> scalar_tac
  simp [UScalarTy.numBits]; omega

theorem cast_usize_cast_u64 (x : Usize) : UScalar.cast .Usize (UScalar.cast .U64 x) = x := by
  rw [UScalar.eq_equiv, UScalar.cast_val_eq, UScalar.cast_val_eq]
  have hb : x.val < 18446744073709551616 := by
    rcases Usize.bounds_eq with h | h <;> scalar_tac
  have hx : x.val < 2 ^ System.Platform.numBits := by
    have := x.hBounds; simpa [UScalar.max, UScalarTy.numBits] using this
  simp only [UScalarTy.numBits]
  have h1 : x.val % 2 ^ 64 = x.val := Nat.mod_eq_of_lt (by simpa using hb)
  rw [h1, Nat.mod_eq_of_lt hx]

theorem dec_from_bytes_of (bytes : Slice U8) (d : tacenta_erasure.Decoder) (hb : bytes.val = decEnc d)
    (hl : d.«have».val.length ≤ 1) (hinv : tacenta_erasure.Decoder.invariant d = ok true)
    (hneed : d.needed.val ≤ 65536) (hsize : d.size.val ≤ 65536 * 32) :
    tacenta_erasure.Decoder.from_bytes bytes = ok (some d) := by
  have hlenB : bytes.val.length = 20 + 34 * d.«have».val.length := by rw [hb, decEnc_length d hl]
  have hblen : (Slice.len bytes).val = 20 + 34 * d.«have».val.length := by simp [Slice.len, hlenB]
  have hd0 : bytes.val.drop 0 = be64 (UScalar.cast .U64 d.size) ++ (be64 (UScalar.cast .U64 d.needed) ++
      (be32 (UScalar.cast .U32 (alloc.vec.Vec.len d.«have»)) ++ d.«have».val.flatMap chunkEnc)) := by
    rw [hb]; rfl
  have hd8 := drop_next hd0
  rw [be64_length] at hd8
  have hd16 := drop_next hd8
  rw [be64_length] at hd16
  have hd20 := drop_next hd16
  rw [be32_length] at hd20
  have hsl0 : List.slice 0 8 bytes.val = be64 (UScalar.cast .U64 d.size) :=
    slice_of_drop hd0 (by rw [be64_length])
  have hsl8 : List.slice 8 16 bytes.val = be64 (UScalar.cast .U64 d.needed) :=
    slice_of_drop hd8 (by rw [be64_length])
  have hsl16 : List.slice 16 20 bytes.val = be32 (UScalar.cast .U32 (alloc.vec.Vec.len d.«have»)) :=
    slice_of_drop hd16 (by rw [be32_length])
  have hmc : tacenta_erasure.MAX_CODEWORDS.val = 65536 := by simp [tacenta_erasure.MAX_CODEWORDS]
  have hcb : tacenta_erasure.CHUNK_BYTES.val = 32 := by simp [tacenta_erasure.CHUNK_BYTES]
  have hsv := cast_u64_usize_val d.size
  have hnv := cast_u64_usize_val d.needed
  have hhl : (alloc.vec.Vec.len d.«have»).val = d.«have».val.length := by simp [alloc.vec.Vec.len]
  have hcl : (UScalar.cast UScalarTy.U32 (alloc.vec.Vec.len d.«have»)).val = d.«have».val.length := by
    rw [UScalar.cast_val_eq]; simp [UScalarTy.numBits, hhl]; omega
  have hs : tacenta_erasure.Decoder.from_bytes bytes ⦃ r => r = some d ⦄ := by
    unfold tacenta_erasure.Decoder.from_bytes
    step*
    · rw [s1_post2]; simp [Slice.length, s_post1]
    · rw [s4_post2]; simp [Slice.length, s3_post1]
    · exfalso
      have hgt : needed_wide > i3 := by assumption
      have hb1 : (to_slice_mut_back1 s5).val = be64 (UScalar.cast .U64 d.needed) := by
        rw [s3_post2, s5_post, Array.from_slice_val _ _ (by rw [s4_post1, hsl8, be64_length]; simp), s4_post1, hsl8]
      have := u64_eq_of_bv needed_wide _ _ needed_wide_post hb1
      rw [this, i3_post] at hgt
      have h3 : (UScalar.cast UScalarTy.U64 tacenta_erasure.MAX_CODEWORDS).val = 65536 := by
        rw [cast_u64_usize_val, hmc]
      scalar_tac
    · exfalso
      have hgt : size_wide > i5 := by assumption
      have hb0 : (to_slice_mut_back s2).val = be64 (UScalar.cast .U64 d.size) := by
        rw [s_post2, s2_post, Array.from_slice_val _ _ (by rw [s1_post1, hsl0, be64_length]; simp), s1_post1, hsl0]
      have := u64_eq_of_bv size_wide _ _ size_wide_post hb0
      rw [this, i5_post] at hgt
      have h5 : (UScalar.cast UScalarTy.U64 i4).val = 65536 * 32 := by
        rw [cast_u64_usize_val, i4_post, hmc, hcb]
      scalar_tac
    · rw [s7_post2]; simp [Slice.length, s6_post1]
    · exfalso
      have hgt : count > i9 := by assumption
      have hb2 : (to_slice_mut_back2 s8).val = be32 (UScalar.cast .U32 (alloc.vec.Vec.len d.«have»)) := by
        rw [s6_post2, s8_post, Array.from_slice_val _ _ (by rw [s7_post1, hsl16, be32_length]; simp), s7_post1,
          hsl16]
      have hi6 := u32_eq_of_bv i6 _ _ i6_post hb2
      have hi6v : i6.val = d.«have».val.length := by rw [hi6, hcl]
      have hcv : count.val = d.«have».val.length := by
        have : count.val = i6.val := by rw [count_post]; scalar_tac
        omega
      have h9 : i9.val = d.«have».val.length := by
        rw [i9_post, hblen, i8_post, hcb]; omega
      scalar_tac
    · have hb2 : (to_slice_mut_back2 s8).val = be32 (UScalar.cast .U32 (alloc.vec.Vec.len d.«have»)) := by
        rw [s6_post2, s8_post, Array.from_slice_val _ _ (by rw [s7_post1, hsl16, be32_length]; simp), s7_post1,
          hsl16]
      have hi6 := u32_eq_of_bv i6 _ _ i6_post hb2
      have hi6v : i6.val = d.«have».val.length := by rw [hi6, hcl]
      have hcv : count.val = d.«have».val.length := by
        have : count.val = i6.val := by rw [count_post]; scalar_tac
        omega
      have hi8 : i8 = 34#usize := by rw [UScalar.eq_equiv, i8_post, hcb]; rfl
      have hb0 : (to_slice_mut_back s2).val = be64 (UScalar.cast .U64 d.size) := by
        rw [s_post2, s2_post, Array.from_slice_val _ _ (by rw [s1_post1, hsl0, be64_length]; simp), s1_post1, hsl0]
      have hsw := u64_eq_of_bv size_wide _ _ size_wide_post hb0
      have hb1 : (to_slice_mut_back1 s5).val = be64 (UScalar.cast .U64 d.needed) := by
        rw [s3_post2, s5_post, Array.from_slice_val _ _ (by rw [s4_post1, hsl8, be64_length]; simp), s4_post1, hsl8]
      have hnw := u64_eq_of_bv needed_wide _ _ needed_wide_post hb1
      have hsz : size = d.size := by rw [size_post, hsw, cast_usize_cast_u64]
      have hnd : needed = d.needed := by rw [needed_post, hnw, cast_usize_cast_u64]
      rw [hi8, hsz, hnd]
      have hdv : ∀ (v : alloc.vec.Vec tacenta_erasure.Chunk), v.val = d.«have».val →
          ({ size := d.size, needed := d.needed, «have» := v } : tacenta_erasure.Decoder) = d := by
        intro v hv'
        obtain ⟨ds, dn, dh⟩ := d
        simp only at hv' ⊢
        rw [Subtype.ext hv']
      rcases hv : d.«have».val with _ | ⟨c, _ | ⟨c', rest⟩⟩
      · have hc0 : count = 0#usize := by rw [UScalar.eq_equiv, hcv, hv]; rfl
        rw [hc0]
        obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists
          (dec_from_bytes_loop_empty bytes 20#usize (alloc.vec.Vec.new tacenta_erasure.Chunk) true)
        rw [hr, hre]
        have hp : (20#usize != Slice.len bytes) = false := by
          simp only [bne_eq_false_iff_eq]; rw [UScalar.eq_equiv, hblen, hv]; rfl
        have hd := hdv (alloc.vec.Vec.new tacenta_erasure.Chunk) (by rw [hv])
        have h20 : bytes.val.length = 20 := by rw [hlenB, hv]; rfl
        simp [h20, hd, hinv]
      · have hc1 : count = 1#usize := by rw [UScalar.eq_equiv, hcv, hv]; rfl
        rw [hc1]
        have hd20' : bytes.val.drop (20#usize).val = chunkEnc c ++ [] := by
          simpa [hv] using hd20
        obtain ⟨r, hr, hr1, hr2, hr3⟩ := Std.WP.spec_imp_exists
          (dec_from_bytes_loop_one bytes 20#usize c [] hd20' (alloc.vec.Vec.new tacenta_erasure.Chunk) rfl)
        rw [hr]
        obtain ⟨pos, have1, ok1⟩ := r
        simp only at hr1 hr2 hr3
        subst hr3
        have hp : (pos != Slice.len bytes) = false := by
          simp only [bne_eq_false_iff_eq]; rw [UScalar.eq_equiv, hblen, hv, hr1]; simp
        have hd := hdv have1 (by rw [hr2, hv])
        have h54 : bytes.val.length = pos.val := by rw [hlenB, hv, hr1]; rfl
        simp [h54, hd, hinv]
      · rw [hv] at hl; simp at hl
  obtain ⟨r, hr, rfl⟩ := Std.WP.spec_imp_exists hs
  exact hr

/-! ## The agreement waiting for the header -/

attribute [local step] Tacenta.UnitLifecycleSessionCodec.auth_to_bytes_spec

@[local step]
theorem braid_push_len_prefixed_spec (out : alloc.vec.Vec U8) (s : Slice U8)
    (h : out.val.length + 4 + s.val.length ≤ Usize.max) :
    tacenta_braid.push_len_prefixed out s ⦃ w => w.val = out.val ++ lenEnc s ⦄ := by
  unfold tacenta_braid.push_len_prefixed
  step*
  all_goals (try simp_all [Array.to_slice, lenEnc, be32, core.num.U32.to_be_bytes])

theorem braid_take_len_prefixed_of (bytes : Slice U8) (pos : Usize) (n : U32) (payload rest : List U8)
    (hn : n.val = payload.length) (h : bytes.val.drop pos.val = be32 n ++ (payload ++ rest)) :
    tacenta_braid.take_len_prefixed bytes pos ⦃ r => ∃ sl p', r = some (sl, p') ∧ sl.val = payload ∧
      p'.val = pos.val + 4 + payload.length ⦄ := by
  have hfit : pos.val + 4 + payload.length ≤ bytes.val.length := by
    have := congrArg List.length h
    simp only [List.length_drop, List.length_append, be32_length] at this
    have := length_of_drop h (by rw [be32_length]; decide)
    rw [be32_length] at this
    omega
  have hmax : bytes.val.length ≤ Usize.max := bytes.property
  have hlenp := length_of_drop h (by rw [be32_length]; decide)
  rw [be32_length] at hlenp
  have hp : bytes.val.drop (pos.val + 4) = payload ++ rest := by
    have := drop_next h; rwa [be32_length] at this
  unfold tacenta_braid.take_len_prefixed
  step as ⟨o, ho⟩
  obtain ⟨s, rfl, hsv⟩ : ∃ s : Usize, o = some s ∧ s.val = pos.val + 4 := by
    rcases o with _ | s
    · simp at ho; scalar_tac
    · simp only at ho; exact ⟨s, rfl, ho.2.1⟩
  simp only
  rw [if_neg (by simp only [Slice.len]; scalar_tac)]
  step as ⟨s1, back, hs11, hs12⟩
  step as ⟨s2, hs21, hs22⟩
  step as ⟨s3, hs3⟩
  · rw [hs22]; simp [Slice.length, hs11, hsv]
  step as ⟨i1, hi1⟩
  have hs2v : s2.val = be32 n := by rw [hs21, hsv]; exact slice_of_drop h (by rw [be32_length])
  have hb3 : (back s3).val = be32 n := by
    rw [hs12, hs3, Array.from_slice_val _ _ (by rw [hs2v, be32_length]; simp), hs2v]
  have hi1n : i1 = n := u32_eq_of_bv i1 n _ hi1 hb3
  step as ⟨len, hlen⟩
  have hlenv : len.val = payload.length := by
    rw [hlen, hi1n, UScalar.cast_val_eq, ← hn]
    have : n.val < 2 ^ UScalarTy.Usize.numBits := by
      have h1 := n.hBounds; have h2 : 2 ^ UScalarTy.U32.numBits ≤ 2 ^ UScalarTy.Usize.numBits := by
        apply Nat.pow_le_pow_right (by decide); simp [UScalarTy.numBits]
      omega
    exact Nat.mod_eq_of_lt this
  step as ⟨o1, ho1⟩
  obtain ⟨e, rfl, hev⟩ : ∃ e : Usize, o1 = some e ∧ e.val = s.val + len.val := by
    rcases o1 with _ | e
    · simp at ho1; scalar_tac
    · simp only at ho1; exact ⟨e, rfl, ho1.2.1⟩
  simp only
  rw [if_neg (by simp only [Slice.len]; scalar_tac)]
  step as ⟨s4, hs41, hs42⟩
  refine ⟨s4, e, rfl, ?_, by rw [hev, hsv, hlenv]⟩
  rw [hs41, hsv, hev, hsv, hlenv]
  exact slice_of_drop hp rfl

/-- The bytes `Braid::to_bytes` writes for an agreement waiting for the header, with the decoder's length prefix
`n`. -/
def braidEncNH (epoch : U64) (auth : tacenta_braid.Auth) (n : U32) (dec : tacenta_erasure.Decoder) : List U8 :=
  1#u8 :: 5#u8 :: (be64 epoch ++ (authEnc auth ++ (be32 n ++ decEnc dec)))

theorem braid_to_bytes_nh_spec (hz : ZeroizingVecRoundTrip) (epoch : U64) (auth : tacenta_braid.Auth)
    (dec : tacenta_erasure.Decoder) (hl : dec.«have».val.length ≤ 1) :
    tacenta_braid.Braid.to_bytes ⟨tacenta_braid.State.NoHeaderReceived epoch auth dec⟩ ⦃ z => ∃ v n,
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧ n.val = (decEnc dec).length ∧
      v.val = braidEncNH epoch auth n dec ⦄ := by
  unfold tacenta_braid.Braid.to_bytes tacenta_braid.Braid.encoded_len tacenta_braid.Braid.state_tag
    tacenta_braid.len_prefixed_len
  simp only [head_len_eq, epoch_and_auth_len_eq, bind_tc_ok, alloc.vec.Vec.with_capacity]
  have hdl := decEnc_length dec hl
  have hu : 4294967295 ≤ Usize.max := Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  step*
  · simp_all [Array.to_slice, authEnc_length, alloc.vec.Vec.new]; scalar_tac
  · simp_all [Array.to_slice, authEnc_length, alloc.vec.Vec.new, alloc.vec.Vec.deref]; scalar_tac
  · rw [UScalar.eq_equiv]
    simp_all [alloc.vec.Vec.len, Array.to_slice, authEnc_length, alloc.vec.Vec.new, lenEnc_length,
      alloc.vec.Vec.deref]
    omega
  · refine ⟨out3, UScalar.cast .U32 (Slice.len (alloc.vec.Vec.deref x)), z_post, ?_, ?_⟩
    · rw [cast_len_val _ (by simp [alloc.vec.Vec.deref, x_post, hdl]; omega)]
      simp [alloc.vec.Vec.deref, x_post]
    · simp_all [Array.to_slice, braidEncNH, lenEnc, be64, core.num.U64.to_be_bytes, tacenta_braid.STATE_VERSION,
        alloc.vec.Vec.deref]

theorem decode_state_nh_of (bytes : Slice U8) (pos : Usize) (epoch : U64) (auth : tacenta_braid.Auth)
    (n : U32) (dec : tacenta_erasure.Decoder) (rest : List U8)
    (h : bytes.val.drop pos.val = be64 epoch ++ (authEnc auth ++ (be32 n ++ (decEnc dec ++ rest))))
    (hmax : epoch ≠ core.num.U64.MAX) (hn : n.val = (decEnc dec).length)
    (hl : dec.«have».val.length ≤ 1) (hinv : tacenta_erasure.Decoder.invariant dec = ok true)
    (hneed : dec.needed.val ≤ 65536) (hsize : dec.size.val ≤ 65536 * 32) :
    tacenta_braid.decode_state 5#u8 bytes pos ⦃ r => ∃ p,
      r = some (tacenta_braid.State.NoHeaderReceived epoch auth dec, p) ∧
        p.val = pos.val + 72 + 4 + (decEnc dec).length ⦄ := by
  have hl8 := length_of_drop h (by rw [be64_length]; decide)
  rw [be64_length] at hl8
  have ha : bytes.val.drop (pos.val + 8) = authEnc auth ++ (be32 n ++ (decEnc dec ++ rest)) := by
    have := drop_next h; rwa [be64_length] at this
  have hp : bytes.val.drop (pos.val + 8 + 64) = be32 n ++ (decEnc dec ++ rest) := by
    have := drop_next ha; rwa [authEnc_length] at this
  unfold tacenta_braid.decode_state
  show (do
    let o ← tacenta_braid.read_epoch bytes pos
    match o with
    | none => ok none
    | some epoch =>
      let i ← pos + 8#usize
      let o1 ← tacenta_braid.read_auth bytes i
      match o1 with
      | none => ok none
      | some p =>
        let (auth, pos1) := p
        let o2 ← tacenta_braid.take_len_prefixed bytes pos1
        match o2 with
        | none => ok none
        | some p1 =>
          let (hdr_dec_bytes, pos2) := p1
          let o3 ← tacenta_erasure.Decoder.from_bytes hdr_dec_bytes
          match o3 with
          | none => ok none
          | some hdr_dec =>
            ok (some (tacenta_braid.State.NoHeaderReceived epoch auth hdr_dec, pos2))) ⦃ _ ⦄
  rw [read_epoch_of bytes pos epoch _ h hmax]
  simp only [bind_tc_ok]
  step as ⟨i, hi⟩
  step with read_auth_of bytes i auth _ (by rw [hi]; exact ha) as ⟨p1, o1, ho1, hp1⟩
  simp only [ho1]
  step with braid_take_len_prefixed_of bytes p1 n (decEnc dec) rest hn (by rw [hp1, hi]; exact hp) as
    ⟨sl, p2, o2, ho2, hsl, hp2⟩
  simp only [ho2]
  show (do
    let o3 ← tacenta_erasure.Decoder.from_bytes sl
    match o3 with
    | none => ok none
    | some hdr_dec => ok (some (tacenta_braid.State.NoHeaderReceived epoch auth hdr_dec, p2))) ⦃ _ ⦄
  rw [dec_from_bytes_of sl dec hsl hl hinv hneed hsize]
  simp only [bind_tc_ok]
  simp only [WP.spec_ok]
  refine ⟨p2, rfl, ?_⟩
  rw [hp2, hp1, hi]

theorem braid_from_bytes_nh_of (bytes : Slice U8) (epoch : U64) (auth : tacenta_braid.Auth) (n : U32)
    (dec : tacenta_erasure.Decoder) (hb : bytes.val = braidEncNH epoch auth n dec)
    (hmax : epoch ≠ core.num.U64.MAX) (hn : n.val = (decEnc dec).length)
    (hl : dec.«have».val.length ≤ 1) (hdinv : tacenta_erasure.Decoder.invariant dec = ok true)
    (hneed : dec.needed.val ≤ 65536) (hsize : dec.size.val ≤ 65536 * 32)
    (hinv : tacenta_braid.Braid.invariant ⟨tacenta_braid.State.NoHeaderReceived epoch auth dec⟩ = ok true) :
    tacenta_braid.Braid.from_bytes bytes =
      ok (core.result.Result.Ok ⟨tacenta_braid.State.NoHeaderReceived epoch auth dec⟩) := by
  have hlen : bytes.val.length = 2 + 72 + 4 + (decEnc dec).length := by
    rw [hb]; simp [braidEncNH, be64_length, authEnc_length, be32_length]; omega
  have d0 : bytes.val.drop (0#usize).val = 1#u8 :: (braidEncNH epoch auth n dec).tail := by
    simp only [hb, braidEncNH]; rfl
  have d1 : bytes.val.drop (1#usize).val = 5#u8 :: (be64 epoch ++ (authEnc auth ++ (be32 n ++ decEnc dec))) := by
    simp only [hb, braidEncNH]; rfl
  have d2 : bytes.val.drop (2#usize).val =
      be64 epoch ++ (authEnc auth ++ (be32 n ++ (decEnc dec ++ []))) := by
    simp only [hb, braidEncNH, List.append_nil]; rfl
  have hs : tacenta_braid.Braid.from_bytes bytes ⦃ x =>
      x = core.result.Result.Ok ⟨tacenta_braid.State.NoHeaderReceived epoch auth dec⟩ ⦄ := by
    unfold tacenta_braid.Braid.from_bytes
    rw [if_neg (by simp only [Slice.len]; scalar_tac)]
    rw [index_usize_of _ _ _ _ d0]
    simp only [bind_tc_ok, tacenta_braid.STATE_VERSION, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte]
    rw [index_usize_of _ _ _ _ d1]
    simp only [bind_tc_ok]
    step with decode_state_nh_of bytes 2#usize epoch auth n dec [] d2 hmax hn hl hdinv hneed hsize as ⟨p, o, ho, hp⟩
    simp only [ho]
    have hpl : p = Slice.len bytes := by rw [UScalar.eq_equiv, hp]; simp [Slice.len, hlen]
    simp only [hpl, ↓reduceIte, hinv, bind_tc_ok]
    step*
    rw [hinv]
    simp
  obtain ⟨x, hx, rfl⟩ := Std.WP.spec_imp_exists hs
  exact hx

/-! ## The session after the responder's first receipt -/

/-- The shape of a session the responder's round trip covers: the agreement waits for the header with a decoder
holding at most one chunk, no stored key in either ratchet, one sparse chain-table entry with both chains, no
pending initial message, an established ephemeral, and the two variable-length fields below 64 KiB. -/
structure CodecShapeR (s : lifecycle.Session) (epoch : U64) (auth : tacenta_braid.Auth)
    (dec : tacenta_erasure.Decoder) (e : U64) (c1 c2 : tacenta_spqr.Chain) (eph : alloc.vec.Vec U8) : Prop where
  braid : s.braid = ⟨tacenta_braid.State.NoHeaderReceived epoch auth dec⟩
  epochNotMax : epoch ≠ core.num.U64.MAX
  decHave : dec.«have».val.length ≤ 1
  decInv : tacenta_erasure.Decoder.invariant dec = ok true
  decNeeded : dec.needed.val ≤ 65536
  decSize : dec.size.val ≤ 65536 * 32
  classicalSkipped : s.triple.classical.skipped.val = []
  chains : s.triple.post_quantum.chains.val = [(e, { send := some c1, receive := some c2 })]
  sparseSkipped : s.triple.post_quantum.skipped.val = []
  identityAd : s.identity_ad.val.length ≤ 65536
  pending : s.pending_initial = none
  established : s.established_ephemeral = some eph
  ephemeralLen : eph.val.length ≤ 65536

/-- The bytes `Session::export` writes for a session of that shape. -/
def sessionEncR (vt vb : alloc.vec.Vec U8) (pa : Array U8 32#usize) (ad : alloc.vec.Vec U8)
    (oa pea : Array U8 32#usize) (eph : alloc.vec.Vec U8) : List U8 :=
  1#u8 :: (lenEnc (alloc.vec.Vec.deref vt) ++ (lenEnc (alloc.vec.Vec.deref vb) ++ (pa.val ++
    (lenEnc (alloc.vec.Vec.deref ad) ++ (oa.val ++ (pea.val ++ (0#u8 :: (1#u8 ::
    lenEnc (alloc.vec.Vec.deref eph)))))))))

set_option maxHeartbeats 2000000 in
theorem export_spec_R (hz : ZeroizingVecRoundTrip) (s : lifecycle.Session) (epoch : U64)
    (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder) (e : U64) (c1 c2 : tacenta_spqr.Chain)
    (eph : alloc.vec.Vec U8) (shape : CodecShapeR s epoch auth dec e c1 c2 eph)
    (zp : zeroize.Zeroizing (Array U8 32#usize)) (pa : Array U8 32#usize)
    (hpk : tacenta_boundary.dh.PrivateKey.to_bytes s.ratchet_private = ok zp)
    (hpa : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref arrInst zp = ok pa)
    (oa pea : Array U8 32#usize)
    (hoa : tacenta_boundary.dh.PublicKeyBytes.as_bytes s.our_identity_public = ok oa)
    (hpea : tacenta_boundary.dh.PublicKeyBytes.as_bytes s.peer_identity_public = ok pea) :
    lifecycle.Session.export s ⦃ z => ∃ vt vb n v,
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      vt.val = tripleEnc s.triple e c1 c2 ∧ vb.val = braidEncNH epoch auth n dec ∧
      n.val = (decEnc dec).length ∧ v.val = sessionEncR vt vb pa s.identity_ad oa pea eph ⦄ := by
  unfold lifecycle.Session.export
  step with triple_to_bytes_spec hz s.triple e c1 c2 shape.classicalSkipped shape.chains
    shape.sparseSkipped as ⟨vt, zt, hvt, hvtv⟩
  rw [shape.braid]
  step with braid_to_bytes_nh_spec hz epoch auth dec shape.decHave as ⟨vb, n, zb, hvb, hn, hvbv⟩
  rw [hpk, shape.pending, shape.established]
  simp only [bind_tc_ok]
  simp only [hvt, hvb, hpa, hoa, hpea, bind_tc_ok]
  have hlt : vt.val.length = 334 := by rw [hvtv, tripleEnc_length]
  have hdl := decEnc_length dec shape.decHave
  have hlb : vb.val.length = 78 + (decEnc dec).length := by
    rw [hvbv]; simp [braidEncNH, be64_length, authEnc_length, be32_length]; omega
  have had := shape.identityAd
  have hel := shape.ephemeralLen
  have hu : 4294967295 ≤ Usize.max := Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  have hk := shape.decHave
  have hvbl : (alloc.vec.Vec.len vb).val = 78 + (decEnc dec).length := by simp [alloc.vec.Vec.len, hlb]
  have hvtl : (alloc.vec.Vec.len vt).val = 334 := by simp [alloc.vec.Vec.len, hlt]
  have hadl : (alloc.vec.Vec.len s.identity_ad).val = s.identity_ad.val.length := by simp [alloc.vec.Vec.len]
  have hepl : (alloc.vec.Vec.len eph).val = eph.val.length := by simp [alloc.vec.Vec.len]
  step*
  all_goals try (simp only [*, Slice.length, alloc.vec.Vec.deref, Array.to_slice, alloc.vec.Vec.with_capacity,
    alloc.vec.Vec.new, List.length_append, List.length_cons, List.length_nil, List.length_singleton,
    lenEnc_length, arr32_len, alloc.vec.Vec.len, Slice.len]; scalar_tac)
  all_goals try (simp only [alloc.vec.Vec.len, Slice.len, alloc.vec.Vec.deref, Array.to_slice, Slice.length,
    alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, List.length_append, lenEnc_length, arr32_len,
    List.length_cons, List.length_nil] at *; scalar_tac)
  · refine ⟨vt, vb, n, out9, z_post, hvtv, hvbv, hn, ?_⟩
    simp only [out9_post, x_post, out8_post, out7_post, out6_post, out5_post, out4_post, out3_post,
      out2_post, out1_post, s3_post, s5_post, s6_post, Array.to_slice, alloc.vec.Vec.with_capacity,
      alloc.vec.Vec.new, lifecycle.SESSION_VERSION, sessionEncR, List.nil_append, List.append_assoc,
      List.cons_append, List.singleton_append]
  · exfalso
    rename_i hne
    apply hne
    rw [UScalar.eq_equiv]
    simp only [*, alloc.vec.Vec.len, Slice.len, Slice.length, alloc.vec.Vec.deref, Array.to_slice,
      alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, List.length_append, List.length_cons,
      List.length_nil, List.length_singleton, lenEnc_length, arr32_len]
    scalar_tac

set_option maxHeartbeats 4000000 in
theorem import_unchecked_spec_R (hbr : OptionBranchSome) (s : lifecycle.Session) (epoch : U64)
    (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder) (e : U64) (c1 c2 : tacenta_spqr.Chain)
    (eph : alloc.vec.Vec U8) (shape : CodecShapeR s epoch auth dec e c1 c2 eph)
    (hinvT : tacenta_triple.State.invariant s.triple = ok true)
    (hinvB : tacenta_braid.Braid.invariant s.braid = ok true)
    (vt vb : alloc.vec.Vec U8) (n : U32) (pa oa pea : Array U8 32#usize)
    (hvt : vt.val = tripleEnc s.triple e c1 c2) (hvb : vb.val = braidEncNH epoch auth n dec)
    (hn : n.val = (decEnc dec).length)
    (hfpa : tacenta_boundary.dh.PrivateKey.from_bytes pa = ok s.ratchet_private)
    (hfoa : tacenta_boundary.dh.PublicKeyBytes.from_bytes oa = ok s.our_identity_public)
    (hfpea : tacenta_boundary.dh.PublicKeyBytes.from_bytes pea = ok s.peer_identity_public)
    (bytes : Slice U8) (hb : bytes.val = sessionEncR vt vb pa s.identity_ad oa pea eph) :
    lifecycle.Session.import_unchecked bytes ⦃ r => r = core.result.Result.Ok s ⦄ := by
  have hlt : vt.val.length = 334 := by rw [hvt, tripleEnc_length]
  have hdl := decEnc_length dec shape.decHave
  have hk := shape.decHave
  have hlb : vb.val.length = 78 + (decEnc dec).length := by
    rw [hvb]; simp [braidEncNH, be64_length, authEnc_length, be32_length]; omega
  have had := shape.identityAd
  have hel := shape.ephemeralLen
  have hmaxb : bytes.val.length ≤ Usize.max := bytes.property
  have hlen : bytes.val.length = 1 + (4 + 334) + (4 + vb.val.length) + 32 + (4 + s.identity_ad.val.length) + 32 +
      32 + 1 + 1 + (4 + eph.val.length) := by
    rw [hb]; simp [sessionEncR, lenEnc_length, alloc.vec.Vec.deref, hlt]; omega
  have d0 : bytes.val.drop (0#usize).val = 1#u8 :: (sessionEncR vt vb pa s.identity_ad oa pea eph).tail := by
    simp only [hb, sessionEncR]; rfl
  have d1 : bytes.val.drop (1#usize).val = (sessionEncR vt vb pa s.identity_ad oa pea eph).tail := by
    rw [hb]; rfl
  simp only [sessionEncR, List.tail_cons, lenEnc, List.append_assoc] at d1
  unfold lifecycle.Session.import_unchecked
  simp only [core.slice.Slice.is_empty, bind_tc_ok]
  rw [if_neg (by simp [Slice.length, hlen])]
  rw [index_usize_of _ _ _ _ d0]
  simp only [bind_tc_ok, lifecycle.SESSION_VERSION, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  step with lifecycle_take_len_prefixed_of hbr bytes 1#usize _ (alloc.vec.Vec.deref vt).val _
    (cast_len_val _ (by simp [alloc.vec.Vec.deref, hlt])) d1 as ⟨tsl, pos, o, ho, htsl, hpos⟩
  simp only [ho]
  step with (show tacenta_triple.State.from_bytes tsl ⦃ x => x = core.result.Result.Ok s.triple ⦄ by
    rw [triple_from_bytes_of tsl s.triple e c1 c2 (by rw [htsl]; exact hvt) shape.classicalSkipped
      shape.chains shape.sparseSkipped hinvT]; simp) as ⟨r, hr⟩
  simp only [hr]
  have dB := drop_next (drop_next d1)
  rw [be32_length, show (1#usize).val + 4 + (alloc.vec.Vec.deref vt).val.length = pos.val by
    rw [hpos]; simp] at dB
  step with lifecycle_take_len_prefixed_of hbr bytes pos _ (alloc.vec.Vec.deref vb).val _
    (cast_len_val _ (by simp [alloc.vec.Vec.deref, hlb]; omega)) dB as ⟨bsl, pos1, o1, ho1, hbsl, hpos1⟩
  simp only [ho1]
  rw [shape.braid] at hinvB
  step with (show tacenta_braid.Braid.from_bytes bsl ⦃ x => x = core.result.Result.Ok s.braid ⦄ by
    rw [shape.braid, braid_from_bytes_nh_of bsl epoch auth n dec (by rw [hbsl]; exact hvb) shape.epochNotMax hn
      shape.decHave shape.decInv shape.decNeeded shape.decSize hinvB]
    simp) as ⟨r1, hr1⟩
  simp only [hr1]
  have dP := drop_next (drop_next dB)
  rw [be32_length, ← hpos1] at dP
  have hp1v : pos1.val = 343 + vb.val.length := by
    rw [hpos1, hpos]; simp [alloc.vec.Vec.deref, hlt]
  step as ⟨i2, hi2⟩
  rw [if_neg (by simp only [Slice.len]; scalar_tac)]
  step as ⟨sp, backp, hsp1, hsp2⟩
  step as ⟨sp1, hsp11, hsp12⟩
  step as ⟨sp2, hsp2'⟩
  · rw [hsp12]; simp [Slice.length, hsp1, hi2]
  have hba : backp sp2 = pa := by
    rw [hsp2]; exact from_slice_eq _ _ _ (by
      rw [hsp2', hsp11, hi2]; exact slice_of_drop dP (by rw [arr32_len]))
  rw [hba, hfpa]
  simp only [bind_tc_ok]
  have dA := drop_next dP
  rw [arr32_len, show pos1.val + 32 = i2.val by rw [hi2]] at dA
  step with lifecycle_take_len_prefixed_of hbr bytes i2 _ (alloc.vec.Vec.deref s.identity_ad).val _
    (cast_len_val _ (by simp [alloc.vec.Vec.deref]; omega)) dA as ⟨asl, pos2, o2, ho2, hasl, hpos2⟩
  simp only [ho2]
  step as ⟨ad1, had1⟩
  have dO := drop_next (drop_next dA)
  rw [be32_length, ← hpos2] at dO
  have dPe := drop_next dO
  rw [arr32_len] at dPe
  have dF := drop_next dPe
  rw [arr32_len] at dF
  have hp2v : pos2.val = 379 + vb.val.length + s.identity_ad.val.length := by
    rw [hpos2, hi2, hp1v]; simp [alloc.vec.Vec.deref]; omega
  step as ⟨i4, hi4⟩
  rw [if_neg (by simp only [Slice.len]; scalar_tac)]
  step as ⟨so, backo, hso1, hso2⟩
  step as ⟨i5, hi5⟩
  step as ⟨so1, hso11, hso12⟩
  step as ⟨so2, hso2'⟩
  · rw [hso12]; simp [Slice.length, hso1, hi5]
  step as ⟨se, backe, hse1, hse2⟩
  step as ⟨se1, hse11, hse12⟩
  step as ⟨se2, hse2'⟩
  · rw [hse12]; simp [Slice.length, hse1, hi5, hi4]
  step as ⟨i7, hi7⟩
  rw [if_neg (by simp only [Slice.len]; scalar_tac)]
  rw [index_usize_of bytes i4 0#u8 _ (by rw [hi4, show pos2.val + 64 = pos2.val + 32 + 32 by omega]; exact dF)]
  simp only [bind_tc_ok]
  split
  · have dE := drop_next (seg := [0#u8]) dF
    simp only [List.length_singleton] at dE
    rw [show pos2.val + 32 + 32 + 1 = i7.val by rw [hi7, hi4]] at dE
    step as ⟨i10, hi10⟩
    rw [if_neg (by simp only [Slice.len]; scalar_tac)]
    rw [index_usize_of bytes i7 1#u8 _ dE]
    simp only [bind_tc_ok]
    split
    · rename_i h01; exact absurd h01 (by decide)
    · have dL := drop_next (seg := [1#u8]) dE
      simp only [List.length_singleton] at dL
      rw [show i7.val + 1 = i10.val by rw [hi10]] at dL
      have dL' : bytes.val.drop i10.val =
          be32 (UScalar.cast UScalarTy.U32 (Slice.len (alloc.vec.Vec.deref eph))) ++
            ((alloc.vec.Vec.deref eph).val ++ []) := by
        rw [dL]; simp [lenEnc]
      step with lifecycle_take_len_prefixed_of hbr bytes i10 _ (alloc.vec.Vec.deref eph).val _
        (cast_len_val _ (by simp [alloc.vec.Vec.deref]; omega)) dL' as ⟨esl, next, o3, ho3, hesl, hnext⟩
      simp only [ho3]
      step with alloc.slice.Slice.to_vec_spec core.clone.CloneU8 esl (fun _ _ => rfl) as ⟨v, hv⟩
      have hnv : next.val = bytes.val.length := by
        rw [hnext, hi10, hi7, hi4, hp2v, hlen]; simp [alloc.vec.Vec.deref]; omega
      have hnl : next = Slice.len bytes := by rw [UScalar.eq_equiv, hnv]; simp [Slice.len]
      have hbo : backo so2 = oa := by
        rw [hso2]; exact from_slice_eq _ _ _ (by
          rw [hso2', hso11, hi5]; exact slice_of_drop dO (by rw [arr32_len]))
      have hbe : backe se2 = pea := by
        rw [hse2]; exact from_slice_eq _ _ _ (by
          rw [hse2', hse11, hi5, hi4]; exact slice_of_drop dPe (by rw [arr32_len]))
      have hadv : ad1 = s.identity_ad := by rw [← had1]; exact Subtype.ext hasl
      have hvv : v = eph := by rw [← hv]; exact Subtype.ext hesl
      simp only [hnl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hbo, hbe, hfoa, hfpea,
        bind_tc_ok, hadv, hvv, ← shape.pending, ← shape.established]
      simp
    · exfalso; rename_i a b; first | exact a rfl | exact b rfl
  · rename_i h01; exact absurd h01 (by decide)
  · exfalso; rename_i a b; first | exact a rfl | exact b rfl

/-- **Export then import is the identity on sessions of the responder's shape**: for every session `s` that passes
`Session::invariant` and has `CodecShapeR`, `export` returns, and `import` of the exported bytes accepts and returns
`s` itself, every field equal.  Under the five laws of the initiator's round trip (`ZeroizingVecRoundTrip`,
`OptionBranchSome`, `VecAsSlice`, `DhPrivateBytesRoundTrip`, `DhPublicBytesRoundTrip`). -/
theorem export_import_of_shape_R (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome)
    (hsl : VecAsSlice) (hpriv : DhPrivateBytesRoundTrip) (hpub : DhPublicBytesRoundTrip)
    (s : lifecycle.Session) (epoch : U64) (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder) (e : U64)
    (c1 c2 : tacenta_spqr.Chain) (eph : alloc.vec.Vec U8) (shape : CodecShapeR s epoch auth dec e c1 c2 eph)
    (hinv : lifecycle.Session.invariant s = ok true) :
    ∃ z v, lifecycle.Session.export s = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      lifecycle.Session.import (alloc.vec.Vec.deref v) = ok (core.result.Result.Ok s) := by
  obtain ⟨hinvT, hinvB⟩ := session_invariant_leaves s hinv
  obtain ⟨zp, pa, hzp, hpa, hfpa⟩ := hpriv s.ratchet_private
  obtain ⟨oa, hoa, hfoa⟩ := hpub s.our_identity_public
  obtain ⟨pea, hpea, hfpea⟩ := hpub s.peer_identity_public
  obtain ⟨z, hz', vt, vb, n, v, hv, hvt, hvb, hn, hvv⟩ := Std.WP.spec_imp_exists
    (export_spec_R hz s epoch auth dec e c1 c2 eph shape zp pa hzp hpa oa pea hoa hpea)
  refine ⟨z, v, hz', hv, ?_⟩
  obtain ⟨r, hr, hrs⟩ := Std.WP.spec_imp_exists
    (import_unchecked_spec_R hbr s epoch auth dec e c1 c2 eph shape hinvT hinvB vt vb n pa oa pea hvt hvb hn
      hfpa hfoa hfpea (alloc.vec.Vec.deref v) (by simpa [alloc.vec.Vec.deref] using hvv))
  subst hrs
  unfold lifecycle.Session.import
  rw [hr]
  have hsv : alloc.vec.Vec.as_slice Global v = ok (alloc.vec.Vec.deref v) := hsl v
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch, hz', hv, hsv, slice_ne_self,
    Bool.false_eq_true, ↓reduceIte, hinv]

/-- `decode_ec` of a byte string that is not 33 bytes long is `none`. -/
theorem decode_ec_none_of_len (bytes : Slice U8) (h : bytes.val.length ≠ 33) : decode_ec bytes = ok none := by
  unfold decode_ec tacenta_session.decode_ec
  have hne : ¬ (Slice.len bytes = tacenta_session.ENCODE_EC_LEN) := by
    intro heq
    apply h
    have := congrArg UScalar.val heq
    simpa [Slice.len, tacenta_session.ENCODE_EC_LEN] using this
  simp [hne]

/-- **`Session::structural_invariant` fixes an established ephemeral key's encoding to 33 bytes.**  No hypothesis
about any opaque operation. -/
theorem established_len_of_structural (s : lifecycle.Session) (e : alloc.vec.Vec U8)
    (he : s.established_ephemeral = some e) (h : lifecycle.Session.structural_invariant s = ok true) :
    e.val.length = 33 := by
  by_contra hne
  have hd : decode_ec (alloc.vec.Vec.deref e) = ok none :=
    decode_ec_none_of_len _ (by simpa [alloc.vec.Vec.deref] using hne)
  unfold lifecycle.Session.structural_invariant at h
  simp only [he, hd, bind_tc_ok, core.option.Option.is_some, core.option.Option.is_none] at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_inv h)
    | (split at h)
    | (simp at h)

/-! ## The responder's session after its first receipt -/

open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts)

open Tacenta.UnitLifecycleResponderSuccessor (braid_receive_noHeader decoder_invariant_small add_chunk_fresh_have
  receivedSession receivedTriple triple_eq_received decrypt_ratchet_ok_parts)
open Tacenta.UnitLifecycleT3 (DhView DhCodecOf arrayOf SessionRefines)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf)
open Tacenta.UnitLifecycleEstablishResponder (responderModelOf)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstReceiptSession)

open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts) in
/-- **The decoder the agreement holds after the first receive holds at most one chunk and passes the Braid's checks**: for the prepare phase's
parts, every `NoHeaderReceived` state `Braid::receive` returns from the prepared agreement holds a decoder that passes
`Decoder::invariant` and is sized for the header and its MAC, under `DivCeilValue` and the header-length bound. -/
theorem received_decoder_small (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (hhdr : Tacenta.SessionUnitBraidT1.HeaderLenTotal) {ourB : lifecycle.Identity}
    {storeB : lifecycle.PrekeyStore} {msg : Slice U8} (p : ResponderPreparedParts ourB storeB msg)
    (m : tacenta_braid.Msg) (x : U64) (y : Option tacenta_braid.Output) (bc : tacenta_braid.Braid)
    (hrecv : tacenta_braid.Braid.receive p.braid m = ok (x, y, bc))
    (e : U64) (a : tacenta_braid.Auth) (d' : tacenta_erasure.Decoder)
    (hb : bc.state = tacenta_braid.State.NoHeaderReceived e a d') :
    d'.«have».val.length ≤ 1 ∧ tacenta_erasure.Decoder.invariant d' = ok true ∧
      (do
        let i ← tacenta_kem.HEADER_LEN
        let i1 ← i + tacenta_braid.MAC_LEN
        tacenta_braid.decoder_sized d' i1) = ok true := by
  obtain ⟨auth, d, hd, hbraid⟩ := Tacenta.UnitLifecycleEstablishResponder.braid_responder_ok _ _ p.hBraid
  rw [hbraid] at hrecv
  obtain ⟨hdinv, hsized⟩ := Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_checks hdiv hhdr d hd
  have hv0 : d.«have».val = [] := by
    obtain ⟨_, _, _, -, -, -, -, rfl⟩ := Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_ok d hd
    rfl
  rcases braid_receive_noHeader 1#u64 auth d m x y bc hrecv e a d' hb with rfl | ⟨c, r, hadd⟩
  · exact ⟨by rw [hv0]; simp, hdinv, hsized⟩
  obtain ⟨hv, n, needed, -, -, -, hcc, rfl⟩ := Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_ok d hd
  have hle := Tacenta.SessionUnitDecoderBound.invariant_true_needed_le _ hdinv
  obtain ⟨hs, hn, hl1, hln⟩ := add_chunk_fresh_have _ d' c r (by simp) hadd
  refine ⟨hl1, decoder_invariant_small d' (by rw [hs, hn]; exact hcc) (by rw [hn]; exact hle) hl1
    (by rw [hn]; exact hln), ?_⟩
  simpa [tacenta_braid.decoder_sized, tacenta_erasure.Decoder.impl.size, hs] using hsized

/-- **The session a successful inner receive returns at the prepared session, when it refines `firstReceiptSession`**, as `first_receipt_successor_shape` states it, with the decoder holding at most one chunk:
it is `receivedSession` of the parts at a `receivedTriple` whose peer key is `a4`, with a ratchet private key whose
public key bytes are the Triple's sending key, and a decoder that passes the Braid's two checks.  Under `DivCeilValue`,
the header-length bound, the responder's oracle record and the view's codec relation, and the per-run premise that the
responder's trace holds the draw. -/
theorem first_receipt_successor_shape_small (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (hhdr : Tacenta.SessionUnitBraidT1.HeaderLenTotal) {E : Type} (rcB : rand_core_1.RngCore E)
    (crcB : rand_core_1.CryptoRng E) {dh : DhView} (codec : DhCodecOf dh)
    {traceB : E → List Model.Lifecycle.Key} {oracleB : Model.Lifecycle.Oracle}
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB) {K : Model.Braid.Kem}
    {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts ourB storeB msg) (rngB : E) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (rngB' : E)
    (hinner : lifecycle.Session.decrypt_ratchet rcB crcB p.session p.message rngB =
      ok (core.result.Result.Ok ptB, sB', rngB'))
    (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk) (ec prk k1 k2 d dSend : Model.State.Key)
    (a4 : Array U8 32#usize)
    (hrel : SessionRefines dh K sB'
      (firstReceiptSession (responderModelOf dh p) secret rcv ec prk k1 k2 (arrayOf a4) d dSend
        (oracleB.dhPublic dB) dB)) :
    ∃ (dhs rk cks ckr prk' c2 cr : Array U8 32#usize) (auth : tacenta_braid.Auth)
      (dec : tacenta_erasure.Decoder) (rp : tacenta_boundary.dh.PrivateKey)
      (pk : tacenta_boundary.dh.PublicKeyBytes),
      sB' = receivedSession p (receivedTriple dhs a4 rk cks ckr prk' c2 cr) auth dec rp ∧
      tacenta_boundary.dh.PrivateKey.public_key rp = ok pk ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok dhs ∧
      dec.«have».val.length ≤ 1 ∧ tacenta_erasure.Decoder.invariant dec = ok true ∧
      (do
        let i ← tacenta_kem.HEADER_LEN
        let i1 ← i + tacenta_braid.MAC_LEN
        tacenta_braid.decoder_sized dec i1) = ok true := by
  obtain ⟨m, x, y, bc, a, ck, pkb, new, hrecv, hrand, hck, hpkb, hnew, hcases⟩ :=
    decrypt_ratchet_ok_parts rcB crcB p.session p.message rngB ptB sB' rngB' hinner
  -- the Triple, from the relation
  obtain ⟨dhs, dhr, rk, cks, ckr, prk', c2, cr, ht, hdhs, hdhr⟩ :=
    triple_eq_received ec prk k1 k2 (arrayOf a4) d dSend (oracleB.dhPublic dB) sB'.triple hrel.triple
  have hdhr' : dhr = a4 := Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes hdhr
  subst hdhr'
  -- the candidate's public bytes are the Triple's new sending key
  obtain ⟨value, rng'', hval, hvd, -⟩ := oracleOfB.random32 rngB dB restB hdrawB
  rw [hrand] at hval
  simp only [ok.injEq, Prod.mk.injEq] at hval
  obtain ⟨rfl, -⟩ := hval
  obtain ⟨k', hk', hkv⟩ := codec.privateFromBytes a
  rw [hck] at hk'
  cases hk'
  obtain ⟨pk', hpk', hpkv⟩ := oracleOfB.dhPublic ck
  rw [hpkb] at hpk'
  cases hpk'
  obtain ⟨bytes, hbytes, hbv⟩ := codec.asBytes pkb
  rw [hnew] at hbytes
  cases hbytes
  have hdn : dhs = new := by
    apply Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes
    have : arrayOf dhs = arrayOf new := by rw [hdhs, ← hvd, ← hkv, ← hpkv, hbv]
    exact this
  subst hdn
  -- the Braid: the relation fixes its constructor and epoch, the code walk its decoder
  have hb := hrel.braid
  simp only [firstReceiptSession] at hb
  have hbc : sB'.braid = bc := by
    rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> (rw [h])
  rcases hst : sB'.braid.state with _ | _ | _ | _ | _ | ⟨e, auth, dec⟩ | _ | _ | _ | _ | _ | _
  all_goals (rw [hst] at hb; try (simp [Tacenta.SessionUnitBraidT3.StateRefines] at hb; done))
  obtain ⟨he, -, -, -⟩ := hb
  have he' : e = 1#u64 := UScalar.eq_of_val_eq (by simpa using he)
  subst he'
  rw [hbc] at hst
  obtain ⟨hsmall, hdinv, hsized⟩ := received_decoder_small hdiv hhdr p m x y bc hrecv 1#u64 auth dec hst
  have hbr : bc = ⟨tacenta_braid.State.NoHeaderReceived 1#u64 auth dec⟩ := by
    cases bc; simp only at hst; rw [hst]
  obtain ⟨rk0, prk0, c10, c20, htrip⟩ := Tacenta.UnitLifecycleEstablishResponder.init_receiver_ok _ _ _ p.hTriple
  rcases hcases with ⟨-, hs'⟩ | ⟨hsame, hs'⟩
  · refine ⟨dhs, rk, cks, ckr, prk', c2, cr, auth, dec, ck, pkb, ?_, hpkb, hnew, hsmall, hdinv, hsized⟩
    rw [hs', ht, hbr]
    rfl
  · have hd0 : dhs = p.ratchetBytes := by
      rw [ht] at hsame
      simpa [receivedTriple, Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.session, htrip,
        Tacenta.UnitLifecycleEstablishResponder.responderTriple] using hsame
    subst hd0
    refine ⟨p.ratchetBytes, rk, cks, ckr, prk', c2, cr, auth, dec, p.ratchetPrivate, p.ratchetPublic, ?_,
      by rw [p.ratchetPrivate_eq]; exact p.hRatchetPublic, p.hRatchetBytes, hsmall, hdinv, hsized⟩
    rw [hs', ht, hbr]
    rfl


/-- **A decoder that passes `Decoder::invariant` is for a message of at most `32 · MAX_CODEWORDS` bytes**, under
`DivCeilValue`: the invariant ties `needed` to the chunk count of `size`. -/
theorem invariant_size_le (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (d : tacenta_erasure.Decoder)
    (h : tacenta_erasure.Decoder.invariant d = ok true) : d.size.val ≤ 65536 * 32 := by
  have hle := Tacenta.SessionUnitDecoderBound.invariant_true_needed_le d h
  unfold tacenta_erasure.Decoder.invariant at h
  obtain ⟨⟨i, i1, v, dist⟩, hloop, h2⟩ := bind_eq_ok_inv h
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
    (Tacenta.SessionUnitDecoderBound.inv_loop_post d (Array.repeat 8192#usize 0#u8) true 0#usize (by simp))
  rw [hloop] at hr
  cases hr
  obtain ⟨hp1, hp2⟩ := hp
  simp only [] at hp1 hp2
  subst hp1 hp2
  obtain ⟨i2, hi2, h3⟩ := bind_eq_ok_inv h2
  by_cases h1 : d.needed = i2
  · subst h1
    obtain ⟨r', hr', hrv⟩ := hdiv d.size
    unfold tacenta_erasure.chunk_count at hi2
    simp only [tacenta_erasure.CHUNK_BYTES] at hi2
    rw [hr'] at hi2
    cases hi2
    omega
  · rw [if_neg h1] at h3
    simp at h3

open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid)
open Tacenta.UnitHeadroomInvariant (OptionEqU64Shape)

/-- **The responder's session after its first receipt has the round trip's shape**: for parts of the prepare phase
and every session of the form `receivedSession` at a `receivedTriple` whose decoder holds at most one chunk and passes
`Decoder::invariant`, if the session passes `Session::invariant`, it has `CodecShapeR` (associated data of 66 bytes, an
established ephemeral of 33), under `DivCeilValue` and `DhCodecTotal`. -/
theorem received_codecShapeR (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal) {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore}
    {msg : Slice U8} (p : ResponderPreparedParts ourB storeB msg) (dhs dhr rk cks ckr prk c2 cr : Array U8 32#usize)
    (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder) (rp : tacenta_boundary.dh.PrivateKey)
    (hsmall : dec.«have».val.length ≤ 1) (hdinv : tacenta_erasure.Decoder.invariant dec = ok true)
    (hinv : lifecycle.Session.invariant (receivedSession p (receivedTriple dhs dhr rk cks ckr prk c2 cr) auth dec rp)
      = ok true) :
    CodecShapeR (receivedSession p (receivedTriple dhs dhr rk cks ckr prk c2 cr) auth dec rp) 1#u64 auth dec 0#u64
      { ck := c2, n := 0#u64 } { ck := cr, n := 1#u64 } p.ephemeralCopy := by
  have hstr := ((Tacenta.UnitLifecycleSendPreserve.session_invariant_iff _).mp hinv).1
  have had := Tacenta.UnitHeadroomInvariant.invariant_gives_ad_length hdh _ hinv
  have hel := established_len_of_structural _ p.ephemeralCopy rfl hstr
  refine ⟨rfl, ?_, hsmall, hdinv, Tacenta.SessionUnitDecoderBound.invariant_true_needed_le dec hdinv,
    invariant_size_le hdiv dec hdinv, ?_, ?_, ?_, by omega, rfl, rfl, by omega⟩
  · intro h; have h1 := congrArg UScalar.val h; simp [core.num.U64.MAX, U64.rMax] at h1
  · simp [receivedSession, receivedTriple, alloc.vec.Vec.new]
  · simp [receivedSession, receivedTriple, Tacenta.UnitLifecycleResponderSuccessor.receivedChains,
      Tacenta.UnitHeadroomSatisfiable.vecOf]
  · simp [receivedSession, receivedTriple, alloc.vec.Vec.new]

/-- **The responder's session after its first receipt has room for every `k` operations with `k + 3 < u32::MAX`**:
classical clock 1, sparse epoch 0, chain counters 0 and 1, agreement epoch 1.  Hypothesis-free. -/
theorem received_counterRoom {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts ourB storeB msg) (dhs dhr rk cks ckr prk c2 cr : Array U8 32#usize)
    (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder) (rp : tacenta_boundary.dh.PrivateKey) (k : Nat)
    (hk : k + 3 < Std.U32.max) :
    CounterRoom (receivedSession p (receivedTriple dhs dhr rk cks ckr prk c2 cr) auth dec rp) k := by
  have hu : Std.U32.max = 4294967295 := by simp [Std.U32.max_eq]
  have hv : Std.U64.max = 18446744073709551615 := by simp [Std.U64.max_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [receivedSession, receivedTriple]; omega
  · simp [receivedSession, receivedTriple]; omega
  · intro q hq ch hch
    simp [receivedSession, receivedTriple, Tacenta.UnitLifecycleResponderSuccessor.receivedChains,
      Tacenta.UnitHeadroomSatisfiable.vecOf] at hq
    subst hq
    rcases hch with h | h <;> (simp at h; subst h; simp; omega)
  · simp only [receivedSession, Tacenta.SessionUnitBraidT1.State.epoch_val]
    simp; omega

/-- **The responder's session after its first receipt survives `Session::export` then `Session::import`**: under the
hypotheses of `first_receipt_successor_facts`, the five laws of the round trip and `DhCodecTotal`, the bytes `export`
writes for the session the inner receive returned are accepted by `import`, which returns that session itself, every
field equal; and the session has room for every `j` operations with `j + 3 < u32::MAX`. -/
theorem first_receipt_successor_round_trip (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome)
    (hsl : VecAsSlice) (hpriv : DhPrivateBytesRoundTrip) (hpubb : DhPublicBytesRoundTrip)
    (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal) (hpub : DhPublicValid)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (hhdr : Tacenta.SessionUnitBraidT1.HeaderLenTotal) {E : Type} (rcB : rand_core_1.RngCore E)
    (crcB : rand_core_1.CryptoRng E) {dh : DhView} (codec : DhCodecOf dh)
    {traceB : E → List Model.Lifecycle.Key} {oracleB : Model.Lifecycle.Oracle}
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB) {K : Model.Braid.Kem}
    {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts ourB storeB msg) (rngB : E) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (rngB' : E)
    (hinner : lifecycle.Session.decrypt_ratchet rcB crcB p.session p.message rngB =
      ok (core.result.Result.Ok ptB, sB', rngB'))
    (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk) (ec prk k1 k2 d dSend : Model.State.Key)
    (a4 : Array U8 32#usize) (ha4 : Tacenta.SessionUnitT1.canonicalX25519 a4 = true)
    (hrel : SessionRefines dh K sB'
      (firstReceiptSession (responderModelOf dh p) secret rcv ec prk k1 k2 (arrayOf a4) d dSend
        (oracleB.dhPublic dB) dB)) :
    (∃ z v, lifecycle.Session.export sB' = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      lifecycle.Session.import (alloc.vec.Vec.deref v) = ok (core.result.Result.Ok sB')) ∧
      ∀ j, j + 3 < Std.U32.max → CounterRoom sB' j := by
  have hfacts := Tacenta.UnitLifecycleResponderSuccessor.first_receipt_successor_facts hpub hoeq hdiv hhdr rcB crcB
    codec oracleOfB p rngB dB restB hdrawB ptB sB' rngB' hinner secret rcv ec prk k1 k2 d dSend a4 ha4 hrel
  obtain ⟨dhs, rk, cks, ckr, prk', c2, cr, auth, dec, rp, pk, rfl, -, -, hsmall, hdinv, -⟩ :=
    first_receipt_successor_shape_small hdiv hhdr rcB crcB codec oracleOfB p rngB dB restB hdrawB ptB sB' rngB'
      hinner secret rcv ec prk k1 k2 d dSend a4 hrel
  exact ⟨export_import_of_shape_R hz hbr hsl hpriv hpubb _ _ _ _ _ _ _ _
    (received_codecShapeR hdiv hdh p dhs a4 rk cks ckr prk' c2 cr auth dec rp hsmall hdinv hfacts.1) hfacts.1,
    fun j hj => received_counterRoom p dhs a4 rk cks ckr prk' c2 cr auth dec rp j hj⟩

section Comp
variable {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
  {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}

open Tacenta.UnitLifecycleT3 (vecOf sliceOf modelChunkOf modelCodewordOf CodewordViewSendOf)
open Tacenta.UnitLifecycleEstablishInitiatorShape (establishedModelOf)
open Tacenta.UnitLifecycleEstablishedEncrypt (firstFrame initialWire)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees StoreRefusal responder_first_frame_prepares)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptRatchetAgreements)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstKey DhAgreeContributory AeadRoundTrip
  parts_of_first_frame responder_first_frame_inner_succeeds establish_responder_commit_of_inner)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)

/-- **The session `establish_responder` returns on the initiator's first frame survives `Session::export` then
`Session::import`, and the restored copy is that session**: under the hypotheses of
`responder_first_frame_successor` and four more laws of the round trip (`ZeroizingVecRoundTrip`, `OptionBranchSome`,
`VecAsSlice`, `DhPrivateBytesRoundTrip`; the fifth, `DhPublicBytesRoundTrip`, is already among them), at every
return of the call that is `Ok (sB', ptB)`: `sB'` refines `firstReceiptSession`, passes `Session::invariant`, meets
`CounterHeadroom` and has room for every `j` operations with `j + 3 < u32::MAX`, and the bytes `export` writes for it
are accepted by `import`, which returns `sB'` itself. -/
theorem responder_first_frame_restored [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type}
    (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome) (hsl : VecAsSlice) (hpriv : DhPrivateBytesRoundTrip)
    (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {dh : DhView} (codec : DhCodecOf dh) (view : Model.Lifecycle.CodewordView)
    (oracleA : Model.Lifecycle.Oracle) (hsealA : Tacenta.UnitOracleShape.AeadSealClause Interp.real oracleA)
    (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (q : InitiatorSecretParts rc crc our bundle) (pending : Model.Lifecycle.PendingInitial)
    (hpend : (establishedModelOf dh q.session).pendingInitial = some pending)
    (plaintext : Slice U8) (hroom : plaintext.val.length + 48 ≤ Usize.max)
    (src : Model.Lifecycle.Bytes) (hsrc : src.length = Model.Braid.headerSize + Model.Braid.macSize)
    (c : tacenta_erasure.Chunk) (hcw : Tacenta.SessionUnitBraidT3.CodewordOf src c)
    (hsend : view.send (establishedModelOf dh q.session).braid (modelChunkOf src c) = modelCodewordOf c)
    (msg : Slice U8)
    (hmsg : sliceOf msg = initialWire (establishedModelOf dh q.session) pending
      (firstFrame view oracleA (establishedModelOf dh q.session) (sliceOf plaintext)
        (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) (modelChunkOf src c)))
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundle)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundle.kem_prekey_id q.kemCiphertext q.kemSecret)
    (rngB : E) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (storeB' : lifecycle.PrekeyStore) (rngB' : E)
    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB')) :
    ∃ (p : ResponderPreparedParts ourB storeB msg) (ec : Array U8 32#usize) (dSend : Model.Lifecycle.Key),
      SessionRefines dh oracleB.braidKem sB'
        (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)
          (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
          (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) ∧
      lifecycle.Session.invariant sB' = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' ∧
      (∀ j, j + 3 < Std.U32.max → CounterRoom sB' j) ∧
      ∃ z v, lifecycle.Session.export sB' = ok z ∧
        zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
        lifecycle.Session.import (alloc.vec.Vec.deref v) = ok (core.result.Result.Ok sB') := by
  have hsize := Tacenta.UnitLifecycleEstablishResponder.establish_responder_ok_fits rcB crcB ourB storeB
    msg rngB _ _ _ hcallB
  rcases responder_first_frame_prepares rcB crcB contracts hpub hsym hrt hct hbound codec q pending hpend _ msg
      hmsg hsize ourB storeB hpublish hidentity hdistinct hkem rngB with ⟨-, e, -, hrefuse⟩ |
    ⟨p, -, -, h3, -, h5, -, -, h8, -⟩
  · rw [hrefuse] at hcallB
    cases hcallB
  obtain ⟨-, -, hsp, hop⟩ := parts_of_first_frame contracts.decrypt.braid.zeroizingArray hpub codec hct
    hbound q pending hpend _ msg hmsg ourB storeB hpublish hidentity p
  obtain ⟨ec, dSend, ptB0, sB0, rngB0, -, -, hinner, -, -, hrel⟩ :=
    responder_first_frame_inner_succeeds rcB crcB contracts hpub hsym hcon haead hoeq codec view oracleA hsealA
      traceB oracleB oracleOfB agreements q plaintext hroom src hsrc c hcw hsend p h3 h5 hsp hop h8 rngB
      htraceB dB restB hdrawB
  obtain ⟨storeB0, -, hout⟩ := establish_responder_commit_of_inner rcB crcB p rngB ptB0 sB0 rngB0 hinner _ hcallB
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at hout
  obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ := hout
  have ha4 := Tacenta.UnitLifecycleEstablishInitiatorShape.dhPublicValid_canonical hpub q.hRatchetPublic q.hRatchetBytes
  obtain ⟨hinv, hhead⟩ := Tacenta.UnitLifecycleResponderSuccessor.first_receipt_successor_facts hpub hoeq
    contracts.divCeilValue contracts.decrypt.braid.headerLen rcB crcB codec oracleOfB p rngB dB restB hdrawB _ _ _
    hinner _ _ _ _ _ _ _ _ q.ratchetBytes ha4 hrel
  obtain ⟨hrt', hroom'⟩ := first_receipt_successor_round_trip hz hbr hsl hpriv hrt
    contracts.decrypt.dhCodec hpub hoeq contracts.divCeilValue contracts.decrypt.braid.headerLen rcB crcB codec
    oracleOfB p rngB dB restB hdrawB _ _ _ hinner _ _ _ _ _ _ _ _ q.ratchetBytes ha4 hrel
  exact ⟨p, ec, dSend, hrel, hinv, hhead, hroom', hrt'⟩

/-- **Restore then continue on the responder's side**: under the hypotheses of `responder_first_frame_restored`, the
encrypt boundary records at the responder's source with an encrypt oracle whose Braid KEM is the receipt's, and a
plaintext bound, at every return `Ok (sB', ptB)` of `establish_responder` on the initiator's first frame: `export sB'`
writes bytes, every session `import` accepts them with is `sB'`, and the public `encrypt` at that restored session
refines the model's step at `firstReceiptSession`, and leaves a session that passes `Session::invariant` with room for
`k` operations (`encrypt_refines_keeps_invariant`, at `NoHeaderReceived`).  Conditional on `AeadSealBounded` and
`OracleOf`, false of the shipping AEAD by reading at long lengths. -/
theorem responder_first_frame_restored_encrypt [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type}
    (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome) (hsl : VecAsSlice) (hpriv : DhPrivateBytesRoundTrip)
    (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {dh : DhView} (codec : DhCodecOf dh) (view : Model.Lifecycle.CodewordView)
    (oracleA : Model.Lifecycle.Oracle) (hsealA : Tacenta.UnitOracleShape.AeadSealClause Interp.real oracleA)
    (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (q : InitiatorSecretParts rc crc our bundle) (pending : Model.Lifecycle.PendingInitial)
    (hpend : (establishedModelOf dh q.session).pendingInitial = some pending)
    (plaintext : Slice U8) (hroom : plaintext.val.length + 48 ≤ Usize.max)
    (src : Model.Lifecycle.Bytes) (hsrc : src.length = Model.Braid.headerSize + Model.Braid.macSize)
    (c : tacenta_erasure.Chunk) (hcw : Tacenta.SessionUnitBraidT3.CodewordOf src c)
    (hsend : view.send (establishedModelOf dh q.session).braid (modelChunkOf src c) = modelCodewordOf c)
    (msg : Slice U8)
    (hmsg : sliceOf msg = initialWire (establishedModelOf dh q.session) pending
      (firstFrame view oracleA (establishedModelOf dh q.session) (sliceOf plaintext)
        (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) (modelChunkOf src c)))
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundle)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundle.kem_prekey_id q.kemCiphertext q.kemSecret)
    (rngB : E) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (storeB' : lifecycle.PrekeyStore) (rngB' : E)
    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB'))
    {kemE : Tacenta.UnitLifecycleT3.KemView} {viewE : Model.Lifecycle.CodewordView}
    {traceE : E → List Model.Lifecycle.Key} {oracleE : Model.Lifecycle.Oracle}
    (braidE : Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rcB oracleE.braidKem)
    (tripleE : Tacenta.UnitLifecycleT3.TripleSendRefinementContracts)
    (aeadE : Tacenta.UnitLifecycleT1.AeadSealBounded)
    (oracleOfE : Tacenta.UnitLifecycleT3.OracleOf rcB crcB dh kemE traceE oracleE)
    (codewordViewE : CodewordViewSendOf viewE)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (lawsE : SendInvariantLaws oracleE.braidKem)
    (hgenE : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracleE.braidKem rcB crcB traceE)
    (hK : oracleE.braidKem = oracleB.braidKem)
    (ptE : Slice U8) (hptE : ptE.val.length + 65770 ≤ Usize.max) (rngE : E) (htraceE : traceE rngE = oracleE.draws)
    (k : Nat) (hk : k + 4 < Std.U32.max) :
    ∃ (p : ResponderPreparedParts ourB storeB msg) (ec : Array U8 32#usize) (dSend : Model.Lifecycle.Key)
      (z : zeroize.Zeroizing (alloc.vec.Vec U8)) (v : alloc.vec.Vec U8),
      lifecycle.Session.export sB' = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      ∀ sR, lifecycle.Session.import (alloc.vec.Vec.deref v) = ok (core.result.Result.Ok sR) →
        sR = sB' ∧
        ∃ output, lifecycle.Session.encrypt rcB crcB sR ptE rngE = ok output ∧
          Tacenta.UnitLifecycleT3.StepRefines traceE dh oracleE.braidKem output
            (Model.Lifecycle.encrypt viewE oracleE
              (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)
                (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
                (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB)
              (sliceOf ptE)) ∧
          lifecycle.Session.invariant output.2.1 = ok true ∧ CounterRoom output.2.1 k := by
  obtain ⟨p, ec, dSend, hrel, hinv, -, hroom, z, v, hz', hv, himp⟩ :=
    responder_first_frame_restored hz hbr hsl hpriv rcB crcB contracts hpub hsym hcon haead hrt hct hbound hoeq
      codec view oracleA hsealA traceB oracleB oracleOfB agreements q pending hpend plaintext hroom src hsrc c hcw
      hsend msg hmsg ourB storeB hpublish hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB'
      hcallB
  refine ⟨p, ec, dSend, z, v, hz', hv, fun sR hR => ?_⟩
  have hsR : sR = sB' := by
    rw [himp] at hR
    exact (core.result.Result.Ok.inj (Result.ok.inj hR)).symm
  subst hsR
  refine ⟨rfl, ?_⟩
  rw [← hK] at hrel
  have hns : ∀ e a hdr dec, sR.braid.state ≠ tacenta_braid.State.HeaderReceived e a hdr dec := by
    intro e a hdr dec h
    have hb := hrel.braid
    rw [h] at hb
    simp [firstReceiptSession, Tacenta.SessionUnitBraidT3.StateRefines] at hb
  have hlive : Tacenta.SessionUnitBraidT3.EncodersLive
      (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)
        (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
        (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB).braid := by
    intro enc henc
    simp [firstReceiptSession, Tacenta.SessionUnitBraidT3.EncoderOf] at henc
  have hdraws : ∀ e a, sR.braid.state = tacenta_braid.State.KeysUnsampled e a →
      ∃ d1 d2 rest, traceE rngE = d1 :: d2 :: rest := by
    intro e a h
    have hb := hrel.braid
    rw [h] at hb
    simp [firstReceiptSession, Tacenta.SessionUnitBraidT3.StateRefines] at hb
  exact Tacenta.UnitLifecycleEncryptCompose.encrypt_refines_keeps_invariant braidE tripleE aeadE
    contracts.decrypt.dhCodec oracleOfE codec codewordViewE hz80 hz32 hzKeys lawsE hgenE hbound sR _ k hinv hrel
    (hroom (k + 1) (by omega)) hlive hns ptE hptE rngE htraceE hdraws

open Tacenta.UnitLifecycleResponderFirstReceipt (headerSource established_triple_first first_send_key)
open Tacenta.UnitLifecycleEstablishInitiatorShape (InitiatorOutputParts)
open Tacenta.UnitLifecycleT3 (OracleOf BraidSendRefinementContracts TripleSendRefinementContracts KemView) in
/-- **The responder's session after the initiator's first send survives `Session::export` then `Session::import`**:
under the hypotheses of `initiator_first_send_responder_successor_hypotheses` and four more laws of the round trip, at
every successful return of `establish_responder` on the bytes the initiator's first `encrypt` emitted, `sB'` refines
`firstReceiptSession`, passes `Session::invariant`, meets the ceilings, has room for every `j` with `j + 3 < u32::MAX`,
and the bytes `export` writes for it are accepted by `import`, which returns `sB'` itself. -/
theorem initiator_first_send_responder_restored [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (hzR : ZeroizingVecRoundTrip) (hbrR : OptionBranchSome) (hslR : VecAsSlice) (hprivR : DhPrivateBytesRoundTrip)
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E) (ourA : lifecycle.Identity)
    (bundleA : lifecycle.PublishedBundle) (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
    (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE ourA bundleA expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (q : InitiatorSecretParts rcE crcE ourA bundleA) (hq : s = q.session)
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws) (d1 d2 : Model.Lifecycle.Key)
    (rest : List Model.Lifecycle.Key) (hdraws : trace rng = d1 :: d2 :: rest)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng = ok (core.result.Result.Ok bytes, s', rng'))
    (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (traceB : F → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundleA)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundleA.kem_prekey_id q.kemCiphertext q.kemSecret)
    (rngB : F) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (storeB' : lifecycle.PrekeyStore) (rngB' : F)
    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB')) :
    ∃ (p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes)) (ec : Array U8 32#usize)
      (dSend : Model.Lifecycle.Key) (dk ekSeed ekVector : Model.Braid.Bytes),
      oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector) ∧
      SessionRefines dh oracleB.braidKem sB'
        (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret)
          ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
          (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
          (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) ∧
      lifecycle.Session.invariant sB' = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' ∧
      (∀ j, j + 3 < Std.U32.max → CounterRoom sB' j) ∧
      ∃ z v, lifecycle.Session.export sB' = ok z ∧
        zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
        lifecycle.Session.import (alloc.vec.Vec.deref v) = ok (core.result.Result.Ok sB') := by
  have hfits := Tacenta.UnitLifecycleT3.encrypt_ok_plaintext_fits rc crc s plaintext rng
    bytes s' rng' hcall
  obtain ⟨output, hcall', hdr, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes rc
    crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen
    hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h plaintext hroom hfits rng htrace d1 d2 rest hdraws
  rw [hcall] at hcall'
  cases hcall'
  rcases hcases with ⟨-, hres, -⟩ | ⟨dk, ekSeed, ekVector, hkg, bytes', hres, -, -, tripleNext, messageKey,
    chunk, encoder, pending, a, ⟨header, hsendM⟩, hbraidA, hnc, hpend, hwire, -⟩
  · cases hres
  simp only [core.result.Result.Ok.injEq] at hres
  subst hres
  subst hq
  -- the message key is the first key of the initiator's chains
  have hmk : messageKey = firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend) := by
    rw [established_triple_first dh q.toInitiatorOutputParts, first_send_key] at hsendM
    simp only [Except.ok.injEq, Prod.mk.injEq] at hsendM
    exact hsendM.2.2.symm
  -- the chunk is the first chunk of the header source
  have ha : a = Tacenta.SessionUnitBraidT3.AuthOf q.auth := by
    simp only [establishedModelOf, InitiatorOutputParts.session,
      Tacenta.UnitLifecycleEstablishInitiatorShape.unsampledModelOf, Model.Braid.BraidState.keysUnsampled.injEq]
      at hbraidA
    exact hbraidA.2.symm
  subst ha
  have hchunk : chunk = ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed
      ekVector, 0⟩ := by
    simp only [Model.Braid.encode, Model.Braid.Encoder.nextChunk, Prod.mk.injEq] at hnc
    rw [← hnc.1]
    rfl
  obtain ⟨hs32, -, hhl⟩ := hsizes _ _ _ _ hkg
  have hsrc : (headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector).length =
      Model.Braid.headerSize + Model.Braid.macSize := by
    simp [headerSource, Model.Braid.Auth.macHdr, Model.Kdf.hmac_length, Model.Kdf.hashLen, hs32, hhl,
      Model.Braid.headerSize, Model.Braid.macSize]
  obtain ⟨-, -, c, -, -, hc0, hcw, -⟩ := Tacenta.UnitHeldKemWitness.held_encoder contracts.divCeilValue
    agreements.erasure _ (by rw [hsrc]; rfl)
  have hmc : modelChunkOf (headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed
      ekVector) c = ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩ := by
    simp [modelChunkOf, hc0]
  have hsend := codewordView.send (establishedModelOf dh q.session).braid _ c hcw
  rw [hmk, hchunk, ← hmc] at hwire
  obtain ⟨p, ec, dSend, hrel, hinv, hhead', hroomB, hrtB⟩ := responder_first_frame_restored hzR hbrR hslR hprivR
    rcB crcB contracts hpub hsym hcon
    haead hrt hct hbound hoeq codec view oracle oracleOf.aeadSeal traceB oracleB oracleOfB agreements q pending
    hpend plaintext (by omega) _ hsrc c hcw hsend (alloc.vec.Vec.deref bytes) hwire ourB storeB hpublish hidentity
    hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB
  rw [hmc] at hrel
  exact ⟨p, ec, dSend, dk, ekSeed, ekVector, hkg, hrel, hinv, hhead', hroomB, hrtB⟩


end Comp

section Reach

open Tacenta.UnitLifecycleResponderSuccessor (initiator_first_send_responder_successor_hypotheses)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptRatchetAgreements)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitLifecycleResponderFirstFrame (FirstFrameSuccessShape InitiatorSecretParts DhAgreeSymmetric)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory AeadRoundTrip first_send_receive_reachable)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)
/-! ## The reach -/

open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleEstablishedEncrypt (EncryptExtraLaws emptyPlaintext) in
/-- **The reach, with the responder's session restored**: under the laws of `first_send_receive_successor_reachable`
and four more laws of the round trip, there is a run from `publish` through the establishment and a first send of the
empty plaintext to a successful `establish_responder` whose session passes `Session::invariant`, meets the ceilings,
and survives `Session::export` then `Session::import` as itself.  Last-resort path only. -/
theorem first_send_restored_reachable (hzR : ZeroizingVecRoundTrip) (hbrR : OptionBranchSome)
    (hslR : VecAsSlice) (hprivR : DhPrivateBytesRoundTrip) (K : Model.Braid.Kem) (dh : DhView)
    (kem : Tacenta.UnitLifecycleT3.KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (X : EncryptExtraLaws K dh kem) (RA : Nonempty (ResponderAxiom Interp.real byteRng))
    (hsym : DhAgreeSymmetric) (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (FS : FirstFrameSuccessShape Interp.real tacenta_boundary.kem.KeyPair.public_key
      @alloc.vec.Vec.is_empty)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K)
    (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (ourA : lifecycle.Identity) (seed : List Std.U8) (hseed : seed.length = 64)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle)
      (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (bytes : alloc.vec.Vec Std.U8)
      (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity)
      (storeB : lifecycle.PrekeyStore) (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8)
      (storeB' : lifecycle.PrekeyStore) (rngB' : List Std.U8),
      oracle.braidKem = K ∧
      lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext seed =
        ok (core.result.Result.Ok bytes, s', rng') ∧
      lifecycle.PrekeyStore.publish storeB = ok bundle ∧
      lifecycle.establish_responder byteRng byteCrc ourB storeB (alloc.vec.Vec.deref bytes) seed =
        ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
      lifecycle.Session.invariant sB' = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' ∧
      ∃ z v, lifecycle.Session.export sB' = ok z ∧
        zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
        lifecycle.Session.import (alloc.vec.Vec.deref v) = ok (core.result.Result.Ok sB') := by
  obtain ⟨oracle, bundle, rng0, rng1, q, bytes, s', rng', ourB, storeB, sB', ptB, storeB', rngB', hK, H, hcall,
    hpublish, hidentity, hdistinct, hkem, -, oracleOfB, htraceB, -, -, hcallB, -⟩ :=
    first_send_receive_reachable K dh kem L A S hpub hct X RA hsym hrt FS hsizes hcon haead ourA seed hseed hkg
  obtain ⟨contracts⟩ := Tacenta.UnitSatisfiabilityRecords.responder_contracts_of_axiom_base byteRng RA L.laws
  obtain ⟨inst⟩ := H.derivedKeys
  subst hK
  obtain ⟨oracle0, bundle1, s1, rng11, hK0, H1⟩ :=
    Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable
      oracle.braidKem dh L A S hpub hct ourA
  have ag : DecryptRatchetAgreements oracle.braidKem :=
    hK0 ▸ (H1 Tacenta.UnitLifecycleRepair.witnessView).agreements
  obtain ⟨d1, d2, rest2, hdrB⟩ : ∃ d1 d2 rest2, byteTrace seed = d1 :: d2 :: rest2 := by
    have := Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega)
    exact ⟨_, _, _, this⟩
  obtain ⟨-, -, -, -, -, -, -, -, hinv, hhead, -, hrtB⟩ := initiator_first_send_responder_restored hzR hbrR hslR
    hprivR byteRng
    byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec
    H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes
    H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session H.established q rfl
    emptyPlaintext H.room seed H.trace_eq _ _ _ (Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega))
    bytes s' rng' hcall byteRng byteCrc contracts hpub hsym hcon haead hrt L.optionEq byteTrace oracle oracleOfB ag
    ourB storeB hpublish hidentity hdistinct hkem seed htraceB d1 (d2 :: rest2) hdrB ptB sB' storeB' rngB' hcallB
  exact ⟨oracle, bundle, q, bytes, s', rng', ourB, storeB, sB', ptB, storeB', rngB', rfl, hcall, hpublish,
    hcallB, hinv, hhead, hrtB⟩

end Reach

end Tacenta.UnitLifecycleRestoredResponder

-- The pins `genpins.py` writes after this line print each statement whole: with no cut at depth 50
-- (`pp.deepTerms`) and each omitted proof with its proposition, `(⋯ : P)` (`pp.proofs.withType`). `attest.py`
-- refuses a statement pin that prints a bare `⋯`, and every other `pp` option.
set_option pp.deepTerms true
set_option pp.proofs.withType true

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.be16_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.be16_length

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.chunkEnc_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.chunkEnc_length

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.dec_to_bytes_loop_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.dec_to_bytes_loop_empty

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.dec_to_bytes_loop_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.dec_to_bytes_loop_one

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.dec_encoded_len_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.dec_encoded_len_spec

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.dec_to_bytes_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.dec_to_bytes_spec

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.from_be16' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.from_be16

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.dec_from_bytes_loop_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.dec_from_bytes_loop_empty

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.dec_from_bytes_loop_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.dec_from_bytes_loop_one

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.decEnc_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.decEnc_length

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.cast_u64_usize_val' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.cast_u64_usize_val

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.cast_usize_cast_u64' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.cast_usize_cast_u64

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.dec_from_bytes_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.dec_from_bytes_of

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.braid_push_len_prefixed_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.braid_push_len_prefixed_spec

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.braid_take_len_prefixed_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.braid_take_len_prefixed_of

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.braid_to_bytes_nh_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 zeroize.Zeroizing,
 tacenta_kem.EncapsState.to_bytes,
 tacenta_kem.IncrementalKeyPair.to_bytes,
 zeroize.Zeroizing.new,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.braid_to_bytes_nh_spec

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.decode_state_nh_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.EncapsState.from_bytes,
 tacenta_kem.IncrementalKeyPair.from_bytes,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.decode_state_nh_of

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.braid_from_bytes_nh_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.validate_ek,
 tacenta_kem.EncapsState.from_bytes,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_kem.IncrementalKeyPair.header,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.braid_from_bytes_nh_of

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.export_spec_R' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 zeroize.Zeroizing,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_kem.EncapsState.to_bytes,
 tacenta_kem.IncrementalKeyPair.to_bytes,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 core.num.Usize.div_ceil,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 lifecycle.PrekeyStore.to_bytes._native.decide.ax_1]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.export_spec_R

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.import_unchecked_spec_R' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.validate_ek,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_kem.EncapsState.from_bytes,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_kem.IncrementalKeyPair.header,
 core.num.Usize.div_ceil,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 core.option.Option.Insts.CoreOpsTry_traitTry.branch]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.import_unchecked_spec_R

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.export_import_of_shape_R' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.EncapsState.from_bytes,
 tacenta_kem.EncapsState.to_bytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 tacenta_kem.IncrementalKeyPair.to_bytes,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.as_slice,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.export_import_of_shape_R

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.decode_ec_none_of_len' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.decode_ec_none_of_len

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.established_len_of_structural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.established_len_of_structural

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.received_decoder_small' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.received_decoder_small

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.first_receipt_successor_shape_small' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.first_receipt_successor_shape_small

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.invariant_size_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.invariant_size_le

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.received_codecShapeR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 core.num.Usize.div_ceil,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.received_codecShapeR

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.received_counterRoom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 zeroize.Zeroizing,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 core.num.Usize.div_ceil,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.received_counterRoom

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.first_receipt_successor_round_trip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.EncapsState.from_bytes,
 tacenta_kem.EncapsState.to_bytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 tacenta_kem.IncrementalKeyPair.to_bytes,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.as_slice,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.first_receipt_successor_round_trip

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.responder_first_frame_restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.EncapsState.from_bytes,
 tacenta_kem.EncapsState.to_bytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 tacenta_kem.IncrementalKeyPair.to_bytes,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.as_slice,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.is_empty,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_boundary.kem.KeyPair.public_key,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.responder_first_frame_restored

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.responder_first_frame_restored_encrypt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.EncapsState.from_bytes,
 tacenta_kem.EncapsState.to_bytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 tacenta_kem.IncrementalKeyPair.to_bytes,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.as_slice,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.is_empty,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_boundary.kem.KeyPair.public_key,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.responder_first_frame_restored_encrypt

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.initiator_first_send_responder_restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.EncapsState.from_bytes,
 tacenta_kem.EncapsState.to_bytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 tacenta_kem.IncrementalKeyPair.to_bytes,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.as_slice,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.is_empty,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_boundary.kem.KeyPair.public_key,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.initiator_first_send_responder_restored

/--
info: 'Tacenta.UnitLifecycleRestoredResponder.first_send_restored_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.EncapsState.from_bytes,
 tacenta_kem.EncapsState.to_bytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 tacenta_kem.IncrementalKeyPair.to_bytes,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.as_slice,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.is_empty,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_boundary.kem.KeyPair.public_key,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredResponder.first_send_restored_reachable

/--
info: Tacenta.UnitLifecycleRestoredResponder.be16_length : ∀ (x : U16),
  (Tacenta.UnitLifecycleRestoredResponder.be16 x).length = 2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.be16_length

/--
info: Tacenta.UnitLifecycleRestoredResponder.chunkEnc_length : ∀ (c : tacenta_erasure.Chunk),
  (Tacenta.UnitLifecycleRestoredResponder.chunkEnc c).length = 34
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.chunkEnc_length

/--
info: Tacenta.UnitLifecycleRestoredResponder.dec_to_bytes_loop_empty : ∀ (v : alloc.vec.Vec tacenta_erasure.Chunk)
  (out : alloc.vec.Vec U8), ↑v = [] → tacenta_erasure.Decoder.to_bytes_loop v out 0#usize ⦃ w => w = out ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.dec_to_bytes_loop_empty

/--
info: Tacenta.UnitLifecycleRestoredResponder.dec_to_bytes_loop_one : ∀ (v : alloc.vec.Vec tacenta_erasure.Chunk)
  (out : alloc.vec.Vec U8) (c : tacenta_erasure.Chunk),
  ↑v = [c] →
    (↑out).length + 34 ≤ Usize.max →
      tacenta_erasure.Decoder.to_bytes_loop v out 0#usize ⦃ w =>
        ↑w = ↑out ++ Tacenta.UnitLifecycleRestoredResponder.chunkEnc c ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.dec_to_bytes_loop_one

/--
info: Tacenta.UnitLifecycleRestoredResponder.dec_encoded_len_spec : ∀ (d : tacenta_erasure.Decoder),
  (↑d.have).length ≤ 1 → d.encoded_len ⦃ r => ↑r = 20 + 34 * (↑d.have).length ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.dec_encoded_len_spec

/--
info: Tacenta.UnitLifecycleRestoredResponder.dec_to_bytes_spec : ∀ (d : tacenta_erasure.Decoder),
  (↑d.have).length ≤ 1 → d.to_bytes ⦃ v => ↑v = Tacenta.UnitLifecycleRestoredResponder.decEnc d ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.dec_to_bytes_spec

/--
info: Tacenta.UnitLifecycleRestoredResponder.from_be16 : ∀ (x : U16) (a : Std.Array U8 2#usize),
  ↑a = Tacenta.UnitLifecycleRestoredResponder.be16 x → core.num.U16.from_be_bytes a = x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.from_be16

/--
info: Tacenta.UnitLifecycleRestoredResponder.dec_from_bytes_loop_empty : ∀ (bytes : Slice U8) (pos : Usize)
  (v : alloc.vec.Vec tacenta_erasure.Chunk) (b : Bool),
  tacenta_erasure.Decoder.from_bytes_loop 34#usize { start := 0#usize, «end» := 0#usize } bytes pos v b ⦃ r =>
    r = (pos, v, b) ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.dec_from_bytes_loop_empty

/--
info: Tacenta.UnitLifecycleRestoredResponder.dec_from_bytes_loop_one : ∀ (bytes : Slice U8) (pos : Usize)
  (c : tacenta_erasure.Chunk) (rest : List U8),
  List.drop ↑pos ↑bytes = Tacenta.UnitLifecycleRestoredResponder.chunkEnc c ++ rest →
    ∀ (v : alloc.vec.Vec tacenta_erasure.Chunk),
      ↑v = [] →
        tacenta_erasure.Decoder.from_bytes_loop 34#usize { start := 0#usize, «end» := 1#usize } bytes pos v true ⦃ r =>
          ↑r.1 = ↑pos + 34 ∧ ↑r.2.1 = [c] ∧ r.2.2 = true ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.dec_from_bytes_loop_one

/--
info: Tacenta.UnitLifecycleRestoredResponder.decEnc_length : ∀ (d : tacenta_erasure.Decoder),
  (↑d.have).length ≤ 1 → (Tacenta.UnitLifecycleRestoredResponder.decEnc d).length = 20 + 34 * (↑d.have).length
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.decEnc_length

/--
info: Tacenta.UnitLifecycleRestoredResponder.cast_u64_usize_val : ∀ (x : Usize), ↑(UScalar.cast UScalarTy.U64 x) = ↑x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.cast_u64_usize_val

/--
info: Tacenta.UnitLifecycleRestoredResponder.cast_usize_cast_u64 : ∀ (x : Usize),
  UScalar.cast UScalarTy.Usize (UScalar.cast UScalarTy.U64 x) = x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.cast_usize_cast_u64

/--
info: Tacenta.UnitLifecycleRestoredResponder.dec_from_bytes_of : ∀ (bytes : Slice U8) (d : tacenta_erasure.Decoder),
  ↑bytes = Tacenta.UnitLifecycleRestoredResponder.decEnc d →
    (↑d.have).length ≤ 1 →
      d.invariant = ok true →
        ↑d.needed ≤ 65536 → ↑d.size ≤ 65536 * 32 → tacenta_erasure.Decoder.from_bytes bytes = ok (some d)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.dec_from_bytes_of

/--
info: Tacenta.UnitLifecycleRestoredResponder.braid_push_len_prefixed_spec : ∀ (out : alloc.vec.Vec U8) (s : Slice U8),
  (↑out).length + 4 + (↑s).length ≤ Usize.max →
    tacenta_braid.push_len_prefixed out s ⦃ w => ↑w = ↑out ++ Tacenta.UnitLifecycleSessionCodec.lenEnc s ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.braid_push_len_prefixed_spec

/--
info: Tacenta.UnitLifecycleRestoredResponder.braid_take_len_prefixed_of : ∀ (bytes : Slice U8) (pos : Usize) (n : U32)
  (payload rest : List U8),
  ↑n = payload.length →
    List.drop ↑pos ↑bytes = Tacenta.UnitLifecycleSessionCodec.be32 n ++ (payload ++ rest) →
      tacenta_braid.take_len_prefixed bytes pos ⦃ r =>
        ∃ sl p', r = some (sl, p') ∧ ↑sl = payload ∧ ↑p' = ↑pos + 4 + payload.length ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.braid_take_len_prefixed_of

/--
info: Tacenta.UnitLifecycleRestoredResponder.braid_to_bytes_nh_spec : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  ∀ (epoch : U64) (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder),
    (↑dec.have).length ≤ 1 →
      { state := tacenta_braid.State.NoHeaderReceived epoch auth dec }.to_bytes ⦃ z =>
        ∃ v n,
          zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleSessionCodec.vecInst z = ok v ∧
            ↑n = (Tacenta.UnitLifecycleRestoredResponder.decEnc dec).length ∧
              ↑v = Tacenta.UnitLifecycleRestoredResponder.braidEncNH epoch auth n dec ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.braid_to_bytes_nh_spec

/--
info: Tacenta.UnitLifecycleRestoredResponder.decode_state_nh_of : ∀ (bytes : Slice U8) (pos : Usize) (epoch : U64)
  (auth : tacenta_braid.Auth) (n : U32) (dec : tacenta_erasure.Decoder) (rest : List U8),
  List.drop ↑pos ↑bytes =
      Tacenta.UnitLifecycleSessionCodec.be64 epoch ++
        (Tacenta.UnitLifecycleSessionCodec.authEnc auth ++
          (Tacenta.UnitLifecycleSessionCodec.be32 n ++ (Tacenta.UnitLifecycleRestoredResponder.decEnc dec ++ rest))) →
    epoch ≠ core.num.U64.MAX →
      ↑n = (Tacenta.UnitLifecycleRestoredResponder.decEnc dec).length →
        (↑dec.have).length ≤ 1 →
          dec.invariant = ok true →
            ↑dec.needed ≤ 65536 →
              ↑dec.size ≤ 65536 * 32 →
                tacenta_braid.decode_state 5#u8 bytes pos ⦃ r =>
                  ∃ p,
                    r = some (tacenta_braid.State.NoHeaderReceived epoch auth dec, p) ∧
                      ↑p = ↑pos + 72 + 4 + (Tacenta.UnitLifecycleRestoredResponder.decEnc dec).length ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.decode_state_nh_of

/--
info: Tacenta.UnitLifecycleRestoredResponder.braid_from_bytes_nh_of : ∀ (bytes : Slice U8) (epoch : U64)
  (auth : tacenta_braid.Auth) (n : U32) (dec : tacenta_erasure.Decoder),
  ↑bytes = Tacenta.UnitLifecycleRestoredResponder.braidEncNH epoch auth n dec →
    epoch ≠ core.num.U64.MAX →
      ↑n = (Tacenta.UnitLifecycleRestoredResponder.decEnc dec).length →
        (↑dec.have).length ≤ 1 →
          dec.invariant = ok true →
            ↑dec.needed ≤ 65536 →
              ↑dec.size ≤ 65536 * 32 →
                { state := tacenta_braid.State.NoHeaderReceived epoch auth dec }.invariant = ok true →
                  tacenta_braid.Braid.from_bytes bytes =
                    ok (core.result.Result.Ok { state := tacenta_braid.State.NoHeaderReceived epoch auth dec })
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.braid_from_bytes_nh_of

/--
info: Tacenta.UnitLifecycleRestoredResponder.export_spec_R : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  ∀ (s : lifecycle.Session) (epoch : U64) (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder) (e : U64)
    (c1 c2 : tacenta_spqr.Chain) (eph : alloc.vec.Vec U8),
    Tacenta.UnitLifecycleRestoredResponder.CodecShapeR s epoch auth dec e c1 c2 eph →
      ∀ (zp : zeroize.Zeroizing (Std.Array U8 32#usize)) (pa : Std.Array U8 32#usize),
        s.ratchet_private.to_bytes = ok zp →
          zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleSessionCodec.arrInst zp = ok pa →
            ∀ (oa pea : Std.Array U8 32#usize),
              s.our_identity_public.as_bytes = ok oa →
                s.peer_identity_public.as_bytes = ok pea →
                  s.export ⦃ z =>
                    ∃ vt vb n v,
                      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleSessionCodec.vecInst z =
                          ok v ∧
                        ↑vt = Tacenta.UnitLifecycleSessionCodec.tripleEnc s.triple e c1 c2 ∧
                          ↑vb = Tacenta.UnitLifecycleRestoredResponder.braidEncNH epoch auth n dec ∧
                            ↑n = (Tacenta.UnitLifecycleRestoredResponder.decEnc dec).length ∧
                              ↑v =
                                Tacenta.UnitLifecycleRestoredResponder.sessionEncR vt vb pa s.identity_ad oa pea eph ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.export_spec_R

/--
info: Tacenta.UnitLifecycleRestoredResponder.import_unchecked_spec_R : Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
  ∀ (s : lifecycle.Session) (epoch : U64) (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder) (e : U64)
    (c1 c2 : tacenta_spqr.Chain) (eph : alloc.vec.Vec U8),
    Tacenta.UnitLifecycleRestoredResponder.CodecShapeR s epoch auth dec e c1 c2 eph →
      s.triple.invariant = ok true →
        s.braid.invariant = ok true →
          ∀ (vt vb : alloc.vec.Vec U8) (n : U32) (pa oa pea : Std.Array U8 32#usize),
            ↑vt = Tacenta.UnitLifecycleSessionCodec.tripleEnc s.triple e c1 c2 →
              ↑vb = Tacenta.UnitLifecycleRestoredResponder.braidEncNH epoch auth n dec →
                ↑n = (Tacenta.UnitLifecycleRestoredResponder.decEnc dec).length →
                  tacenta_boundary.dh.PrivateKey.from_bytes pa = ok s.ratchet_private →
                    tacenta_boundary.dh.PublicKeyBytes.from_bytes oa = ok s.our_identity_public →
                      tacenta_boundary.dh.PublicKeyBytes.from_bytes pea = ok s.peer_identity_public →
                        ∀ (bytes : Slice U8),
                          ↑bytes =
                              Tacenta.UnitLifecycleRestoredResponder.sessionEncR vt vb pa s.identity_ad oa pea eph →
                            lifecycle.Session.import_unchecked bytes ⦃ r => r = core.result.Result.Ok s ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.import_unchecked_spec_R

/--
info: Tacenta.UnitLifecycleRestoredResponder.export_import_of_shape_R : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
    Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
      Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
        Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
          ∀ (s : lifecycle.Session) (epoch : U64) (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder) (e : U64)
            (c1 c2 : tacenta_spqr.Chain) (eph : alloc.vec.Vec U8),
            Tacenta.UnitLifecycleRestoredResponder.CodecShapeR s epoch auth dec e c1 c2 eph →
              s.invariant = ok true →
                ∃ z v,
                  s.export = ok z ∧
                    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleSessionCodec.vecInst z = ok v ∧
                      lifecycle.Session.import v.deref = ok (core.result.Result.Ok s)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.export_import_of_shape_R

/--
info: Tacenta.UnitLifecycleRestoredResponder.decode_ec_none_of_len : ∀ (bytes : Slice U8),
  (↑bytes).length ≠ 33 → decode_ec bytes = ok none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.decode_ec_none_of_len

/--
info: Tacenta.UnitLifecycleRestoredResponder.established_len_of_structural : ∀ (s : lifecycle.Session) (e : alloc.vec.Vec U8),
  s.established_ephemeral = some e → s.structural_invariant = ok true → (↑e).length = 33
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.established_len_of_structural

/--
info: Tacenta.UnitLifecycleRestoredResponder.received_decoder_small : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  Tacenta.SessionUnitBraidT1.HeaderLenTotal →
    ∀ {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
      (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg) (m : tacenta_braid.Msg)
      (x : U64) (y : Option tacenta_braid.Output) (bc : tacenta_braid.Braid),
      p.braid.receive m = ok (x, y, bc) →
        ∀ (e : U64) (a : tacenta_braid.Auth) (d' : tacenta_erasure.Decoder),
          bc.state = tacenta_braid.State.NoHeaderReceived e a d' →
            (↑d'.have).length ≤ 1 ∧
              d'.invariant = ok true ∧
                (do
                    let i ← tacenta_kem.HEADER_LEN
                    let i1 ← i + tacenta_braid.MAC_LEN
                    tacenta_braid.decoder_sized d' i1) =
                  ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.received_decoder_small

/--
info: Tacenta.UnitLifecycleRestoredResponder.first_receipt_successor_shape_small : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  Tacenta.SessionUnitBraidT1.HeaderLenTotal →
    ∀ {E : Type} (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E) {dh : Tacenta.UnitLifecycleT3.DhView},
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        ∀ {traceB : E → List Model.Lifecycle.Key} {oracleB : Model.Lifecycle.Oracle},
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
            ∀ {K : Model.Braid.Kem} {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
              (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg) (rngB : E)
              (dB : Model.Lifecycle.Key) (restB : List Model.Lifecycle.Key),
              traceB rngB = dB :: restB →
                ∀ (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (rngB' : E),
                  lifecycle.Session.decrypt_ratchet rcB crcB p.session p.message rngB =
                      ok (core.result.Result.Ok ptB, sB', rngB') →
                    ∀ (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk)
                      (ec prk k1 k2 d dSend : Model.State.Key) (a4 : Std.Array U8 32#usize),
                      Tacenta.UnitLifecycleT3.SessionRefines dh K sB'
                          (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                            (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) secret rcv ec prk k1 k2
                            (Tacenta.UnitLifecycleT3.arrayOf a4) d dSend (oracleB.dhPublic dB) dB) →
                        ∃ dhs rk cks ckr prk' c2 cr auth dec rp pk,
                          sB' =
                              Tacenta.UnitLifecycleResponderSuccessor.receivedSession p
                                (Tacenta.UnitLifecycleResponderSuccessor.receivedTriple dhs a4 rk cks ckr prk' c2 cr)
                                auth dec rp ∧
                            rp.public_key = ok pk ∧
                              pk.as_bytes = ok dhs ∧
                                (↑dec.have).length ≤ 1 ∧
                                  dec.invariant = ok true ∧
                                    (do
                                        let i ← tacenta_kem.HEADER_LEN
                                        let i1 ← i + tacenta_braid.MAC_LEN
                                        tacenta_braid.decoder_sized dec i1) =
                                      ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.first_receipt_successor_shape_small

/--
info: Tacenta.UnitLifecycleRestoredResponder.invariant_size_le : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  ∀ (d : tacenta_erasure.Decoder), d.invariant = ok true → ↑d.size ≤ 65536 * 32
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.invariant_size_le

/--
info: Tacenta.UnitLifecycleRestoredResponder.received_codecShapeR : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  Tacenta.UnitLifecycleT1.DhCodecTotal →
    ∀ {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
      (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg)
      (dhs dhr rk cks ckr prk c2 cr : Std.Array U8 32#usize) (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder)
      (rp : tacenta_boundary.dh.PrivateKey),
      (↑dec.have).length ≤ 1 →
        dec.invariant = ok true →
          (Tacenta.UnitLifecycleResponderSuccessor.receivedSession p
                  (Tacenta.UnitLifecycleResponderSuccessor.receivedTriple dhs dhr rk cks ckr prk c2 cr) auth dec
                  rp).invariant =
              ok true →
            Tacenta.UnitLifecycleRestoredResponder.CodecShapeR
              (Tacenta.UnitLifecycleResponderSuccessor.receivedSession p
                (Tacenta.UnitLifecycleResponderSuccessor.receivedTriple dhs dhr rk cks ckr prk c2 cr) auth dec rp)
              1#u64 auth dec 0#u64 { ck := c2, n := 0#u64 } { ck := cr, n := 1#u64 } p.ephemeralCopy
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.received_codecShapeR

/--
info: @Tacenta.UnitLifecycleRestoredResponder.received_counterRoom : ∀ {ourB : lifecycle.Identity}
  {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg)
  (dhs dhr rk cks ckr prk c2 cr : Std.Array U8 32#usize) (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder)
  (rp : tacenta_boundary.dh.PrivateKey) (k : ℕ),
  k + 3 < U32.max →
    Tacenta.UnitLifecycleSendPreserve.CounterRoom
      (Tacenta.UnitLifecycleResponderSuccessor.receivedSession p
        (Tacenta.UnitLifecycleResponderSuccessor.receivedTriple dhs dhr rk cks ckr prk c2 cr) auth dec rp)
      k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.received_counterRoom

/--
info: Tacenta.UnitLifecycleRestoredResponder.first_receipt_successor_round_trip : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
    Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
      Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
        Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
          Tacenta.UnitLifecycleT1.DhCodecTotal →
            Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
              Tacenta.UnitHeadroomInvariant.OptionEqU64Shape @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                Tacenta.SessionUnitDecoderBound.DivCeilValue →
                  Tacenta.SessionUnitBraidT1.HeaderLenTotal →
                    ∀ {E : Type} (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
                      {dh : Tacenta.UnitLifecycleT3.DhView},
                      Tacenta.UnitLifecycleT3.DhCodecOf dh →
                        ∀ {traceB : E → List Model.Lifecycle.Key} {oracleB : Model.Lifecycle.Oracle},
                          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
                            ∀ {K : Model.Braid.Kem} {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore}
                              {msg : Slice U8}
                              (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg)
                              (rngB : E) (dB : Model.Lifecycle.Key) (restB : List Model.Lifecycle.Key),
                              traceB rngB = dB :: restB →
                                ∀ (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (rngB' : E),
                                  lifecycle.Session.decrypt_ratchet rcB crcB p.session p.message rngB =
                                      ok (core.result.Result.Ok ptB, sB', rngB') →
                                    ∀ (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk)
                                      (ec prk k1 k2 d dSend : Model.State.Key) (a4 : Std.Array U8 32#usize),
                                      Tacenta.SessionUnitT1.canonicalX25519 a4 = true →
                                        Tacenta.UnitLifecycleT3.SessionRefines dh K sB'
                                            (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                              (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) secret rcv
                                              ec prk k1 k2 (Tacenta.UnitLifecycleT3.arrayOf a4) d dSend
                                              (oracleB.dhPublic dB) dB) →
                                          (∃ z v,
                                              sB'.export = ok z ∧
                                                zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                                      Tacenta.UnitLifecycleSessionCodec.vecInst z =
                                                    ok v ∧
                                                  lifecycle.Session.import v.deref = ok (core.result.Result.Ok sB')) ∧
                                            ∀ (j : ℕ),
                                              j + 3 < U32.max → Tacenta.UnitLifecycleSendPreserve.CounterRoom sB' j
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.first_receipt_successor_round_trip

/--
info: @Tacenta.UnitLifecycleRestoredResponder.responder_first_frame_restored : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
  [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type},
  Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
    Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
      Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
        Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
          ∀ (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
            (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
            Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
              Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                  Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                    Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                      Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                        Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                              @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                            ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
                              Tacenta.UnitLifecycleT3.DhCodecOf dh →
                                ∀ (view : Model.Lifecycle.CodewordView) (oracleA : Model.Lifecycle.Oracle),
                                  Tacenta.UnitOracleShape.AeadSealClause Tacenta.UnitSatisfiabilityJoint.Interp.real
                                      oracleA →
                                    ∀ (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle),
                                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
                                        Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                            oracleB.braidKem →
                                          ∀
                                            (q :
                                              Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our
                                                bundle)
                                            (pending : Model.Lifecycle.PendingInitial),
                                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh
                                                    q.session).pendingInitial =
                                                some pending →
                                              ∀ (plaintext : Slice U8),
                                                (↑plaintext).length + 48 ≤ Usize.max →
                                                  ∀ (src : Model.Lifecycle.Bytes),
                                                    List.length src = Model.Braid.headerSize + Model.Braid.macSize →
                                                      ∀ (c : tacenta_erasure.Chunk),
                                                        Tacenta.SessionUnitBraidT3.CodewordOf src c →
                                                          view.send
                                                                (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                    dh q.session).braid
                                                                (Tacenta.UnitLifecycleT3.modelChunkOf src c) =
                                                              Tacenta.UnitLifecycleT3.modelCodewordOf c →
                                                            ∀ (msg : Slice U8),
                                                              Tacenta.UnitLifecycleT3.sliceOf msg =
                                                                  Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
                                                                    (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                      dh q.session)
                                                                    pending
                                                                    (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame
                                                                      view oracleA
                                                                      (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                        dh q.session)
                                                                      (Tacenta.UnitLifecycleT3.sliceOf plaintext)
                                                                      (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                        (Tacenta.UnitLifecycleT3.arrayOf q.sendChain)
                                                                        (Tacenta.UnitLifecycleT3.arrayOf q.sparseSend))
                                                                      (Tacenta.UnitLifecycleT3.modelChunkOf src c)) →
                                                                ∀ (ourB : lifecycle.Identity)
                                                                  (storeB : lifecycle.PrekeyStore),
                                                                  storeB.publish = ok bundle →
                                                                    ourB.public = ok storeB.identity_public →
                                                                      Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                          storeB →
                                                                        Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                            storeB bundle.kem_prekey_id q.kemCiphertext
                                                                            q.kemSecret →
                                                                          ∀ (rngB : E),
                                                                            traceB rngB = oracleB.draws →
                                                                              ∀ (dB : Model.Lifecycle.Key)
                                                                                (restB : List Model.Lifecycle.Key),
                                                                                traceB rngB = dB :: restB →
                                                                                  ∀ (ptB : alloc.vec.Vec U8)
                                                                                    (sB' : lifecycle.Session)
                                                                                    (storeB' : lifecycle.PrekeyStore)
                                                                                    (rngB' : E),
                                                                                    lifecycle.establish_responder rcB
                                                                                          crcB ourB storeB msg rngB =
                                                                                        ok
                                                                                          (core.result.Result.Ok
                                                                                              (sB', ptB),
                                                                                            storeB', rngB') →
                                                                                      ∃ p ec dSend,
                                                                                        Tacenta.UnitLifecycleT3.SessionRefines
                                                                                            dh oracleB.braidKem sB'
                                                                                            (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                                              (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                                dh p)
                                                                                              (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                p.braidSecret)
                                                                                              (Tacenta.UnitLifecycleT3.modelChunkOf
                                                                                                src c)
                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                ec)
                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                q.sparseRoot)
                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                q.sparseSend)
                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                q.sparseReceive)
                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                q.ratchetBytes)
                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                q.dhOut)
                                                                                              dSend
                                                                                              (oracleB.dhPublic dB)
                                                                                              dB) ∧
                                                                                          sB'.invariant = ok true ∧
                                                                                            Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                                sB' ∧
                                                                                              (∀ (j : ℕ),
                                                                                                  j + 3 < U32.max →
                                                                                                    Tacenta.UnitLifecycleSendPreserve.CounterRoom
                                                                                                      sB' j) ∧
                                                                                                ∃ z v,
                                                                                                  sB'.export = ok z ∧
                                                                                                    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                                                                                          Tacenta.UnitLifecycleSessionCodec.vecInst
                                                                                                          z =
                                                                                                        ok v ∧
                                                                                                      lifecycle.Session.import
                                                                                                          v.deref =
                                                                                                        ok
                                                                                                          (core.result.Result.Ok
                                                                                                            sB')
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.responder_first_frame_restored

/--
info: @Tacenta.UnitLifecycleRestoredResponder.responder_first_frame_restored_encrypt : ∀ {R : Type}
  {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity}
  {bundle : lifecycle.PublishedBundle} [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type},
  Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
    Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
      Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
        Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
          ∀ (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
            (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
            Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
              Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                  Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                    Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                      Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                        Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                              @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                            ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
                              Tacenta.UnitLifecycleT3.DhCodecOf dh →
                                ∀ (view : Model.Lifecycle.CodewordView) (oracleA : Model.Lifecycle.Oracle),
                                  Tacenta.UnitOracleShape.AeadSealClause Tacenta.UnitSatisfiabilityJoint.Interp.real
                                      oracleA →
                                    ∀ (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle),
                                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
                                        Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                            oracleB.braidKem →
                                          ∀
                                            (q :
                                              Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our
                                                bundle)
                                            (pending : Model.Lifecycle.PendingInitial),
                                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh
                                                    q.session).pendingInitial =
                                                some pending →
                                              ∀ (plaintext : Slice U8),
                                                (↑plaintext).length + 48 ≤ Usize.max →
                                                  ∀ (src : Model.Lifecycle.Bytes),
                                                    List.length src = Model.Braid.headerSize + Model.Braid.macSize →
                                                      ∀ (c : tacenta_erasure.Chunk),
                                                        Tacenta.SessionUnitBraidT3.CodewordOf src c →
                                                          view.send
                                                                (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                    dh q.session).braid
                                                                (Tacenta.UnitLifecycleT3.modelChunkOf src c) =
                                                              Tacenta.UnitLifecycleT3.modelCodewordOf c →
                                                            ∀ (msg : Slice U8),
                                                              Tacenta.UnitLifecycleT3.sliceOf msg =
                                                                  Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
                                                                    (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                      dh q.session)
                                                                    pending
                                                                    (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame
                                                                      view oracleA
                                                                      (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                        dh q.session)
                                                                      (Tacenta.UnitLifecycleT3.sliceOf plaintext)
                                                                      (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                        (Tacenta.UnitLifecycleT3.arrayOf q.sendChain)
                                                                        (Tacenta.UnitLifecycleT3.arrayOf q.sparseSend))
                                                                      (Tacenta.UnitLifecycleT3.modelChunkOf src c)) →
                                                                ∀ (ourB : lifecycle.Identity)
                                                                  (storeB : lifecycle.PrekeyStore),
                                                                  storeB.publish = ok bundle →
                                                                    ourB.public = ok storeB.identity_public →
                                                                      Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                          storeB →
                                                                        Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                            storeB bundle.kem_prekey_id q.kemCiphertext
                                                                            q.kemSecret →
                                                                          ∀ (rngB : E),
                                                                            traceB rngB = oracleB.draws →
                                                                              ∀ (dB : Model.Lifecycle.Key)
                                                                                (restB : List Model.Lifecycle.Key),
                                                                                traceB rngB = dB :: restB →
                                                                                  ∀ (ptB : alloc.vec.Vec U8)
                                                                                    (sB' : lifecycle.Session)
                                                                                    (storeB' : lifecycle.PrekeyStore)
                                                                                    (rngB' : E),
                                                                                    lifecycle.establish_responder rcB
                                                                                          crcB ourB storeB msg rngB =
                                                                                        ok
                                                                                          (core.result.Result.Ok
                                                                                              (sB', ptB),
                                                                                            storeB', rngB') →
                                                                                      ∀
                                                                                        {kemE :
                                                                                          Tacenta.UnitLifecycleT3.KemView}
                                                                                        {viewE :
                                                                                          Model.Lifecycle.CodewordView}
                                                                                        {traceE :
                                                                                          E → List Model.Lifecycle.Key}
                                                                                        {oracleE :
                                                                                          Model.Lifecycle.Oracle},
                                                                                        Tacenta.UnitLifecycleT3.BraidSendRefinementContracts
                                                                                            rcB oracleE.braidKem →
                                                                                          Tacenta.UnitLifecycleT3.TripleSendRefinementContracts →
                                                                                            Tacenta.UnitLifecycleT1.AeadSealBounded →
                                                                                              Tacenta.UnitLifecycleT3.OracleOf
                                                                                                  rcB crcB dh kemE
                                                                                                  traceE oracleE →
                                                                                                Tacenta.UnitLifecycleT3.CodewordViewSendOf
                                                                                                    viewE →
                                                                                                  Tacenta.SessionUnitT3.ZeroizingRoundTrips80 →
                                                                                                    Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
                                                                                                        (Std.Array U8
                                                                                                          32#usize) →
                                                                                                      Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
                                                                                                          (Std.Array U8
                                                                                                              32#usize ×
                                                                                                            Std.Array U8
                                                                                                                32#usize ×
                                                                                                              Std.Array
                                                                                                                U8
                                                                                                                16#usize) →
                                                                                                        Tacenta.UnitLifecycleEncryptPreserve.SendInvariantLaws
                                                                                                            oracleE.braidKem →
                                                                                                          Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor
                                                                                                              oracleE.braidKem
                                                                                                              rcB crcB
                                                                                                              traceE →
                                                                                                            oracleE.braidKem =
                                                                                                                oracleB.braidKem →
                                                                                                              ∀
                                                                                                                (ptE :
                                                                                                                  Slice
                                                                                                                    U8),
                                                                                                                (↑ptE).length +
                                                                                                                      65770 ≤
                                                                                                                    Usize.max →
                                                                                                                  ∀
                                                                                                                    (rngE :
                                                                                                                      E),
                                                                                                                    traceE
                                                                                                                          rngE =
                                                                                                                        oracleE.draws →
                                                                                                                      ∀
                                                                                                                        (k :
                                                                                                                          ℕ),
                                                                                                                        k +
                                                                                                                              4 <
                                                                                                                            U32.max →
                                                                                                                          ∃
                                                                                                                            p
                                                                                                                            ec
                                                                                                                            dSend
                                                                                                                            z
                                                                                                                            v,
                                                                                                                            sB'.export =
                                                                                                                                ok
                                                                                                                                  z ∧
                                                                                                                              zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                                                                                                                    Tacenta.UnitLifecycleSessionCodec.vecInst
                                                                                                                                    z =
                                                                                                                                  ok
                                                                                                                                    v ∧
                                                                                                                                ∀
                                                                                                                                  (sR :
                                                                                                                                    lifecycle.Session),
                                                                                                                                  lifecycle.Session.import
                                                                                                                                        v.deref =
                                                                                                                                      ok
                                                                                                                                        (core.result.Result.Ok
                                                                                                                                          sR) →
                                                                                                                                    sR =
                                                                                                                                        sB' ∧
                                                                                                                                      ∃
                                                                                                                                        output,
                                                                                                                                        lifecycle.Session.encrypt
                                                                                                                                              rcB
                                                                                                                                              crcB
                                                                                                                                              sR
                                                                                                                                              ptE
                                                                                                                                              rngE =
                                                                                                                                            ok
                                                                                                                                              output ∧
                                                                                                                                          Tacenta.UnitLifecycleT3.StepRefines
                                                                                                                                              traceE
                                                                                                                                              dh
                                                                                                                                              oracleE.braidKem
                                                                                                                                              output
                                                                                                                                              (Model.Lifecycle.encrypt
                                                                                                                                                viewE
                                                                                                                                                oracleE
                                                                                                                                                (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                                                                                                  (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                                                                                    dh
                                                                                                                                                    p)
                                                                                                                                                  (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                                    p.braidSecret)
                                                                                                                                                  (Tacenta.UnitLifecycleT3.modelChunkOf
                                                                                                                                                    src
                                                                                                                                                    c)
                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                    ec)
                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                    q.sparseRoot)
                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                    q.sparseSend)
                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                    q.sparseReceive)
                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                    q.ratchetBytes)
                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                    q.dhOut)
                                                                                                                                                  dSend
                                                                                                                                                  (oracleB.dhPublic
                                                                                                                                                    dB)
                                                                                                                                                  dB)
                                                                                                                                                (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                                  ptE)) ∧
                                                                                                                                            output.2.1.invariant =
                                                                                                                                                ok
                                                                                                                                                  true ∧
                                                                                                                                              Tacenta.UnitLifecycleSendPreserve.CounterRoom
                                                                                                                                                output.2.1
                                                                                                                                                k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.responder_first_frame_restored_encrypt

/--
info: @Tacenta.UnitLifecycleRestoredResponder.initiator_first_send_responder_restored : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type},
  Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
    Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
      Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
        Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
          ∀ (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
            (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
            (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
            Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc oracle.braidKem →
              Tacenta.UnitLifecycleT3.TripleSendRefinementContracts →
                Tacenta.UnitLifecycleT1.AeadSealBounded →
                  Tacenta.UnitLifecycleT1.DhCodecTotal →
                    Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle →
                      Tacenta.UnitLifecycleT3.DhCodecOf dh →
                        Tacenta.UnitLifecycleT3.CodewordViewSendOf view →
                          Tacenta.SessionUnitT3.ZeroizingRoundTrips80 →
                            Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Std.Array U8 32#usize) →
                              Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
                                  (Std.Array U8 32#usize × Std.Array U8 32#usize × Std.Array U8 16#usize) →
                                Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
                                  Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem →
                                    Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                                      Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                                        ∀ (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
                                          (ourA : lifecycle.Identity) (bundleA : lifecycle.PublishedBundle)
                                          (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                                          (s : lifecycle.Session),
                                          lifecycle.establish_initiator_for rcE crcE ourA bundleA expected rng0 =
                                              ok (core.result.Result.Ok s, rng1) →
                                            ∀
                                              (q :
                                                Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcE crcE
                                                  ourA bundleA),
                                              s = q.session →
                                                ∀ (plaintext : Slice U8),
                                                  (↑plaintext).length + 65770 ≤ Usize.max →
                                                    ∀ (rng : R),
                                                      trace rng = oracle.draws →
                                                        ∀ (d1 d2 : Model.Lifecycle.Key)
                                                          (rest : List Model.Lifecycle.Key),
                                                          trace rng = d1 :: d2 :: rest →
                                                            ∀ (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session)
                                                              (rng' : R),
                                                              lifecycle.Session.encrypt rc crc s plaintext rng =
                                                                  ok (core.result.Result.Ok bytes, s', rng') →
                                                                ∀ (rcB : rand_core_1.RngCore F)
                                                                  (crcB : rand_core_1.CryptoRng F)
                                                                  (contracts :
                                                                    Tacenta.UnitLifecycleT1.EstablishResponderContracts
                                                                      rcB),
                                                                  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                                                                    Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                                                                      Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                                                                        Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                                                                          Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                                                                            Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                                                                                @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                                                                              ∀ (traceB : F → List Model.Lifecycle.Key)
                                                                                (oracleB : Model.Lifecycle.Oracle),
                                                                                Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf
                                                                                    rcB crcB dh traceB oracleB →
                                                                                  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                                      oracleB.braidKem →
                                                                                    ∀ (ourB : lifecycle.Identity)
                                                                                      (storeB : lifecycle.PrekeyStore),
                                                                                      storeB.publish = ok bundleA →
                                                                                        ourB.public =
                                                                                            ok storeB.identity_public →
                                                                                          Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                                              storeB →
                                                                                            Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                                                storeB
                                                                                                bundleA.kem_prekey_id
                                                                                                q.kemCiphertext
                                                                                                q.kemSecret →
                                                                                              ∀ (rngB : F),
                                                                                                traceB rngB =
                                                                                                    oracleB.draws →
                                                                                                  ∀
                                                                                                    (dB :
                                                                                                      Model.Lifecycle.Key)
                                                                                                    (restB :
                                                                                                      List
                                                                                                        Model.Lifecycle.Key),
                                                                                                    traceB rngB =
                                                                                                        dB :: restB →
                                                                                                      ∀
                                                                                                        (ptB :
                                                                                                          alloc.vec.Vec
                                                                                                            U8)
                                                                                                        (sB' :
                                                                                                          lifecycle.Session)
                                                                                                        (storeB' :
                                                                                                          lifecycle.PrekeyStore)
                                                                                                        (rngB' : F),
                                                                                                        lifecycle.establish_responder
                                                                                                              rcB crcB
                                                                                                              ourB
                                                                                                              storeB
                                                                                                              bytes.deref
                                                                                                              rngB =
                                                                                                            ok
                                                                                                              (core.result.Result.Ok
                                                                                                                  (sB',
                                                                                                                    ptB),
                                                                                                                storeB',
                                                                                                                rngB') →
                                                                                                          ∃ p ec dSend
                                                                                                            dk ekSeed
                                                                                                            ekVector,
                                                                                                            oracle.braidKem.keyGen
                                                                                                                  (Model.Lifecycle.braidRandomness
                                                                                                                    (d1 ++
                                                                                                                      d2)) =
                                                                                                                some
                                                                                                                  (dk,
                                                                                                                    ekSeed,
                                                                                                                    ekVector) ∧
                                                                                                              Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                                  dh
                                                                                                                  oracleB.braidKem
                                                                                                                  sB'
                                                                                                                  (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                                                                    (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                                                      dh
                                                                                                                      p)
                                                                                                                    (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                      p.braidSecret)
                                                                                                                    {
                                                                                                                      source :=
                                                                                                                        Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                          oracle.braidKem
                                                                                                                          (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                            q.auth)
                                                                                                                          ekSeed
                                                                                                                          ekVector,
                                                                                                                      index :=
                                                                                                                        0 }
                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                      ec)
                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                      q.sparseRoot)
                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                      q.sparseSend)
                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                      q.sparseReceive)
                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                      q.ratchetBytes)
                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                      q.dhOut)
                                                                                                                    dSend
                                                                                                                    (oracleB.dhPublic
                                                                                                                      dB)
                                                                                                                    dB) ∧
                                                                                                                sB'.invariant =
                                                                                                                    ok
                                                                                                                      true ∧
                                                                                                                  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                                                      sB' ∧
                                                                                                                    (∀
                                                                                                                        (j :
                                                                                                                          ℕ),
                                                                                                                        j +
                                                                                                                              3 <
                                                                                                                            U32.max →
                                                                                                                          Tacenta.UnitLifecycleSendPreserve.CounterRoom
                                                                                                                            sB'
                                                                                                                            j) ∧
                                                                                                                      ∃
                                                                                                                        z
                                                                                                                        v,
                                                                                                                        sB'.export =
                                                                                                                            ok
                                                                                                                              z ∧
                                                                                                                          zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                                                                                                                Tacenta.UnitLifecycleSessionCodec.vecInst
                                                                                                                                z =
                                                                                                                              ok
                                                                                                                                v ∧
                                                                                                                            lifecycle.Session.import
                                                                                                                                v.deref =
                                                                                                                              ok
                                                                                                                                (core.result.Result.Ok
                                                                                                                                  sB')
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.initiator_first_send_responder_restored

/--
info: Tacenta.UnitLifecycleRestoredResponder.first_send_restored_reachable : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
    Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
      Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
        ∀ (K : Model.Braid.Kem) (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView),
          Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
            Nonempty
                (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
                  Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
              Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape
                  Tacenta.UnitSatisfiabilityJoint.Interp.real Tacenta.UnitLifecycleIntegrationScreen.byteRng
                  Tacenta.UnitLifecycleIntegrationScreen.byteCrc →
                Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                  Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                    Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLaws K dh kem →
                      Nonempty
                          (Tacenta.UnitSatisfiabilityJoint.ResponderAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
                            Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
                        Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                          Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                            Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape
                                Tacenta.UnitSatisfiabilityJoint.Interp.real tacenta_boundary.kem.KeyPair.public_key
                                @alloc.vec.Vec.is_empty →
                              Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K →
                                Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                                  Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                                    ∀ (ourA : lifecycle.Identity) (seed : List U8),
                                      seed.length = 64 →
                                        K.keyGen
                                              (Model.Lifecycle.braidRandomness
                                                (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠
                                            none →
                                          ∃ oracle bundle q bytes s' rng' ourB storeB sB' ptB storeB' rngB',
                                            oracle.braidKem = K ∧
                                              lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                    Tacenta.UnitLifecycleIntegrationScreen.byteCrc q.session
                                                    Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed =
                                                  ok (core.result.Result.Ok bytes, s', rng') ∧
                                                storeB.publish = ok bundle ∧
                                                  lifecycle.establish_responder
                                                        Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                        Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourB storeB
                                                        bytes.deref seed =
                                                      ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
                                                    sB'.invariant = ok true ∧
                                                      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' ∧
                                                        ∃ z v,
                                                          sB'.export = ok z ∧
                                                            zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                                                  Tacenta.UnitLifecycleSessionCodec.vecInst z =
                                                                ok v ∧
                                                              lifecycle.Session.import v.deref =
                                                                ok (core.result.Result.Ok sB')
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredResponder.first_send_restored_reachable

/--
info: def Tacenta.UnitLifecycleRestoredResponder.be16 : U16 → List U8 :=
fun x => ↑(core.num.U16.to_be_bytes x)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRestoredResponder.be16

/--
info: def Tacenta.UnitLifecycleRestoredResponder.chunkEnc : tacenta_erasure.Chunk → List U8 :=
fun c => Tacenta.UnitLifecycleRestoredResponder.be16 c.index ++ ↑c.data
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRestoredResponder.chunkEnc

/--
info: def Tacenta.UnitLifecycleRestoredResponder.decEnc : tacenta_erasure.Decoder → List U8 :=
fun d =>
  Tacenta.UnitLifecycleSessionCodec.be64 (UScalar.cast UScalarTy.U64 d.size) ++
    (Tacenta.UnitLifecycleSessionCodec.be64 (UScalar.cast UScalarTy.U64 d.needed) ++
      (Tacenta.UnitLifecycleSessionCodec.be32 (UScalar.cast UScalarTy.U32 d.have.len) ++
        List.flatMap Tacenta.UnitLifecycleRestoredResponder.chunkEnc ↑d.have))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRestoredResponder.decEnc

/--
info: def Tacenta.UnitLifecycleRestoredResponder.braidEncNH : U64 →
  tacenta_braid.Auth → U32 → tacenta_erasure.Decoder → List U8 :=
fun epoch auth n dec =>
  1#u8 ::
    5#u8 ::
      (Tacenta.UnitLifecycleSessionCodec.be64 epoch ++
        (Tacenta.UnitLifecycleSessionCodec.authEnc auth ++
          (Tacenta.UnitLifecycleSessionCodec.be32 n ++ Tacenta.UnitLifecycleRestoredResponder.decEnc dec)))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRestoredResponder.braidEncNH

/--
info: structure Tacenta.UnitLifecycleRestoredResponder.CodecShapeR (s : lifecycle.Session) (epoch : U64)
  (auth : tacenta_braid.Auth) (dec : tacenta_erasure.Decoder) (e : U64) (c1 c2 : tacenta_spqr.Chain)
  (eph : alloc.vec.Vec U8) : Prop
number of parameters: 8
fields:
  Tacenta.UnitLifecycleRestoredResponder.CodecShapeR.braid : s.braid =
      { state := tacenta_braid.State.NoHeaderReceived epoch auth dec }
  Tacenta.UnitLifecycleRestoredResponder.CodecShapeR.epochNotMax : epoch ≠ core.num.U64.MAX
  Tacenta.UnitLifecycleRestoredResponder.CodecShapeR.decHave : (↑dec.have).length ≤ 1
  Tacenta.UnitLifecycleRestoredResponder.CodecShapeR.decInv : dec.invariant = ok true
  Tacenta.UnitLifecycleRestoredResponder.CodecShapeR.decNeeded : ↑dec.needed ≤ 65536
  Tacenta.UnitLifecycleRestoredResponder.CodecShapeR.decSize : ↑dec.size ≤ 65536 * 32
  Tacenta.UnitLifecycleRestoredResponder.CodecShapeR.classicalSkipped : ↑s.triple.classical.skipped = []
  Tacenta.UnitLifecycleRestoredResponder.CodecShapeR.chains : ↑s.triple.post_quantum.chains =
      [(e, { send := some c1, receive := some c2 })]
  Tacenta.UnitLifecycleRestoredResponder.CodecShapeR.sparseSkipped : ↑s.triple.post_quantum.skipped = []
  Tacenta.UnitLifecycleRestoredResponder.CodecShapeR.identityAd : (↑s.identity_ad).length ≤ 65536
  Tacenta.UnitLifecycleRestoredResponder.CodecShapeR.pending : s.pending_initial = none
  Tacenta.UnitLifecycleRestoredResponder.CodecShapeR.established : s.established_ephemeral = some eph
  Tacenta.UnitLifecycleRestoredResponder.CodecShapeR.ephemeralLen : (↑eph).length ≤ 65536
constructor:
  Tacenta.UnitLifecycleRestoredResponder.CodecShapeR.mk {s : lifecycle.Session} {epoch : U64}
    {auth : tacenta_braid.Auth} {dec : tacenta_erasure.Decoder} {e : U64} {c1 c2 : tacenta_spqr.Chain}
    {eph : alloc.vec.Vec U8} (braid : s.braid = { state := tacenta_braid.State.NoHeaderReceived epoch auth dec })
    (epochNotMax : epoch ≠ core.num.U64.MAX) (decHave : (↑dec.have).length ≤ 1) (decInv : dec.invariant = ok true)
    (decNeeded : ↑dec.needed ≤ 65536) (decSize : ↑dec.size ≤ 65536 * 32)
    (classicalSkipped : ↑s.triple.classical.skipped = [])
    (chains : ↑s.triple.post_quantum.chains = [(e, { send := some c1, receive := some c2 })])
    (sparseSkipped : ↑s.triple.post_quantum.skipped = []) (identityAd : (↑s.identity_ad).length ≤ 65536)
    (pending : s.pending_initial = none) (established : s.established_ephemeral = some eph)
    (ephemeralLen : (↑eph).length ≤ 65536) :
    Tacenta.UnitLifecycleRestoredResponder.CodecShapeR s epoch auth dec e c1 c2 eph
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRestoredResponder.CodecShapeR

/--
info: def Tacenta.UnitLifecycleRestoredResponder.sessionEncR : alloc.vec.Vec U8 →
  alloc.vec.Vec U8 →
    Std.Array U8 32#usize →
      alloc.vec.Vec U8 → Std.Array U8 32#usize → Std.Array U8 32#usize → alloc.vec.Vec U8 → List U8 :=
fun vt vb pa ad oa pea eph =>
  1#u8 ::
    (Tacenta.UnitLifecycleSessionCodec.lenEnc vt.deref ++
      (Tacenta.UnitLifecycleSessionCodec.lenEnc vb.deref ++
        (↑pa ++
          (Tacenta.UnitLifecycleSessionCodec.lenEnc ad.deref ++
            (↑oa ++ (↑pea ++ 0#u8 :: 1#u8 :: Tacenta.UnitLifecycleSessionCodec.lenEnc eph.deref))))))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRestoredResponder.sessionEncR
