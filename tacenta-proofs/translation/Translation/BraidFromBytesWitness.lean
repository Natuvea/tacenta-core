import Translation.ImportInv

/-!
# `tacenta_braid.Braid.from_bytes` accepts a byte string, so the Braid import theorems are not vacuous

`Braid.from_bytes_establishes_inv`, `Braid.from_bytes_establishes_invariant` and
`Braid.decoded_receive_no_panic` (`Translation/ImportInv.lean`, namespace
`Tacenta.ImportInv.Braid`) take as hypothesis that the translated decoder
`tacenta_braid.Braid.from_bytes` returned `Ok b`. Before this file no theorem showed that the
Braid decoder accepts any byte string, so those theorems were true of a decoder that refuses every
buffer. This file is the witness, in the leaf environment (no Triple or Session unit), for the
`KeysUnsampled` state, which holds no erasure or KEM value. It does not cover the states that do
(tags 1 to 10), whose decode runs through the opaque erasure and KEM decoders. It follows the
classical ratchet's `Ratchet.from_bytes_accepts_witness` in `ImportInv.lean`.

## The byte string

74 bytes: the encoding `Braid::to_bytes` writes for the smallest `KeysUnsampled` state.
In the order of the format (`braid/src/lib.rs`, `STATE_VERSION`, `decode_state` tag 0,
`read_epoch`, `read_auth`):

* byte 0: version `1`;
* byte 1: state tag `0` (`KeysUnsampled`);
* bytes 2 to 9: epoch, big-endian `1` (seven zero bytes, then a `1` at byte 9);
* bytes 10 to 73: the authenticator, sixty-four zero bytes (root key and MAC key).

Every byte other than byte 0 and byte 9 is zero. Nothing is left over: the decoder's position
after `read_auth` is 74, the length of the buffer.

## What the decode path calls

On this path the decoder calls only functions the translation defines: `read_epoch` (which
reads eight bytes and refuses `u64::MAX`), `read_auth` (which needs sixty-four more bytes and
calls `Auth::from_bytes`, a pair of `copy_from_slice` calls on fixed ranges), and then
`Braid::invariant`. For a `KeysUnsampled` state the translated `invariant` is
`ok (epoch >= 1#u64)`. It calls no opaque declaration: nothing from `tacenta_erasure`, nothing
from `tacenta_kem`, no hash and no MAC. So acceptance is proved here with no hypothesis about
any of them. The only library facts used are the Aeneas standard library's specifications of
slice indexing, `copy_from_slice` and `from_be_bytes`, which `step*` consumes.

Read the `#print axioms` lines at the foot accordingly. They list `tacenta_erasure.*` and
`tacenta_kem.*` declarations, but only because those names occur in the definitions of
`decode_state` (tags 1 to 10) and `Braid.invariant` (the other eleven arms), which the
theorem's statement mentions; this path never reaches them. Every one of them is an
uninterpreted data constant (a type, a function or a `Result`), none is a proposition, and the
proof uses no property of any of them. The same list is what
`Tacenta.ImportInv.Braid.from_bytes_establishes_inv` prints, since it names the same definitions.

`braid_from_bytes_establishes_inv_nonvacuous` then composes with
`Tacenta.ImportInv.Braid.from_bytes_establishes_inv`, which needs the one hypothesis that
theorem already carries: `Tacenta.BraidT1.Ct1LenTotal`, that the opaque constant
`tacenta_kem.CT1_LEN` is a value of at most 4096 (the Rust constant is 1408). That hypothesis
is not used by the acceptance theorem; it is used only to derive `Inv` from the invariant
returning `true`, by an earlier theorem of the file this one imports. `Braid.Inv` has one clause, a
ciphertext-length bound that is `True` outside tags 3, 4, 7, 8 and 9, so on this state it is trivial:
the result shows that the decoder accepts a string and that the premise of
`from_bytes_establishes_inv` is satisfiable, and it does not exercise the clause.

## The proof

The classical witness's technique: a concrete list literal, local `@[step]` specifications for
the byte readers (here on the eight-byte epoch `1` and on any sixty-four bytes for the
authenticator, whose value the invariant never reads), `decide` and `rfl` on concrete reads,
and `step*`. The tag-0 arm of `decode_state` is isolated by an `rfl` equation, because
`step*` on the whole eleven-way `match` on the tag trips over its literal patterns.
-/

open Aeneas Aeneas.Std Result
open tacenta_braid

namespace Tacenta.BraidFromBytesWitness

set_option maxRecDepth 100000

/-- The 74 bytes: version `1`, tag `0`, the epoch `1` as eight big-endian bytes (seven zeros
and a `1`), and a sixty-four byte all-zero authenticator. -/
def braidWitnessList : List Std.U8 :=
  1#u8 :: 0#u8 :: (List.replicate 7 0#u8 ++ 1#u8 :: List.replicate 64 0#u8)

theorem braidWitnessList_length : braidWitnessList.length = 74 := by simp [braidWitnessList]

/-- The same bytes, as the `Slice` the translated `from_bytes` takes. -/
def braidWitnessBytes : Slice Std.U8 :=
  ⟨braidWitnessList, by rw [braidWitnessList_length]; scalar_tac⟩

@[local simp] theorem braidWitnessBytes_val : braidWitnessBytes.val = braidWitnessList := rfl
@[local simp] theorem braidWitnessBytes_length : braidWitnessBytes.length = 74 :=
  braidWitnessList_length
@[local simp] theorem braidWitnessBytes_len : Slice.len braidWitnessBytes = 74#usize := rfl

def epochOneBytes : List Std.U8 := List.replicate 7 0#u8 ++ [1#u8]

@[local step]
theorem read_u64_epoch_one (v : Slice Std.U8) (pos : Std.Usize)
    (hlen : pos.val + 8 ≤ v.length)
    (hz : List.slice pos.val (pos.val + 8) v.val = epochOneBytes) :
    read_u64 v pos ⦃ fun r => r = some 1#u64 ⦄ := by
  unfold read_u64
  step*
  · scalar_tac
  · have h8 : s2.val = epochOneBytes := by
      rw [s2_post, s1_post1, i1_post]; exact hz
    have h5 : to_slice_mut_back s2 = ⟨epochOneBytes, by simp [epochOneBytes]⟩ := by
      rw [s_post2]
      apply Subtype.ext
      rw [Std.Array.from_slice_val _ _ (by rw [h8]; rfl)]
      rw [h8]
    have h6 : i2.bv = (1#u64).bv := by
      rw [i2_post, h5]
      decide
    have h7 : i2 = 1#u64 := by
      cases i2; cases h6; rfl
    rw [h7]

@[local step]
theorem read_epoch_one (v : Slice Std.U8) (pos : Std.Usize)
    (hlen : pos.val + 8 ≤ v.length)
    (hz : List.slice pos.val (pos.val + 8) v.val = epochOneBytes) :
    read_epoch v pos ⦃ fun r => r = some 1#u64 ⦄ := by
  have hne : ¬ ((1#u64 : Std.U64) = core.num.U64.MAX) := by decide
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists (read_u64_epoch_one v pos hlen hz)
  unfold read_epoch
  rw [hr]
  subst hre
  simp only [bind_tc_ok]
  rw [if_neg hne]
  simp

@[local step]
theorem auth_from_bytes_total (bytes : Std.Array Std.U8 64#usize) :
    Auth.from_bytes bytes ⦃ fun _ => True ⦄ := by
  unfold Auth.from_bytes
  step*
  · simp [Slice.length, s_post1, s1_post2]
  · have hb : bytes.to_slice.length = 64 := by simp [Std.Array.to_slice, Slice.length]
    simp only [Slice.length] at s3_post1 s4_post2 hb ⊢
    simp [s3_post1, s4_post2]

@[local step]
theorem read_auth_present (v : Slice Std.U8) (pos : Std.Usize)
    (hlen : pos.val + 64 ≤ v.length) :
    read_auth v pos ⦃ fun r => ∃ a p, r = some (a, p) ∧ p.val = pos.val + 64 ⦄ := by
  unfold read_auth
  step*
  rw [s1_post2]
  simp only [Slice.length, s_post1]
  simp
  omega

theorem slice_2_10 : List.slice 2 10 braidWitnessList = epochOneBytes := by
  simp [List.slice, braidWitnessList, epochOneBytes]

theorem decode_state_zero (bytes : Slice Std.U8) (pos : Std.Usize) :
    decode_state 0#u8 bytes pos = (do
      let o ← read_epoch bytes pos
      match o with
      | none => ok none
      | some epoch =>
        let i ← pos + 8#usize
        let o1 ← read_auth bytes i
        match o1 with
        | none => ok none
        | some p =>
          let (auth, pos1) := p
          ok (some (State.KeysUnsampled epoch auth, pos1))) := by
  unfold decode_state
  rfl

theorem decode_state_witness :
    decode_state 0#u8 braidWitnessBytes 2#usize ⦃ fun r =>
      ∃ a e, r = some (State.KeysUnsampled e a, 74#usize) ∧ e.val = 1 ⦄ := by
  rw [decode_state_zero]
  step*
  · simp [braidWitnessList_length]
  · exact slice_2_10
  · rw [i_post]; simp [braidWitnessList_length]
  · rename_i hxu hxo hp
    rw [o1_post1] at hp
    have hp' := Option.some.inj hp
    subst hp'
    have he : epoch = 1#u64 := by
      have h := ‹o = some epoch›
      rw [o_post] at h
      exact (Option.some.inj h).symm
    have hxu' : hxu = 74#usize := by
      apply Std.UScalar.eq_of_val_eq
      rw [o1_post2, i_post]
      rfl
    subst hxu'
    exact ⟨o1, epoch, rfl, by rw [he]; rfl⟩

set_option maxHeartbeats 1000000 in
/-- **The translated `Braid.from_bytes` accepts `braidWitnessBytes`.** No hypothesis. -/
theorem braid_from_bytes_accepts_witness :
    ∃ b, Braid.from_bytes braidWitnessBytes = ok (core.result.Result.Ok b) := by
  have h : Braid.from_bytes braidWitnessBytes
      ⦃ fun r => ∃ b, r = core.result.Result.Ok b ⦄ := by
    unfold Braid.from_bytes
    rw [if_neg (by decide), Tacenta.ImportInv.slice_index_eq braidWitnessBytes 0#usize 1#u8 (by decide)]
    simp only [bind_tc_ok]
    rw [if_neg (by simp [STATE_VERSION])]
    rw [Tacenta.ImportInv.slice_index_eq braidWitnessBytes 1#usize 0#u8 (by decide)]
    simp only [bind_tc_ok]
    obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists decode_state_witness
    obtain ⟨a, e, rfl, he⟩ := hre
    rw [hr]
    simp only [bind_tc_ok]
    change (if (74#usize : Std.Usize) = 74#usize then (do
          let b ← Braid.invariant { state := State.KeysUnsampled e a }
          if b = true then ok (core.result.Result.Ok { state := State.KeysUnsampled e a })
          else ok (core.result.Result.Err BraidDecodeError.Malformed))
        else ok (core.result.Result.Err BraidDecodeError.Malformed) :
          Result (core.result.Result Braid BraidDecodeError)) ⦃ _ ⦄
    rw [if_pos rfl]
    have hinv : Braid.invariant { state := State.KeysUnsampled e a } = ok true := by
      unfold Braid.invariant
      have : decide (e ≥ 1#u64) = true := by
        simp only [ge_iff_le, decide_eq_true_eq]; scalar_tac
      show ok (decide (e ≥ 1#u64)) = ok true
      rw [this]
    rw [hinv]
    simp only [bind_tc_ok]
    rw [if_pos trivial]
    exact ⟨_, rfl⟩
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  obtain ⟨s, rfl⟩ := hre
  exact ⟨s, hr⟩

/-- **`Braid.from_bytes_establishes_inv` is not vacuous.** Some byte string reaches `Ok`, and the
state it yields satisfies the leaf `Braid.Inv`, so the implication has a witness rather than an
empty premise. The one hypothesis, `Ct1LenTotal`, is the one `from_bytes_establishes_inv` already
takes. -/
theorem braid_from_bytes_establishes_inv_nonvacuous (hct1 : Tacenta.BraidT1.Ct1LenTotal) :
    ∃ (bytes : Slice Std.U8) (b : Braid),
      Braid.from_bytes bytes = ok (core.result.Result.Ok b) ∧
        Tacenta.ImportInv.Braid.Inv b := by
  obtain ⟨b, hb⟩ := braid_from_bytes_accepts_witness
  exact ⟨braidWitnessBytes, b, hb,
    Tacenta.ImportInv.Braid.from_bytes_establishes_inv hct1 braidWitnessBytes b hb⟩


end Tacenta.BraidFromBytesWitness

/--
info: 'Tacenta.BraidFromBytesWitness.braid_from_bytes_accepts_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
 tacenta_erasure.chunk_count,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.validate_ek,
 tacenta_erasure.Decoder.from_bytes,
 tacenta_erasure.Decoder.invariant,
 tacenta_erasure.Decoder.size,
 tacenta_erasure.Encoder.from_bytes,
 tacenta_erasure.Encoder.invariant,
 tacenta_erasure.Encoder.needed,
 tacenta_kem.EncapsState.from_bytes,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_kem.IncrementalKeyPair.header]
-/
#guard_msgs in
#print axioms Tacenta.BraidFromBytesWitness.braid_from_bytes_accepts_witness

/--
info: Tacenta.BraidFromBytesWitness.braid_from_bytes_accepts_witness :
  ∃ b, Braid.from_bytes Tacenta.BraidFromBytesWitness.braidWitnessBytes = ok (core.result.Result.Ok b)
-/
#guard_msgs in
#check Tacenta.BraidFromBytesWitness.braid_from_bytes_accepts_witness

/--
info: 'Tacenta.BraidFromBytesWitness.braid_from_bytes_establishes_inv_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
 tacenta_erasure.chunk_count,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.validate_ek,
 tacenta_erasure.Decoder.from_bytes,
 tacenta_erasure.Decoder.invariant,
 tacenta_erasure.Decoder.size,
 tacenta_erasure.Encoder.from_bytes,
 tacenta_erasure.Encoder.invariant,
 tacenta_erasure.Encoder.needed,
 tacenta_kem.EncapsState.from_bytes,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_kem.IncrementalKeyPair.header]
-/
#guard_msgs in
#print axioms Tacenta.BraidFromBytesWitness.braid_from_bytes_establishes_inv_nonvacuous

/--
info: Tacenta.BraidFromBytesWitness.braid_from_bytes_establishes_inv_nonvacuous (hct1 : Tacenta.BraidT1.Ct1LenTotal) :
  ∃ bytes b, Braid.from_bytes bytes = ok (core.result.Result.Ok b) ∧ Tacenta.ImportInv.Braid.Inv b
-/
#guard_msgs in
#check Tacenta.BraidFromBytesWitness.braid_from_bytes_establishes_inv_nonvacuous
