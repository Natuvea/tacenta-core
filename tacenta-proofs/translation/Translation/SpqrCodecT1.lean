import Translation.ImportInv
import Translation.SessionT1

/-!
# T1 for the sparse post-quantum ratchet's persistence codec: decoding stored state cannot fail

`tacenta-spqr`'s `State::from_bytes` parses what a storage layer wrote and hands
back a state the sparse ratchet then runs on. `Translation/ImportInv.lean`
proves what a state it returns satisfies; this file proves the decoder returns:
every byte string decodes to an `Ok` or an `Err`.

## The one precondition

`bytes.length + 90 ≤ Usize.max`, for the reason `RatchetCodecT1.lean` gives: the
chains loop computes where the next 90-byte entry would end before it checks
that end against the input, and Aeneas models a slice as anything up to
`Usize.max` long. No Rust slice is within 90 bytes of that ceiling.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.SpqrCodecT1

open tacenta_spqr
open Tacenta.ImportInv (slice_index_eq)
open Tacenta.ImportInv.Spqr (invariant_eq inv_gives_chains_len)

/-! ## The layout's widths, as the values they compute to -/

theorem chain_len_eq : CHAIN_LEN = ok 41#usize := by
  have h : CHAIN_LEN ⦃ fun r => r = 41#usize ⦄ := by
    unfold CHAIN_LEN; step*
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

theorem chains_len_eq : CHAINS_LEN = ok 90#usize := by
  have h : CHAINS_LEN ⦃ fun r => r = 90#usize ⦄ := by
    unfold CHAINS_LEN; simp only [chain_len_eq, bind_tc_ok]; step*
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

theorem skipped_len_eq : SKIPPED_LEN = ok 48#usize := by
  have h : SKIPPED_LEN ⦃ fun r => r = 48#usize ⦄ := by
    unfold SKIPPED_LEN; step*
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

theorem fixed_prefix_eq : FIXED_PREFIX = ok 46#usize := by
  have h : FIXED_PREFIX ⦃ fun r => r = 46#usize ⦄ := by
    unfold FIXED_PREFIX; step*
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

/-! ## Entries -/

/-- An absent chain's padding scan cannot fail over its forty bytes. -/
@[local step]
theorem decode_chain_loop_no_panic (bytes : Slice U8) (pos : Usize) (clean : Bool) (i : Usize)
    (h : pos.val + 41 ≤ bytes.length) (hi : i.val ≤ pos.val + 41) :
    decode_chain_loop 41#usize bytes pos clean i ⦃ fun _ => True ⦄ := by
  unfold decode_chain_loop
  apply loop.spec_decr_nat
    (measure := fun p => pos.val + 41 - p.2.val)
    (inv := fun p => p.2.val ≤ pos.val + 41)
  · rintro ⟨c, j⟩ hj
    unfold decode_chain_loop.body
    simp only at hj ⊢
    step*
    all_goals (try (split <;> step*))
  · exact hi

/-- One chain at `pos` cannot fail to decode, and decodes only when its
forty-one bytes are inside the input. -/
@[local step]
theorem decode_chain_spec (bytes : Slice U8) (pos : Usize) (h : pos.val + 41 ≤ Usize.max) :
    decode_chain bytes pos ⦃ fun o => match o with
      | some _ => pos.val + 41 ≤ bytes.length
      | none => True ⦄ := by
  unfold decode_chain
  simp only [chain_len_eq, bind_tc_ok]
  by_cases hlt : bytes.val.length < pos.val + 41
  · step*
  · have hi : pos.val < bytes.val.length := by omega
    rw [slice_index_eq bytes pos _ (List.getElem?_eq_getElem hi)]
    simp only [bind_tc_ok]
    all_goals repeat' (first | simp only [WP.spec_ok] | step | split)
    all_goals (try simp_all [Slice.length, Array.repeat])

/-- One chains entry at `pos` -- its epoch and two chains -- cannot fail to
decode, and decodes only when its ninety bytes are inside the input. -/
@[local step]
theorem decode_chains_entry_spec (bytes : Slice U8) (pos : Usize) (h : pos.val + 90 ≤ Usize.max) :
    decode_chains_entry bytes pos ⦃ fun o => match o with
      | some _ => pos.val + 90 ≤ bytes.length
      | none => True ⦄ := by
  unfold decode_chains_entry
  simp only [chain_len_eq, bind_tc_ok]
  step*
  all_goals (try simp_all [Slice.length, Array.repeat])

/-- One skipped entry at `pos` cannot fail to decode, and decodes only when its
forty-eight bytes are inside the input. -/
@[local step]
theorem decode_skipped_entry_spec (bytes : Slice U8) (pos : Usize) (h : pos.val + 48 ≤ Usize.max) :
    decode_skipped_entry bytes pos ⦃ fun o => match o with
      | some _ => pos.val + 48 ≤ bytes.length
      | none => True ⦄ := by
  unfold decode_skipped_entry
  simp only [skipped_len_eq, bind_tc_ok]
  step*
  all_goals (try simp_all [Slice.length, Array.repeat])

/-! ## The two loops -/

@[local step]
theorem from_bytes_loop0_no_panic (bytes : Slice U8) (iter : core.ops.range.Range Usize) (pos : Usize)
    (chains : alloc.vec.Vec (U64 × Chains)) (ok1 : Bool)
    (hroom : bytes.length + 90 ≤ Usize.max) (hpos : pos.val ≤ bytes.length)
    (hlen : chains.val.length + (iter.end.val - iter.start.val) ≤ Usize.max) :
    State.from_bytes_loop0 90#usize iter bytes pos chains ok1 ⦃ fun r => r.1.val ≤ bytes.length ⦄ := by
  unfold State.from_bytes_loop0
  apply loop.spec_decr_nat
    (measure := fun x => x.1.end.val - x.1.start.val)
    (inv := fun x => x.2.1.val ≤ bytes.length ∧
      x.2.2.1.val.length + (x.1.end.val - x.1.start.val) ≤ Usize.max)
  · rintro ⟨it, p, cs, b⟩ ⟨hp, hl⟩
    simp only at hp hl ⊢
    unfold State.from_bytes_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step*
      all_goals (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩)
    · step*
  · exact ⟨hpos, hlen⟩

@[local step]
theorem from_bytes_loop1_no_panic (bytes : Slice U8) (iter : core.ops.range.Range Usize) (pos : Usize)
    (skipped : alloc.vec.Vec Skipped) (ok1 : Bool)
    (hroom : bytes.length + 48 ≤ Usize.max) (hpos : pos.val ≤ bytes.length)
    (hlen : skipped.val.length + (iter.end.val - iter.start.val) ≤ Usize.max) :
    State.from_bytes_loop1 48#usize iter bytes pos skipped ok1 ⦃ fun _ => True ⦄ := by
  unfold State.from_bytes_loop1
  apply loop.spec_decr_nat
    (measure := fun x => x.1.end.val - x.1.start.val)
    (inv := fun x => x.2.1.val ≤ bytes.length ∧
      x.2.2.1.val.length + (x.1.end.val - x.1.start.val) ≤ Usize.max)
  · rintro ⟨it, p, sk, b⟩ ⟨hp, hl⟩
    simp only at hp hl ⊢
    unfold State.from_bytes_loop1.body
    by_cases hlt : it.start.val < it.end.val
    · step*
      all_goals (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩)
    · step*
  · exact ⟨hpos, hlen⟩


/-! ## The decoder -/

theorem direction_from_byte_eq (b : U8) :
    ∃ o, Direction.from_byte b = ok o ∧
      (o = none ∨ o = some Direction.A2b ∨ o = some Direction.B2a) := by
  unfold Direction.from_byte
  split <;> simp

/-- Reading the direction cannot fail. Stated with its outcomes named, so the
decoder's `match` on it splits. -/
@[local step]
theorem direction_from_byte_spec (b : U8) :
    Direction.from_byte b ⦃ fun o =>
      o = none ∨ o = some Direction.A2b ∨ o = some Direction.B2a ⦄ := by
  obtain ⟨o, h, ho⟩ := direction_from_byte_eq b
  rw [h]
  simpa using ho

/-- The final check cannot fail: `invariant` computes `InvB`. -/
@[local step]
theorem invariant_no_panic (s : State) : State.invariant s ⦃ fun _ => True ⦄ := by
  rw [invariant_eq]
  simp

/-- **Decoding stored state cannot fail, for every byte string** a Rust slice
can hold. -/
theorem from_bytes_no_panic (bytes : Slice U8) (hroom : bytes.length + 90 ≤ Usize.max) :
    State.from_bytes bytes ⦃ fun _ => True ⦄ := by
  unfold State.from_bytes
  simp only [fixed_prefix_eq, chains_len_eq, skipped_len_eq, bind_tc_ok]
  all_goals repeat' (first | simp only [WP.spec_ok] | step | split)
  all_goals (try simp_all [Slice.length, Array.repeat])


/-! ## Encoding

`State::to_bytes` sizes its buffer with `encoded_len` and ends by asserting the
buffer came out that long, so its panic-freedom is a length statement: every
write adds exactly what `encoded_len` counted. -/

/-- The `zeroize` crate's wrapper returns on a byte vector: the same assumption
as `RatchetCodecT1.ZeroizingVecTotal`, at this crate's copy of the type. -/
def ZeroizingVecTotal : Prop :=
  ∀ (inst : zeroize.Zeroize (alloc.vec.Vec U8)) (v : alloc.vec.Vec U8),
    ∃ z, zeroize.Zeroizing.new inst v = ok z

theorem zeroizing_vec_new_no_panic (hz : ZeroizingVecTotal)
    (inst : zeroize.Zeroize (alloc.vec.Vec U8)) (v : alloc.vec.Vec U8) :
    zeroize.Zeroizing.new inst v ⦃ fun _ => True ⦄ := by
  obtain ⟨z, h⟩ := hz inst v
  rw [h]
  simp

theorem direction_to_byte_ok (d : Direction) : ∃ b, Direction.to_byte d = ok b := by
  cases d <;> exact ⟨_, rfl⟩

@[local step]
theorem direction_to_byte_no_panic (d : Direction) : Direction.to_byte d ⦃ fun _ => True ⦄ := by
  obtain ⟨b, h⟩ := direction_to_byte_ok d
  rw [h]
  simp

/-- An optional chain appends forty-one bytes. -/
@[local step]
theorem push_optional_chain_spec (out : alloc.vec.Vec U8) (chain : Option Chain)
    (h : out.val.length + 41 ≤ Usize.max) :
    push_optional_chain out chain ⦃ fun w => w.val.length = out.val.length + 41 ⦄ := by
  unfold push_optional_chain
  rcases hc : chain with _ | c <;> simp only [] <;> step*
  all_goals (try simp_all [Array.to_slice, Array.repeat])
  all_goals scalar_tac

/-- The chains loop appends ninety bytes per entry still to write. -/
@[local step]
theorem to_bytes_loop0_spec (v : alloc.vec.Vec (U64 × Chains)) (out : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ v.val.length) (h : out.val.length + 90 * (v.val.length - i.val) ≤ Usize.max) :
    State.to_bytes_loop0 v out i
      ⦃ fun w => w.val.length = out.val.length + 90 * (v.val.length - i.val) ⦄ := by
  unfold State.to_bytes_loop0
  apply loop.spec_decr_nat
    (measure := fun p => v.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ v.val.length ∧
      p.1.val.length + 90 * (v.val.length - p.2.val) = out.val.length + 90 * (v.val.length - i.val))
  · rintro ⟨o, j⟩ ⟨hj, heq⟩
    simp only at hj heq ⊢
    unfold State.to_bytes_loop0.body
    step*
    all_goals (try simp_all [Array.to_slice])
    all_goals first | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩) | scalar_tac
  · exact ⟨hi, rfl⟩

/-- The skipped loop appends forty-eight bytes per key still to write. -/
@[local step]
theorem to_bytes_loop1_spec (v : alloc.vec.Vec Skipped) (out : alloc.vec.Vec U8) (j : Usize)
    (hj : j.val ≤ v.val.length) (h : out.val.length + 48 * (v.val.length - j.val) ≤ Usize.max) :
    State.to_bytes_loop1 v out j
      ⦃ fun w => w.val.length = out.val.length + 48 * (v.val.length - j.val) ⦄ := by
  unfold State.to_bytes_loop1
  apply loop.spec_decr_nat
    (measure := fun p => v.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ v.val.length ∧
      p.1.val.length + 48 * (v.val.length - p.2.val) = out.val.length + 48 * (v.val.length - j.val))
  · rintro ⟨o, k⟩ ⟨hk, heq⟩
    simp only at hk heq ⊢
    unfold State.to_bytes_loop1.body
    step*
    all_goals (try simp_all [Array.to_slice])
    all_goals first | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩) | scalar_tac
  · exact ⟨hj, rfl⟩

/-- `encoded_len` counts the prefix, the two counts and every entry. -/
@[local step]
theorem encoded_len_spec (s : State)
    (h : 50 + 90 * s.chains.val.length + 48 * s.skipped.val.length ≤ Usize.max) :
    State.encoded_len s
      ⦃ fun r => r.val = 50 + 90 * s.chains.val.length + 48 * s.skipped.val.length ⦄ := by
  unfold State.encoded_len
  simp only [chains_len_eq, fixed_prefix_eq, skipped_len_eq, bind_tc_ok]
  step*

/-- **Encoding a state cannot fail** when its buffer fits a `usize`, given that
the `zeroize` wrapper returns. -/
theorem to_bytes_no_panic (hz : ZeroizingVecTotal) (s : State)
    (hroom : 50 + 90 * s.chains.val.length + 48 * s.skipped.val.length ≤ Usize.max) :
    State.to_bytes s ⦃ fun _ => True ⦄ := by
  unfold State.to_bytes
  simp only [alloc.vec.Vec.with_capacity]
  step*
  all_goals first | exact zeroizing_vec_new_no_panic hz _ _ | skip
  all_goals (try simp_all [Array.to_slice])
  all_goals scalar_tac

/-- The encoder's precondition holds of every state satisfying `Inv`: at most
two chains entries (`ImportInv`'s `inv_gives_chains_len`) and `MAX_SKIPPED_STORE`
(2000) skipped keys make a buffer of
at most 96,230 bytes, which fits a `usize` on either target Aeneas models. So
every state `from_bytes` returns can be written back. -/
theorem to_bytes_no_panic_of_inv (hz : ZeroizingVecTotal) (s : State)
    (hinv : Tacenta.ImportInv.Spqr.Inv s) :
    State.to_bytes s ⦃ fun _ => True ⦄ := by
  apply to_bytes_no_panic hz s
  have hc := inv_gives_chains_len s hinv
  have hb := hinv.store_bound
  have h := Std.Usize.bounds_eq
  simp only [MAX_SKIPPED_STORE] at hb
  rcases h with h | h <;> simp [h] <;> scalar_tac

-- The axiom audit, enforced rather than asserted. The decoder rests on the
-- kernel's three axioms and nothing else. The encoder's base adds the `zeroize`
-- crate's declarations the translation cannot see inside, which
-- `ZeroizingVecTotal` is the hypothesis about. A proof that starts trusting
-- something new fails here.
/-- info: 'Tacenta.SpqrCodecT1.from_bytes_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.SpqrCodecT1.from_bytes_no_panic

/--
info: 'Tacenta.SpqrCodecT1.to_bytes_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 zeroize.Zeroize.Blanket.zeroize,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.SpqrCodecT1.to_bytes_no_panic

/--
info: 'Tacenta.SpqrCodecT1.to_bytes_no_panic_of_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 zeroize.Zeroize.Blanket.zeroize,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.SpqrCodecT1.to_bytes_no_panic_of_inv

end Tacenta.SpqrCodecT1
