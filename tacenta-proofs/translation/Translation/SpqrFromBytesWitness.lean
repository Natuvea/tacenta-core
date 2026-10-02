import Translation.ImportInv
import Translation.SpqrCodecT1

/-!
# `tacenta_spqr.State.from_bytes` accepts a byte string, so the import theorems are not vacuous

`Spqr.from_bytes_establishes_inv` and `Spqr.decoded_receive_no_panic`
(`Translation/ImportInv.lean`) take as hypothesis that the translated decoder
`tacenta_spqr.State.from_bytes` returned `Ok s`. Before this file no theorem showed that the
sparse ratchet's decoder accepts any byte string, so those theorems were true of a decoder that
refuses every buffer. This file is the witness, in the leaf environment (no Triple or Session
unit), and follows the classical ratchet's `Ratchet.from_bytes_accepts_witness` in
`ImportInv.lean`. No hypothesis about an opaque constant is used on the decode path.

## The byte string

140 bytes, the encoding `State::to_bytes` writes for the smallest state the invariant admits.
In the order of the format (`spqr/src/lib.rs`, `STATE_VERSION`, `FIXED_PREFIX`, `CHAINS_LEN`):

* byte 0: version `1`;
* bytes 1 to 32: `rk`, all zero (the invariant has no clause about `rk`);
* bytes 33 to 40: `epoch`, big-endian zero;
* byte 41: direction `0` (`A2b`);
* bytes 42 to 45: chains count, big-endian `1` (so byte 45 is `1`);
* bytes 46 to 135: one chains entry, ninety zero bytes: epoch `0`, then `send` absent (tag `0`
  and forty zero bytes) and `receive` absent (the same);
* bytes 136 to 139: skipped-key count, big-endian zero, and no skipped entries.

Every byte other than byte 0 and byte 45 is zero. The decoded state has `epoch = 0`, a single
chains entry at epoch `0`, and an empty skipped store, so the invariant's loops run over one
chain and no skipped key. Nothing about the invariant is curve-key shaped in this crate
(there is no canonical-key clause as in the classical ratchet), so no key is constrained.

## The proof

The classical witness's technique, with the byte readers inlined in this translation rather
than behind helper functions: a concrete list literal, `decide` and `rfl` on the concrete
slices and fixed-width reads, and `step*`. Local specifications cover the all-zero padding scan
in `decode_chain`, `decode_chain` on an absent chain, `decode_chains_entry` on a zero entry, the chains loop over a range of one, and the
skipped loop over an empty range. The final `invariant` call is settled by `InvB` from
`ImportInv.lean`, evaluated on the concrete state.
-/

open Aeneas Aeneas.Std Result
open tacenta_spqr

namespace Tacenta.SpqrFromBytesWitness

set_option maxRecDepth 100000

/-- The 140 bytes: the version byte, forty-four zero bytes (`rk`, `epoch`, direction `A2b`, and
the first three bytes of the chains count), a `1` (the chains count is one), and ninety-four
zero bytes (the one chains entry, then a skipped-key count of zero). -/
def spqrWitnessList : List Std.U8 :=
  1#u8 :: (List.replicate 44 0#u8 ++ 1#u8 :: List.replicate 94 0#u8)

theorem spqrWitnessList_length : spqrWitnessList.length = 140 := by simp [spqrWitnessList]

/-- The same bytes, as the `Slice` the translated `from_bytes` takes. -/
def spqrWitnessBytes : Slice Std.U8 :=
  ⟨spqrWitnessList, by rw [spqrWitnessList_length]; scalar_tac⟩

@[local simp] theorem spqrWitnessBytes_val : spqrWitnessBytes.val = spqrWitnessList := rfl
@[local simp] theorem spqrWitnessBytes_length : spqrWitnessBytes.length = 140 := spqrWitnessList_length
@[local simp] theorem spqrWitnessBytes_len : Slice.len spqrWitnessBytes = 140#usize := rfl

theorem wb_zero (k : Nat) (h1 : 1 ≤ k) (h2 : k < 140) (h3 : k ≠ 45) :
    spqrWitnessList[k]? = some 0#u8 := by
  unfold spqrWitnessList
  rcases k with _ | k
  · omega
  · simp only [List.getElem?_cons_succ]
    by_cases hk : k < 44
    · rw [List.getElem?_append_left (by simpa using hk), List.getElem?_replicate]
      simp only [hk, if_true]
    · rw [List.getElem?_append_right (by simpa using (by omega : 44 ≤ k))]
      obtain ⟨m, hm⟩ : ∃ m, k - 44 = m + 1 := ⟨k - 45, by omega⟩
      rw [List.length_replicate, hm, List.getElem?_cons_succ, List.getElem?_replicate]
      have : m < 94 := by omega
      simp only [this, if_true]

theorem wb_zero0 : spqrWitnessList[0]? = some 1#u8 := rfl

open Tacenta.ImportInv (slice_index_eq)
open Tacenta.SpqrCodecT1 (chain_len_eq chains_len_eq skipped_len_eq fixed_prefix_eq)

/-- An absent chain's padding scan over zero bytes leaves `clean` as it was. -/
theorem decode_chain_loop_zeros (bytes : Slice Std.U8) (pos : Std.Usize) (clean : Bool)
    (i : Std.Usize) (hlen : pos.val + 41 ≤ bytes.length) (hi : i.val ≤ pos.val + 41)
    (hz : ∀ k, i.val ≤ k → k < pos.val + 41 → bytes.val[k]? = some 0#u8) :
    decode_chain_loop 41#usize bytes pos clean i ⦃ fun r => r = clean ⦄ := by
  unfold decode_chain_loop
  apply loop.spec_decr_nat
    (measure := fun p => pos.val + 41 - p.2.val)
    (inv := fun p => p.2.val ≤ pos.val + 41 ∧ p.1 = clean ∧ ∀ k, p.2.val ≤ k → k < pos.val + 41 → bytes.val[k]? = some 0#u8)
  · rintro ⟨c, j⟩ ⟨hj, hc, hzj⟩
    unfold decode_chain_loop.body
    simp only at hj hc hzj ⊢
    step*
    have h0 : bytes.val[j.val]? = some 0#u8 := hzj j.val (le_refl _) (by scalar_tac)
    obtain ⟨hlt, h2⟩ := List.getElem?_eq_some_iff.mp h0
    have hi3 : i3 = 0#u8 := by rw [i3_post]; exact h2
    subst hi3
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_tc_ok]
    step*
    refine ⟨by scalar_tac, hc, ?_, by scalar_tac⟩
    intro k hk1 hk2
    exact hzj k (by scalar_tac) hk2
  · exact ⟨hi, rfl, hz⟩

theorem decode_chain_absent (bytes : Slice Std.U8) (pos : Std.Usize)
    (hlen : pos.val + 41 ≤ bytes.length) (h0 : bytes.val[pos.val]? = some 0#u8)
    (hz : ∀ k, pos.val < k → k < pos.val + 41 → bytes.val[k]? = some 0#u8) :
    decode_chain bytes pos ⦃ fun r => r = some none ⦄ := by
  unfold decode_chain
  simp only [chain_len_eq, bind_tc_ok]
  have hlt : ¬ (bytes.val.length < pos.val + 41) := by scalar_tac
  rw [slice_index_eq bytes pos 0#u8 h0]
  simp only [bind_tc_ok]
  step as ⟨i2, hi2⟩
  rw [if_neg (by simp [Slice.len]; scalar_tac)]
  show (do
    let i4 ← pos + 1#usize
    let clean ← decode_chain_loop 41#usize bytes pos true i4
    if clean = true then ok (some none) else ok none) ⦃ _ ⦄
  step as ⟨i4, hi4⟩
  have hloop := decode_chain_loop_zeros bytes pos true i4 hlen (by scalar_tac)
    (by intro k hk1 hk2; exact hz k (by scalar_tac) hk2)
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists hloop
  rw [hr]
  simp only [bind_tc_ok]
  rw [hre]
  simp

attribute [local step] decode_chain_absent

theorem slice_zeros (l : List Std.U8) (i j : Nat) (hj : j ≤ l.length)
    (hz : ∀ k, i ≤ k → k < j → l[k]? = some 0#u8) :
    l.slice i j = List.replicate (j - i) 0#u8 := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < j - i
  · rw [List.getElem?_slice _ _ _ _ ⟨hj, by omega⟩, List.getElem?_replicate]
    simp only [hk, if_true]
    exact hz (i + k) (by omega) (by omega)
  · rw [List.getElem?_replicate]
    simp only [hk, if_false]
    apply List.getElem?_eq_none
    rw [List.slice_length]
    omega

theorem from_slice_zeros {N : Std.Usize} (s : Slice Std.U8) (hs : s.val = List.replicate N.val 0#u8) :
    (Std.Array.repeat N 0#u8).from_slice s = Std.Array.repeat N 0#u8 := by
  apply Subtype.ext
  rw [Std.Array.from_slice_val _ _ (by rw [hs]; simp)]
  rw [hs]; rfl

theorem decode_chains_entry_zeros (bytes : Slice Std.U8) (pos : Std.Usize)
    (hlen : pos.val + 90 ≤ bytes.length)
    (hz : ∀ k, pos.val ≤ k → k < pos.val + 90 → bytes.val[k]? = some 0#u8) :
    decode_chains_entry bytes pos ⦃ fun r =>
      r = some (0#u64, { send := none, receive := none }) ⦄ := by
  unfold decode_chains_entry
  simp only [chain_len_eq, bind_tc_ok]
  step*
  · have hl : s.length = 8 := by simp [Slice.length, s_post1, Std.Array.repeat]
    omega
  · have hov : o = some v := by assumption
    have hv1 : o1 = some v1 := by assumption
    rw [o_post] at hov
    rw [o1_post] at hv1
    simp only [Option.some.injEq] at hov hv1
    subst hov; subst hv1
    have hs1 : s1.val = List.replicate 8 0#u8 := by
      rw [s1_post1, i1_post]
      rw [slice_zeros _ _ _ (by scalar_tac) (fun k hk1 hk2 => hz k (by scalar_tac) (by scalar_tac))]
      congr 1; scalar_tac
    have h5 : to_slice_mut_back s2 = Std.Array.repeat 8#usize 0#u8 := by
      rw [s_post2, s2_post]; exact from_slice_zeros s1 hs1
    have hi4 : i4 = 0#u64 := by
      rw [h5] at i4_post
      apply U64.bv_eq_imp_eq
      exact i4_post.trans (by rfl)
    rw [hi4]

theorem direction_from_byte_zero : Direction.from_byte 0#u8 = ok (some Direction.A2b) := rfl

theorem decode_entry_wit :
    decode_chains_entry spqrWitnessBytes 46#usize
      = ok (some (0#u64, { send := none, receive := none })) := by
  have h := decode_chains_entry_zeros spqrWitnessBytes 46#usize (by simp; decide)
    (fun k hk1 hk2 => by
      simp only [spqrWitnessBytes_val]
      exact wb_zero k (by simp at hk1; omega) (by simp at hk2; omega) (by simp at hk1; omega))
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  rw [hr, hre]

theorem from_bytes_loop0_one (chains : alloc.vec.Vec (Std.U64 × Chains))
    (hc : chains.val.length + 1 ≤ Std.Usize.max) :
    State.from_bytes_loop0 90#usize { start := 0#usize, «end» := 1#usize } spqrWitnessBytes 46#usize
      chains true ⦃ fun r => r.1 = 136#usize ∧ r.2.2 = true ∧
        r.2.1.val = chains.val ++ [(0#u64, { send := none, receive := none })] ⦄ := by
  unfold State.from_bytes_loop0
  apply loop.spec_decr_nat
    (measure := fun p => p.1.end.val - p.1.start.val)
    (inv := fun p => p.1.end = 1#usize ∧
      ((p.1.start = 0#usize ∧ p.2.1 = 46#usize ∧ p.2.2.1 = chains ∧ p.2.2.2 = true) ∨
       (p.1.start = 1#usize ∧ p.2.1 = 136#usize ∧
          p.2.2.1.val = chains.val ++ [(0#u64, { send := none, receive := none })] ∧
          p.2.2.2 = true)))
  · rintro ⟨⟨st, en⟩, pos', cs', b'⟩ ⟨hen, h1 | h1⟩
    · simp only at hen h1 ⊢
      obtain ⟨hst, hpos, hcs, hb⟩ := h1
      rw [hst, hpos, hcs, hb, hen]
      unfold State.from_bytes_loop0.body
      step*
      rw [decode_entry_wit]
      simp only [bind_tc_ok]
      step*
    · simp only at hen h1 ⊢
      obtain ⟨hst, hpos, h2, hb⟩ := h1
      rw [hst, hpos, hb, hen]
      unfold State.from_bytes_loop0.body
      step*
  · exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩

theorem from_bytes_loop1_empty (i : Std.Usize) (bytes : Slice Std.U8)
    (pos : Std.Usize) (v : alloc.vec.Vec Skipped) (b : Bool) :
    State.from_bytes_loop1 i { start := 0#usize, «end» := 0#usize } bytes pos v b
      ⦃ fun r => r = (pos, v, b) ⦄ := by
  unfold State.from_bytes_loop1
  apply loop.spec_decr_nat
    (measure := fun _ => 0)
    (inv := fun p => p.1.end.val ≤ p.1.start.val ∧ p.2 = (pos, v, b))
  · rintro ⟨⟨st, en⟩, pos', v', b'⟩ ⟨h1, h2⟩
    simp only at h1 h2
    simp only [State.from_bytes_loop1.body]
    step*
  · exact ⟨by simp, rfl⟩

theorem sat_zero : (core.num.U64.saturating_add 0#u64 EPOCHS_KEPT).val = 2 := by
  unfold EPOCHS_KEPT
  simp only [core.num.U64.saturating_add, UScalar.saturating_add]
  simp [UScalar.val, Std.U64.max_eq]

theorem invB_wit (rk : Std.Array Std.U8 32#usize) (d : Direction)
    (chains1 : alloc.vec.Vec (Std.U64 × Chains))
    (h3 : chains1.val = [(0#u64, { send := none, receive := none })])
    (skipped1 : alloc.vec.Vec Skipped) (hs : skipped1.val = []) :
    Tacenta.ImportInv.Spqr.InvB
      { rk := rk, epoch := 0#u64, chains := chains1, skipped := skipped1, direction := d } = true := by
  simp [Tacenta.ImportInv.Spqr.InvB, Tacenta.ImportInv.Spqr.chainsOkFrom,
    Tacenta.ImportInv.Spqr.skippedOkFrom, Tacenta.ImportInv.Spqr.isEpoch, h3, hs, sat_zero]

attribute [local step] from_bytes_loop1_empty

/-- **The translated sparse-ratchet `from_bytes` accepts `spqrWitnessBytes`.** -/
theorem spqr_from_bytes_accepts_witness :
    ∃ s, State.from_bytes spqrWitnessBytes = ok (core.result.Result.Ok s) := by
  have h : State.from_bytes spqrWitnessBytes
      ⦃ fun r => ∃ s, r = core.result.Result.Ok s ⦄ := by
    unfold State.from_bytes
    simp only [fixed_prefix_eq, chains_len_eq, skipped_len_eq, bind_tc_ok]
    rw [if_neg (by decide), slice_index_eq spqrWitnessBytes 0#usize 1#u8 wb_zero0]
    simp only [bind_tc_ok]
    rw [if_neg (by simp [STATE_VERSION])]
    step*
    · simp only [spqrWitnessBytes_length]; omega
    · simp [Slice.length, Std.Array.repeat, List.slice_length, spqrWitnessList_length, *]
    · simp only [spqrWitnessBytes_length]; omega
    · simp [Slice.length, Std.Array.repeat, List.slice_length, spqrWitnessList_length, *]
    · simp only [spqrWitnessBytes_length]; omega
    have hi4 : i4 = 41#usize := by scalar_tac
    have hi3 : i3 = 33#usize := by scalar_tac
    have hbd : i4.val < spqrWitnessBytes.val.length := by
      simp only [spqrWitnessBytes_val, spqrWitnessList_length]; scalar_tac
    have hi5 : i5 = 0#u8 := by
      have hq : spqrWitnessBytes.val[i4.val]? = some 0#u8 := by
        rw [hi4]; exact wb_zero 41 (by omega) (by omega) (by omega)
      rw [List.getElem?_eq_getElem hbd] at hq
      rw [i5_post]; exact Option.some.inj hq
    have hep : epoch = 0#u64 := by
      have hi3v : i3.val = 33 := by scalar_tac
      have hi4v : i4.val = 41 := by scalar_tac
      have hs4 : s4.val = List.replicate 8 0#u8 := by
        rw [s4_post1, hi3v, hi4v]; decide
      have h5 : to_slice_mut_back1 s5 = Std.Array.repeat 8#usize 0#u8 := by
        rw [s3_post2, s5_post]; exact from_slice_zeros s4 hs4
      rw [h5] at epoch_post
      apply U64.bv_eq_imp_eq
      exact epoch_post.trans (by rfl)
    rw [hi5, direction_from_byte_zero]
    simp only [bind_tc_ok]
    step*
    · simp only [spqrWitnessBytes_length]; scalar_tac
    · simp [Slice.length, Std.Array.repeat, List.slice_length, spqrWitnessList_length, *]
    all_goals
      have hpos : pos.val = 42 := by scalar_tac
      have hi6 : i6.val = 46 := by scalar_tac
      have hs7 : s7.val = [0#u8, 0#u8, 0#u8, 1#u8] := by
        rw [s7_post1, hpos, hi6]; decide
      have hi7 : i7 = 1#u32 := by
        have hb : (to_slice_mut_back2 s8).val = [0#u8, 0#u8, 0#u8, 1#u8] := by
          rw [s6_post2, s8_post, Std.Array.from_slice_val _ _ (by rw [hs7]; rfl)]
          exact hs7
        have hbarr : to_slice_mut_back2 s8
            = (⟨[0#u8, 0#u8, 0#u8, 1#u8], by simp⟩ : Std.Array Std.U8 4#usize) := Subtype.ext hb
        rw [hbarr] at i7_post
        apply U32.bv_eq_imp_eq
        exact i7_post.trans (by rfl)
      have hcc : chains_count = 1#usize := by
        rw [chains_count_post, hi7]; scalar_tac
    · exfalso
      rename_i hgt
      rw [hcc] at hgt
      simp only [spqrWitnessBytes_len] at i10_post
      scalar_tac
    · have hloop := from_bytes_loop0_one (alloc.vec.Vec.with_capacity (Std.U64 × Chains) 1#usize)
        (by simp [alloc.vec.Vec.with_capacity]; scalar_tac)
      have hi6' : i6 = 46#usize := by scalar_tac
      rw [hcc, hi6']
      obtain ⟨⟨pos1, chains1, cok⟩, hr, h1, h2, h3⟩ := Std.WP.spec_imp_exists hloop
      simp only at h1 h2 h3
      rw [hr]
      simp only [bind_tc_ok]
      obtain rfl : pos1 = 136#usize := h1
      obtain rfl : cok = true := h2
      have hcap : (alloc.vec.Vec.with_capacity (Std.U64 × Chains) 1#usize).val = [] := rfl
      rw [hcap, List.nil_append] at h3
      step*
      · exfalso
        rename_i hlt
        simp only [spqrWitnessBytes_len] at hlt
        scalar_tac
      · simp [Slice.length, Std.Array.repeat, List.slice_length, spqrWitnessList_length, *]
      all_goals
        have hi12 : i12.val = 140 := by scalar_tac
        have hs10 : s10.val = List.replicate 4 0#u8 := by
          rw [s10_post1, hi12]; decide
        have hi13 : i13 = 0#u32 := by
          have h5 : to_slice_mut_back3 s11 = Std.Array.repeat 4#usize 0#u8 := by
            rw [s9_post2, s11_post]; exact from_slice_zeros s10 hs10
          rw [h5] at i13_post
          apply U32.bv_eq_imp_eq
          exact i13_post.trans (by rfl)
        have hsc : skipped_count = 0#usize := by
          rw [skipped_count_post, hi13]; scalar_tac
      · exfalso
        rename_i hgt
        rw [hsc] at hgt
        simp only [spqrWitnessBytes_len] at i16_post
        scalar_tac
      · have hi12' : i12 = 140#usize := by scalar_tac
        rw [hsc, hi12']
        step*
        · exfalso
          simp only [Prod.mk.injEq] at pos2_post
          obtain ⟨hp, -, -⟩ := pos2_post
          rename_i hne
          rw [hp] at hne
          simp [spqrWitnessBytes_len] at hne
        · simp only [Prod.mk.injEq] at pos2_post
          obtain ⟨-, hsk, -⟩ := pos2_post
          subst hsk
          rw [hep, Tacenta.ImportInv.Spqr.invariant_eq,
            invB_wit (to_slice_mut_back s2) Direction.A2b chains1 h3 _ rfl]
          simp
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  obtain ⟨s, rfl⟩ := hre
  exact ⟨s, hr⟩

/-- **`Spqr.from_bytes_establishes_inv` is not vacuous.** Some byte string reaches `Ok`, and the
state it yields satisfies `Inv`, so the implication has a witness rather than an empty premise. -/
theorem spqr_from_bytes_establishes_inv_nonvacuous :
    ∃ (bytes : Slice Std.U8) (s : State),
      State.from_bytes bytes = ok (core.result.Result.Ok s) ∧ Tacenta.ImportInv.Spqr.Inv s := by
  obtain ⟨s, hs⟩ := spqr_from_bytes_accepts_witness
  exact ⟨spqrWitnessBytes, s, hs,
    Tacenta.ImportInv.Spqr.from_bytes_establishes_inv spqrWitnessBytes s hs⟩


end Tacenta.SpqrFromBytesWitness

/--
info: 'Tacenta.SpqrFromBytesWitness.spqr_from_bytes_accepts_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SpqrFromBytesWitness.spqr_from_bytes_accepts_witness

/--
info: Tacenta.SpqrFromBytesWitness.spqr_from_bytes_accepts_witness :
  ∃ s, State.from_bytes Tacenta.SpqrFromBytesWitness.spqrWitnessBytes = ok (core.result.Result.Ok s)
-/
#guard_msgs in
#check Tacenta.SpqrFromBytesWitness.spqr_from_bytes_accepts_witness

/--
info: 'Tacenta.SpqrFromBytesWitness.spqr_from_bytes_establishes_inv_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SpqrFromBytesWitness.spqr_from_bytes_establishes_inv_nonvacuous

/--
info: Tacenta.SpqrFromBytesWitness.spqr_from_bytes_establishes_inv_nonvacuous :
  ∃ bytes s, State.from_bytes bytes = ok (core.result.Result.Ok s) ∧ Tacenta.ImportInv.Spqr.Inv s
-/
#guard_msgs in
#check Tacenta.SpqrFromBytesWitness.spqr_from_bytes_establishes_inv_nonvacuous
