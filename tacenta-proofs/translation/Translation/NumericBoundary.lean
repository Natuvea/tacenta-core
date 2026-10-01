import Aeneas

/-!
# The numeric bounds of the refinement and panic-freedom theorems, against the caps they are compared with

Every bound a theorem of this package takes about a length or a counter is written against one of
four constants: `usize::MAX` (`Usize.max`), `u32::MAX`, `u64::MAX`, or a fixed cap of the code
(`MAX_SKIP = 1000`, `MAX_SKIPPED_STORE = 2000`, `EPOCHS_KEPT = 2`, `MAX_CODEWORDS = 65536`, ...).
Only the first depends on the platform: Aeneas defines `Usize.max` as `2^System.Platform.numBits - 1`
and the only fact Lean has about `numBits` is that it is 32 or 64 (`Usize.bounds_eq`). Everything
below is proved for the constant `Usize.max`, by a case split on `both_widths`, so each statement
holds on a 32-bit target and on a 64-bit one, and a bound that holds at 64 bits and not at 32
fails here in the 32-bit case. That is the defect of 2026-09-10, where `receive_no_panic` asked for
`max n MAX_SKIPPED_STORE + u32::MAX ≤ usize::MAX`, which is false for every store at 32 bits.

What is proved:

* the room bounds the theorems take hold for every state size the code's own caps allow, at both
  widths (`classical_store_cap_fits`, `classical_skip_cap_fits`, `spqr_chain_cap_fits`,
  `spqr_skip_cap_fits`, `ratchet_codec_cap_fits`, `spqr_codec_cap_fits`, `erasure_cap_fits`);
* the 32-bit erasure bound `32 * needed < usize::MAX` is exactly `needed ≤ 2^27 - 1`
  (`erasure_room_exact_at_32`), so it is not slack by accident;
* each ceiling that stays a caller's premise excludes exactly one honest value:
  `events + 1 < u32::MAX` excludes `events = u32::MAX - 1` and nothing else among the values the
  decoder's invariant allows, and `epoch + 1 < u64::MAX` excludes `epoch = u64::MAX - 1`
  (`clock_ceiling_excludes_only_parked`, `epoch_ceiling_excludes_only_top`).

The constants' values in each translation, and their agreement with the model's, are in
`NumericBoundaryLeaf.lean`, `NumericBoundaryTriple.lean` and `NumericBoundarySession.lean`; they have
to be stated per translation, because the three environments do not share declarations.

What is not proved: that the Rust constants have these values (the translation makes them
definitions, so the island files evaluate them), or that a real run reaches a given size.
-/

open Aeneas Aeneas.Std

namespace Tacenta.NumericBoundary

theorem both_widths : Usize.max = 4294967295 ∨ Usize.max = 18446744073709551615 := by
  rcases Usize.bounds_eq with h | h <;> simp [h, U32.max_eq, U64.max_eq]

/-! ## Every size a state may legally hold meets its bound, at both widths -/

/-- classical store: `hs` (`max n MAX_SKIPPED_STORE + MAX_SKIP ≤ usize::MAX`), for every store up
to its cap -/
theorem classical_store_cap_fits :
    ∀ n ≤ 2000, max n 2000 + 1000 ≤ Usize.max := by
  intro n hn
  rcases both_widths with h | h <;> rw [h] <;> omega

/-- classical store: the bound of `skip_message_keys`, for every store up to its cap -/
theorem classical_skip_cap_fits : ∀ n ≤ 2000, n + 1000 ≤ Usize.max := by
  intro n hn
  rcases both_widths with h | h <;> rw [h] <;> omega

/-- sparse ratchet: `hroom` of receive and of send, for the at most two chain entries the decoder
invariant allows (`Spqr.inv_gives_chains_len`) -/
theorem spqr_chain_cap_fits : ∀ n ≤ 2, n + 2 < Usize.max := by
  intro n hn
  rcases both_widths with h | h <;> rw [h] <;> omega

/-- sparse ratchet: `hskiproom`, for every skipped store up to its cap -/
theorem spqr_skip_cap_fits : ∀ n ≤ 2000, n + 1000 ≤ Usize.max := by
  intro n hn
  rcases both_widths with h | h <;> rw [h] <;> omega

/-- the persistence codecs' `hroom`, for states within the caps -/
theorem ratchet_codec_cap_fits : ∀ n ≤ 2000, 185 + 72 * n ≤ Usize.max := by
  intro n hn
  rcases both_widths with h | h <;> rw [h] <;> omega

theorem spqr_codec_cap_fits : ∀ c ≤ 2, ∀ k ≤ 2000, 50 + 90 * c + 48 * k ≤ Usize.max := by
  intro c hc k hk
  rcases both_widths with h | h <;> rw [h] <;> omega

/-- the erasure coder's room bounds, for every chunk count its invariant admits -/
theorem erasure_cap_fits :
    ∀ n ≤ 65536, n < Usize.max ∧ 32 * n < Usize.max ∧ 20 + 34 * n ≤ Usize.max ∧
      7 + 32 * n ≤ Usize.max := by
  intro n hn
  rcases both_widths with h | h <;> rw [h] <;> omega

/-- The 32-bit bound is not slack by accident: `32 * needed < usize::MAX` is exactly
`needed ≤ 2^27 - 1` there. -/
theorem erasure_room_exact_at_32 :
    (32 * 134217727 < 4294967295) ∧ ¬ (32 * 134217728 < 4294967295) := by omega

/-! ## What each ceiling excludes, exactly -/

/-- `events + 1 < u32::MAX` against the invariant's `events < u32::MAX`: the one value excluded is
`u32::MAX - 1`, the parked clock (`MAX_EVENTS`). -/
theorem clock_ceiling_excludes_only_parked :
    ∀ e : ℕ, e < U32.max → (¬ (e + 1 < U32.max) ↔ e = U32.max - 1) := by
  intro e he
  simp only [U32.max_eq] at *
  omega

/-- `epoch + 1 < u64::MAX` against `epoch < u64::MAX`: the one value excluded is `u64::MAX - 1`. -/
theorem epoch_ceiling_excludes_only_top :
    ∀ e : ℕ, e < U64.max → (¬ (e + 1 < U64.max) ↔ e = U64.max - 1) := by
  intro e he
  simp only [U64.max_eq] at *
  omega

end Tacenta.NumericBoundary

/--
info: 'Tacenta.NumericBoundary.both_widths' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundary.both_widths

/--
info: 'Tacenta.NumericBoundary.classical_store_cap_fits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundary.classical_store_cap_fits

/--
info: 'Tacenta.NumericBoundary.classical_skip_cap_fits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundary.classical_skip_cap_fits

/--
info: 'Tacenta.NumericBoundary.spqr_chain_cap_fits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundary.spqr_chain_cap_fits

/--
info: 'Tacenta.NumericBoundary.spqr_skip_cap_fits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundary.spqr_skip_cap_fits

/--
info: 'Tacenta.NumericBoundary.ratchet_codec_cap_fits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundary.ratchet_codec_cap_fits

/--
info: 'Tacenta.NumericBoundary.spqr_codec_cap_fits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundary.spqr_codec_cap_fits

/--
info: 'Tacenta.NumericBoundary.erasure_cap_fits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundary.erasure_cap_fits

/--
info: 'Tacenta.NumericBoundary.erasure_room_exact_at_32' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundary.erasure_room_exact_at_32

/--
info: 'Tacenta.NumericBoundary.clock_ceiling_excludes_only_parked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundary.clock_ceiling_excludes_only_parked

/--
info: 'Tacenta.NumericBoundary.epoch_ceiling_excludes_only_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundary.epoch_ceiling_excludes_only_top
