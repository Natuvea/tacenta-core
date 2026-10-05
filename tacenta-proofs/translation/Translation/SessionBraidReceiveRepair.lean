import Translation.UnitLifecyclePublicT1
import Translation.SessionBraidReceiveVacuity

/-!
# The repaired decoder hypothesis is not touched by the old refutation

`SessionBraidReceiveVacuity.lean` shows that `Decoder::message` fails for a decoder that needs and
holds `K = (Usize.max + 1) / 32` chunks, so the statement "it returns for every decoder" is false.  The
repair states the field for decoders with `needed <= 65536`
(`SessionUnitBraidT1.DecoderMessageTotal`) and supplies that bound from the state.  This file shows,
in Lean, what the repair does and does not buy.

1. The decoder of the old refutation needs `K` chunks, and `K` is more than 65536 on either
   platform width, so the new premise excludes it (`old_witness_fails_bounded_premise`).
2. The translated `Decoder::invariant` rejects it too (`old_witness_rejected_by_invariant`), which is
   the reason the premise is one a Braid that passed its invariant meets.
3. Given only the law "`Vec::truncate` returns" (`TruncateTotal`), the repaired field is true and
   the unbounded one is false (`bounded_holds_unbounded_fails`).  Together with the absence of
   the old argument against the repaired field this is what makes the repaired field a statement that
   can be met; it does not show that the whole record `BraidReceiveContracts` can be
   (`UnitSatisfiabilityRecords.lean` shows that, in the sense recorded in `LIMITATIONS.md`;
   `GAP-REGISTER.md`, row `SESSION-CONTRACT-VACUITY`).
4. Under the same law every decoder that passes the translated `Decoder::invariant` has a
   returning `Decoder::message` (`message_total_of_invariant`).
5. The line between true and false is `K`: the field holds for `needed < K` and fails at
   `needed = K` (`boundary_exact`).  A premise raised to `K` is refuted
   (`mutant_premise_at_boundary_refuted`), so the bound cannot be raised to the line, and the
   chosen bound sits well below it.
6. The new law `DivCeilValue` has a model on the shape of the operation
   (`divCeilValue_shape_satisfiable`).  This is consistency of the statement, not a model of the
   unit's own `div_ceil`.

Nothing here assumes a property of an opaque operation except where a hypothesis says so, and the
hypotheses are named.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit.tacenta_erasure
open Tacenta.SessionBraidReceiveVacuity (message_OF_false usize_max_facts)
open Tacenta.SessionUnitErasureT1 (TruncateTotal noPanic_iff)

namespace Tacenta.SessionBraidReceiveRepair

/-! ## A. The decoder of the old refutation -/

/-- The decoder of the old refutation, as a statement: it needs `K = (Usize.max + 1) / 32`
chunks (so `32 * needed = Usize.max + 1`) and `Decoder::message` cannot return a value on it. -/
theorem old_witness : ∃ d : Decoder, d.size.val ≤ 4128 ∧
    32 * d.needed.val = Usize.max + 1 ∧
    ¬ ∃ r, Decoder.message d = ok r := by
  obtain ⟨K, hK32, hKlt⟩ := usize_max_facts
  have hKb : K < 2 ^ UScalarTy.Usize.numBits := by
    have : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
      scalar_tac
    omega
  let needed : Usize := Usize.ofNatCore K hKb
  let c : Chunk := ⟨0#u16, Array.repeat 32#usize 0#u8⟩
  let hv : alloc.vec.Vec Chunk := ⟨List.replicate K c, by simp; omega⟩
  let d : Decoder := ⟨0#usize, needed, hv⟩
  have hneed : d.needed.val = K := Usize.ofNatCore_val_eq hKb
  refine ⟨d, by simp [d], by omega, ?_⟩
  rintro ⟨r, hr⟩
  have hh : d.needed.val ≤ d.«have».val.length := by
    simp [d, hv, hneed]
  rcases message_OF_false d hh (by omega) (by omega) with ⟨e, he⟩ | ⟨r', hr', hf⟩
  · rw [he] at hr; cases hr
  · exact hf

/-- `K` is more than `MAX_CODEWORDS`, on either platform width. -/
theorem boundary_gt_max_codewords : 65536 < (Usize.max + 1) / 32 := by
  rcases Usize.bounds_eq with h | h
  · rw [h]; simp [U32.max, U32.numBits]
  · rw [h]; simp [U64.max, U64.numBits]

/-- **The old witness fails the repaired premise.**  There is a decoder on which `message` cannot
return, and it needs more than 65536 chunks, so `DecoderMessageTotal` says nothing about it. -/
theorem old_witness_fails_bounded_premise :
    ∃ d : Decoder, ¬ d.needed.val ≤ 65536 ∧ ¬ ∃ r, Decoder.message d = ok r := by
  obtain ⟨d, hsize, hd, hf⟩ := old_witness
  refine ⟨d, ?_, hf⟩
  have := boundary_gt_max_codewords
  omega

/-- **The translated `Decoder::invariant` rejects a decoder like the old witness.**  There is a
decoder with `32 * needed = Usize.max + 1` on which `message` cannot return, and
`Decoder::invariant` does not return `true` on it. -/
theorem old_witness_rejected_by_invariant :
    ∃ d : Decoder, 32 * d.needed.val = Usize.max + 1 ∧
      ¬ Decoder.invariant d = ok true ∧ ¬ ∃ r, Decoder.message d = ok r := by
  obtain ⟨d, hsize, h32, hf⟩ := old_witness
  refine ⟨d, h32, fun h => ?_, hf⟩
  have hle := Tacenta.SessionUnitDecoderBound.invariant_true_needed_le d h
  have := boundary_gt_max_codewords
  omega

/-! ## B. The repaired field holds under one law, the unbounded one is false -/

/-- **The repaired field follows from `Vec::truncate` returning.**  `Decoder::message` is total on
every decoder with `needed <= 65536`.  The law is the only assumption: the real `Vec::truncate`
never panics. -/
theorem decoderMessageTotal_of_truncate (htr : TruncateTotal) :
    Tacenta.SessionUnitBraidT1.DecoderMessageTotal := by
  intro d _hsize hd
  have hbig : Usize.max ≥ 4294967295 := by scalar_tac
  exact (noPanic_iff _).mp
    (Tacenta.SessionUnitErasureT1.message_no_panic htr d (by scalar_tac) (by scalar_tac))

/-- **The repaired field is true and the old one is false, under the one law.** -/
theorem bounded_holds_unbounded_fails (htr : TruncateTotal) :
    Tacenta.SessionUnitBraidT1.DecoderMessageTotal ∧
      ¬ Tacenta.SessionUnitBraidT1.DecoderMessageTotalUnbounded :=
  ⟨decoderMessageTotal_of_truncate htr,
    Tacenta.SessionBraidReceiveVacuity.decoderMessage_not_total⟩

/-- **Every decoder that passes the translated `Decoder::invariant` has a returning
`Decoder::message`**, given `Vec::truncate` returns.  This is what the repair buys for a state that
passed `Braid::invariant`. -/
theorem message_total_of_invariant (htr : TruncateTotal) (d : Decoder)
    (hsize : d.size.val ≤ 4128) (h : Decoder.invariant d = ok true) : ∃ r, Decoder.message d = ok r :=
  decoderMessageTotal_of_truncate htr d hsize
    (Tacenta.SessionUnitDecoderBound.invariant_true_needed_le d h)

/-! ## C. Where the line is

The exact line between a returning and a failing `Decoder::message` is `K = (Usize.max + 1) / 32`
chunks.  Below it the call returns (given the law), at it the call fails.  A premise raised to
`K` is therefore false, so the premise cannot be raised to the line. -/

/-- `DecoderMessageTotal` with the bound as a parameter.  `decoderMessageTotal_is` ties it to the
field by `Iff.rfl`, so a change to the consequent of the field stops this file from building. -/
def DecoderMessageTotalAt (n : Nat) : Prop :=
  ∀ d : Decoder, d.size.val ≤ 4128 → d.needed.val ≤ n → ∃ r, Decoder.message d = ok r

theorem decoderMessageTotal_is :
    Tacenta.SessionUnitBraidT1.DecoderMessageTotal ↔ DecoderMessageTotalAt 65536 := Iff.rfl

/-- The field holds for every `needed < K` and fails at `needed = K`. -/
theorem boundary_exact (htr : TruncateTotal) :
    (∀ d : Decoder, d.size.val ≤ 4128 →
      d.needed.val < (Usize.max + 1) / 32 →
        ∃ r, Decoder.message d = ok r) ∧
      ¬ DecoderMessageTotalAt ((Usize.max + 1) / 32) := by
  constructor
  · intro d hsize hd
    obtain ⟨K, hK32, hKlt⟩ := usize_max_facts
    have hKeq : (Usize.max + 1) / 32 = K := by omega
    rw [hKeq] at hd
    exact (noPanic_iff _).mp
      (Tacenta.SessionUnitErasureT1.message_no_panic htr d (by omega) (by omega))
  · intro H
    obtain ⟨d, hsize, hd, hf⟩ := old_witness
    exact hf (H d hsize (by omega))

/-- **The premise at the boundary is refuted.**  Replacing `65536` by `K` in the repaired field
gives a false statement, for every interpretation of the unit's axioms.  This is the second part of
`boundary_exact`, stated without the law. -/
theorem mutant_premise_at_boundary_refuted :
    ¬ DecoderMessageTotalAt ((Usize.max + 1) / 32) := by
  intro H
  obtain ⟨d, hsize, hd, hf⟩ := old_witness
  exact hf (H d hsize (by omega))

/-! ## D. The new law is consistent

`DivCeilValue` is the value of `usize::div_ceil` at divisor 32.  The real operation satisfies it,
so the statement is not itself contradictory.  This is a model of the shape of the statement (a
function with the required property exists), not a model of the unit's opaque `div_ceil`. -/

/-- `DivCeilValue` with the function abstracted.  `DivCeilValue_is` ties it to the unit's
`usize::div_ceil` by `Iff.rfl`, so a change to the statement of `DivCeilValue` stops this file
from building. -/
def DivCeilValueShape (f : Usize → Usize → Result Usize) : Prop :=
  ∀ a : Usize, ∃ r, f a 32#usize = ok r ∧ r.val = (a.val + 31) / 32

theorem DivCeilValue_is :
    Tacenta.SessionUnitDecoderBound.DivCeilValue ↔
      DivCeilValueShape tacenta_session_unit.core.num.Usize.div_ceil := Iff.rfl

theorem divCeilValue_shape_satisfiable :
    ∃ f : Usize → Usize → Result Usize, DivCeilValueShape f := by
  have key : ∀ a b : Usize, b.val ≠ 0 →
      (a.val + b.val - 1) / b.val < 2 ^ UScalarTy.Usize.numBits := by
    intro a b hb
    have h1 := a.hBounds
    have hbpos : 0 < b.val := Nat.pos_of_ne_zero hb
    have h2 : (a.val + b.val - 1) / b.val < a.val + 1 := by
      rw [Nat.div_lt_iff_lt_mul hbpos]
      rcases Nat.eq_zero_or_pos a.val with h | h
      · rw [h]; omega
      · have h3 : a.val * b.val ≥ a.val := Nat.le_mul_of_pos_right _ hbpos
        have e : (a.val + 1) * b.val = a.val * b.val + b.val := by ring
        omega
    omega
  refine ⟨fun a b => if h : b.val = 0 then fail .panic
      else ok (Usize.ofNatCore ((a.val + b.val - 1) / b.val) (key a b h)), ?_⟩
  intro a
  have h32 : (32#usize).val = 32 := by simp
  have hne : ¬ (32#usize).val = 0 := by simp
  refine ⟨Usize.ofNatCore ((a.val + (32#usize).val - 1) / (32#usize).val)
    (key a 32#usize (by simp)), ?_, ?_⟩
  · simp only [dif_neg hne]
  · rw [Usize.ofNatCore_val_eq]
    rw [h32]; omega

end Tacenta.SessionBraidReceiveRepair

/-! ## Axiom pins

The axiom bases of the results above, held by the build.  The lists name constants that occur in the
statements of the results, not assumptions the proofs make: `Vec::truncate` occurs in every
statement about `Decoder::message`, and `div_ceil` occurs in `Decoder::invariant` through
`chunk_count`.  The results that take `TruncateTotal` assume that one law and nothing else about an
opaque operation.  `divCeilValue_shape_satisfiable` and `boundary_gt_max_codewords` use no
translated constant. -/

/--
info: 'Tacenta.SessionBraidReceiveRepair.old_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveRepair.old_witness

/--
info: 'Tacenta.SessionBraidReceiveRepair.boundary_gt_max_codewords' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveRepair.boundary_gt_max_codewords

/--
info: 'Tacenta.SessionBraidReceiveRepair.old_witness_fails_bounded_premise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveRepair.old_witness_fails_bounded_premise

/--
info: 'Tacenta.SessionBraidReceiveRepair.old_witness_rejected_by_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveRepair.old_witness_rejected_by_invariant

/--
info: 'Tacenta.SessionBraidReceiveRepair.decoderMessageTotal_of_truncate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveRepair.decoderMessageTotal_of_truncate

/--
info: 'Tacenta.SessionBraidReceiveRepair.bounded_holds_unbounded_fails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveRepair.bounded_holds_unbounded_fails

/--
info: 'Tacenta.SessionBraidReceiveRepair.message_total_of_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveRepair.message_total_of_invariant

/--
info: 'Tacenta.SessionBraidReceiveRepair.boundary_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveRepair.boundary_exact

/--
info: 'Tacenta.SessionBraidReceiveRepair.mutant_premise_at_boundary_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveRepair.mutant_premise_at_boundary_refuted

/--
info: 'Tacenta.SessionBraidReceiveRepair.divCeilValue_shape_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveRepair.divCeilValue_shape_satisfiable

/--
info: 'Tacenta.SessionBraidReceiveRepair.decoderMessageTotal_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveRepair.decoderMessageTotal_is

/--
info: 'Tacenta.SessionBraidReceiveRepair.DivCeilValue_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.SessionBraidReceiveRepair.DivCeilValue_is
