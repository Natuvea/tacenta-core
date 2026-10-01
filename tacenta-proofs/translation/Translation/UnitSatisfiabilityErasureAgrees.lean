import Translation.UnitSatisfiabilityErasure
import Translation.SessionUnitBraidT3

/-!
# Two halves of the erasure agreement of the Session unit that need no compiler-trust axiom

`SessionUnitBraidT3.lean` takes `ErasureAgrees` and `ErasureCloneAgrees` as hypotheses of the four
Braid refinement theorems.  In the complete Session unit the erasure coder is translated Rust
(`tacenta_session_unit.tacenta_erasure.*`), so both are statements about definitions and not about
opaque operations, and the standalone model of `ErasureWitness.lean` covers neither.

* `erasureCloneAgrees`: `ErasureCloneAgrees` holds of the translated unit, outright.  A clone of an
  encoder or a decoder is equal to it.  No law about an opaque constant is used.
* `erasureAgrees_encoder`: the encoder half of `ErasureAgrees` holds of the translated unit, given
  that `usize::div_ceil` returns at divisor 32 (`DivCeil32`, which the value law `DivCeilValue`
  implies).  For every message, `Encoder::new` returns an encoder that refines the model's encoder
  of the same bytes, for as many steps as a `u16` index allows.

Both are kernel-checked.  The decoder half of `ErasureAgrees` is not here.

## What it does not show

* The decoder half of `ErasureAgrees`.  It needs that decoding the codewords of a message at
  distinct indices returns the message: that is the Reed-Solomon proof of `UnitErasureRsGlue.lean`,
  which assembles the whole of `ErasureAgrees` under the two laws `DivCeilValue` and `TruncatePrefix`.
* That `usize::div_ceil` returns at divisor 32: `DivCeil32` is a hypothesis of
  `erasureAgrees_encoder`, and `UnitSatisfiabilityErasure.divCeil32_of_value` derives it from
  `DivCeilValue`, a law about an opaque standard-library function.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit.tacenta_erasure

namespace Tacenta.UnitSatisfiabilityErasureAgrees

/-- A clone of a translated encoder is equal to the encoder.  The translated `clone` is a
`Slice.clone` over an element clone that returns its argument, plus the scalar clones. -/
theorem encoder_clone_eq (e e' : Encoder)
    (h : Encoder.Insts.CoreCloneClone.clone e = ok e') : e' = e := by
  unfold Encoder.Insts.CoreCloneClone.clone at h
  unfold alloc.vec.CloneVec.clone at h
  have hc : ∀ x ∈ e.chunks.val,
      (core.clone.CloneArray 32#usize core.clone.CloneU8).clone x = ok x := by
    intro x _
    show core.array.CloneArray.clone core.clone.CloneU8 x = ok x
    obtain ⟨a', ha, hx⟩ := WP.spec_imp_exists
      (core.array.CloneArray.clone_spec core.clone.CloneU8 x (by intro y _; simp))
    rw [ha, ← hx]
  obtain ⟨s', hs, hx⟩ := WP.spec_imp_exists (Slice.clone_spec hc)
  rw [hs] at h
  change ok _ = ok e' at h
  injection h with h
  subst h
  cases e
  simp only at hx
  simp [core.clone.impls.CloneU16.clone, core.clone.impls.CloneBool.clone, ← hx]

theorem decoder_clone_eq (d d' : Decoder)
    (h : Decoder.Insts.CoreCloneClone.clone d = ok d') : d' = d := by
  unfold Decoder.Insts.CoreCloneClone.clone at h
  unfold alloc.vec.CloneVec.clone at h
  have hc : ∀ x ∈ d.«have».val, Chunk.Insts.CoreCloneClone.clone x = ok x := by
    intro x _; rfl
  obtain ⟨s', hs, hx⟩ := WP.spec_imp_exists (Slice.clone_spec hc)
  rw [hs] at h
  change ok _ = ok d' at h
  injection h with h
  subst h
  cases d
  simp only at hx
  simp [core.clone.impls.CloneUsize.clone, ← hx]

/-- **`ErasureCloneAgrees` holds of the translated unit, outright**: a clone of an encoder or a
decoder is equal to it.  No law about an opaque constant is used. -/
theorem erasureCloneAgrees : Tacenta.SessionUnitBraidT3.ErasureCloneAgrees :=
  ⟨fun e e' h => encoder_clone_eq e e' h, fun d d' h => decoder_clone_eq d d' h⟩


private theorem u16_succ_ok {x : U16} (h : ¬x = core.num.U16.MAX) :
    x.val + 1 ≤ U16.max := by
  have hne : x.val ≠ U16.max := by
    intro e
    exact h (UScalar.eq_of_val_eq (by simpa [core.num.U16.MAX, U16.max, U16.rMax, U16.numBits] using e))
  scalar_tac

/-- What `Encoder::next_chunk` does to a live encoder, structurally: it returns the chunk at the
index `next`, keeps the chunk store, and either sets `exhausted` (at `u16::MAX`, leaving `next`)
or advances `next` by one. -/
theorem next_chunk_shape (e : Encoder) (hne : e.exhausted = false)
    (h : e.chunks.val.length < Usize.max) :
    Encoder.next_chunk e ⦃ fun r =>
      (∃ data, r.1 = some { index := e.next, data := data }) ∧ r.2.chunks = e.chunks ∧
      (e.next = core.num.U16.MAX → r.2.exhausted = true ∧ r.2.next = e.next) ∧
      (e.next ≠ core.num.U16.MAX → r.2.exhausted = false ∧ r.2.next.val = e.next.val + 1) ⦄ := by
  have hlen : (e.chunks.len).val < Usize.max := by
    rw [alloc.vec.Vec.len_val]; exact h
  have hcap : (alloc.vec.Vec.with_capacity U16 e.chunks.len).val.length
      + (e.chunks.len).val < Usize.max := by
    simp only [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, List.length_nil,
      Nat.zero_add]
    exact hlen
  unfold Encoder.next_chunk
  simp only [hne, Bool.false_eq_true, if_false]
  step* <;> first
    | exact Tacenta.SessionUnitErasureT1.next_chunk_nodes_no_panic _ _ _ hcap
    | exact Tacenta.SessionUnitErasureT1.weights_no_panic _
    | exact Tacenta.SessionUnitErasureT1.coefficients_no_panic _ _ _
    | exact Tacenta.SessionUnitErasureT1.next_chunk_lanes_no_panic _ _ _ _ _ hlen (by simp)
    | (have := u16_succ_ok (by assumption); simpa using this)


/-- The same without the length hypothesis.  A chunk store of length `Usize.max` is longer than
every `u16` index, so `next_chunk` takes the copying branch, which needs no room. -/
theorem next_chunk_shape' (e : Encoder) (hne : e.exhausted = false) :
    Encoder.next_chunk e ⦃ fun r =>
      (∃ data, r.1 = some { index := e.next, data := data }) ∧ r.2.chunks = e.chunks ∧
      (e.next = core.num.U16.MAX → r.2.exhausted = true ∧ r.2.next = e.next) ∧
      (e.next ≠ core.num.U16.MAX → r.2.exhausted = false ∧ r.2.next.val = e.next.val + 1) ⦄ := by
  by_cases h : e.chunks.val.length < Usize.max
  · exact next_chunk_shape e hne h
  · have hlen : e.chunks.val.length = Usize.max := le_antisymm e.chunks.property (not_lt.mp h)
    have hlt : (UScalar.cast .Usize e.next) < e.chunks.len := by
      have h2 : (e.chunks.len).val = Usize.max := by
        rw [alloc.vec.Vec.len_val]; exact hlen
      have h3 := e.next.hBounds
      have h4 : (UScalar.cast .Usize e.next).val = e.next.val := U16.cast_Usize_val_eq e.next
      scalar_tac
    unfold Encoder.next_chunk
    simp only [hne, Bool.false_eq_true, if_false, lift, bind_tc_ok, hlt, if_true]
    step*
    all_goals (have := u16_succ_ok (by assumption); simpa using this)


theorem u16max_val : (core.num.U16.MAX).val = 65535 := by
  simp [core.num.U16.MAX, U16.rMax]

open Tacenta.SessionUnitBraidT3 (EncoderSim EncoderRefines sliceOf)

/-- A live real encoder simulates the model encoder at the same position for as many steps as a
`u16` index allows.  The encoder is an arbitrary one with `exhausted = false` and `next` at the
model's position; nothing about its chunk store is assumed. -/
theorem encoderSim_live : ∀ (n : ℕ) (e : Encoder) (m : Model.Braid.Encoder),
    e.exhausted = false → e.next.val = m.next → m.next + n ≤ 65536 → EncoderSim n e m := by
  intro n
  induction n with
  | zero => intro e m _ _ _; trivial
  | succ n ih =>
    intro e m hex hn hle
    obtain ⟨⟨r1, r2⟩, hr, ⟨⟨data, hdata⟩, hch, hmax, hnmax⟩⟩ :=
      WP.spec_imp_exists (next_chunk_shape' e hex)
    simp only at hdata hch hmax hnmax
    subst hdata
    refine ⟨⟨e.next, data⟩, r2, hr, ?_, ?_⟩
    · simp [Model.Braid.Encoder.nextChunk, hn]
    · by_cases hm : e.next = core.num.U16.MAX
      · have h1 : e.next.val = 65535 := by rw [hm]; exact u16max_val
        have h2 : n = 0 := by omega
        subst h2
        trivial
      · obtain ⟨hex', hnext'⟩ := hnmax hm
        exact ih r2 _ hex' (by simp [Model.Braid.Encoder.nextChunk, hnext', hn])
          (by simp [Model.Braid.Encoder.nextChunk]; omega)


open Tacenta.SessionUnitDecoderBound (bind_eq_ok_inv)

/-- A new encoder has emitted nothing and is not exhausted. -/
theorem new_shape (s : Slice U8) (r : Encoder) (h : Encoder.new s = ok r) :
    r.exhausted = false ∧ r.next = 0#u16 := by
  unfold Encoder.new at h
  obtain ⟨k, -, h1⟩ := bind_eq_ok_inv h
  obtain ⟨k1, -, h2⟩ := bind_eq_ok_inv h1
  obtain ⟨c1, -, h3⟩ := bind_eq_ok_inv h2
  simp only [ok.injEq] at h3
  subst h3
  exact ⟨rfl, rfl⟩

/-- `ErasureAgrees` is its two clauses, one for `Encoder::new` and one for `Decoder::new`, stated
here in full and bound to the predicate of `SessionUnitBraidT3.lean` by `Iff.rfl`.  The first clause is
exactly the conclusion of `erasureAgrees_encoder`, so that theorem is the first conjunct of
`ErasureAgrees` and not a copy that could drift from it. -/
theorem erasureAgrees_iff_clauses :
    Tacenta.SessionUnitBraidT3.ErasureAgrees ↔
      (∀ (s : Slice Std.U8), ∃ real, Encoder.new s = ok real ∧
        Tacenta.SessionUnitBraidT3.EncoderRefines real
          (Model.Braid.encode (Tacenta.SessionUnitBraidT3.sliceOf s))) ∧
      (∀ (n : Usize), ∃ real, Decoder.new n = ok real ∧
        Tacenta.SessionUnitBraidT3.DecoderRefines real (Model.Braid.Decoder.new n.val)) :=
  Iff.rfl

/-- **The encoder half of `ErasureAgrees` holds of the translated unit, given that `usize::div_ceil`
returns at divisor 32** (`DivCeil32`, which the value law `DivCeilValue` implies).  For every
message `s`, `Encoder::new` returns an encoder that refines the model's encoder of the same
bytes: it was made from them, it has emitted nothing, and it simulates the model for every number
of steps a `u16` index allows. -/
theorem erasureAgrees_encoder (hdc : Tacenta.UnitSatisfiabilityErasure.DivCeil32) :
    ∀ s : Slice U8, ∃ real, Encoder.new s = ok real ∧
      EncoderRefines real (Model.Braid.encode (sliceOf s)) := by
  intro s
  obtain ⟨r, hr⟩ := Tacenta.UnitSatisfiabilityErasure.encoderNew_total hdc s
  obtain ⟨hex, hnext⟩ := new_shape s r hr
  refine ⟨r, hr, ⟨s, r, rfl, hr, rfl⟩, fun n hn => encoderSim_live n r _ hex ?_ ?_⟩
  · simp [Model.Braid.encode, hnext]
  · simpa [Model.Braid.encode] using hn

end Tacenta.UnitSatisfiabilityErasureAgrees

/--
info: 'Tacenta.UnitSatisfiabilityErasureAgrees.erasureCloneAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityErasureAgrees.erasureCloneAgrees

/--
info: 'Tacenta.UnitSatisfiabilityErasureAgrees.erasureAgrees_encoder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityErasureAgrees.erasureAgrees_encoder

/--
info: Tacenta.UnitSatisfiabilityErasureAgrees.erasureCloneAgrees : Tacenta.SessionUnitBraidT3.ErasureCloneAgrees
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityErasureAgrees.erasureCloneAgrees

/--
info: Tacenta.UnitSatisfiabilityErasureAgrees.erasureAgrees_encoder (hdc : Tacenta.UnitSatisfiabilityErasure.DivCeil32)
  (s : Slice U8) :
  ∃ real,
    Encoder.new s = ok real ∧
      Tacenta.SessionUnitBraidT3.EncoderRefines real (Model.Braid.encode (Tacenta.SessionUnitBraidT3.sliceOf s))
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityErasureAgrees.erasureAgrees_encoder

/--
info: 'Tacenta.UnitSatisfiabilityErasureAgrees.erasureAgrees_iff_clauses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityErasureAgrees.erasureAgrees_iff_clauses

/--
info: Tacenta.UnitSatisfiabilityErasureAgrees.erasureAgrees_iff_clauses :
  Tacenta.SessionUnitBraidT3.ErasureAgrees ↔
    (∀ (s : Slice U8),
        ∃ real,
          Encoder.new s = ok real ∧
            Tacenta.SessionUnitBraidT3.EncoderRefines real
              (Model.Braid.encode (Tacenta.SessionUnitBraidT3.sliceOf s))) ∧
      ∀ (n : Usize),
        ∃ real, Decoder.new n = ok real ∧ Tacenta.SessionUnitBraidT3.DecoderRefines real (Model.Braid.Decoder.new ↑n)
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityErasureAgrees.erasureAgrees_iff_clauses
