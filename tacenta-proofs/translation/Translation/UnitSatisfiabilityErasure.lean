import Translation.SessionBraidReceiveRepair

/-!
# The erasure coder's fields of the Braid contract records

The Braid contract records (`BraidSendContracts`, `BraidReceiveContracts` in
`UnitLifecyclePublicT1.lean`) carry seven fields about the erasure coder, which the Session
unit translates with a body rather than leaving opaque.  A field about a translated function
is not satisfied by choosing a model: its truth is fixed by the body and by the opaque
operations the body reaches.  This module settles each by a proof about the translated
definitions.

* `encoderClone_total`, `decoderClone_total`, `decoderAddChunk_total` and
  `encoderNextChunk_total` hold with no assumption about any opaque operation.  The two
  hypotheses of the existing `add_chunk_no_panic` and `next_chunk_no_panic` are not needed:
  the one length they exclude (`Usize.max`) makes the function return at once.
* `decoderNew_total` and `encoderNew_total` hold given `DivCeil32`, that the opaque
  `usize::div_ceil` returns at divisor 32.  `decoderNew_iff` and `encoderNew_iff` show that
  each of the two fields is *exactly* that law.  `divCeil32_of_value` shows the law follows
  from `DivCeilValue`, the field `divCeilValue` of `EstablishResponderContracts`, so the two
  fields are consequences of a statement the responder record already makes.
* The seventh erasure field, `DecoderMessageTotal`, is not here.  It was false before the
  repair (`SessionBraidReceiveVacuity.lean`) and is a consequence of `TruncateTotal` after
  it (`SessionBraidReceiveRepair.decoderMessageTotal_of_truncate`).

Nothing here shows that the real `div_ceil` satisfies the law.  `UnitSatisfiabilityJoint.lean`
shows the law holds in one interpretation of the unit's opaque constants.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit.tacenta_erasure

namespace Tacenta.UnitSatisfiabilityErasure

open Tacenta.SessionUnitErasureT1 (noPanic_iff)
open Tacenta.SessionUnitDecoderBound (DivCeilValue bind_eq_ok_inv)

/-! ## A. The four fields that hold with no law -/

theorem encoderClone_total : Tacenta.SessionUnitBraidT1.EncoderCloneTotal := by
  intro e
  unfold Encoder.Insts.CoreCloneClone.clone
  unfold alloc.vec.CloneVec.clone
  have hc : ∀ x ∈ e.chunks.val,
      (core.clone.CloneArray 32#usize core.clone.CloneU8).clone x = ok x := by
    intro x _
    show core.array.CloneArray.clone core.clone.CloneU8 x = ok x
    obtain ⟨a', ha, hx⟩ := WP.spec_imp_exists
      (core.array.CloneArray.clone_spec core.clone.CloneU8 x (by intro y _; simp))
    rw [ha, ← hx]
  obtain ⟨s', hs, hx⟩ := WP.spec_imp_exists (Slice.clone_spec hc)
  exact ⟨_, by simp [hs]; rfl⟩

theorem decoderClone_total : Tacenta.SessionUnitBraidT1.DecoderCloneTotal := by
  intro d
  unfold Decoder.Insts.CoreCloneClone.clone
  unfold alloc.vec.CloneVec.clone
  have hc : ∀ x ∈ d.«have».val,
      Chunk.Insts.CoreCloneClone.clone x = ok x := by
    intro x _; rfl
  obtain ⟨s', hs, hx⟩ := WP.spec_imp_exists (Slice.clone_spec hc)
  exact ⟨_, by simp [hs]; rfl⟩

/-- `Decoder::add_chunk` returns for every decoder and every chunk.  The existing
`add_chunk_no_panic` assumes `have.length < Usize.max`.  That assumption is not needed: a
vector of length `Usize.max` is at least `needed`, so `add_chunk` returns at once. -/
theorem decoderAddChunk_total : Tacenta.SessionUnitBraidT1.DecoderAddChunkTotal := by
  intro d c
  by_cases h : d.«have».val.length < Usize.max
  · exact (noPanic_iff _).mp
      (Tacenta.SessionUnitErasureT1.add_chunk_no_panic d c h)
  · have hlen : d.«have».val.length = Usize.max :=
      le_antisymm d.«have».property (not_lt.mp h)
    have hge : d.«have».len ≥ d.needed := by
      have := d.needed.hBounds
      have h2 : (d.«have».len).val = Usize.max := by
        rw [alloc.vec.Vec.len_val]; exact hlen
      show d.needed ≤ d.«have».len
      scalar_tac
    unfold Decoder.add_chunk
    simp [hge]

private theorem u16_succ_ok {x : U16} (h : ¬x = core.num.U16.MAX) :
    x.val + 1 ≤ U16.max := by
  have hne : x.val ≠ U16.max := by
    intro e
    exact h (UScalar.eq_of_val_eq (by simpa [core.num.U16.MAX, U16.max, U16.rMax, U16.numBits] using e))
  scalar_tac

/-- `Encoder::next_chunk` returns for every encoder.  The existing `next_chunk_no_panic`
assumes `chunks.length < Usize.max`.  When the length is `Usize.max`, the node index `next` (a
`u16`) is below it, so the function copies a stored chunk and never reaches the interpolation
branch. -/
theorem encoderNextChunk_total : Tacenta.SessionUnitBraidT1.EncoderNextChunkTotal := by
  intro e
  by_cases h : e.chunks.val.length < Usize.max
  · exact (noPanic_iff _).mp
      (Tacenta.SessionUnitErasureT1.next_chunk_no_panic e h)
  · have hlen : e.chunks.val.length = Usize.max :=
      le_antisymm e.chunks.property (not_lt.mp h)
    have hlt : (UScalar.cast .Usize e.next) < e.chunks.len := by
      have h2 : (e.chunks.len).val = Usize.max := by
        rw [alloc.vec.Vec.len_val]; exact hlen
      have h3 := e.next.hBounds
      have h4 : (UScalar.cast .Usize e.next).val = e.next.val := U16.cast_Usize_val_eq e.next
      scalar_tac
    unfold Encoder.next_chunk
    by_cases hx : e.exhausted
    · simp [hx]
    · simp only [hx, Bool.false_eq_true, if_false, lift, bind_tc_ok]
      simp only [hlt, if_true]
      rw [← noPanic_iff]
      unfold Tacenta.SessionUnitErasureT1.NoPanic
      step*
      have := u16_succ_ok (by assumption)
      simpa using this

/-! ## B. The two constructors

Both fields are exactly the statement that `div_ceil` returns when its divisor is 32. -/

/-- `usize::div_ceil` returns at divisor 32.  The part of the recorded law
`SessionUnitErasureT1.DivCeilTotal` (every non-zero divisor) that the constructors use. -/
def DivCeil32 : Prop :=
  ∀ a : Usize, ∃ r, tacenta_session_unit.core.num.Usize.div_ceil a 32#usize = ok r

/-- The value law of `div_ceil` at divisor 32 implies that it returns. -/
theorem divCeil32_of_value (h : DivCeilValue) : DivCeil32 := by
  intro a
  obtain ⟨r, hr, -⟩ := h a
  exact ⟨r, hr⟩

theorem chunk_count_eq (a : Usize) :
    chunk_count a = tacenta_session_unit.core.num.Usize.div_ceil a 32#usize := by
  unfold chunk_count
  simp only [CHUNK_BYTES]

theorem chunk_count_no_panic32 (h : DivCeil32) (size : Usize) :
    chunk_count size ⦃ fun _ => True ⦄ := by
  rw [chunk_count_eq]
  obtain ⟨r, hr⟩ := h size
  simp [hr]

theorem new_inner_no_panic (message : Slice U8) (buf : Array U8 32#usize) (start b : Usize)
    (hb : b.val ≤ 32) (hs : start.val + 32 ≤ Usize.max) :
    Encoder.new_loop0_loop0 message buf start b ⦃ fun _ => True ⦄ := by
  unfold Encoder.new_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun p => 32 - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ 32)
  · rintro ⟨a1, b1⟩ hinv
    simp only [] at hinv
    unfold Encoder.new_loop0_loop0.body
    simp only [CHUNK_BYTES]
    split
    · rename_i hlt
      step*
      all_goals (try split)
      all_goals (try step*)
    · simp
  · exact hb

attribute [local step] new_inner_no_panic

theorem new_outer_no_panic (message : Slice U8) (k : Usize)
    (chunks : alloc.vec.Vec (Array U8 32#usize)) (t : Usize)
    (hk : k.val ≤ 65536) (hc : chunks.val.length + k.val < Usize.max) (ht : t.val ≤ k.val) :
    Encoder.new_loop0 message k chunks t ⦃ fun _ => True ⦄ := by
  unfold Encoder.new_loop0
  apply loop.spec_decr_nat
    (measure := fun p => k.val - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ k.val ∧
      (Prod.fst p).val.length + (k.val - (Prod.snd p).val) ≤ chunks.val.length + k.val)
  · rintro ⟨c1, t1⟩ ⟨hinv1, hinv2⟩
    simp only [] at hinv1 hinv2
    unfold Encoder.new_loop0.body
    simp only []
    split
    · rename_i hlt
      have hbig : Usize.max ≥ 4294967295 := by scalar_tac
      step*
      all_goals (try simp only [CHUNK_BYTES] at *)
      all_goals (try scalar_tac)
    · simp
  · refine ⟨ht, ?_⟩
    scalar_tac

/-- `Encoder::new` returns for every message, given that `div_ceil` returns at divisor 32.
The clamp at `MAX_CODEWORDS` keeps every index product below 2^21. -/
theorem encoderNew_total (hdc : DivCeil32) : Tacenta.SessionUnitBraidT1.EncoderNewTotal := by
  intro s
  rw [← noPanic_iff]
  unfold Tacenta.SessionUnitErasureT1.NoPanic Encoder.new
  step with chunk_count_no_panic32 hdc
  rename_i kc
  have hmax : MAX_CODEWORDS.val = 65536 := by simp [MAX_CODEWORDS]
  have hbig : Usize.max ≥ 4294967295 := by scalar_tac
  by_cases hx : kc > MAX_CODEWORDS
  · simp only [hx, if_true, bind_tc_ok]
    have := new_outer_no_panic s MAX_CODEWORDS
      (alloc.vec.Vec.with_capacity (Std.Array U8 32#usize) MAX_CODEWORDS) 0#usize
      (by scalar_tac) (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]; scalar_tac)
      (by simp)
    obtain ⟨r, hr, -⟩ := WP.spec_imp_exists this
    simp [hr]
  · simp only [hx, if_false, bind_tc_ok]
    have := new_outer_no_panic s kc
      (alloc.vec.Vec.with_capacity (Std.Array U8 32#usize) kc) 0#usize
      (by scalar_tac) (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]; scalar_tac)
      (by simp)
    obtain ⟨r, hr, -⟩ := WP.spec_imp_exists this
    simp [hr]

/-- `Decoder::new` returns for every size, given the same law. -/
theorem decoderNew_total (hdc : DivCeil32) : Tacenta.SessionUnitBraidT1.DecoderNewTotal := by
  intro n
  rw [← noPanic_iff]
  unfold Tacenta.SessionUnitErasureT1.NoPanic Decoder.new
  step with chunk_count_no_panic32 hdc

/-- **`DecoderNewTotal` is exactly the law `DivCeil32`.** -/
theorem decoderNew_iff : Tacenta.SessionUnitBraidT1.DecoderNewTotal ↔ DivCeil32 :=
  ⟨fun H a => by
    obtain ⟨d, hd⟩ := H a
    unfold Decoder.new at hd
    obtain ⟨k, hk, -⟩ := bind_eq_ok_inv hd
    rw [chunk_count_eq] at hk
    exact ⟨k, hk⟩, decoderNew_total⟩

/-- **`EncoderNewTotal` is exactly the law `DivCeil32`.**  The witness slice for a length `a`
is `a` zero bytes. -/
theorem encoderNew_iff : Tacenta.SessionUnitBraidT1.EncoderNewTotal ↔ DivCeil32 :=
  ⟨fun H a => by
    let s : Slice U8 := ⟨List.replicate a.val 0#u8, by simp; scalar_tac⟩
    obtain ⟨e, he⟩ := H s
    unfold Encoder.new at he
    obtain ⟨k, hk, -⟩ := bind_eq_ok_inv he
    rw [chunk_count_eq] at hk
    have hs : Slice.len s = a := by
      apply UScalar.eq_of_val_eq
      simp [Slice.len, s]
    rw [hs] at hk
    exact ⟨k, hk⟩, encoderNew_total⟩

/-- `DecoderNewTotal` follows from the field `divCeilValue` of `EstablishResponderContracts`. -/
theorem decoderNew_of_divCeilValue (h : DivCeilValue) :
    Tacenta.SessionUnitBraidT1.DecoderNewTotal :=
  decoderNew_iff.mpr (divCeil32_of_value h)

/-- `EncoderNewTotal` follows from the same law. -/
theorem encoderNew_of_divCeilValue (h : DivCeilValue) :
    Tacenta.SessionUnitBraidT1.EncoderNewTotal :=
  encoderNew_iff.mpr (divCeil32_of_value h)

end Tacenta.UnitSatisfiabilityErasure

/-! ## Axiom pins

The axiom bases of the results above, held by the build.  A list names the constants that occur in
the statement of a result, not assumptions its proof makes: the statements of `decoderNew_iff`
and `encoderNew_iff` mention `div_ceil`.  The four results with no law list the three standard
axioms only.  `divCeil32_of_value`, `decoderNew_of_divCeilValue` and `encoderNew_of_divCeilValue` take
`DivCeilValue` as a hypothesis and assume nothing else about an opaque operation. -/

/--
info: 'Tacenta.UnitSatisfiabilityErasure.decoderAddChunk_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityErasure.decoderAddChunk_total

/--
info: 'Tacenta.UnitSatisfiabilityErasure.encoderNextChunk_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityErasure.encoderNextChunk_total

/--
info: 'Tacenta.UnitSatisfiabilityErasure.encoderClone_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityErasure.encoderClone_total

/--
info: 'Tacenta.UnitSatisfiabilityErasure.decoderClone_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityErasure.decoderClone_total

/--
info: 'Tacenta.UnitSatisfiabilityErasure.decoderNew_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityErasure.decoderNew_iff

/--
info: 'Tacenta.UnitSatisfiabilityErasure.encoderNew_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityErasure.encoderNew_iff

/--
info: 'Tacenta.UnitSatisfiabilityErasure.divCeil32_of_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityErasure.divCeil32_of_value

/--
info: 'Tacenta.UnitSatisfiabilityErasure.decoderNew_of_divCeilValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityErasure.decoderNew_of_divCeilValue

/--
info: 'Tacenta.UnitSatisfiabilityErasure.encoderNew_of_divCeilValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityErasure.encoderNew_of_divCeilValue
