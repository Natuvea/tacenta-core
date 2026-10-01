import Translation.T3
import Translation.SpqrT3
import Translation.ErasureT1
import Translation.ProtobufT3
import Translation.PreconditionShapes
import Translation.NumericBoundary

/-!
# The numeric constants of the standalone leaf translations

`NumericBoundary.lean` proves the arithmetic of the bounds for every size the caps allow. This module
states, in the standalone translations of the ratchet, the sparse ratchet, the erasure coder and
the protobuf parser, the values of the constants the bounds mention and that they equal the
model's copies (`code_matches_model`). The translation makes each constant a definition, so these
are evaluations of the generated code and nothing more: they do not say the Rust source has these
values, which is what the translation attestation and the build of the generated file are for.

It also connects the two theorems of `PreconditionShapes.lean` about the clock premise to the
statement that matters: the premise `events + 1 < u32::MAX` is satisfiable
(`clock_headroom_satisfiable`), the parked clock `MAX_EVENTS` fails it
(`clock_headroom_excludes_parked_clock`), and that is the only honest value it fails
(`clock_ceiling_summary`). The two theorems of `PreconditionShapes.lean` were referenced by no
other theorem; they are the first two conjuncts of the summary.
-/

open Aeneas Aeneas.Std

namespace Tacenta.NumericBoundaryLeaf

theorem ratchet_constants :
    (tacenta_ratchet.MAX_SKIP).val = 1000 ∧ (tacenta_ratchet.MAX_SKIPPED_STORE).val = 2000 ∧
    (tacenta_ratchet.MAX_EVENTS).val = 4294967294 := by
  simp [tacenta_ratchet.MAX_SKIP, tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_EVENTS]

theorem spqr_constants :
    (tacenta_spqr.MAX_SKIP).val = 1000 ∧ (tacenta_spqr.MAX_SKIPPED_STORE).val = 2000 ∧
    (tacenta_spqr.EPOCHS_KEPT).val = 2 := by
  simp [tacenta_spqr.MAX_SKIP, tacenta_spqr.MAX_SKIPPED_STORE, tacenta_spqr.EPOCHS_KEPT]

theorem erasure_constants :
    (tacenta_erasure.MAX_CODEWORDS).val = 65536 ∧ (tacenta_erasure.CHUNK_BYTES).val = 32 := by
  simp [tacenta_erasure.MAX_CODEWORDS, tacenta_erasure.CHUNK_BYTES]

theorem protobuf_constants : (tacenta_protobuf.MAX_FIELDS).val = 32 := by
  simp [tacenta_protobuf.MAX_FIELDS]

/-- Code and model agree on every constant a precondition mentions. -/
theorem code_matches_model :
    (tacenta_ratchet.MAX_SKIP).val = Model.State.maxSkip ∧
    (tacenta_ratchet.MAX_SKIPPED_STORE).val = Model.State.maxSkippedStore ∧
    (tacenta_ratchet.MAX_EVENTS).val = Model.State.maxEvents ∧
    (tacenta_spqr.MAX_SKIP).val = Model.SparseRatchet.maxSkip ∧
    (tacenta_spqr.MAX_SKIPPED_STORE).val = Model.SparseRatchet.maxSkippedStore ∧
    (tacenta_spqr.EPOCHS_KEPT).val = Model.SparseRatchet.epochsKept := by
  simp [tacenta_ratchet.MAX_SKIP, tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_EVENTS,
    tacenta_spqr.MAX_SKIP, tacenta_spqr.MAX_SKIPPED_STORE, tacenta_spqr.EPOCHS_KEPT,
    Model.State.maxSkip, Model.State.maxSkippedStore, Model.State.maxEvents, Model.State.u32Max,
    Model.SparseRatchet.maxSkip, Model.SparseRatchet.maxSkippedStore,
    Model.SparseRatchet.epochsKept]

/-- The parked clock is `u32::MAX - 1`. -/
theorem max_events_is_parked : (tacenta_ratchet.MAX_EVENTS).val = U32.max - 1 := by
  simp [tacenta_ratchet.MAX_EVENTS, U32.max_eq]

/-- The clock premise `events + 1 < u32::MAX` of `T3.receive_refines` is satisfiable, the parked
clock fails it, and the parked clock is the only value below `u32::MAX` that does. -/
theorem clock_ceiling_summary :
    (∃ e : U32, e.val + 1 < U32.max) ∧
    ¬ ((tacenta_ratchet.MAX_EVENTS).val + 1 < U32.max) ∧
    (∀ e : ℕ, e < U32.max → (¬ (e + 1 < U32.max) ↔ e = (tacenta_ratchet.MAX_EVENTS).val)) :=
  ⟨PreconditionShapes.clock_headroom_satisfiable,
    PreconditionShapes.clock_headroom_excludes_parked_clock,
    fun e he => by
      rw [max_events_is_parked]
      exact NumericBoundary.clock_ceiling_excludes_only_parked e he⟩

end Tacenta.NumericBoundaryLeaf

/--
info: 'Tacenta.NumericBoundaryLeaf.ratchet_constants' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundaryLeaf.ratchet_constants

/--
info: 'Tacenta.NumericBoundaryLeaf.spqr_constants' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundaryLeaf.spqr_constants

/--
info: 'Tacenta.NumericBoundaryLeaf.erasure_constants' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundaryLeaf.erasure_constants

/--
info: 'Tacenta.NumericBoundaryLeaf.protobuf_constants' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundaryLeaf.protobuf_constants

/--
info: 'Tacenta.NumericBoundaryLeaf.code_matches_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundaryLeaf.code_matches_model

/--
info: 'Tacenta.NumericBoundaryLeaf.max_events_is_parked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundaryLeaf.max_events_is_parked

/--
info: 'Tacenta.NumericBoundaryLeaf.clock_ceiling_summary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundaryLeaf.clock_ceiling_summary
