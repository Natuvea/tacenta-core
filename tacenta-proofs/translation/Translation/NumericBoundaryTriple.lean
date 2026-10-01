import Translation.UnitT3
import Translation.UnitSpqrT3
import Translation.NumericBoundary

/-!
# The numeric constants of the three-leaf unit

The values of the constants the numeric bounds mention, in the translation of the Triple Ratchet
unit (the classical and sparse ratchets compiled as one crate), and that they equal the model's
copies. See `NumericBoundaryLeaf.lean` for what this does and does not establish; the arithmetic
over the caps is in `NumericBoundary.lean`.
-/

open Aeneas Aeneas.Std
namespace Tacenta.NumericBoundaryTriple
open tacenta_triple_unit

theorem unit_ratchet_constants :
    (tacenta_ratchet.MAX_SKIP).val = 1000 ∧ (tacenta_ratchet.MAX_SKIPPED_STORE).val = 2000 ∧
    (tacenta_ratchet.MAX_EVENTS).val = 4294967294 := by
  simp [tacenta_ratchet.MAX_SKIP, tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_EVENTS]

theorem unit_spqr_constants :
    (tacenta_spqr.MAX_SKIP).val = 1000 ∧ (tacenta_spqr.MAX_SKIPPED_STORE).val = 2000 ∧
    (tacenta_spqr.EPOCHS_KEPT).val = 2 := by
  simp [tacenta_spqr.MAX_SKIP, tacenta_spqr.MAX_SKIPPED_STORE, tacenta_spqr.EPOCHS_KEPT]

/-- Code and model agree on every constant a precondition mentions. -/
theorem unit_code_matches_model :
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

end Tacenta.NumericBoundaryTriple

/--
info: 'Tacenta.NumericBoundaryTriple.unit_ratchet_constants' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundaryTriple.unit_ratchet_constants

/--
info: 'Tacenta.NumericBoundaryTriple.unit_spqr_constants' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundaryTriple.unit_spqr_constants

/--
info: 'Tacenta.NumericBoundaryTriple.unit_code_matches_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericBoundaryTriple.unit_code_matches_model
