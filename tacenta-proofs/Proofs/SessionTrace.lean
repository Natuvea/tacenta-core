/-
Proofs.SessionTrace: the narrow theorem for `SESSION-LIFECYCLE-01`.

This theorem is about the explicit, bounded trace abstraction in
`Model.SessionTrace`, not a refinement of the Rust session code. Its crypto
verdicts and committed joint snapshot are assumptions documented in
`SESSION-OPERATION-MODEL.md`. The concrete differential tests remain necessary
to show that the selected Rust traces inhabit this model boundary.
-/
import Model.SessionTrace

namespace Proofs.SessionTrace

open Model.SessionTrace

/-- Inserting an ordinary refused input and restoring fresh objects from the
    same committed snapshot does not change the outcomes of later honest
    actions. This is the trace-level persistence property; it deliberately
    excludes product-store crash windows and hostile rollback. -/
theorem refusal_restore_preserves_continuation (st : State) (actions : List Action) :
    run st ([.refused, .restore] ++ actions) = run st actions := by
  change run (step (step st .refused) .restore) actions = run st actions
  rw [refused_is_no_op, restore_is_no_op]

/-- A committed terminal agreement failure survives every later abstract
    lifecycle action. -/
theorem terminal_failure_preserves_refusal (st : State) (actions : List Action)
    (failed : st.phase = .failed) :
    (run st actions).phase = .failed :=
  failed_run_stays_failed st actions failed

/-- A replay carrying a message already accepted in the committed observation
    has no operation effect. Concrete traces must additionally check the public
    error they return. -/
theorem replay_has_no_second_acceptance (st : State) (message : Nat)
    (accepted : message ∈ st.accepted) :
    step st (.receive message) = st :=
  accepted_replay_is_no_op st message accepted

end Proofs.SessionTrace
