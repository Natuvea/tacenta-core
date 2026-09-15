import Model.PersistedState

/-!
# Bounded session lifecycle trace

`SESSION-LIFECYCLE-01` is an executable, deliberately abstract operation model.
It represents only the committed observations that a two-party session trace
shares with the concrete harness: phase, queued message labels and accepted
message labels. Cryptographic verdicts and the joint persistence snapshot are
inputs at this boundary; see `SESSION-OPERATION-MODEL.md`.

The model is intentionally small. It proves the effect of inserting an
ordinary refusal or restoration observation, replaying an accepted message and
continuing after terminal failure. It does not claim to refine Rust or compute
signatures, DH, KEM or AEAD.
-/

namespace Model
namespace SessionTrace

inductive Phase where
  | fresh
  | active
  | failed
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  queued : List Nat
  accepted : List Nat
  deriving DecidableEq, Repr

inductive Action where
  | establish
  | send (message : Nat)
  | receive (message : Nat)
  | refused
  | restore
  | terminalFailure
  deriving DecidableEq, Repr

/-- An honest session operation can run only after establishment and before a
    terminal Braid failure. -/
def canOperate (st : State) : Bool := st.phase == .active

/-- One committed lifecycle transition. `refused` and `restore` model a
    refusal that has no durable effect and a fresh object imported from the
    committed joint snapshot respectively. A duplicate receive leaves the
    observation unchanged, which is the model's replay refusal. -/
def step (st : State) : Action → State
  | .establish =>
      if st.phase == .fresh then { st with phase := .active } else st
  | .send message =>
      if canOperate st && message ∉ st.queued && message ∉ st.accepted then
        { st with queued := message :: st.queued }
      else st
  | .receive message =>
      if canOperate st && message ∈ st.queued && message ∉ st.accepted then
        { st with queued := st.queued.erase message, accepted := message :: st.accepted }
      else st
  | .refused => st
  | .restore => st
  | .terminalFailure =>
      if st.phase == .fresh then st else { st with phase := .failed }

def run (st : State) : List Action → State
  | [] => st
  | action :: rest => run (step st action) rest

/-- The initial observation has no session, queued messages or accepted
    plaintexts. -/
def initial : State := { phase := .fresh, queued := [], accepted := [] }

theorem refused_is_no_op (st : State) : step st .refused = st := rfl

theorem restore_is_no_op (st : State) : step st .restore = st := rfl

theorem refused_prefix (st : State) (actions : List Action) :
    run st (.refused :: actions) = run st actions := rfl

theorem restore_prefix (st : State) (actions : List Action) :
    run st (.restore :: actions) = run st actions := rfl

/-- A message already accepted in the committed observation cannot be accepted
    again. The concrete trace records the matching public refusal separately. -/
theorem accepted_replay_is_no_op (st : State) (message : Nat)
    (accepted : message ∈ st.accepted) :
    step st (.receive message) = st := by
  simp [step, accepted]

/-- Once terminal failure is committed, every later action leaves the phase
    failed. This is scoped to the abstract lifecycle state; it says nothing
    about a caller replacing its store with an older hostile snapshot. -/
theorem failed_step_stays_failed (st : State) (failed : st.phase = .failed)
    (action : Action) : (step st action).phase = .failed := by
  cases action <;> simp [step, canOperate, failed]

theorem failed_run_stays_failed (st : State) (actions : List Action)
    (failed : st.phase = .failed) : (run st actions).phase = .failed := by
  induction actions generalizing st with
  | nil => exact failed
  | cons action rest ih =>
      exact ih (step st action) (failed_step_stays_failed st failed action)

/-- The concrete/model comparison can use this executable witness for the
    smallest happy-path lifecycle: establish, send, receive, then restore. -/
example : (run initial [.establish, .send 1, .receive 1, .restore]).accepted = [1] := by
  native_decide

end SessionTrace
end Model
