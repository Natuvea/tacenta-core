import Model.LifecycleTrace
import Properties.Lifecycle

/-!
# Properties of executable two-party schedules

The network queue may change when a delivery is attempted. These theorems pin
the security-relevant frame condition: a refused delivery cannot change the
recipient Session, even though the oracle trace and queue remain observable.
-/

namespace Properties.LifecycleTrace

open Model.Lifecycle
open Model.LifecycleTrace

theorem refused_receive_keeps_alice (view : CodewordView) (state : State)
    (id : Nat) (reason : Refusal)
    (h : (step view state (.receive .alice id)).2 = .refused id reason) :
    (step view state (.receive .alice id)).1.alice = state.alice := by
  cases ht : takeEnvelope id state.queue with
  | none => simp [step, ht] at h
  | some found =>
      rcases found with ⟨envelope, rest⟩
      cases hr : decrypt view state.aliceOracle state.alice envelope.bytes with
      | mk next result oracle =>
          cases result with
          | error actual =>
              have hk := Model.Lifecycle.decrypt_refusal_keeps_session view
                state.aliceOracle state.alice envelope.bytes actual (by simp [hr])
              simpa [step, ht, hr] using hk
          | ok plaintext => simp [step, ht, hr] at h

theorem refused_receive_keeps_bob (view : CodewordView) (state : State)
    (id : Nat) (reason : Refusal)
    (h : (step view state (.receive .bob id)).2 = .refused id reason) :
    (step view state (.receive .bob id)).1.bob = state.bob := by
  cases ht : takeEnvelope id state.queue with
  | none => simp [step, ht] at h
  | some found =>
      rcases found with ⟨envelope, rest⟩
      cases hr : decrypt view state.bobOracle state.bob envelope.bytes with
      | mk next result oracle =>
          cases result with
          | error actual =>
              have hk := Model.Lifecycle.decrypt_refusal_keeps_session view
                state.bobOracle state.bob envelope.bytes actual (by simp [hr])
              simpa [step, ht, hr] using hk
          | ok plaintext => simp [step, ht, hr] at h

/-- Loss, replay insertion, reordering and byte forgery are network-only
    actions. They cannot change either live Session before a receive runs. -/
theorem network_action_keeps_sessions (view : CodewordView) (state : State)
    (action : Action)
    (hNetwork : (∃ id, action = .drop id) ∨ (∃ id, action = .replay id)
      ∨ (∃ id, action = .reorderFirst id)
      ∨ (∃ id offset value, action = .forge id offset value)) :
    (step view state action).1.alice = state.alice
      ∧ (step view state action).1.bob = state.bob := by
  rcases hNetwork with ⟨id, rfl⟩ | ⟨id, rfl⟩ | ⟨id, rfl⟩ | ⟨id, offset, value, rfl⟩
  all_goals simp [step]
  all_goals split <;> simp_all

/-- Terminal Braid failure is sticky for Alice across every scheduled action,
    including malformed deliveries, peer activity and network operations. -/
theorem failed_step_stays_failed_alice (view : CodewordView) (state : State)
    (action : Action) (hFailed : agreementFailed state.alice = true) :
    agreementFailed (step view state action).1.alice = true := by
  cases action with
  | send sender id plaintext =>
      cases sender with
      | alice =>
          have hs := Properties.Lifecycle.agreement_failed_encrypt_sticky view
            state.aliceOracle state.alice plaintext hFailed
          simp [step, hs, hFailed]
      | bob =>
          cases hs : encrypt view state.bobOracle state.bob plaintext with
          | mk next result oracle =>
              cases result <;> simpa [step, hs] using hFailed
  | receive receiver id =>
      cases receiver with
      | alice =>
          cases ht : takeEnvelope id state.queue with
          | none => simp [step, ht, hFailed]
          | some found =>
              rcases found with ⟨envelope, rest⟩
              have hs := Properties.Lifecycle.agreement_failed_decrypt_keeps_session view
                state.aliceOracle state.alice envelope.bytes hFailed
              cases hr : decrypt view state.aliceOracle state.alice envelope.bytes with
              | mk next result oracle =>
                  have hn : next = state.alice := by simpa [hr] using hs
                  cases result <;> simp [step, ht, hr, hn, hFailed]
      | bob =>
          cases ht : takeEnvelope id state.queue with
          | none => simpa [step, ht] using hFailed
          | some found =>
              rcases found with ⟨envelope, rest⟩
              cases hr : decrypt view state.bobOracle state.bob envelope.bytes with
              | mk next result oracle =>
                  cases result <;> simpa [step, ht, hr] using hFailed
  | drop id =>
      cases ht : takeEnvelope id state.queue <;> simpa [step, ht] using hFailed
  | replay id =>
      cases ht : findEnvelope id state.history <;> simpa [step, ht] using hFailed
  | reorderFirst id =>
      cases ht : takeEnvelope id state.queue <;> simpa [step, ht] using hFailed
  | forge id offset value =>
      cases ht : findEnvelope id state.queue <;> simpa [step, ht] using hFailed
  | failAgreement side =>
      cases side with
      | alice => simp [step, failSession, agreementFailed]
      | bob => simpa [step] using hFailed

/-- The symmetric terminal-failure fact for Bob. -/
theorem failed_step_stays_failed_bob (view : CodewordView) (state : State)
    (action : Action) (hFailed : agreementFailed state.bob = true) :
    agreementFailed (step view state action).1.bob = true := by
  cases action with
  | send sender id plaintext =>
      cases sender with
      | alice =>
          cases hs : encrypt view state.aliceOracle state.alice plaintext with
          | mk next result oracle =>
              cases result <;> simpa [step, hs] using hFailed
      | bob =>
          have hs := Properties.Lifecycle.agreement_failed_encrypt_sticky view
            state.bobOracle state.bob plaintext hFailed
          simp [step, hs, hFailed]
  | receive receiver id =>
      cases receiver with
      | alice =>
          cases ht : takeEnvelope id state.queue with
          | none => simpa [step, ht] using hFailed
          | some found =>
              rcases found with ⟨envelope, rest⟩
              cases hr : decrypt view state.aliceOracle state.alice envelope.bytes with
              | mk next result oracle =>
                  cases result <;> simpa [step, ht, hr] using hFailed
      | bob =>
          cases ht : takeEnvelope id state.queue with
          | none => simp [step, ht, hFailed]
          | some found =>
              rcases found with ⟨envelope, rest⟩
              have hs := Properties.Lifecycle.agreement_failed_decrypt_keeps_session view
                state.bobOracle state.bob envelope.bytes hFailed
              cases hr : decrypt view state.bobOracle state.bob envelope.bytes with
              | mk next result oracle =>
                  have hn : next = state.bob := by simpa [hr] using hs
                  cases result <;> simp [step, ht, hr, hn, hFailed]
  | drop id =>
      cases ht : takeEnvelope id state.queue <;> simpa [step, ht] using hFailed
  | replay id =>
      cases ht : findEnvelope id state.history <;> simpa [step, ht] using hFailed
  | reorderFirst id =>
      cases ht : takeEnvelope id state.queue <;> simpa [step, ht] using hFailed
  | forge id offset value =>
      cases ht : findEnvelope id state.queue <;> simpa [step, ht] using hFailed
  | failAgreement side =>
      cases side with
      | alice => simpa [step] using hFailed
      | bob => simp [step, failSession, agreementFailed]

/-- Alice remains terminal through an arbitrary remainder of the executable
    two-party schedule. -/
theorem failed_run_stays_failed_alice (view : CodewordView) (state : State)
    (actions : List Action) (hFailed : agreementFailed state.alice = true) :
    agreementFailed (run view state actions).1.alice = true := by
  induction actions generalizing state with
  | nil => simpa [run] using hFailed
  | cons action rest ih =>
      have nextFailed := failed_step_stays_failed_alice view state action hFailed
      simpa [run] using ih (step view state action).1 nextFailed

/-- Bob remains terminal through an arbitrary remainder of the executable
    two-party schedule. -/
theorem failed_run_stays_failed_bob (view : CodewordView) (state : State)
    (actions : List Action) (hFailed : agreementFailed state.bob = true) :
    agreementFailed (run view state actions).1.bob = true := by
  induction actions generalizing state with
  | nil => simpa [run] using hFailed
  | cons action rest ih =>
      have nextFailed := failed_step_stays_failed_bob view state action hFailed
      simpa [run] using ih (step view state action).1 nextFailed

/-- The old P6 trace's terminal-phase theorem is a projection of the
    operational schedule for Alice, rather than an independent `rfl` fact. -/
theorem observed_failed_run_alice (view : CodewordView) (state : State)
    (actions : List Action) (hFailed : agreementFailed state.alice = true) :
    (observe .alice (run view state actions).1).phase = .failed := by
  have hf := failed_run_stays_failed_alice view state actions hFailed
  simp [observe, phaseOf, hf]

/-- The symmetric projection for Bob. -/
theorem observed_failed_run_bob (view : CodewordView) (state : State)
    (actions : List Action) (hFailed : agreementFailed state.bob = true) :
    (observe .bob (run view state actions).1).phase = .failed := by
  have hf := failed_run_stays_failed_bob view state actions hFailed
  simp [observe, phaseOf, hf]

end Properties.LifecycleTrace
