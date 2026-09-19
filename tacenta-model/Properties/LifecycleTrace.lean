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

end Properties.LifecycleTrace
