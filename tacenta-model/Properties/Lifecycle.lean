import Model.Lifecycle

/-!
# Properties of the executable Session lifecycle

These lift the public state and refusal rules out of the operation definitions.
They are model properties (T2), not claims that shipping Rust refines the model;
that relation belongs to the translated-session phases.
-/

namespace Properties.Lifecycle

open Model.Lifecycle

/-- An initiator that still has a pending initial clears it exactly when an
    authenticated decrypt succeeds. The premise excludes a responder or an
    initiator that has already received its first reply, where `none` is not a
    state change. -/
theorem pending_cleared_iff_ok (view : CodewordView) (oracle : Oracle)
    (session : Session) (message : Bytes)
    (hPending : session.pendingInitial.isSome = true) :
    (decrypt view oracle session message).session.pendingInitial = none ↔
      ∃ plaintext, (decrypt view oracle session message).result = .ok plaintext := by
  constructor
  · intro hCleared
    cases hr : (decrypt view oracle session message).result with
    | error reason =>
        have hs := decrypt_refusal_keeps_session view oracle session message reason hr
        rw [hs] at hCleared
        cases hp : session.pendingInitial with
        | none => simp [hp] at hPending
        | some pending => simp [hp] at hCleared
    | ok plaintext => exact ⟨plaintext, rfl⟩
  · rintro ⟨plaintext, hOk⟩
    exact decrypt_success_clears_pending view oracle session message plaintext hOk

/-- The exact repeated-initial recognition rule: both stored key fields must
    match byte for byte; the ciphertext and three identifiers are ignored. -/
theorem repeated_initial_accepted_iff (session : Session) (message inner : Bytes)
    (hInitial : messageType message = some .initial) :
    dispatchDecrypt session message = .ok inner ↔
      ∃ initial,
        Model.Messages.decodeInitialDetailed message = .ok initial
          ∧ repeatedInitial session initial = true
          ∧ initial.ratchetMessage = inner :=
  dispatchDecrypt_initial_ok_iff session message inner hInitial

/-- A terminal agreement state makes encryption refuse without another state
    transition or random draw. -/
theorem agreement_failed_encrypt_sticky (view : CodewordView) (oracle : Oracle)
    (session : Session) (plaintext : Bytes)
    (hFailed : agreementFailed session = true) :
    encrypt view oracle session plaintext =
      { session, result := .error .agreementFailed, oracle } :=
  encrypt_terminal_guard view oracle session plaintext hFailed

/-- Once dispatch has accepted the outer framing, a terminal agreement state
    makes decryption refuse without another state transition or random draw. -/
theorem agreement_failed_decrypt_sticky (view : CodewordView) (oracle : Oracle)
    (session : Session) (message inner : Bytes)
    (hDispatch : dispatchDecrypt session message = .ok inner)
    (hFailed : agreementFailed session = true) :
    decrypt view oracle session message =
      { session, result := .error .agreementFailed, oracle } := by
  simp [decrypt, hDispatch, decryptRatchet, hFailed]

/-- Outer-frame refusals can precede the terminal guard, so the public refusal
    need not always be `agreementFailed`. Whichever refusal is observed, a
    terminal Session remains byte-for-byte unchanged. -/
theorem agreement_failed_decrypt_keeps_session (view : CodewordView)
    (oracle : Oracle) (session : Session) (message : Bytes)
    (hFailed : agreementFailed session = true) :
    (decrypt view oracle session message).session = session := by
  cases hDispatch : dispatchDecrypt session message with
  | error reason => simp [decrypt, hDispatch]
  | ok inner => simp [decrypt, hDispatch, decryptRatchet, hFailed]

/-- Ordinary decrypt refusals are state no-ops at the executable Session
    boundary. Oracle draws remain observable separately. -/
theorem refusal_is_no_op (view : CodewordView) (oracle : Oracle)
    (session : Session) (message : Bytes) (reason : Refusal)
    (hRefused : (decrypt view oracle session message).result = .error reason) :
    (decrypt view oracle session message).session = session :=
  decrypt_refusal_keeps_session view oracle session message reason hRefused

/-- Responder-establishment refusals are no-ops on the whole prekey store. -/
theorem responder_refusal_is_no_op (view : CodewordView) (oracle : Oracle)
    (identity : Identity) (store : PrekeyStore) (message : Bytes) (reason : Refusal)
    (hRefused : (establishResponder view oracle identity store message).result =
      .error reason) :
    (establishResponder view oracle identity store message).store = store :=
  establishResponder_refusal_keeps_store view oracle identity store message reason hRefused

end Properties.Lifecycle
