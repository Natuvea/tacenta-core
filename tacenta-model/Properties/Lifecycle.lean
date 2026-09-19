import Model.Lifecycle

/-!
# Properties of the executable Session lifecycle

These lift the public state and refusal rules out of the operation definitions.
They are model properties (T2), not claims that shipping Rust refines the model;
that relation belongs to the translated-session phases.
-/

namespace Properties.Lifecycle

open Model.Lifecycle

/-- Identity orientation and responder role marker never change after a
    Session has been constructed. -/
def identityFrame (before after : Session) : Prop :=
  after.ourIdentityPublic = before.ourIdentityPublic
    ∧ after.peerIdentityPublic = before.peerIdentityPublic
    ∧ after.establishedEphemeral = before.establishedEphemeral

/-! ## Responder key lookup -/

/-- The current signed prekey is selected by its exact identifier. -/
theorem signed_lookup_current (store : PrekeyStore) (id : Nat)
    (hId : id = store.state.signedPrekeyId) :
    responderSignedPrekeySecret store id = some store.state.signedPrekeySecret := by
  simp [responderSignedPrekeySecret, hId]

/-- A retained signed prekey remains selectable after rotation. -/
theorem signed_lookup_retired (store : PrekeyStore) (id previousId : Nat)
    (secret signature : Bytes)
    (hCurrent : id ≠ store.state.signedPrekeyId)
    (hPrevious : store.state.previousSigned = some (secret, previousId, signature))
    (hId : id = previousId) :
    responderSignedPrekeySecret store id = some secret := by
  subst id
  simp [responderSignedPrekeySecret, hCurrent, hPrevious]

/-- With no retained signed prekey, an identifier other than the current one
    is unknown. -/
theorem signed_lookup_unknown (store : PrekeyStore) (id : Nat)
    (hCurrent : id ≠ store.state.signedPrekeyId)
    (hPrevious : store.state.previousSigned = none) :
    responderSignedPrekeySecret store id = none := by
  simp [responderSignedPrekeySecret, hCurrent, hPrevious]

/-- A legacy block is checked before the current last-resort KEM key can be
    used. -/
theorem kem_lookup_current_legacy_blocked (store : PrekeyStore) (id : Nat)
    (hId : id = store.state.kemId)
    (hBlocked : store.legacyLastResortBlocked.contains id = true) :
    responderKemPair store id = .error .legacyLastResortRecord := by
  subst id
  have hb : store.state.kemId ∈ store.legacyLastResortBlocked := by
    simpa using hBlocked
  simp [responderKemPair, hb]

/-- The unblocked current KEM key is identified as a last-resort key. -/
theorem kem_lookup_current (store : PrekeyStore) (id : Nat)
    (hId : id = store.state.kemId)
    (hAllowed : store.legacyLastResortBlocked.contains id = false) :
    responderKemPair store id = .ok (store.state.kemPair, true) := by
  subst id
  have hb : store.state.kemId ∉ store.legacyLastResortBlocked := by
    simpa using hAllowed
  simp [responderKemPair, hb]

/-- The unblocked retained KEM key is also a last-resort key. -/
theorem kem_lookup_retired (store : PrekeyStore) (id previousId : Nat)
    (pair signature : Bytes)
    (hCurrent : id ≠ store.state.kemId)
    (hPrevious : store.state.previousKem = some (pair, previousId, signature))
    (hId : id = previousId)
    (hAllowed : store.legacyLastResortBlocked.contains id = false) :
    responderKemPair store id = .ok (pair, true) := by
  subst id
  have hb : previousId ∉ store.legacyLastResortBlocked := by
    simpa using hAllowed
  simp [responderKemPair, hCurrent, hPrevious, hb]

/-- A named one-time KEM key is distinguished from current and retained
    last-resort keys. -/
theorem kem_lookup_one_time (store : PrekeyStore) (id : Nat)
    (entry : Nat × (Bytes × Bytes))
    (hCurrent : id ≠ store.state.kemId)
    (hPrevious : store.state.previousKem = none)
    (hEntry : store.state.kemOneTime.find? (fun candidate => candidate.1 = id) =
      some entry) :
    responderKemPair store id = .ok (entry.2.1, false) := by
  simp [responderKemPair, hCurrent, hPrevious, hEntry]

/-- If neither a current, retained nor one-time KEM key has the identifier,
    lookup returns the exact public refusal. -/
theorem kem_lookup_unknown (store : PrekeyStore) (id : Nat)
    (hCurrent : id ≠ store.state.kemId)
    (hPrevious : store.state.previousKem = none)
    (hEntry : store.state.kemOneTime.find? (fun candidate => candidate.1 = id) = none) :
    responderKemPair store id = .error .unknownPrekeyId := by
  simp [responderKemPair, hCurrent, hPrevious, hEntry]

/-- The sentinel curve-prekey identifier selects the no-DH4 path. -/
theorem curve_lookup_absent (store : PrekeyStore) :
    responderOneTimeSecret store
      Model.PersistedState.PrekeyStoreState.absentId = .ok none := by
  simp [responderOneTimeSecret]

/-- An absent named curve prekey returns the same exact unknown-id refusal as
    other missing responder keys. -/
theorem curve_lookup_unknown (store : PrekeyStore) (id : Nat)
    (hId : id ≠ Model.PersistedState.PrekeyStoreState.absentId)
    (hEntry : store.state.oneTime.find? (fun candidate => candidate.1 = id) = none) :
    responderOneTimeSecret store id = .error .unknownPrekeyId := by
  simp [responderOneTimeSecret, hId, hEntry]

/-- A repeated SK-bound identity is the first last-resort refusal, even when
    the named key's budget is also full. -/
theorem replayed_last_resort_refused (store : PrekeyStore) (kemId : Nat)
    (sharedSecret : Key)
    (hReplay : store.state.seen.any
      (fun entry => entry.2 = lastResortFingerprint sharedSecret) = true) :
    lastResortReplayCheck store kemId sharedSecret true = .error .replayedLastResort := by
  simp [lastResortReplayCheck, hReplay]

/-- A fresh identity at a spent per-key budget is refused without producing a
    fingerprint for later commit. -/
theorem full_last_resort_record_refused (store : PrekeyStore) (kemId : Nat)
    (sharedSecret : Key)
    (hFresh : store.state.seen.any
      (fun entry => entry.2 = lastResortFingerprint sharedSecret) = false)
    (hFull : Model.PersistedState.PrekeyStoreState.maxLastResortSeen ≤
      (store.state.seen.filter (fun entry => entry.1 = kemId)).length) :
    lastResortReplayCheck store kemId sharedSecret true =
      .error .lastResortRecordFull := by
  simp [lastResortReplayCheck, hFresh, hFull]

/-- A one-time KEM path neither consults nor modifies the replay record. -/
theorem one_time_path_has_no_replay_record (store : PrekeyStore) (kemId : Nat)
    (sharedSecret : Key) :
    lastResortReplayCheck store kemId sharedSecret false = .ok none := by
  simp [lastResortReplayCheck]

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

/-- Encrypt preserves both identity bindings, the responder marker and the
    pending initial wrapper on every branch. -/
theorem encrypt_frame (view : CodewordView) (oracle : Oracle)
    (session : Session) (plaintext : Bytes) :
    identityFrame session (encrypt view oracle session plaintext).session
      ∧ (encrypt view oracle session plaintext).session.pendingInitial =
        session.pendingInitial := by
  grind (config := { gen := 20, splits := 30 }) [encrypt, identityFrame]

/-- The authenticated ratchet transaction can replace ratchet keys and both
    ratchet states, but it cannot change identities, role or pending wrapper. -/
theorem decryptRatchet_frame (view : CodewordView) (oracle : Oracle)
    (session : Session) (message : Bytes) :
    identityFrame session (decryptRatchet view oracle session message).session
      ∧ (decryptRatchet view oracle session message).session.pendingInitial =
        session.pendingInitial := by
  grind (config := { gen := 30, splits := 50 }) [decryptRatchet, identityFrame]

/-- Public decrypt preserves identities and the responder marker on every
    branch. Its only wrapper-field change is the separately proved successful
    clearing of `pendingInitial`. -/
theorem decrypt_identity_frame (view : CodewordView) (oracle : Oracle)
    (session : Session) (message : Bytes) :
    identityFrame session (decrypt view oracle session message).session := by
  cases hd : dispatchDecrypt session message with
  | error reason => simp [decrypt, hd, identityFrame]
  | ok inner =>
      have hf := (decryptRatchet_frame view oracle session inner).1
      cases hr : decryptRatchet view oracle session inner with
      | mk next result remaining =>
          cases result <;> simpa [decrypt, hd, hr, identityFrame] using hf

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

/-- A successful responder opening has exactly one durable store effect: the
    named one-time entries are consumed, or the accepted last-resort replay
    identity is appended, using the values fixed by the read-only preparation
    phase. No unmentioned store field can change. -/
theorem responder_success_store_effect (view : CodewordView) (oracle : Oracle)
    (identity : Identity) (store : PrekeyStore) (message : Bytes)
    (value : Session × Bytes)
    (hOk : (establishResponder view oracle identity store message).result = .ok value) :
    ∃ prepared plaintext,
      prepareResponder oracle identity store message = .ok prepared
        ∧ (decryptRatchet view oracle prepared.session prepared.ratchetMessage).result =
          .ok plaintext
        ∧ value =
          ((decryptRatchet view oracle prepared.session prepared.ratchetMessage).session,
            plaintext)
        ∧ (establishResponder view oracle identity store message).store =
          consumeResponderPrekeys store prepared.oneTimeId prepared.kemId
            prepared.lastResort prepared.fingerprint := by
  cases hp : prepareResponder oracle identity store message with
  | error reason => simp [establishResponder, hp] at hOk
  | ok prepared =>
      cases hr : decryptRatchet view oracle prepared.session prepared.ratchetMessage with
      | mk next result remaining =>
          cases result with
          | error reason => simp [establishResponder, hp, finishResponderReceive, hr] at hOk
          | ok plaintext =>
              refine ⟨prepared, plaintext, rfl, ?_, ?_, ?_⟩
              · simp [hr]
              · simpa [establishResponder, hp, finishResponderReceive, hr] using hOk.symm
              · simp [establishResponder, hp, finishResponderReceive, hr]

/-- Successful initiator establishment binds the two identities, carries the
    selected bundle identifiers in a pending initial wrapper, and has no
    responder replay marker. -/
theorem initiator_success_shape (oracle : Oracle) (identity : Identity)
    (bundle : Bundle) (expectedIdentity : Key) (session : Session)
    (hOk : (establishInitiator oracle identity bundle expectedIdentity).result =
      .ok session) :
    session.ourIdentityPublic = identity.publicKey
      ∧ session.peerIdentityPublic = bundle.identityKey
      ∧ session.pendingInitial.isSome = true
      ∧ session.establishedEphemeral = none
      ∧ session.pendingInitial.map (fun pending =>
          (pending.signedPrekeyId, pending.oneTimePrekeyId, pending.kemPrekeyId)) =
        some (bundle.signedPrekeyId.toNat, bundle.oneTimeId.toNat,
          bundle.kemPrekeyId.toNat) := by
  grind (config := { gen := 20, splits := 30 }) [establishInitiator]

end Properties.Lifecycle
