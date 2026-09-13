import Model.PersistedState

/-!
# Session-establishment operation checks

The concrete lifecycle code performs signatures, KEM encapsulation, curve
agreement and AEAD authentication.  This P6 boundary model receives the
accepted persisted session those operations produced.  It checks the durable
facts that remain after those opaque verdicts: the role, identity binding,
pending-initial state, and the composed session invariant.
-/

namespace Model
namespace SessionOperations

open PersistedState
open PersistedState.SessionState

/-- A successful initiator establishment creates an initiator session with one
    pending initial wrapper.  The pending wrapper is what binds the later first
    send to the bundle selected during establishment. -/
def initiatorPendingOk (ourIdentity peerIdentity : Bytes) (after : Session) : Bool :=
  after.ourIdentityPublic == ourIdentity
    && after.peerIdentityPublic == peerIdentity
    && after.pendingInitial.isSome
    && after.establishedEphemeral.isNone
    && isInitiator after
    && invariant after

/-- A successful responder establishment creates a responder session.  The
    initial wrapper has already authenticated and been consumed, so no pending
    initiator material remains; the responder instead retains the establishing
    ephemeral key for repeated-initial recognition. -/
def responderEstablishedOk (ourIdentity peerIdentity : Bytes) (after : Session) : Bool :=
  after.ourIdentityPublic == ourIdentity
    && after.peerIdentityPublic == peerIdentity
    && after.pendingInitial.isNone
    && after.establishedEphemeral.isSome
    && !(isInitiator after)
    && invariant after

end SessionOperations
end Model
