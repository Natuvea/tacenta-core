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

/-- An accepted send advances the composed session but preserves its identities
    and role fields. A pending initiator keeps its initial wrapper until an
    authenticated peer answer arrives. -/
def sendOk (before after : Session) : Bool :=
  after != before
    && after.ourIdentityPublic == before.ourIdentityPublic
    && after.peerIdentityPublic == before.peerIdentityPublic
    && after.pendingInitial == before.pendingInitial
    && after.establishedEphemeral == before.establishedEphemeral
    && invariant before && invariant after

/-- An accepted receive advances the composed session. It may clear an
    initiator's pending wrapper, but cannot create one or change the responder
    marker. -/
def receiveOk (before after : Session) : Bool :=
  after != before
    && after.ourIdentityPublic == before.ourIdentityPublic
    && after.peerIdentityPublic == before.peerIdentityPublic
    && (before.pendingInitial.isNone || after.pendingInitial.isNone)
    && after.establishedEphemeral == before.establishedEphemeral
    && invariant before && invariant after

/-- Ordinary refusals leave the persisted session unchanged. Terminal Braid
    failure is deliberately not this relation because it commits failure. -/
def noOpOk (before after : Session) : Bool := before == after && invariant before

/-- The message that reveals a Braid failure may still authenticate and advance
    the ratchets, but commits the terminal Braid state. -/
def agreementFailedOk (before after : Session) : Bool :=
  after != before
    && after.ourIdentityPublic == before.ourIdentityPublic
    && after.peerIdentityPublic == before.peerIdentityPublic
    && after.establishedEphemeral == before.establishedEphemeral
    && after.braid.tag == BraidState.failedTag
    && invariant before && invariant after

end SessionOperations
end Model
