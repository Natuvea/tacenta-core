/-
Model.Lifecycle: executable orchestration for the public session operations.

This first slice fixes the primitive boundary and its randomness discipline.
The lifecycle functions consume `draws` from the head and return the oracle
with the unused suffix. Every primitive result is a function of the complete
argument list passed at the boundary. The later refinement relation can
therefore say that Rust and the model made the same call, rather than merely
that they happened to receive the same result.

The primitive algorithms are deliberately outside this model. The theorem is
intended to quantify over every oracle; real-crypto vectors instantiate one.
-/
import Model.PersistedState

namespace Model.Lifecycle

abbrev Bytes := List UInt8
abbrev Key := Model.State.Key
abbrev Iv := Bytes

/-- Results supplied by the trusted primitive boundary.

    `draws` is ordered. Operations that need randomness consume its head and
    return the oracle containing its tail. `kemEncaps` and `sigSign` take that
    draw explicitly, so using the wrong draw or calling them in the wrong order
    changes the model result. -/
structure Oracle where
  draws : List Key
  dhPublic : Key → Key
  dhAgree : Key → Key → Option Key
  aeadSeal : Key → Key → Iv → Bytes → Bytes → Bytes
  aeadOpen : Key → Key → Iv → Bytes → Bytes → Option Bytes
  kemEncaps : Bytes → Key → Option (Bytes × Key)
  kemDecaps : Bytes → Bytes → Option Key
  sigVerify : Key → Bytes → Bytes → Bool
  sigSign : Key → Bytes → Key → Bytes

/-- Consume one named 32-byte random draw. Exhaustion is a model refusal rather
    than an invented value; callers decide which public refusal it maps to. -/
def takeDraw (oracle : Oracle) : Option (Key × Oracle) :=
  match oracle.draws with
  | [] => none
  | draw :: rest => some (draw, { oracle with draws := rest })

@[simp] theorem takeDraw_empty (oracle : Oracle) (h : oracle.draws = []) :
    takeDraw oracle = none := by
  simp [takeDraw, h]

@[simp] theorem takeDraw_cons (oracle : Oracle) (draw : Key) (rest : List Key)
    (h : oracle.draws = draw :: rest) :
    takeDraw oracle = some (draw, { oracle with draws := rest }) := by
  simp [takeDraw, h]

/-- Consuming a draw changes no primitive interpretation. This is the small
    frame fact used whenever an operation threads the remaining trace onward. -/
theorem takeDraw_keeps_dhPublic (oracle oracle' : Oracle) (draw : Key)
    (h : takeDraw oracle = some (draw, oracle')) :
    oracle'.dhPublic = oracle.dhPublic := by
  cases hd : oracle.draws with
  | nil => simp [takeDraw, hd] at h
  | cons head tail =>
      simp only [takeDraw, hd, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]

/-- The `random32` boundary call. Named separately from `takeDraw` so
    refinement can relate that shipping function to this exact trace step. -/
def random32 (oracle : Oracle) : Option (Key × Oracle) := takeDraw oracle

/-- Encapsulation consumes exactly one draw, then calls the oracle with the KEM
    public key and that draw. A primitive refusal still consumes the draw: the
    shipping RNG call happened before the primitive returned its result. -/
def kemEncapsulate (oracle : Oracle) (publicKey : Bytes) :
    Option (Option (Bytes × Key) × Oracle) := do
  let (draw, rest) ← takeDraw oracle
  some (oracle.kemEncaps publicKey draw, rest)

/-- Signing consumes exactly one draw and binds the result to the secret,
    message and draw supplied to the primitive. -/
def sign (oracle : Oracle) (secret : Key) (message : Bytes) :
    Option (Bytes × Oracle) := do
  let (draw, rest) ← takeDraw oracle
  some (oracle.sigSign secret message draw, rest)

theorem kemEncapsulate_cons (oracle : Oracle) (draw : Key) (rest : List Key)
    (publicKey : Bytes) (h : oracle.draws = draw :: rest) :
    kemEncapsulate oracle publicKey =
      some (oracle.kemEncaps publicKey draw, { oracle with draws := rest }) := by
  simp [kemEncapsulate, takeDraw, h]

theorem sign_cons (oracle : Oracle) (draw : Key) (rest : List Key)
    (secret : Key) (message : Bytes) (h : oracle.draws = draw :: rest) :
    sign oracle secret message =
      some (oracle.sigSign secret message draw, { oracle with draws := rest }) := by
  simp [sign, takeDraw, h]

/-! ## Repeated initial recognition

An established responder retains the initiator's ephemeral. An initial wrapper
reaches the inner ratchet message exactly when that retained value and the
stored peer identity match the wrapper byte for byte. The KEM ciphertext and
the three prekey identifiers are deliberately absent from this predicate.
-/

abbrev PendingInitial := Model.PersistedState.SessionState.PendingInitial

/-- The executable session state. It has the shipping session's fields, but its
    Braid is the operational `Model.Braid.BraidState` rather than the stored
    format's opaque byte fields. Most persisted Braid states deliberately have
    no generic conversion back to the operational model: their KEM internals
    are delegated to the implementation. Refinement relates this field directly
    through `BraidT3.StateRefines`; persistence is a separate relation. -/
structure Session where
  triple : Model.Triple.State
  braid : Model.Braid.BraidState
  ratchetPrivate : Bytes
  identityAd : Bytes
  ourIdentityPublic : Bytes
  peerIdentityPublic : Bytes
  pendingInitial : Option PendingInitial
  establishedEphemeral : Option Bytes

abbrev Initial := Model.Messages.Initial

/-! ## Public refusal vocabulary

`error-handling.md` makes the refusal behaviour normative while leaving the
Rust error type to the implementation. These constructors mirror that public
type so T3 can cover every concrete `Err` branch without making the names part
of the protocol. `ceiling` is the model's explicit result outside theorem
headroom; no Rust `Error` maps to it on a discharged proof path.
-/

inductive RatchetRefusal where
  | tooManySkipped | skippedStoreFull | noSendingChain | noReceivingChain
  | outOfOrder | chainExhausted
  deriving Repr, DecidableEq, Inhabited

inductive SparseRefusal where
  | epochOutOfOrder | noChain | chainRetired | tooManySkipped
  | skippedStoreFull | outOfOrder | chainExhausted
  deriving Repr, DecidableEq, Inhabited

inductive TripleRefusal where
  | classical (reason : RatchetRefusal)
  | postQuantum (reason : SparseRefusal)
  deriving Repr, DecidableEq, Inhabited

inductive HandshakeRefusal where
  | badSignedPrekeySignature | badKemPrekeySignature
  | nonContributoryAgreement
  deriving Repr, DecidableEq, Inhabited

inductive DecodeRefusal where
  | unknownVersion | wrongType | tooShort | lengthOverrun
  deriving Repr, DecidableEq, Inhabited

inductive Refusal where
  | triple (reason : TripleRefusal)
  | handshake (reason : HandshakeRefusal)
  | kem
  | decode (reason : DecodeRefusal)
  | badEncoding
  | inconsistentBundle
  | unexpectedIdentity
  | unknownPrekeyId
  | aead
  | notARepeatedInitial
  | replayedLastResort
  | legacyLastResortRecord
  | lastResortRecordFull
  | agreementFailed
  | ceiling
  deriving Repr, DecidableEq, Inhabited

/-- Whether an initial wrapper is the repeat belonging to this responder
    session (session-establishment.md, Receiving the initial message). -/
def repeatedInitial (session : Session) (initial : Initial) : Bool :=
  match session.establishedEphemeral with
  | none => false
  | some ephemeral =>
      ephemeral == initial.ephemeral
        && initial.identity == Model.PersistedState.SessionState.encodeEc session.peerIdentityPublic

theorem repeatedInitial_iff (session : Session) (initial : Initial) :
    repeatedInitial session initial = true ↔
      ∃ ephemeral, session.establishedEphemeral = some ephemeral
        ∧ ephemeral = initial.ephemeral
        ∧ initial.identity =
          Model.PersistedState.SessionState.encodeEc session.peerIdentityPublic := by
  cases h : session.establishedEphemeral with
  | none => simp [repeatedInitial, h]
  | some ephemeral => simp [repeatedInitial, h]

/-- Recognition does not inspect the KEM ciphertext, identifiers or inner
    ratchet message. This is an intentional part of the protocol rule. -/
theorem repeatedInitial_ignores_other_fields (session : Session) (initial : Initial)
    (kemCiphertext ratchetMessage : Bytes) (signedPrekeyId oneTimeId kemPrekeyId : UInt32) :
    repeatedInitial session
      { initial with kemCiphertext, signedPrekeyId, oneTimeId, kemPrekeyId, ratchetMessage }
      = repeatedInitial session initial := by
  simp [repeatedInitial]

end Model.Lifecycle
