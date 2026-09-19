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

/-! ## Repeated initial recognition

An established responder retains the initiator's ephemeral. An initial wrapper
reaches the inner ratchet message exactly when that retained value and the
stored peer identity match the wrapper byte for byte. The KEM ciphertext and
the three prekey identifiers are deliberately absent from this predicate.
-/

abbrev Session := Model.PersistedState.SessionState.Session
abbrev Initial := Model.Messages.Initial

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
