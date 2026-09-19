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
import Model.CompositeHeader

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
  braidKem : Model.Braid.Kem
  dhPublic : Key → Key
  dhAgree : Key → Key → Option Key
  aeadSeal : Key → Key → Iv → Bytes → Bytes → Bytes
  aeadOpen : Key → Key → Iv → Bytes → Bytes → Option Bytes
  kemEncaps : Bytes → Key → Option (Bytes × Key)
  kemDecaps : Bytes → Bytes → Option Key
  sigVerify : Key → Bytes → Bytes → Bool
  sigSign : Key → Bytes → Key → Bytes

/-- Executable view of the erasure codeword relation already used by the Braid
    refinement. A wire codeword does not reveal the Braid model's ghost source,
    and a model chunk does not contain its wire bytes. The current Braid state
    is part of each complete argument list because it supplies the encoder or
    decoder context. `CodewordViewOf` in the refinement layer will constrain
    these choices by the existing `BraidT3.CodewordOf` relation. -/
structure CodewordView where
  receive : Model.Braid.BraidState → UInt16 → Bytes → Model.Braid.Chunk
  send : Model.Braid.BraidState → Model.Braid.Chunk → Model.CompositeHeader.Codeword

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

/-- The two Braid send states that make a fresh 32-byte random draw. Other
    states accept a `rand` argument in the leaf model but do not inspect it, so
    the lifecycle must not consume a caller draw there. -/
def braidSendNeedsDraw : Model.Braid.BraidState → Bool
  | .keysUnsampled .. => true
  | .headerReceived .. => true
  | _ => false

/-- Interpret the Braid's 32-byte draw as the natural-number randomness used
    by its existing model. This is the same complete byte string, little-endian,
    rather than a fresh or reordered value. -/
def braidRandomness (draw : Key) : Nat := Model.Messages.leValue draw

/-- Run the agreement send and consume exactly the randomness the shipping
    state consumes. The KEM record is the existing Braid model boundary carried
    by the oracle; it is not an additional shipping primitive. -/
def sendAgreement (oracle : Oracle) (state : Model.Braid.BraidState) :
    Option ((Option Model.Braid.Msg × Nat × Option Model.Braid.Output ×
      Model.Braid.BraidState) × Oracle) :=
  if braidSendNeedsDraw state then do
    let (draw, rest) ← takeDraw oracle
    some (Model.Braid.send oracle.braidKem (braidRandomness draw) state, rest)
  else
    some (Model.Braid.send oracle.braidKem 0 state, oracle)

theorem sendAgreement_no_draw (oracle : Oracle) (state : Model.Braid.BraidState)
    (h : braidSendNeedsDraw state = false) :
    sendAgreement oracle state = some (Model.Braid.send oracle.braidKem 0 state, oracle) := by
  simp [sendAgreement, h]

theorem sendAgreement_draw (oracle : Oracle) (state : Model.Braid.BraidState)
    (draw : Key) (rest : List Key) (hn : braidSendNeedsDraw state = true)
    (hd : oracle.draws = draw :: rest) :
    sendAgreement oracle state =
      some (Model.Braid.send oracle.braidKem (braidRandomness draw) state,
        { oracle with draws := rest }) := by
  simp [sendAgreement, hn, takeDraw, hd]

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

abbrev DecodeRefusal := Model.Messages.DecodeRefusal

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

def ratchetSendRefusalOf : Model.Ratchet.SendRefusal → RatchetRefusal
  | .noSendingChain => .noSendingChain
  | .chainExhausted => .chainExhausted

def sparseSendRefusalOf : Model.SparseRatchet.SendRefusal → SparseRefusal
  | .epochOutOfOrder => .epochOutOfOrder
  | .noChain => .noChain
  | .chainRetired => .chainRetired
  | .chainExhausted => .chainExhausted

def tripleSendRefusalOf : Model.Triple.SendRefusal → Refusal
  | .classical reason => .triple (.classical (ratchetSendRefusalOf reason))
  | .postQuantum reason => .triple (.postQuantum (sparseSendRefusalOf reason))

theorem ratchetSendRefusalOf_injective : Function.Injective ratchetSendRefusalOf := by
  intro left right h
  cases left <;> cases right <;> simp [ratchetSendRefusalOf] at h ⊢

theorem sparseSendRefusalOf_injective : Function.Injective sparseSendRefusalOf := by
  intro left right h
  cases left <;> cases right <;> simp [sparseSendRefusalOf] at h ⊢

theorem tripleSendRefusalOf_injective : Function.Injective tripleSendRefusalOf := by
  intro left right h
  cases left with
  | classical left =>
      cases right with
      | classical right =>
          simp [tripleSendRefusalOf] at h
          exact congrArg Model.Triple.SendRefusal.classical
            (ratchetSendRefusalOf_injective h)
      | postQuantum right => simp [tripleSendRefusalOf] at h
  | postQuantum left =>
      cases right with
      | classical right => simp [tripleSendRefusalOf] at h
      | postQuantum right =>
          simp [tripleSendRefusalOf] at h
          exact congrArg Model.Triple.SendRefusal.postQuantum
            (sparseSendRefusalOf_injective h)

def agreementFailed (session : Session) : Bool :=
  match session.braid with
  | .failed => true
  | _ => false

theorem agreementFailed_iff (session : Session) :
    agreementFailed session = true ↔ session.braid = .failed := by
  cases h : session.braid <;> simp [agreementFailed, h]

inductive MessageType where
  | ratchet | initial
  deriving Repr, DecidableEq, Inhabited

/-- Read only the two framing bytes used for session dispatch. A malformed or
    unknown frame returns `none`; `decrypt` then sends it to the ratchet decoder,
    which supplies the public decode refusal. -/
def messageType : Bytes → Option MessageType
  | version :: ty :: _ =>
      if version != Model.Messages.version then none
      else if ty == Model.Messages.typeRatchet then some .ratchet
      else if ty == Model.Messages.typeInitial then some .initial
      else none
  | _ => none

theorem messageType_initial_iff (bytes : Bytes) :
    messageType bytes = some .initial ↔
      bytes.length ≥ 2 ∧ bytes[0]? = some Model.Messages.version
        ∧ bytes[1]? = some Model.Messages.typeInitial := by
  cases bytes with
  | nil => simp [messageType]
  | cons first rest =>
      cases rest with
      | nil => simp [messageType]
      | cons second tail =>
          simp only [messageType, List.length_cons, List.getElem?_cons_zero,
            List.getElem?_cons_succ, ge_iff_le]
          by_cases hv : first = Model.Messages.version <;>
            by_cases hr : second = 0x01 <;>
            by_cases hi : second = 0x02 <;>
            simp [hv, hr, hi, Model.Messages.typeRatchet, Model.Messages.typeInitial]

/-! ## Composite-header adapters

The session owns the correspondence between the wire header, the Triple
Ratchet header and the Braid message. Codeword payloads cross the explicit
`CodewordView`; all remaining fields are direct, total conversions.
-/

def braidTypeOf : Model.CompositeHeader.AgreementType → Model.Braid.MsgType
  | .none => .none
  | .hdr => .hdr
  | .ek => .ek
  | .ekCt1Ack => .ekCt1Ack
  | .ct1 => .ct1
  | .ct2 => .ct2

/-- The Braid model contains `ct1Ack` for the published state machine, but the
    shipping wire format deliberately gives it no byte because no send
    transition emits it. All emitted message types have a wire image. -/
def compositeTypeOf : Model.Braid.MsgType → Option Model.CompositeHeader.AgreementType
  | .none => some .none
  | .hdr => some .hdr
  | .ek => some .ek
  | .ekCt1Ack => some .ekCt1Ack
  | .ct1Ack => none
  | .ct1 => some .ct1
  | .ct2 => some .ct2

theorem compositeTypeOf_braidTypeOf (ty : Model.CompositeHeader.AgreementType) :
    compositeTypeOf (braidTypeOf ty) = some ty := by
  cases ty <;> rfl

def braidMessageOf (view : CodewordView) (state : Model.Braid.BraidState)
    (header : Model.CompositeHeader.Composite) : Model.Braid.Msg :=
  { epoch := header.agEpoch.toNat
    type := braidTypeOf header.agType
    data := header.agChunk.map (fun chunk => view.receive state chunk.index chunk.data) }

def tripleHeaderOf (header : Model.CompositeHeader.Composite) : Model.Triple.Header :=
  { dr :=
      { dh := header.dh
        pn := header.pn.toNat
        n := header.n.toNat }
    epoch := header.pqEpoch.toNat
    pqN := header.pqN.toNat }

/-- Build the wire header for a message emitted by the two operational models.
    `none` is reachable only for the Braid model's unencodable `ct1Ack`, which
    its send transition never produces. -/
def compositeOf (view : CodewordView) (braidBefore : Model.Braid.BraidState)
    (header : Model.Triple.Header) (message : Model.Braid.Msg) :
    Option Model.CompositeHeader.Composite := do
  let ty ← compositeTypeOf message.type
  some
    { dh := header.dr.dh
      pn := UInt32.ofNat header.dr.pn
      n := UInt32.ofNat header.dr.n
      pqEpoch := UInt64.ofNat header.epoch
      pqN := UInt64.ofNat header.pqN
      agEpoch := UInt64.ofNat message.epoch
      agType := ty
      agChunk := message.data.map (view.send braidBefore) }

theorem braidMessageOf_fields (view : CodewordView) (state : Model.Braid.BraidState)
    (header : Model.CompositeHeader.Composite) :
    (braidMessageOf view state header).epoch = header.agEpoch.toNat
      ∧ (braidMessageOf view state header).type = braidTypeOf header.agType := by
  exact ⟨rfl, rfl⟩

theorem tripleHeaderOf_fields (header : Model.CompositeHeader.Composite) :
    (tripleHeaderOf header).dr.dh = header.dh
      ∧ (tripleHeaderOf header).dr.pn = header.pn.toNat
      ∧ (tripleHeaderOf header).dr.n = header.n.toNat
      ∧ (tripleHeaderOf header).epoch = header.pqEpoch.toNat
      ∧ (tripleHeaderOf header).pqN = header.pqN.toNat := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

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

/-! ## Established-session dispatch

`Session.decrypt` first removes a repeated initial wrapper, when present, and
passes every other frame unchanged to the ratchet decoder. Keeping this step
separate makes its refusal and frame behaviour visible before the much larger
receive transition is introduced.
-/

/-- Select the bytes that an established session gives to its ratchet
    receiver. An initial frame must decode canonically and name this exact
    established session; ratchet and unrecognised framing is passed through so
    the ratchet decoder supplies the final public decode refusal. -/
def dispatchDecrypt (session : Session) (message : Bytes) : Except Refusal Bytes :=
  match messageType message with
  | some .initial =>
      match Model.Messages.decodeInitialDetailed message with
      | .error reason => .error (.decode reason)
      | .ok initial =>
          if repeatedInitial session initial then .ok initial.ratchetMessage
          else .error .notARepeatedInitial
  | _ => .ok message

theorem dispatchDecrypt_passthrough (session : Session) (message : Bytes)
    (h : messageType message ≠ some .initial) :
    dispatchDecrypt session message = .ok message := by
  cases ht : messageType message with
  | none => simp [dispatchDecrypt, ht]
  | some kind =>
      cases kind with
      | ratchet => simp [dispatchDecrypt, ht]
      | initial => exact (h ht).elim

theorem dispatchDecrypt_decode_refusal (session : Session) (message : Bytes)
    (reason : DecodeRefusal) (ht : messageType message = some .initial)
    (hd : Model.Messages.decodeInitialDetailed message = .error reason) :
    dispatchDecrypt session message = .error (.decode reason) := by
  simp [dispatchDecrypt, ht, hd]

theorem dispatchDecrypt_repeat (session : Session) (message : Bytes) (initial : Initial)
    (ht : messageType message = some .initial)
    (hd : Model.Messages.decodeInitialDetailed message = .ok initial)
    (hr : repeatedInitial session initial = true) :
    dispatchDecrypt session message = .ok initial.ratchetMessage := by
  simp [dispatchDecrypt, ht, hd, hr]

theorem dispatchDecrypt_not_repeat (session : Session) (message : Bytes) (initial : Initial)
    (ht : messageType message = some .initial)
    (hd : Model.Messages.decodeInitialDetailed message = .ok initial)
    (hr : repeatedInitial session initial = false) :
    dispatchDecrypt session message = .error .notARepeatedInitial := by
  simp [dispatchDecrypt, ht, hd, hr]

/-- Complete success condition for an initial frame: it has one canonical
    decode, belongs to this established session, and contributes exactly its
    embedded ratchet bytes. -/
theorem dispatchDecrypt_initial_ok_iff (session : Session) (message inner : Bytes)
    (ht : messageType message = some .initial) :
    dispatchDecrypt session message = .ok inner ↔
      ∃ initial, Model.Messages.decodeInitialDetailed message = .ok initial
        ∧ repeatedInitial session initial = true
        ∧ initial.ratchetMessage = inner := by
  cases hd : Model.Messages.decodeInitialDetailed message with
  | error reason => simp [dispatchDecrypt, ht, hd]
  | ok initial =>
      cases hr : repeatedInitial session initial <;>
        simp [dispatchDecrypt, ht, hd, hr]

/-! ## Receive preparation

This is the complete non-mutating prefix of `Session.decrypt`: remove a valid
repeat wrapper, apply the terminal agreement guard, and decode the composite
ratchet frame. The remaining ratchet/agreement/AEAD transition is added after
the codeword view and leaf refusal results are frozen.
-/

abbrev DecodedRatchet := Model.CompositeHeader.Composite × Bytes

def prepareDecrypt (session : Session) (message : Bytes) :
    Except Refusal DecodedRatchet :=
  match dispatchDecrypt session message with
  | .error reason => .error reason
  | .ok inner =>
      if agreementFailed session then .error .agreementFailed
      else
        match Model.CompositeHeader.decodeDetailed inner with
        | .error reason => .error (.decode reason)
        | .ok decoded => .ok decoded

theorem prepareDecrypt_dispatch_refusal (session : Session) (message : Bytes)
    (reason : Refusal) (h : dispatchDecrypt session message = .error reason) :
    prepareDecrypt session message = .error reason := by
  simp [prepareDecrypt, h]

theorem prepareDecrypt_failed (session : Session) (message inner : Bytes)
    (hd : dispatchDecrypt session message = .ok inner)
    (hf : agreementFailed session = true) :
    prepareDecrypt session message = .error .agreementFailed := by
  simp [prepareDecrypt, hd, hf]

theorem prepareDecrypt_decode_refusal (session : Session) (message inner : Bytes)
    (reason : DecodeRefusal) (hd : dispatchDecrypt session message = .ok inner)
    (hf : agreementFailed session = false)
    (hw : Model.CompositeHeader.decodeDetailed inner = .error reason) :
    prepareDecrypt session message = .error (.decode reason) := by
  simp [prepareDecrypt, hd, hf, hw]

theorem prepareDecrypt_ok (session : Session) (message inner : Bytes)
    (decoded : DecodedRatchet) (hd : dispatchDecrypt session message = .ok inner)
    (hf : agreementFailed session = false)
    (hw : Model.CompositeHeader.decodeDetailed inner = .ok decoded) :
    prepareDecrypt session message = .ok decoded := by
  simp [prepareDecrypt, hd, hf, hw]

end Model.Lifecycle
