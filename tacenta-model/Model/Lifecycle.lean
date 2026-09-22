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
import Model.SessionEstablishment

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

def ratchetReceiveRefusalOf : Model.Ratchet.ReceiveRefusal → RatchetRefusal
  | .tooManySkipped => .tooManySkipped
  | .skippedStoreFull => .skippedStoreFull
  | .noReceivingChain => .noReceivingChain
  | .outOfOrder => .outOfOrder
  | .chainExhausted => .chainExhausted

def sparseReceiveRefusalOf : Model.SparseRatchet.ReceiveRefusal → SparseRefusal
  | .epochOutOfOrder => .epochOutOfOrder
  | .noChain => .noChain
  | .chainRetired => .chainRetired
  | .tooManySkipped => .tooManySkipped
  | .skippedStoreFull => .skippedStoreFull
  | .outOfOrder => .outOfOrder
  | .chainExhausted => .chainExhausted

def tripleReceiveRefusalOf : Model.Triple.ReceiveRefusal → Refusal
  | .classical reason => .triple (.classical (ratchetReceiveRefusalOf reason))
  | .postQuantum reason => .triple (.postQuantum (sparseReceiveRefusalOf reason))

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

theorem ratchetReceiveRefusalOf_injective :
    Function.Injective ratchetReceiveRefusalOf := by
  intro left right h
  cases left <;> cases right <;> simp [ratchetReceiveRefusalOf] at h ⊢

theorem sparseReceiveRefusalOf_injective :
    Function.Injective sparseReceiveRefusalOf := by
  intro left right h
  cases left <;> cases right <;> simp [sparseReceiveRefusalOf] at h ⊢

theorem tripleReceiveRefusalOf_injective :
    Function.Injective tripleReceiveRefusalOf := by
  intro left right h
  cases left with
  | classical left =>
      cases right with
      | classical right =>
          simp [tripleReceiveRefusalOf] at h
          exact congrArg Model.Triple.ReceiveRefusal.classical
            (ratchetReceiveRefusalOf_injective h)
      | postQuantum right => simp [tripleReceiveRefusalOf] at h
  | postQuantum left =>
      cases right with
      | classical right => simp [tripleReceiveRefusalOf] at h
      | postQuantum right =>
          simp [tripleReceiveRefusalOf] at h
          exact congrArg Model.Triple.ReceiveRefusal.postQuantum
            (sparseReceiveRefusalOf_injective h)

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

/-! ## Session operations

An operation returns the state and remaining oracle trace even when its public
result is a refusal. This is necessary for the two effects Rust exposes on an
error: random draws have happened, and a Braid that reaches its terminal state
is committed before `AgreementFailed` is returned. -/

structure Step (Result : Type) where
  session : Session
  result : Except Refusal Result
  oracle : Oracle

structure EstablishStep where
  result : Except Refusal Session
  oracle : Oracle

structure Identity where
  secret : Key
  publicKey : Key

abbrev Bundle := Model.Messages.Bundle
abbrev StoredPrekeys := Model.PersistedState.PrekeyStoreState.Store

structure PrekeyStore where
  state : StoredPrekeys
  legacyLastResortBlocked : List Nat

structure ResponderStep where
  store : PrekeyStore
  result : Except Refusal (Session × Bytes)
  oracle : Oracle

def absentId : UInt32 :=
  UInt32.ofNat Model.PersistedState.PrekeyStoreState.absentId

def encodeKem (publicKey : Bytes) : Bytes := 0x08 :: publicKey

def responderSignedPrekeySecret (store : PrekeyStore) (id : Nat) : Option Key :=
  if id = store.state.signedPrekeyId then some store.state.signedPrekeySecret
  else
    match store.state.previousSigned with
    | some (secret, previousId, _) => if id = previousId then some secret else none
    | none => none

def responderKemPair (store : PrekeyStore) (id : Nat) :
    Except Refusal (Bytes × Bool) :=
  if id = store.state.kemId then
    if store.legacyLastResortBlocked.contains id then
      .error .legacyLastResortRecord
    else .ok (store.state.kemPair, true)
  else
    match store.state.previousKem with
    | some (pair, previousId, _) =>
        if id = previousId then
          if store.legacyLastResortBlocked.contains id then
            .error .legacyLastResortRecord
          else .ok (pair, true)
        else
          match store.state.kemOneTime.find? (fun entry => entry.1 = id) with
          | some entry => .ok (entry.2.1, false)
          | none => .error .unknownPrekeyId
    | none =>
        match store.state.kemOneTime.find? (fun entry => entry.1 = id) with
        | some entry => .ok (entry.2.1, false)
        | none => .error .unknownPrekeyId

def responderOneTimeSecret (store : PrekeyStore) (id : Nat) :
    Except Refusal (Option Key) :=
  if id = Model.PersistedState.PrekeyStoreState.absentId then .ok none
  else
    match store.state.oneTime.find? (fun entry => entry.1 = id) with
    | some entry => .ok (some entry.2)
    | none => .error .unknownPrekeyId

/-- `LAST_RESORT_HANDSHAKE_LABEL` (CONSTANTS.md), as 32 ASCII bytes. -/
def lastResortHandshakeLabel : Bytes :=
  [0x74,0x61,0x63,0x65,0x6e,0x74,0x61,0x20,0x6c,0x61,0x73,0x74,0x2d,0x72,
   0x65,0x73,0x6f,0x72,0x74,0x20,0x68,0x61,0x6e,0x64,0x73,0x68,0x61,0x6b,
   0x65,0x20,0x76,0x32]

def lastResortFingerprint (sharedSecret : Key) : Key :=
  Model.Kdf.hmac lastResortHandshakeLabel sharedSecret

def lastResortReplayCheck (store : PrekeyStore) (kemId : Nat)
    (sharedSecret : Key) (lastResort : Bool) : Except Refusal (Option Key) :=
  if !lastResort then .ok none
  else
    let fingerprint := lastResortFingerprint sharedSecret
    if store.state.seen.any (fun entry => entry.2 = fingerprint) then
      .error .replayedLastResort
    else if Model.PersistedState.PrekeyStoreState.maxLastResortSeen ≤
        (store.state.seen.filter (fun entry => entry.1 = kemId)).length then
      .error .lastResortRecordFull
    else .ok (some fingerprint)

def establishInitiator (oracle : Oracle) (identity : Identity) (bundle : Bundle)
    (expectedIdentity : Key) : EstablishStep :=
  if bundle.identityKey != expectedIdentity then
    { result := .error .unexpectedIdentity, oracle }
  else if bundle.oneTimePrekey.isSome != (bundle.oneTimeId != absentId) then
    { result := .error .inconsistentBundle, oracle }
  else if !(Model.Messages.canonicalKey bundle.identityKey)
      || !(Model.Messages.canonicalKey bundle.signedPrekey)
      || !(bundle.oneTimePrekey.all Model.Messages.canonicalKey) then
    { result := .error .badEncoding, oracle }
  else if !(oracle.sigVerify bundle.identityKey
      (Model.PersistedState.SessionState.encodeEc bundle.signedPrekey)
      bundle.signedPrekeySig) then
    { result := .error (.handshake .badSignedPrekeySignature), oracle }
  else if !(oracle.sigVerify bundle.identityKey (encodeKem bundle.kemPrekey)
      bundle.kemPrekeySig) then
    { result := .error (.handshake .badKemPrekeySignature), oracle }
  else
    match random32 oracle with
    | none => { result := .error .ceiling, oracle }
    | some (ephemeralPrivate, afterEphemeral) =>
        match kemEncapsulate afterEphemeral bundle.kemPrekey with
        | none => { result := .error .ceiling, oracle := afterEphemeral }
        | some (none, afterKem) => { result := .error .kem, oracle := afterKem }
        | some (some (kemCiphertext, kemSecret), afterKem) =>
            match oracle.dhAgree identity.secret bundle.signedPrekey with
            | none =>
                { result := .error (.handshake .nonContributoryAgreement)
                  oracle := afterKem }
            | some dh1 =>
                match oracle.dhAgree ephemeralPrivate bundle.identityKey with
                | none =>
                    { result := .error (.handshake .nonContributoryAgreement)
                      oracle := afterKem }
                | some dh2 =>
                    match oracle.dhAgree ephemeralPrivate bundle.signedPrekey with
                    | none =>
                        { result := .error (.handshake .nonContributoryAgreement)
                          oracle := afterKem }
                    | some dh3 =>
                        let dh4 := bundle.oneTimePrekey.map
                          (oracle.dhAgree ephemeralPrivate)
                        if dh4.any Option.isNone then
                          { result := .error (.handshake .nonContributoryAgreement)
                            oracle := afterKem }
                        else
                          let sharedSecret := Model.SessionEstablishment.sharedSecret
                            dh1 dh2 dh3 (dh4.bind id) kemSecret
                          match random32 afterKem with
                          | none => { result := .error .ceiling, oracle := afterKem }
                          | some (ratchetPrivate, afterRatchet) =>
                              match oracle.dhAgree ratchetPrivate bundle.signedPrekey with
                              | none =>
                                  { result := .error
                                      (.handshake .nonContributoryAgreement)
                                    oracle := afterRatchet }
                              | some dhOut =>
                                  let ourRatchetPublic := oracle.dhPublic ratchetPrivate
                                  let ephemeralPublic := oracle.dhPublic ephemeralPrivate
                                  { result := .ok
                                      { triple := Model.Triple.initAlice sharedSecret
                                          ourRatchetPublic bundle.signedPrekey dhOut .tacenta
                                        braid := Model.Braid.initAlice sharedSecret
                                        ratchetPrivate
                                        identityAd :=
                                          Model.SessionEstablishment.associatedData
                                            (Model.PersistedState.SessionState.encodeEc
                                              identity.publicKey)
                                            (Model.PersistedState.SessionState.encodeEc
                                              bundle.identityKey)
                                        ourIdentityPublic := identity.publicKey
                                        peerIdentityPublic := bundle.identityKey
                                        pendingInitial := some
                                          { ephemeralPublic
                                            kemCiphertext
                                            signedPrekeyId := bundle.signedPrekeyId.toNat
                                            oneTimePrekeyId := bundle.oneTimeId.toNat
                                            kemPrekeyId := bundle.kemPrekeyId.toNat }
                                        establishedEphemeral := none }
                                    oracle := afterRatchet }

theorem establishInitiator_identity_mismatch (oracle : Oracle) (identity : Identity)
    (bundle : Bundle) (expectedIdentity : Key)
    (h : (bundle.identityKey != expectedIdentity) = true) :
    establishInitiator oracle identity bundle expectedIdentity =
      { result := .error .unexpectedIdentity, oracle } := by
  simp [establishInitiator, h]

theorem establishInitiator_presence_mismatch (oracle : Oracle) (identity : Identity)
    (bundle : Bundle) (expectedIdentity : Key)
    (hi : bundle.identityKey = expectedIdentity)
    (hp : (bundle.oneTimePrekey.isSome != (bundle.oneTimeId != absentId)) = true) :
    establishInitiator oracle identity bundle expectedIdentity =
      { result := .error .inconsistentBundle, oracle } := by
  simp [establishInitiator, hi, hp]

/-- A bundle with any non-canonical curve key is rejected before signatures,
    draws or agreement. -/
theorem establishInitiator_noncanonical (oracle : Oracle) (identity : Identity)
    (bundle : Bundle) (expectedIdentity : Key)
    (hi : bundle.identityKey = expectedIdentity)
    (hp : bundle.oneTimePrekey.isSome = (bundle.oneTimeId != absentId))
    (hc : (!(Model.Messages.canonicalKey bundle.identityKey)
      || !(Model.Messages.canonicalKey bundle.signedPrekey)
      || !(bundle.oneTimePrekey.all Model.Messages.canonicalKey)) = true) :
    establishInitiator oracle identity bundle expectedIdentity =
      { result := .error .badEncoding, oracle } := by
  subst expectedIdentity
  grind [establishInitiator]

/-- A failed signed-prekey signature is rejected before any random draw or
    agreement. -/
theorem establishInitiator_bad_signed_prekey_signature (oracle : Oracle)
    (identity : Identity) (bundle : Bundle) (expectedIdentity : Key)
    (hi : bundle.identityKey = expectedIdentity)
    (hp : bundle.oneTimePrekey.isSome = (bundle.oneTimeId != absentId))
    (hc : Model.Messages.canonicalKey bundle.identityKey = true)
    (hs : Model.Messages.canonicalKey bundle.signedPrekey = true)
    (ho : bundle.oneTimePrekey.all Model.Messages.canonicalKey = true)
    (hSig : oracle.sigVerify bundle.identityKey
      (Model.PersistedState.SessionState.encodeEc bundle.signedPrekey)
      bundle.signedPrekeySig = false) :
    establishInitiator oracle identity bundle expectedIdentity =
      { result := .error (.handshake .badSignedPrekeySignature), oracle } := by
  subst expectedIdentity
  simp [establishInitiator, hp, hc, hs, ho, hSig]

/-- A non-contributory initiator-ephemeral/signed-prekey agreement is rejected
    after the preceding draws and agreements, retaining their remaining oracle
    state and constructing no Session. -/
theorem establishInitiator_ephemeral_signed_noncontributory (oracle afterEphemeral
    afterKem : Oracle) (identity : Identity) (bundle : Bundle)
    (expectedIdentity ephemeralPrivate kemCiphertext kemSecret dh1 dh2 : Key)
    (hi : bundle.identityKey = expectedIdentity)
    (hp : bundle.oneTimePrekey.isSome = (bundle.oneTimeId != absentId))
    (hc : Model.Messages.canonicalKey bundle.identityKey = true)
    (hs : Model.Messages.canonicalKey bundle.signedPrekey = true)
    (ho : bundle.oneTimePrekey.all Model.Messages.canonicalKey = true)
    (hSignedSig : oracle.sigVerify bundle.identityKey
      (Model.PersistedState.SessionState.encodeEc bundle.signedPrekey)
      bundle.signedPrekeySig = true)
    (hKemSig : oracle.sigVerify bundle.identityKey (encodeKem bundle.kemPrekey)
      bundle.kemPrekeySig = true)
    (hDraw : random32 oracle = some (ephemeralPrivate, afterEphemeral))
    (hKem : kemEncapsulate afterEphemeral bundle.kemPrekey =
      some (some (kemCiphertext, kemSecret), afterKem))
    (hDh1 : oracle.dhAgree identity.secret bundle.signedPrekey = some dh1)
    (hDh2 : oracle.dhAgree ephemeralPrivate bundle.identityKey = some dh2)
    (hDh3 : oracle.dhAgree ephemeralPrivate bundle.signedPrekey = none) :
    establishInitiator oracle identity bundle expectedIdentity =
      { result := .error (.handshake .nonContributoryAgreement), oracle := afterKem } := by
  subst expectedIdentity
  simp [establishInitiator, hp, hc, hs, ho, hSignedSig, hKemSig, hDraw,
    hKem, hDh1, hDh2, hDh3]

def consumeResponderPrekeys (store : PrekeyStore) (oneTimeId kemId : Nat)
    (lastResort : Bool) (fingerprint : Option Key) : PrekeyStore :=
  let withoutKem :=
    if lastResort then store.state
    else { store.state with
      kemOneTime := store.state.kemOneTime.filter (fun entry => entry.1 != kemId) }
  let withoutCurve :=
    if oneTimeId = Model.PersistedState.PrekeyStoreState.absentId then withoutKem
    else { withoutKem with
      oneTime := withoutKem.oneTime.filter (fun entry => entry.1 != oneTimeId) }
  let recorded :=
    match fingerprint with
    | none => withoutCurve
    | some value => { withoutCurve with seen := withoutCurve.seen ++ [(kemId, value)] }
  { store with state := recorded }

def braidFailed : Model.Braid.BraidState → Bool
  | .failed => true
  | _ => false

theorem braidFailed_iff (state : Model.Braid.BraidState) :
    braidFailed state = true ↔ state = .failed := by
  cases state <;> simp [braidFailed]

def sparseOutputOf : Option Model.Braid.Output → Option Model.SparseRatchet.Output :=
  Option.map fun value => { keyEpoch := value.keyEpoch, key := value.key }

inductive FullStore where
  | classical | postQuantum
  deriving Repr, DecidableEq, Inhabited

def fullStore : Model.Triple.ReceiveRefusal → Option FullStore
  | .classical .skippedStoreFull => some .classical
  | .postQuantum .skippedStoreFull => some .postQuantum
  | _ => none

def receiveShortfall (half : FullStore) (state : Model.Triple.State)
    (composite : Model.CompositeHeader.Composite) : Nat :=
  match half with
  | .classical =>
      max 1 (Model.Triple.classicalSkippedLength state
        + (composite.n.toNat - Model.Triple.receiveCount state)
        - Model.State.maxSkippedStore)
  | .postQuantum =>
      match Model.Triple.postQuantumReceiveCount state composite.pqEpoch.toNat with
      | none => 1
      | some received =>
          max 1 (Model.Triple.postQuantumSkippedLength state
            + (composite.pqN.toNat - 1 - received)
            - Model.SparseRatchet.maxSkippedStore)

private def receiveWithEvictionLoop (state : Model.Triple.State)
    (composite : Model.CompositeHeader.Composite) (header : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Key)
    (output : Option Model.SparseRatchet.Output)
    (pending : Model.Triple.ReceiveRefusal) (half : FullStore) (batch : Nat) :
    Nat → Except Model.Triple.ReceiveRefusal (Model.Triple.State × Key)
  | 0 => .error pending
  | fuel + 1 =>
      let evicted :=
        match half with
        | .classical => Model.Triple.evictOldestClassical state batch
        | .postQuantum => Model.Triple.evictOldestPostQuantum state batch
      if evicted.2 = 0 then .error pending
      else
        match Model.Triple.receiveDetailed evicted.1 header
            dhOutRecv dhOutSend newDhsPub output with
        | .ok result => .ok result
        | .error reason =>
            match fullStore reason with
            | none => .error reason
            | some next =>
                if next = half then
                  receiveWithEvictionLoop evicted.1 composite header
                    dhOutRecv dhOutSend newDhsPub output reason next (batch * 2) fuel
                else
                  receiveWithEvictionLoop evicted.1 composite header
                    dhOutRecv dhOutSend newDhsPub output reason next
                    (receiveShortfall next evicted.1 composite) fuel

/-- The Session receive retry policy. A full leaf store is evicted only on this
    working Triple copy. The fuel is one more than the total entries held; every
    recursive retry has deleted at least one, so the fuel boundary is
    unreachable for a well-formed execution and supplies structural recursion
    without changing the Rust loop's result. -/
def receiveWithEviction (state : Model.Triple.State)
    (composite : Model.CompositeHeader.Composite) (header : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Key)
    (output : Option Model.SparseRatchet.Output) :
    Except Model.Triple.ReceiveRefusal (Model.Triple.State × Key) :=
  match Model.Triple.receiveDetailed state header
      dhOutRecv dhOutSend newDhsPub output with
  | .ok result => .ok result
  | .error reason =>
      match fullStore reason with
      | none => .error reason
      | some half =>
          receiveWithEvictionLoop state composite header
            dhOutRecv dhOutSend newDhsPub output reason half
            (receiveShortfall half state composite)
            (Model.Triple.classicalSkippedLength state
              + Model.Triple.postQuantumSkippedLength state + 1)

/-- A single successful retry is exposed for the translation composition.
The theorem names the direct refusal, the selected full-store half, the
working-copy eviction and the successful retry; it does not hide those facts
inside the private recursive loop. -/
theorem receiveWithEviction_one_retry
    (state : Model.Triple.State)
    (composite : Model.CompositeHeader.Composite) (header : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Key)
    (output : Option Model.SparseRatchet.Output)
    (result : Model.Triple.State × Key)
    (evictedState : Model.Triple.State)
    (reason : Model.Triple.ReceiveRefusal) (half : FullStore)
    (evicted : Nat)
    (hDirect : Model.Triple.receiveDetailed state header dhOutRecv dhOutSend
      newDhsPub output = .error reason)
    (hFull : fullStore reason = some half)
    (hEvict : (match half with
      | .classical => (Model.Triple.evictOldestClassical state (receiveShortfall half state composite))
      | .postQuantum => (Model.Triple.evictOldestPostQuantum state (receiveShortfall half state composite))) =
      (evictedState, evicted))
    (hNonzero : evicted ≠ 0)
    (hRetry : Model.Triple.receiveDetailed evictedState header dhOutRecv dhOutSend
      newDhsPub output = .ok result) :
    receiveWithEviction state composite header dhOutRecv dhOutSend newDhsPub output = .ok result := by
  simp [receiveWithEviction, hDirect, hFull]
  cases half <;> simp [receiveWithEvictionLoop, hEvict, hNonzero, hRetry]

/-! Expose the recursive continuation after a retry fails with another
    full-store refusal.  This equation is the induction step for the bounded
    lifecycle retry invariant; it leaves the decremented fuel and doubled
    batch explicit. -/
theorem receiveWithEvictionLoop_continue_same_half
    (state : Model.Triple.State)
    (composite : Model.CompositeHeader.Composite) (header : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Key)
    (output : Option Model.SparseRatchet.Output)
    (pending reason : Model.Triple.ReceiveRefusal)
    (half : FullStore) (batch fuel : Nat)
    (evictedState : Model.Triple.State) (evicted : Nat)
    (hEvict : (match half with
      | .classical => Model.Triple.evictOldestClassical state batch
      | .postQuantum => Model.Triple.evictOldestPostQuantum state batch) =
        (evictedState, evicted))
    (hNonzero : evicted ≠ 0)
    (hRetry : Model.Triple.receiveDetailed evictedState header
      dhOutRecv dhOutSend newDhsPub output = .error reason)
    (hFull : fullStore reason = some half) :
    receiveWithEvictionLoop state composite header dhOutRecv dhOutSend newDhsPub output
      pending half batch (fuel + 1) =
      receiveWithEvictionLoop evictedState composite header dhOutRecv dhOutSend
        newDhsPub output reason half (batch * 2) fuel := by
  cases half <;> simp [receiveWithEvictionLoop, hEvict, hNonzero, hRetry, hFull]

theorem receiveWithEvictionLoop_continue_switch_half
    (state : Model.Triple.State)
    (composite : Model.CompositeHeader.Composite) (header : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Key)
    (output : Option Model.SparseRatchet.Output)
    (pending reason : Model.Triple.ReceiveRefusal)
    (half nextHalf : FullStore) (batch fuel : Nat)
    (evictedState : Model.Triple.State) (evicted : Nat)
    (hEvict : (match half with
      | .classical => Model.Triple.evictOldestClassical state batch
      | .postQuantum => Model.Triple.evictOldestPostQuantum state batch) =
        (evictedState, evicted))
    (hNonzero : evicted ≠ 0)
    (hRetry : Model.Triple.receiveDetailed evictedState header
      dhOutRecv dhOutSend newDhsPub output = .error reason)
    (hFull : fullStore reason = some nextHalf)
    (hDifferent : nextHalf ≠ half) :
    receiveWithEvictionLoop state composite header dhOutRecv dhOutSend newDhsPub output
      pending half batch (fuel + 1) =
      receiveWithEvictionLoop evictedState composite header dhOutRecv dhOutSend
        newDhsPub output reason nextHalf
        (receiveShortfall nextHalf evictedState composite) fuel := by
  cases half <;> cases nextHalf <;>
    simp_all [receiveWithEvictionLoop, hEvict, hNonzero, hRetry, hFull, hDifferent]

theorem receiveWithEvictionLoop_zero_evict
    (state : Model.Triple.State)
    (composite : Model.CompositeHeader.Composite) (header : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Key)
    (output : Option Model.SparseRatchet.Output)
    (pending : Model.Triple.ReceiveRefusal)
    (half : FullStore) (batch fuel : Nat)
    (evictedState : Model.Triple.State)
    (hEvict : (match half with
      | .classical => Model.Triple.evictOldestClassical state batch
      | .postQuantum => Model.Triple.evictOldestPostQuantum state batch) =
        (evictedState, 0)) :
    receiveWithEvictionLoop state composite header dhOutRecv dhOutSend newDhsPub output
      pending half batch (fuel + 1) = .error pending := by
  cases half <;> simp [receiveWithEvictionLoop, hEvict]

/-- A classical consumed-message refusal is not an eviction case, so the
    Session retry policy preserves it exactly. -/
theorem receiveWithEviction_classical_outOfOrder (state : Model.Triple.State)
    (composite : Model.CompositeHeader.Composite) (header : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Key)
    (output : Option Model.SparseRatchet.Output)
    (hReplay : Model.Ratchet.receiveDetailed state.classical header.dr
      dhOutRecv dhOutSend newDhsPub = .error .outOfOrder) :
    receiveWithEviction state composite header dhOutRecv dhOutSend newDhsPub output =
      .error (.classical .outOfOrder) := by
  have ht : Model.Triple.receiveDetailed state header dhOutRecv dhOutSend
      newDhsPub output = .error (.classical .outOfOrder) :=
    (Model.Triple.receiveDetailed_classical_iff state header dhOutRecv dhOutSend
      newDhsPub output .outOfOrder).2 hReplay
  simp [receiveWithEviction, ht, fullStore]

/-- `Session::encrypt`, through the executable leaf models and the primitive
    oracle. The Braid runs first, a terminal Braid is committed on refusal, the
    Triple candidate commits only on success, and the initial wrapper remains
    present until a successful receive clears it. -/
def encrypt (view : CodewordView) (oracle : Oracle) (session : Session)
    (plaintext : Bytes) : Step Bytes :=
  if agreementFailed session then
    { session, result := .error .agreementFailed, oracle }
  else
    match sendAgreement oracle session.braid with
    | none => { session, result := .error .ceiling, oracle }
    | some ((message, sendingEpoch, output, braidNext), oracleNext) =>
        if braidFailed braidNext then
          { session := { session with braid := braidNext }
            result := .error .agreementFailed
            oracle := oracleNext }
        else
          match message with
          | none => { session, result := .error .ceiling, oracle := oracleNext }
          | some agreementMessage =>
              match Model.Triple.sendDetailed session.triple sendingEpoch
                  (sparseOutputOf output) with
              | .error reason =>
                  { session
                    result := .error (tripleSendRefusalOf reason)
                    oracle := oracleNext }
              | .ok (tripleNext, header, messageKey) =>
                  match compositeOf view session.braid header agreementMessage with
                  | none => { session, result := .error .ceiling, oracle := oracleNext }
                  | some composite =>
                      let keys := Model.State.messageKeys messageKey .tacenta
                      let associatedData := Model.Messages.concatAd session.identityAd
                        (Model.CompositeHeader.encode composite)
                      let ciphertext := oracle.aeadSeal keys.1 keys.2.1 keys.2.2
                        plaintext associatedData
                      let ratchetMessage := Model.CompositeHeader.encodeMessage
                        composite ciphertext
                      let wireMessage :=
                        match session.pendingInitial with
                        | none => ratchetMessage
                        | some pending =>
                            Model.Messages.encodeInitial
                              (Model.PersistedState.SessionState.encodeEc
                                session.ourIdentityPublic)
                              (Model.PersistedState.SessionState.encodeEc
                                pending.ephemeralPublic)
                              pending.kemCiphertext
                              (UInt32.ofNat pending.signedPrekeyId)
                              (UInt32.ofNat pending.oneTimePrekeyId)
                              (UInt32.ofNat pending.kemPrekeyId)
                              ratchetMessage
                      { session := { session with triple := tripleNext, braid := braidNext }
                        result := .ok wireMessage
                        oracle := oracleNext }

theorem encrypt_terminal_guard (view : CodewordView) (oracle : Oracle)
    (session : Session) (plaintext : Bytes)
    (h : agreementFailed session = true) :
    encrypt view oracle session plaintext =
      { session, result := .error .agreementFailed, oracle } := by
  simp [encrypt, h]

theorem encrypt_braid_failure_commits (view : CodewordView) (oracle oracleNext : Oracle)
    (session : Session) (plaintext : Bytes)
    (message : Option Model.Braid.Msg) (sendingEpoch : Nat)
    (output : Option Model.Braid.Output) (braidNext : Model.Braid.BraidState)
    (hg : agreementFailed session = false)
    (hs : sendAgreement oracle session.braid =
      some ((message, sendingEpoch, output, braidNext), oracleNext))
    (hf : braidFailed braidNext = true) :
    encrypt view oracle session plaintext =
      { session := { session with braid := braidNext }
        result := .error .agreementFailed
        oracle := oracleNext } := by
  simp [encrypt, hg, hs, hf]

theorem encrypt_triple_refusal_keeps_state (view : CodewordView)
    (oracle oracleNext : Oracle) (session : Session) (plaintext : Bytes)
    (message : Model.Braid.Msg) (sendingEpoch : Nat)
    (output : Option Model.Braid.Output) (braidNext : Model.Braid.BraidState)
    (reason : Model.Triple.SendRefusal)
    (hg : agreementFailed session = false)
    (hs : sendAgreement oracle session.braid =
      some ((some message, sendingEpoch, output, braidNext), oracleNext))
    (hf : braidFailed braidNext = false)
    (ht : Model.Triple.sendDetailed session.triple sendingEpoch
      (sparseOutputOf output) = .error reason) :
    encrypt view oracle session plaintext =
      { session
        result := .error (tripleSendRefusalOf reason)
        oracle := oracleNext } := by
  simp [encrypt, hg, hs, hf, ht]

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

/-- The inner `Session::decrypt_ratchet` transaction. Every candidate change,
    including eviction, stays local until the AEAD opens. The fresh ratchet
    private draw is consumed after the incoming DH succeeds, matching the call
    order in Rust, and remains consumed on every later refusal. -/
def decryptRatchet (view : CodewordView) (oracle : Oracle) (session : Session)
    (message : Bytes) : Step Bytes :=
  if agreementFailed session then
    { session, result := .error .agreementFailed, oracle }
  else
    match Model.CompositeHeader.decodeDetailed message with
    | .error reason => { session, result := .error (.decode reason), oracle }
    | .ok (composite, ciphertext) =>
        let agreement := Model.Braid.receive oracle.braidKem session.braid
          (braidMessageOf view session.braid composite)
        let output := sparseOutputOf agreement.2.1
        let braidCandidate := agreement.2.2
        match oracle.dhAgree session.ratchetPrivate composite.dh with
        | none =>
            { session
              result := .error (.handshake .nonContributoryAgreement)
              oracle }
        | some dhOutRecv =>
            match random32 oracle with
            | none => { session, result := .error .ceiling, oracle }
            | some (candidatePrivate, oracleNext) =>
                match oracle.dhAgree candidatePrivate composite.dh with
                | none =>
                    { session
                      result := .error (.handshake .nonContributoryAgreement)
                      oracle := oracleNext }
                | some dhOutSend =>
                    let header := tripleHeaderOf composite
                    let candidatePublic := oracle.dhPublic candidatePrivate
                    match receiveWithEviction session.triple composite header
                        dhOutRecv dhOutSend candidatePublic output with
                    | .error reason =>
                        { session
                          result := .error (tripleReceiveRefusalOf reason)
                          oracle := oracleNext }
                    | .ok (tripleCandidate, messageKey) =>
                        let keys := Model.State.messageKeys messageKey .tacenta
                        let associatedData := Model.Messages.concatAd session.identityAd
                          (Model.CompositeHeader.encode composite)
                        match oracle.aeadOpen keys.1 keys.2.1 keys.2.2
                            ciphertext associatedData with
                        | none => { session, result := .error .aead, oracle := oracleNext }
                        | some plaintext =>
                            let ratchetPrivate :=
                              if tripleCandidate.classical.dhsPub ==
                                  session.triple.classical.dhsPub then
                                session.ratchetPrivate
                              else candidatePrivate
                            { session :=
                                { session with
                                  triple := tripleCandidate
                                  braid := braidCandidate
                                  ratchetPrivate }
                              result := .ok plaintext
                              oracle := oracleNext }

theorem decryptRatchet_refusal_keeps_session (view : CodewordView)
    (oracle : Oracle) (session : Session) (message : Bytes) (reason : Refusal)
    (h : (decryptRatchet view oracle session message).result = .error reason) :
    (decryptRatchet view oracle session message).session = session := by
  by_cases hf : agreementFailed session = true
  · simp [decryptRatchet, hf]
  · cases hd : Model.CompositeHeader.decodeDetailed message with
    | error decodeReason => simp [decryptRatchet, hf, hd]
    | ok decoded =>
        obtain ⟨composite, ciphertext⟩ := decoded
        cases hr : oracle.dhAgree session.ratchetPrivate composite.dh with
        | none => simp [decryptRatchet, hf, hd, hr]
        | some dhOutRecv =>
            cases hdraw : random32 oracle with
            | none => simp [decryptRatchet, hf, hd, hr, hdraw]
            | some drawn =>
                obtain ⟨candidatePrivate, oracleNext⟩ := drawn
                cases hs : oracle.dhAgree candidatePrivate composite.dh with
                | none => simp [decryptRatchet, hf, hd, hr, hdraw, hs]
                | some dhOutSend =>
                    cases ht : receiveWithEviction session.triple composite
                        (tripleHeaderOf composite) dhOutRecv dhOutSend
                        (oracle.dhPublic candidatePrivate)
                        (sparseOutputOf
                          (Model.Braid.receive oracle.braidKem session.braid
                            (braidMessageOf view session.braid composite)).2.1) with
                    | error tripleReason =>
                        simp [decryptRatchet, hf, hd, hr, hdraw, hs, ht]
                    | ok candidate =>
                        obtain ⟨tripleCandidate, messageKey⟩ := candidate
                        cases ha : oracle.aeadOpen
                            (Model.State.messageKeys messageKey .tacenta).1
                            (Model.State.messageKeys messageKey .tacenta).2.1
                            (Model.State.messageKeys messageKey .tacenta).2.2 ciphertext
                            (Model.Messages.concatAd session.identityAd
                              (Model.CompositeHeader.encode composite)) with
                        | none =>
                            simp [decryptRatchet, hf, hd, hr, hdraw, hs, ht, ha]
                        | some plaintext =>
                            simp [decryptRatchet, hf, hd, hr, hdraw, hs, ht, ha] at h

/-- Public `Session::decrypt`: remove an accepted repeated-initial wrapper,
    run the authenticated ratchet transaction, and clear `pendingInitial` only
    after that transaction succeeds. -/
def decrypt (view : CodewordView) (oracle : Oracle) (session : Session)
    (message : Bytes) : Step Bytes :=
  match dispatchDecrypt session message with
  | .error reason => { session, result := .error reason, oracle }
  | .ok inner =>
      let step := decryptRatchet view oracle session inner
      match step.result with
      | .error _ => step
      | .ok plaintext =>
          { step with
            session := { step.session with pendingInitial := none }
            result := .ok plaintext }

theorem decrypt_dispatch_refusal_keeps_state (view : CodewordView)
    (oracle : Oracle) (session : Session) (message : Bytes) (reason : Refusal)
    (h : dispatchDecrypt session message = .error reason) :
    decrypt view oracle session message =
      { session, result := .error reason, oracle } := by
  simp [decrypt, h]

theorem decrypt_refusal_keeps_session (view : CodewordView)
    (oracle : Oracle) (session : Session) (message : Bytes) (reason : Refusal)
    (h : (decrypt view oracle session message).result = .error reason) :
    (decrypt view oracle session message).session = session := by
  cases hd : dispatchDecrypt session message with
  | error dispatchReason => simp [decrypt, hd]
  | ok inner =>
      cases hr : decryptRatchet view oracle session inner with
      | mk next result oracleNext =>
          cases result with
          | error ratchetReason =>
              have hk := decryptRatchet_refusal_keeps_session view oracle session
                inner ratchetReason (by simp [hr])
              simpa [decrypt, hd, hr] using hk
          | ok plaintext => simp [decrypt, hd, hr] at h

theorem decrypt_success_clears_pending (view : CodewordView)
    (oracle : Oracle) (session : Session) (message plaintext : Bytes)
    (h : (decrypt view oracle session message).result = .ok plaintext) :
    (decrypt view oracle session message).session.pendingInitial = none := by
  cases hd : dispatchDecrypt session message with
  | error reason => simp [decrypt, hd] at h
  | ok inner =>
      cases hr : decryptRatchet view oracle session inner with
      | mk next result oracleNext =>
          cases result with
          | error reason => simp [decrypt, hd, hr] at h
          | ok actual => simp [decrypt, hd, hr]

theorem decrypt_aead_refusal_keeps_state (view : CodewordView)
    (oracle oracleNext : Oracle) (session : Session) (message ciphertext : Bytes)
    (composite : Model.CompositeHeader.Composite) (dhOutRecv candidatePrivate dhOutSend : Key)
    (tripleCandidate : Model.Triple.State) (messageKey : Key)
    (hd : Model.CompositeHeader.decodeDetailed message = .ok (composite, ciphertext))
    (hf : agreementFailed session = false)
    (hr : oracle.dhAgree session.ratchetPrivate composite.dh = some dhOutRecv)
    (hdraw : random32 oracle = some (candidatePrivate, oracleNext))
    (hs : oracle.dhAgree candidatePrivate composite.dh = some dhOutSend)
    (ht : receiveWithEviction session.triple composite (tripleHeaderOf composite)
      dhOutRecv dhOutSend (oracle.dhPublic candidatePrivate)
      (sparseOutputOf
        (Model.Braid.receive oracle.braidKem session.braid
          (braidMessageOf view session.braid composite)).2.1) =
        .ok (tripleCandidate, messageKey))
    (ha : oracle.aeadOpen
      (Model.State.messageKeys messageKey .tacenta).1
      (Model.State.messageKeys messageKey .tacenta).2.1
      (Model.State.messageKeys messageKey .tacenta).2.2 ciphertext
      (Model.Messages.concatAd session.identityAd
        (Model.CompositeHeader.encode composite)) = none) :
    decryptRatchet view oracle session message =
      { session, result := .error .aead, oracle := oracleNext } := by
  simp [decryptRatchet, hf, hd, hr, hdraw, hs, ht, ha]

/-! The corresponding success branch is kept as a named model theorem so the
translation proof can consume the authenticated plaintext and the exact
conditional ratchet-private update without re-proving the lifecycle match. -/
theorem decrypt_aead_success_commits (view : CodewordView)
    (oracle oracleNext : Oracle) (session : Session) (message ciphertext : Bytes)
    (composite : Model.CompositeHeader.Composite) (dhOutRecv candidatePrivate dhOutSend : Key)
    (tripleCandidate : Model.Triple.State) (messageKey plaintext : Key)
    (hd : Model.CompositeHeader.decodeDetailed message = .ok (composite, ciphertext))
    (hf : agreementFailed session = false)
    (hr : oracle.dhAgree session.ratchetPrivate composite.dh = some dhOutRecv)
    (hdraw : random32 oracle = some (candidatePrivate, oracleNext))
    (hs : oracle.dhAgree candidatePrivate composite.dh = some dhOutSend)
    (ht : receiveWithEviction session.triple composite (tripleHeaderOf composite)
      dhOutRecv dhOutSend (oracle.dhPublic candidatePrivate)
      (sparseOutputOf
        (Model.Braid.receive oracle.braidKem session.braid
          (braidMessageOf view session.braid composite)).2.1) =
        .ok (tripleCandidate, messageKey))
    (ha : oracle.aeadOpen
      (Model.State.messageKeys messageKey .tacenta).1
      (Model.State.messageKeys messageKey .tacenta).2.1
      (Model.State.messageKeys messageKey .tacenta).2.2 ciphertext
      (Model.Messages.concatAd session.identityAd
        (Model.CompositeHeader.encode composite)) = some plaintext) :
    decryptRatchet view oracle session message =
      { session :=
          { session with
            triple := tripleCandidate
            braid :=
              (Model.Braid.receive oracle.braidKem session.braid
                (braidMessageOf view session.braid composite)).2.2
            ratchetPrivate :=
              if tripleCandidate.classical.dhsPub == session.triple.classical.dhsPub then
                session.ratchetPrivate
              else candidatePrivate }
        result := .ok plaintext
        oracle := oracleNext } := by
  simp [decryptRatchet, hf, hd, hr, hdraw, hs, ht, ha]

/-! ## Responder establishment -/

def finishResponderReceive (store : PrekeyStore) (oneTimeId kemId : Nat)
    (lastResort : Bool) (fingerprint : Option Key) (received : Step Bytes) :
    ResponderStep :=
  match received.result with
  | .error reason =>
      { store, result := .error reason, oracle := received.oracle }
  | .ok plaintext =>
      { store := consumeResponderPrekeys store oneTimeId kemId lastResort fingerprint
        result := .ok (received.session, plaintext)
        oracle := received.oracle }

/-- The responder's commit boundary is after authenticated decryption. A failed
    receive preserves every prekey-store field while retaining oracle draws. -/
theorem finishResponderReceive_refusal_keeps_store (store : PrekeyStore)
    (oneTimeId kemId : Nat) (lastResort : Bool) (fingerprint : Option Key)
    (received : Step Bytes) (reason : Refusal)
    (h : (finishResponderReceive store oneTimeId kemId lastResort fingerprint
      received).result = .error reason) :
    (finishResponderReceive store oneTimeId kemId lastResort fingerprint
      received).store = store := by
  cases received with
  | mk session result oracle =>
      cases result <;> simp_all [finishResponderReceive]

structure PreparedResponder where
  session : Session
  ratchetMessage : Bytes
  oneTimeId : Nat
  kemId : Nat
  lastResort : Bool
  fingerprint : Option Key

/-- Read and validate every responder-establishment input without changing the
    prekey store. The authenticated ratchet receive and durable consumption are
    deliberately separate operations below. -/
def prepareResponder (oracle : Oracle) (identity : Identity) (store : PrekeyStore)
    (initialMessage : Bytes) : Except Refusal PreparedResponder :=
  match Model.Messages.decodeInitialDetailed initialMessage with
  | .error reason => .error (.decode reason)
  | .ok initial =>
      match responderSignedPrekeySecret store initial.signedPrekeyId.toNat with
      | none => .error .unknownPrekeyId
      | some signedSecret =>
          match responderKemPair store initial.kemPrekeyId.toNat with
          | .error reason => .error reason
          | .ok (kemPair, lastResort) =>
              -- Every identifier the message names is resolved before the
              -- decapsulation is spent on it, the order `establish_responder`
              -- has and session-establishment.md states ("uses the identifiers
              -- to load the matching private keys, recovers SS"): an unknown
              -- one-time identifier is refused as `unknownPrekeyId`, not `kem`.
              let initiatorIdentity := initial.identity.drop 1
              let initiatorEphemeral := initial.ephemeral.drop 1
              match responderOneTimeSecret store initial.oneTimeId.toNat with
              | .error reason => .error reason
              | .ok oneTimeSecret =>
                  match oracle.kemDecaps kemPair initial.kemCiphertext with
                  | none => .error .kem
                  | some kemSecret =>
                      match oracle.dhAgree signedSecret initiatorIdentity with
                      | none => .error (.handshake .nonContributoryAgreement)
                      | some dh1 =>
                          match oracle.dhAgree identity.secret initiatorEphemeral with
                          | none => .error (.handshake .nonContributoryAgreement)
                          | some dh2 =>
                              match oracle.dhAgree signedSecret initiatorEphemeral with
                              | none => .error (.handshake .nonContributoryAgreement)
                              | some dh3 =>
                                  let dh4 := oneTimeSecret.map
                                    (fun secret => oracle.dhAgree secret initiatorEphemeral)
                                  if dh4.any Option.isNone then
                                    .error (.handshake .nonContributoryAgreement)
                                  else
                                    let sharedSecret :=
                                      Model.SessionEstablishment.sharedSecret dh1 dh2 dh3
                                        (dh4.bind id) kemSecret
                                    match lastResortReplayCheck store
                                        initial.kemPrekeyId.toNat sharedSecret lastResort with
                                    | .error reason => .error reason
                                    | .ok fingerprint =>
                                        let session : Session :=
                                          { triple := Model.Triple.initBob sharedSecret
                                              (oracle.dhPublic signedSecret) .tacenta
                                            braid := Model.Braid.initBob sharedSecret
                                            ratchetPrivate := signedSecret
                                            identityAd :=
                                              Model.SessionEstablishment.associatedData
                                                initial.identity
                                                (Model.PersistedState.SessionState.encodeEc
                                                  identity.publicKey)
                                            ourIdentityPublic := identity.publicKey
                                            peerIdentityPublic := initiatorIdentity
                                            pendingInitial := none
                                            establishedEphemeral := some initial.ephemeral }
                                        .ok
                                          { session
                                            ratchetMessage := initial.ratchetMessage
                                            oneTimeId := initial.oneTimeId.toNat
                                            kemId := initial.kemPrekeyId.toNat
                                            lastResort
                                            fingerprint }

/-- Responder establishment keeps the prekey store unchanged through the
    complete authenticated Session receive. Only its success branch consumes
    the named one-time keys or records a last-resort fingerprint. -/
def establishResponder (view : CodewordView) (oracle : Oracle) (identity : Identity)
    (store : PrekeyStore) (initialMessage : Bytes) : ResponderStep :=
  match prepareResponder oracle identity store initialMessage with
  | .error reason => { store, result := .error reason, oracle }
  | .ok prepared =>
      finishResponderReceive store prepared.oneTimeId prepared.kemId
        prepared.lastResort prepared.fingerprint
        (decryptRatchet view oracle prepared.session prepared.ratchetMessage)

/-- Every responder-establishment refusal is store-atomic, including decode,
    key lookup, replay-budget, primitive and authenticated-decrypt failures. -/
theorem establishResponder_refusal_keeps_store (view : CodewordView)
    (oracle : Oracle) (identity : Identity) (store : PrekeyStore)
    (initialMessage : Bytes) (reason : Refusal)
    (h : (establishResponder view oracle identity store initialMessage).result =
      .error reason) :
    (establishResponder view oracle identity store initialMessage).store = store := by
  cases hp : prepareResponder oracle identity store initialMessage with
  | error prepareReason => simp [establishResponder, hp]
  | ok prepared =>
      have hs := finishResponderReceive_refusal_keeps_store store prepared.oneTimeId
        prepared.kemId prepared.lastResort prepared.fingerprint
        (decryptRatchet view oracle prepared.session prepared.ratchetMessage) reason
        (by simpa [establishResponder, hp] using h)
      simpa [establishResponder, hp] using hs

/-! ## Executable lifecycle check -/

namespace Examples

def toySecret : Key := List.replicate 32 0x42
def toyAgreementDraw : Key := List.replicate 32 0x31

def toyPrekeyStore : PrekeyStore :=
  { state :=
      { (default : StoredPrekeys) with
        oneTime := [(7, [0x71]), (9, [0x91])]
        kemOneTime := [(8, [0x81], [0x82]), (10, [0xa1], [0xa2])] }
    legacyLastResortBlocked := [] }

/-- A successful one-time establishment consumes exactly the two named entries
    and leaves the other entries and replay record untouched. -/
example :
    let consumed := consumeResponderPrekeys toyPrekeyStore 7 8 false none
    consumed.state.oneTime.map Prod.fst = [9]
      ∧ consumed.state.kemOneTime.map Prod.fst = [10]
      ∧ consumed.state.seen = [] := by
  native_decide

/-- A successful last-resort establishment keeps the reusable KEM pair,
    consumes a named curve one-time prekey, and records the fingerprint. -/
example :
    let fingerprint : Key := List.replicate 32 0xf1
    let consumed := consumeResponderPrekeys toyPrekeyStore 7 8 true (some fingerprint)
    consumed.state.oneTime.map Prod.fst = [9]
      ∧ consumed.state.kemOneTime.map Prod.fst = [8, 10]
      ∧ consumed.state.seen = [(8, fingerprint)] := by
  native_decide

/-- Replay matching ignores the record's budget tag. The tag controls counting
    and rotation only; the SK-bound fingerprint decides replay globally. -/
example :
    let shared : Key := List.replicate 32 0x51
    let replayStore : PrekeyStore :=
      { toyPrekeyStore with
        state := { toyPrekeyStore.state with
          seen := [(99, lastResortFingerprint shared)] } }
    lastResortReplayCheck replayStore 8 shared true = .error .replayedLastResort := by
  simp [lastResortReplayCheck]

def toyCodewordSourceFor (secret : Key) : Bytes :=
  match (Model.Braid.send Model.Braid.toyKem (braidRandomness toyAgreementDraw)
      (Model.Braid.initAlice secret)).1 with
  | some message => message.data.map (fun chunk => chunk.source) |>.getD []
  | none => []

def toyViewFor (secret : Key) : CodewordView where
  receive := fun _ index _ => { source := toyCodewordSourceFor secret, index := index.toNat }
  send := fun _ chunk =>
    { index := UInt16.ofNat chunk.index
      data := chunk.source.take Model.CompositeHeader.chunkBytes }

def toyView : CodewordView := toyViewFor toySecret

def toyOracle (draws : List Key) : Oracle where
  draws
  braidKem := Model.Braid.toyKem
  dhPublic := id
  dhAgree := fun _ _ => some (List.replicate 32 0xdd)
  aeadSeal := fun enc mac iv plaintext ad =>
    Model.Kdf.hmac (enc ++ mac ++ iv) ad ++ plaintext
  aeadOpen := fun enc mac iv ciphertext ad =>
    if ciphertext.take Model.Kdf.hashLen == Model.Kdf.hmac (enc ++ mac ++ iv) ad then
      some (ciphertext.drop Model.Kdf.hashLen)
    else none
  kemEncaps := fun _ _ => some ([], List.replicate 32 0xee)
  kemDecaps := fun _ _ => some (List.replicate 32 0xee)
  sigVerify := fun _ _ _ => true
  sigSign := fun _ _ _ => List.replicate 64 0x55

def toyAlice (secret : Key) : Session :=
  { triple := Model.Triple.initAlice secret (List.replicate 32 0x21)
      (List.replicate 32 0x22) (List.replicate 32 0xdd) .tacenta
    braid := Model.Braid.initAlice secret
    ratchetPrivate := List.replicate 32 0xa1
    identityAd := [0x01, 0x02]
    ourIdentityPublic := List.replicate 32 0x11
    peerIdentityPublic := List.replicate 32 0x22
    pendingInitial := none
    establishedEphemeral := none }

def toyBob (secret : Key) : Session :=
  { triple := Model.Triple.initBob secret (List.replicate 32 0x22) .tacenta
    braid := Model.Braid.initBob secret
    ratchetPrivate := List.replicate 32 0xb1
    identityAd := [0x01, 0x02]
    ourIdentityPublic := List.replicate 32 0x22
    peerIdentityPublic := List.replicate 32 0x11
    pendingInitial := none
    establishedEphemeral := none }

def toyAliceIdentity : Identity :=
  { secret := List.replicate 32 0x11, publicKey := List.replicate 32 0x11 }

def toyBobIdentity : Identity :=
  { secret := List.replicate 32 0x22, publicKey := List.replicate 32 0x22 }

def toySignedPrekey : Key := List.replicate 32 0x23

def toyBundle : Bundle :=
  { identityKey := toyBobIdentity.publicKey
    signedPrekey := toySignedPrekey
    signedPrekeySig := List.replicate 64 0x51
    kemPrekey := [0x61]
    kemPrekeySig := List.replicate 64 0x52
    oneTimePrekey := none
    signedPrekeyId := UInt32.ofNat 1
    oneTimeId := absentId
    kemPrekeyId := UInt32.ofNat 2 }

def toyResponderStore : PrekeyStore :=
  { state :=
      { (default : StoredPrekeys) with
        identityPublic := toyBobIdentity.publicKey
        signedPrekeySecret := toySignedPrekey
        signedPrekeyId := 1
        signedPrekeySig := List.replicate 64 0x51
        kemPair := [0x62]
        kemId := 2
        kemSig := List.replicate 64 0x52
        nextId := 3 }
    legacyLastResortBlocked := [] }

def toyEstablishedSecret : Key :=
  Model.SessionEstablishment.sharedSecret
    (List.replicate 32 0xdd) (List.replicate 32 0xdd)
    (List.replicate 32 0xdd) none (List.replicate 32 0xee)

def toyOneTimeBundle : Bundle :=
  { toyBundle with
    kemPrekey := [0x64]
    oneTimePrekey := some (List.replicate 32 0x24)
    oneTimeId := UInt32.ofNat 3
    kemPrekeyId := UInt32.ofNat 4 }

def toyOneTimeResponderStore : PrekeyStore :=
  { toyResponderStore with
    state :=
      { toyResponderStore.state with
        oneTime := [(3, List.replicate 32 0x24)]
        kemOneTime := [(4, [0x65], List.replicate 64 0x54)]
        nextId := 5 } }

def toyOneTimeEstablishedSecret : Key :=
  Model.SessionEstablishment.sharedSecret
    (List.replicate 32 0xdd) (List.replicate 32 0xdd)
    (List.replicate 32 0xdd) (some (List.replicate 32 0xdd))
    (List.replicate 32 0xee)

/-- One complete Session send and receive runs through both ratchets, the Braid,
    wire codecs and the AEAD boundary. Fixed toy primitives make it executable;
    the boundary-refinement work later replaces them with related Rust calls. -/
example :
    let sent := encrypt toyView (toyOracle [toyAgreementDraw])
      (toyAlice toySecret) [0xde, 0xad]
    (match sent.result with
      | .error _ => false
      | .ok wire =>
          match (decrypt toyView (toyOracle [List.replicate 32 0x32])
            (toyBob toySecret) wire).result with
          | .error _ => false
          | .ok plaintext => plaintext == [0xde, 0xad]) = true := by
  native_decide

/-- A complete public lifecycle opens the initiator, sends its initial wrapper,
    opens the responder, authenticates the first plaintext, and records the
    accepted last-resort handshake. -/
example :
    let initiated := establishInitiator
      (toyOracle [List.replicate 32 0x12, List.replicate 32 0x13,
        List.replicate 32 0x14]) toyAliceIdentity toyBundle toyBobIdentity.publicKey
    (match initiated.result with
      | .error _ => false
      | .ok alice =>
          let sent := encrypt (toyViewFor toyEstablishedSecret)
            (toyOracle [toyAgreementDraw]) alice [0xde, 0xad]
          match sent.result with
          | .error _ => false
          | .ok wire =>
              let responded := establishResponder (toyViewFor toyEstablishedSecret)
                (toyOracle [List.replicate 32 0x32]) toyBobIdentity toyResponderStore wire
              match responded.result with
              | .error _ => false
              | .ok (_, plaintext) =>
                  plaintext == [0xde, 0xad]
                    && responded.store.state.seen.length == 1) = true := by
  native_decide

/-- The full one-time path uses DH4 and consumes both named one-time entries
    only after the first ciphertext authenticates. It records no replay entry. -/
example :
    let initiated := establishInitiator
      (toyOracle [List.replicate 32 0x12, List.replicate 32 0x13,
        List.replicate 32 0x14]) toyAliceIdentity toyOneTimeBundle
        toyBobIdentity.publicKey
    (match initiated.result with
      | .error _ => false
      | .ok alice =>
          let sent := encrypt (toyViewFor toyOneTimeEstablishedSecret)
            (toyOracle [toyAgreementDraw]) alice [0xca, 0xfe]
          match sent.result with
          | .error _ => false
          | .ok wire =>
              let responded := establishResponder (toyViewFor toyOneTimeEstablishedSecret)
                (toyOracle [List.replicate 32 0x32]) toyBobIdentity
                toyOneTimeResponderStore wire
              match responded.result with
              | .error _ => false
              | .ok (_, plaintext) =>
                  plaintext == [0xca, 0xfe]
                    && responded.store.state.oneTime.isEmpty
                    && responded.store.state.kemOneTime.isEmpty
                    && responded.store.state.seen.isEmpty) = true := by
  native_decide

end Examples

end Model.Lifecycle
