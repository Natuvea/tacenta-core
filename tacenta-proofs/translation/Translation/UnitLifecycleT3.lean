import Translation.SessionUnitTripleT3
import Translation.SessionUnitBraidT3
import Model.Lifecycle

/-!
# Session lifecycle T3 relation

This file starts the end-to-end refinement layer by fixing the relation between
the translated shipping `Session` and `Model.Lifecycle.Session`.  The two
primitive key types are opaque at the Aeneas boundary, so their byte views are
parameters here.  `OracleOf` will constrain those same views against every
primitive call; the state relation does not invent a second interpretation.
-/

namespace Tacenta.UnitLifecycleT3

open Aeneas Aeneas.Std Result
open tacenta_session_unit

abbrev Bytes := List UInt8

/-- The byte interpretation of the two opaque X25519 boundary types.  These
are the only fields of a lifecycle state that cannot be read structurally from
the generated translation. -/
structure DhView where
  privateKey : tacenta_boundary.dh.PrivateKey → Bytes
  publicKey : tacenta_boundary.dh.PublicKeyBytes → Bytes

/-- A translated byte vector as the model's bytes. -/
def vecOf (v : alloc.vec.Vec Std.U8) : Bytes :=
  v.val.map Tacenta.SessionUnitBraidT3.u8

/-- The pending initial record is field-for-field apart from the opaque public
key and the scalar wrappers. -/
def pendingInitialOf (view : DhView)
    (p : lifecycle.PendingInitial) : Model.Lifecycle.PendingInitial where
  ephemeralPublic := view.publicKey p.ephemeral_public
  kemCiphertext := vecOf p.kem_ciphertext
  signedPrekeyId := p.signed_prekey_id.val
  oneTimePrekeyId := p.one_time_prekey_id.val
  kemPrekeyId := p.kem_prekey_id.val

/-- The shipping Session refines the executable lifecycle model.

The Triple and Braid fields reuse their existing aggregate refinement
relations.  The six remaining state components are byte equality (with the
two optional records mapped field-for-field). -/
structure SessionRefines (view : DhView) (K : Model.Braid.Kem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session) : Prop where
  triple : Tacenta.SessionUnitTripleT3.StateRefines
    Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
    real.triple model.triple
  braid : Tacenta.SessionUnitBraidT3.StateRefines K real.braid.state model.braid
  ratchetPrivate : view.privateKey real.ratchet_private = model.ratchetPrivate
  identityAd : vecOf real.identity_ad = model.identityAd
  ourIdentityPublic : view.publicKey real.our_identity_public = model.ourIdentityPublic
  peerIdentityPublic : view.publicKey real.peer_identity_public = model.peerIdentityPublic
  pendingInitial : real.pending_initial.map (pendingInitialOf view) = model.pendingInitial
  establishedEphemeral : real.established_ephemeral.map vecOf = model.establishedEphemeral

/-! ## Primitive oracle agreement

The lifecycle model has nine primitive functions.  Each clause below names
the complete translated argument list.  Randomness is one ordered trace:
`random_secret`, KEM encapsulation and signing must each consume exactly its
head and return a state interpreted by the tail. -/

def arrayOf {n : Usize} (a : Array Std.U8 n) : Bytes :=
  a.val.map Tacenta.SessionUnitBraidT3.u8

def sliceOf (s : Slice Std.U8) : Bytes :=
  s.val.map Tacenta.SessionUnitBraidT3.u8

structure KemView where
  keyPair : tacenta_boundary.kem.KeyPair → Bytes

def resultOptionOf {A B : Type} (f : A → B) : core.result.Result A Unit → Option B
  | .Ok value => some (f value)
  | .Err _ => none

def verified : core.result.Result Unit Unit → Bool
  | .Ok _ => true
  | .Err _ => false

def encapsulationOf :
    core.result.Result (alloc.vec.Vec Std.U8 × Array Std.U8 32#usize) Unit →
      Option (Bytes × Model.Lifecycle.Key) :=
  resultOptionOf (fun value => (vecOf value.1, arrayOf value.2))

/-- Agreement between all nine translated primitive calls and one executable
model oracle.  `trace` interprets the threaded RNG state; the three random
clauses make call order observable rather than allowing a fresh existential
draw at each call. -/
structure OracleOf {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (dh : DhView) (kem : KemView) (trace : R → List Model.Lifecycle.Key)
    (oracle : Model.Lifecycle.Oracle) : Prop where
  dhPublic : ∀ secret,
    ∃ publicKey, tacenta_boundary.dh.PrivateKey.public_key secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)
  dhAgree : ∀ secret publicKey,
    ∃ result, tacenta_boundary.dh.PrivateKey.agree secret publicKey = ok result ∧
      result.map arrayOf = oracle.dhAgree (dh.privateKey secret) (dh.publicKey publicKey)
  aeadSeal : ∀ key1 key2 iv ad plaintext,
    ∃ ciphertext,
      tacenta_boundary.aead.encrypt key1 key2 iv ad plaintext = ok ciphertext ∧
      vecOf ciphertext = oracle.aeadSeal (arrayOf key1) (arrayOf key2)
        (arrayOf iv) (sliceOf ad) (sliceOf plaintext)
  aeadOpen : ∀ key1 key2 iv ad ciphertext,
    ∃ result,
      tacenta_boundary.aead.decrypt key1 key2 iv ad ciphertext = ok result ∧
      resultOptionOf vecOf result = oracle.aeadOpen (arrayOf key1) (arrayOf key2)
        (arrayOf iv) (sliceOf ad) (sliceOf ciphertext)
  kemEncapsulate : ∀ publicKey rng draw rest, trace rng = draw :: rest →
    ∃ result rng',
      tacenta_boundary.kem.encapsulate rngCore cryptoRng publicKey rng = ok (result, rng') ∧
      trace rng' = rest ∧
      encapsulationOf result = oracle.kemEncaps (sliceOf publicKey) draw
  kemDecapsulate : ∀ keyPair ciphertext,
    ∃ result,
      tacenta_boundary.kem.decapsulate keyPair ciphertext = ok result ∧
      resultOptionOf arrayOf result =
        oracle.kemDecaps (kem.keyPair keyPair) (sliceOf ciphertext)
  sigVerify : ∀ publicKey message signature,
    ∃ result,
      tacenta_boundary.xeddsa.verify publicKey message signature = ok result ∧
      verified result = oracle.sigVerify (dh.publicKey publicKey)
        (sliceOf message) (arrayOf signature)
  sigSign : ∀ secret message rng draw rest, trace rng = draw :: rest →
    ∃ signature rng',
      tacenta_boundary.xeddsa.sign rngCore cryptoRng secret message rng = ok (signature, rng') ∧
      trace rng' = rest ∧
      arrayOf signature = oracle.sigSign (arrayOf secret) (sliceOf message) draw
  random32 : ∀ rng draw rest, trace rng = draw :: rest →
    ∃ value rng',
      lifecycle.random_secret rngCore cryptoRng rng = ok (value, rng') ∧
      arrayOf value = draw ∧ trace rng' = rest

/-! ## Erasure-codeword view agreement -/

def modelChunkOf (source : Bytes) (chunk : tacenta_erasure.Chunk) :
    Model.Braid.Chunk where
  source := source
  index := chunk.index.val

def modelCodewordOf (chunk : tacenta_erasure.Chunk) :
    Model.CompositeHeader.Codeword where
  index := UInt16.ofNat chunk.index.val
  data := arrayOf chunk.data

/-- The lifecycle model's wire view names exactly the source and bytes of an
honest chunk from the existing Braid refinement.  Both directions use the same
relation, so receive cannot reinterpret a codeword differently from send. -/
structure CodewordViewOf (view : Model.Lifecycle.CodewordView) : Prop where
  receive : ∀ state source chunk,
    Tacenta.SessionUnitBraidT3.CodewordOf source chunk →
    view.receive state (UInt16.ofNat chunk.index.val) (arrayOf chunk.data) =
      modelChunkOf source chunk
  send : ∀ state source chunk,
    Tacenta.SessionUnitBraidT3.CodewordOf source chunk →
    view.send state (modelChunkOf source chunk) = modelCodewordOf chunk

def agreementTypeOf : tacenta_wire.AgreementType →
    Model.CompositeHeader.AgreementType
  | .None => .none
  | .Hdr => .hdr
  | .Ek => .ek
  | .EkCt1Ack => .ekCt1Ack
  | .Ct1 => .ct1
  | .Ct2 => .ct2

def WireCodewordRefines (real : tacenta_wire.Codeword)
    (model : Model.CompositeHeader.Codeword) : Prop :=
  real.index.val = model.index.toNat ∧ arrayOf real.data = model.data

structure CompositeRefines (real : tacenta_wire.Composite)
    (model : Model.CompositeHeader.Composite) : Prop where
  dh : arrayOf real.dh = model.dh
  pn : real.pn.val = model.pn.toNat
  n : real.n.val = model.n.toNat
  pqEpoch : real.pq_epoch.val = model.pqEpoch.toNat
  pqN : real.pq_n.val = model.pqN.toNat
  agEpoch : real.ag_epoch.val = model.agEpoch.toNat
  agType : agreementTypeOf real.ag_type = model.agType
  agChunk : match real.ag_chunk, model.agChunk with
    | none, none => True
    | some realChunk, some modelChunk => WireCodewordRefines realChunk modelChunk
    | _, _ => False

theorem agreement_type_of_refines (real : tacenta_braid.MsgType)
    (model : Model.Braid.MsgType)
    (hrel : Tacenta.SessionUnitBraidT3.MsgTypeRefines real model) :
    ∃ wire,
      lifecycle.agreement_type_of real = ok wire ∧
      Model.Lifecycle.compositeTypeOf model = some (agreementTypeOf wire) := by
  cases real <;> cases model <;>
    simp [Tacenta.SessionUnitBraidT3.MsgTypeRefines,
      lifecycle.agreement_type_of, Model.Lifecycle.compositeTypeOf,
      agreementTypeOf] at hrel ⊢

theorem msg_type_of_refines (wire : tacenta_wire.AgreementType) :
    ∃ real,
      lifecycle.msg_type_of wire = ok real ∧
      Tacenta.SessionUnitBraidT3.MsgTypeRefines real
        (Model.Lifecycle.braidTypeOf (agreementTypeOf wire)) := by
  cases wire <;>
    simp [lifecycle.msg_type_of, Model.Lifecycle.braidTypeOf,
      Tacenta.SessionUnitBraidT3.MsgTypeRefines, agreementTypeOf]

/-! ## Public refusal correspondence

Every concrete shipping `Err` has one public model refusal.  Keeping this as
one total conversion prevents the operation theorems from silently omitting a
constructor or choosing different meanings for the same error on two paths. -/

def ratchetRefusalOf : tacenta_ratchet.RatchetError → Model.Lifecycle.RatchetRefusal
  | .TooManySkipped => .tooManySkipped
  | .SkippedStoreFull => .skippedStoreFull
  | .NoSendingChain => .noSendingChain
  | .NoReceivingChain => .noReceivingChain
  | .OutOfOrder => .outOfOrder
  | .ChainExhausted => .chainExhausted

def sparseRefusalOf : tacenta_spqr.SpqrError → Model.Lifecycle.SparseRefusal
  | .EpochOutOfOrder => .epochOutOfOrder
  | .NoChain => .noChain
  | .ChainRetired => .chainRetired
  | .TooManySkipped => .tooManySkipped
  | .SkippedStoreFull => .skippedStoreFull
  | .OutOfOrder => .outOfOrder
  | .ChainExhausted => .chainExhausted

def tripleRefusalOf : tacenta_triple.TripleError → Model.Lifecycle.TripleRefusal
  | .Classical reason => .classical (ratchetRefusalOf reason)
  | .PostQuantum reason => .postQuantum (sparseRefusalOf reason)

def handshakeRefusalOf : SessionError → Model.Lifecycle.HandshakeRefusal
  | .BadSignedPrekeySignature => .badSignedPrekeySignature
  | .BadKemPrekeySignature => .badKemPrekeySignature
  | .NonContributoryAgreement => .nonContributoryAgreement

def decodeRefusalOf : tacenta_wire.DecodeError → Model.Messages.DecodeRefusal
  | .UnknownVersion => .unknownVersion
  | .WrongType => .wrongType
  | .TooShort => .tooShort
  | .LengthOverrun => .lengthOverrun

def refusalOf : lifecycle.Error → Model.Lifecycle.Refusal
  | .Triple reason => .triple (tripleRefusalOf reason)
  | .Handshake reason => .handshake (handshakeRefusalOf reason)
  | .Kem => .kem
  | .Decode reason => .decode (decodeRefusalOf reason)
  | .BadEncoding => .badEncoding
  | .InconsistentBundle => .inconsistentBundle
  | .UnexpectedIdentity => .unexpectedIdentity
  | .UnknownPrekeyId => .unknownPrekeyId
  | .Aead => .aead
  | .NotARepeatedInitial => .notARepeatedInitial
  | .ReplayedLastResort => .replayedLastResort
  | .LegacyLastResortRecord => .legacyLastResortRecord
  | .LastResortRecordFull => .lastResortRecordFull
  | .AgreementFailed => .agreementFailed

def ratchetSendRefusalOfReal : tacenta_ratchet.RatchetError →
    Option Model.Ratchet.SendRefusal
  | .NoSendingChain => some .noSendingChain
  | .ChainExhausted => some .chainExhausted
  | _ => none

def sparseSendRefusalOfReal : tacenta_spqr.SpqrError →
    Option Model.SparseRatchet.SendRefusal
  | .EpochOutOfOrder => some .epochOutOfOrder
  | .NoChain => some .noChain
  | .ChainRetired => some .chainRetired
  | .ChainExhausted => some .chainExhausted
  | _ => none

def tripleSendRefusalOfReal : tacenta_triple.TripleError →
    Option Model.Triple.SendRefusal
  | .Classical reason => (ratchetSendRefusalOfReal reason).map .classical
  | .PostQuantum reason => (sparseSendRefusalOfReal reason).map .postQuantum

def ratchetReceiveRefusalOfReal : tacenta_ratchet.RatchetError →
    Option Model.Ratchet.ReceiveRefusal
  | .TooManySkipped => some .tooManySkipped
  | .SkippedStoreFull => some .skippedStoreFull
  | .NoReceivingChain => some .noReceivingChain
  | .OutOfOrder => some .outOfOrder
  | .ChainExhausted => some .chainExhausted
  | .NoSendingChain => none

def sparseReceiveRefusalOfReal : tacenta_spqr.SpqrError →
    Model.SparseRatchet.ReceiveRefusal
  | .EpochOutOfOrder => .epochOutOfOrder
  | .NoChain => .noChain
  | .ChainRetired => .chainRetired
  | .TooManySkipped => .tooManySkipped
  | .SkippedStoreFull => .skippedStoreFull
  | .OutOfOrder => .outOfOrder
  | .ChainExhausted => .chainExhausted

def tripleReceiveRefusalOfReal : tacenta_triple.TripleError →
    Option Model.Triple.ReceiveRefusal
  | .Classical reason => (ratchetReceiveRefusalOfReal reason).map .classical
  | .PostQuantum reason => some (.postQuantum (sparseReceiveRefusalOfReal reason))

theorem tripleSendRefusalOfReal_sound {realReason : tacenta_triple.TripleError}
    {modelReason : Model.Triple.SendRefusal}
    (h : tripleSendRefusalOfReal realReason = some modelReason) :
    refusalOf (.Triple realReason) =
      Model.Lifecycle.tripleSendRefusalOf modelReason := by
  cases realReason with
  | Classical reason =>
      cases reason <;> cases modelReason <;>
        simp [tripleSendRefusalOfReal, ratchetSendRefusalOfReal] at h <;>
        cases h <;>
        rfl
  | PostQuantum reason =>
      cases reason <;> cases modelReason <;>
        simp [tripleSendRefusalOfReal, sparseSendRefusalOfReal] at h <;>
        cases h <;>
        rfl

theorem tripleReceiveRefusalOfReal_sound {realReason : tacenta_triple.TripleError}
    {modelReason : Model.Triple.ReceiveRefusal}
    (h : tripleReceiveRefusalOfReal realReason = some modelReason) :
    refusalOf (.Triple realReason) =
      Model.Lifecycle.tripleReceiveRefusalOf modelReason := by
  cases realReason with
  | Classical reason =>
      cases reason <;> cases modelReason <;>
        simp [tripleReceiveRefusalOfReal, ratchetReceiveRefusalOfReal] at h <;>
        cases h <;>
        rfl
  | PostQuantum reason =>
      cases reason <;> cases modelReason <;>
        simp [tripleReceiveRefusalOfReal, sparseReceiveRefusalOfReal] at h <;>
        cases h <;>
        rfl

theorem ratchetRefusalOf_injective : Function.Injective ratchetRefusalOf := by
  intro left right h
  cases left <;> cases right <;> simp [ratchetRefusalOf] at h ⊢

theorem sparseRefusalOf_injective : Function.Injective sparseRefusalOf := by
  intro left right h
  cases left <;> cases right <;> simp [sparseRefusalOf] at h ⊢

theorem tripleRefusalOf_injective : Function.Injective tripleRefusalOf := by
  intro left right h
  cases left <;> cases right <;> simp [tripleRefusalOf] at h ⊢
  · exact ratchetRefusalOf_injective h
  · exact sparseRefusalOf_injective h

theorem handshakeRefusalOf_injective : Function.Injective handshakeRefusalOf := by
  intro left right h
  cases left <;> cases right <;> simp [handshakeRefusalOf] at h ⊢

theorem decodeRefusalOf_injective : Function.Injective decodeRefusalOf := by
  intro left right h
  cases left <;> cases right <;> simp [decodeRefusalOf] at h ⊢

theorem refusalOf_injective : Function.Injective refusalOf := by
  intro left right h
  cases left <;> cases right <;> simp [refusalOf] at h ⊢
  · exact tripleRefusalOf_injective h
  · exact handshakeRefusalOf_injective h
  · exact decodeRefusalOf_injective h

theorem refusalOf_ne_ceiling (reason : lifecycle.Error) :
    refusalOf reason ≠ .ceiling := by
  cases reason <;> simp [refusalOf]

def ResultRefines
    (real : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error)
    (model : Except Model.Lifecycle.Refusal Bytes) : Prop :=
  match real, model with
  | .Ok bytes, .ok modelBytes => vecOf bytes = modelBytes
  | .Err reason, .error modelReason => refusalOf reason = modelReason
  | _, _ => False

/-- Common target for every stateful Session operation: public result, full
state and remaining randomness all agree after the translated call. -/
structure StepRefines {R : Type} (trace : R → List Model.Lifecycle.Key)
    (dh : DhView) (K : Model.Braid.Kem)
    (real : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error ×
      lifecycle.Session × R)
    (model : Model.Lifecycle.Step Bytes) : Prop where
  result : ResultRefines real.1 model.result
  session : SessionRefines dh K real.2.1 model.session
  draws : trace real.2.2 = model.oracle.draws

/-! ## Lifecycle observations -/

theorem braid_failed_refines (K : Model.Braid.Kem)
    (real : tacenta_braid.Braid) (model : Model.Braid.BraidState)
    (hrel : Tacenta.SessionUnitBraidT3.StateRefines K real.state model) :
    tacenta_braid.Braid.failed real = ok (Model.Lifecycle.braidFailed model) := by
  cases hr : real.state <;> cases hm : model <;>
    simp [tacenta_braid.Braid.failed, Model.Lifecycle.braidFailed,
      Tacenta.SessionUnitBraidT3.StateRefines, hr, hm] at hrel ⊢

/-- The first `encrypt` refusal branch agrees exactly: a terminal Braid returns
`AgreementFailed`, leaves the complete Session and RNG untouched, and performs
no primitive call. -/
theorem encrypt_terminal_guard_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (dh : DhView) (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
    (model : Model.Lifecycle.Session) (plaintext : Slice Std.U8) (rng : R)
    (hrel : SessionRefines dh K real model)
    (hfailed : Model.Lifecycle.agreementFailed model = true) :
    lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng =
        ok (.Err lifecycle.Error.AgreementFailed, real, rng) ∧
      Model.Lifecycle.encrypt view oracle model (sliceOf plaintext) =
        { session := model, result := .error .agreementFailed, oracle := oracle } := by
  have hm : model.braid = .failed :=
    (Model.Lifecycle.agreementFailed_iff model).mp hfailed
  have hbraid := braid_failed_refines K real.braid model.braid hrel.braid
  have hbf : Model.Lifecycle.braidFailed model.braid = true :=
    (Model.Lifecycle.braidFailed_iff model.braid).2 hm
  rw [hbf] at hbraid
  constructor
  · unfold lifecycle.Session.encrypt
    rw [hbraid]
    simp
  · exact Model.Lifecycle.encrypt_terminal_guard view oracle model
      (sliceOf plaintext) hfailed

theorem encrypt_terminal_guard_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng : R)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hfailed : Model.Lifecycle.agreementFailed model = true) :
    ∃ output,
      lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext)) := by
  have h := encrypt_terminal_guard_refines rngCore cryptoRng dh K view oracle
    real model plaintext rng hrel hfailed
  refine ⟨(.Err lifecycle.Error.AgreementFailed, real, rng), h.1, ?_⟩
  rw [h.2]
  exact ⟨rfl, hrel, htrace⟩

/-- Once the Braid send step is related, its terminal transition is committed
on both sides before `AgreementFailed` is returned.  This outer lifecycle fact
does not depend on the unused message, epoch or sparse output. -/
theorem encrypt_braid_failure_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng rngNext : R)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output) (realBraidNext : tacenta_braid.Braid)
    (modelMessage : Option Model.Braid.Msg) (modelEpoch : Nat)
    (modelOutput : Option Model.Braid.Output) (modelBraidNext : Model.Braid.BraidState)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hsendReal : tacenta_braid.Braid.send rngCore cryptoRng real.braid rng =
      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
    (hsendModel : Model.Lifecycle.sendAgreement oracle model.braid =
      some ((modelMessage, modelEpoch, modelOutput, modelBraidNext), oracleNext))
    (hnext : Tacenta.SessionUnitBraidT3.StateRefines K
      realBraidNext.state modelBraidNext)
    (hfailed : Model.Lifecycle.braidFailed modelBraidNext = true)
    (htrace : trace rngNext = oracleNext.draws) :
    ∃ output,
      lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext)) := by
  have hrealReady := braid_failed_refines K real.braid model.braid hrel.braid
  have hmodelReady : Model.Lifecycle.braidFailed model.braid = false := by
    cases hb : model.braid <;>
      simp [Model.Lifecycle.agreementFailed, Model.Lifecycle.braidFailed, hb] at hready ⊢
  rw [hmodelReady] at hrealReady
  have hrealFailed := braid_failed_refines K realBraidNext modelBraidNext hnext
  rw [hfailed] at hrealFailed
  let realNext := { real with braid := realBraidNext }
  let modelNext := { model with braid := modelBraidNext }
  have hnextSession : SessionRefines dh K realNext modelNext := by
    exact ⟨hrel.triple, hnext, hrel.ratchetPrivate, hrel.identityAd,
      hrel.ourIdentityPublic, hrel.peerIdentityPublic, hrel.pendingInitial,
      hrel.establishedEphemeral⟩
  have hreal : lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng =
      ok (.Err lifecycle.Error.AgreementFailed, realNext, rngNext) := by
    unfold lifecycle.Session.encrypt
    simp [hrealReady, hsendReal, hrealFailed, realNext]
  have hmodel : Model.Lifecycle.encrypt view oracle model (sliceOf plaintext) =
      { session := modelNext, result := .error .agreementFailed,
        oracle := oracleNext } := by
    simp [Model.Lifecycle.encrypt, hready, hsendModel, hfailed, modelNext]
  refine ⟨(.Err lifecycle.Error.AgreementFailed, realNext, rngNext), hreal, ?_⟩
  rw [hmodel]
  exact ⟨rfl, hnextSession, htrace⟩

def realSparseOutputOf (output : Option tacenta_braid.Output) :
    Result (Option tacenta_spqr.Output) :=
  match output with
  | none => ok none
  | some value => do
      let converted ← tacenta_spqr.Output.new value.key_epoch value.key
      ok (some converted)

inductive RealTripleRefusal (state : tacenta_triple.State) (epoch : Std.U64)
    (output : Option tacenta_braid.Output) (candidate : tacenta_triple.State)
    (reason : tacenta_triple.TripleError) : Prop where
  | none
      (hout : output = none)
      (hsend : lifecycle.send_candidate state epoch none = ok (candidate, .Err reason))
  | some (realOutput : tacenta_braid.Output) (converted : tacenta_spqr.Output)
      (hout : output = some realOutput)
      (hconverted : tacenta_spqr.Output.new realOutput.key_epoch realOutput.key = ok converted)
      (hsend : lifecycle.send_candidate state epoch (some converted) =
        ok (candidate, .Err reason))

/-- The Triple refusal branch is atomic at the lifecycle boundary.  Braid has
already produced a candidate next state, but neither implementation commits it
when Triple send refuses; only the already-consumed RNG trace advances. -/
theorem encrypt_triple_refusal_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng rngNext : R)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output) (realBraidNext : tacenta_braid.Braid)
    (candidate : tacenta_triple.State)
    (realReason : tacenta_triple.TripleError)
    (modelMessage : Model.Braid.Msg) (modelEpoch : Nat)
    (modelOutput : Option Model.Braid.Output) (modelBraidNext : Model.Braid.BraidState)
    (modelReason : Model.Triple.SendRefusal)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hsendReal : tacenta_braid.Braid.send rngCore cryptoRng real.braid rng =
      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
    (htripleReal : RealTripleRefusal real.triple realEpoch realOutput
      candidate realReason)
    (hsendModel : Model.Lifecycle.sendAgreement oracle model.braid =
      some ((some modelMessage, modelEpoch, modelOutput, modelBraidNext), oracleNext))
    (hnext : Tacenta.SessionUnitBraidT3.StateRefines K
      realBraidNext.state modelBraidNext)
    (hnotFailed : Model.Lifecycle.braidFailed modelBraidNext = false)
    (htripleModel : Model.Triple.sendDetailed model.triple modelEpoch
      (Model.Lifecycle.sparseOutputOf modelOutput) = .error modelReason)
    (hreason : tripleSendRefusalOfReal realReason = some modelReason)
    (htrace : trace rngNext = oracleNext.draws) :
    ∃ output,
      lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext)) := by
  have hrealReady := braid_failed_refines K real.braid model.braid hrel.braid
  have hmodelReady : Model.Lifecycle.braidFailed model.braid = false := by
    cases hb : model.braid <;>
      simp [Model.Lifecycle.agreementFailed, Model.Lifecycle.braidFailed, hb] at hready ⊢
  rw [hmodelReady] at hrealReady
  have hrealNext := braid_failed_refines K realBraidNext modelBraidNext hnext
  rw [hnotFailed] at hrealNext
  have hreal : lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng =
      ok (.Err (.Triple realReason), real, rngNext) := by
    unfold lifecycle.Session.encrypt
    simp [hrealReady, hsendReal, hrealNext]
    cases htripleReal with
    | none hout hsend => simp [hout, hsend]
    | some value converted hout hconverted hsend =>
        simp [hout, hconverted, hsend]
  have hmodel : Model.Lifecycle.encrypt view oracle model (sliceOf plaintext) =
      { session := model,
        result := .error (Model.Lifecycle.tripleSendRefusalOf modelReason),
        oracle := oracleNext } := by
    simp [Model.Lifecycle.encrypt, hready, hsendModel, hnotFailed, htripleModel]
  refine ⟨(.Err (.Triple realReason), real, rngNext), hreal, ?_⟩
  rw [hmodel]
  exact ⟨tripleSendRefusalOfReal_sound hreason, hrel, htrace⟩

end Tacenta.UnitLifecycleT3
