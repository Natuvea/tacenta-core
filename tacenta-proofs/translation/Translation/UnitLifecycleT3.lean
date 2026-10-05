import Translation.SessionUnitTripleT3
import Translation.SessionUnitBraidT3
import Translation.SessionUnitWireT3
import Translation.SessionUnitWireInitialT3
import Translation.SessionUnitSessionT1
import Model.Lifecycle
import Mathlib.Tactic.IntervalCases

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

/-! The lifecycle unit and the Braid port call the same generated KDF
    operations. Keep the correspondence at the shared lifecycle boundary so
    callers do not restate the same primitive contracts under Braid-specific
    names. This is a type-level reuse theorem; it does not manufacture either
    contract for the shipped implementation. -/
theorem braid_kdf_contracts_of_session
    (hmac : Tacenta.SessionUnitT3.HmacAgrees)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees) :
    Tacenta.SessionUnitBraidT3.BraidHmacAgrees ∧
      Tacenta.SessionUnitBraidT3.BraidHkdfAgrees := by
  exact ⟨hmac, hkdf⟩

/-! ## Primitive oracle agreement

The lifecycle model has ten primitive operations and twelve contract clauses:
KEM encapsulation has one success clause and two refusal clauses. Each clause
below names the complete translated argument list. Randomness is one ordered trace:
`random_secret` and KEM encapsulation each consume the trace's head and signing
its first two entries, and each returns a state interpreted by the rest. -/

def arrayOf {n : Usize} (a : Array Std.U8 n) : Bytes :=
  a.val.map Tacenta.SessionUnitBraidT3.u8

/-- The opaque public-key byte projection agrees with the interpretation used
by `DhView`.  This is a representation relation for a boundary already present
in T1, rather than a new cryptographic primitive contract. -/
structure DhCodecOf (view : DhView) : Prop where
  privateFromBytes : ∀ bytes, ∃ privateKey,
    tacenta_boundary.dh.PrivateKey.from_bytes bytes = ok privateKey ∧
    view.privateKey privateKey = arrayOf bytes
  fromBytes : ∀ bytes, ∃ publicKey,
    tacenta_boundary.dh.PublicKeyBytes.from_bytes bytes = ok publicKey ∧
    view.publicKey publicKey = arrayOf bytes
  asBytes : ∀ publicKey, ∃ bytes,
    tacenta_boundary.dh.PublicKeyBytes.as_bytes publicKey = ok bytes ∧
    arrayOf bytes = view.publicKey publicKey

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
  aeadOpen : ∀ key1 key2 iv ciphertext associatedData,
    ∃ result,
      tacenta_boundary.aead.decrypt key1 key2 iv ciphertext associatedData = ok result ∧
      resultOptionOf vecOf result = oracle.aeadOpen (arrayOf key1) (arrayOf key2)
        (arrayOf iv) (sliceOf ciphertext) (sliceOf associatedData)
  /-- A model refusal is allowed for malformed public keys; only a model
      `some` result for a model-valid public key obliges the real boundary to
      produce the matching success. This keeps the contract satisfiable for
      the wrapper's pre-RNG length refusal while making invalid-key refusal
      explicit rather than relying on `kemEncaps = none` to imply it. -/
  kemEncapsulateSuccess : ∀ publicKey rng draw rest expected,
    trace rng = draw :: rest →
    oracle.kemValid (sliceOf publicKey) = true →
    oracle.kemEncaps (sliceOf publicKey) draw = some expected →
    ∃ result rng',
      tacenta_boundary.kem.encapsulate rngCore cryptoRng publicKey rng =
        ok (.Ok result, rng') ∧
      trace rng' = rest ∧
      encapsulationOf (.Ok result) = some expected
  /-- Invalid-key refusal is pre-RNG and is represented by the model's
      validity predicate, so the empty-trace case remains observable. -/
  kemInvalidKey : ∀ publicKey rng error,
    oracle.kemValid (sliceOf publicKey) = false →
    tacenta_boundary.kem.encapsulate rngCore cryptoRng publicKey rng =
      ok (.Err error, rng)
  kemEncapsulateError : ∀ publicKey rng error,
    tacenta_boundary.kem.encapsulate rngCore cryptoRng publicKey rng =
      ok (.Err error, rng) →
    oracle.kemValid (sliceOf publicKey) = false ∧
    ∀ draw, oracle.kemEncaps (sliceOf publicKey) draw = none
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
  sigSign : ∀ secret message rng draw1 draw2 rest,
    trace rng = draw1 :: draw2 :: rest →
    ∃ signature rng',
      tacenta_boundary.xeddsa.sign rngCore cryptoRng secret message rng = ok (signature, rng') ∧
      trace rng' = rest ∧
      arrayOf signature = oracle.sigSign (arrayOf secret) (sliceOf message) draw1 draw2
  random32 : ∀ rng draw rest, trace rng = draw :: rest →
    ∃ value rng',
      lifecycle.random_secret rngCore cryptoRng rng = ok (value, rng') ∧
      arrayOf value = draw ∧ trace rng' = rest

theorem kem_invalid_key_refines_without_draw {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (dh : DhView) (kem : KemView) (trace : R → List Model.Lifecycle.Key)
    (oracle : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (publicKey : Slice Std.U8) (rng : R)
    (hinvalid : oracle.kemValid (sliceOf publicKey) = false) :
    ∃ error,
      tacenta_boundary.kem.encapsulate rngCore cryptoRng publicKey rng =
        ok (.Err error, rng) := by
  exact ⟨(), oracleOf.kemInvalidKey publicKey rng () hinvalid⟩

/-- An authentication failure at the translated AEAD boundary is the model
oracle's `none` verdict for those same keys, ciphertext and associated data.
Keeping this small consequence separate makes the receive-side commit proof
use the exact boundary result rather than treating `Error.Aead` as an
uninterpreted branch label. -/
theorem aead_open_error_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (dh : DhView) (kem : KemView) (trace : R → List Model.Lifecycle.Key)
    (oracle : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (key1 key2 : Array Std.U8 32#usize) (iv : Array Std.U8 16#usize)
    (ciphertext associatedData : Slice Std.U8) (error : Unit)
    (herror : tacenta_boundary.aead.decrypt key1 key2 iv ciphertext associatedData =
      ok (.Err error)) :
    oracle.aeadOpen (arrayOf key1) (arrayOf key2) (arrayOf iv)
      (sliceOf ciphertext) (sliceOf associatedData) = none := by
  obtain ⟨result, hcall, hresult⟩ :=
    oracleOf.aeadOpen key1 key2 iv ciphertext associatedData
  rw [herror] at hcall
  have heq : result = .Err error := by
    simpa using hcall.symm
  subst result
  simpa [resultOptionOf] using hresult.symm

/-- A successful translated AEAD open is the model oracle's `some` verdict,
including the exact returned plaintext bytes. This is the success-side
counterpart of `aead_open_error_refines` and is kept at the boundary so the
receive transaction can consume one precise oracle result. -/
theorem aead_open_success_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (dh : DhView) (kem : KemView) (trace : R → List Model.Lifecycle.Key)
    (oracle : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (key1 key2 : Array Std.U8 32#usize) (iv : Array Std.U8 16#usize)
    (ciphertext associatedData : Slice Std.U8) (plaintext : alloc.vec.Vec Std.U8)
    (hsuccess : tacenta_boundary.aead.decrypt key1 key2 iv ciphertext associatedData =
      ok (.Ok plaintext)) :
    oracle.aeadOpen (arrayOf key1) (arrayOf key2) (arrayOf iv)
      (sliceOf ciphertext) (sliceOf associatedData) = some (vecOf plaintext) := by
  obtain ⟨result, hcall, hresult⟩ :=
    oracleOf.aeadOpen key1 key2 iv ciphertext associatedData
  rw [hsuccess] at hcall
  have heq : result = .Ok plaintext := by
    simpa using hcall.symm
  subst result
  simpa [resultOptionOf] using hresult.symm

/-- Exact constructor/projection behaviour needed from the external `zeroize`
newtype at the two wrapper types used by successful Session encryption. -/
def ZeroizingRoundTrips (T : Type) : Prop :=
  ∀ inst : zeroize.Zeroize T,
    (∀ value, ∃ wrapped, zeroize.Zeroizing.new inst value = ok wrapped ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst wrapped = ok value)

theorem zeroizing_roundtrip (hz : ZeroizingRoundTrips T)
    (inst : zeroize.Zeroize T) (value : T) :
    ∃ wrapped, zeroize.Zeroizing.new inst value = ok wrapped ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst wrapped = ok value :=
  hz inst value


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
relation, so receive cannot reinterpret a codeword differently from send.

Superseded by `CodewordViewSendOf` below.  Kept unchanged so that its statement can still be
examined; no consumer takes it. -/
structure CodewordViewOf (view : Model.Lifecycle.CodewordView) : Prop where
  receive : ∀ state source chunk,
    Tacenta.SessionUnitBraidT3.CodewordOf source chunk →
    view.receive state (UInt16.ofNat chunk.index.val) (arrayOf chunk.data) =
      modelChunkOf source chunk
  send : ∀ state source chunk,
    Tacenta.SessionUnitBraidT3.CodewordOf source chunk →
    view.send state (modelChunkOf source chunk) = modelCodewordOf chunk

/-- The send direction of `CodewordViewOf`, which is all that the encrypt-side theorems use.

`CodewordViewOf` is kept unchanged and no consumer takes it. It is restated because its `receive`
clause asks the view to name one source for each wire chunk, which is a function of the chunk; two
messages that agree on their first 32 bytes have the same codeword at index 0, so, given that
`Encoder::new` returns on two such messages, no view meets that clause. That consequence is read
from the encoder's behaviour here and is not a theorem of this tree. The receive direction is
carried per run by `IncomingChunkRefines`, which asks for a source and not for the one a view names.
That a view meets this structure is shown in `UnitLifecycleRepair.lean`. -/
structure CodewordViewSendOf (view : Model.Lifecycle.CodewordView) : Prop where
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

theorem uint32_ofNat_toNat_of_u32 (real : Std.U32) (value : Nat)
    (h : real.val = value) : (UInt32.ofNat value).toNat = real.val := by
  rw [UInt32.toNat_ofNat', ← h, Nat.mod_eq_of_lt]
  have hbound := UScalar.hrBounds real
  simp [UScalar.rMax, U32.rMax] at hbound
  omega

theorem uint64_ofNat_toNat_of_u64 (real : Std.U64) (value : Nat)
    (h : real.val = value) : (UInt64.ofNat value).toNat = real.val := by
  rw [UInt64.toNat_ofNat', ← h, Nat.mod_eq_of_lt]
  have hbound := UScalar.hrBounds real
  simp [UScalar.rMax, U64.rMax] at hbound
  omega

theorem uint16_ofNat_toNat_of_u16 (real : Std.U16) (value : Nat)
    (h : real.val = value) : (UInt16.ofNat value).toNat = real.val := by
  rw [UInt16.toNat_ofNat', ← h, Nat.mod_eq_of_lt]
  have hbound := UScalar.hrBounds real
  simp [UScalar.rMax, U16.rMax] at hbound
  omega

theorem codeword_send_refines (view : Model.Lifecycle.CodewordView)
    (state : Model.Braid.BraidState) (real : tacenta_erasure.Chunk)
    (model : Model.Braid.Chunk)
    (hindex : real.index.val = model.index)
    (hcodeword : Tacenta.SessionUnitBraidT3.CodewordOf model.source real)
    (hview : CodewordViewSendOf view) :
    WireCodewordRefines { index := real.index, data := real.data }
      (view.send state model) := by
  have hmodel : modelChunkOf model.source real = model := by
    cases model
    simp [modelChunkOf, hindex]
  rw [← hmodel, hview.send state model.source real hcodeword]
  exact ⟨(uint16_ofNat_toNat_of_u16 real.index real.index.val rfl).symm, rfl⟩

/-- The translated header constructor agrees with the lifecycle model's wire
header.  The codeword bytes are fixed by the honest Braid chunk relation and
the shared `CodewordViewSendOf`, rather than chosen independently here. -/
theorem composite_of_refines (view : Model.Lifecycle.CodewordView)
    (braidBefore : Model.Braid.BraidState)
    (realHeader : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (realMessage : tacenta_braid.Msg) (modelMessage : Model.Braid.Msg)
    (hheader : Tacenta.SessionUnitTripleT3.TripleHeaderR realHeader modelHeader)
    (hmessage : Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage)
    (hview : CodewordViewSendOf view) :
    ∃ realComposite modelComposite,
      lifecycle.composite_of realHeader realMessage = ok realComposite ∧
      Model.Lifecycle.compositeOf view braidBefore modelHeader modelMessage =
        some modelComposite ∧
      CompositeRefines realComposite modelComposite := by
  rcases hheader with ⟨⟨hdh, hpn, hn⟩, hpqEpoch, hpqN⟩
  have hpn' := (uint32_ofNat_toNat_of_u32 realHeader.dr.pn modelHeader.dr.pn hpn).symm
  have hn' := (uint32_ofNat_toNat_of_u32 realHeader.dr.n modelHeader.dr.n hn).symm
  have hpqEpoch' :=
    (uint64_ofNat_toNat_of_u64 realHeader.epoch modelHeader.epoch hpqEpoch).symm
  have hpqN' :=
    (uint64_ofNat_toNat_of_u64 realHeader.pq_n modelHeader.pqN hpqN).symm
  rcases hmessage with ⟨hepoch, htype, hdata⟩
  obtain ⟨wireType, hrealType, hmodelType⟩ :=
    agreement_type_of_refines realMessage.ty modelMessage.type htype
  have hepoch' :=
    (uint64_ofNat_toNat_of_u64 realMessage.epoch modelMessage.epoch hepoch).symm
  let realComposite : tacenta_wire.Composite :=
    { dh := realHeader.dr.dh
      pn := realHeader.dr.pn
      n := realHeader.dr.n
      pq_epoch := realHeader.epoch
      pq_n := realHeader.pq_n
      ag_epoch := realMessage.epoch
      ag_type := wireType
      ag_chunk := realMessage.data.map
        (fun chunk => { index := chunk.index, data := chunk.data }) }
  let modelComposite : Model.CompositeHeader.Composite :=
    { dh := modelHeader.dr.dh
      pn := UInt32.ofNat modelHeader.dr.pn
      n := UInt32.ofNat modelHeader.dr.n
      pqEpoch := UInt64.ofNat modelHeader.epoch
      pqN := UInt64.ofNat modelHeader.pqN
      agEpoch := UInt64.ofNat modelMessage.epoch
      agType := agreementTypeOf wireType
      agChunk := modelMessage.data.map (view.send braidBefore) }
  refine ⟨realComposite, modelComposite, ?_, ?_, ?_⟩
  · unfold lifecycle.composite_of
    rw [hrealType]
    cases hr : realMessage.data <;> simp [realComposite, hr]
  · simp [Model.Lifecycle.compositeOf, hmodelType, modelComposite]
  · cases hr : realMessage.data with
    | none =>
        cases hm : modelMessage.data with
        | none =>
            refine ⟨hdh, hpn', hn', hpqEpoch', hpqN', hepoch', rfl, ?_⟩
            simp [realComposite, modelComposite, hr, hm]
        | some modelChunk => simp [hr, hm] at hdata
    | some realChunk =>
        cases hm : modelMessage.data with
        | none => simp [hr, hm] at hdata
        | some modelChunk =>
            simp [hr, hm] at hdata
            refine ⟨hdh, hpn', hn', hpqEpoch', hpqN', hepoch', rfl, ?_⟩
            simpa [realComposite, modelComposite, hr, hm] using
              (codeword_send_refines view braidBefore realChunk modelChunk
                hdata.1 hdata.2 hview)

/-- Splitting a received composite header for the Triple ratchet preserves all
five wire fields exactly. -/
theorem triple_header_of_refines (real : tacenta_wire.Composite)
    (model : Model.CompositeHeader.Composite)
    (hrel : CompositeRefines real model) :
    ∃ header,
      lifecycle.triple_header_of real = ok header ∧
      Tacenta.SessionUnitTripleT3.TripleHeaderR header
        (Model.Lifecycle.tripleHeaderOf model) := by
  let header : tacenta_triple.Header :=
    { dr := { dh := real.dh, pn := real.pn, n := real.n }
      epoch := real.pq_epoch
      pq_n := real.pq_n }
  refine ⟨header, rfl, ?_⟩
  exact ⟨⟨hrel.dh, hrel.pn, hrel.n⟩, hrel.pqEpoch, hrel.pqN⟩

/-- The extra input relation needed for a received Braid codeword.  Wire
decoding fixes its index and bytes; the Braid proof additionally needs the
chunk to come from one erasure-code source, because mixed-source chunks are a
documented model/implementation difference. -/
def IncomingChunkRefines (view : Model.Lifecycle.CodewordView)
    (state : Model.Braid.BraidState) (real : tacenta_wire.Composite)
    (model : Model.CompositeHeader.Composite) : Prop :=
  match real.ag_chunk, model.agChunk with
  | none, none => True
  | some realChunk, some modelChunk =>
      ∃ source,
        Tacenta.SessionUnitBraidT3.CodewordOf source
          { index := realChunk.index, data := realChunk.data } ∧
        view.receive state modelChunk.index modelChunk.data =
          modelChunkOf source { index := realChunk.index, data := realChunk.data }
  | _, _ => False

/-- The shipping adapter from a decoded composite header to a Braid message
agrees exactly with the lifecycle model, including the explicitly related
incoming erasure-code chunk. -/
theorem msg_of_refines (view : Model.Lifecycle.CodewordView)
    (state : Model.Braid.BraidState) (real : tacenta_wire.Composite)
    (model : Model.CompositeHeader.Composite)
    (hrel : CompositeRefines real model)
    (hchunk : IncomingChunkRefines view state real model) :
    ∃ message, lifecycle.msg_of real = ok message ∧
      Tacenta.SessionUnitBraidT3.MsgRefines message
        (Model.Lifecycle.braidMessageOf view state model) := by
  obtain ⟨realType, hrealType, htype⟩ := msg_type_of_refines real.ag_type
  have htype' : Tacenta.SessionUnitBraidT3.MsgTypeRefines realType
      (Model.Lifecycle.braidMessageOf view state model).type := by
    change Tacenta.SessionUnitBraidT3.MsgTypeRefines realType
      (Model.Lifecycle.braidTypeOf model.agType)
    rw [← hrel.agType]
    exact htype
  cases hr : real.ag_chunk with
  | none =>
      cases hm : model.agChunk with
      | none =>
          refine ⟨{ epoch := real.ag_epoch, ty := realType, data := none }, ?_, ?_⟩
          · simp [lifecycle.msg_of, hrealType, hr]
          · exact ⟨hrel.agEpoch, htype', by simp [Model.Lifecycle.braidMessageOf, hm]⟩
      | some modelChunk => simp [IncomingChunkRefines, hr, hm] at hchunk
  | some realChunk =>
      cases hm : model.agChunk with
      | none => simp [IncomingChunkRefines, hr, hm] at hchunk
      | some modelChunk =>
          simp [IncomingChunkRefines, hr, hm] at hchunk
          obtain ⟨source, hcodeword, hview⟩ := hchunk
          have hwire := hrel.agChunk
          simp [hr, hm] at hwire
          let data : tacenta_erasure.Chunk :=
            { index := realChunk.index, data := realChunk.data }
          let message : tacenta_braid.Msg :=
            { epoch := real.ag_epoch, ty := realType, data := some data }
          refine ⟨message, ?_, ?_⟩
          · simp [lifecycle.msg_of, hrealType, hr, message, data]
          · refine ⟨hrel.agEpoch, htype', ?_⟩
            simpa [Model.Lifecycle.braidMessageOf, hm, hview, modelChunkOf,
              message, data, hwire.1] using hcodeword

theorem wire_bytesOf_eq_arrayOf {n : Usize} (bytes : Array Std.U8 n) :
    Tacenta.SessionUnitWireT3.bytesOf bytes.val = arrayOf bytes := by
  rfl

theorem wire_agTypeOf_eq (ty : tacenta_wire.AgreementType) :
    Tacenta.SessionUnitWireT3.agTypeOf ty = agreementTypeOf ty := by
  cases ty <;> rfl

theorem wire_bytesOf_eq_sliceOf (bytes : Slice Std.U8) :
    Tacenta.SessionUnitWireT3.bytesOf bytes.val = sliceOf bytes := by
  rfl

theorem wire_bytesOf_eq_vecOf (bytes : alloc.vec.Vec Std.U8) :
    Tacenta.SessionUnitWireT3.bytesOf bytes.val = vecOf bytes := by
  rfl

theorem composite_refines_wire_compositeOf (real : tacenta_wire.Composite) :
    CompositeRefines real (Tacenta.SessionUnitWireT3.compositeOf real) := by
  refine ⟨wire_bytesOf_eq_arrayOf real.dh,
    (uint32_ofNat_toNat_of_u32 real.pn real.pn.val rfl).symm,
    (uint32_ofNat_toNat_of_u32 real.n real.n.val rfl).symm,
    (uint64_ofNat_toNat_of_u64 real.pq_epoch real.pq_epoch.val rfl).symm,
    (uint64_ofNat_toNat_of_u64 real.pq_n real.pq_n.val rfl).symm,
    (uint64_ofNat_toNat_of_u64 real.ag_epoch real.ag_epoch.val rfl).symm,
    (wire_agTypeOf_eq real.ag_type).symm, ?_⟩
  cases hchunk : real.ag_chunk with
  | none =>
      simp [Tacenta.SessionUnitWireT3.compositeOf, hchunk]
  | some chunk =>
      simp [Tacenta.SessionUnitWireT3.compositeOf, hchunk]
      exact ⟨(uint16_ofNat_toNat_of_u16 chunk.index chunk.index.val rfl).symm,
        wire_bytesOf_eq_arrayOf chunk.data⟩

theorem wire_codewordOf_eq (real : tacenta_wire.Codeword)
    (model : Model.CompositeHeader.Codeword)
    (hrel : WireCodewordRefines real model) :
    { index := UInt16.ofNat real.index.val
      data := Tacenta.SessionUnitWireT3.bytesOf real.data.val } = model := by
  cases model with
  | mk index data =>
      simp only [Model.CompositeHeader.Codeword.mk.injEq]
      constructor
      · apply UInt16.ext
        exact (uint16_ofNat_toNat_of_u16 real.index real.index.val rfl).trans
          hrel.1
      · rw [wire_bytesOf_eq_arrayOf]
        exact hrel.2

/-- The lifecycle relation is the same concrete wire relation used by the
deterministically ported decoder proof. -/
theorem wire_compositeOf_eq (real : tacenta_wire.Composite)
    (model : Model.CompositeHeader.Composite)
    (hrel : CompositeRefines real model) :
    Tacenta.SessionUnitWireT3.compositeOf real = model := by
  have hdh : Tacenta.SessionUnitWireT3.bytesOf real.dh.val = model.dh := by
    rw [wire_bytesOf_eq_arrayOf]
    exact hrel.dh
  have hpn : UInt32.ofNat real.pn.val = model.pn := by
    apply UInt32.ext
    exact (uint32_ofNat_toNat_of_u32 real.pn real.pn.val rfl).trans hrel.pn
  have hn : UInt32.ofNat real.n.val = model.n := by
    apply UInt32.ext
    exact (uint32_ofNat_toNat_of_u32 real.n real.n.val rfl).trans hrel.n
  have hpqEpoch : UInt64.ofNat real.pq_epoch.val = model.pqEpoch := by
    apply UInt64.ext
    exact (uint64_ofNat_toNat_of_u64 real.pq_epoch real.pq_epoch.val rfl).trans
      hrel.pqEpoch
  have hpqN : UInt64.ofNat real.pq_n.val = model.pqN := by
    apply UInt64.ext
    exact (uint64_ofNat_toNat_of_u64 real.pq_n real.pq_n.val rfl).trans hrel.pqN
  have hagEpoch : UInt64.ofNat real.ag_epoch.val = model.agEpoch := by
    apply UInt64.ext
    exact (uint64_ofNat_toNat_of_u64 real.ag_epoch real.ag_epoch.val rfl).trans
      hrel.agEpoch
  have hagType : Tacenta.SessionUnitWireT3.agTypeOf real.ag_type = model.agType := by
    exact (wire_agTypeOf_eq real.ag_type).trans hrel.agType
  have hagChunk : real.ag_chunk.map (fun chunk =>
      { index := UInt16.ofNat chunk.index.val
        data := Tacenta.SessionUnitWireT3.bytesOf chunk.data.val }) =
      model.agChunk := by
    cases hr : real.ag_chunk with
    | none =>
        cases hm : model.agChunk with
        | none => rfl
        | some modelChunk =>
            have hchunkRel := hrel.agChunk
            simp [hr, hm] at hchunkRel
    | some realChunk =>
        cases hm : model.agChunk with
        | none =>
            have hchunkRel := hrel.agChunk
            simp [hr, hm] at hchunkRel
        | some modelChunk =>
            have hchunkRel := hrel.agChunk
            simp [hr, hm] at hchunkRel
            apply congrArg some
            exact wire_codewordOf_eq realChunk modelChunk hchunkRel
  cases real
  cases model
  simp only [Tacenta.SessionUnitWireT3.compositeOf,
    Model.CompositeHeader.Composite.mk.injEq]
  exact ⟨hdh, hpn, hn, hpqEpoch, hpqN, hagEpoch, hagType, hagChunk⟩

/-- The ported wire T3 theorem, expressed in the lifecycle relations used by
the outer decrypt proof. -/
theorem decode_message_refines_lifecycle (bytes : Slice Std.U8) :
    tacenta_wire.decode_message bytes ⦃ fun result =>
      match result with
      | .Ok message => ∃ modelHeader,
          Model.CompositeHeader.decode (sliceOf bytes) =
            some (modelHeader, vecOf message.ciphertext) ∧
          CompositeRefines message.header modelHeader
      | .Err _ => Model.CompositeHeader.decode (sliceOf bytes) = none ⦄ := by
  refine WP.spec_mono
    (Tacenta.SessionUnitWireT3.decode_message_refines bytes) ?_
  intro result hresult
  cases result with
  | Err reason =>
      simpa [wire_bytesOf_eq_sliceOf] using hresult
  | Ok message =>
      refine ⟨Tacenta.SessionUnitWireT3.compositeOf message.header, ?_,
        composite_refines_wire_compositeOf message.header⟩
      rw [← wire_bytesOf_eq_sliceOf bytes,
        ← wire_bytesOf_eq_vecOf message.ciphertext]
      exact hresult

/-- The deterministically ported initial-message decoder computes the lifecycle
model's detailed success value exactly.  On refusal the model's classifier also
returns a reason, whose exact correspondence is proved separately from this
success bridge. -/
theorem decode_initial_refines_lifecycle (bytes : Slice Std.U8) :
    tacenta_wire.decode_initial bytes ⦃ fun result =>
      match result with
      | .Ok initial =>
          Model.Messages.decodeInitialDetailed (sliceOf bytes) =
            .ok (Tacenta.SessionUnitWireInitialT3.initialOf initial)
      | .Err _ => ∃ reason,
          Model.Messages.decodeInitialDetailed (sliceOf bytes) = .error reason ⦄ := by
  refine WP.spec_mono
    (Tacenta.SessionUnitWireInitialT3.decode_initial_refines bytes) ?_
  intro result hresult
  cases result with
  | Ok initial =>
      apply (Model.Messages.decodeInitialDetailed_ok_iff _ _).2
      simpa [wire_bytesOf_eq_sliceOf] using hresult
  | Err reason =>
      refine ⟨Model.Messages.initialDecodeRefusal (sliceOf bytes), ?_⟩
      simp only [Model.Messages.decodeInitialDetailed]
      have hnone : Model.Messages.decodeInitial (sliceOf bytes) = none := by
        simpa [wire_bytesOf_eq_sliceOf] using hresult
      rw [hnone]

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
  | .InvalidIdentityKey => .invalidIdentityKey
  | .BadSignedPrekeySignature => .badSignedPrekeySignature
  | .BadKemPrekeySignature => .badKemPrekeySignature
  | .NonContributoryAgreement => .nonContributoryAgreement

def decodeRefusalOf : tacenta_wire.DecodeError → Model.Messages.DecodeRefusal
  | .UnknownVersion => .unknownVersion
  | .WrongType => .wrongType
  | .TooShort => .tooShort
  | .LengthOverrun => .lengthOverrun

theorem wireByte_ne_zero (x : Std.U8) :
    Tacenta.SessionUnitWireT3.byteOf x ≠ 0 ↔ x ≠ 0#u8 := by
  rw [show (0 : UInt8) = Tacenta.SessionUnitWireT3.byteOf 0#u8 from rfl]
  exact not_congr (Tacenta.SessionUnitWireT3.byteOf_inj x 0#u8)

theorem wireByte_ne_one (x : Std.U8) :
    Tacenta.SessionUnitWireT3.byteOf x ≠ 1 ↔ x ≠ 1#u8 := by
  rw [show (1 : UInt8) = Tacenta.SessionUnitWireT3.byteOf 1#u8 from rfl]
  exact not_congr (Tacenta.SessionUnitWireT3.byteOf_inj x 1#u8)

set_option maxHeartbeats 1000000 in
theorem decode_composite_refusal_classifies (bytes : Slice Std.U8) :
    tacenta_wire.decode_composite bytes ⦃ fun result =>
      match result with
      | .Ok _ => True
      | .Err reason => decodeRefusalOf reason =
          Model.CompositeHeader.decodeRefusal
            (Tacenta.SessionUnitWireT3.bytesOf bytes.val) ⦄ := by
  unfold tacenta_wire.decode_composite
  simp only [tacenta_wire.CHUNK_BYTES]
  step*
  all_goals first
    | trivial
    | (simp_all [Slice.length, Array.repeat]; done)
    | skip
  all_goals first | scalar_tac | skip
  all_goals simp only [decodeRefusalOf]
  all_goals first
    | (unfold Model.CompositeHeader.decodeRefusal
       rw [if_pos (by simp only [Tacenta.SessionUnitWireT3.bytesOf_length,
         Model.CompositeHeader.size, Model.CompositeHeader.chunkBytes]; scalar_tac)])
    | skip
  all_goals (
    have hlong : 102 ≤ bytes.val.length := by scalar_tac
    unfold Model.CompositeHeader.decodeRefusal
    rw [if_neg (by simp only [Tacenta.SessionUnitWireT3.bytesOf_length,
      Model.CompositeHeader.size, Model.CompositeHeader.chunkBytes]; omega)]
    simp (disch := omega) only [Tacenta.SessionUnitWireT3.bytesOf_getElem!,
      ← Tacenta.SessionUnitWireT3.byteOf_version,
      ← Tacenta.SessionUnitWireT3.byteOf_type_ratchet,
      Tacenta.SessionUnitWireT3.bne_byteOf]
    subst_vars)
  -- version and message-type refusals
  all_goals first
    | (rw [if_pos (by assumption)])
    | (rw [if_neg (by assumption), if_pos (by assumption)])
    | skip
  -- the copied key and the model inspect the same thirty-two bytes
  all_goals (
    have hdhk : (Array.from_slice (Array.repeat 32#usize 0#u8) s2).val =
        (bytes.val.drop 2).take 32 := by
      rw [Array.from_slice_val _ _ (by simp [s1_post1, List.slice]; omega), s1_post1]
      rfl
    rw [Tacenta.SessionUnitWireT3.canonicalKey_at _ 2 _ hdhk])
  all_goals first
    | (rw [if_neg (by assumption), if_neg (by assumption),
        if_pos (Tacenta.SessionUnitWireT3.not_eq_true_of_eq_false'
          (by assumption : ¬ Tacenta.SessionUnitWireT1.canonicalX25519
            (Array.from_slice (Array.repeat 32#usize 0#u8) s2) = true))])
    | (have hkt : Tacenta.SessionUnitWireT1.canonicalX25519
          (Array.from_slice (Array.repeat 32#usize 0#u8) s2) = true := by
         rw [← b_post]
       rw [if_neg (by assumption), if_neg (by assumption), hkt, Bool.not_true,
         if_neg Bool.false_ne_true, ← o_post])
  all_goals (simp only [Option.map, Option.isNone,
    Tacenta.SessionUnitWireT3.byteOf_beq_zero])
  all_goals first | rfl | skip
  all_goals (simp only [bne_iff_ne, ne_eq, not_not] at *)
  all_goals simp only [Bool.false_eq_true, if_false]
  -- absent codewords must have a zero index and zero payload
  on_goal 1 =>
    rw [if_pos (by
      simp only [Bool.and_eq_true, bne_iff_ne]
      constructor
      · exact (wireByte_ne_zero _).mpr (by assumption)
      · exact (wireByte_ne_one _).mpr (by assumption))]
  on_goal 1 =>
    rw [if_neg (by
      simp only [Bool.and_eq_true, bne_iff_ne]
      intro hboth
      exact (wireByte_ne_zero _).mp hboth.1 (by assumption))]
    rw [if_pos (by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · assumption
      · simp only [Bool.or_eq_true, bne_iff_ne]
        left
        rw [wireByte_ne_zero, wireByte_ne_zero]
        by_contra hz
        push Not at hz
        scalar_tac)]
  on_goal 1 =>
    rw [if_neg (by
      simp only [Bool.and_eq_true, bne_iff_ne]
      intro hboth
      exact (wireByte_ne_zero _).mp hboth.1 (by assumption))]
    rw [if_pos (by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · assumption
      · simp only [Bool.or_eq_true, bne_iff_ne]
        right
        simp only [List.any_eq_true]
        have hi15 : i15 ≠ 0#u8 := by assumption
        have hnall : ¬ ∀ j < 32, bytes.val[70 + j]! = 0#u8 := by
          intro hall
          exact hi15 (i15_post.mpr hall)
        push Not at hnall
        obtain ⟨j, hj, hjne⟩ := hnall
        refine ⟨Tacenta.SessionUnitWireT3.byteOf bytes.val[70 + j]!, ?_, ?_⟩
        · rw [Tacenta.SessionUnitWireT3.bytesOf_drop_take]
          simp only [Tacenta.SessionUnitWireT3.bytesOf, List.mem_map]
          refine ⟨bytes.val[70 + j]!, ?_, rfl⟩
          rw [List.mem_iff_getElem]
          refine ⟨j, by simp [Model.CompositeHeader.chunkBytes]; omega, ?_⟩
          simp [List.getElem!_eq_getElem?_getD,
            List.getElem?_eq_getElem (by omega : 70 + j < bytes.val.length)]
        · simpa only [bne_iff_ne] using (wireByte_ne_zero _).mpr hjne)]

/-- The message wrapper preserves the composite decoder's exact public refusal.
Copying the accepted ciphertext is infallible and therefore introduces no new
refusal class. -/
theorem decode_message_refusal_classifies (bytes : Slice Std.U8) :
    tacenta_wire.decode_message bytes ⦃ fun result =>
      match result with
      | .Ok _ => True
      | .Err reason => decodeRefusalOf reason =
          Model.CompositeHeader.decodeRefusal
            (Tacenta.SessionUnitWireT3.bytesOf bytes.val) ⦄ := by
  unfold tacenta_wire.decode_message
  apply WP.spec_bind (decode_composite_refusal_classifies bytes)
  intro result hresult
  cases result with
  | Err reason => simpa using hresult
  | Ok pair =>
      obtain ⟨header, rest⟩ := pair
      simp only
      step with alloc.slice.Slice.to_vec_spec

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
    Option Model.Ratchet.SendRefusal :=
  Tacenta.SessionUnitT3.sendRefusalOfReal

def sparseSendRefusalOfReal : tacenta_spqr.SpqrError →
    Option Model.SparseRatchet.SendRefusal :=
  Tacenta.SessionUnitSpqrT3.sendRefusalOfReal

def tripleSendRefusalOfReal : tacenta_triple.TripleError →
    Option Model.Triple.SendRefusal :=
  Tacenta.SessionUnitTripleT3.sendRefusalOfReal

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

/-! ## Establishment-level refinement

`StepRefines` deliberately includes a live Session because every public
Session operation already has one.  Establishment is the other public root:
the model returns an `EstablishStep`, while the translated function returns a
Session only on success and always returns the post-call RNG.  Keep that
boundary explicit instead of smuggling establishment through a Session
operation theorem. -/

def EstablishResultRefines
    (dh : DhView) (K : Model.Braid.Kem)
    (real : core.result.Result lifecycle.Session lifecycle.Error)
    (model : Except Model.Lifecycle.Refusal Model.Lifecycle.Session) : Prop :=
  match real, model with
  | .Ok realSession, .ok modelSession => SessionRefines dh K realSession modelSession
  | .Err reason, .error modelReason => refusalOf reason = modelReason
  | _, _ => False

structure EstablishStepRefines {R : Type} (trace : R → List Model.Lifecycle.Key)
    (dh : DhView) (K : Model.Braid.Kem)
    (real : core.result.Result lifecycle.Session lifecycle.Error × R)
    (model : Model.Lifecycle.EstablishStep) : Prop where
  result : EstablishResultRefines dh K real.1 model.result
  draws : trace real.2 = model.oracle.draws

/-! Responder establishment has one additional durable component: the
prekey store.  Keep its representation relation abstract at this boundary;
the decode-refusal theorem below needs only that the input stores correspond,
while the authenticated success theorem will have to define and preserve the
field-level relation. -/

def ResponderResultRefines
    (dh : DhView) (K : Model.Braid.Kem)
    (real : core.result.Result
      (lifecycle.Session × alloc.vec.Vec Std.U8) lifecycle.Error)
    (model : Except Model.Lifecycle.Refusal
      (Model.Lifecycle.Session × Bytes)) : Prop :=
  match real, model with
  | .Ok (realSession, realBytes), .ok (modelSession, modelBytes) =>
      SessionRefines dh K realSession modelSession ∧ vecOf realBytes = modelBytes
  | .Err reason, .error modelReason => refusalOf reason = modelReason
  | _, _ => False

structure ResponderEstablishStepRefines {R : Type}
    (storeRel : lifecycle.PrekeyStore → Model.Lifecycle.PrekeyStore → Prop)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (real : core.result.Result
        (lifecycle.Session × alloc.vec.Vec Std.U8) lifecycle.Error ×
      lifecycle.PrekeyStore × R)
    (model : Model.Lifecycle.ResponderStep) : Prop where
  result : ResponderResultRefines dh K real.1 model.result
  store : storeRel real.2.1 model.store
  draws : trace real.2.2 = model.oracle.draws

/-! The responder's malformed-initial-message branch is now composed at the
public root.  The generated decoder classification supplies the model's
exact refusal, `establish_responder` returns the original prekey store, and
the model's `establishResponder` does the same through `prepareResponder`.
No authenticated session or durable-consumption claim is hidden in this
theorem. -/
theorem establish_responder_decode_refusal_step_refines {R : Type}
    (storeRel : lifecycle.PrekeyStore → Model.Lifecycle.PrekeyStore → Prop)
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (ourIdentity : lifecycle.Identity) (modelIdentity : Model.Lifecycle.Identity)
    (ourPrekeys : lifecycle.PrekeyStore) (modelStore : Model.Lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng : R)
    (realReason : tacenta_wire.DecodeError)
    (hstore : storeRel ourPrekeys modelStore)
    (htrace : trace rng = oracle.draws)
    (hdecodeReal : tacenta_wire.decode_initial initialMessage =
      ok (.Err realReason)) :
    ∃ output,
      lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
        initialMessage rng = ok output ∧
      ResponderEstablishStepRefines storeRel trace dh K output
        (Model.Lifecycle.establishResponder view oracle modelIdentity modelStore
          (sliceOf initialMessage)) := by
  obtain ⟨classified, hclassified, hreason⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitWireInitialT3.decode_initial_refusal_classifies initialMessage)
  have hclassifiedEq : classified = .Err realReason := by
    rw [hdecodeReal] at hclassified
    have heq : (.Err realReason : core.result.Result tacenta_wire.DecodedInitial
        tacenta_wire.DecodeError) = classified := by simpa using hclassified
    exact heq.symm
  subst classified
  have hreason' : decodeRefusalOf realReason =
      Model.Messages.initialDecodeRefusal (sliceOf initialMessage) := by
    cases realReason <;>
      simpa [decodeRefusalOf,
        Tacenta.SessionUnitWireInitialT3.decodeRefusalOf,
        wire_bytesOf_eq_sliceOf] using hreason
  obtain ⟨decoded, hdecoded, hnone⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitWireInitialT3.decode_initial_refines initialMessage)
  have hdecodedEq : decoded = .Err realReason := by
    rw [hdecodeReal] at hdecoded
    have heq : (.Err realReason : core.result.Result tacenta_wire.DecodedInitial
        tacenta_wire.DecodeError) = decoded := by simpa using hdecoded
    exact heq.symm
  subst decoded
  have hdecodeModel : Model.Messages.decodeInitialDetailed (sliceOf initialMessage) =
      .error (decodeRefusalOf realReason) := by
    simp only [Model.Messages.decodeInitialDetailed]
    have hnone' : Model.Messages.decodeInitial (sliceOf initialMessage) = none := by
      simpa [wire_bytesOf_eq_sliceOf] using hnone
    rw [hnone', hreason']
  have hreal :
      lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
        initialMessage rng =
        ok (.Err (.Decode realReason), ourPrekeys, rng) := by
    unfold lifecycle.establish_responder
    simp [hdecodeReal]
  have hmodel :
      Model.Lifecycle.establishResponder view oracle modelIdentity modelStore
        (sliceOf initialMessage) =
        { store := modelStore,
          result := .error (.decode (decodeRefusalOf realReason)),
          oracle := oracle } := by
    simp [Model.Lifecycle.establishResponder, Model.Lifecycle.prepareResponder,
      hdecodeModel]
  refine ⟨(.Err (.Decode realReason), ourPrekeys, rng), hreal, ?_⟩
  rw [hmodel]
  constructor
  · simp [ResponderResultRefines, refusalOf]
  · exact hstore
  · exact htrace

/-! An unknown signed-prekey ID is a pre-KEM refusal.  The concrete root
    returns the original store and RNG, and no later lookup or primitive is
    part of the branch equation. -/
theorem establish_responder_unknown_signed_prekey_of_calls {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (ourPrekeys : lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng : R)
    (decoded : tacenta_wire.DecodedInitial)
    (unknown : lifecycle.Error)
    (hunknown : unknown = lifecycle.Error.UnknownPrekeyId)
    (hdecode : tacenta_wire.decode_initial initialMessage =
      ok (.Ok decoded))
    (hsigned : lifecycle.responder_signed_prekey_secret ourPrekeys
      decoded.signed_prekey_id = ok (.Err unknown)) :
    lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng =
      ok (.Err (.UnknownPrekeyId), ourPrekeys, rng) := by
  unfold lifecycle.establish_responder
  simp [hdecode, hsigned,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from, hunknown]

/-! Join the unknown-signed-prekey refusal to the model's corresponding
    pre-lookup refusal, preserving the store relation and trace. -/
theorem establish_responder_unknown_signed_prekey_step_refines {R : Type}
    (storeRel : lifecycle.PrekeyStore → Model.Lifecycle.PrekeyStore → Prop)
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (oracle : Model.Lifecycle.Oracle) (view : Model.Lifecycle.CodewordView)
    (ourIdentity : lifecycle.Identity) (modelIdentity : Model.Lifecycle.Identity)
    (ourPrekeys : lifecycle.PrekeyStore) (modelStore : Model.Lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng : R)
    (initial : Model.Messages.Initial)
    (hstore : storeRel ourPrekeys modelStore)
    (htrace : trace rng = oracle.draws)
    (hreal : lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng = ok (.Err (.UnknownPrekeyId), ourPrekeys, rng))
    (hdecodeModel : Model.Messages.decodeInitialDetailed (sliceOf initialMessage) =
      .ok initial)
    (hs : Model.Lifecycle.responderSignedPrekeySecret modelStore
      initial.signedPrekeyId.toNat = none) :
    ∃ output,
      lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
        initialMessage rng = ok output ∧
      ResponderEstablishStepRefines storeRel trace dh K output
        (Model.Lifecycle.establishResponder view oracle modelIdentity modelStore
          (sliceOf initialMessage)) := by
  have hprep := Model.Lifecycle.prepareResponder_unknown_signed_prekey oracle
    modelIdentity modelStore (sliceOf initialMessage) initial hdecodeModel hs
  have hmodel : Model.Lifecycle.establishResponder view oracle modelIdentity modelStore
      (sliceOf initialMessage) =
      { store := modelStore, result := .error .unknownPrekeyId, oracle := oracle } := by
    simp [Model.Lifecycle.establishResponder, hprep]
  refine ⟨(.Err (.UnknownPrekeyId), ourPrekeys, rng), hreal, ?_⟩
  rw [hmodel]
  constructor
  · simp [ResponderResultRefines, refusalOf]
  · exact hstore
  · exact htrace

/-! A refusal from the responder's KEM-slot lookup is also public-root and
    store-atomic.  Its mapped model reason is supplied explicitly because the
    Rust error vocabulary is implementation-defined. -/
theorem establish_responder_kem_slot_refusal_of_calls {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (ourPrekeys : lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng : R)
    (decoded : tacenta_wire.DecodedInitial)
    (signedSecret : zeroize.Zeroizing (Array Std.U8 32#usize))
    (kemError : lifecycle.Error)
    (hdecode : tacenta_wire.decode_initial initialMessage =
      ok (.Ok decoded))
    (hsigned : lifecycle.responder_signed_prekey_secret ourPrekeys
      decoded.signed_prekey_id = ok (.Ok signedSecret))
    (hkem : lifecycle.responder_kem_slot ourPrekeys decoded.kem_prekey_id =
      ok (.Err kemError)) :
    lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng =
      ok (.Err kemError, ourPrekeys, rng) := by
  unfold lifecycle.establish_responder
  simp [hdecode, hsigned, hkem,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

theorem establish_responder_kem_slot_refusal_step_refines {R : Type}
    (storeRel : lifecycle.PrekeyStore → Model.Lifecycle.PrekeyStore → Prop)
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (oracle : Model.Lifecycle.Oracle) (view : Model.Lifecycle.CodewordView)
    (ourIdentity : lifecycle.Identity) (modelIdentity : Model.Lifecycle.Identity)
    (ourPrekeys : lifecycle.PrekeyStore) (modelStore : Model.Lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng : R)
    (initial : Model.Messages.Initial) (signedSecret : Model.Lifecycle.Key)
    (reason : Model.Lifecycle.Refusal) (kemError : lifecycle.Error)
    (hstore : storeRel ourPrekeys modelStore)
    (htrace : trace rng = oracle.draws)
    (hreal : lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng = ok (.Err kemError, ourPrekeys, rng))
    (hmap : refusalOf kemError = reason)
    (hdecodeModel : Model.Messages.decodeInitialDetailed (sliceOf initialMessage) =
      .ok initial)
    (hs : Model.Lifecycle.responderSignedPrekeySecret modelStore
      initial.signedPrekeyId.toNat = some signedSecret)
    (hk : Model.Lifecycle.responderKemPair modelStore
      initial.kemPrekeyId.toNat = .error reason) :
    ∃ output,
      lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
        initialMessage rng = ok output ∧
      ResponderEstablishStepRefines storeRel trace dh K output
        (Model.Lifecycle.establishResponder view oracle modelIdentity modelStore
          (sliceOf initialMessage)) := by
  have hprep := Model.Lifecycle.prepareResponder_kem_slot_refusal oracle
    modelIdentity modelStore (sliceOf initialMessage) initial signedSecret reason
    hdecodeModel hs hk
  have hmodel : Model.Lifecycle.establishResponder view oracle modelIdentity modelStore
      (sliceOf initialMessage) =
      { store := modelStore, result := .error reason, oracle := oracle } := by
    simp [Model.Lifecycle.establishResponder, hprep]
  refine ⟨(.Err kemError, ourPrekeys, rng), hreal, ?_⟩
  rw [hmodel]
  constructor
  · simp [ResponderResultRefines, hmap]
  · exact hstore
  · exact htrace

/-! A missing curve one-time-prekey is a public-root refusal after identity
    validation and before any decapsulation or durable mutation. -/
theorem establish_responder_one_time_slot_refusal_of_calls {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (ourPrekeys : lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng : R)
    (decoded : tacenta_wire.DecodedInitial)
    (signedSecret : zeroize.Zeroizing (Array Std.U8 32#usize))
    (kemSlot : lifecycle.KemKeySlot) (lastResort : Bool)
    (initiatorIdentity initiatorEphemeral : tacenta_boundary.dh.PublicKeyBytes)
    (unknown : lifecycle.Error)
    (hdecode : tacenta_wire.decode_initial initialMessage =
      ok (.Ok decoded))
    (hsigned : lifecycle.responder_signed_prekey_secret ourPrekeys
      decoded.signed_prekey_id = ok (.Ok signedSecret))
    (hkem : lifecycle.responder_kem_slot ourPrekeys decoded.kem_prekey_id =
      ok (.Ok (kemSlot, lastResort)))
    (hcurve : lifecycle.responder_curve_inputs
      (alloc.vec.Vec.deref decoded.identity)
      (alloc.vec.Vec.deref decoded.ephemeral) =
      ok (.Ok (initiatorIdentity, initiatorEphemeral)))
    (hone : lifecycle.responder_one_time_key ourPrekeys
      decoded.one_time_prekey_id = ok (.Err unknown)) :
    lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng =
      ok (.Err unknown, ourPrekeys, rng) := by
  unfold lifecycle.establish_responder
  cases lastResort <;>
    simp [hdecode, hsigned, hkem, hcurve, hone,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

theorem establish_responder_one_time_slot_refusal_step_refines {R : Type}
    (storeRel : lifecycle.PrekeyStore → Model.Lifecycle.PrekeyStore → Prop)
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (oracle : Model.Lifecycle.Oracle) (view : Model.Lifecycle.CodewordView)
    (ourIdentity : lifecycle.Identity) (modelIdentity : Model.Lifecycle.Identity)
    (ourPrekeys : lifecycle.PrekeyStore) (modelStore : Model.Lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng : R)
    (initial : Model.Messages.Initial) (signedSecret : Model.Lifecycle.Key)
    (kemPair : Bytes) (lastResort : Bool) (reason : Model.Lifecycle.Refusal)
    (unknown : lifecycle.Error)
    (hstore : storeRel ourPrekeys modelStore)
    (htrace : trace rng = oracle.draws)
    (hreal : lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng = ok (.Err unknown, ourPrekeys, rng))
    (hmap : refusalOf unknown = reason)
    (hdecodeModel : Model.Messages.decodeInitialDetailed (sliceOf initialMessage) =
      .ok initial)
    (hs : Model.Lifecycle.responderSignedPrekeySecret modelStore
      initial.signedPrekeyId.toNat = some signedSecret)
    (hk : Model.Lifecycle.responderKemPair modelStore
      initial.kemPrekeyId.toNat = .ok (kemPair, lastResort))
    (hv : oracle.identityValid (initial.identity.drop 1) = true)
    (ho : Model.Lifecycle.responderOneTimeSecret modelStore
      initial.oneTimeId.toNat = .error reason) :
    ∃ output,
      lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
        initialMessage rng = ok output ∧
      ResponderEstablishStepRefines storeRel trace dh K output
        (Model.Lifecycle.establishResponder view oracle modelIdentity modelStore
          (sliceOf initialMessage)) := by
  have hprep := Model.Lifecycle.prepareResponder_one_time_slot_refusal oracle
    modelIdentity modelStore (sliceOf initialMessage) initial signedSecret kemPair
    lastResort reason hdecodeModel hs hk hv ho
  have hmodel : Model.Lifecycle.establishResponder view oracle modelIdentity modelStore
      (sliceOf initialMessage) =
      { store := modelStore, result := .error reason, oracle := oracle } := by
    simp [Model.Lifecycle.establishResponder, hprep]
  refine ⟨(.Err unknown, ourPrekeys, rng), hreal, ?_⟩
  rw [hmodel]
  constructor
  · simp [ResponderResultRefines, hmap]
  · exact hstore
  · exact htrace

/-! The responder's identity refusal is reached after the decoder and the two
    key-slot lookups, but before one-time lookup, decapsulation, DH, replay
    recording, or session construction.  Keep those call results explicit so
    the proof also records the transaction boundary being protected. -/
theorem establish_responder_invalid_identity_of_calls {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (ourPrekeys : lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng : R)
    (decoded : tacenta_wire.DecodedInitial)
    (signedSecret : zeroize.Zeroizing (Array Std.U8 32#usize))
    (kemSlot : lifecycle.KemKeySlot) (lastResort : Bool)
    (hdecode : tacenta_wire.decode_initial initialMessage =
      ok (.Ok decoded))
    (hsigned : lifecycle.responder_signed_prekey_secret ourPrekeys
      decoded.signed_prekey_id = ok (.Ok signedSecret))
    (hkem : lifecycle.responder_kem_slot ourPrekeys decoded.kem_prekey_id =
      ok (.Ok (kemSlot, lastResort)))
    (hcurve : lifecycle.responder_curve_inputs
      (alloc.vec.Vec.deref decoded.identity)
      (alloc.vec.Vec.deref decoded.ephemeral) =
      ok (.Err (.Handshake .InvalidIdentityKey))) :
    lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng =
      ok (.Err (.Handshake .InvalidIdentityKey), ourPrekeys, rng) := by
  unfold lifecycle.establish_responder
  cases lastResort <;>
    simp [hdecode, hsigned, hkem, hcurve,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-! The concrete responder KEM refusal follows the same protected ordering as
    the model: no DH agreement, replay check, session construction, or store
    consumption is reached after decapsulation refuses. -/
theorem establish_responder_kem_refusal_of_calls {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (ourPrekeys : lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng : R)
    (decoded : tacenta_wire.DecodedInitial)
    (signedSecret : zeroize.Zeroizing (Array Std.U8 32#usize))
    (kemSlot : lifecycle.KemKeySlot) (lastResort : Bool)
    (initiatorIdentity initiatorEphemeral : tacenta_boundary.dh.PublicKeyBytes)
    (oneTimeSecret : Option tacenta_boundary.dh.PrivateKey)
    (hdecode : tacenta_wire.decode_initial initialMessage =
      ok (.Ok decoded))
    (hsigned : lifecycle.responder_signed_prekey_secret ourPrekeys
      decoded.signed_prekey_id = ok (.Ok signedSecret))
    (hkem : lifecycle.responder_kem_slot ourPrekeys decoded.kem_prekey_id =
      ok (.Ok (kemSlot, lastResort)))
    (hcurve : lifecycle.responder_curve_inputs
      (alloc.vec.Vec.deref decoded.identity)
      (alloc.vec.Vec.deref decoded.ephemeral) =
      ok (.Ok (initiatorIdentity, initiatorEphemeral)))
    (hone : lifecycle.responder_one_time_key ourPrekeys decoded.one_time_prekey_id =
      ok (.Ok oneTimeSecret))
    (hdecap : lifecycle.responder_decapsulate ourPrekeys kemSlot
      (alloc.vec.Vec.deref decoded.kem_ciphertext) =
      ok (.Err lifecycle.Error.Kem)) :
    lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng =
      ok (.Err lifecycle.Error.Kem, ourPrekeys, rng) := by
  unfold lifecycle.establish_responder
  cases lastResort <;>
    simp [hdecode, hsigned, hkem, hcurve, hone, hdecap,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-! Join the concrete responder identity refusal to the model's pre-lookup
    identity check.  The store relation is carried through unchanged, making
    the no-durable-effect claim part of the refinement result. -/
theorem establish_responder_invalid_identity_step_refines_of_root {R : Type}
    (storeRel : lifecycle.PrekeyStore → Model.Lifecycle.PrekeyStore → Prop)
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (oracle : Model.Lifecycle.Oracle)
    (view : Model.Lifecycle.CodewordView)
    (ourIdentity : lifecycle.Identity) (modelIdentity : Model.Lifecycle.Identity)
    (ourPrekeys : lifecycle.PrekeyStore) (modelStore : Model.Lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng : R)
    (initial : Model.Messages.Initial) (signedSecret : Model.Lifecycle.Key)
    (kemPair : Bytes) (lastResort : Bool)
    (hstore : storeRel ourPrekeys modelStore)
    (htrace : trace rng = oracle.draws)
    (hreal : lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng =
      ok (.Err (.Handshake .InvalidIdentityKey), ourPrekeys, rng))
    (hdecodeModel : Model.Messages.decodeInitialDetailed (sliceOf initialMessage) =
      .ok initial)
    (hs : Model.Lifecycle.responderSignedPrekeySecret modelStore
      initial.signedPrekeyId.toNat = some signedSecret)
    (hk : Model.Lifecycle.responderKemPair modelStore
      initial.kemPrekeyId.toNat = .ok (kemPair, lastResort))
    (hv : oracle.identityValid (initial.identity.drop 1) = false) :
    ∃ output,
      lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
        initialMessage rng = ok output ∧
      ResponderEstablishStepRefines storeRel trace dh K output
        (Model.Lifecycle.establishResponder view oracle modelIdentity modelStore
          (sliceOf initialMessage)) := by
  have hprep := Model.Lifecycle.prepareResponder_invalid_identity oracle
    modelIdentity modelStore (sliceOf initialMessage) initial signedSecret kemPair
    lastResort hdecodeModel hs hk hv
  have hmodel : Model.Lifecycle.establishResponder view oracle modelIdentity modelStore
      (sliceOf initialMessage) =
      { store := modelStore,
        result := .error (.handshake .invalidIdentityKey), oracle := oracle } := by
    simp [Model.Lifecycle.establishResponder, hprep]
  refine ⟨(.Err (.Handshake .InvalidIdentityKey), ourPrekeys, rng), hreal, ?_⟩
  rw [hmodel]
  constructor
  · simp [ResponderResultRefines, refusalOf, handshakeRefusalOf]
  · exact hstore
  · exact htrace

/-! Join the concrete responder KEM refusal to the model's authenticated
    preparation refusal.  The store and RNG are unchanged on both sides. -/
theorem establish_responder_kem_refusal_step_refines_of_root {R : Type}
    (storeRel : lifecycle.PrekeyStore → Model.Lifecycle.PrekeyStore → Prop)
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (oracle : Model.Lifecycle.Oracle)
    (view : Model.Lifecycle.CodewordView)
    (ourIdentity : lifecycle.Identity) (modelIdentity : Model.Lifecycle.Identity)
    (ourPrekeys : lifecycle.PrekeyStore) (modelStore : Model.Lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng : R)
    (initial : Model.Messages.Initial) (signedSecret : Model.Lifecycle.Key)
    (kemPair : Bytes) (lastResort : Bool) (oneTimeSecret : Option Model.Lifecycle.Key)
    (hstore : storeRel ourPrekeys modelStore)
    (htrace : trace rng = oracle.draws)
    (hreal : lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng = ok (.Err lifecycle.Error.Kem, ourPrekeys, rng))
    (hdecodeModel : Model.Messages.decodeInitialDetailed (sliceOf initialMessage) =
      .ok initial)
    (hs : Model.Lifecycle.responderSignedPrekeySecret modelStore
      initial.signedPrekeyId.toNat = some signedSecret)
    (hk : Model.Lifecycle.responderKemPair modelStore
      initial.kemPrekeyId.toNat = .ok (kemPair, lastResort))
    (hv : oracle.identityValid (initial.identity.drop 1) = true)
    (ho : Model.Lifecycle.responderOneTimeSecret modelStore
      initial.oneTimeId.toNat = .ok oneTimeSecret)
    (hkem : oracle.kemDecaps kemPair initial.kemCiphertext = none) :
    ∃ output,
      lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
        initialMessage rng = ok output ∧
      ResponderEstablishStepRefines storeRel trace dh K output
        (Model.Lifecycle.establishResponder view oracle modelIdentity modelStore
          (sliceOf initialMessage)) := by
  have hprep := Model.Lifecycle.prepareResponder_kem_refusal oracle modelIdentity
    modelStore (sliceOf initialMessage) initial signedSecret kemPair lastResort
    oneTimeSecret hdecodeModel hs hk hv ho hkem
  have hmodel : Model.Lifecycle.establishResponder view oracle modelIdentity modelStore
      (sliceOf initialMessage) =
      { store := modelStore, result := .error .kem, oracle := oracle } := by
    simp [Model.Lifecycle.establishResponder, hprep]
  refine ⟨(.Err lifecycle.Error.Kem, ourPrekeys, rng), hreal, ?_⟩
  rw [hmodel]
  constructor
  · simp [ResponderResultRefines, refusalOf]
  · exact hstore
  · exact htrace

/-! The successful responder branch has a different commit shape from every
    preparation refusal: authenticated `decrypt_ratchet` returns a plaintext,
    then the named one-time slots and (when applicable) the last-resort
    fingerprint are committed.  Keep that public success boundary explicit so
    a later call-order theorem cannot hide either the post-auth store or the
    returned wire bytes behind an existential `SessionRefines` witness. -/
theorem responder_session_refines_of_constructors
    (dh : DhView) (K : Model.Braid.Kem)
    (sharedSecret : Model.Lifecycle.Key)
    (realTriple : tacenta_triple.State) (realBraid : tacenta_braid.Braid)
    (ratchetPrivate : tacenta_boundary.dh.PrivateKey)
    (identityAd : alloc.vec.Vec Std.U8)
    (ourIdentityPublic peerIdentityPublic establishedEphemeral :
      tacenta_boundary.dh.PublicKeyBytes)
    (establishedBytes : alloc.vec.Vec Std.U8)
    (modelRatchetPrivate modelIdentityAd modelOurIdentityPublic
      modelPeerIdentityPublic modelEstablishedEphemeral : Model.Lifecycle.Key)
    (htriple : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realTriple
      (Model.Triple.initBob sharedSecret
        (dh.publicKey establishedEphemeral) .tacenta))
    (hbraid : Tacenta.SessionUnitBraidT3.StateRefines K realBraid.state
      (Model.Braid.initBob sharedSecret))
    (hprivate : dh.privateKey ratchetPrivate = modelRatchetPrivate)
    (had : vecOf identityAd = modelIdentityAd)
    (hour : dh.publicKey ourIdentityPublic = modelOurIdentityPublic)
    (hpeer : dh.publicKey peerIdentityPublic = modelPeerIdentityPublic)
    (hEstablished : vecOf establishedBytes = modelEstablishedEphemeral) :
    SessionRefines dh K
      { triple := realTriple, braid := realBraid,
        ratchet_private := ratchetPrivate, identity_ad := identityAd,
        our_identity_public := ourIdentityPublic,
        peer_identity_public := peerIdentityPublic,
        pending_initial := none,
        established_ephemeral := some establishedBytes }
      { triple := Model.Triple.initBob sharedSecret
          (dh.publicKey establishedEphemeral) .tacenta,
        braid := Model.Braid.initBob sharedSecret,
        ratchetPrivate := modelRatchetPrivate,
        identityAd := modelIdentityAd,
        ourIdentityPublic := modelOurIdentityPublic,
        peerIdentityPublic := modelPeerIdentityPublic,
        pendingInitial := none,
        establishedEphemeral := some modelEstablishedEphemeral } := by
  constructor
  · exact htriple
  · exact hbraid
  · exact hprivate
  · exact had
  · exact hour
  · exact hpeer
  · simp
  · simp [hEstablished]

/-! Root/model adapter for the successful responder branch.  This is the
    responder analogue of the initiator success adapter below: the concrete
    root equation, executable-model equation, session relation, plaintext
    relation, store relation, and trace relation are all separate obligations.
    In particular, this theorem does not prove the transaction boundary by
    assumption; it makes the post-auth store that must be supplied by that
    proof visible in the result. -/
theorem establish_responder_success_step_refines_of_root_and_model
    {R : Type}
    (storeRel : lifecycle.PrekeyStore → Model.Lifecycle.PrekeyStore → Prop)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (ourPrekeys : lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng rngAfter : R)
    (realSession : lifecycle.Session) (realPlaintext : alloc.vec.Vec Std.U8)
    (realStoreAfter : lifecycle.PrekeyStore)
    (modelIdentity : Model.Lifecycle.Identity)
    (modelStore : Model.Lifecycle.PrekeyStore)
    (modelSession : Model.Lifecycle.Session) (modelPlaintext : Bytes)
    (modelStoreAfter : Model.Lifecycle.PrekeyStore)
    (modelOracleAfter : Model.Lifecycle.Oracle)
    (hreal : lifecycle.establish_responder rngCore cryptoRng ourIdentity
      ourPrekeys initialMessage rng =
      ok (.Ok (realSession, realPlaintext), realStoreAfter, rngAfter))
    (hmodel : Model.Lifecycle.establishResponder view oracle modelIdentity
      modelStore (sliceOf initialMessage) =
      { store := modelStoreAfter,
        result := .ok (modelSession, modelPlaintext),
        oracle := modelOracleAfter })
    (hrel : SessionRefines dh K realSession modelSession)
    (hplaintext : vecOf realPlaintext = modelPlaintext)
    (hstore : storeRel realStoreAfter modelStoreAfter)
    (htrace : trace rngAfter = modelOracleAfter.draws) :
    ∃ output,
      lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
        initialMessage rng = ok output ∧
      ResponderEstablishStepRefines storeRel trace dh K output
        (Model.Lifecycle.establishResponder view oracle modelIdentity modelStore
          (sliceOf initialMessage)) := by
  refine ⟨(.Ok (realSession, realPlaintext), realStoreAfter, rngAfter), hreal, ?_⟩
  rw [hmodel]
  constructor
  · exact ⟨hrel, hplaintext⟩
  · exact hstore
  · exact htrace

/-! Concrete successful call-order branch: no curve one-time prekey and no
    last-resort replay record.  This is the first responder success equation
    at the generated public root.  The other successful store-commit variants
    will reuse the same prefix and replace only the explicit commit tail. -/
theorem establish_responder_success_no_one_time_no_last_resort_of_calls {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (ourPrekeys : lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng rngAfter : R)
    (decoded : tacenta_wire.DecodedInitial)
    (kemSlot : lifecycle.KemKeySlot)
    (initiatorIdentity initiatorEphemeral : tacenta_boundary.dh.PublicKeyBytes)
    (oneTimeSecret : Option tacenta_boundary.dh.PrivateKey)
    (kemSecret sharedSecret : Array Std.U8 32#usize)
    (signedBytes : Array Std.U8 32#usize)
    (signedSecret : zeroize.Zeroizing (Array Std.U8 32#usize))
    (signedPrekey identityPrivate : tacenta_boundary.dh.PrivateKey)
    (sharedWrapped kemWrapped : zeroize.Zeroizing (Array Std.U8 32#usize))
    (sharedSlice : Slice Std.U8)
    (realTriple : tacenta_triple.State) (realBraid : tacenta_braid.Braid)
    (identityAd : alloc.vec.Vec Std.U8)
    (ourIdentityPublic signedPrekeyPublic : tacenta_boundary.dh.PublicKeyBytes)
    (signedPrekeyBytes : Array Std.U8 32#usize)
    (establishedEphemeral : alloc.vec.Vec Std.U8)
    (realSession : lifecycle.Session)
    (plaintext : alloc.vec.Vec Std.U8)
    (storeAfter : lifecycle.PrekeyStore)
    (hdecode : tacenta_wire.decode_initial initialMessage =
      ok (.Ok decoded))
    (hsigned : lifecycle.responder_signed_prekey_secret ourPrekeys
      decoded.signed_prekey_id = ok (.Ok signedSecret))
    (hkem : lifecycle.responder_kem_slot ourPrekeys decoded.kem_prekey_id =
      ok (.Ok (kemSlot, false)))
    (hcurve : lifecycle.responder_curve_inputs
      (alloc.vec.Vec.deref decoded.identity)
      (alloc.vec.Vec.deref decoded.ephemeral) =
      ok (.Ok (initiatorIdentity, initiatorEphemeral)))
    (hone : lifecycle.responder_one_time_key ourPrekeys
      decoded.one_time_prekey_id = ok (.Ok none))
    (hdecap : lifecycle.responder_decapsulate ourPrekeys kemSlot
      (alloc.vec.Vec.deref decoded.kem_ciphertext) =
      ok (.Ok kemSecret))
    (hdecapNew : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) kemSecret =
      ok kemWrapped)
    (hdecapDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) kemWrapped =
      ok kemSecret)
    (hsignedDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) signedSecret =
      ok signedBytes)
    (hsignedPrivate : tacenta_boundary.dh.PrivateKey.from_bytes signedBytes =
      ok signedPrekey)
    (hshared : responder_shared_secret identityPrivate signedPrekey none
      initiatorIdentity initiatorEphemeral kemSecret =
      ok (.Ok sharedSecret))
    (hsharedNew : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sharedSecret =
      ok sharedWrapped)
    (hsharedDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sharedWrapped =
      ok sharedSecret)
    (hidentityDh : lifecycle.Identity.dh_key ourIdentity = ok identityPrivate)
    (hidentityPublic : lifecycle.Identity.public ourIdentity =
      ok ourIdentityPublic)
    (hidentityAd : lifecycle.identity_ad initiatorIdentity ourIdentityPublic =
      ok identityAd)
    (hsharedSlice : core.array.Array.index (core.ops.index.IndexSlice
      (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice
      Std.U8)) sharedSecret () = ok sharedSlice)
    (hsignedPublic : tacenta_boundary.dh.PrivateKey.public_key signedPrekey =
      ok signedPrekeyPublic)
    (hsignedPublicBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes
      signedPrekeyPublic = ok signedPrekeyBytes)
    (htriple : tacenta_triple.State.init_receiver sharedSlice
      signedPrekeyBytes tacenta_ratchet.LabelSet.Tacenta =
      ok realTriple)
    (hbraid : tacenta_braid.Braid.responder sharedSlice = ok realBraid)
    (hclone : alloc.vec.CloneVec.clone core.clone.CloneU8 decoded.ephemeral =
      ok establishedEphemeral)
    (hdecrypt : lifecycle.Session.decrypt_ratchet rngCore cryptoRng
      { triple := realTriple, braid := realBraid,
        ratchet_private := signedPrekey, identity_ad := identityAd,
        our_identity_public := ourIdentityPublic,
        peer_identity_public := initiatorIdentity,
        pending_initial := none,
        established_ephemeral := some establishedEphemeral }
      (alloc.vec.Vec.deref decoded.message) rng =
      ok (.Ok plaintext, realSession, rngAfter))
    (honeId : decoded.one_time_prekey_id = serialization.ABSENT_ID)
    (htake : lifecycle.PrekeyStore.take_one_time_kem ourPrekeys
      decoded.kem_prekey_id = ok (none, storeAfter)) :
    lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng = ok (.Ok (realSession, plaintext), storeAfter, rngAfter) := by
  have hone' : lifecycle.responder_one_time_key ourPrekeys
      serialization.ABSENT_ID = ok (.Ok none) := by
    simpa [honeId] using hone
  unfold lifecycle.establish_responder
  simp [hdecode, hsigned, hkem, hcurve, hone, hdecap, hdecapNew,
    hdecapDeref, hsignedDeref, hsignedPrivate, hshared, hsharedNew,
    hsharedDeref, hidentityDh, hidentityPublic, hidentityAd, hsharedSlice,
    hsignedPublic, hsignedPublicBytes, htriple, hbraid, hclone, hdecrypt,
    honeId, hone', htake, lifecycle.responder_replay_fingerprint,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-! The matching one-time-prekey success branch.  The authenticated prefix is
    intentionally repeated here rather than hidden behind a postulated root
    result: this branch proves that both durable consumptions occur only after
    `decrypt_ratchet` has returned an authenticated plaintext. -/
theorem establish_responder_success_one_time_no_last_resort_of_calls {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (ourPrekeys : lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng rngAfter : R)
    (decoded : tacenta_wire.DecodedInitial)
    (kemSlot : lifecycle.KemKeySlot)
    (initiatorIdentity initiatorEphemeral : tacenta_boundary.dh.PublicKeyBytes)
    (oneTimePrivate : tacenta_boundary.dh.PrivateKey)
    (kemSecret sharedSecret : Array Std.U8 32#usize)
    (signedBytes : Array Std.U8 32#usize)
    (signedSecret : zeroize.Zeroizing (Array Std.U8 32#usize))
    (signedPrekey identityPrivate : tacenta_boundary.dh.PrivateKey)
    (sharedWrapped kemWrapped : zeroize.Zeroizing (Array Std.U8 32#usize))
    (sharedSlice : Slice Std.U8)
    (realTriple : tacenta_triple.State) (realBraid : tacenta_braid.Braid)
    (identityAd : alloc.vec.Vec Std.U8)
    (ourIdentityPublic signedPrekeyPublic : tacenta_boundary.dh.PublicKeyBytes)
    (signedPrekeyBytes : Array Std.U8 32#usize)
    (establishedEphemeral : alloc.vec.Vec Std.U8)
    (realSession : lifecycle.Session)
    (plaintext : alloc.vec.Vec Std.U8)
    (storeAfterKem storeAfter : lifecycle.PrekeyStore)
    (hdecode : tacenta_wire.decode_initial initialMessage =
      ok (.Ok decoded))
    (hsigned : lifecycle.responder_signed_prekey_secret ourPrekeys
      decoded.signed_prekey_id = ok (.Ok signedSecret))
    (hkem : lifecycle.responder_kem_slot ourPrekeys decoded.kem_prekey_id =
      ok (.Ok (kemSlot, false)))
    (hcurve : lifecycle.responder_curve_inputs
      (alloc.vec.Vec.deref decoded.identity)
      (alloc.vec.Vec.deref decoded.ephemeral) =
      ok (.Ok (initiatorIdentity, initiatorEphemeral)))
    (hone : lifecycle.responder_one_time_key ourPrekeys
      decoded.one_time_prekey_id = ok (.Ok (some oneTimePrivate)))
    (hdecap : lifecycle.responder_decapsulate ourPrekeys kemSlot
      (alloc.vec.Vec.deref decoded.kem_ciphertext) =
      ok (.Ok kemSecret))
    (hdecapNew : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) kemSecret =
      ok kemWrapped)
    (hdecapDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) kemWrapped =
      ok kemSecret)
    (hsignedDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) signedSecret =
      ok signedBytes)
    (hsignedPrivate : tacenta_boundary.dh.PrivateKey.from_bytes signedBytes =
      ok signedPrekey)
    (hshared : responder_shared_secret identityPrivate signedPrekey
      (some oneTimePrivate) initiatorIdentity initiatorEphemeral kemSecret =
      ok (.Ok sharedSecret))
    (hsharedNew : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sharedSecret =
      ok sharedWrapped)
    (hsharedDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sharedWrapped =
      ok sharedSecret)
    (hidentityDh : lifecycle.Identity.dh_key ourIdentity = ok identityPrivate)
    (hidentityPublic : lifecycle.Identity.public ourIdentity =
      ok ourIdentityPublic)
    (hidentityAd : lifecycle.identity_ad initiatorIdentity ourIdentityPublic =
      ok identityAd)
    (hsharedSlice : core.array.Array.index (core.ops.index.IndexSlice
      (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice
      Std.U8)) sharedSecret () = ok sharedSlice)
    (hsignedPublic : tacenta_boundary.dh.PrivateKey.public_key signedPrekey =
      ok signedPrekeyPublic)
    (hsignedPublicBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes
      signedPrekeyPublic = ok signedPrekeyBytes)
    (htriple : tacenta_triple.State.init_receiver sharedSlice
      signedPrekeyBytes tacenta_ratchet.LabelSet.Tacenta =
      ok realTriple)
    (hbraid : tacenta_braid.Braid.responder sharedSlice = ok realBraid)
    (hclone : alloc.vec.CloneVec.clone core.clone.CloneU8 decoded.ephemeral =
      ok establishedEphemeral)
    (hdecrypt : lifecycle.Session.decrypt_ratchet rngCore cryptoRng
      { triple := realTriple, braid := realBraid,
        ratchet_private := signedPrekey, identity_ad := identityAd,
        our_identity_public := ourIdentityPublic,
        peer_identity_public := initiatorIdentity,
        pending_initial := none,
        established_ephemeral := some establishedEphemeral }
      (alloc.vec.Vec.deref decoded.message) rng =
      ok (.Ok plaintext, realSession, rngAfter))
    (honeId : decoded.one_time_prekey_id ≠ serialization.ABSENT_ID)
    (htakeKem : lifecycle.PrekeyStore.take_one_time_kem ourPrekeys
      decoded.kem_prekey_id = ok (none, storeAfterKem))
    (htakeOne : lifecycle.PrekeyStore.take_one_time storeAfterKem
      decoded.one_time_prekey_id = ok (true, storeAfter)) :
    lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng = ok (.Ok (realSession, plaintext), storeAfter, rngAfter) := by
  unfold lifecycle.establish_responder
  have honeId' : ¬ (decoded.one_time_prekey_id.val =
      serialization.ABSENT_ID.val) := by
    intro h
    exact honeId (UScalar.eq_of_val_eq h)
  simp [hdecode, hsigned, hkem, hcurve, hone, hdecap, hdecapNew,
    hdecapDeref, hsignedDeref, hsignedPrivate, hshared, hsharedNew,
    hsharedDeref, hidentityDh, hidentityPublic, hidentityAd, hsharedSlice,
    hsignedPublic, hsignedPublicBytes, htriple, hbraid, hclone, hdecrypt,
    honeId, honeId', htakeKem, htakeOne,
    lifecycle.responder_replay_fingerprint,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-! The last-resort success branch.  Unlike the reusable one-time branch above,
    this branch proves the authenticated replay-record append and its capacity
    check after the ratchet has accepted the inner message. -/
theorem establish_responder_success_last_resort_no_one_time_of_calls {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (ourPrekeys : lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng rngAfter : R)
    (decoded : tacenta_wire.DecodedInitial)
    (kemSlot : lifecycle.KemKeySlot)
    (initiatorIdentity initiatorEphemeral : tacenta_boundary.dh.PublicKeyBytes)
    (kemSecret sharedSecret : Array Std.U8 32#usize)
    (signedBytes : Array Std.U8 32#usize)
    (signedSecret : zeroize.Zeroizing (Array Std.U8 32#usize))
    (signedPrekey identityPrivate : tacenta_boundary.dh.PrivateKey)
    (sharedWrapped kemWrapped : zeroize.Zeroizing (Array Std.U8 32#usize))
    (sharedSlice : Slice Std.U8)
    (realTriple : tacenta_triple.State) (realBraid : tacenta_braid.Braid)
    (identityAd : alloc.vec.Vec Std.U8)
    (ourIdentityPublic signedPrekeyPublic : tacenta_boundary.dh.PublicKeyBytes)
    (signedPrekeyBytes : Array Std.U8 32#usize)
    (establishedEphemeral : alloc.vec.Vec Std.U8)
    (realSession : lifecycle.Session)
    (plaintext : alloc.vec.Vec Std.U8)
    (fingerprint : Array Std.U8 32#usize)
    (seenCount : Std.Usize)
    (seenAfter : alloc.vec.Vec (Std.U32 × (Array Std.U8 32#usize)))
    (storeAfter : lifecycle.PrekeyStore)
    (hdecode : tacenta_wire.decode_initial initialMessage =
      ok (.Ok decoded))
    (hsigned : lifecycle.responder_signed_prekey_secret ourPrekeys
      decoded.signed_prekey_id = ok (.Ok signedSecret))
    (hkem : lifecycle.responder_kem_slot ourPrekeys decoded.kem_prekey_id =
      ok (.Ok (kemSlot, true)))
    (hcurve : lifecycle.responder_curve_inputs
      (alloc.vec.Vec.deref decoded.identity)
      (alloc.vec.Vec.deref decoded.ephemeral) =
      ok (.Ok (initiatorIdentity, initiatorEphemeral)))
    (hone : lifecycle.responder_one_time_key ourPrekeys
      decoded.one_time_prekey_id = ok (.Ok none))
    (hdecap : lifecycle.responder_decapsulate ourPrekeys kemSlot
      (alloc.vec.Vec.deref decoded.kem_ciphertext) =
      ok (.Ok kemSecret))
    (hdecapNew : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) kemSecret =
      ok kemWrapped)
    (hdecapDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) kemWrapped =
      ok kemSecret)
    (hsignedDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) signedSecret =
      ok signedBytes)
    (hsignedPrivate : tacenta_boundary.dh.PrivateKey.from_bytes signedBytes =
      ok signedPrekey)
    (hshared : responder_shared_secret identityPrivate signedPrekey none
      initiatorIdentity initiatorEphemeral kemSecret =
      ok (.Ok sharedSecret))
    (hsharedNew : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sharedSecret =
      ok sharedWrapped)
    (hsharedDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sharedWrapped =
      ok sharedSecret)
    (hidentityDh : lifecycle.Identity.dh_key ourIdentity = ok identityPrivate)
    (hidentityPublic : lifecycle.Identity.public ourIdentity =
      ok ourIdentityPublic)
    (hidentityAd : lifecycle.identity_ad initiatorIdentity ourIdentityPublic =
      ok identityAd)
    (hsharedSlice : core.array.Array.index (core.ops.index.IndexSlice
      (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice
      Std.U8)) sharedSecret () = ok sharedSlice)
    (hsignedPublic : tacenta_boundary.dh.PrivateKey.public_key signedPrekey =
      ok signedPrekeyPublic)
    (hsignedPublicBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes
      signedPrekeyPublic = ok signedPrekeyBytes)
    (htriple : tacenta_triple.State.init_receiver sharedSlice
      signedPrekeyBytes tacenta_ratchet.LabelSet.Tacenta =
      ok realTriple)
    (hbraid : tacenta_braid.Braid.responder sharedSlice = ok realBraid)
    (hclone : alloc.vec.CloneVec.clone core.clone.CloneU8 decoded.ephemeral =
      ok establishedEphemeral)
    (hdecrypt : lifecycle.Session.decrypt_ratchet rngCore cryptoRng
      { triple := realTriple, braid := realBraid,
        ratchet_private := signedPrekey, identity_ad := identityAd,
        our_identity_public := ourIdentityPublic,
        peer_identity_public := initiatorIdentity,
        pending_initial := none,
        established_ephemeral := some establishedEphemeral }
      (alloc.vec.Vec.deref decoded.message) rng =
      ok (.Ok plaintext, realSession, rngAfter))
    (honeId : decoded.one_time_prekey_id = serialization.ABSENT_ID)
    (hreplay : lifecycle.responder_replay_fingerprint ourPrekeys
      decoded.kem_prekey_id sharedSecret true =
      ok (.Ok (some fingerprint)))
    (hseen : lifecycle.PrekeyStore.last_resort_seen_for ourPrekeys
      decoded.kem_prekey_id = ok seenCount)
    (hcount : seenCount < lifecycle.MAX_LAST_RESORT_SEEN)
    (hpush : alloc.vec.Vec.push ourPrekeys.last_resort_seen
      (decoded.kem_prekey_id, fingerprint) = ok seenAfter)
    (hstore : { ourPrekeys with last_resort_seen := seenAfter } = storeAfter) :
    lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng = ok (.Ok (realSession, plaintext), storeAfter, rngAfter) := by
  have hone' : lifecycle.responder_one_time_key ourPrekeys
      serialization.ABSENT_ID = ok (.Ok none) := by
    simpa [honeId] using hone
  have hcount' : (↑seenCount : Nat) <
      (↑lifecycle.MAX_LAST_RESORT_SEEN : Nat) :=
    (UScalar.lt_equiv _ _).mp hcount
  unfold lifecycle.establish_responder
  simp [hdecode, hsigned, hkem, hcurve, hone, hdecap, hdecapNew,
    hdecapDeref, hsignedDeref, hsignedPrivate, hshared, hsharedNew,
    hsharedDeref, hidentityDh, hidentityPublic, hidentityAd, hsharedSlice,
    hsignedPublic, hsignedPublicBytes, htriple, hbraid, hclone, hdecrypt,
    honeId, hone', hreplay, hseen, hcount, hcount', hpush, hstore,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-! The mixed success branch is the remaining concrete responder commit shape:
    the reusable last-resort KEM is recorded, while the authenticated message
    also consumes a curve one-time prekey.  The KEM slot is not removed on this
    path; the curve slot is removed before the replay record is appended. -/
theorem establish_responder_success_last_resort_one_time_of_calls {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (ourPrekeys : lifecycle.PrekeyStore)
    (initialMessage : Slice Std.U8) (rng rngAfter : R)
    (decoded : tacenta_wire.DecodedInitial)
    (kemSlot : lifecycle.KemKeySlot)
    (initiatorIdentity initiatorEphemeral : tacenta_boundary.dh.PublicKeyBytes)
    (oneTimePrivate : tacenta_boundary.dh.PrivateKey)
    (kemSecret sharedSecret : Array Std.U8 32#usize)
    (signedBytes : Array Std.U8 32#usize)
    (signedSecret : zeroize.Zeroizing (Array Std.U8 32#usize))
    (signedPrekey identityPrivate : tacenta_boundary.dh.PrivateKey)
    (sharedWrapped kemWrapped : zeroize.Zeroizing (Array Std.U8 32#usize))
    (sharedSlice : Slice Std.U8)
    (realTriple : tacenta_triple.State) (realBraid : tacenta_braid.Braid)
    (identityAd : alloc.vec.Vec Std.U8)
    (ourIdentityPublic signedPrekeyPublic : tacenta_boundary.dh.PublicKeyBytes)
    (signedPrekeyBytes : Array Std.U8 32#usize)
    (establishedEphemeral : alloc.vec.Vec Std.U8)
    (realSession : lifecycle.Session)
    (plaintext : alloc.vec.Vec Std.U8)
    (fingerprint : Array Std.U8 32#usize)
    (seenCount : Std.Usize)
    (seenAfter : alloc.vec.Vec (Std.U32 × (Array Std.U8 32#usize)))
    (storeAfterCurve storeAfter : lifecycle.PrekeyStore)
    (hdecode : tacenta_wire.decode_initial initialMessage =
      ok (.Ok decoded))
    (hsigned : lifecycle.responder_signed_prekey_secret ourPrekeys
      decoded.signed_prekey_id = ok (.Ok signedSecret))
    (hkem : lifecycle.responder_kem_slot ourPrekeys decoded.kem_prekey_id =
      ok (.Ok (kemSlot, true)))
    (hcurve : lifecycle.responder_curve_inputs
      (alloc.vec.Vec.deref decoded.identity)
      (alloc.vec.Vec.deref decoded.ephemeral) =
      ok (.Ok (initiatorIdentity, initiatorEphemeral)))
    (hone : lifecycle.responder_one_time_key ourPrekeys
      decoded.one_time_prekey_id = ok (.Ok (some oneTimePrivate)))
    (hdecap : lifecycle.responder_decapsulate ourPrekeys kemSlot
      (alloc.vec.Vec.deref decoded.kem_ciphertext) =
      ok (.Ok kemSecret))
    (hdecapNew : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) kemSecret =
      ok kemWrapped)
    (hdecapDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) kemWrapped =
      ok kemSecret)
    (hsignedDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) signedSecret =
      ok signedBytes)
    (hsignedPrivate : tacenta_boundary.dh.PrivateKey.from_bytes signedBytes =
      ok signedPrekey)
    (hshared : responder_shared_secret identityPrivate signedPrekey
      (some oneTimePrivate) initiatorIdentity initiatorEphemeral kemSecret =
      ok (.Ok sharedSecret))
    (hsharedNew : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sharedSecret =
      ok sharedWrapped)
    (hsharedDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sharedWrapped =
      ok sharedSecret)
    (hidentityDh : lifecycle.Identity.dh_key ourIdentity = ok identityPrivate)
    (hidentityPublic : lifecycle.Identity.public ourIdentity =
      ok ourIdentityPublic)
    (hidentityAd : lifecycle.identity_ad initiatorIdentity ourIdentityPublic =
      ok identityAd)
    (hsharedSlice : core.array.Array.index (core.ops.index.IndexSlice
      (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice
      Std.U8)) sharedSecret () = ok sharedSlice)
    (hsignedPublic : tacenta_boundary.dh.PrivateKey.public_key signedPrekey =
      ok signedPrekeyPublic)
    (hsignedPublicBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes
      signedPrekeyPublic = ok signedPrekeyBytes)
    (htriple : tacenta_triple.State.init_receiver sharedSlice
      signedPrekeyBytes tacenta_ratchet.LabelSet.Tacenta =
      ok realTriple)
    (hbraid : tacenta_braid.Braid.responder sharedSlice = ok realBraid)
    (hclone : alloc.vec.CloneVec.clone core.clone.CloneU8 decoded.ephemeral =
      ok establishedEphemeral)
    (hdecrypt : lifecycle.Session.decrypt_ratchet rngCore cryptoRng
      { triple := realTriple, braid := realBraid,
        ratchet_private := signedPrekey, identity_ad := identityAd,
        our_identity_public := ourIdentityPublic,
        peer_identity_public := initiatorIdentity,
        pending_initial := none,
        established_ephemeral := some establishedEphemeral }
      (alloc.vec.Vec.deref decoded.message) rng =
      ok (.Ok plaintext, realSession, rngAfter))
    (honeId : decoded.one_time_prekey_id ≠ serialization.ABSENT_ID)
    (hreplay : lifecycle.responder_replay_fingerprint ourPrekeys
      decoded.kem_prekey_id sharedSecret true =
      ok (.Ok (some fingerprint)))
    (hseen : lifecycle.PrekeyStore.last_resort_seen_for ourPrekeys
      decoded.kem_prekey_id = ok seenCount)
    (hcount : seenCount < lifecycle.MAX_LAST_RESORT_SEEN)
    (hpush : alloc.vec.Vec.push ourPrekeys.last_resort_seen
      (decoded.kem_prekey_id, fingerprint) = ok seenAfter)
    (htakeOne : lifecycle.PrekeyStore.take_one_time ourPrekeys
      decoded.one_time_prekey_id = ok (true, storeAfterCurve))
    (hseenCurve : storeAfterCurve.last_resort_seen = ourPrekeys.last_resort_seen)
    (hseenCurveCount : lifecycle.PrekeyStore.last_resort_seen_for storeAfterCurve
      decoded.kem_prekey_id = ok seenCount)
    (hpushCurve : alloc.vec.Vec.push storeAfterCurve.last_resort_seen
      (decoded.kem_prekey_id, fingerprint) = ok seenAfter)
    (hstore : { storeAfterCurve with last_resort_seen := seenAfter } = storeAfter) :
    lifecycle.establish_responder rngCore cryptoRng ourIdentity ourPrekeys
      initialMessage rng = ok (.Ok (realSession, plaintext), storeAfter, rngAfter) := by
  have honeId' : ¬ (decoded.one_time_prekey_id.val =
      serialization.ABSENT_ID.val) := by
    intro h
    exact honeId (UScalar.eq_of_val_eq h)
  have hcount' : (↑seenCount : Nat) <
      (↑lifecycle.MAX_LAST_RESORT_SEEN : Nat) :=
    (UScalar.lt_equiv _ _).mp hcount
  unfold lifecycle.establish_responder
  simp [hdecode, hsigned, hkem, hcurve, hone, hdecap, hdecapNew,
    hdecapDeref, hsignedDeref, hsignedPrivate, hshared, hsharedNew,
    hsharedDeref, hidentityDh, hidentityPublic, hidentityAd, hsharedSlice,
    hsignedPublic, hsignedPublicBytes, htriple, hbraid, hclone, hdecrypt,
    honeId, honeId', hreplay, hseen, hcount, hcount', hpush, htakeOne,
    hseenCurve, hseenCurveCount, hpushCurve, hstore,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-! The first concrete establishment composition.  The translated public
root and executable model both refuse an unexpected peer identity before any
signature, KEM, DH, or RNG work.  The comparison result is supplied by the
existing translated boundary contract; the theorem consumes it and proves
the complete public result/refinement pair, including the unchanged RNG. -/
theorem establish_initiator_identity_mismatch_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (oracle : Model.Lifecycle.Oracle)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (expectedIdentity : tacenta_boundary.dh.PublicKeyBytes) (rng : R)
    (modelIdentity : Model.Lifecycle.Identity)
    (modelBundle : Model.Lifecycle.Bundle) (modelExpectedIdentity : Model.Lifecycle.Key)
    (hcmp : core.cmp.PartialEq.ne.trait_default
      tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes
      theirBundle.bundle.identity_key expectedIdentity = ok true)
    (hmodelIdentity : (modelBundle.identityKey != modelExpectedIdentity) = true)
    (htrace : trace rng = oracle.draws) :
    ∃ output,
      lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity theirBundle
        expectedIdentity rng = ok output ∧
      EstablishStepRefines trace dh K output
        (Model.Lifecycle.establishInitiator oracle modelIdentity modelBundle
          modelExpectedIdentity) := by
  have hreal :
      lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity theirBundle
        expectedIdentity rng =
        ok (.Err lifecycle.Error.UnexpectedIdentity, rng) := by
    unfold lifecycle.establish_initiator_for
    rw [hcmp]
    simp
  have hmodel := Model.Lifecycle.establishInitiator_identity_mismatch
    oracle modelIdentity modelBundle modelExpectedIdentity hmodelIdentity
  refine ⟨(.Err lifecycle.Error.UnexpectedIdentity, rng), hreal, ?_⟩
  rw [hmodel]
  constructor
  · simp [EstablishResultRefines, refusalOf]
  · exact htrace

theorem establish_initiator_presence_mismatch_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (oracle : Model.Lifecycle.Oracle)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (expectedIdentity : tacenta_boundary.dh.PublicKeyBytes) (rng : R)
    (modelIdentity : Model.Lifecycle.Identity)
    (modelBundle : Model.Lifecycle.Bundle) (modelExpectedIdentity : Model.Lifecycle.Key)
    (hcmp : core.cmp.PartialEq.ne.trait_default
      tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes
      theirBundle.bundle.identity_key expectedIdentity = ok false)
    (hmodelIdentity : modelBundle.identityKey = modelExpectedIdentity)
    (hpresence : (modelBundle.oneTimePrekey.isSome !=
      (modelBundle.oneTimeId != Model.Lifecycle.absentId)) = true)
    (hrealPresence : (core.option.Option.is_some theirBundle.bundle.one_time_prekey !=
      (theirBundle.one_time_prekey_id != serialization.ABSENT_ID)) = true)
    (htrace : trace rng = oracle.draws) :
    ∃ output,
      lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity theirBundle
        expectedIdentity rng = ok output ∧
      EstablishStepRefines trace dh K output
        (Model.Lifecycle.establishInitiator oracle modelIdentity modelBundle
          modelExpectedIdentity) := by
  have hreal :
      lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity theirBundle
        expectedIdentity rng =
        ok (.Err lifecycle.Error.InconsistentBundle, rng) := by
    unfold lifecycle.establish_initiator_for
    rw [hcmp]
    simp only [bne_iff_ne] at hrealPresence
    have hrealPresence' :
        ¬ (theirBundle.bundle.one_time_prekey.isSome =
          (theirBundle.one_time_prekey_id != serialization.ABSENT_ID)) := by
      intro h
      exact hrealPresence h
    simp [hrealPresence']
  have hmodel := Model.Lifecycle.establishInitiator_presence_mismatch
    oracle modelIdentity modelBundle modelExpectedIdentity hmodelIdentity hpresence
  refine ⟨(.Err lifecycle.Error.InconsistentBundle, rng), hreal, ?_⟩
  rw [hmodel]
  constructor
  · simp [EstablishResultRefines, refusalOf]
  · exact htrace

/-! The next refusal is the public canonical-key gate.  This is deliberately
composed at the root rather than left as a leaf predicate: the translated
optional-key checks and the model's three-key canonicality guard must agree on
the same ordering, and the refusal must still leave the RNG trace untouched. -/
theorem establish_initiator_noncanonical_identity_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (oracle : Model.Lifecycle.Oracle)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (expectedIdentity : tacenta_boundary.dh.PublicKeyBytes) (rng : R)
    (modelIdentity : Model.Lifecycle.Identity)
    (modelBundle : Model.Lifecycle.Bundle) (modelExpectedIdentity : Model.Lifecycle.Key)
    (hcmp : core.cmp.PartialEq.ne.trait_default
      tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes
      theirBundle.bundle.identity_key expectedIdentity = ok false)
    (hmodelIdentity : modelBundle.identityKey = modelExpectedIdentity)
    (hpresence : modelBundle.oneTimePrekey.isSome =
      (modelBundle.oneTimeId != Model.Lifecycle.absentId))
    (hnoOneTime : theirBundle.bundle.one_time_prekey = none)
    (habsentId : theirBundle.one_time_prekey_id = serialization.ABSENT_ID)
    (hcanonical : is_canonical_key theirBundle.bundle.identity_key = ok false)
    (hmodelCanonical : Model.Messages.canonicalKey modelBundle.identityKey = false)
    (htrace : trace rng = oracle.draws) :
    ∃ output,
      lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity theirBundle
        expectedIdentity rng = ok output ∧
      EstablishStepRefines trace dh K output
        (Model.Lifecycle.establishInitiator oracle modelIdentity modelBundle
          modelExpectedIdentity) := by
  have hreal :
      lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity theirBundle
        expectedIdentity rng =
        ok (.Err lifecycle.Error.BadEncoding, rng) := by
    unfold lifecycle.establish_initiator_for
    rw [hcmp]
    simp [hnoOneTime, habsentId, hcanonical]
  have hmodelCanonical' :
      (!Model.Messages.canonicalKey modelBundle.identityKey ||
        !Model.Messages.canonicalKey modelBundle.signedPrekey ||
        !modelBundle.oneTimePrekey.all Model.Messages.canonicalKey) = true := by
    simp [hmodelCanonical]
  have hmodel := Model.Lifecycle.establishInitiator_noncanonical
    oracle modelIdentity modelBundle modelExpectedIdentity hmodelIdentity
    hpresence hmodelCanonical'
  refine ⟨(.Err lifecycle.Error.BadEncoding, rng), hreal, ?_⟩
  rw [hmodel]
  constructor
  · simp [EstablishResultRefines, refusalOf]
  · exact htrace

/-! The shipped public initiator root fixes the expected identity to the
bundle's advertised identity.  Compose that wrapper explicitly so the
canonical-key refusal is attached to the public root, not only to the
parameterised helper above. -/
theorem establish_initiator_noncanonical_identity_public_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (oracle : Model.Lifecycle.Oracle)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (rng : R) (modelIdentity : Model.Lifecycle.Identity)
    (modelBundle : Model.Lifecycle.Bundle)
    (hcmpSelf : core.cmp.PartialEq.ne.trait_default
      tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes
      theirBundle.bundle.identity_key theirBundle.bundle.identity_key = ok false)
    (hpresence : modelBundle.oneTimePrekey.isSome =
      (modelBundle.oneTimeId != Model.Lifecycle.absentId))
    (hnoOneTime : theirBundle.bundle.one_time_prekey = none)
    (habsentId : theirBundle.one_time_prekey_id = serialization.ABSENT_ID)
    (hcanonical : is_canonical_key theirBundle.bundle.identity_key = ok false)
    (hmodelCanonical : Model.Messages.canonicalKey modelBundle.identityKey = false)
    (htrace : trace rng = oracle.draws) :
    ∃ output,
      lifecycle.establish_initiator rngCore cryptoRng ourIdentity theirBundle rng =
        ok output ∧
      EstablishStepRefines trace dh K output
        (Model.Lifecycle.establishInitiator oracle modelIdentity modelBundle
          modelBundle.identityKey) := by
  obtain ⟨output, hcall, hstep⟩ := establish_initiator_noncanonical_identity_step_refines
    rngCore cryptoRng trace dh K oracle ourIdentity theirBundle
      theirBundle.bundle.identity_key rng modelIdentity modelBundle
      modelBundle.identityKey hcmpSelf rfl hpresence hnoOneTime habsentId hcanonical
      hmodelCanonical htrace
  refine ⟨output, ?_, hstep⟩
  simpa [lifecycle.establish_initiator] using hcall

theorem establish_initiator_presence_mismatch_public_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (oracle : Model.Lifecycle.Oracle)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (rng : R) (modelIdentity : Model.Lifecycle.Identity)
    (modelBundle : Model.Lifecycle.Bundle)
    (hcmpSelf : core.cmp.PartialEq.ne.trait_default
      tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes
      theirBundle.bundle.identity_key theirBundle.bundle.identity_key = ok false)
    (hmodelPresence : (modelBundle.oneTimePrekey.isSome !=
      (modelBundle.oneTimeId != Model.Lifecycle.absentId)) = true)
    (hrealPresence : (core.option.Option.is_some theirBundle.bundle.one_time_prekey !=
      (theirBundle.one_time_prekey_id != serialization.ABSENT_ID)) = true)
    (htrace : trace rng = oracle.draws) :
    ∃ output,
      lifecycle.establish_initiator rngCore cryptoRng ourIdentity theirBundle rng =
        ok output ∧
      EstablishStepRefines trace dh K output
        (Model.Lifecycle.establishInitiator oracle modelIdentity modelBundle
          modelBundle.identityKey) := by
  obtain ⟨output, hcall, hstep⟩ := establish_initiator_presence_mismatch_step_refines
    rngCore cryptoRng trace dh K oracle ourIdentity theirBundle
      theirBundle.bundle.identity_key rng modelIdentity modelBundle
      modelBundle.identityKey hcmpSelf rfl hmodelPresence hrealPresence htrace
  refine ⟨output, ?_, hstep⟩
  simpa [lifecycle.establish_initiator] using hcall

/-! The successful establishment tail is an explicit composition seam.

The generated root constructs a Session only after the two aggregate
initialisers and the identity/public-key encodings have returned.  Keeping
this constructor relation separate makes the remaining root theorem consume
field-level evidence rather than a pre-built `SessionRefines` proposition. -/
theorem initiator_session_refines_of_constructors
    (dh : DhView) (K : Model.Braid.Kem)
    (sharedSecret : Model.Lifecycle.Key)
    (realTriple : tacenta_triple.State) (realBraid : tacenta_braid.Braid)
    (ratchetPrivate : tacenta_boundary.dh.PrivateKey)
    (identityAd : alloc.vec.Vec Std.U8)
    (ourIdentityPublic peerIdentityPublic ephemeralPublic ratchetPublic
      signedPrekeyPublic :
      tacenta_boundary.dh.PublicKeyBytes)
    (dhOut : Array Std.U8 32#usize)
    (kemCiphertext : alloc.vec.Vec Std.U8)
    (signedPrekeyId oneTimePrekeyId kemPrekeyId : Std.U32)
    (modelRatchetPrivate : Model.Lifecycle.Key)
    (modelIdentityAd modelOurIdentityPublic modelPeerIdentityPublic :
      Model.Lifecycle.Key)
    (modelEphemeralPublic : Model.Lifecycle.Key)
    (modelKemCiphertext : Model.Lifecycle.Key)
    (modelDhOut : Model.Lifecycle.Key)
    (modelSignedPrekeyId modelOneTimePrekeyId modelKemPrekeyId : Nat)
    (htriple : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realTriple
      (Model.Triple.initAlice sharedSecret
        (dh.publicKey ratchetPublic) (dh.publicKey signedPrekeyPublic)
        modelDhOut .tacenta))
    (hbraid : Tacenta.SessionUnitBraidT3.StateRefines K realBraid.state
      (Model.Braid.initAlice sharedSecret))
    (hprivate : dh.privateKey ratchetPrivate = modelRatchetPrivate)
    (had : vecOf identityAd = modelIdentityAd)
    (hour : dh.publicKey ourIdentityPublic = modelOurIdentityPublic)
    (hpeer : dh.publicKey peerIdentityPublic = modelPeerIdentityPublic)
    (hephemeral : dh.publicKey ephemeralPublic = modelEphemeralPublic)
    (hkem : vecOf kemCiphertext = modelKemCiphertext)
    (hdhOut : arrayOf dhOut = modelDhOut)
    (hsigned : signedPrekeyId.val = modelSignedPrekeyId)
    (hone : oneTimePrekeyId.val = modelOneTimePrekeyId)
    (hkemId : kemPrekeyId.val = modelKemPrekeyId) :
    SessionRefines dh K
      { triple := realTriple, braid := realBraid,
        ratchet_private := ratchetPrivate, identity_ad := identityAd,
        our_identity_public := ourIdentityPublic,
        peer_identity_public := peerIdentityPublic,
        pending_initial := some
          { ephemeral_public := ephemeralPublic,
            kem_ciphertext := kemCiphertext,
            signed_prekey_id := signedPrekeyId,
            one_time_prekey_id := oneTimePrekeyId,
            kem_prekey_id := kemPrekeyId },
        established_ephemeral := none }
      { triple := Model.Triple.initAlice sharedSecret
          (dh.publicKey ratchetPublic) (dh.publicKey signedPrekeyPublic)
          modelDhOut .tacenta,
        braid := Model.Braid.initAlice sharedSecret,
        ratchetPrivate := modelRatchetPrivate,
        identityAd := modelIdentityAd,
        ourIdentityPublic := modelOurIdentityPublic,
        peerIdentityPublic := modelPeerIdentityPublic,
        pendingInitial := some
          { ephemeralPublic := modelEphemeralPublic,
            kemCiphertext := modelKemCiphertext,
            signedPrekeyId := modelSignedPrekeyId,
            oneTimePrekeyId := modelOneTimePrekeyId,
            kemPrekeyId := modelKemPrekeyId },
        establishedEphemeral := none } := by
  constructor
  · simpa [hour, hpeer, hdhOut] using htriple
  · exact hbraid
  · exact hprivate
  · exact had
  · exact hour
  · exact hpeer
  · simp [pendingInitialOf, hephemeral, hkem, hsigned, hone, hkemId]
  · simp

/-! The first concrete successful-root composition.  This theorem is intentionally
    below the model relation: it proves that the generated public root follows
    the documented successful call order and constructs exactly one pending
    initial record.  Every opaque boundary result and every `Zeroizing` readback
    is an explicit premise.  The refinement theorem must additionally relate
    those results to the model oracle and discharge the session-field relation;
    this separation prevents a root theorem from hiding an unproved primitive
    contract behind a pre-built `SessionRefines` witness. -/
theorem establish_initiator_for_success_no_one_time_of_calls {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (expectedIdentity : tacenta_boundary.dh.PublicKeyBytes) (rng rng1 rng2 rng3 : R)
    (ephemeralBytes ratchetBytes kemSecret sharedSecretArray dhOutArray :
      Array Std.U8 32#usize)
    (ephemeralPrivate ratchetPrivate identityPrivate : tacenta_boundary.dh.PrivateKey)
    (kemCiphertext : alloc.vec.Vec Std.U8)
    (kemWrapped sharedWrapped dhOutWrapped : zeroize.Zeroizing (Array Std.U8 32#usize))
    (ephemeralPublic ratchetPublic ourIdentityPublic : tacenta_boundary.dh.PublicKeyBytes)
    (ratchetPublicBytes signedPrekeyBytes : Array Std.U8 32#usize)
    (sharedSlice : Slice Std.U8)
    (realTriple : tacenta_triple.State) (realBraid : tacenta_braid.Braid)
    (identityAd : alloc.vec.Vec Std.U8)
    (hcmp : core.cmp.PartialEq.ne.trait_default
      tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes
      theirBundle.bundle.identity_key expectedIdentity = ok false)
    (honeId : theirBundle.one_time_prekey_id = serialization.ABSENT_ID)
    (hone : theirBundle.bundle.one_time_prekey = none)
    (hidentityCanonical : is_canonical_key theirBundle.bundle.identity_key = ok true)
    (hsignedCanonical : is_canonical_key theirBundle.bundle.signed_prekey = ok true)
    (hverify : verify_bundle { theirBundle.bundle with one_time_prekey := none } =
      ok (.Ok ()))
    (hrandom : lifecycle.random_secret rngCore cryptoRng rng =
      ok (ephemeralBytes, rng1))
    (hephemeral : tacenta_boundary.dh.PrivateKey.from_bytes ephemeralBytes =
      ok ephemeralPrivate)
    (hkem : tacenta_boundary.kem.encapsulate rngCore cryptoRng
      (alloc.vec.Vec.deref theirBundle.bundle.kem_prekey) rng1 =
      ok (.Ok (kemCiphertext, kemSecret), rng2))
    (hkemNew : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) kemSecret =
      ok kemWrapped)
    (hkemDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) kemWrapped =
      ok kemSecret)
    (hidentityDh : lifecycle.Identity.dh_key ourIdentity = ok identityPrivate)
    (hshared : initiator_shared_secret identityPrivate ephemeralPrivate
      { theirBundle.bundle with one_time_prekey := none } kemSecret =
      ok (.Ok sharedSecretArray))
    (hsharedNew : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sharedSecretArray =
      ok sharedWrapped)
    (hsharedDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sharedWrapped =
      ok sharedSecretArray)
    (hrandomRatchet : lifecycle.random_secret rngCore cryptoRng rng2 =
      ok (ratchetBytes, rng3))
    (hratchet : tacenta_boundary.dh.PrivateKey.from_bytes ratchetBytes =
      ok ratchetPrivate)
    (hagreement : tacenta_boundary.dh.PrivateKey.agree ratchetPrivate
      theirBundle.bundle.signed_prekey = ok (some dhOutArray))
    (hdhOutNew : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) dhOutArray =
      ok dhOutWrapped)
    (hdhOutDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) dhOutWrapped =
      ok dhOutArray)
    (hsharedSlice : core.array.Array.index (core.ops.index.IndexSlice
      (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
      sharedSecretArray () = ok sharedSlice)
    (hratchetPublic : tacenta_boundary.dh.PrivateKey.public_key ratchetPrivate =
      ok ratchetPublic)
    (hratchetPublicBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes ratchetPublic =
      ok ratchetPublicBytes)
    (hsignedBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes
      theirBundle.bundle.signed_prekey = ok signedPrekeyBytes)
    (htriple : tacenta_triple.State.init_sender sharedSlice ratchetPublicBytes
      signedPrekeyBytes dhOutArray tacenta_ratchet.LabelSet.Tacenta = ok realTriple)
    (hbraid : tacenta_braid.Braid.initiator sharedSlice = ok realBraid)
    (hidentityPublic : lifecycle.Identity.public ourIdentity = ok ourIdentityPublic)
    (hidentityAd : lifecycle.identity_ad ourIdentityPublic
      theirBundle.bundle.identity_key = ok identityAd)
    (hephemeralPublic : tacenta_boundary.dh.PrivateKey.public_key ephemeralPrivate =
      ok ephemeralPublic) :
    lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity theirBundle
      expectedIdentity rng =
      ok (.Ok
        { triple := realTriple, braid := realBraid,
          ratchet_private := ratchetPrivate, identity_ad := identityAd,
          our_identity_public := ourIdentityPublic,
          peer_identity_public := theirBundle.bundle.identity_key,
          pending_initial := some
            { ephemeral_public := ephemeralPublic,
              kem_ciphertext := kemCiphertext,
              signed_prekey_id := theirBundle.signed_prekey_id,
              one_time_prekey_id := theirBundle.one_time_prekey_id,
              kem_prekey_id := theirBundle.kem_prekey_id },
          established_ephemeral := none }, rng3) := by
  unfold lifecycle.establish_initiator_for
  simp [hcmp, honeId, hidentityCanonical, hsignedCanonical, hverify, hrandom,
    hone,
    hephemeral, hkem, hkemNew, hkemDeref, hidentityDh, hshared, hsharedNew,
    hsharedDeref, hrandomRatchet, hratchet, hagreement, hdhOutNew, hdhOutDeref,
    hsharedSlice, hratchetPublic, hratchetPublicBytes, hsignedBytes, htriple,
    hbraid, hidentityPublic, hidentityAd, hephemeralPublic]

/-! The matching concrete success composition when the published bundle carries
    a curve one-time prekey.  The generated implementation folds that
    optional agreement into `initiator_shared_secret`; keeping the full bundle
    in the shared-secret premise makes the branch explicit and prevents the
    no-one-time proof from being mistaken for coverage of the consuming path. -/
theorem establish_initiator_for_success_with_one_time_of_calls {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (expectedIdentity : tacenta_boundary.dh.PublicKeyBytes) (rng rng1 rng2 rng3 : R)
    (oneTimePublic : tacenta_boundary.dh.PublicKeyBytes)
    (ephemeralBytes ratchetBytes kemSecret sharedSecretArray dhOutArray :
      Array Std.U8 32#usize)
    (ephemeralPrivate ratchetPrivate identityPrivate : tacenta_boundary.dh.PrivateKey)
    (kemCiphertext : alloc.vec.Vec Std.U8)
    (kemWrapped sharedWrapped dhOutWrapped : zeroize.Zeroizing (Array Std.U8 32#usize))
    (ephemeralPublic ratchetPublic ourIdentityPublic : tacenta_boundary.dh.PublicKeyBytes)
    (ratchetPublicBytes signedPrekeyBytes : Array Std.U8 32#usize)
    (sharedSlice : Slice Std.U8)
    (realTriple : tacenta_triple.State) (realBraid : tacenta_braid.Braid)
    (identityAd : alloc.vec.Vec Std.U8)
    (hcmp : core.cmp.PartialEq.ne.trait_default
      tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes
      theirBundle.bundle.identity_key expectedIdentity = ok false)
    (honeId : theirBundle.one_time_prekey_id ≠ serialization.ABSENT_ID)
    (hone : theirBundle.bundle.one_time_prekey = some oneTimePublic)
    (hidentityCanonical : is_canonical_key theirBundle.bundle.identity_key = ok true)
    (hsignedCanonical : is_canonical_key theirBundle.bundle.signed_prekey = ok true)
    (honeCanonical : is_canonical_key oneTimePublic = ok true)
    (hverify : verify_bundle { theirBundle.bundle with
      one_time_prekey := some oneTimePublic } = ok (.Ok ()))
    (hrandom : lifecycle.random_secret rngCore cryptoRng rng =
      ok (ephemeralBytes, rng1))
    (hephemeral : tacenta_boundary.dh.PrivateKey.from_bytes ephemeralBytes =
      ok ephemeralPrivate)
    (hkem : tacenta_boundary.kem.encapsulate rngCore cryptoRng
      (alloc.vec.Vec.deref theirBundle.bundle.kem_prekey) rng1 =
      ok (.Ok (kemCiphertext, kemSecret), rng2))
    (hkemNew : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) kemSecret =
      ok kemWrapped)
    (hkemDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) kemWrapped =
      ok kemSecret)
    (hidentityDh : lifecycle.Identity.dh_key ourIdentity = ok identityPrivate)
    (hshared : initiator_shared_secret identityPrivate ephemeralPrivate
      { theirBundle.bundle with one_time_prekey := some oneTimePublic } kemSecret =
      ok (.Ok sharedSecretArray))
    (hsharedNew : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sharedSecretArray =
      ok sharedWrapped)
    (hsharedDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sharedWrapped =
      ok sharedSecretArray)
    (hrandomRatchet : lifecycle.random_secret rngCore cryptoRng rng2 =
      ok (ratchetBytes, rng3))
    (hratchet : tacenta_boundary.dh.PrivateKey.from_bytes ratchetBytes =
      ok ratchetPrivate)
    (hagreement : tacenta_boundary.dh.PrivateKey.agree ratchetPrivate
      theirBundle.bundle.signed_prekey = ok (some dhOutArray))
    (hdhOutNew : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) dhOutArray =
      ok dhOutWrapped)
    (hdhOutDeref : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) dhOutWrapped =
      ok dhOutArray)
    (hsharedSlice : core.array.Array.index (core.ops.index.IndexSlice
      (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
      sharedSecretArray () = ok sharedSlice)
    (hratchetPublic : tacenta_boundary.dh.PrivateKey.public_key ratchetPrivate =
      ok ratchetPublic)
    (hratchetPublicBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes ratchetPublic =
      ok ratchetPublicBytes)
    (hsignedBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes
      theirBundle.bundle.signed_prekey = ok signedPrekeyBytes)
    (htriple : tacenta_triple.State.init_sender sharedSlice ratchetPublicBytes
      signedPrekeyBytes dhOutArray tacenta_ratchet.LabelSet.Tacenta = ok realTriple)
    (hbraid : tacenta_braid.Braid.initiator sharedSlice = ok realBraid)
    (hidentityPublic : lifecycle.Identity.public ourIdentity = ok ourIdentityPublic)
    (hidentityAd : lifecycle.identity_ad ourIdentityPublic
      theirBundle.bundle.identity_key = ok identityAd)
    (hephemeralPublic : tacenta_boundary.dh.PrivateKey.public_key ephemeralPrivate =
      ok ephemeralPublic) :
    lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity theirBundle
      expectedIdentity rng =
      ok (.Ok
        { triple := realTriple, braid := realBraid,
          ratchet_private := ratchetPrivate, identity_ad := identityAd,
          our_identity_public := ourIdentityPublic,
          peer_identity_public := theirBundle.bundle.identity_key,
          pending_initial := some
            { ephemeral_public := ephemeralPublic,
              kem_ciphertext := kemCiphertext,
              signed_prekey_id := theirBundle.signed_prekey_id,
              one_time_prekey_id := theirBundle.one_time_prekey_id,
              kem_prekey_id := theirBundle.kem_prekey_id },
          established_ephemeral := none }, rng3) := by
  unfold lifecycle.establish_initiator_for
  simp [hcmp, honeId, hone, hidentityCanonical, hsignedCanonical, honeCanonical,
    hverify,
    hrandom, hephemeral, hkem, hkemNew, hkemDeref, hidentityDh, hshared,
    hsharedNew, hsharedDeref, hrandomRatchet, hratchet, hagreement, hdhOutNew,
    hdhOutDeref, hsharedSlice, hratchetPublic, hratchetPublicBytes,
    hsignedBytes, htriple, hbraid, hidentityPublic, hidentityAd,
    hephemeralPublic]

/-! The corresponding KEM refusal is a complete public-root branch up to the
    boundary error.  It proves the important effect fact for this branch: the
    first ephemeral draw is retained in the returned RNG state, while no
    session is constructed and no later primitive is called. -/
theorem establish_initiator_for_kem_refusal_of_calls {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (expectedIdentity : tacenta_boundary.dh.PublicKeyBytes) (rng rngAfter : R)
    (ephemeralBytes : Array Std.U8 32#usize)
    (ephemeralPrivate : tacenta_boundary.dh.PrivateKey) (kemError : Unit)
    (hcmp : core.cmp.PartialEq.ne.trait_default
      tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes
      theirBundle.bundle.identity_key expectedIdentity = ok false)
    (honeId : theirBundle.one_time_prekey_id = serialization.ABSENT_ID)
    (hone : theirBundle.bundle.one_time_prekey = none)
    (hidentityCanonical : is_canonical_key theirBundle.bundle.identity_key = ok true)
    (hsignedCanonical : is_canonical_key theirBundle.bundle.signed_prekey = ok true)
    (hverify : verify_bundle { theirBundle.bundle with one_time_prekey := none } =
      ok (.Ok ()))
    (hrandom : lifecycle.random_secret rngCore cryptoRng rng =
      ok (ephemeralBytes, rngAfter))
    (hephemeral : tacenta_boundary.dh.PrivateKey.from_bytes ephemeralBytes =
      ok ephemeralPrivate)
    (hkem : tacenta_boundary.kem.encapsulate rngCore cryptoRng
      (alloc.vec.Vec.deref theirBundle.bundle.kem_prekey) rngAfter =
      ok (.Err kemError, rngAfter)) :
    lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity theirBundle
      expectedIdentity rng = ok (.Err lifecycle.Error.Kem, rngAfter) := by
  unfold lifecycle.establish_initiator_for
  simp [hcmp, honeId, hone, hidentityCanonical, hsignedCanonical, hverify, hrandom,
    hephemeral, hkem]

/-! Join the concrete KEM refusal call-order proof to the executable model.
    The model draw and encapsulation equations remain explicit: this theorem
    closes the refinement seam without pretending that a concrete KEM error is
    itself evidence for the model oracle transition. -/
theorem establish_initiator_kem_refusal_step_refines_of_root
    {R : Type} (trace : R → List Model.Lifecycle.Key)
    (dh : DhView) (K : Model.Braid.Kem)
    (oracle : Model.Lifecycle.Oracle)
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (expectedIdentity : tacenta_boundary.dh.PublicKeyBytes) (rng rngAfter : R)
    (modelIdentity : Model.Lifecycle.Identity)
    (modelBundle : Model.Lifecycle.Bundle)
    (modelExpectedIdentity : Model.Lifecycle.Key)
    (ephemeralPrivate : Model.Lifecycle.Key)
    (afterEphemeral afterKem : Model.Lifecycle.Oracle)
    (hreal : lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity
      theirBundle expectedIdentity rng =
      ok (.Err lifecycle.Error.Kem, rngAfter))
    (hmodelIdentity : modelBundle.identityKey = modelExpectedIdentity)
    (hOne : modelBundle.oneTimePrekey = none)
    (hOneId : modelBundle.oneTimeId = Model.Lifecycle.absentId)
    (hp : modelBundle.oneTimePrekey.isSome =
      (modelBundle.oneTimeId != Model.Lifecycle.absentId))
    (hv : oracle.identityValid modelBundle.identityKey = true)
    (hc : Model.Messages.canonicalKey modelBundle.identityKey = true)
    (hs : Model.Messages.canonicalKey modelBundle.signedPrekey = true)
    (ho : modelBundle.oneTimePrekey.all Model.Messages.canonicalKey = true)
    (hSignedSig : oracle.sigVerify modelBundle.identityKey
      (Model.PersistedState.SessionState.encodeEc modelBundle.signedPrekey)
      modelBundle.signedPrekeySig = true)
    (hKemSig : oracle.sigVerify modelBundle.identityKey
      (Model.Lifecycle.encodeKem modelBundle.kemPrekey)
      modelBundle.kemPrekeySig = true)
    (hDraw : Model.Lifecycle.random32 oracle =
      some (ephemeralPrivate, afterEphemeral))
    (hKem : Model.Lifecycle.kemEncapsulate afterEphemeral
      modelBundle.kemPrekey = some (none, afterKem))
    (htrace : trace rngAfter = afterKem.draws) :
    ∃ output,
      lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity
        theirBundle expectedIdentity rng = ok output ∧
      EstablishStepRefines trace dh K output
        (Model.Lifecycle.establishInitiator oracle modelIdentity modelBundle
          modelExpectedIdentity) := by
  have hmodel := Model.Lifecycle.establishInitiator_kem_refusal oracle
    afterEphemeral afterKem modelIdentity modelBundle modelExpectedIdentity
    ephemeralPrivate hmodelIdentity hOne hOneId hp hv hc hs ho hSignedSig hKemSig
    hDraw hKem
  refine ⟨(.Err lifecycle.Error.Kem, rngAfter), hreal, ?_⟩
  rw [hmodel]
  constructor
  · simp [EstablishResultRefines, refusalOf]
  · exact htrace

/-! Once the concrete call-order theorem and the model success theorem have
    been instantiated, this adapter composes them at the public refinement
    boundary.  Keeping the model equality and the constructor `SessionRefines`
    relation as separate arguments makes the remaining work measurable: it is
    the discharge of those relations from the named oracle/leaf contracts, not
    an unexamined `simp` over the public root. -/
theorem establish_initiator_for_success_step_refines_of_root_and_model
    {R : Type} (trace : R → List Model.Lifecycle.Key)
    (dh : DhView) (K : Model.Braid.Kem)
    (oracle : Model.Lifecycle.Oracle)
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (expectedIdentity : tacenta_boundary.dh.PublicKeyBytes) (rng rngAfter : R)
    (realSession : lifecycle.Session) (modelSession : Model.Lifecycle.Session)
    (modelIdentity : Model.Lifecycle.Identity)
    (modelBundle : Model.Lifecycle.Bundle)
    (modelExpectedIdentity : Model.Lifecycle.Key)
    (modelOracleAfter : Model.Lifecycle.Oracle)
    (hreal : lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity
      theirBundle expectedIdentity rng = ok (.Ok realSession, rngAfter))
    (hmodel : Model.Lifecycle.establishInitiator oracle modelIdentity modelBundle
      modelExpectedIdentity =
      { result := .ok modelSession, oracle := modelOracleAfter })
    (hrel : SessionRefines dh K realSession modelSession)
    (htrace : trace rngAfter = modelOracleAfter.draws) :
    ∃ output,
      lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity theirBundle
        expectedIdentity rng = ok output ∧
      EstablishStepRefines trace dh K output
        (Model.Lifecycle.establishInitiator oracle modelIdentity modelBundle
          modelExpectedIdentity) := by
  refine ⟨(.Ok realSession, rngAfter), hreal, ?_⟩
  rw [hmodel]
  constructor
  · simpa [EstablishResultRefines] using hrel
  · exact htrace

/-! The public wrapper fixes the expected identity to the bundle's advertised
    identity.  This small theorem keeps the distinction visible: a successful
    parameterised-root proof is not silently counted as a proof of the public
    root until this wrapper equation is discharged. -/
theorem establish_initiator_success_no_one_time_of_calls
    {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (expectedIdentity : tacenta_boundary.dh.PublicKeyBytes) (rng : R)
    (output : core.result.Result lifecycle.Session lifecycle.Error × R)
    (hexpected : expectedIdentity = theirBundle.bundle.identity_key)
    (hfor : lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity
      theirBundle expectedIdentity rng = ok output) :
    lifecycle.establish_initiator rngCore cryptoRng ourIdentity theirBundle rng =
      ok output := by
  simpa [lifecycle.establish_initiator, hexpected] using hfor

/-! Lift any parameterised-root refinement to the public initiator root once
    its expected identity is the bundle identity.  Branch theorems therefore
    cannot accidentally stop one wrapper short of the advertised API. -/
theorem establish_initiator_public_step_refines_of_for_step
    {R : Type} (trace : R → List Model.Lifecycle.Key)
    (dh : DhView) (K : Model.Braid.Kem)
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (expectedIdentity : tacenta_boundary.dh.PublicKeyBytes) (rng : R)
    (modelStep : Model.Lifecycle.EstablishStep)
    (hexpected : expectedIdentity = theirBundle.bundle.identity_key)
    (hstep : ∃ output,
      lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity
        theirBundle expectedIdentity rng = ok output ∧
      EstablishStepRefines trace dh K output modelStep) :
    ∃ output,
      lifecycle.establish_initiator rngCore cryptoRng ourIdentity theirBundle rng =
        ok output ∧ EstablishStepRefines trace dh K output modelStep := by
  obtain ⟨output, hfor, hrefines⟩ := hstep
  refine ⟨output, ?_, hrefines⟩
  simpa [lifecycle.establish_initiator, hexpected] using hfor

/-! Complete the successful initiator composition at the advertised public
    root.  The premises are intentionally the four reviewable seams rather
    than one opaque witness: concrete control flow, model transition, session
    fields, and the consumed-randomness trace. -/
theorem establish_initiator_success_step_refines_of_root_and_model
    {R : Type} (trace : R → List Model.Lifecycle.Key)
    (dh : DhView) (K : Model.Braid.Kem)
    (oracle : Model.Lifecycle.Oracle)
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (expectedIdentity : tacenta_boundary.dh.PublicKeyBytes) (rng rngAfter : R)
    (realSession : lifecycle.Session) (modelSession : Model.Lifecycle.Session)
    (modelIdentity : Model.Lifecycle.Identity)
    (modelBundle : Model.Lifecycle.Bundle)
    (modelExpectedIdentity : Model.Lifecycle.Key)
    (modelOracleAfter : Model.Lifecycle.Oracle)
    (hexpected : expectedIdentity = theirBundle.bundle.identity_key)
    (hreal : lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity
      theirBundle expectedIdentity rng = ok (.Ok realSession, rngAfter))
    (hmodel : Model.Lifecycle.establishInitiator oracle modelIdentity modelBundle
      modelExpectedIdentity =
      { result := .ok modelSession, oracle := modelOracleAfter })
    (hrel : SessionRefines dh K realSession modelSession)
    (htrace : trace rngAfter = modelOracleAfter.draws) :
    ∃ output,
      lifecycle.establish_initiator rngCore cryptoRng ourIdentity theirBundle rng =
        ok output ∧ EstablishStepRefines trace dh K output
        (Model.Lifecycle.establishInitiator oracle modelIdentity modelBundle
          modelExpectedIdentity) := by
  apply establish_initiator_public_step_refines_of_for_step trace dh K rngCore
    cryptoRng ourIdentity theirBundle expectedIdentity rng
    (Model.Lifecycle.establishInitiator oracle modelIdentity modelBundle
      modelExpectedIdentity) hexpected
  exact establish_initiator_for_success_step_refines_of_root_and_model trace dh K
    oracle rngCore cryptoRng ourIdentity theirBundle expectedIdentity rng rngAfter
    realSession modelSession modelIdentity modelBundle modelExpectedIdentity
    modelOracleAfter hreal hmodel hrel htrace

/-! Constructor-backed success composition for the no-curve-one-time-prekey
    branch.  The root equations remain explicit inputs, but the session
    relation is derived here from the generated Triple/Braid relations and
    each persisted field correspondence rather than supplied as a witness. -/
theorem establish_initiator_success_no_one_time_step_refines_of_constructors
    {R : Type} (trace : R → List Model.Lifecycle.Key)
    (dh : DhView) (K : Model.Braid.Kem)
    (oracle : Model.Lifecycle.Oracle)
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (ourIdentity : lifecycle.Identity) (theirBundle : lifecycle.PublishedBundle)
    (expectedIdentity : tacenta_boundary.dh.PublicKeyBytes) (rng rngAfter : R)
    (sharedSecret : Model.Lifecycle.Key)
    (realTriple : tacenta_triple.State) (realBraid : tacenta_braid.Braid)
    (ratchetPrivate : tacenta_boundary.dh.PrivateKey)
    (identityAd : alloc.vec.Vec Std.U8)
    (ourIdentityPublic peerIdentityPublic ephemeralPublic ratchetPublic
      signedPrekeyPublic : tacenta_boundary.dh.PublicKeyBytes)
    (dhOut : Array Std.U8 32#usize)
    (kemCiphertext : alloc.vec.Vec Std.U8)
    (signedPrekeyId oneTimePrekeyId kemPrekeyId : Std.U32)
    (modelRatchetPrivate : Model.Lifecycle.Key)
    (modelIdentityAd modelOurIdentityPublic modelPeerIdentityPublic :
      Model.Lifecycle.Key)
    (modelEphemeralPublic modelKemCiphertext modelDhOut : Model.Lifecycle.Key)
    (modelSignedPrekeyId modelOneTimePrekeyId modelKemPrekeyId : Nat)
    (modelIdentity : Model.Lifecycle.Identity)
    (modelBundle : Model.Lifecycle.Bundle)
    (modelExpectedIdentity : Model.Lifecycle.Key)
    (modelOracleAfter : Model.Lifecycle.Oracle)
    (hexpected : expectedIdentity = theirBundle.bundle.identity_key)
    (hreal : lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity
      theirBundle expectedIdentity rng =
      ok (.Ok
        { triple := realTriple, braid := realBraid,
          ratchet_private := ratchetPrivate, identity_ad := identityAd,
          our_identity_public := ourIdentityPublic,
          peer_identity_public := peerIdentityPublic,
          pending_initial := some
            { ephemeral_public := ephemeralPublic,
              kem_ciphertext := kemCiphertext,
              signed_prekey_id := signedPrekeyId,
              one_time_prekey_id := oneTimePrekeyId,
              kem_prekey_id := kemPrekeyId },
          established_ephemeral := none }, rngAfter))
    (hmodel : Model.Lifecycle.establishInitiator oracle modelIdentity modelBundle
      modelExpectedIdentity =
      { result := .ok
          { triple := Model.Triple.initAlice sharedSecret
              (dh.publicKey ratchetPublic) (dh.publicKey signedPrekeyPublic)
              modelDhOut .tacenta,
            braid := Model.Braid.initAlice sharedSecret,
            ratchetPrivate := modelRatchetPrivate,
            identityAd := modelIdentityAd,
            ourIdentityPublic := modelOurIdentityPublic,
            peerIdentityPublic := modelPeerIdentityPublic,
            pendingInitial := some
              { ephemeralPublic := modelEphemeralPublic,
                kemCiphertext := modelKemCiphertext,
                signedPrekeyId := modelSignedPrekeyId,
                oneTimePrekeyId := modelOneTimePrekeyId,
                kemPrekeyId := modelKemPrekeyId },
            establishedEphemeral := none },
        oracle := modelOracleAfter })
    (htriple : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realTriple
      (Model.Triple.initAlice sharedSecret
        (dh.publicKey ratchetPublic) (dh.publicKey signedPrekeyPublic)
        modelDhOut .tacenta))
    (hbraid : Tacenta.SessionUnitBraidT3.StateRefines K realBraid.state
      (Model.Braid.initAlice sharedSecret))
    (hprivate : dh.privateKey ratchetPrivate = modelRatchetPrivate)
    (had : vecOf identityAd = modelIdentityAd)
    (hour : dh.publicKey ourIdentityPublic = modelOurIdentityPublic)
    (hpeer : dh.publicKey peerIdentityPublic = modelPeerIdentityPublic)
    (hephemeral : dh.publicKey ephemeralPublic = modelEphemeralPublic)
    (hkem : vecOf kemCiphertext = modelKemCiphertext)
    (hdhOut : arrayOf dhOut = modelDhOut)
    (hsigned : signedPrekeyId.val = modelSignedPrekeyId)
    (hone : oneTimePrekeyId.val = modelOneTimePrekeyId)
    (hkemId : kemPrekeyId.val = modelKemPrekeyId)
    (htrace : trace rngAfter = modelOracleAfter.draws) :
    ∃ output,
      lifecycle.establish_initiator rngCore cryptoRng ourIdentity theirBundle rng =
        ok output ∧ EstablishStepRefines trace dh K output
        (Model.Lifecycle.establishInitiator oracle modelIdentity modelBundle
          modelExpectedIdentity) := by
  let realSession : lifecycle.Session :=
    { triple := realTriple, braid := realBraid,
      ratchet_private := ratchetPrivate, identity_ad := identityAd,
      our_identity_public := ourIdentityPublic,
      peer_identity_public := peerIdentityPublic,
      pending_initial := some
        { ephemeral_public := ephemeralPublic,
          kem_ciphertext := kemCiphertext,
          signed_prekey_id := signedPrekeyId,
          one_time_prekey_id := oneTimePrekeyId,
          kem_prekey_id := kemPrekeyId },
      established_ephemeral := none }
  let modelSession : Model.Lifecycle.Session :=
    { triple := Model.Triple.initAlice sharedSecret
        (dh.publicKey ratchetPublic) (dh.publicKey signedPrekeyPublic)
        modelDhOut .tacenta,
      braid := Model.Braid.initAlice sharedSecret,
      ratchetPrivate := modelRatchetPrivate,
      identityAd := modelIdentityAd,
      ourIdentityPublic := modelOurIdentityPublic,
      peerIdentityPublic := modelPeerIdentityPublic,
      pendingInitial := some
        { ephemeralPublic := modelEphemeralPublic,
          kemCiphertext := modelKemCiphertext,
          signedPrekeyId := modelSignedPrekeyId,
          oneTimePrekeyId := modelOneTimePrekeyId,
          kemPrekeyId := modelKemPrekeyId },
      establishedEphemeral := none }
  have hreal' : lifecycle.establish_initiator_for rngCore cryptoRng ourIdentity
      theirBundle expectedIdentity rng = ok (.Ok realSession, rngAfter) := by
    simpa [realSession] using hreal
  have hmodel' : Model.Lifecycle.establishInitiator oracle modelIdentity modelBundle
      modelExpectedIdentity = { result := .ok modelSession, oracle := modelOracleAfter } := by
    simpa [modelSession] using hmodel
  have hrel : SessionRefines dh K realSession modelSession := by
    simpa [realSession, modelSession] using
      (initiator_session_refines_of_constructors dh K sharedSecret realTriple realBraid
        ratchetPrivate identityAd ourIdentityPublic peerIdentityPublic ephemeralPublic
        ratchetPublic signedPrekeyPublic dhOut kemCiphertext signedPrekeyId
        oneTimePrekeyId kemPrekeyId modelRatchetPrivate modelIdentityAd
        modelOurIdentityPublic modelPeerIdentityPublic modelEphemeralPublic
        modelKemCiphertext modelDhOut modelSignedPrekeyId modelOneTimePrekeyId
        modelKemPrekeyId htriple hbraid hprivate had hour hpeer hephemeral hkem
        hdhOut hsigned hone hkemId)
  exact establish_initiator_success_step_refines_of_root_and_model trace dh K oracle
    rngCore cryptoRng ourIdentity theirBundle expectedIdentity rng rngAfter
    realSession modelSession modelIdentity modelBundle modelExpectedIdentity
    modelOracleAfter hexpected hreal' hmodel' hrel htrace

/-! Shared public-dispatch conclusion used by every `Session::decrypt` branch.
Keeping the concrete output and its refinement witness together gives the
initial dispatcher a single premise/result interface instead of six unrelated
existential signatures. -/
def PublicDecryptWitness {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R) : Prop :=
  ∃ output,
    lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
    StepRefines trace dh K output
      (Model.Lifecycle.decrypt view oracle model (sliceOf message))

/-! Encryption has the same public result/state/randomness boundary as
    decryption, but it is intentionally a separate witness.  The send side
    has different atomicity (Braid may commit on refusal and pending-initial
    changes only on a successful wire message), so a decrypt witness must not
    be reused to claim the `Session::encrypt` theorem. -/
def PublicEncryptWitness {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng : R) : Prop :=
  ∃ output,
    lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng = ok output ∧
    StepRefines trace dh K output
      (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext))

structure InitialDispatchContext {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R) where
  hrel : SessionRefines dh K real model
  htrace : trace rng = oracle.draws
  htype : serialization.message_type message =
    ok (some serialization.MessageType.Initial)

theorem initial_decode_cases (message : Slice Std.U8) :
    (∃ reason, tacenta_wire.decode_initial message =
      ok (core.result.Result.Err reason)) ∨
    (∃ decoded, tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded)) := by
  by_cases h : ∃ reason, tacenta_wire.decode_initial message =
      ok (core.result.Result.Err reason)
  · exact Or.inl h
  · right
    obtain ⟨result, hresult⟩ :=
      Std.WP.spec_imp_exists (Tacenta.SessionUnitWireInitialT3.decode_initial_refines message)
    cases result with
    | Err reason => exact False.elim (h ⟨reason, hresult.1⟩)
    | Ok decoded => exact ⟨decoded, hresult.1⟩

theorem initial_established_ephemeral_cases (real : lifecycle.Session) :
    real.established_ephemeral = none ∨
      ∃ established, real.established_ephemeral = some established := by
  cases h : real.established_ephemeral with
  | none => exact Or.inl rfl
  | some established => exact Or.inr ⟨established, rfl⟩

theorem initial_vec_equality_cases (left right : alloc.vec.Vec Std.U8) :
    vecOf left = vecOf right ∨ vecOf left ≠ vecOf right := by
  exact Classical.em _

inductive InitialDispatchRoute {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R) : Type where
  | decodeRefusal
      (reason : tacenta_wire.DecodeError)
      (hdecode : tacenta_wire.decode_initial message =
        ok (core.result.Result.Err reason))
      (w : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng) :
      InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng
  | noEstablished
      (decoded : tacenta_wire.DecodedInitial)
      (hdecode : tacenta_wire.decode_initial message =
        ok (core.result.Result.Ok decoded))
      (hnone : real.established_ephemeral = none)
      (w : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng) :
      InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng
  | ephemeralMismatch
      (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial)
      (hdecode : tacenta_wire.decode_initial message =
        ok (core.result.Result.Ok decoded))
      (hestablished : real.established_ephemeral = some established)
      (hmismatch : vecOf established ≠ vecOf decoded.ephemeral)
      (w : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng) :
      InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng
  | identityMismatch
      (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial)
      (hdecode : tacenta_wire.decode_initial message =
        ok (core.result.Result.Ok decoded))
      (hestablished : real.established_ephemeral = some established)
      (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
        established.deref decoded.ephemeral.deref = ok true)
      (hmismatch : vecOf decoded.identity ≠
        Model.PersistedState.SessionState.encodeEc
          (dh.publicKey real.peer_identity_public))
      (w : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng) :
      InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng
  | repeatRefusal
      (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial)
      (realReason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R)
      (hdecode : tacenta_wire.decode_initial message =
        ok (core.result.Result.Ok decoded))
      (hestablished : real.established_ephemeral = some established)
      (hidentity : vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc
          (dh.publicKey real.peer_identity_public))
      (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
        established.deref decoded.ephemeral.deref = ok true)
      (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
        (alloc.vec.Vec.deref decoded.message) rng =
          ok (.Err realReason, next, rngNext))
      (w : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng) :
      InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng
  | repeatSuccess
      (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial)
      (plaintext : alloc.vec.Vec Std.U8) (realNext : lifecycle.Session)
      (rngNext : R) (hdecode : tacenta_wire.decode_initial message =
        ok (core.result.Result.Ok decoded))
      (hestablished : real.established_ephemeral = some established)
      (hidentity : vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc
          (dh.publicKey real.peer_identity_public))
      (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
        established.deref decoded.ephemeral.deref = ok true)
      (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
        (alloc.vec.Vec.deref decoded.message) rng =
          ok (.Ok plaintext, realNext, rngNext))
      (w : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng) :
      InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng

theorem initial_dispatch_join
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (route : InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng) :
    PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng := by
  cases route with
  | decodeRefusal _ _ w => exact w
  | noEstablished _ _ _ w => exact w
  | ephemeralMismatch _ _ _ _ _ w => exact w
  | identityMismatch _ _ _ _ _ _ w => exact w
  | repeatRefusal _ _ _ _ _ _ _ _ _ _ w => exact w
  | repeatSuccess _ _ _ _ _ _ _ _ _ _ w => exact w

/-- Final composition step for the initial dispatcher.  The selector supplies
the typed route after proving the generated control-flow premises; this lemma
connects that route to the common public witness. -/
theorem initial_dispatch_select_and_join
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (route : InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng) :
    PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng :=
  initial_dispatch_join route

def initial_dispatch_decode_refusal_route
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rngCore cryptoRng trace dh K view oracle real model message rng)
    (reason : tacenta_wire.DecodeError)
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Err reason))
    (w : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng) :
    InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng := by
  exact .decodeRefusal reason hdecode w

def initial_dispatch_no_established_route
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rngCore cryptoRng trace dh K view oracle real model message rng)
    (decoded : tacenta_wire.DecodedInitial)
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hnone : real.established_ephemeral = none)
    (w : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng) :
    InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng :=
  .noEstablished decoded hdecode hnone w

def initial_dispatch_ephemeral_mismatch_route
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rngCore cryptoRng trace dh K view oracle real model message rng)
    (established : alloc.vec.Vec Std.U8)
    (decoded : tacenta_wire.DecodedInitial)
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hmismatch : vecOf established ≠ vecOf decoded.ephemeral)
    (w : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng) :
    InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng :=
  .ephemeralMismatch established decoded hdecode hestablished hmismatch w

def initial_dispatch_identity_mismatch_route
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rngCore cryptoRng trace dh K view oracle real model message rng)
    (established : alloc.vec.Vec Std.U8)
    (decoded : tacenta_wire.DecodedInitial)
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok true)
    (hmismatch : vecOf decoded.identity ≠
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public))
    (w : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng) :
    InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng :=
  .identityMismatch established decoded hdecode hestablished hsameAgreement hmismatch w

def initial_dispatch_repeat_refusal_route
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rngCore cryptoRng trace dh K view oracle real model message rng)
    (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial)
    (realReason : lifecycle.Error) (modelReason : Model.Lifecycle.Refusal)
    (modelNext : Model.Lifecycle.Session) (rngNext : R)
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hephemeral : vecOf established = vecOf decoded.ephemeral)
    (hidentity : vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public))
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok true)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref decoded.message) rng =
      ok (.Err realReason, real, rngNext))
    (hmodelStep : Model.Lifecycle.decryptRatchet view oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage =
      { session := modelNext, result := .error modelReason, oracle := oracle })
    (w : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng) :
    InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng :=
  .repeatRefusal established decoded realReason real rngNext hdecode hestablished hidentity
    hsameAgreement hinner w

def initial_dispatch_repeat_success_route
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rngCore cryptoRng trace dh K view oracle real model message rng)
    (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial)
    (plaintext : alloc.vec.Vec Std.U8) (modelPlaintext : Bytes)
    (realNext : lifecycle.Session) (modelNext : Model.Lifecycle.Session) (rngNext : R)
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hephemeral : vecOf established = vecOf decoded.ephemeral)
    (hidentity : vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public))
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok true)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref decoded.message) rng =
      ok (.Ok plaintext, realNext, rngNext))
    (hmodelStep : Model.Lifecycle.decryptRatchet view oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage =
      { session := modelNext, result := .ok modelPlaintext, oracle := oracle })
    (hbytes : vecOf plaintext = modelPlaintext)
    (w : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng) :
    InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng :=
  .repeatSuccess established decoded plaintext realNext rngNext hdecode hestablished
    hidentity hsameAgreement hinner w

/-! A refusal branch must retain the wrapper relation as well as the inner
state relation.  The dispatcher uses this small lemma after the model-side
atomicity theorem has established that its refusal session is unchanged. -/

theorem step_refines_unchanged_pending_initial
    {R : Type} {trace : R → List Model.Lifecycle.Key}
    {dh : DhView} {K : Model.Braid.Kem}
    {realResult : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error}
    {realSession : lifecycle.Session} {rng : R}
    {model : Model.Lifecycle.Session}
    {modelStep : Model.Lifecycle.Step Bytes}
    (hstep : StepRefines trace dh K
      (realResult, realSession, rng) modelStep)
    (hmodel : modelStep.session = model) :
    realSession.pending_initial.map (pendingInitialOf dh) = model.pendingInitial := by
  rw [← hmodel]
  exact hstep.session.pendingInitial

theorem step_refines_cleared_pending_initial
    {R : Type} {trace : R → List Model.Lifecycle.Key}
    {dh : DhView} {K : Model.Braid.Kem}
    {realResult : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error}
    {realSession : lifecycle.Session} {rng : R}
    {modelStep : Model.Lifecycle.Step Bytes}
    (hstep : StepRefines trace dh K
      (realResult, realSession, rng) modelStep)
    (hmodel : modelStep.session.pendingInitial = none) :
    realSession.pending_initial.map (pendingInitialOf dh) = none := by
  rw [← hmodel]
  exact hstep.session.pendingInitial

theorem decrypt_ratchet_step_refines_unchanged_pending_initial
    {R : Type} {trace : R → List Model.Lifecycle.Key}
    {dh : DhView} {K : Model.Braid.Kem}
    {realResult : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error}
    {realSession : lifecycle.Session} {rng : R}
    (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (reason : Model.Lifecycle.Refusal)
    (hstep : StepRefines trace dh K
      (realResult, realSession, rng)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)))
    (herror : (Model.Lifecycle.decryptRatchet view oracle model
      (sliceOf message)).result = .error reason) :
    realSession.pending_initial.map (pendingInitialOf dh) = model.pendingInitial := by
  apply step_refines_unchanged_pending_initial hstep
  exact Model.Lifecycle.decryptRatchet_refusal_keeps_session
    view oracle model (sliceOf message) reason herror

theorem decrypt_step_refines_cleared_pending_initial
    {R : Type} {trace : R → List Model.Lifecycle.Key}
    {dh : DhView} {K : Model.Braid.Kem}
    {realResult : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error}
    {realSession : lifecycle.Session} {rng : R}
    (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (plaintext : Bytes)
    (hstep : StepRefines trace dh K
      (realResult, realSession, rng)
      (Model.Lifecycle.decrypt view oracle model (sliceOf message)))
    (hsuccess : (Model.Lifecycle.decrypt view oracle model
      (sliceOf message)).result = .ok plaintext) :
    realSession.pending_initial.map (pendingInitialOf dh) = none := by
  have hmodelPending := Model.Lifecycle.decrypt_success_clears_pending
    view oracle model (sliceOf message) plaintext hsuccess
  exact step_refines_cleared_pending_initial hstep hmodelPending

theorem decrypt_step_refines_unchanged_pending_initial
    {R : Type} {trace : R → List Model.Lifecycle.Key}
    {dh : DhView} {K : Model.Braid.Kem}
    {realResult : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error}
    {realSession : lifecycle.Session} {rng : R}
    (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (reason : Model.Lifecycle.Refusal)
    (hstep : StepRefines trace dh K
      (realResult, realSession, rng)
      (Model.Lifecycle.decrypt view oracle model (sliceOf message)))
    (herror : (Model.Lifecycle.decrypt view oracle model
      (sliceOf message)).result = .error reason) :
    realSession.pending_initial.map (pendingInitialOf dh) = model.pendingInitial := by
  apply step_refines_unchanged_pending_initial hstep
  exact Model.Lifecycle.decrypt_refusal_keeps_session
    view oracle model (sliceOf message) reason herror

/-- Public decrypt refusals preserve the pending-initial relation.  This is
the dispatcher-level atomicity consequence shared by decoder, repeat-check,
and inner-ratchet refusal branches. -/
theorem public_decrypt_witness_refusal_preserves_pending
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (reason : Model.Lifecycle.Refusal)
    (hw : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model
      message rng)
    (hresult : (Model.Lifecycle.decrypt view oracle model (sliceOf message)).result
      = .error reason) :
    ∃ output, lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      output.2.1.pending_initial.map (pendingInitialOf dh) = model.pendingInitial := by
  obtain ⟨output, hreal, hstep⟩ := hw
  refine ⟨output, hreal, ?_⟩
  exact decrypt_step_refines_unchanged_pending_initial view oracle model message
    reason hstep hresult

theorem public_decrypt_witness_success_clears_pending
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (plaintext : Bytes)
    (hw : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model
      message rng)
    (hresult : (Model.Lifecycle.decrypt view oracle model (sliceOf message)).result
      = .ok plaintext) :
    ∃ output, lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      output.2.1.pending_initial.map (pendingInitialOf dh) = none := by
  obtain ⟨output, hreal, hstep⟩ := hw
  refine ⟨output, hreal, ?_⟩
  exact decrypt_step_refines_cleared_pending_initial view oracle model message
    plaintext hstep hresult

theorem public_decrypt_witness_atomicity_cases
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (hw : PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model
      message rng) :
    (∃ reason output,
      (Model.Lifecycle.decrypt view oracle model (sliceOf message)).result
        = .error reason ∧
      lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      output.2.1.pending_initial.map (pendingInitialOf dh) = model.pendingInitial) ∨
    (∃ plaintext output,
      (Model.Lifecycle.decrypt view oracle model (sliceOf message)).result
        = .ok plaintext ∧
      lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      output.2.1.pending_initial.map (pendingInitialOf dh) = none) := by
  cases hresult : (Model.Lifecycle.decrypt view oracle model (sliceOf message)).result with
  | error reason =>
      obtain ⟨output, hreal, hpending⟩ :=
        public_decrypt_witness_refusal_preserves_pending rngCore cryptoRng trace dh K
          view oracle real model message rng reason hw hresult
      exact Or.inl ⟨reason, output, rfl, hreal, hpending⟩
  | ok plaintext =>
      obtain ⟨output, hreal, hpending⟩ :=
        public_decrypt_witness_success_clears_pending rngCore cryptoRng trace dh K
          view oracle real model message rng plaintext hw hresult
      exact Or.inr ⟨plaintext, output, rfl, hreal, hpending⟩


/-! The repeated-initial dispatcher has a refusal arm and a success arm.  Keep
the refusal-side pending relation named separately so the eventual split of
`decrypt_initial_repeat_step_refines` cannot accidentally reuse the success
clearance lemma. -/
theorem decrypt_initial_repeat_refusal_preserves_pending
    {R : Type} {trace : R → List Model.Lifecycle.Key}
    {dh : DhView} {K : Model.Braid.Kem}
    {realResult : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error}
    {realSession : lifecycle.Session} {rng : R}
    (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (reason : Model.Lifecycle.Refusal)
    (hstep : StepRefines trace dh K
      (realResult, realSession, rng)
      (Model.Lifecycle.decrypt view oracle model (sliceOf message)))
    (herror : (Model.Lifecycle.decrypt view oracle model
      (sliceOf message)).result = .error reason) :
    realSession.pending_initial.map (pendingInitialOf dh) = model.pendingInitial :=
  decrypt_step_refines_unchanged_pending_initial view oracle model message reason
    hstep herror

theorem decrypt_initial_repeat_success_clears_pending
    {R : Type} {trace : R → List Model.Lifecycle.Key}
    {dh : DhView} {K : Model.Braid.Kem}
    {realResult : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error}
    {realSession : lifecycle.Session} {rng : R}
    (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (plaintext : Bytes)
    (hstep : StepRefines trace dh K
      (realResult, realSession, rng)
      (Model.Lifecycle.decrypt view oracle model (sliceOf message)))
    (hsuccess : (Model.Lifecycle.decrypt view oracle model
      (sliceOf message)).result = .ok plaintext) :
    realSession.pending_initial.map (pendingInitialOf dh) = none :=
  decrypt_step_refines_cleared_pending_initial view oracle model message plaintext
    hstep hsuccess

/-! ## Lifecycle observations -/


theorem initial_dispatch_select_atomicity
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (route : InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng) :
    (∃ reason output,
      (Model.Lifecycle.decrypt view oracle model (sliceOf message)).result =
        .error reason ∧
      lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      output.2.1.pending_initial.map (pendingInitialOf dh) = model.pendingInitial) ∨
    (∃ plaintext output,
      (Model.Lifecycle.decrypt view oracle model (sliceOf message)).result =
        .ok plaintext ∧
      lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      output.2.1.pending_initial.map (pendingInitialOf dh) = none) :=
  public_decrypt_witness_atomicity_cases rngCore cryptoRng trace dh K view oracle
    real model message rng (initial_dispatch_select_and_join route)

/-- Equality on translated byte vectors returns exactly list equality. -/
theorem vec_u8_eq_refines (left right : alloc.vec.Vec Std.U8) :
    alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8 left right
      ⦃ fun equal => equal = true ↔ left.val = right.val ⦄ := by
  rcases left with ⟨left, hleft⟩
  rcases right with ⟨right, hright⟩
  induction left generalizing right with
  | nil =>
      cases right <;>
        simp [alloc.vec.partial_eq.PartialEqVec.eq, alloc.vec.Vec.length,
          pure, WP.spec_ok]
      | cons x xs ih =>
      cases right with
      | nil =>
          simp [alloc.vec.partial_eq.PartialEqVec.eq, alloc.vec.Vec.length,
            WP.spec_ok]
      | cons y ys =>
          by_cases hxy : x = y
          · subst y
            simp [alloc.vec.partial_eq.PartialEqVec.eq, alloc.vec.Vec.length,
              pure]
            have hxs : xs.length ≤ Usize.max :=
              Nat.le_trans (Nat.le_succ xs.length) hleft
            have hys : ys.length ≤ Usize.max :=
              Nat.le_trans (Nat.le_succ ys.length) hright
            simpa [alloc.vec.partial_eq.PartialEqVec.eq, alloc.vec.Vec.length] using
              (ih hxs ys hys)
          · simp [alloc.vec.partial_eq.PartialEqVec.eq, alloc.vec.Vec.length,
              pure, WP.spec_ok, hxy]

theorem vec_u8_eq_result_cases (left right : alloc.vec.Vec Std.U8) :
    ∃ equal,
      alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8 left right =
        ok equal ∧
      (equal = true → left.val = right.val) ∧
      (equal = false → left.val ≠ right.val) := by
  obtain ⟨equal, hcall, hpost⟩ :=
    Std.WP.spec_imp_exists (vec_u8_eq_refines left right)
  cases equal with
  | false =>
      refine ⟨false, hcall, ?_, ?_⟩
      · intro h
        cases h
      · intro _
        intro hEq
        have hfalse : false = true := hpost.mpr hEq
        cases hfalse
  | true =>
      refine ⟨true, hcall, ?_, ?_⟩
      · intro _
        exact hpost.mp rfl
      · intro hEq
        cases hEq

def messageTypeOf : serialization.MessageType → Model.Lifecycle.MessageType
  | .Ratchet => .ratchet
  | .Initial => .initial

theorem vecOf_injective : Function.Injective vecOf := by
  intro left right h
  cases left with
  | mk left hleft =>
      cases right with
      | mk right hright =>
          simp only [vecOf] at h
          have hl : left = right :=
            List.map_injective_iff.mpr
              (fun _ _ => Tacenta.SessionUnitBraidT3.u8_injective) h
          subst right
          rfl

theorem u8_eq_u8_iff (left right : Std.U8) :
    Tacenta.SessionUnitBraidT3.u8 left =
      Tacenta.SessionUnitBraidT3.u8 right ↔ left.val = right.val := by
  constructor
  · intro h
    exact congrArg UScalar.val (Tacenta.SessionUnitBraidT3.u8_injective h)
  · intro h
    simp [Tacenta.SessionUnitBraidT3.u8, h]

theorem lifecycle_version_agrees :
    Model.Messages.version = Tacenta.SessionUnitBraidT3.u8 tacenta_wire.VERSION := by
  symm
  simpa [Tacenta.SessionUnitWireT3.byteOf,
    Tacenta.SessionUnitBraidT3.u8] using
      Tacenta.SessionUnitWireT3.byteOf_version

theorem lifecycle_type_ratchet_agrees :
    Model.Messages.typeRatchet =
      Tacenta.SessionUnitBraidT3.u8 tacenta_wire.TYPE_RATCHET := by
  symm
  simpa [Tacenta.SessionUnitWireT3.byteOf,
    Tacenta.SessionUnitBraidT3.u8] using
      Tacenta.SessionUnitWireT3.byteOf_type_ratchet

theorem lifecycle_type_initial_agrees :
    Model.Messages.typeInitial =
      Tacenta.SessionUnitBraidT3.u8 tacenta_wire.TYPE_INITIAL := by
  simp [Model.Messages.typeInitial, tacenta_wire.TYPE_INITIAL,
    Tacenta.SessionUnitBraidT3.u8]

/-- Encoding an opaque curve public key produces the model's exact EncodeEC
bytes under the shared public-key representation. -/
theorem encode_ec_refines (dh : DhView) (codec : DhCodecOf dh)
    (publicKey : tacenta_boundary.dh.PublicKeyBytes) :
    ∃ encoded, encode_ec publicKey = ok encoded ∧
      vecOf encoded =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey publicKey) := by
  obtain ⟨bytes, hbytes, hview⟩ := codec.asBytes publicKey
  have hspec := Tacenta.SessionUnitSessionT1.encode_ec_spec bytes
  obtain ⟨encoded, hencoded, hvalue⟩ := Std.WP.spec_imp_exists hspec
  refine ⟨encoded, ?_, ?_⟩
  · simp [encode_ec, hbytes, hencoded]
  · rw [Model.PersistedState.SessionState.encodeEc, ← hview]
    simp [vecOf, arrayOf, hvalue, tacenta_session.ENCODE_EC_CURVE25519,
      Model.Messages.ecCurveByte, Tacenta.SessionUnitBraidT3.u8]

/-! The lifecycle identity binding is the session associated-data binding with
the two curve encodings made explicit.  This is a small but necessary bridge
for establishment: the final Session relation must account for the bytes
stored by the generated `identity_ad` wrapper, not merely assume them. -/
theorem identity_ad_refines {dh : DhView} (codec : DhCodecOf dh)
    (initiator responder : tacenta_boundary.dh.PublicKeyBytes) :
    ∃ output,
      lifecycle.identity_ad initiator responder = ok output ∧
      vecOf output = Model.SessionEstablishment.associatedData
        (Model.PersistedState.SessionState.encodeEc (dh.publicKey initiator))
        (Model.PersistedState.SessionState.encodeEc (dh.publicKey responder)) := by
  obtain ⟨initiatorEncoded, hInitiatorEncoded, hInitiatorEncodedVal⟩ :=
    encode_ec_refines dh codec initiator
  obtain ⟨responderEncoded, hResponderEncoded, hResponderEncodedVal⟩ :=
    encode_ec_refines dh codec responder
  obtain ⟨initiatorBytes, _, hInitiatorBytesView⟩ := codec.asBytes initiator
  obtain ⟨responderBytes, _, hResponderBytesView⟩ := codec.asBytes responder
  have hInitiatorPublicLen : (dh.publicKey initiator).length = 32 := by
    rw [← hInitiatorBytesView]
    simp [arrayOf]
  have hResponderPublicLen : (dh.publicKey responder).length = 32 := by
    rw [← hResponderBytesView]
    simp [arrayOf]
  have hInitiatorLen : initiatorEncoded.val.length = 33 := by
    have h := congrArg List.length hInitiatorEncodedVal
    simp [vecOf, Model.PersistedState.SessionState.encodeEc,
      Tacenta.SessionUnitBraidT3.u8, hInitiatorPublicLen] at h
    exact h
  have hResponderLen : responderEncoded.val.length = 33 := by
    have h := congrArg List.length hResponderEncodedVal
    simp [vecOf, Model.PersistedState.SessionState.encodeEc,
      Tacenta.SessionUnitBraidT3.u8, hResponderPublicLen] at h
    exact h
  have hbound : initiatorEncoded.deref.val.length + responderEncoded.deref.val.length ≤
      Usize.max := by
    simp only [hInitiatorLen, hResponderLen, alloc.vec.Vec.deref]
    have := Tacenta.SessionUnitSessionT1.small_le_usize_max (n := 66) (by omega)
    omega
  unfold lifecycle.identity_ad
  rw [hInitiatorEncoded, hResponderEncoded]
  obtain ⟨output, hOutput, hOutputVal⟩ :=
    Std.WP.spec_imp_exists (Tacenta.SessionUnitSessionT1.associated_data_spec
      initiatorEncoded.deref responderEncoded.deref hbound)
  refine ⟨output, ?_, ?_⟩
  · exact hOutput
  · have hOutputVal' := congrArg
      (List.map Tacenta.SessionUnitBraidT3.u8) hOutputVal
    change List.map Tacenta.SessionUnitBraidT3.u8 output.val =
      Model.PersistedState.SessionState.encodeEc (dh.publicKey initiator) ++
        Model.PersistedState.SessionState.encodeEc (dh.publicKey responder)
    rw [← hInitiatorEncodedVal, ← hResponderEncodedVal]
    simpa [vecOf, alloc.vec.Vec.deref] using hOutputVal'

/-- The candidate ratchet private key's public bytes are exactly the model
oracle's public-key result.  Receive uses both opaque calls in sequence, so the
bridge records both call equations rather than assuming a byte value after the
fact. -/
theorem candidate_public_bytes_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (oracle : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (codec : DhCodecOf dh) (privateKey : tacenta_boundary.dh.PrivateKey) :
    ∃ publicKey bytes,
      tacenta_boundary.dh.PrivateKey.public_key privateKey = ok publicKey ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes publicKey = ok bytes ∧
      arrayOf bytes = oracle.dhPublic (dh.privateKey privateKey) := by
  obtain ⟨publicKey, hpublic, hpublicValue⟩ := oracleOf.dhPublic privateKey
  obtain ⟨bytes, hbytes, hbytesValue⟩ := codec.asBytes publicKey
  refine ⟨publicKey, bytes, hpublic, hbytes, ?_⟩
  rw [hbytesValue, hpublicValue]

/-- The two concrete checks for an accepted repeated-initial wrapper agree
with the model predicate.  The result exposes the exact translated call
equations needed by the public decrypt proof. -/
theorem repeated_initial_checks_refine (oracle : Model.Lifecycle.Oracle)
    (dh : DhView) (codec : DhCodecOf dh)
    (K : Model.Braid.Kem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (established : alloc.vec.Vec Std.U8)
    (decoded : tacenta_wire.DecodedInitial)
    (hrel : SessionRefines dh K real model)
    (hestablished : real.established_ephemeral = some established)
    (hephemeral : vecOf established = vecOf decoded.ephemeral)
    (hidentity : vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public))
    (hmodelSame : Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
      (vecOf established) (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val) = true) :
    ∃ encoded,
      encode_ec real.peer_identity_public = ok encoded ∧
      alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8
        established decoded.ephemeral = ok true ∧
      alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8
        decoded.identity encoded = ok true ∧
      Model.Lifecycle.repeatedInitial oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded) = true := by
  obtain ⟨encoded, hencoded, hencodedValue⟩ :=
    encode_ec_refines dh codec real.peer_identity_public
  have hephemeralEq : established = decoded.ephemeral :=
    vecOf_injective hephemeral
  have hidentityEq : decoded.identity = encoded := by
    apply vecOf_injective
    exact hidentity.trans hencodedValue.symm
  obtain ⟨ephemeralEqual, hephemeralCall, hephemeralPost⟩ :=
    Std.WP.spec_imp_exists (vec_u8_eq_refines established decoded.ephemeral)
  have hephemeralTrue : ephemeralEqual = true :=
    hephemeralPost.2 (congrArg (fun value => value.val) hephemeralEq)
  rw [hephemeralTrue] at hephemeralCall
  obtain ⟨identityEqual, hidentityCall, hidentityPost⟩ :=
    Std.WP.spec_imp_exists (vec_u8_eq_refines decoded.identity encoded)
  have hidentityTrue : identityEqual = true :=
    hidentityPost.2 (congrArg (fun value => value.val) hidentityEq)
  rw [hidentityTrue] at hidentityCall
  have hmodelEstablished :
      model.establishedEphemeral = some (vecOf established) := by
    have h := hrel.establishedEphemeral
    rw [hestablished] at h
    exact h.symm
  have hmodelRepeat : Model.Lifecycle.repeatedInitial oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded) = true := by
    apply (Model.Lifecycle.repeatedInitial_iff oracle _ _).2
    refine ⟨vecOf established, hmodelEstablished, hmodelSame, ?_⟩
    · change Tacenta.SessionUnitWireT3.bytesOf decoded.identity.val =
        Model.PersistedState.SessionState.encodeEc model.peerIdentityPublic
      rw [wire_bytesOf_eq_vecOf, ← hrel.peerIdentityPublic]
      exact hidentity
  exact ⟨encoded, hencoded, hephemeralCall, hidentityCall, hmodelRepeat⟩

/-! The agreement-class variant deliberately omits the byte-equality check.
    The generated wrapper asks the DH agreement oracle, so a byte-different
    encoding that lands in the same successful agreement class must follow the
    repeat path as well. -/
theorem repeated_initial_agreement_checks_refine (oracle : Model.Lifecycle.Oracle)
    (dh : DhView) (codec : DhCodecOf dh)
    (K : Model.Braid.Kem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (established : alloc.vec.Vec Std.U8)
    (decoded : tacenta_wire.DecodedInitial)
    (hrel : SessionRefines dh K real model)
    (hestablished : real.established_ephemeral = some established)
    (hidentity : vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public))
    (hmodelSame : Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
      (vecOf established) (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val) = true) :
    ∃ encoded,
      encode_ec real.peer_identity_public = ok encoded ∧
      alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8
        decoded.identity encoded = ok true ∧
      Model.Lifecycle.repeatedInitial oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded) = true := by
  obtain ⟨encoded, hencoded, hencodedValue⟩ :=
    encode_ec_refines dh codec real.peer_identity_public
  have hidentityEq : decoded.identity = encoded := by
    apply vecOf_injective
    exact hidentity.trans hencodedValue.symm
  obtain ⟨identityEqual, hidentityCall, hidentityPost⟩ :=
    Std.WP.spec_imp_exists (vec_u8_eq_refines decoded.identity encoded)
  have hidentityTrue : identityEqual = true :=
    hidentityPost.2 (congrArg (fun value => value.val) hidentityEq)
  rw [hidentityTrue] at hidentityCall
  have hmodelEstablished :
      model.establishedEphemeral = some (vecOf established) := by
    have h := hrel.establishedEphemeral
    rw [hestablished] at h
    exact h.symm
  have hmodelRepeat : Model.Lifecycle.repeatedInitial oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded) = true := by
    apply (Model.Lifecycle.repeatedInitial_iff oracle _ _).2
    refine ⟨vecOf established, hmodelEstablished, hmodelSame, ?_⟩
    change Tacenta.SessionUnitWireT3.bytesOf decoded.identity.val =
      Model.PersistedState.SessionState.encodeEc model.peerIdentityPublic
    rw [wire_bytesOf_eq_vecOf, ← hrel.peerIdentityPublic]
    exact hidentity
  exact ⟨encoded, hencoded, hidentityCall, hmodelRepeat⟩

theorem message_type_refines (bytes : Slice Std.U8) :
    serialization.message_type bytes ⦃ fun result =>
      result.map messageTypeOf = Model.Lifecycle.messageType (sliceOf bytes) ⦄ := by
  rcases bytes with ⟨bytes, hbound⟩
  cases bytes with
  | nil =>
      simp [serialization.message_type, sliceOf, Model.Lifecycle.messageType]
  | cons first rest =>
      cases rest with
      | nil =>
          simp [serialization.message_type, sliceOf, Model.Lifecycle.messageType]
      | cons second tail =>
          unfold serialization.message_type
          step*
          all_goals
            simp_all [sliceOf, Model.Lifecycle.messageType, messageTypeOf,
              lifecycle_version_agrees, lifecycle_type_ratchet_agrees,
              lifecycle_type_initial_agrees, u8_eq_u8_iff]

theorem message_type_refines_initial (bytes : Slice Std.U8)
    (htype : serialization.message_type bytes =
      ok (some serialization.MessageType.Initial)) :
    Model.Lifecycle.messageType (sliceOf bytes) = some .initial := by
  have h := message_type_refines bytes
  rw [htype] at h
  simpa [messageTypeOf] using h.symm

theorem message_type_refines_noninitial (bytes : Slice Std.U8)
    (realType : Option serialization.MessageType)
    (htype : serialization.message_type bytes = ok realType)
    (hnotInitial : realType ≠ some .Initial) :
    Model.Lifecycle.messageType (sliceOf bytes) ≠ some .initial := by
  intro hmodel
  have h := message_type_refines bytes
  rw [htype] at h
  have hinitial : Option.map messageTypeOf realType = some .initial :=
    h.trans hmodel
  cases realType with
  | none => simp at hinitial
  | some ty =>
      cases ty with
      | Ratchet => simp [messageTypeOf] at hinitial
      | Initial => exact hnotInitial rfl

theorem message_type_refines_none (bytes : Slice Std.U8)
    (htype : serialization.message_type bytes = ok none) :
    Model.Lifecycle.messageType (sliceOf bytes) = none := by
  have h := message_type_refines bytes
  rw [htype] at h
  simpa using h.symm

theorem message_type_refines_ratchet (bytes : Slice Std.U8)
    (htype : serialization.message_type bytes =
      ok (some serialization.MessageType.Ratchet)) :
    Model.Lifecycle.messageType (sliceOf bytes) = some .ratchet := by
  have h := message_type_refines bytes
  rw [htype] at h
  simpa [messageTypeOf] using h.symm

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

/-! Public encryption boundary for the terminal route.  This is the first
    constructor of the separate `Session::encrypt` composition; the remaining
    sendAgreement, Triple, composite and AEAD routes must be supplied by the
    send-side dispatcher rather than inferred from decrypt. -/
theorem public_encrypt_terminal_witness {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng : R)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hfailed : Model.Lifecycle.agreementFailed model = true) :
    PublicEncryptWitness rngCore cryptoRng trace dh K view oracle real model
      plaintext rng := by
  exact encrypt_terminal_guard_step_refines rngCore cryptoRng trace dh K view oracle
    real model plaintext rng hrel htrace hfailed

/-! The translated Braid send theorem returns an existential model random value.
The lifecycle oracle has a stricter interface: states which do not sample
randomness must use the unchanged oracle, while sampling states must consume
its head.  These two adapters keep that distinction explicit at the public
`Session::encrypt` boundary. -/
theorem braid_send_model_result_of_no_draw
    {R : Type} {K : Model.Braid.Kem}
    (oracle : Model.Lifecycle.Oracle) (model : Model.Braid.BraidState)
    (hkem : oracle.braidKem = K)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output)
    (realNext : tacenta_braid.Braid)
    (hnoDraw : Model.Lifecycle.braidSendNeedsDraw model = false)
    (hpost : ∃ rand,
      (∀ modelMessage,
        (Model.Braid.send K rand model).1 = some modelMessage →
          Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage) ∧
      realEpoch.val = (Model.Braid.send K rand model).2.2.2.epoch - 1 ∧
      Tacenta.SessionUnitBraidT3.OptionOutputRefines realOutput
        (Model.Braid.send K rand model).2.2.1 ∧
      Tacenta.SessionUnitBraidT3.StateRefines K realNext.state
        (Model.Braid.send K rand model).2.2.2) :
    ∃ (modelMessage : Option Model.Braid.Msg) (modelEpoch : Nat)
      (modelOutput : Option Model.Braid.Output)
      (modelNext : Model.Braid.BraidState),
      Model.Lifecycle.sendAgreement oracle model =
          some ((modelMessage, modelEpoch, modelOutput, modelNext), oracle) ∧
      (∀ decoded,
        modelMessage = some decoded →
          Tacenta.SessionUnitBraidT3.MsgRefines realMessage decoded) ∧
      realEpoch.val = modelEpoch ∧
      Tacenta.SessionUnitBraidT3.OptionOutputRefines realOutput modelOutput ∧
      Tacenta.SessionUnitBraidT3.StateRefines K realNext.state modelNext := by
  obtain ⟨rand, hmsg, hepoch, hout, hnext⟩ := hpost
  let sent := Model.Braid.send K rand model
  have hsent0 : Model.Braid.send K 0 model = sent :=
    (Model.Lifecycle.braid_send_random_irrelevant_of_no_draw K model hnoDraw rand).symm
  have horacle : Model.Lifecycle.sendAgreement oracle model =
      some (sent, oracle) := by
    rw [Model.Lifecycle.sendAgreement_no_draw oracle model hnoDraw]
    simpa [sent, hkem] using hsent0
  rcases hsent : sent with ⟨modelMessage, modelEpoch, modelOutput, modelNext⟩
  have htuple : Model.Braid.send K rand model =
      (modelMessage, modelEpoch, modelOutput, modelNext) := by
    simpa [sent] using hsent
  have hsendEpoch : (Model.Braid.send K rand model).2.1 =
      (Model.Braid.send K rand model).2.2.2.epoch - 1 := by
    cases model <;> rfl
  rw [htuple] at hmsg hepoch hout hnext
  rw [htuple] at hsendEpoch
  rw [hsent] at horacle
  have hsendEpoch' : modelEpoch = modelNext.epoch - 1 := by
    simpa only [Prod.fst, Prod.snd] using hsendEpoch
  refine ⟨modelMessage, modelEpoch, modelOutput, modelNext, ?_, ?_, ?_, ?_, ?_⟩
  · exact horacle
  · intro decoded hdecoded
    exact hmsg decoded hdecoded
  · exact hepoch.trans hsendEpoch'.symm
  · exact hout
  · exact hnext

theorem braid_send_model_result_of_draw
    {R : Type} {K : Model.Braid.Kem}
    (trace : R → List Model.Lifecycle.Key)
    (oracle : Model.Lifecycle.Oracle) (model : Model.Braid.BraidState)
    (hkem : oracle.braidKem = K)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output)
    (realNext : tacenta_braid.Braid) (rng rngNext : R)
    (htrace : trace rng = oracle.draws)
    (hdraw : ∃ draws rest, draws.length = Model.Lifecycle.braidSendDrawCount model ∧
      trace rng = draws ++ rest ∧ trace rngNext = rest)
    (hneedsDraw : Model.Lifecycle.braidSendNeedsDraw model = true)
    (hpost : ∀ draws rest, draws.length = Model.Lifecycle.braidSendDrawCount model →
      trace rng = draws ++ rest → ∃ rand,
      rand = Model.Lifecycle.braidRandomness draws.flatten ∧
      (∀ modelMessage,
        (Model.Braid.send K rand model).1 = some modelMessage →
          Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage) ∧
      realEpoch.val = (Model.Braid.send K rand model).2.2.2.epoch - 1 ∧
      Tacenta.SessionUnitBraidT3.OptionOutputRefines realOutput
        (Model.Braid.send K rand model).2.2.1 ∧
      Tacenta.SessionUnitBraidT3.StateRefines K realNext.state
        (Model.Braid.send K rand model).2.2.2) :
    ∃ (draws : List Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key)
      (modelMessage : Option Model.Braid.Msg) (modelEpoch : Nat)
      (modelOutput : Option Model.Braid.Output)
      (modelNext : Model.Braid.BraidState),
      draws.length = Model.Lifecycle.braidSendDrawCount model ∧
      trace rng = draws ++ rest ∧ trace rngNext = rest ∧
      Model.Lifecycle.sendAgreement oracle model =
        some ((modelMessage, modelEpoch, modelOutput, modelNext),
          { oracle with draws := rest }) ∧
      (∀ decoded,
        modelMessage = some decoded →
          Tacenta.SessionUnitBraidT3.MsgRefines realMessage decoded) ∧
      realEpoch.val = modelEpoch ∧
      Tacenta.SessionUnitBraidT3.OptionOutputRefines realOutput modelOutput ∧
      Tacenta.SessionUnitBraidT3.StateRefines K realNext.state modelNext := by
  obtain ⟨draws, rest, hcount, hhead, htail⟩ := hdraw
  obtain ⟨rand, hrand', hmsg, hepoch, hout, hnext⟩ := hpost draws rest hcount hhead
  have horacle : oracle.draws = draws ++ rest := htrace.symm.trans hhead
  let sent := Model.Braid.send K rand model
  have hsentDraw : Model.Lifecycle.sendAgreement oracle model =
      some (sent, { oracle with draws := rest }) := by
    rw [Model.Lifecycle.sendAgreement_draws oracle model draws rest hneedsDraw hcount horacle]
    simp [sent, hrand', hkem]
  rcases hsent : sent with ⟨modelMessage, modelEpoch, modelOutput, modelNext⟩
  have htuple : Model.Braid.send K rand model =
      (modelMessage, modelEpoch, modelOutput, modelNext) := by
    simpa [sent] using hsent
  have hsendEpoch : (Model.Braid.send K rand model).2.1 =
      (Model.Braid.send K rand model).2.2.2.epoch - 1 := by
    cases model <;> rfl
  rw [htuple] at hmsg hepoch hout hnext
  rw [htuple] at hsendEpoch
  rw [hsent] at hsentDraw
  have hsendEpoch' : modelEpoch = modelNext.epoch - 1 := by
    simpa only [Prod.fst, Prod.snd] using hsendEpoch
  refine ⟨draws, rest, modelMessage, modelEpoch, modelOutput, modelNext,
    hcount, hhead, htail, ?_, ?_, ?_, ?_, ?_⟩
  · exact hsentDraw
  · intro decoded hdecoded
    exact hmsg decoded hdecoded
  · exact hepoch.trans hsendEpoch'.symm
  · exact hout
  · exact hnext

/-! The public encrypt composition must obtain its Braid result from the
    generated call itself.  This bundle names the T3 semantic contracts and
    the T1 totality/clone contracts consumed by `Braid.send_refines`; the
    adapter below then inverts the exact generated `Ok` result rather than
    accepting a separately chosen model successor. -/
structure BraidSendRefinementContracts {R : Type}
    (rc : rand_core_1.RngCore R) (K : Model.Braid.Kem) : Prop where
  hka : Tacenta.SessionUnitBraidT3.KemAgreesFor K
  hea : Tacenta.SessionUnitBraidT3.ErasureAgrees
  hmac : Tacenta.SessionUnitT3.HmacAgrees
  hkdf : Tacenta.SessionUnitT3.HkdfAgrees
  header : Tacenta.SessionUnitBraidT1.KeyPairHeaderTotal
  ekVector : Tacenta.SessionUnitBraidT1.KeyPairEkVectorTotal
  ct1Len : Tacenta.SessionUnitBraidT1.Ct1LenTotal
  ct2Len : Tacenta.SessionUnitBraidT1.Ct2LenTotal
  kemClone : Tacenta.SessionUnitBraidT3.KemCloneAgrees
  erasureClone : Tacenta.SessionUnitBraidT3.ErasureCloneAgrees
  encoderClone : Tacenta.SessionUnitBraidT1.EncoderCloneTotal
  decoderClone : Tacenta.SessionUnitBraidT1.DecoderCloneTotal
  keyPairClone : Tacenta.SessionUnitBraidT1.KeyPairCloneTotal
  encapsStateClone : Tacenta.SessionUnitBraidT1.EncapsStateCloneTotal
  zeroizingArray : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip
  arrayZeroize : Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal
  rangeFullIndex : Tacenta.SessionUnitBraidT1.RangeFullIndexTotal
  rng : Tacenta.SessionUnitBraidT1.RngTotal rc
  keyPairGenerate : Tacenta.SessionUnitBraidT1.KeyPairGenerateTotal
  encoderNew : Tacenta.SessionUnitBraidT1.EncoderNewTotal
  encoderNext : Tacenta.SessionUnitBraidT1.EncoderNextChunkTotal
  encapsulate1 : Tacenta.SessionUnitBraidT1.Encapsulate1Total

theorem braid_send_result_of_contracts
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {K : Model.Braid.Kem}
    (contracts : BraidSendRefinementContracts rc K)
    (self : tacenta_braid.Braid) (rng : R) :
    ∃ result rngNext,
      tacenta_braid.Braid.send rc crc self rng = ok (result, rngNext) := by
  obtain ⟨result, hresult⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitBraidT1.Braid.send_no_panic rc crc contracts.rng
      contracts.encoderClone contracts.decoderClone contracts.keyPairClone
      contracts.encapsStateClone contracts.keyPairGenerate contracts.header
      contracts.hmac.total contracts.encoderNew contracts.encoderNext contracts.hkdf.total
      contracts.encapsulate1 contracts.zeroizingArray contracts.arrayZeroize
      contracts.rangeFullIndex self rng)
  rcases result with ⟨result, rngNext⟩
  exact ⟨result, rngNext, hresult.1⟩

theorem braid_send_post_of_contracts
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {K : Model.Braid.Kem}
    (contracts : BraidSendRefinementContracts rc K)
    (self : tacenta_braid.Braid) (rng : R)
    {model : Model.Braid.BraidState}
    (hrel : Tacenta.SessionUnitBraidT3.StateRefines K self.state model)
    (hlive : Tacenta.SessionUnitBraidT3.EncodersLive model)
    {realMessage : tacenta_braid.Msg} {realEpoch : Std.U64}
    {realOutput : Option tacenta_braid.Output}
    {realNext : tacenta_braid.Braid} {rngNext : R}
    (hsendReal : tacenta_braid.Braid.send rc crc self rng =
      ok ((realMessage, realEpoch, realOutput, realNext), rngNext)) :
    ∃ rand,
      (∀ modelMessage,
        (Model.Braid.send K rand model).1 = some modelMessage →
          Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage) ∧
      realEpoch.val = (Model.Braid.send K rand model).2.2.2.epoch - 1 ∧
      Tacenta.SessionUnitBraidT3.OptionOutputRefines realOutput
        (Model.Braid.send K rand model).2.2.1 ∧
      Tacenta.SessionUnitBraidT3.StateRefines K realNext.state
        (Model.Braid.send K rand model).2.2.2 := by
  have hKdf := braid_kdf_contracts_of_session contracts.hmac contracts.hkdf
  obtain ⟨result, hcall, hpost⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitBraidT3.Braid.send_refines
      contracts.hka contracts.hea hKdf.1 hKdf.2
      contracts.header contracts.ekVector contracts.ct1Len contracts.ct2Len
      contracts.kemClone contracts.erasureClone contracts.encoderClone
      contracts.decoderClone contracts.keyPairClone contracts.encapsStateClone
      contracts.zeroizingArray contracts.arrayZeroize contracts.rangeFullIndex
      rc crc contracts.rng self rng hrel hlive)
  have heq : result = ((realMessage, realEpoch, realOutput, realNext), rngNext) := by
    exact Result.ok.inj (hcall.symm.trans hsendReal)
  cases heq
  exact hpost

/-! The corresponding Triple adapter keeps the exact generated candidate-send
    result tied to the `SessionUnitTripleT3.send_refines_discharged` postcondition.
    The model-side bounds are explicit because they are the preconditions of
    the sparse ratchet's finite-store theorem, not facts that can be inferred
    from the outer Session relation. -/
structure TripleSendRefinementContracts : Prop where
  hmac : Tacenta.SessionUnitT3.HmacAgrees
  hkdf : Tacenta.SessionUnitT3.HkdfAgrees
  zeroizing : Tacenta.SessionUnitT3.ZeroizingRoundTrips
  ratchetRemove : Tacenta.SessionUnitT1.RemoveSkippedAtTotal
  spqrZeroizing96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96
  spqrZeroizing64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64
  vecRetain : Tacenta.SessionUnitSpqrT3.VecRetainAgrees
  vecRetainTotal : Tacenta.SessionUnitSpqrT1.VecRetainTotal
  spqrRemove : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees
  spqrZeroize : Tacenta.SessionUnitSpqrT1.ZeroizeTotal
  optionClone : Tacenta.SessionUnitSpqrT1.OptionCloneTotal

theorem triple_send_post_of_contracts
    {s : tacenta_triple.State} {m : Model.Triple.State}
    (contracts : TripleSendRefinementContracts)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (sendingEpoch : Std.U64) (output : Option tacenta_spqr.Output)
    (hroom : m.postQuantum.chains.length + 1 < Usize.max)
    (hcb : ∀ p ∈ m.postQuantum.chains,
      p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ m.postQuantum.skipped,
      sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, output = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hepoch : m.postQuantum.epoch + 1 < Std.U64.max)
    (hcounter : ∀ p ∈ m.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max)
    {sent : core.result.Result (tacenta_triple.Header × Array Std.U8 32#usize)
      tacenta_triple.TripleError}
    {candidate : tacenta_triple.State}
    (hsend : tacenta_triple.State.send s sendingEpoch output =
      ok (sent, candidate)) :
    ((∀ hdr mk, sent = core.result.Result.Ok (hdr, mk) →
        ∃ m' mh key,
          Model.Triple.send m sendingEpoch.val
            (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) =
            some (m', mh, key) ∧
          Tacenta.SessionUnitTripleT3.StateRefines
            Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
            candidate m' ∧ Tacenta.SessionUnitTripleT3.TripleHeaderR hdr mh ∧
            Tacenta.SessionUnitTripleT3.keyOf mk = key) ∧
      (∀ e, sent = core.result.Result.Err e →
        ∃ reason, tripleSendRefusalOfReal e = some reason ∧
          Model.Triple.sendDetailed m sendingEpoch.val
            (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) = .error reason)) := by
  obtain ⟨result, hcall, hpost⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitTripleT3.send_refines_discharged
      contracts.hmac contracts.hkdf contracts.zeroizing contracts.ratchetRemove
      contracts.spqrZeroizing96 contracts.spqrZeroizing64 contracts.vecRetain
      contracts.vecRetainTotal contracts.spqrRemove contracts.spqrZeroize contracts.optionClone
      hrel sendingEpoch output hroom hcb hsb hnewb hepoch hcounter)
  have heq : result = (sent, candidate) := by
    exact Result.ok.inj (hcall.symm.trans hsend)
  cases heq
  simpa only [Prod.fst, Prod.snd, tripleSendRefusalOfReal] using hpost

theorem triple_send_candidate_post_of_contracts
    {s : tacenta_triple.State} {m : Model.Triple.State}
    (contracts : TripleSendRefinementContracts)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (sendingEpoch : Std.U64) (output : Option tacenta_spqr.Output)
    (hroom : m.postQuantum.chains.length + 1 < Usize.max)
    (hcb : ∀ p ∈ m.postQuantum.chains,
      p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ m.postQuantum.skipped,
      sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, output = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hepoch : m.postQuantum.epoch + 1 < Std.U64.max)
    (hcounter : ∀ p ∈ m.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max)
    {sent : core.result.Result (tacenta_triple.Header × Array Std.U8 32#usize)
      tacenta_triple.TripleError}
    {candidate : tacenta_triple.State}
    (hsend : lifecycle.send_candidate s sendingEpoch output =
      ok (candidate, sent)) :
    ((∀ hdr mk, sent = core.result.Result.Ok (hdr, mk) →
        ∃ m' mh key,
          Model.Triple.send m sendingEpoch.val
            (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) =
            some (m', mh, key) ∧
          Tacenta.SessionUnitTripleT3.StateRefines
            Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
            candidate m' ∧ Tacenta.SessionUnitTripleT3.TripleHeaderR hdr mh ∧
            Tacenta.SessionUnitTripleT3.keyOf mk = key) ∧
      (∀ e, sent = core.result.Result.Err e →
        ∃ reason, tripleSendRefusalOfReal e = some reason ∧
          Model.Triple.sendDetailed m sendingEpoch.val
            (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) = .error reason)) := by
  unfold lifecycle.send_candidate at hsend
  rw [Tacenta.SessionUnitTripleT1.triple_state_clone_id contracts.optionClone s] at hsend
  cases output with
  | none =>
      have hstate : tacenta_triple.State.send s sendingEpoch none =
          ok (sent, candidate) := by
        cases hresult : tacenta_triple.State.send s sendingEpoch none with
        | fail error => simp [hresult] at hsend
        | div => simp [hresult] at hsend
        | ok value =>
            rcases value with ⟨sent', candidate'⟩
            have heq : (candidate', sent') = (candidate, sent) := by
              simpa [hresult] using hsend
            cases heq
            simpa [hresult]
      apply triple_send_post_of_contracts contracts hrel sendingEpoch none hroom hcb hsb hnewb
        hepoch hcounter
      exact hstate
  | some output =>
      have hstate : tacenta_triple.State.send s sendingEpoch (some output) =
          ok (sent, candidate) := by
        cases hresult : tacenta_triple.State.send s sendingEpoch (some output) with
        | fail error => simp [hresult] at hsend
        | div => simp [hresult] at hsend
        | ok value =>
            rcases value with ⟨sent', candidate'⟩
            have heq : (candidate', sent') = (candidate, sent) := by
              simpa [hresult] using hsend
            cases heq
            simpa [hresult]
      apply triple_send_post_of_contracts contracts hrel sendingEpoch (some output) hroom hcb hsb
        hnewb hepoch hcounter
      exact hstate

/-! The generated candidate result plus the contract-backed Triple adapter can
    also produce the model's detailed success result.  This is the success
    counterpart to the refusal bridge: the model successor, header and key
    are existentially tied to the same concrete candidate and output. -/
theorem triple_success_evidence_of_exact_candidate_and_contracts
    {s : tacenta_triple.State} {m : Model.Triple.State}
    (contracts : TripleSendRefinementContracts)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (sendingEpoch : Std.U64) (output : Option tacenta_spqr.Output)
    (hroom : m.postQuantum.chains.length + 1 < Usize.max)
    (hcb : ∀ p ∈ m.postQuantum.chains,
      p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ m.postQuantum.skipped,
      sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, output = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hepoch : m.postQuantum.epoch + 1 < Std.U64.max)
    (hcounter : ∀ p ∈ m.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max)
    {candidate : tacenta_triple.State}
    {header : tacenta_triple.Header} {mk : Array Std.U8 32#usize}
    (hsend : lifecycle.send_candidate s sendingEpoch output =
      ok (candidate, .Ok (header, mk))) :
    ∃ modelCandidate modelHeader modelMk,
      Model.Triple.sendDetailed m sendingEpoch.val
        (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) =
          .ok (modelCandidate, modelHeader, modelMk) ∧
      Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        candidate modelCandidate ∧
      Tacenta.SessionUnitTripleT3.TripleHeaderR header modelHeader ∧
      Tacenta.SessionUnitTripleT3.keyOf mk = modelMk := by
  have hpost := triple_send_candidate_post_of_contracts contracts hrel sendingEpoch output
    hroom hcb hsb hnewb hepoch hcounter hsend
  obtain ⟨modelCandidate, modelHeader, modelMk, hsome, hstate, hheader, hkey⟩ :=
    hpost.1 header mk (by rfl)
  have hdetail := (Model.Triple.sendDetailed_ok_iff m sendingEpoch.val
    (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf)
    (modelCandidate, modelHeader, modelMk)).2 hsome
  exact ⟨modelCandidate, modelHeader, modelMk, hdetail, hstate, hheader, hkey⟩

/-! The refusal counterpart preserves the exact model refusal and derives its
    correspondence with the implementation error from the two leaf proofs. -/
theorem triple_refusal_evidence_of_exact_candidate_and_contracts
    {s : tacenta_triple.State} {m : Model.Triple.State}
    (contracts : TripleSendRefinementContracts)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (sendingEpoch : Std.U64) (output : Option tacenta_spqr.Output)
    (hroom : m.postQuantum.chains.length + 1 < Usize.max)
    (hcb : ∀ p ∈ m.postQuantum.chains,
      p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ m.postQuantum.skipped,
      sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, output = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hepoch : m.postQuantum.epoch + 1 < Std.U64.max)
    (hcounter : ∀ p ∈ m.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max)
    {candidate : tacenta_triple.State} {reason : tacenta_triple.TripleError}
    (hsend : lifecycle.send_candidate s sendingEpoch output =
      ok (candidate, .Err reason)) :
    ∃ modelReason,
      Model.Triple.sendDetailed m sendingEpoch.val
        (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) = .error modelReason ∧
      tripleSendRefusalOfReal reason = some modelReason := by
  have hpost := triple_send_candidate_post_of_contracts contracts hrel sendingEpoch output
    hroom hcb hsb hnewb hepoch hcounter hsend
  obtain ⟨modelReason, hreason, hdetail⟩ := hpost.2 reason (by rfl)
  exact ⟨modelReason, hdetail, hreason⟩

/-- `decrypt_ratchet` has the same terminal agreement guard as `encrypt`: it
returns the exact public refusal without decoding attacker-controlled bytes or
changing state/randomness. -/
theorem decrypt_ratchet_terminal_guard_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hfailed : Model.Lifecycle.agreementFailed model = true) :
    lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
        ok (.Err lifecycle.Error.AgreementFailed, real, rng) ∧
      StepRefines trace dh K
        (.Err lifecycle.Error.AgreementFailed, real, rng)
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  have hm : model.braid = .failed :=
    (Model.Lifecycle.agreementFailed_iff model).mp hfailed
  have hbraid := braid_failed_refines K real.braid model.braid hrel.braid
  have hbf : Model.Lifecycle.braidFailed model.braid = true :=
    (Model.Lifecycle.braidFailed_iff model.braid).2 hm
  rw [hbf] at hbraid
  have hreal : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err lifecycle.Error.AgreementFailed, real, rng) := by
    unfold lifecycle.Session.decrypt_ratchet
    rw [hbraid]
    simp
  have hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session := model, result := .error .agreementFailed, oracle := oracle } := by
    simp [Model.Lifecycle.decryptRatchet, hfailed]
  refine ⟨hreal, ?_⟩
  rw [hmodel]
  exact ⟨rfl, hrel, htrace⟩

theorem decrypt_ratchet_terminal_guard_atomicity {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (dh : DhView) (K : Model.Braid.Kem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (hrel : SessionRefines dh K real model)
    (hfailed : Model.Lifecycle.agreementFailed model = true) :
    lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err lifecycle.Error.AgreementFailed, real, rng) := by
  have hm : model.braid = .failed :=
    (Model.Lifecycle.agreementFailed_iff model).mp hfailed
  have hbraid := braid_failed_refines K real.braid model.braid hrel.braid
  have hbf : Model.Lifecycle.braidFailed model.braid = true :=
    (Model.Lifecycle.braidFailed_iff model.braid).2 hm
  rw [hbf] at hbraid
  unfold lifecycle.Session.decrypt_ratchet
  rw [hbraid]
  simp

/-- A rejected ratchet-message encoding is an atomic Session refusal.  The
decoder-specific relation is kept explicit so the later decoder theorem must
identify the exact reason, rather than merely showing that both sides fail. -/
theorem decrypt_ratchet_decode_refusal_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (realReason : tacenta_wire.DecodeError)
    (modelReason : Model.Messages.DecodeRefusal)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Err realReason))
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .error modelReason)
    (hreason : decodeRefusalOf realReason = modelReason) :
    lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
        ok (.Err (.Decode realReason), real, rng) ∧
      StepRefines trace dh K
        (.Err (.Decode realReason), real, rng)
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  have hrealReady := braid_failed_refines K real.braid model.braid hrel.braid
  have hmodelReady : Model.Lifecycle.braidFailed model.braid = false := by
    cases hb : model.braid <;>
      simp [Model.Lifecycle.agreementFailed, Model.Lifecycle.braidFailed, hb] at hready ⊢
  rw [hmodelReady] at hrealReady
  have hreal : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Decode realReason), real, rng) := by
    unfold lifecycle.Session.decrypt_ratchet
    simp [hrealReady, hdecodeReal]
  have hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session := model, result := .error (.decode modelReason), oracle := oracle } := by
    simp [Model.Lifecycle.decryptRatchet, hready, hdecodeModel]
  refine ⟨hreal, ?_⟩
  rw [hmodel]
  exact ⟨congrArg Model.Lifecycle.Refusal.decode hreason, hrel, htrace⟩

theorem decrypt_ratchet_decode_refusal_atomicity {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (dh : DhView) (K : Model.Braid.Kem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (realReason : tacenta_wire.DecodeError)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Err realReason)) :
    lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Decode realReason), real, rng) := by
  have hrealReady := braid_failed_refines K real.braid model.braid hrel.braid
  have hmodelReady : Model.Lifecycle.braidFailed model.braid = false := by
    cases hb : model.braid <;>
      simp [Model.Lifecycle.agreementFailed, Model.Lifecycle.braidFailed, hb] at hready ⊢
  rw [hmodelReady] at hrealReady
  unfold lifecycle.Session.decrypt_ratchet
  simp [hrealReady, hdecodeReal]

/-- A concrete ratchet-message decoder refusal determines the model's detailed
refusal without an agreement premise at the Session boundary. -/
theorem decrypt_ratchet_decode_refusal_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (realReason : tacenta_wire.DecodeError)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Err realReason)) :
    lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
        ok (.Err (.Decode realReason), real, rng) ∧
      StepRefines trace dh K
        (.Err (.Decode realReason), real, rng)
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  obtain ⟨classified, hclassified, hreason⟩ := Std.WP.spec_imp_exists
    (decode_message_refusal_classifies message)
  have hclassifiedEq : classified = .Err realReason := by
    rw [hdecodeReal] at hclassified
    have heq : (.Err realReason : core.result.Result tacenta_wire.DecodedMessage
        tacenta_wire.DecodeError) = classified := by simpa using hclassified
    exact heq.symm
  subst classified
  obtain ⟨decoded, hdecoded, hnone⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitWireT3.decode_message_refines message)
  have hdecodedEq : decoded = .Err realReason := by
    rw [hdecodeReal] at hdecoded
    have heq : (.Err realReason : core.result.Result tacenta_wire.DecodedMessage
        tacenta_wire.DecodeError) = decoded := by simpa using hdecoded
    exact heq.symm
  subst decoded
  have hmodelDecode : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .error (decodeRefusalOf realReason) := by
    rw [← wire_bytesOf_eq_sliceOf]
    simp [Model.CompositeHeader.decodeDetailed, hnone, ← hreason]
  have hexact := decrypt_ratchet_decode_refusal_step_refines rngCore cryptoRng trace dh K
    view oracle real model message rng realReason (decodeRefusalOf realReason)
    hrel htrace hready hdecodeReal hmodelDecode rfl
  exact hexact

/-- Lift an already-related ratchet receive through the public decrypt
dispatcher's passthrough arms (`none` and explicit ratchet).  Refusals preserve
the inner state; success clears `pending_initial` on both sides. -/
theorem decrypt_passthrough_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (realType : Option serialization.MessageType)
    (inner : alloc.vec.Vec Std.U8)
    (innerOutput : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error ×
      lifecycle.Session × R)
    (htype : serialization.message_type message = ok realType)
    (hnotInitial : realType ≠ some .Initial)
    (hcopy : alloc.slice.Slice.to_vec core.clone.CloneU8 message = ok inner)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref inner) rng = ok innerOutput)
    (hstep : StepRefines trace dh K innerOutput
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))) :
    ∃ output,
      lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.decrypt view oracle model (sliceOf message)) := by
  have htypeRel := message_type_refines message
  rw [htype] at htypeRel
  have hmodelNot : Model.Lifecycle.messageType (sliceOf message) ≠ some .initial := by
    rw [← htypeRel]
    cases realType with
    | none => simp
    | some ty =>
        cases ty with
        | Ratchet => simp [messageTypeOf]
        | Initial => exact (hnotInitial rfl).elim
  have hdispatch := Model.Lifecycle.dispatchDecrypt_passthrough oracle model
    (sliceOf message) hmodelNot
  rcases innerOutput with ⟨realResult, realNext, rngNext⟩
  cases hmodelStep : Model.Lifecycle.decryptRatchet view oracle model
      (sliceOf message) with
  | mk modelNext modelResult oracleNext =>
      rw [hmodelStep] at hstep
      cases realResult with
      | Err realReason =>
          cases modelResult with
          | ok modelBytes =>
              have himpossible := hstep.result
              simp [ResultRefines] at himpossible
          | error modelReason =>
              let output : core.result.Result (alloc.vec.Vec Std.U8)
                  lifecycle.Error × lifecycle.Session × R :=
                (core.result.Result.Err realReason, realNext, rngNext)
              have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
                  ok output := by
                unfold lifecycle.Session.decrypt
                cases realType with
                | none =>
                    simp [htype, hcopy, hinner, output,
                      core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame.from]
                | some ty =>
                    cases ty with
                    | Ratchet =>
                        simp [htype, hcopy, hinner, output,
                          core.result.Result.Insts.CoreOpsTry.branch,
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                          core.convert.FromSame.from]
                    | Initial => exact (hnotInitial rfl).elim
              have hmodel : Model.Lifecycle.decrypt view oracle model (sliceOf message) =
                  { session := modelNext, result := .error modelReason,
                    oracle := oracleNext } := by
                simp [Model.Lifecycle.decrypt, hdispatch, hmodelStep]
              refine ⟨output, hreal, ?_⟩
              rw [hmodel]
              exact hstep
      | Ok realBytes =>
          cases modelResult with
          | error modelReason =>
              have himpossible := hstep.result
              simp [ResultRefines] at himpossible
          | ok modelBytes =>
              let realFinal := { realNext with pending_initial := none }
              let modelFinal := { modelNext with pendingInitial := none }
              let output : core.result.Result (alloc.vec.Vec Std.U8)
                  lifecycle.Error × lifecycle.Session × R :=
                (core.result.Result.Ok realBytes, realFinal, rngNext)
              have hfinal : SessionRefines dh K realFinal modelFinal := by
                exact ⟨hstep.session.triple, hstep.session.braid,
                  hstep.session.ratchetPrivate, hstep.session.identityAd,
                  hstep.session.ourIdentityPublic, hstep.session.peerIdentityPublic,
                  rfl, hstep.session.establishedEphemeral⟩
              have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
                  ok output := by
                unfold lifecycle.Session.decrypt
                cases realType with
                | none =>
                    simp [htype, hcopy, hinner, output, realFinal,
                      core.result.Result.Insts.CoreOpsTry.branch]
                | some ty =>
                    cases ty with
                    | Ratchet =>
                        simp [htype, hcopy, hinner, output, realFinal,
                          core.result.Result.Insts.CoreOpsTry.branch]
                    | Initial => exact (hnotInitial rfl).elim
              have hmodel : Model.Lifecycle.decrypt view oracle model (sliceOf message) =
                  { session := modelFinal, result := .ok modelBytes,
                    oracle := oracleNext } := by
                simp [Model.Lifecycle.decrypt, hdispatch, hmodelStep, modelFinal]
              refine ⟨output, hreal, ?_⟩
              rw [hmodel]
              exact ⟨hstep.result, hfinal, hstep.draws⟩

/-- The public decrypt passthrough proof with the infallible byte-copy step
discharged.  Callers reason about the copied bytes by value rather than carrying
an implementation-level `Slice::to_vec` equation. -/
theorem decrypt_passthrough_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (realType : Option serialization.MessageType)
    (innerOutput : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error ×
      lifecycle.Session × R)
    (htype : serialization.message_type message = ok realType)
    (hnotInitial : realType ≠ some .Initial)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref (show alloc.vec.Vec Std.U8 from message)) rng =
        ok innerOutput)
    (hstep : StepRefines trace dh K innerOutput
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))) :
    PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model
      message rng := by
  have hclone : ∀ x ∈ message.val, core.clone.CloneU8.clone x = ok x := by
    intro x _
    rfl
  obtain ⟨inner, hcopy, hsame⟩ := Std.WP.spec_imp_exists
    (alloc.slice.Slice.to_vec_spec core.clone.CloneU8 message hclone)
  have hinnerEq : inner = (show alloc.vec.Vec Std.U8 from message) := by
    exact hsame.symm
  subst inner
  exact decrypt_passthrough_step_refines rngCore cryptoRng trace dh K view oracle
    real model message rng realType (show alloc.vec.Vec Std.U8 from message)
    innerOutput htype hnotInitial hcopy hinner hstep

theorem decrypt_none_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (innerOutput : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error ×
      lifecycle.Session × R)
    (htype : serialization.message_type message = ok none)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref (show alloc.vec.Vec Std.U8 from message)) rng =
      ok innerOutput)
    (hstep : StepRefines trace dh K innerOutput
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))) :
    PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model
      message rng := by
  exact decrypt_passthrough_refines rngCore cryptoRng trace dh K view oracle
    real model message rng none innerOutput htype (by simp) hinner hstep

theorem decrypt_ratchet_message_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (innerOutput : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error ×
      lifecycle.Session × R)
    (htype : serialization.message_type message =
      ok (some serialization.MessageType.Ratchet))
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref (show alloc.vec.Vec Std.U8 from message)) rng =
      ok innerOutput)
    (hstep : StepRefines trace dh K innerOutput
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))) :
    PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model
      message rng := by
  exact decrypt_passthrough_refines rngCore cryptoRng trace dh K view oracle
    real model message rng (some .Ratchet) innerOutput htype (by simp) hinner hstep

/-! ## Public decrypt composition

The initial dispatcher and the ratchet passthrough are separate control-flow
roots in the generated function.  Keep their composition explicit: the
initial route is a typed sum of all six decoder/identity/repeat branches, and
the passthrough route is split by the two non-initial message-type outcomes.
The theorem below is the public-root join, rather than another branch lemma.
-/

inductive DecryptEndToEndEvidence {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R) : Type where
  | initial
      (route : InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model
        message rng) :
      DecryptEndToEndEvidence rngCore cryptoRng trace dh K view oracle real model message rng
  | ratchetNone
      (innerOutput : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error ×
        lifecycle.Session × R)
      (htype : serialization.message_type message = ok none)
      (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
        (alloc.vec.Vec.deref (show alloc.vec.Vec Std.U8 from message)) rng = ok innerOutput)
      (hstep : StepRefines trace dh K innerOutput
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))) :
      DecryptEndToEndEvidence rngCore cryptoRng trace dh K view oracle real model message rng
  | ratchetMessage
      (innerOutput : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error ×
        lifecycle.Session × R)
      (htype : serialization.message_type message = ok (some serialization.MessageType.Ratchet))
      (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
        (alloc.vec.Vec.deref (show alloc.vec.Vec Std.U8 from message)) rng = ok innerOutput)
      (hstep : StepRefines trace dh K innerOutput
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))) :
      DecryptEndToEndEvidence rngCore cryptoRng trace dh K view oracle real model message rng

theorem public_decrypt_end_to_end
    {R : Type} {rngCore : rand_core_1.RngCore R} {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (evidence : DecryptEndToEndEvidence rngCore cryptoRng trace dh K view oracle real model
      message rng) :
    PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model message rng := by
  cases evidence with
  | initial route => exact initial_dispatch_select_and_join route
  | ratchetNone innerOutput htype hinner hstep =>
      exact decrypt_none_refines rngCore cryptoRng trace dh K view oracle real model message rng
        innerOutput htype hinner hstep
  | ratchetMessage innerOutput htype hinner hstep =>
      exact decrypt_ratchet_message_refines rngCore cryptoRng trace dh K view oracle real model
        message rng innerOutput htype hinner hstep

theorem decrypt_passthrough_refusal_exact
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (inner : alloc.vec.Vec Std.U8) (rng rngNext : R)
    (realType : Option serialization.MessageType)
    (realReason : lifecycle.Error) (modelReason : Model.Lifecycle.Refusal)
    (realNext : lifecycle.Session) (modelNext : Model.Lifecycle.Session)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref inner) rng = ok (.Err realReason, realNext, rngNext))
    (hstep : StepRefines trace dh K
      (.Err realReason, realNext, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)))
    (hmodelStep : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session := modelNext, result := .error modelReason, oracle := oracleNext })
    (hmodel : Model.Lifecycle.decrypt view oracle model (sliceOf message) =
      { session := modelNext, result := .error modelReason, oracle := oracleNext })
    (htype : serialization.message_type message = ok realType)
    (hnotInitial : realType ≠ some .Initial)
    (hcopy : alloc.slice.Slice.to_vec core.clone.CloneU8 message = ok inner) :
    lifecycle.Session.decrypt rngCore cryptoRng real message rng =
        ok (.Err realReason, realNext, rngNext) ∧
      StepRefines trace dh K (.Err realReason, realNext, rngNext)
        (Model.Lifecycle.decrypt view oracle model (sliceOf message)) := by
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok (.Err realReason, realNext, rngNext) := by
    unfold lifecycle.Session.decrypt
    cases realType with
    | none =>
        simp [htype, hcopy, hinner,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from]
    | some ty =>
        cases ty with
        | Ratchet =>
            simp [htype, hcopy, hinner,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from]
        | Initial => exact (hnotInitial rfl).elim
  exact ⟨hreal, by rw [hmodel]; simpa [hmodelStep] using hstep⟩

theorem decrypt_passthrough_success_exact
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (inner : alloc.vec.Vec Std.U8) (rng rngNext : R)
    (realType : Option serialization.MessageType)
    (plaintext : alloc.vec.Vec Std.U8) (modelPlaintext : Bytes)
    (realNext : lifecycle.Session) (modelNext : Model.Lifecycle.Session)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref inner) rng = ok (.Ok plaintext, realNext, rngNext))
    (hstep : StepRefines trace dh K
      (.Ok plaintext, realNext, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)))
    (hmodelStep : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session := modelNext, result := .ok modelPlaintext, oracle := oracleNext })
    (hmodel : Model.Lifecycle.decrypt view oracle model (sliceOf message) =
      { session := { modelNext with pendingInitial := none },
        result := .ok modelPlaintext, oracle := oracleNext })
    (hbytes : vecOf plaintext = modelPlaintext)
    (htrace : trace rngNext = oracleNext.draws)
    (htype : serialization.message_type message = ok realType)
    (hnotInitial : realType ≠ some .Initial)
    (hcopy : alloc.slice.Slice.to_vec core.clone.CloneU8 message = ok inner) :
    lifecycle.Session.decrypt rngCore cryptoRng real message rng =
        ok (.Ok plaintext, { realNext with pending_initial := none }, rngNext) ∧
      StepRefines trace dh K
        (.Ok plaintext, { realNext with pending_initial := none }, rngNext)
        (Model.Lifecycle.decrypt view oracle model (sliceOf message)) := by
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok (.Ok plaintext, { realNext with pending_initial := none }, rngNext) := by
    unfold lifecycle.Session.decrypt
    cases realType with
    | none =>
        simp [htype, hcopy, hinner,
          core.result.Result.Insts.CoreOpsTry.branch]
    | some ty =>
        cases ty with
        | Ratchet =>
            simp [htype, hcopy, hinner,
              core.result.Result.Insts.CoreOpsTry.branch]
        | Initial => exact (hnotInitial rfl).elim
  have hstepSession : SessionRefines dh K realNext modelNext := by
    simpa [hmodelStep] using hstep.session
  have hfinal : SessionRefines dh K { realNext with pending_initial := none }
      { modelNext with pendingInitial := none } := by
    exact ⟨hstepSession.triple, hstepSession.braid, hstepSession.ratchetPrivate,
      hstepSession.identityAd, hstepSession.ourIdentityPublic,
      hstepSession.peerIdentityPublic, rfl, hstepSession.establishedEphemeral⟩
  exact ⟨hreal, by rw [hmodel]; exact ⟨by simpa [ResultRefines] using hbytes, hfinal, htrace⟩⟩

/-- Lift an exact initial-wrapper decoder refusal through public decrypt.
Like the ratchet decoder branch, this isolates the remaining obligation: prove
the detailed concrete and model decoders choose the same public reason. -/
theorem decrypt_initial_decode_refusal_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (realReason : tacenta_wire.DecodeError)
    (modelReason : Model.Messages.DecodeRefusal)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (htype : serialization.message_type message =
      ok (some serialization.MessageType.Initial))
    (hdecodeReal : tacenta_wire.decode_initial message =
      ok (core.result.Result.Err realReason))
    (hdecodeModel : Model.Messages.decodeInitialDetailed (sliceOf message) =
      .error modelReason)
    (hreason : decodeRefusalOf realReason = modelReason) :
    lifecycle.Session.decrypt rngCore cryptoRng real message rng =
        ok (.Err (.Decode realReason), real, rng) ∧
      StepRefines trace dh K
        (.Err (.Decode realReason), real, rng)
        (Model.Lifecycle.decrypt view oracle model (sliceOf message)) := by
  have htypeRel := message_type_refines message
  rw [htype] at htypeRel
  have hmodelType : Model.Lifecycle.messageType (sliceOf message) = some .initial := by
    simpa [messageTypeOf] using htypeRel.symm
  have hdispatch := Model.Lifecycle.dispatchDecrypt_decode_refusal oracle model
    (sliceOf message) modelReason hmodelType hdecodeModel
  have hmodel := Model.Lifecycle.decrypt_dispatch_refusal_keeps_state view oracle
    model (sliceOf message) (.decode modelReason) hdispatch
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok (.Err (.Decode realReason), real, rng) := by
    simp [lifecycle.Session.decrypt, htype, hdecodeReal]
  refine ⟨hreal, ?_⟩
  rw [hmodel]
  exact ⟨congrArg Model.Lifecycle.Refusal.decode hreason, hrel, htrace⟩

/-- A concrete initial-message decoder refusal determines the model's exact
public reason.  This discharges the reason-agreement premise at the Session
boundary instead of leaving it to a caller. -/
theorem decrypt_initial_decode_refusal_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (realReason : tacenta_wire.DecodeError)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (htype : serialization.message_type message =
      ok (some serialization.MessageType.Initial))
    (hdecodeReal : tacenta_wire.decode_initial message =
      ok (core.result.Result.Err realReason)) :
    PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model
      message rng := by
  obtain ⟨classified, hclassified, hreason⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitWireInitialT3.decode_initial_refusal_classifies message)
  have hclassifiedEq : classified = .Err realReason := by
    rw [hdecodeReal] at hclassified
    have heq : (.Err realReason : core.result.Result tacenta_wire.DecodedInitial
        tacenta_wire.DecodeError) = classified := by simpa using hclassified
    exact heq.symm
  subst classified
  have hreason' : decodeRefusalOf realReason =
      Model.Messages.initialDecodeRefusal (sliceOf message) := by
    cases realReason <;>
      simpa [decodeRefusalOf,
        Tacenta.SessionUnitWireInitialT3.decodeRefusalOf,
        wire_bytesOf_eq_sliceOf] using hreason
  obtain ⟨decoded, hdecoded, hnone⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitWireInitialT3.decode_initial_refines message)
  have hdecodedEq : decoded = .Err realReason := by
    rw [hdecodeReal] at hdecoded
    have heq : (.Err realReason : core.result.Result tacenta_wire.DecodedInitial
        tacenta_wire.DecodeError) = decoded := by simpa using hdecoded
    exact heq.symm
  subst decoded
  have hdecodeModel : Model.Messages.decodeInitialDetailed (sliceOf message) =
      .error (decodeRefusalOf realReason) := by
    simp only [Model.Messages.decodeInitialDetailed]
    have hnone' : Model.Messages.decodeInitial (sliceOf message) = none := by
      simpa [wire_bytesOf_eq_sliceOf] using hnone
    rw [hnone', hreason']
  have hexact := decrypt_initial_decode_refusal_step_refines rngCore cryptoRng trace dh K
    view oracle real model message rng realReason (decodeRefusalOf realReason)
    hrel htrace htype hdecodeReal hdecodeModel rfl
  exact ⟨(.Err (.Decode realReason), real, rng), hexact.1, hexact.2⟩

/-- An initial frame cannot be a repeat when the established Session has no
recorded establishment ephemeral.  Both implementations refuse it before the
inner ratchet receive and leave state and randomness unchanged. -/
def initial_dispatch_decode_refusal_from_premises
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rngCore cryptoRng trace dh K view oracle real model message rng)
    (reason : tacenta_wire.DecodeError)
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Err reason))
    (hdecodeModel : Model.Messages.decodeInitialDetailed (sliceOf message) =
      .error (Tacenta.SessionUnitWireInitialT3.decodeRefusalOf reason)) :
    InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng := by
  refine InitialDispatchRoute.decodeRefusal reason hdecode ?_
  exact decrypt_initial_decode_refusal_refines rngCore cryptoRng trace dh K view oracle
    real model message rng reason ctx.hrel ctx.htrace ctx.htype hdecode


theorem decrypt_initial_without_established_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (decoded : tacenta_wire.DecodedInitial)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (htype : serialization.message_type message =
      ok (some serialization.MessageType.Initial))
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hnone : real.established_ephemeral = none) :
    PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model
      message rng := by
  have hmodelType := message_type_refines_initial message htype
  have hdecodeRel := decode_initial_refines_lifecycle message
  rw [hdecode] at hdecodeRel
  have hmodelNone : model.establishedEphemeral = none := by
    have h := hrel.establishedEphemeral
    rw [hnone] at h
    exact h.symm
  have hrepeat : Model.Lifecycle.repeatedInitial oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded) = false := by
    simp [Model.Lifecycle.repeatedInitial, hmodelNone]
  have hdispatch := Model.Lifecycle.dispatchDecrypt_not_repeat oracle model
    (sliceOf message) (Tacenta.SessionUnitWireInitialT3.initialOf decoded)
    hmodelType hdecodeRel hrepeat
  have hmodel := Model.Lifecycle.decrypt_dispatch_refusal_keeps_state view oracle
    model (sliceOf message) .notARepeatedInitial hdispatch
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok (.Err lifecycle.Error.NotARepeatedInitial, real, rng) := by
    simp [lifecycle.Session.decrypt, htype, hdecode, hnone]
  refine ⟨(.Err lifecycle.Error.NotARepeatedInitial, real, rng), hreal, ?_⟩
  rw [hmodel]
  exact ⟨rfl, hrel, htrace⟩

/-- A decoded initial wrapper with the wrong establishment ephemeral is refused
before public-key encoding or the inner ratchet receive. -/
def initial_dispatch_no_established_from_premises
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rngCore cryptoRng trace dh K view oracle real model message rng)
    (decoded : tacenta_wire.DecodedInitial)
    (hdecode : tacenta_wire.decode_initial message = ok (core.result.Result.Ok decoded))
    (hnone : real.established_ephemeral = none)
    : InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng := by
  refine InitialDispatchRoute.noEstablished decoded hdecode hnone ?_
  exact decrypt_initial_without_established_refines rngCore cryptoRng trace dh K view oracle
    real model message rng decoded ctx.hrel ctx.htrace ctx.htype hdecode hnone

theorem decrypt_initial_ephemeral_mismatch_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (established : alloc.vec.Vec Std.U8)
    (decoded : tacenta_wire.DecodedInitial)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (htype : serialization.message_type message =
      ok (some serialization.MessageType.Initial))
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hmismatch : vecOf established ≠ vecOf decoded.ephemeral)
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok false)
    (hagreementMismatch : oracle.dhAgree model.ratchetPrivate (vecOf established) ≠
      oracle.dhAgree model.ratchetPrivate
        (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val)) :
    ∃ output,
      lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.decrypt view oracle model (sliceOf message)) := by
  have htypeRel := message_type_refines message
  rw [htype] at htypeRel
  have hmodelType : Model.Lifecycle.messageType (sliceOf message) = some .initial := by
    simpa [messageTypeOf] using htypeRel.symm
  have hdecodeRel := decode_initial_refines_lifecycle message
  rw [hdecode] at hdecodeRel
  obtain ⟨ephemeralEqual, hephemeralCall, hephemeralPost⟩ :=
    Std.WP.spec_imp_exists (vec_u8_eq_refines established decoded.ephemeral)
  have hvalMismatch : established.val ≠ decoded.ephemeral.val := by
    intro h
    apply hmismatch
    simp [vecOf, h]
  have hephemeralFalse : ephemeralEqual = false := by
    cases ephemeralEqual with
    | false => rfl
    | true => exact (hvalMismatch (hephemeralPost.1 rfl)).elim
  rw [hephemeralFalse] at hephemeralCall
  have hmodelEstablished :
      model.establishedEphemeral = some (vecOf established) := by
    have h := hrel.establishedEphemeral
    rw [hestablished] at h
    exact h.symm
  have hrepeat : Model.Lifecycle.repeatedInitial oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded) = false := by
    cases hr : Model.Lifecycle.repeatedInitial oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded) with
    | false => rfl
    | true =>
        obtain ⟨ephemeral, he, heq, _⟩ :=
          (Model.Lifecycle.repeatedInitial_iff oracle _ _).1 hr
        rw [hmodelEstablished] at he
        cases he
        have hcontra : False := by
          have heq' : oracle.dhAgree model.ratchetPrivate (vecOf established) =
              oracle.dhAgree model.ratchetPrivate
                (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val) := by
            cases hleft : oracle.dhAgree model.ratchetPrivate (vecOf established) with
            | none =>
                simp [Model.Lifecycle.sameEphemeralAgreement,
                  Tacenta.SessionUnitWireInitialT3.initialOf, hleft] at heq
            | some left =>
                cases hright : oracle.dhAgree model.ratchetPrivate
                    (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val) with
                | none =>
                    simp [Model.Lifecycle.sameEphemeralAgreement,
                      Tacenta.SessionUnitWireInitialT3.initialOf, hleft, hright] at heq
                | some right =>
                    have hkeys : left = right := by
                      simpa [Model.Lifecycle.sameEphemeralAgreement,
                        Tacenta.SessionUnitWireInitialT3.initialOf, hleft, hright] using heq
                    simpa [hleft, hright, hkeys]
          exact hagreementMismatch heq'
        exact hcontra.elim
  have hdispatch := Model.Lifecycle.dispatchDecrypt_not_repeat oracle model
    (sliceOf message) (Tacenta.SessionUnitWireInitialT3.initialOf decoded)
    hmodelType hdecodeRel hrepeat
  have hmodel := Model.Lifecycle.decrypt_dispatch_refusal_keeps_state view oracle
    model (sliceOf message) .notARepeatedInitial hdispatch
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok (.Err lifecycle.Error.NotARepeatedInitial, real, rng) := by
    simp [lifecycle.Session.decrypt, htype, hdecode, hestablished,
      hsameAgreement, hephemeralCall]
  refine ⟨(.Err lifecycle.Error.NotARepeatedInitial, real, rng), hreal, ?_⟩
  rw [hmodel]
  exact ⟨rfl, hrel, htrace⟩

/-- A wrapper with the right establishment ephemeral but the wrong peer
identity is refused after the exact EncodeEC comparison and before the inner
ratchet receive. -/
def initial_dispatch_ephemeral_mismatch_from_premises
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rngCore cryptoRng trace dh K view oracle real model message rng)
    (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial)
    (hdecode : tacenta_wire.decode_initial message = ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hmismatch : vecOf established ≠ vecOf decoded.ephemeral)
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok false)
    (hagreementMismatch : oracle.dhAgree model.ratchetPrivate (vecOf established) ≠
      oracle.dhAgree model.ratchetPrivate
        (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val)) :
    InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng := by
  refine InitialDispatchRoute.ephemeralMismatch established decoded hdecode hestablished hmismatch ?_
  exact decrypt_initial_ephemeral_mismatch_refines rngCore cryptoRng trace dh K view oracle
    real model message rng established decoded ctx.hrel ctx.htrace ctx.htype hdecode
    hestablished hmismatch hsameAgreement hagreementMismatch

theorem decrypt_initial_identity_mismatch_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (codec : DhCodecOf dh)
    (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (established : alloc.vec.Vec Std.U8)
    (decoded : tacenta_wire.DecodedInitial)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (htype : serialization.message_type message =
      ok (some serialization.MessageType.Initial))
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hephemeral : vecOf established = vecOf decoded.ephemeral)
    (hmismatch : vecOf decoded.identity ≠
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public))
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok true) :
    ∃ output,
      lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.decrypt view oracle model (sliceOf message)) := by
  have htypeRel := message_type_refines message
  rw [htype] at htypeRel
  have hmodelType : Model.Lifecycle.messageType (sliceOf message) = some .initial := by
    simpa [messageTypeOf] using htypeRel.symm
  have hdecodeRel := decode_initial_refines_lifecycle message
  rw [hdecode] at hdecodeRel
  obtain ⟨encoded, hencoded, hencodedValue⟩ :=
    encode_ec_refines dh codec real.peer_identity_public
  obtain ⟨ephemeralEqual, hephemeralCall, hephemeralPost⟩ :=
    Std.WP.spec_imp_exists (vec_u8_eq_refines established decoded.ephemeral)
  have hephemeralEq : established = decoded.ephemeral :=
    vecOf_injective hephemeral
  have hephemeralTrue : ephemeralEqual = true :=
    hephemeralPost.2 (congrArg (fun value => value.val) hephemeralEq)
  rw [hephemeralTrue] at hephemeralCall
  obtain ⟨identityEqual, hidentityCall, hidentityPost⟩ :=
    Std.WP.spec_imp_exists (vec_u8_eq_refines decoded.identity encoded)
  have hidentityValMismatch : decoded.identity.val ≠ encoded.val := by
    intro h
    apply hmismatch
    calc
      vecOf decoded.identity = vecOf encoded := by simp [vecOf, h]
      _ = Model.PersistedState.SessionState.encodeEc
          (dh.publicKey real.peer_identity_public) := hencodedValue
  have hidentityFalse : identityEqual = false := by
    cases identityEqual with
    | false => rfl
    | true => exact (hidentityValMismatch (hidentityPost.1 rfl)).elim
  rw [hidentityFalse] at hidentityCall
  have hrepeat : Model.Lifecycle.repeatedInitial oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded) = false := by
    cases hr : Model.Lifecycle.repeatedInitial oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded) with
    | false => rfl
    | true =>
        obtain ⟨_, _, _, hmodelIdentity⟩ :=
          (Model.Lifecycle.repeatedInitial_iff oracle _ _).1 hr
        have hcontra : False := by
          apply hmismatch
          have hmodelIdentity' :
              Tacenta.SessionUnitWireT3.bytesOf decoded.identity.val =
                Model.PersistedState.SessionState.encodeEc
                  model.peerIdentityPublic := by
            simpa [Tacenta.SessionUnitWireInitialT3.initialOf] using
              hmodelIdentity
          calc
            vecOf decoded.identity =
                Tacenta.SessionUnitWireT3.bytesOf decoded.identity.val :=
              (wire_bytesOf_eq_vecOf decoded.identity).symm
            _ = Model.PersistedState.SessionState.encodeEc
                model.peerIdentityPublic := hmodelIdentity'
            _ = Model.PersistedState.SessionState.encodeEc
                (dh.publicKey real.peer_identity_public) := by
              rw [hrel.peerIdentityPublic]
        exact hcontra.elim
  have hdispatch := Model.Lifecycle.dispatchDecrypt_not_repeat oracle model
    (sliceOf message) (Tacenta.SessionUnitWireInitialT3.initialOf decoded)
    hmodelType hdecodeRel hrepeat
  have hmodel := Model.Lifecycle.decrypt_dispatch_refusal_keeps_state view oracle
    model (sliceOf message) .notARepeatedInitial hdispatch
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok (.Err lifecycle.Error.NotARepeatedInitial, real, rng) := by
    simp [lifecycle.Session.decrypt, htype, hdecode, hestablished,
      hsameAgreement, hephemeralCall, hencoded, hidentityCall]
  refine ⟨(.Err lifecycle.Error.NotARepeatedInitial, real, rng), hreal, ?_⟩
  rw [hmodel]
  exact ⟨rfl, hrel, htrace⟩

/-! Identity refusal after a successful agreement does not require the two
    ephemeral byte strings to be equal. -/
theorem decrypt_initial_identity_mismatch_agreement_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (codec : DhCodecOf dh)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
    (model : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : R)
    (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (htype : serialization.message_type message =
      ok (some serialization.MessageType.Initial))
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hmismatch : vecOf decoded.identity ≠
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public))
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok true) :
    ∃ output,
      lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.decrypt view oracle model (sliceOf message)) := by
  have htypeRel := message_type_refines message
  rw [htype] at htypeRel
  have hmodelType : Model.Lifecycle.messageType (sliceOf message) = some .initial := by
    simpa [messageTypeOf] using htypeRel.symm
  have hdecodeRel := decode_initial_refines_lifecycle message
  rw [hdecode] at hdecodeRel
  obtain ⟨encoded, hencoded, hencodedValue⟩ :=
    encode_ec_refines dh codec real.peer_identity_public
  obtain ⟨identityEqual, hidentityCall, hidentityPost⟩ :=
    Std.WP.spec_imp_exists (vec_u8_eq_refines decoded.identity encoded)
  have hidentityValMismatch : decoded.identity.val ≠ encoded.val := by
    intro h
    apply hmismatch
    calc
      vecOf decoded.identity = vecOf encoded := by simp [vecOf, h]
      _ = Model.PersistedState.SessionState.encodeEc
          (dh.publicKey real.peer_identity_public) := hencodedValue
  have hidentityFalse : identityEqual = false := by
    cases identityEqual with
    | false => rfl
    | true => exact (hidentityValMismatch (hidentityPost.1 rfl)).elim
  rw [hidentityFalse] at hidentityCall
  have hmodelIdentity :
      Tacenta.SessionUnitWireT3.bytesOf decoded.identity.val ≠
        Model.PersistedState.SessionState.encodeEc model.peerIdentityPublic := by
    intro h
    apply hmismatch
    calc
      vecOf decoded.identity =
          Tacenta.SessionUnitWireT3.bytesOf decoded.identity.val :=
        (wire_bytesOf_eq_vecOf decoded.identity).symm
      _ = Model.PersistedState.SessionState.encodeEc model.peerIdentityPublic := h
      _ = Model.PersistedState.SessionState.encodeEc
          (dh.publicKey real.peer_identity_public) := by
        rw [hrel.peerIdentityPublic]
  have hrepeat : Model.Lifecycle.repeatedInitial oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded) = false := by
    have hmodelEstablished :
        model.establishedEphemeral = some (vecOf established) := by
      have h := hrel.establishedEphemeral
      rw [hestablished] at h
      exact h.symm
    cases hr : Model.Lifecycle.repeatedInitial oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded) with
    | false => rfl
    | true =>
        obtain ⟨ephemeral, he, _, hidentityModel⟩ :=
          (Model.Lifecycle.repeatedInitial_iff oracle _ _).1 hr
        rw [hmodelEstablished] at he
        cases he
        have hmodelIdentity' :
            Tacenta.SessionUnitWireT3.bytesOf decoded.identity.val ≠
              Model.PersistedState.SessionState.encodeEc model.peerIdentityPublic := by
          exact hmodelIdentity
        have hcontra : False := by
          apply hmodelIdentity'
          simpa [Tacenta.SessionUnitWireInitialT3.initialOf] using hidentityModel
        exact hcontra.elim
  have hdispatch := Model.Lifecycle.dispatchDecrypt_not_repeat oracle model
    (sliceOf message) (Tacenta.SessionUnitWireInitialT3.initialOf decoded)
    hmodelType hdecodeRel hrepeat
  have hmodel := Model.Lifecycle.decrypt_dispatch_refusal_keeps_state view oracle
    model (sliceOf message) .notARepeatedInitial hdispatch
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok (.Err lifecycle.Error.NotARepeatedInitial, real, rng) := by
    simp [lifecycle.Session.decrypt, htype, hdecode, hestablished,
      hsameAgreement, hencoded, hidentityCall]
  refine ⟨(.Err lifecycle.Error.NotARepeatedInitial, real, rng), hreal, ?_⟩
  rw [hmodel]
  exact ⟨rfl, hrel, htrace⟩

/-- Lift an accepted repeated-initial wrapper through public decrypt.  The two
wrapper identity checks are derived from the shared byte representation; the
inner receive relation supplies the authenticated ratchet transition. -/
def initial_dispatch_identity_mismatch_from_premises
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {codec : DhCodecOf dh}
    {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
    {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session}
    {model : Model.Lifecycle.Session} {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rngCore cryptoRng trace dh K view oracle real model message rng)
    (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial)
    (hdecode : tacenta_wire.decode_initial message = ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hephemeral : vecOf established = vecOf decoded.ephemeral)
    (hmismatch : vecOf decoded.identity ≠
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public))
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok true) :
    InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng := by
  refine InitialDispatchRoute.identityMismatch established decoded hdecode hestablished
    hsameAgreement hmismatch ?_
  exact decrypt_initial_identity_mismatch_refines rngCore cryptoRng trace dh codec K view oracle
    real model message rng established decoded ctx.hrel ctx.htrace ctx.htype hdecode
    hestablished hephemeral hmismatch hsameAgreement

theorem decrypt_initial_repeat_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (codec : DhCodecOf dh)
    (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (established : alloc.vec.Vec Std.U8)
    (decoded : tacenta_wire.DecodedInitial)
    (innerOutput : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error ×
      lifecycle.Session × R)
    (hrel : SessionRefines dh K real model)
    (htype : serialization.message_type message =
      ok (some serialization.MessageType.Initial))
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hephemeral : vecOf established = vecOf decoded.ephemeral)
    (hidentity : vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public))
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok true)
    (hmodelSame : Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
      (vecOf established) (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val) = true)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref decoded.message) rng = ok innerOutput)
    (hstep : StepRefines trace dh K innerOutput
      (Model.Lifecycle.decryptRatchet view oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage)) :
    PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model
      message rng := by
  have hmodelType := message_type_refines_initial message htype
  have hdecodeRel := decode_initial_refines_lifecycle message
  rw [hdecode] at hdecodeRel
  obtain ⟨encoded, hencoded, hephemeralCall, hidentityCall, hrepeat⟩ :=
    repeated_initial_checks_refine oracle dh codec K real model established decoded hrel
      hestablished hephemeral hidentity hmodelSame
  have hdispatch := Model.Lifecycle.dispatchDecrypt_repeat oracle model
    (sliceOf message) (Tacenta.SessionUnitWireInitialT3.initialOf decoded)
    hmodelType hdecodeRel hrepeat
  rcases innerOutput with ⟨realResult, realNext, rngNext⟩
  cases hmodelStep : Model.Lifecycle.decryptRatchet view oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage with
  | mk modelNext modelResult oracleNext =>
      rw [hmodelStep] at hstep
      cases realResult with
      | Err realReason =>
          cases modelResult with
          | ok modelBytes =>
              have himpossible := hstep.result
              simp [ResultRefines] at himpossible
          | error modelReason =>
              let output : core.result.Result (alloc.vec.Vec Std.U8)
                  lifecycle.Error × lifecycle.Session × R :=
                (core.result.Result.Err realReason, realNext, rngNext)
              have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
                  ok output := by
                simp [lifecycle.Session.decrypt, htype, hdecode, hestablished,
                  hsameAgreement, hephemeralCall, hencoded, hidentityCall, hinner, output,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from]
              have hmodel : Model.Lifecycle.decrypt view oracle model (sliceOf message) =
                  { session := modelNext, result := .error modelReason,
                    oracle := oracleNext } := by
                simp [Model.Lifecycle.decrypt, hdispatch, hmodelStep]
              refine ⟨output, hreal, ?_⟩
              rw [hmodel]
              exact hstep
      | Ok realBytes =>
          cases modelResult with
          | error modelReason =>
              have himpossible := hstep.result
              simp [ResultRefines] at himpossible
          | ok modelBytes =>
              let realFinal := { realNext with pending_initial := none }
              let modelFinal := { modelNext with pendingInitial := none }
              let output : core.result.Result (alloc.vec.Vec Std.U8)
                  lifecycle.Error × lifecycle.Session × R :=
                (core.result.Result.Ok realBytes, realFinal, rngNext)
              have hfinal : SessionRefines dh K realFinal modelFinal := by
                exact ⟨hstep.session.triple, hstep.session.braid,
                  hstep.session.ratchetPrivate, hstep.session.identityAd,
                  hstep.session.ourIdentityPublic, hstep.session.peerIdentityPublic,
                  rfl, hstep.session.establishedEphemeral⟩
              have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
                  ok output := by
                simp [lifecycle.Session.decrypt, htype, hdecode, hestablished,
                  hsameAgreement, hephemeralCall, hencoded, hidentityCall, hinner, output, realFinal,
                  core.result.Result.Insts.CoreOpsTry.branch]
              have hmodel : Model.Lifecycle.decrypt view oracle model (sliceOf message) =
                  { session := modelFinal, result := .ok modelBytes,
                    oracle := oracleNext } := by
                simp [Model.Lifecycle.decrypt, hdispatch, hmodelStep, modelFinal]
              refine ⟨output, hreal, ?_⟩
              rw [hmodel]
              exact ⟨hstep.result, hfinal, hstep.draws⟩

/-! Result-shaped repeat refinement for byte-different ephemerals that agree
    in the model's successful agreement class. -/
theorem decrypt_initial_repeat_agreement_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (codec : DhCodecOf dh)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
    (model : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : R)
    (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial)
    (innerOutput : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error ×
      lifecycle.Session × R)
    (hrel : SessionRefines dh K real model)
    (htype : serialization.message_type message =
      ok (some serialization.MessageType.Initial))
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hidentity : vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public))
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok true)
    (hmodelSame : Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
      (vecOf established) (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val) = true)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref decoded.message) rng = ok innerOutput)
    (hstep : StepRefines trace dh K innerOutput
      (Model.Lifecycle.decryptRatchet view oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage)) :
    PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model
      message rng := by
  have hmodelType := message_type_refines_initial message htype
  have hdecodeRel := decode_initial_refines_lifecycle message
  rw [hdecode] at hdecodeRel
  obtain ⟨encoded, hencoded, hidentityCall, hrepeat⟩ :=
    repeated_initial_agreement_checks_refine oracle dh codec K real model established decoded
      hrel hestablished hidentity hmodelSame
  have hdispatch := Model.Lifecycle.dispatchDecrypt_repeat oracle model
    (sliceOf message) (Tacenta.SessionUnitWireInitialT3.initialOf decoded)
    hmodelType hdecodeRel hrepeat
  rcases innerOutput with ⟨realResult, realNext, rngNext⟩
  cases hmodelStep : Model.Lifecycle.decryptRatchet view oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage with
  | mk modelNext modelResult oracleNext =>
      rw [hmodelStep] at hstep
      cases realResult with
      | Err realReason =>
          cases modelResult with
          | ok modelBytes =>
              have himpossible := hstep.result
              simp [ResultRefines] at himpossible
          | error modelReason =>
              let output : core.result.Result (alloc.vec.Vec Std.U8)
                  lifecycle.Error × lifecycle.Session × R :=
                (core.result.Result.Err realReason, realNext, rngNext)
              have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
                  ok output := by
                simp [lifecycle.Session.decrypt, htype, hdecode, hestablished,
                  hsameAgreement, hencoded, hidentityCall, hinner, output,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from]
              have hmodel : Model.Lifecycle.decrypt view oracle model (sliceOf message) =
                  { session := modelNext, result := .error modelReason,
                    oracle := oracleNext } := by
                simp [Model.Lifecycle.decrypt, hdispatch, hmodelStep]
              refine ⟨output, hreal, ?_⟩
              rw [hmodel]
              exact hstep
      | Ok realBytes =>
          cases modelResult with
          | error modelReason =>
              have himpossible := hstep.result
              simp [ResultRefines] at himpossible
          | ok modelBytes =>
              let realFinal := { realNext with pending_initial := none }
              let modelFinal := { modelNext with pendingInitial := none }
              let output : core.result.Result (alloc.vec.Vec Std.U8)
                  lifecycle.Error × lifecycle.Session × R :=
                (core.result.Result.Ok realBytes, realFinal, rngNext)
              have hfinal : SessionRefines dh K realFinal modelFinal := by
                exact ⟨hstep.session.triple, hstep.session.braid,
                  hstep.session.ratchetPrivate, hstep.session.identityAd,
                  hstep.session.ourIdentityPublic, hstep.session.peerIdentityPublic,
                  rfl, hstep.session.establishedEphemeral⟩
              have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
                  ok output := by
                simp [lifecycle.Session.decrypt, htype, hdecode, hestablished,
                  hsameAgreement, hencoded, hidentityCall, hinner, output, realFinal,
                  core.result.Result.Insts.CoreOpsTry.branch]
              have hmodel : Model.Lifecycle.decrypt view oracle model (sliceOf message) =
                  { session := modelFinal, result := .ok modelBytes,
                    oracle := oracleNext } := by
                simp [Model.Lifecycle.decrypt, hdispatch, hmodelStep, modelFinal]
              refine ⟨output, hreal, ?_⟩
              rw [hmodel]
              exact ⟨hstep.result, hfinal, hstep.draws⟩

/-! The refusal half of the mixed repeated-initial theorem, with the concrete
decoder and repeat-check equalities made explicit. -/
theorem decrypt_initial_repeat_refusal_exact
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (codec : DhCodecOf dh) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (established : alloc.vec.Vec Std.U8)
    (decoded : tacenta_wire.DecodedInitial)
    (realReason : lifecycle.Error) (modelReason : Model.Lifecycle.Refusal)
    (modelNext : Model.Lifecycle.Session)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rngNext = oracleNext.draws)
    (htype : serialization.message_type message =
      ok (some serialization.MessageType.Initial))
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hephemeral : vecOf established = vecOf decoded.ephemeral)
    (hidentity : vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public))
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok true)
    (hmodelSame : Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
      (vecOf established) (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val) = true)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref decoded.message) rng =
      ok (.Err realReason, real, rngNext))
    (hmodelStep : Model.Lifecycle.decryptRatchet view oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage =
      { session := modelNext, result := .error modelReason, oracle := oracleNext })
    (hstep : StepRefines trace dh K
      (.Err realReason, real, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage)) :
    PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model
      message rng := by
  have hmodelType := message_type_refines_initial message htype
  have hdecodeRel := decode_initial_refines_lifecycle message
  rw [hdecode] at hdecodeRel
  obtain ⟨encoded, hencoded', hephemeralCall, hidentityCall, hrepeat⟩ :=
    repeated_initial_checks_refine oracle dh codec K real model established decoded hrel
      hestablished hephemeral hidentity hmodelSame
  have hdispatch := Model.Lifecycle.dispatchDecrypt_repeat oracle model
    (sliceOf message) (Tacenta.SessionUnitWireInitialT3.initialOf decoded)
    hmodelType hdecodeRel hrepeat
  have hmodel : Model.Lifecycle.decrypt view oracle model (sliceOf message) =
      { session := modelNext, result := .error modelReason, oracle := oracleNext } := by
    simp [Model.Lifecycle.decrypt, hdispatch, hmodelStep]
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok (.Err realReason, real, rngNext) := by
    simp [lifecycle.Session.decrypt, htype, hdecode, hestablished,
      hsameAgreement, hephemeralCall, hencoded', hidentityCall, hinner,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from]
  exact ⟨(.Err realReason, real, rngNext), hreal,
    by rw [hmodel]; simpa [Model.Lifecycle.decrypt, hdispatch, hmodelStep] using hstep⟩

/-! The byte-different agreement-equivalent refusal route.  It shares the
    generated wrapper's actual agreement result with the model and therefore
    does not manufacture a byte-equality premise. -/
theorem decrypt_initial_repeat_agreement_refusal_exact
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (codec : DhCodecOf dh) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (established : alloc.vec.Vec Std.U8)
    (decoded : tacenta_wire.DecodedInitial)
    (realReason : lifecycle.Error) (modelReason : Model.Lifecycle.Refusal)
    (modelNext : Model.Lifecycle.Session)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rngNext = oracleNext.draws)
    (htype : serialization.message_type message =
      ok (some serialization.MessageType.Initial))
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hidentity : vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public))
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok true)
    (hmodelSame : Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
      (vecOf established) (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val) = true)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref decoded.message) rng =
      ok (.Err realReason, real, rngNext))
    (hmodelStep : Model.Lifecycle.decryptRatchet view oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage =
      { session := modelNext, result := .error modelReason, oracle := oracleNext })
    (hstep : StepRefines trace dh K
      (.Err realReason, real, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage)) :
    PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model
      message rng := by
  have hmodelType := message_type_refines_initial message htype
  have hdecodeRel := decode_initial_refines_lifecycle message
  rw [hdecode] at hdecodeRel
  obtain ⟨encoded, hencoded', hidentityCall, hrepeat⟩ :=
    repeated_initial_agreement_checks_refine oracle dh codec K real model established decoded
      hrel hestablished hidentity hmodelSame
  have hdispatch := Model.Lifecycle.dispatchDecrypt_repeat oracle model
    (sliceOf message) (Tacenta.SessionUnitWireInitialT3.initialOf decoded)
    hmodelType hdecodeRel hrepeat
  have hmodel : Model.Lifecycle.decrypt view oracle model (sliceOf message) =
      { session := modelNext, result := .error modelReason, oracle := oracleNext } := by
    simp [Model.Lifecycle.decrypt, hdispatch, hmodelStep]
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok (.Err realReason, real, rngNext) := by
    simp [lifecycle.Session.decrypt, htype, hdecode, hestablished,
      hsameAgreement, hencoded', hidentityCall, hinner,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from]
  exact ⟨(.Err realReason, real, rngNext), hreal,
    by rw [hmodel]; simpa [Model.Lifecycle.decrypt, hdispatch, hmodelStep] using hstep⟩

def initial_dispatch_repeat_refusal_from_premises
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key}
    {dh : DhView} {codec : DhCodecOf dh} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    (ctx : InitialDispatchContext rngCore cryptoRng trace dh K view oracle real model message rng)
    (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial)
    (realReason : lifecycle.Error) (modelReason : Model.Lifecycle.Refusal)
    (modelNext : Model.Lifecycle.Session)
    (htraceNext : trace rngNext = oracleNext.draws)
    (hdecode : tacenta_wire.decode_initial message = ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hephemeral : vecOf established = vecOf decoded.ephemeral)
    (hidentity : vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public))
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok true)
    (hmodelSame : Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
      (vecOf established) (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val) = true)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref decoded.message) rng = ok (.Err realReason, real, rngNext))
    (hmodelStep : Model.Lifecycle.decryptRatchet view oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage =
      { session := modelNext, result := .error modelReason, oracle := oracleNext })
    (hstep : StepRefines trace dh K (.Err realReason, real, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage)) :
    InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng := by
  refine InitialDispatchRoute.repeatRefusal established decoded realReason real rngNext hdecode
    hestablished hidentity hsameAgreement hinner ?_
  exact decrypt_initial_repeat_refusal_exact rngCore cryptoRng trace dh codec K view oracle
    oracleNext real model message rng rngNext established decoded realReason modelReason modelNext
    ctx.hrel htraceNext ctx.htype hdecode hestablished
    hephemeral hidentity hsameAgreement hmodelSame hinner hmodelStep hstep

theorem decrypt_initial_repeat_success_exact
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (codec : DhCodecOf dh) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (established : alloc.vec.Vec Std.U8)
    (decoded : tacenta_wire.DecodedInitial)
    (plaintext : alloc.vec.Vec Std.U8) (modelPlaintext : Bytes)
    (realNext : lifecycle.Session) (modelNext : Model.Lifecycle.Session)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rngNext = oracleNext.draws)
    (htype : serialization.message_type message =
      ok (some serialization.MessageType.Initial))
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hephemeral : vecOf established = vecOf decoded.ephemeral)
    (hidentity : vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public))
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok true)
    (hmodelSame : Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
      (vecOf established) (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val) = true)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref decoded.message) rng =
      ok (.Ok plaintext, realNext, rngNext))
    (hmodelStep : Model.Lifecycle.decryptRatchet view oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage =
      { session := modelNext, result := .ok modelPlaintext, oracle := oracleNext })
    (hbytes : vecOf plaintext = modelPlaintext)
    (hstep : StepRefines trace dh K
      (.Ok plaintext, realNext, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage)) :
    PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model
      message rng := by
  have hmodelType := message_type_refines_initial message htype
  have hdecodeRel := decode_initial_refines_lifecycle message
  rw [hdecode] at hdecodeRel
  obtain ⟨encoded, hencoded, hephemeralCall, hidentityCall, hrepeat⟩ :=
    repeated_initial_checks_refine oracle dh codec K real model established decoded hrel
      hestablished hephemeral hidentity hmodelSame
  have hdispatch := Model.Lifecycle.dispatchDecrypt_repeat oracle model
    (sliceOf message) (Tacenta.SessionUnitWireInitialT3.initialOf decoded)
    hmodelType hdecodeRel hrepeat
  let realFinal := { realNext with pending_initial := none }
  let modelFinal := { modelNext with pendingInitial := none }
  have hs : SessionRefines dh K realNext modelNext := by
    simpa [hmodelStep] using hstep.session
  have hfinal : SessionRefines dh K realFinal modelFinal := by
    exact ⟨hs.triple, hs.braid, hs.ratchetPrivate, hs.identityAd,
      hs.ourIdentityPublic, hs.peerIdentityPublic, rfl, hs.establishedEphemeral⟩
  have hmodel : Model.Lifecycle.decrypt view oracle model (sliceOf message) =
      { session := modelFinal, result := .ok modelPlaintext, oracle := oracleNext } := by
    simp [Model.Lifecycle.decrypt, hdispatch, hmodelStep, modelFinal]
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok (.Ok plaintext, realFinal, rngNext) := by
    simp [lifecycle.Session.decrypt, htype, hdecode, hestablished,
      hsameAgreement, hephemeralCall, hencoded, hidentityCall, hinner, realFinal,
      core.result.Result.Insts.CoreOpsTry.branch]
  exact ⟨(.Ok plaintext, realFinal, rngNext), hreal,
    by rw [hmodel]; exact ⟨by simpa [ResultRefines] using hbytes, hfinal, htrace⟩⟩

/-! The byte-different agreement-equivalent success route. -/
theorem decrypt_initial_repeat_agreement_success_exact
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (codec : DhCodecOf dh) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (established : alloc.vec.Vec Std.U8)
    (decoded : tacenta_wire.DecodedInitial)
    (plaintext : alloc.vec.Vec Std.U8) (modelPlaintext : Bytes)
    (realNext : lifecycle.Session) (modelNext : Model.Lifecycle.Session)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rngNext = oracleNext.draws)
    (htype : serialization.message_type message =
      ok (some serialization.MessageType.Initial))
    (hdecode : tacenta_wire.decode_initial message =
      ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hidentity : vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public))
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok true)
    (hmodelSame : Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
      (vecOf established) (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val) = true)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref decoded.message) rng =
      ok (.Ok plaintext, realNext, rngNext))
    (hmodelStep : Model.Lifecycle.decryptRatchet view oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage =
      { session := modelNext, result := .ok modelPlaintext, oracle := oracleNext })
    (hbytes : vecOf plaintext = modelPlaintext)
    (hstep : StepRefines trace dh K
      (.Ok plaintext, realNext, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage)) :
    PublicDecryptWitness rngCore cryptoRng trace dh K view oracle real model
      message rng := by
  have hmodelType := message_type_refines_initial message htype
  have hdecodeRel := decode_initial_refines_lifecycle message
  rw [hdecode] at hdecodeRel
  obtain ⟨encoded, hencoded, hidentityCall, hrepeat⟩ :=
    repeated_initial_agreement_checks_refine oracle dh codec K real model established decoded
      hrel hestablished hidentity hmodelSame
  have hdispatch := Model.Lifecycle.dispatchDecrypt_repeat oracle model
    (sliceOf message) (Tacenta.SessionUnitWireInitialT3.initialOf decoded)
    hmodelType hdecodeRel hrepeat
  let realFinal := { realNext with pending_initial := none }
  let modelFinal := { modelNext with pendingInitial := none }
  have hs : SessionRefines dh K realNext modelNext := by
    simpa [hmodelStep] using hstep.session
  have hfinal : SessionRefines dh K realFinal modelFinal := by
    exact ⟨hs.triple, hs.braid, hs.ratchetPrivate, hs.identityAd,
      hs.ourIdentityPublic, hs.peerIdentityPublic, rfl, hs.establishedEphemeral⟩
  have hmodel : Model.Lifecycle.decrypt view oracle model (sliceOf message) =
      { session := modelFinal, result := .ok modelPlaintext, oracle := oracleNext } := by
    simp [Model.Lifecycle.decrypt, hdispatch, hmodelStep, modelFinal]
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok (.Ok plaintext, realFinal, rngNext) := by
    simp [lifecycle.Session.decrypt, htype, hdecode, hestablished,
      hsameAgreement, hencoded, hidentityCall, hinner, realFinal,
      core.result.Result.Insts.CoreOpsTry.branch]
  exact ⟨(.Ok plaintext, realFinal, rngNext), hreal,
    by rw [hmodel]; exact ⟨by simpa [ResultRefines] using hbytes, hfinal, htrace⟩⟩

/-- Once the Braid send step is related, its terminal transition is committed
on both sides before `AgreementFailed` is returned.  This outer lifecycle fact
does not depend on the unused message, epoch or sparse output. -/
def initial_dispatch_repeat_success_from_premises
    {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key}
    {dh : DhView} {codec : DhCodecOf dh} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    (ctx : InitialDispatchContext rngCore cryptoRng trace dh K view oracle real model message rng)
    (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial)
    (plaintext : alloc.vec.Vec Std.U8) (modelPlaintext : Bytes)
    (realNext : lifecycle.Session) (modelNext : Model.Lifecycle.Session)
    (htraceNext : trace rngNext = oracleNext.draws)
    (hdecode : tacenta_wire.decode_initial message = ok (core.result.Result.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (hephemeral : vecOf established = vecOf decoded.ephemeral)
    (hidentity : vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public))
    (hsameAgreement : lifecycle.same_ephemeral_agreement real.ratchet_private
      established.deref decoded.ephemeral.deref = ok true)
    (hmodelSame : Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
      (vecOf established) (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val) = true)
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref decoded.message) rng = ok (.Ok plaintext, realNext, rngNext))
    (hmodelStep : Model.Lifecycle.decryptRatchet view oracle model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage =
      { session := modelNext, result := .ok modelPlaintext, oracle := oracleNext })
    (hbytes : vecOf plaintext = modelPlaintext)
    (hstep : StepRefines trace dh K (.Ok plaintext, realNext, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage)) :
    InitialDispatchRoute rngCore cryptoRng trace dh K view oracle real model message rng := by
  refine InitialDispatchRoute.repeatSuccess established decoded plaintext realNext rngNext
    hdecode hestablished hidentity hsameAgreement hinner ?_
  exact decrypt_initial_repeat_success_exact rngCore cryptoRng trace dh codec K view oracle oracleNext
    real model message rng rngNext established decoded plaintext modelPlaintext realNext modelNext
    ctx.hrel htraceNext ctx.htype hdecode hestablished hephemeral hidentity hsameAgreement
    hmodelSame hinner hmodelStep hbytes
    hstep

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

theorem encrypt_braid_failure_of_no_draw_send
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng rngNext : R)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output)
    (realBraidNext : tacenta_braid.Braid)
    (hkem : oracle.braidKem = K)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hsendReal : tacenta_braid.Braid.send rngCore cryptoRng real.braid rng =
      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
    (hnoDraw : Model.Lifecycle.braidSendNeedsDraw model.braid = false)
    (hpost : ∃ rand,
      (∀ modelMessage,
        (Model.Braid.send K rand model.braid).1 = some modelMessage →
          Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage) ∧
      realEpoch.val = (Model.Braid.send K rand model.braid).2.2.2.epoch - 1 ∧
      Tacenta.SessionUnitBraidT3.OptionOutputRefines realOutput
        (Model.Braid.send K rand model.braid).2.2.1 ∧
      Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state
        (Model.Braid.send K rand model.braid).2.2.2)
    (hfailed : ∀ modelNext : Model.Braid.BraidState,
      Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state modelNext →
      Model.Lifecycle.braidFailed modelNext = true)
    (htrace : trace rngNext = oracle.draws) :
    ∃ output,
      lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext)) := by
  obtain ⟨modelMessage, modelEpoch, modelOutput, modelBraidNext,
      hsendModel, hmessage, hepoch, houtput, hnext⟩ :=
    braid_send_model_result_of_no_draw (R := R) oracle model.braid hkem realMessage realEpoch
      realOutput realBraidNext hnoDraw hpost
  exact encrypt_braid_failure_step_refines rngCore cryptoRng trace dh K view oracle
    oracle real model plaintext rng rngNext realMessage realEpoch realOutput
    realBraidNext modelMessage modelEpoch modelOutput modelBraidNext hrel hready
    hsendReal hsendModel hnext (hfailed modelBraidNext hnext) htrace

theorem encrypt_braid_failure_of_draw_send
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng rngNext : R)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output)
    (realBraidNext : tacenta_braid.Braid)
    (hkem : oracle.braidKem = K)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hsendReal : tacenta_braid.Braid.send rngCore cryptoRng real.braid rng =
      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
    (htrace : trace rng = oracle.draws)
    (hdraw : ∃ draws rest, draws.length = Model.Lifecycle.braidSendDrawCount model.braid ∧
      trace rng = draws ++ rest ∧ trace rngNext = rest)
    (hneedsDraw : Model.Lifecycle.braidSendNeedsDraw model.braid = true)
    (hpost : ∀ draws rest, draws.length = Model.Lifecycle.braidSendDrawCount model.braid →
      trace rng = draws ++ rest → ∃ rand,
      rand = Model.Lifecycle.braidRandomness draws.flatten ∧
      (∀ modelMessage,
        (Model.Braid.send K rand model.braid).1 = some modelMessage →
          Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage) ∧
      realEpoch.val = (Model.Braid.send K rand model.braid).2.2.2.epoch - 1 ∧
      Tacenta.SessionUnitBraidT3.OptionOutputRefines realOutput
        (Model.Braid.send K rand model.braid).2.2.1 ∧
      Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state
        (Model.Braid.send K rand model.braid).2.2.2)
    (hfailed : ∀ modelNext : Model.Braid.BraidState,
      Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state modelNext →
      Model.Lifecycle.braidFailed modelNext = true) :
    ∃ output,
      lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext)) := by
  obtain ⟨draws, rest, modelMessage, modelEpoch, modelOutput, modelBraidNext,
      hcount, hhead, htail, hsendModel, hmessage, hepoch, houtput, hnext⟩ :=
    braid_send_model_result_of_draw (R := R) trace oracle model.braid hkem
      realMessage realEpoch realOutput realBraidNext rng rngNext
      htrace hdraw hneedsDraw hpost
  exact encrypt_braid_failure_step_refines rngCore cryptoRng trace dh K view oracle
    ({ oracle with draws := rest }) real model plaintext rng rngNext realMessage
    realEpoch realOutput realBraidNext modelMessage modelEpoch modelOutput
    modelBraidNext hrel hready hsendReal hsendModel hnext
    (hfailed modelBraidNext hnext) htail

/-! Contract-backed wrappers for the two Braid refusal shapes.  These are the
    public callers' entry points: the model send postcondition is obtained
    from the generated implementation theorem above, while the lifecycle
    refusal proof remains the same result-indexed leaf. -/
theorem encrypt_braid_failure_of_no_draw_contracts
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng rngNext : R)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output)
    (realBraidNext : tacenta_braid.Braid)
    (contracts : BraidSendRefinementContracts rngCore K)
    (hlive : Tacenta.SessionUnitBraidT3.EncodersLive model.braid)
    (hkem : oracle.braidKem = K)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hsendReal : tacenta_braid.Braid.send rngCore cryptoRng real.braid rng =
      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
    (hnoDraw : Model.Lifecycle.braidSendNeedsDraw model.braid = false)
    (hfailed : ∀ modelNext : Model.Braid.BraidState,
      Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state modelNext →
      Model.Lifecycle.braidFailed modelNext = true)
    (htrace : trace rngNext = oracle.draws) :
    ∃ output,
      lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext)) := by
  apply encrypt_braid_failure_of_no_draw_send rngCore cryptoRng trace dh K view oracle
    real model plaintext rng rngNext realMessage realEpoch realOutput realBraidNext hkem hrel
    hready hsendReal hnoDraw
  · exact braid_send_post_of_contracts contracts real.braid rng hrel.braid hlive hsendReal
  · exact hfailed
  · exact htrace

/-! Public no-draw Braid-failure composition.  The implementation result is
    obtained from the generated T1 totality theorem, the model successor from
    the T3 refinement adapter, and the existing leaf proves the committed
    failed-Braid state and unchanged plaintext-side data. -/
theorem public_encrypt_braid_failure_no_draw_of_contracts
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng : R)
    (contracts : BraidSendRefinementContracts rngCore K)
    (hlive : Tacenta.SessionUnitBraidT3.EncodersLive model.braid)
    (hkem : oracle.braidKem = K)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (htrace : trace rng = oracle.draws)
    (hnoDraw : Model.Lifecycle.braidSendNeedsDraw model.braid = false)
    (hfailed : ∀ modelNext : Model.Braid.BraidState,
      ∀ realBraidNext : tacenta_braid.Braid,
      Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state modelNext →
      Model.Lifecycle.braidFailed modelNext = true)
    (htraceNext : ∀ (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
      (realOutput : Option tacenta_braid.Output) (realBraidNext : tacenta_braid.Braid)
      (rngNext : R),
      tacenta_braid.Braid.send rngCore cryptoRng real.braid rng =
        ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext) →
      trace rngNext = oracle.draws) :
    PublicEncryptWitness rngCore cryptoRng trace dh K view oracle real model plaintext rng := by
  obtain ⟨result, rngNext, hsend⟩ := braid_send_result_of_contracts contracts real.braid rng
  rcases result with ⟨realMessage, realEpoch, realOutput, realBraidNext⟩
  have htraceNext' := htraceNext realMessage realEpoch realOutput realBraidNext rngNext hsend
  exact encrypt_braid_failure_of_no_draw_contracts rngCore cryptoRng trace dh K view oracle
    real model plaintext rng rngNext realMessage realEpoch realOutput realBraidNext contracts
    hlive hkem hrel hready hsend hnoDraw
    (fun modelNext hnext => hfailed modelNext realBraidNext hnext) htraceNext'

/-! The draw-consuming Braid-failure route uses the same implementation-result
    constructor, while keeping the ordered trace-head/tail and model
    randomness equality as explicit inputs. -/
theorem public_encrypt_braid_failure_draw_of_contracts
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng : R)
    (contracts : BraidSendRefinementContracts rngCore K)
    (hkem : oracle.braidKem = K)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (htrace : trace rng = oracle.draws)
    (hneedsDraw : Model.Lifecycle.braidSendNeedsDraw model.braid = true)
    (hdraw : ∀ result rngNext,
      tacenta_braid.Braid.send rngCore cryptoRng real.braid rng = ok (result, rngNext) →
      ∃ draws rest, draws.length = Model.Lifecycle.braidSendDrawCount model.braid ∧
        trace rng = draws ++ rest ∧ trace rngNext = rest)
    (hpost : ∀ (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
      (realOutput : Option tacenta_braid.Output) (realBraidNext : tacenta_braid.Braid),
      ∀ draws rest, draws.length = Model.Lifecycle.braidSendDrawCount model.braid →
      trace rng = draws ++ rest → ∃ rand,
      rand = Model.Lifecycle.braidRandomness draws.flatten ∧
      (∀ modelMessage,
        (Model.Braid.send K rand model.braid).1 = some modelMessage →
          Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage) ∧
      realEpoch.val = (Model.Braid.send K rand model.braid).2.2.2.epoch - 1 ∧
      Tacenta.SessionUnitBraidT3.OptionOutputRefines realOutput
        (Model.Braid.send K rand model.braid).2.2.1 ∧
      Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state
        (Model.Braid.send K rand model.braid).2.2.2)
    (hfailed : ∀ modelNext : Model.Braid.BraidState,
      ∀ realBraidNext : tacenta_braid.Braid,
      Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state modelNext →
      Model.Lifecycle.braidFailed modelNext = true) :
    PublicEncryptWitness rngCore cryptoRng trace dh K view oracle real model plaintext rng := by
  obtain ⟨result, rngNext, hsend⟩ := braid_send_result_of_contracts contracts real.braid rng
  rcases result with ⟨realMessage, realEpoch, realOutput, realBraidNext⟩
  obtain ⟨draws, rest, hcount, hhead, htail⟩ := hdraw _ _ hsend
  let hpost' : ∀ draws rest, draws.length = Model.Lifecycle.braidSendDrawCount model.braid →
      trace rng = draws ++ rest → ∃ rand,
      rand = Model.Lifecycle.braidRandomness draws.flatten ∧
      (∀ modelMessage,
        (Model.Braid.send K rand model.braid).1 = some modelMessage →
          Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage) ∧
      realEpoch.val = (Model.Braid.send K rand model.braid).2.2.2.epoch - 1 ∧
      Tacenta.SessionUnitBraidT3.OptionOutputRefines realOutput
        (Model.Braid.send K rand model.braid).2.2.1 ∧
      Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state
        (Model.Braid.send K rand model.braid).2.2.2 := by
    intro draws' rest' hcount' hhead'
    obtain ⟨rand', hrand', hmsg', hepoch', houtput', hnext'⟩ :=
      hpost realMessage realEpoch realOutput realBraidNext draws' rest' hcount' hhead'
    exact ⟨rand', hrand', hmsg', hepoch', houtput', hnext'⟩
  exact encrypt_braid_failure_of_draw_send rngCore cryptoRng trace dh K view oracle
    real model plaintext rng rngNext realMessage realEpoch realOutput realBraidNext hkem hrel
    hready hsend htrace ⟨draws, rest, hcount, hhead, htail⟩ hneedsDraw hpost'
    (fun modelNext hnext => hfailed modelNext realBraidNext hnext)

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

/-- The two implementation shapes that can produce a successful Triple send. -/
inductive RealTripleSuccess (state : tacenta_triple.State) (epoch : Std.U64)
    (output : Option tacenta_braid.Output) (candidate : tacenta_triple.State)
    (header : tacenta_triple.Header) (mk : Array Std.U8 32#usize) : Prop where
  | none
      (hout : output = none)
      (hsend : lifecycle.send_candidate state epoch none =
        ok (candidate, .Ok (header, mk)))
  | some (realOutput : tacenta_braid.Output) (converted : tacenta_spqr.Output)
      (hout : output = some realOutput)
      (hconverted : tacenta_spqr.Output.new realOutput.key_epoch realOutput.key = ok converted)
      (hsend : lifecycle.send_candidate state epoch (some converted) =
        ok (candidate, .Ok (header, mk)))

/-- The two translated shapes for converting an optional Braid output before
the receive-side DH work. -/
inductive RealSparseConversion (output : Option tacenta_braid.Output) :
    Option tacenta_spqr.Output → Prop where
  | none (hout : output = none) : RealSparseConversion output none
  | some (realOutput : tacenta_braid.Output) (sparseOutput : tacenta_spqr.Output)
      (hout : output = some realOutput)
      (hconverted : tacenta_spqr.Output.new realOutput.key_epoch realOutput.key =
        ok sparseOutput) : RealSparseConversion output (some sparseOutput)

/-! A concrete Braid-to-sparse conversion preserves exactly the model output
    already fixed by `OptionOutputRefines`.  This closes the small but
    important gap between the generated conversion call and the Triple
    model's input: a later route provider cannot choose a different sparse
    output for the same generated Braid result. -/
theorem sparse_output_of_conversion
    {realOutput : Option tacenta_braid.Output}
    {sparseOutput : Option tacenta_spqr.Output}
    {modelOutput : Option Model.Braid.Output}
    (hout : Tacenta.SessionUnitBraidT3.OptionOutputRefines realOutput modelOutput)
    (hsparse : RealSparseConversion realOutput sparseOutput) :
    Model.Lifecycle.sparseOutputOf modelOutput =
      sparseOutput.map Tacenta.SessionUnitTripleT3.spqrOutputOf := by
  cases hsparse with
  | none hnone =>
      subst realOutput
      cases modelOutput <;>
        simp [Tacenta.SessionUnitBraidT3.OptionOutputRefines,
          Model.Lifecycle.sparseOutputOf] at hout ⊢
  | some real converted hsome hconverted =>
      subst realOutput
      cases modelOutput with
      | none =>
          simp [Tacenta.SessionUnitBraidT3.OptionOutputRefines] at hout
      | some model =>
          have hconverted' : converted =
              { key_epoch := real.key_epoch, key := real.key } := by
            exact Result.ok.inj (hconverted.symm.trans (by
              simp [tacenta_spqr.Output.new]))
          subst converted
          rcases hout with ⟨hepoch, hkey⟩
          simp [Model.Lifecycle.sparseOutputOf,
            Tacenta.SessionUnitTripleT3.spqrOutputOf,
            Tacenta.SessionUnitBraidT3.keyOf,
            Tacenta.SessionUnitTripleT3.keyOf] at hkey ⊢
          exact ⟨hepoch.symm, hkey.symm⟩

theorem real_triple_refusal_of_exact_candidate
    {state : tacenta_triple.State} {epoch : Std.U64}
    {output : Option tacenta_braid.Output} {sparseOutput : Option tacenta_spqr.Output}
    {candidate : tacenta_triple.State} {reason : tacenta_triple.TripleError}
    (hsparse : RealSparseConversion output sparseOutput)
    (hsend : lifecycle.send_candidate state epoch sparseOutput =
      ok (candidate, .Err reason)) :
    RealTripleRefusal state epoch output candidate reason := by
  cases hsparse with
  | none hout =>
      exact .none hout hsend
  | some realOutput converted hout hconverted =>
      exact .some realOutput converted hout hconverted hsend

theorem real_triple_success_of_exact_candidate
    {state : tacenta_triple.State} {epoch : Std.U64}
    {output : Option tacenta_braid.Output} {sparseOutput : Option tacenta_spqr.Output}
    {candidate : tacenta_triple.State} {header : tacenta_triple.Header}
    {mk : Array Std.U8 32#usize}
    (hsparse : RealSparseConversion output sparseOutput)
    (hsend : lifecycle.send_candidate state epoch sparseOutput =
      ok (candidate, .Ok (header, mk))) :
    RealTripleSuccess state epoch output candidate header mk := by
  cases hsparse with
  | none hout =>
      exact .none hout hsend
  | some realOutput converted hout hconverted =>
      exact .some realOutput converted hout hconverted hsend

/-- A non-contributory first DH agreement is an atomic receive refusal.  Braid
and its optional sparse output have been evaluated, but neither candidate is
committed and no random draw has occurred. -/
theorem decrypt_ratchet_first_dh_refusal_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (codec : DhCodecOf dh)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (decoded : tacenta_wire.DecodedMessage)
    (modelComposite : Model.CompositeHeader.Composite)
    (realBraidMessage : tacenta_braid.Msg) (receivedEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output)
    (realBraidCandidate : tacenta_braid.Braid)
    (realSparseOutput : Option tacenta_spqr.Output)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Ok decoded))
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf decoded.ciphertext))
    (hcomposite : CompositeRefines decoded.header modelComposite)
    (hmessageCall : lifecycle.msg_of decoded.header = ok realBraidMessage)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines realBraidMessage
      (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hreceive : tacenta_braid.Braid.receive real.braid realBraidMessage =
      ok (receivedEpoch, realOutput, realBraidCandidate))
    (hsparse : RealSparseConversion realOutput realSparseOutput)
    (hmodelDhNone : oracle.dhAgree model.ratchetPrivate modelComposite.dh = none) :
    lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Handshake SessionError.NonContributoryAgreement), real, rng) ∧
    StepRefines trace dh K
      (.Err (.Handshake SessionError.NonContributoryAgreement), real, rng)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  have hrealReady := braid_failed_refines K real.braid model.braid hrel.braid
  have hmodelReady : Model.Lifecycle.braidFailed model.braid = false := by
    cases hb : model.braid <;>
      simp [Model.Lifecycle.agreementFailed, Model.Lifecycle.braidFailed, hb] at hready ⊢
  rw [hmodelReady] at hrealReady
  obtain ⟨peer, hpeerCall, hpeerValue⟩ := codec.fromBytes decoded.header.dh
  obtain ⟨agreement, hagreementCall, hagreementValue⟩ :=
    oracleOf.dhAgree real.ratchet_private peer
  have hagreementNone : agreement = none := by
    rw [hrel.ratchetPrivate, hpeerValue, hcomposite.dh, hmodelDhNone] at hagreementValue
    cases agreement <;> simp_all
  subst agreement
  have hreal : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Handshake SessionError.NonContributoryAgreement), real, rng) := by
    unfold lifecycle.Session.decrypt_ratchet
    cases hsparse with
    | none hout =>
        simp [hrealReady, hdecodeReal, hmessageCall, hreceive, hout, hpeerCall,
          hagreementCall]
    | some realSparse converted hout hconverted =>
        simp [hrealReady, hdecodeReal, hmessageCall, hreceive, hout, hconverted,
          hpeerCall, hagreementCall]
  have hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session := model,
        result := .error (.handshake .nonContributoryAgreement),
        oracle := oracle } := by
    simp [Model.Lifecycle.decryptRatchet, hready, hdecodeModel, hmodelDhNone]
  refine ⟨hreal, ?_⟩
  rw [hmodel]
  exact ⟨rfl, hrel, htrace⟩

/-- A non-contributory second DH agreement is also atomic, but the
candidate-private draw has already been consumed.  The returned session is the
original one while the oracle/RNG trace advances by exactly that draw. -/
theorem decrypt_ratchet_second_dh_refusal_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (codec : DhCodecOf dh)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (decoded : tacenta_wire.DecodedMessage)
    (modelComposite : Model.CompositeHeader.Composite)
    (realBraidMessage : tacenta_braid.Msg) (receivedEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output)
    (realBraidCandidate : tacenta_braid.Braid)
    (realSparseOutput : Option tacenta_spqr.Output)
    (draw modelDhOutRecv : Model.Lifecycle.Key)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Ok decoded))
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf decoded.ciphertext))
    (hcomposite : CompositeRefines decoded.header modelComposite)
    (hmessageCall : lifecycle.msg_of decoded.header = ok realBraidMessage)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines realBraidMessage
      (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hreceive : tacenta_braid.Braid.receive real.braid realBraidMessage =
      ok (receivedEpoch, realOutput, realBraidCandidate))
    (hsparse : RealSparseConversion realOutput realSparseOutput)
    (hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
      some modelDhOutRecv)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hmodelSecond : oracle.dhAgree draw modelComposite.dh = none) :
    ∃ rngAfter,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
        ok (.Err (.Handshake SessionError.NonContributoryAgreement), real, rngAfter) ∧
      StepRefines trace dh K
        (.Err (.Handshake SessionError.NonContributoryAgreement), real, rngAfter)
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  have hrealReady := braid_failed_refines K real.braid model.braid hrel.braid
  have hmodelReady : Model.Lifecycle.braidFailed model.braid = false := by
    cases hb : model.braid <;>
      simp [Model.Lifecycle.agreementFailed, Model.Lifecycle.braidFailed, hb] at hready ⊢
  rw [hmodelReady] at hrealReady
  obtain ⟨peer, hpeerCall, hpeerValue⟩ := codec.fromBytes decoded.header.dh
  obtain ⟨firstAgreement, hfirstCall, hfirstValue⟩ :=
    oracleOf.dhAgree real.ratchet_private peer
  have hfirstSome : ∃ secret, firstAgreement = some secret ∧
      arrayOf secret = modelDhOutRecv := by
    rw [hrel.ratchetPrivate, hpeerValue, hcomposite.dh, hmodelFirst] at hfirstValue
    cases firstAgreement with
    | none => simp at hfirstValue
    | some secret =>
        refine ⟨secret, rfl, ?_⟩
        simpa using hfirstValue
  obtain ⟨secret, rfl, hsecretValue⟩ := hfirstSome
  let inst32 := Array.Insts.ZeroizeZeroize 32#usize
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
  obtain ⟨wrappedSecret, hwrapSecret, hderefSecret⟩ :=
    zeroizing_roundtrip hz32 inst32 secret
  have hdrawTrace : ∃ rest, trace rng = draw :: rest ∧ oracleNext.draws = rest := by
    cases hd : oracle.draws with
    | nil => simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hd] at hmodelDraw
    | cons head rest =>
        simp only [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hd,
          Option.some.injEq, Prod.mk.injEq] at hmodelDraw
        obtain ⟨rfl, rfl⟩ := hmodelDraw
        exact ⟨rest, by simpa [htrace, hd], rfl⟩
  obtain ⟨rest, htraceDraw, horacleNextDraws⟩ := hdrawTrace
  obtain ⟨candidateBytes, realRngNext, hrandomCall, hcandidateBytes,
      hrealTraceNext⟩ := oracleOf.random32 rng draw rest htraceDraw
  obtain ⟨candidatePrivate, hcandidateCall, hcandidateValue⟩ :=
    codec.privateFromBytes candidateBytes
  have hcandidateDraw : dh.privateKey candidatePrivate = draw := by
    rw [hcandidateValue, hcandidateBytes]
  obtain ⟨secondAgreement, hsecondCall, hsecondValue⟩ :=
    oracleOf.dhAgree candidatePrivate peer
  have hsecondNone : secondAgreement = none := by
    rw [hcandidateDraw, hpeerValue, hcomposite.dh, hmodelSecond] at hsecondValue
    cases secondAgreement <;> simp_all
  subst secondAgreement
  have hreal : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Handshake SessionError.NonContributoryAgreement), real, realRngNext) := by
    unfold lifecycle.Session.decrypt_ratchet
    cases hsparse with
    | none hout =>
        simp [hrealReady, hdecodeReal, hmessageCall, hreceive, hout, hpeerCall,
          hfirstCall, hwrapSecret, hderefSecret, hrandomCall, hcandidateCall,
          hsecondCall, inst32]
    | some realSparse converted hout hconverted =>
        simp [hrealReady, hdecodeReal, hmessageCall, hreceive, hout, hconverted,
          hpeerCall, hfirstCall, hwrapSecret, hderefSecret, hrandomCall,
          hcandidateCall, hsecondCall, inst32]
  have hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session := model,
        result := .error (.handshake .nonContributoryAgreement),
        oracle := oracleNext } := by
    simp [Model.Lifecycle.decryptRatchet, hready, hdecodeModel, hmodelFirst,
      hmodelDraw, hmodelSecond]
  refine ⟨realRngNext, hreal, ?_⟩
  rw [hmodel]
  exact ⟨rfl, hrel, by simpa [horacleNextDraws] using hrealTraceNext⟩

/-- Once both DH agreements and the candidate public key are related,
a Triple receive refusal discards the Braid, Triple and ratchet-private
candidates.  Only the already-consumed candidate-key draw is committed. -/
theorem decrypt_ratchet_triple_refusal_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (decoded : tacenta_wire.DecodedMessage)
    (modelComposite : Model.CompositeHeader.Composite)
    (realBraidMessage : tacenta_braid.Msg) (receivedEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output)
    (realBraidCandidate : tacenta_braid.Braid)
    (realSparseOutput : Option tacenta_spqr.Output)
    (peer : tacenta_boundary.dh.PublicKeyBytes)
    (recvSecret sendSecret candidateBytes newPublicBytes before : Array Std.U8 32#usize)
    (candidatePrivate : tacenta_boundary.dh.PrivateKey)
    (candidatePublic : tacenta_boundary.dh.PublicKeyBytes)
    (realHeader : tacenta_triple.Header)
    (wrappedRecv wrappedSend : zeroize.Zeroizing (Array Std.U8 32#usize))
    (realReason : tacenta_triple.TripleError)
    (modelReason : Model.Triple.ReceiveRefusal)
    (draw modelDhOutRecv modelDhOutSend : Model.Lifecycle.Key)
    (hrel : SessionRefines dh K real model)
    (htraceNext : trace rngNext = oracleNext.draws)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Ok decoded))
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf decoded.ciphertext))
    (hmessageCall : lifecycle.msg_of decoded.header = ok realBraidMessage)
    (hreceive : tacenta_braid.Braid.receive real.braid realBraidMessage =
      ok (receivedEpoch, realOutput, realBraidCandidate))
    (hsparse : RealSparseConversion realOutput realSparseOutput)
    (hpeerCall : tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer)
    (hfirstCall : tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer =
      ok (some recvSecret))
    (hwrapRecv : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret =
      ok wrappedRecv)
    (hderefRecv : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv =
      ok recvSecret)
    (hrandomCall : lifecycle.random_secret rngCore cryptoRng rng =
      ok (candidateBytes, rngNext))
    (hcandidateCall : tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes =
      ok candidatePrivate)
    (hsecondCall : tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer =
      ok (some sendSecret))
    (hwrapSend : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret =
      ok wrappedSend)
    (hderefSend : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend =
      ok sendSecret)
    (hbeforeCall : tacenta_triple.State.sending_public real.triple = ok before)
    (hheaderCall : lifecycle.triple_header_of decoded.header = ok realHeader)
    (hpublicCall : tacenta_boundary.dh.PrivateKey.public_key candidatePrivate =
      ok candidatePublic)
    (hpublicBytesCall : tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic =
      ok newPublicBytes)
    (htripleReal : lifecycle.receive_with_eviction real.triple decoded.header realHeader
      recvSecret sendSecret newPublicBytes realSparseOutput = ok (.Err realReason))
    (hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
      some modelDhOutRecv)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hmodelSecond : oracle.dhAgree draw modelComposite.dh = some modelDhOutSend)
    (hmodelPublic : oracle.dhPublic draw = arrayOf newPublicBytes)
    (hmodelTriple : Model.Lifecycle.receiveWithEviction model.triple modelComposite
      (Model.Lifecycle.tripleHeaderOf modelComposite) modelDhOutRecv modelDhOutSend
      (oracle.dhPublic draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1) =
        .error modelReason)
    (hreason : tripleReceiveRefusalOfReal realReason = some modelReason) :
    lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Triple realReason), real, rngNext) ∧
    StepRefines trace dh K
      (.Err (.Triple realReason), real, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  have hrealReady := braid_failed_refines K real.braid model.braid hrel.braid
  have hmodelReady : Model.Lifecycle.braidFailed model.braid = false := by
    cases hb : model.braid <;>
      simp [Model.Lifecycle.agreementFailed, Model.Lifecycle.braidFailed, hb] at hready ⊢
  rw [hmodelReady] at hrealReady
  have hreal : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Triple realReason), real, rngNext) := by
    unfold lifecycle.Session.decrypt_ratchet
    cases hsparse with
    | none hout =>
        simp [hrealReady, hdecodeReal, hmessageCall, hreceive, hout, hpeerCall,
          hfirstCall, hwrapRecv, hderefRecv, hrandomCall, hcandidateCall,
          hsecondCall, hwrapSend, hderefSend, hbeforeCall, hheaderCall,
          hpublicCall, hpublicBytesCall, htripleReal]
    | some realSparse converted hout hconverted =>
        simp [hrealReady, hdecodeReal, hmessageCall, hreceive, hout, hconverted,
          hpeerCall, hfirstCall, hwrapRecv, hderefRecv, hrandomCall,
          hcandidateCall, hsecondCall, hwrapSend, hderefSend, hbeforeCall,
          hheaderCall, hpublicCall, hpublicBytesCall, htripleReal]
  have hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session := model,
        result := .error (Model.Lifecycle.tripleReceiveRefusalOf modelReason),
        oracle := oracleNext } := by
    have hmodelTriple' := hmodelTriple
    rw [hmodelPublic] at hmodelTriple'
    simp [Model.Lifecycle.decryptRatchet, hready, hdecodeModel, hmodelFirst,
      hmodelDraw, hmodelSecond, hmodelPublic, hmodelTriple']
  refine ⟨hreal, ?_⟩
  rw [hmodel]
  exact ⟨tripleReceiveRefusalOfReal_sound hreason, hrel, htraceNext⟩

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

/-! Result-indexed Triple refusal composition.  The generated candidate result
    supplies `RealTripleRefusal` through the constructor above; the remaining
    model equation and refusal-code correspondence are indexed by the same
    Braid successor passed to the lifecycle leaf. -/
theorem encrypt_triple_refusal_of_exact_candidate
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng rngNext : R)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output)
    (realBraidNext : tacenta_braid.Braid) (candidate : tacenta_triple.State)
    (sparseOutput : Option tacenta_spqr.Output)
    (realReason : tacenta_triple.TripleError)
    (modelMessage : Model.Braid.Msg) (modelEpoch : Nat)
    (modelOutput : Option Model.Braid.Output)
    (modelBraidNext : Model.Braid.BraidState)
    (modelReason : Model.Triple.SendRefusal)
    (hsparse : RealSparseConversion realOutput sparseOutput)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hsendReal : tacenta_braid.Braid.send rngCore cryptoRng real.braid rng =
      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
    (hsendCandidate : lifecycle.send_candidate real.triple realEpoch sparseOutput =
      ok (candidate, .Err realReason))
    (hsendModel : Model.Lifecycle.sendAgreement oracle model.braid =
      some ((some modelMessage, modelEpoch, modelOutput, modelBraidNext), oracleNext))
    (hnext : Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state modelBraidNext)
    (hnotFailed : Model.Lifecycle.braidFailed modelBraidNext = false)
    (htripleModel : Model.Triple.sendDetailed model.triple modelEpoch
      (Model.Lifecycle.sparseOutputOf modelOutput) = .error modelReason)
    (hreason : tripleSendRefusalOfReal realReason = some modelReason)
    (htrace : trace rngNext = oracleNext.draws) :
    ∃ output,
      lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext)) := by
  exact encrypt_triple_refusal_step_refines rngCore cryptoRng trace dh K view oracle oracleNext
    real model plaintext rng rngNext realMessage realEpoch realOutput realBraidNext candidate
    realReason modelMessage modelEpoch modelOutput modelBraidNext modelReason hrel hready
    hsendReal (real_triple_refusal_of_exact_candidate hsparse hsendCandidate) hsendModel hnext
    hnotFailed htripleModel hreason htrace

/-! Contract-backed public Triple-refusal route.  The generated candidate
    result determines both the model refusal and its exact public-error map. -/
theorem public_encrypt_triple_refusal_of_contracts
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng rngNext : R)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output)
    (realBraidNext : tacenta_braid.Braid) (candidate : tacenta_triple.State)
    (sparseOutput : Option tacenta_spqr.Output)
    (realReason : tacenta_triple.TripleError)
    (modelMessage : Model.Braid.Msg) (modelEpoch : Nat)
    (modelOutput : Option Model.Braid.Output)
    (modelBraidNext : Model.Braid.BraidState)
    (contracts : TripleSendRefinementContracts)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hroom : model.triple.postQuantum.chains.length + 1 < Usize.max)
    (hcb : ∀ p ∈ model.triple.postQuantum.chains,
      p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ model.triple.postQuantum.skipped,
      sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, sparseOutput = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hepoch : model.triple.postQuantum.epoch + 1 < Std.U64.max)
    (hcounter : ∀ p ∈ model.triple.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max)
    (hsparse : RealSparseConversion realOutput sparseOutput)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hsendReal : tacenta_braid.Braid.send rngCore cryptoRng real.braid rng =
      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
    (hsendCandidate : lifecycle.send_candidate real.triple realEpoch sparseOutput =
      ok (candidate, .Err realReason))
    (hsendModel : Model.Lifecycle.sendAgreement oracle model.braid =
      some ((some modelMessage, modelEpoch, modelOutput, modelBraidNext), oracleNext))
    (hnext : Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state modelBraidNext)
    (hnotFailed : Model.Lifecycle.braidFailed modelBraidNext = false)
    (hmodelOf : ∀ modelReason,
      Model.Triple.sendDetailed model.triple realEpoch.val
        (Option.map Tacenta.SessionUnitTripleT3.spqrOutputOf sparseOutput) =
          .error modelReason →
      Model.Triple.sendDetailed model.triple modelEpoch
        (Model.Lifecycle.sparseOutputOf modelOutput) = .error modelReason)
    (htrace : trace rngNext = oracleNext.draws) :
    PublicEncryptWitness rngCore cryptoRng trace dh K view oracle real model plaintext rng := by
  obtain ⟨modelReason, htripleModel, hreason⟩ :=
    triple_refusal_evidence_of_exact_candidate_and_contracts contracts hrel.triple
      realEpoch sparseOutput hroom hcb hsb hnewb hepoch hcounter hsendCandidate
  have htripleModel' := hmodelOf modelReason htripleModel
  exact encrypt_triple_refusal_of_exact_candidate rngCore cryptoRng trace dh K view oracle
    oracleNext real model plaintext rng rngNext realMessage realEpoch realOutput realBraidNext
    candidate sparseOutput realReason modelMessage modelEpoch modelOutput modelBraidNext
    modelReason hsparse hrel hready hsendReal hsendCandidate hsendModel hnext hnotFailed
    htripleModel' hreason htrace

attribute [-step] Tacenta.SessionUnitErasureT1.extend_slice32_spec

private theorem beByte64_eq (v : BitVec 64) (i : Nat) (hi : i < 8) :
    v.toBEBytes[i]! = (v >>> (8 * (7 - i))).setWidth 8 := by
  rw [BitVec.eq_iff]
  intro j hj
  have hlen : v.toLEBytes.length = 8 := by simp [BitVec.toLEBytes_length]
  have hib : i < v.toBEBytes.length := by simp [BitVec.toBEBytes_length]; omega
  have hb : 7 - i < v.toLEBytes.length := by omega
  have hrw : v.toBEBytes[i]! = v.toLEBytes[7 - i]! := by
    rw [← List.Inhabited_getElem_eq_getElem! v.toBEBytes i hib]
    unfold BitVec.toBEBytes
    rw [List.getElem_reverse]
    simp only [hlen]
    exact List.Inhabited_getElem_eq_getElem! v.toLEBytes (7 - i) hb
  have hbit := BitVec.toLEBytes_getElem!_testBit v (7 - i) j hj
  simp only [Byte.testBit, BitVec.getElem!_eq_testBit_toNat] at hbit
  rw [hrw, BitVec.getElem!_setWidth 8 _ j hj, BitVec.getElem!_eq_testBit_toNat,
    BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ushiftRight, hbit,
    Nat.testBit_shiftRight]

private theorem beByte32_eq (v : BitVec 32) (i : Nat) (hi : i < 4) :
    v.toBEBytes[i]! = (v >>> (8 * (3 - i))).setWidth 8 := by
  rw [BitVec.eq_iff]
  intro j hj
  have hlen : v.toLEBytes.length = 4 := by simp [BitVec.toLEBytes_length]
  have hib : i < v.toBEBytes.length := by simp [BitVec.toBEBytes_length]; omega
  have hb : 3 - i < v.toLEBytes.length := by omega
  have hrw : v.toBEBytes[i]! = v.toLEBytes[3 - i]! := by
    rw [← List.Inhabited_getElem_eq_getElem! v.toBEBytes i hib]
    unfold BitVec.toBEBytes
    rw [List.getElem_reverse]
    simp only [hlen]
    exact List.Inhabited_getElem_eq_getElem! v.toLEBytes (3 - i) hb
  have hbit := BitVec.toLEBytes_getElem!_testBit v (3 - i) j hj
  simp only [Byte.testBit, BitVec.getElem!_eq_testBit_toNat] at hbit
  rw [hrw, BitVec.getElem!_setWidth 8 _ j hj, BitVec.getElem!_eq_testBit_toNat,
    BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ushiftRight, hbit,
    Nat.testBit_shiftRight]

private theorem beByte16_eq (v : BitVec 16) (i : Nat) (hi : i < 2) :
    v.toBEBytes[i]! = (v >>> (8 * (1 - i))).setWidth 8 := by
  rw [BitVec.eq_iff]
  intro j hj
  have hlen : v.toLEBytes.length = 2 := by simp [BitVec.toLEBytes_length]
  have hib : i < v.toBEBytes.length := by simp [BitVec.toBEBytes_length]; omega
  have hb : 1 - i < v.toLEBytes.length := by omega
  have hrw : v.toBEBytes[i]! = v.toLEBytes[1 - i]! := by
    rw [← List.Inhabited_getElem_eq_getElem! v.toBEBytes i hib]
    unfold BitVec.toBEBytes
    rw [List.getElem_reverse]
    simp only [hlen]
    exact List.Inhabited_getElem_eq_getElem! v.toLEBytes (1 - i) hb
  have hbit := BitVec.toLEBytes_getElem!_testBit v (1 - i) j hj
  simp only [Byte.testBit, BitVec.getElem!_eq_testBit_toNat] at hbit
  rw [hrw, BitVec.getElem!_setWidth 8 _ j hj, BitVec.getElem!_eq_testBit_toNat,
    BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ushiftRight, hbit,
    Nat.testBit_shiftRight]

private theorem u32_be_agrees (n : Std.U32) :
    List.map Tacenta.SessionUnitBraidT3.u8
        (List.map UScalar.mk n.bv.toBEBytes) =
      Model.Messages.be32 (UInt32.ofNat n.val) := by
  apply List.ext_getElem
  · simp [Model.Messages.be32, BitVec.toBEBytes_length]
  · intro i hleft hright
    have hi : i < 4 := by simpa [Model.Messages.be32] using hright
    have hib : i < n.bv.toBEBytes.length := by simp [BitVec.toBEBytes_length]; omega
    rw [List.getElem_map, List.getElem_map,
      ← getElem!_pos _ i hib, beByte32_eq n.bv i hi]
    interval_cases i <;>
      apply UInt8.toNat.inj <;>
      simp only [Tacenta.SessionUnitBraidT3.u8, Model.Messages.be32,
        List.getElem_cons_zero, List.getElem_cons_succ, UInt8.toNat_ofNat,
        UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.toNat_ofNat]
    all_goals simp only [UScalar.val, UInt8.toNat_ofNat,
      BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
    all_goals norm_num

private theorem u64_be_agrees (n : Std.U64) :
    List.map Tacenta.SessionUnitBraidT3.u8
        (List.map UScalar.mk n.bv.toBEBytes) =
      Model.CompositeHeader.be64 (UInt64.ofNat n.val) := by
  apply List.ext_getElem
  · simp [Model.CompositeHeader.be64, BitVec.toBEBytes_length]
  · intro i hleft hright
    have hi : i < 8 := by simpa [Model.CompositeHeader.be64] using hright
    have hib : i < n.bv.toBEBytes.length := by simp [BitVec.toBEBytes_length]; omega
    rw [List.getElem_map, List.getElem_map,
      ← getElem!_pos _ i hib,
      beByte64_eq n.bv i hi]
    interval_cases i <;>
      apply UInt8.toNat.inj <;>
      simp only [Tacenta.SessionUnitBraidT3.u8, Model.CompositeHeader.be64,
        List.getElem_cons_zero, List.getElem_cons_succ, UInt8.toNat_ofNat,
        UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat]
    all_goals simp only [UScalar.val, UInt8.toNat_ofNat,
      BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
    all_goals norm_num

private theorem u16_be_agrees (n : Std.U16) :
    List.map Tacenta.SessionUnitBraidT3.u8
        (List.map UScalar.mk n.bv.toBEBytes) =
      Model.CompositeHeader.be16 (UInt16.ofNat n.val) := by
  apply List.ext_getElem
  · simp [Model.CompositeHeader.be16, BitVec.toBEBytes_length]
  · intro i hleft hright
    have hi : i < 2 := by simpa [Model.CompositeHeader.be16] using hright
    have hib : i < n.bv.toBEBytes.length := by simp [BitVec.toBEBytes_length]; omega
    rw [List.getElem_map, List.getElem_map,
      ← getElem!_pos _ i hib, beByte16_eq n.bv i hi]
    interval_cases i <;>
      apply UInt8.toNat.inj <;>
      simp only [Tacenta.SessionUnitBraidT3.u8, Model.CompositeHeader.be16,
        List.getElem_cons_zero, List.getElem_cons_succ, UInt8.toNat_ofNat,
        UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, UInt16.toNat_ofNat]
    all_goals simp only [UScalar.val, UInt8.toNat_ofNat,
      BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
    all_goals norm_num

private theorem u32_be_agrees_map (n : Std.U32) :
    List.map (Tacenta.SessionUnitBraidT3.u8 ∘ UScalar.mk) n.bv.toBEBytes =
      Model.Messages.be32 (UInt32.ofNat n.val) := by
  simpa only [List.map_map] using u32_be_agrees n

private theorem u64_be_agrees_map (n : Std.U64) :
    List.map (Tacenta.SessionUnitBraidT3.u8 ∘ UScalar.mk) n.bv.toBEBytes =
      Model.CompositeHeader.be64 (UInt64.ofNat n.val) := by
  simpa only [List.map_map] using u64_be_agrees n

private theorem u16_be_agrees_map (n : Std.U16) :
    List.map (Tacenta.SessionUnitBraidT3.u8 ∘ UScalar.mk) n.bv.toBEBytes =
      Model.CompositeHeader.be16 (UInt16.ofNat n.val) := by
  simpa only [List.map_map] using u16_be_agrees n

private theorem braid_bytes_eq_wire_bytes (l : List Std.U8) :
    List.map Tacenta.SessionUnitBraidT3.u8 l =
      List.map SessionUnitWireT3.byteOf l := rfl

private theorem compositeOf_encode_length (real : tacenta_wire.Composite) :
    (Model.CompositeHeader.encode (SessionUnitWireT3.compositeOf real)).length = 102 := by
  cases hchunk : real.ag_chunk <;>
    simp [Model.CompositeHeader.encode, Model.CompositeHeader.encodeChunk,
      SessionUnitWireT3.compositeOf, SessionUnitWireT3.bytesOf,
      Model.CompositeHeader.chunkBytes, Model.Messages.be32,
      Model.CompositeHeader.be64, Model.CompositeHeader.be16, hchunk]

/-- A related model composite has the fixed wire-header width.  Exposing this
    consequence lets outer Session composition derive serializer headroom from
    the public input bound instead of asking a route provider to restate it. -/
theorem composite_encode_length_of_refines (real : tacenta_wire.Composite)
    (model : Model.CompositeHeader.Composite)
    (hrel : CompositeRefines real model) :
    (Model.CompositeHeader.encode model).length = 102 := by
  rw [← wire_compositeOf_eq real model hrel]
  exact compositeOf_encode_length real

private theorem cast_usize_u32_model (n : Usize) :
    UInt32.ofNat (UScalar.cast UScalarTy.U32 n).val = UInt32.ofNat n.val := by
  apply UInt32.toNat.inj
  unfold UScalar.cast
  change (BitVec.setWidth 32 n.bv).toNat % 2 ^ 32 = n.bv.toNat % 2 ^ 32
  rw [BitVec.toNat_setWidth]
  simp only [Nat.mod_mod]

private theorem setWidth32_usize_model (n : Usize) :
    UInt32.ofNat (BitVec.setWidth 32 n.bv).toNat = UInt32.ofNat n.val := by
  simpa only [UScalar.cast, UScalar.val, UScalarTy.U32_numBits_eq] using
    cast_usize_u32_model n

private theorem setWidth32_usize_scalar_model (n : Usize) :
    UInt32.ofNat (UScalar.mk (BitVec.setWidth 32 n.bv) : U32).val =
      UInt32.ofNat n.val := by
  simpa only [UScalar.val] using setWidth32_usize_model n

set_option maxHeartbeats 2000000 in
/-- Encoding a related shipping composite header produces exactly the model's
fixed-width header bytes. -/
theorem encode_composite_refines (real : tacenta_wire.Composite)
    (model : Model.CompositeHeader.Composite)
    (hrel : CompositeRefines real model) :
    tacenta_wire.encode_composite real ⦃ fun encoded =>
      vecOf encoded = Model.CompositeHeader.encode model ⦄ := by
  rw [← wire_compositeOf_eq real model hrel]
  unfold tacenta_wire.encode_composite
  step*
  all_goals (try simp_all [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
    Array.to_slice, Slice.length])
  all_goals (try scalar_tac)
  all_goals step*
  all_goals (try simp_all [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
    Array.to_slice, Slice.length])
  all_goals (try scalar_tac)
  all_goals cases htype : real.ag_type <;> cases hchunk : real.ag_chunk
  all_goals simp only [tacenta_wire.AgreementType.to_byte, pure]
  all_goals step*
  all_goals (try simp_all [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
    Array.to_slice, Slice.length])
  all_goals (try scalar_tac)
  all_goals step*
  all_goals (try simp_all [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
    Array.to_slice, Slice.length])
  all_goals (try scalar_tac)
  all_goals (try simp only [lift, WP.spec_ok])
  all_goals step*
  all_goals (try simp_all [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
    Array.to_slice, Slice.length])
  all_goals (try scalar_tac)
  all_goals (try simp only [lift, WP.spec_ok])
  all_goals step*
  all_goals (try simp_all [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
    Array.to_slice, Slice.length])
  all_goals (try scalar_tac)
  all_goals simp_all only [vecOf, List.map_cons, List.map_append, List.map_map]
  all_goals rw [u32_be_agrees_map real.pn, u32_be_agrees_map real.n,
    u64_be_agrees_map real.pq_epoch, u64_be_agrees_map real.pq_n,
    u64_be_agrees_map real.ag_epoch]
  all_goals (try rw [u16_be_agrees_map _])
  all_goals simp_all [vecOf, Model.CompositeHeader.encode,
    Model.CompositeHeader.encodeChunk, SessionUnitWireT3.compositeOf,
    SessionUnitWireT3.bytesOf, SessionUnitWireT3.byteOf,
    Tacenta.SessionUnitBraidT3.u8, u32_be_agrees_map, u64_be_agrees_map,
    u16_be_agrees_map, tacenta_wire.VERSION, tacenta_wire.TYPE_RATCHET,
    Model.Messages.version, Model.Messages.typeRatchet,
    Model.CompositeHeader.chunkBytes, Model.CompositeHeader.encodeAgreementType,
    SessionUnitWireT3.agTypeOf, Model.CompositeHeader.be16]
  all_goals rfl

/-- Appending the AEAD output to a related composite header produces exactly
the model ratchet-message encoding. -/
theorem encode_message_refines (real : tacenta_wire.Composite)
    (model : Model.CompositeHeader.Composite) (ciphertext : Slice Std.U8)
    (hrel : CompositeRefines real model)
    (hroom : 102 + ciphertext.val.length ≤ Usize.max) :
    serialization.encode_message real ciphertext ⦃ fun encoded =>
      vecOf encoded = Model.CompositeHeader.encodeMessage model
        (Tacenta.SessionUnitBraidT3.sliceOf ciphertext) ⦄ := by
  unfold serialization.encode_message
  step with encode_composite_refines real model hrel
  rw [← wire_compositeOf_eq real model hrel] at out_post ⊢
  step with Tacenta.SessionUnitSessionT1.extend_from_slice_spec out ciphertext (by
    have hlen : out.val.length = 102 := by
      have h := congrArg List.length out_post
      cases hchunk : real.ag_chunk <;>
        simp [vecOf, Model.CompositeHeader.encode,
          Model.CompositeHeader.encodeChunk, SessionUnitWireT3.compositeOf,
          SessionUnitWireT3.bytesOf, Model.CompositeHeader.chunkBytes,
          hchunk] at h
      · exact h
      · exact h
    omega)
  have hencoded : vecOf encoded = vecOf out ++
      Tacenta.SessionUnitBraidT3.sliceOf ciphertext := by
    simp [vecOf, Tacenta.SessionUnitBraidT3.sliceOf, encoded_post,
      List.map_append]
  rw [hencoded, out_post]
  rfl

/-- Associated data is framed by its four-byte length and followed by the
exact shipping composite header, matching the lifecycle model. -/
theorem concat_ad_refines (ad : Slice Std.U8)
    (real : tacenta_wire.Composite) (model : Model.CompositeHeader.Composite)
    (hrel : CompositeRefines real model)
    (hroom : ad.val.length + 106 ≤ Usize.max) :
    serialization.concat_ad ad real ⦃ fun encoded =>
      vecOf encoded = Model.Messages.concatAd
        (Tacenta.SessionUnitBraidT3.sliceOf ad)
        (Model.CompositeHeader.encode model) ⦄ := by
  unfold serialization.concat_ad
  step with encode_composite_refines real model hrel
  rw [← wire_compositeOf_eq real model hrel] at encoded_post ⊢
  have hencoded_len : encoded.val.length = 102 := by
    have h := congrArg List.length encoded_post
    simp only [List.length_map, compositeOf_encode_length] at h
    simpa [vecOf] using h
  step*
  all_goals (try simp_all [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
    alloc.vec.Vec.deref, Array.to_slice, Slice.length])
  all_goals (try scalar_tac)
  all_goals (try omega)
  all_goals simp_all only [vecOf, List.map_append, List.map_map]
  all_goals (try rw [u32_be_agrees_map _])
  all_goals (try rw [setWidth32_usize_scalar_model ad.len])
  all_goals simp_all [Model.Messages.concatAd,
    Tacenta.SessionUnitBraidT3.sliceOf, SessionUnitWireT3.compositeOf,
    SessionUnitWireT3.bytesOf, alloc.vec.Vec.deref, cast_usize_u32_model]
  all_goals rfl

/-- The initial-message wrapper emitted by the shipping serializer is exactly
the lifecycle model's version/type, two EncodeEC values, length-prefixed KEM
ciphertext, three identifiers, and inner ratchet message. -/
theorem encode_initial_refines
    (identity ephemeral kemCiphertext message : Slice Std.U8)
    (signedPrekeyId oneTimePrekeyId kemPrekeyId : U32)
    (hroom : identity.val.length + ephemeral.val.length
      + kemCiphertext.val.length + message.val.length + 18 ≤ Usize.max) :
    serialization.encode_initial identity ephemeral kemCiphertext signedPrekeyId
      oneTimePrekeyId kemPrekeyId message ⦃ fun encoded =>
        vecOf encoded = Model.Messages.encodeInitial
          (Tacenta.SessionUnitBraidT3.sliceOf identity)
          (Tacenta.SessionUnitBraidT3.sliceOf ephemeral)
          (Tacenta.SessionUnitBraidT3.sliceOf kemCiphertext)
          (UInt32.ofNat signedPrekeyId.val)
          (UInt32.ofNat oneTimePrekeyId.val)
          (UInt32.ofNat kemPrekeyId.val)
          (Tacenta.SessionUnitBraidT3.sliceOf message) ⦄ := by
  unfold serialization.encode_initial
  step*
  all_goals (try simp_all [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
    Array.to_slice, Slice.length])
  all_goals (try scalar_tac)
  all_goals (try omega)
  all_goals simp_all only [vecOf, List.map_cons, List.map_append, List.map_map]
  all_goals (try rw [u32_be_agrees_map signedPrekeyId,
    u32_be_agrees_map oneTimePrekeyId, u32_be_agrees_map kemPrekeyId])
  all_goals (try rw [u32_be_agrees_map _])
  all_goals (try rw [setWidth32_usize_scalar_model kemCiphertext.len])
  all_goals simp_all [Model.Messages.encodeInitial,
    Tacenta.SessionUnitBraidT3.sliceOf, tacenta_wire.VERSION,
    tacenta_wire.TYPE_INITIAL, Model.Messages.version, Model.Messages.typeInitial,
    Tacenta.SessionUnitBraidT3.u8]
  all_goals rfl

set_option maxHeartbeats 4000000 in
/-- An AEAD refusal after a successful Triple receive discards every provisional
receive candidate. The implementation and model both retain the original
session and commit only the already-consumed candidate-key draw. -/
theorem decrypt_ratchet_aead_refusal_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (decoded : tacenta_wire.DecodedMessage)
    (modelComposite : Model.CompositeHeader.Composite)
    (realBraidMessage : tacenta_braid.Msg) (receivedEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output)
    (realBraidCandidate : tacenta_braid.Braid)
    (realSparseOutput : Option tacenta_spqr.Output)
    (peer : tacenta_boundary.dh.PublicKeyBytes)
    (recvSecret sendSecret candidateBytes newPublicBytes before realMk :
      Array Std.U8 32#usize)
    (candidatePrivate : tacenta_boundary.dh.PrivateKey)
    (candidatePublic : tacenta_boundary.dh.PublicKeyBytes)
    (realHeader : tacenta_triple.Header)
    (wrappedRecv wrappedSend wrappedMk : zeroize.Zeroizing (Array Std.U8 32#usize))
    (realTripleCandidate : tacenta_triple.State)
    (modelTripleCandidate : Model.Triple.State)
    (modelMk draw modelDhOutRecv modelDhOutSend : Model.Lifecycle.Key)
    (realKeys : Array Std.U8 32#usize × Array Std.U8 32#usize ×
      Array Std.U8 16#usize)
    (wrappedKeys : zeroize.Zeroizing
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (realAd : alloc.vec.Vec Std.U8) (aeadError : Unit)
    (hrel : SessionRefines dh K real model)
    (htraceNext : trace rngNext = oracleNext.draws)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Ok decoded))
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf decoded.ciphertext))
    (hmessageCall : lifecycle.msg_of decoded.header = ok realBraidMessage)
    (hreceive : tacenta_braid.Braid.receive real.braid realBraidMessage =
      ok (receivedEpoch, realOutput, realBraidCandidate))
    (hsparse : RealSparseConversion realOutput realSparseOutput)
    (hpeerCall : tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer)
    (hfirstCall : tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer =
      ok (some recvSecret))
    (hwrapRecv : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret =
      ok wrappedRecv)
    (hderefRecv : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv =
      ok recvSecret)
    (hrandomCall : lifecycle.random_secret rngCore cryptoRng rng =
      ok (candidateBytes, rngNext))
    (hcandidateCall : tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes =
      ok candidatePrivate)
    (hsecondCall : tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer =
      ok (some sendSecret))
    (hwrapSend : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret =
      ok wrappedSend)
    (hderefSend : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend =
      ok sendSecret)
    (hbeforeCall : tacenta_triple.State.sending_public real.triple = ok before)
    (hheaderCall : lifecycle.triple_header_of decoded.header = ok realHeader)
    (hpublicCall : tacenta_boundary.dh.PrivateKey.public_key candidatePrivate =
      ok candidatePublic)
    (hpublicBytesCall : tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic =
      ok newPublicBytes)
    (htripleReal : lifecycle.receive_with_eviction real.triple decoded.header realHeader
      recvSecret sendSecret newPublicBytes realSparseOutput =
        ok (.Ok (realTripleCandidate, realMk)))
    (hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
      some modelDhOutRecv)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hmodelSecond : oracle.dhAgree draw modelComposite.dh = some modelDhOutSend)
    (hmodelPublic : oracle.dhPublic draw = arrayOf newPublicBytes)
    (hmodelTriple : Model.Lifecycle.receiveWithEviction model.triple modelComposite
      (Model.Lifecycle.tripleHeaderOf modelComposite) modelDhOutRecv modelDhOutSend
      (oracle.dhPublic draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1) =
        .ok (modelTripleCandidate, modelMk))
    (hkeysCall : tacenta_ratchet.message_keys realMk tacenta_ratchet.LabelSet.Tacenta =
      ok realKeys)
    (hkeysValue : (arrayOf realKeys.1, arrayOf realKeys.2.1,
      arrayOf realKeys.2.2) = Model.State.messageKeys modelMk .tacenta)
    (hwrapMk : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) realMk = ok wrappedMk)
    (hderefMk : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedMk = ok realMk)
    (hwrapKeys : zeroize.Zeroizing.new
      (TupleABC.Insts.ZeroizeZeroize
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
        (Array.Insts.ZeroizeZeroize 16#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) realKeys =
      ok wrappedKeys)
    (hderefKeys : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (TupleABC.Insts.ZeroizeZeroize
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
        (Array.Insts.ZeroizeZeroize 16#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) wrappedKeys =
      ok realKeys)
    (hrealAd : serialization.concat_ad (alloc.vec.Vec.deref real.identity_ad)
      decoded.header = ok realAd)
    (hrealAdValue : vecOf realAd = Model.Messages.concatAd model.identityAd
      (Model.CompositeHeader.encode modelComposite))
    (haead : tacenta_boundary.aead.decrypt realKeys.1 realKeys.2.1 realKeys.2.2
      (alloc.vec.Vec.deref decoded.ciphertext) (alloc.vec.Vec.deref realAd) =
        ok (.Err aeadError)) :
    lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, real, rngNext) ∧
    StepRefines trace dh K
      (.Err .Aead, real, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  have hrealReady := braid_failed_refines K real.braid model.braid hrel.braid
  have hmodelReady : Model.Lifecycle.braidFailed model.braid = false := by
    cases hb : model.braid <;>
      simp [Model.Lifecycle.agreementFailed, Model.Lifecycle.braidFailed, hb] at hready ⊢
  rw [hmodelReady] at hrealReady
  rcases realKeys with ⟨encKey, macKey, ivKey⟩
  have hk1 : arrayOf encKey = (Model.State.messageKeys modelMk .tacenta).1 :=
    congrArg Prod.fst hkeysValue
  have hk2 : arrayOf macKey = (Model.State.messageKeys modelMk .tacenta).2.1 :=
    congrArg (fun keys => keys.2.1) hkeysValue
  have hk3 : arrayOf ivKey = (Model.State.messageKeys modelMk .tacenta).2.2 :=
    congrArg (fun keys => keys.2.2) hkeysValue
  have hcipher : sliceOf (alloc.vec.Vec.deref decoded.ciphertext) =
      vecOf decoded.ciphertext := by rfl
  have had : sliceOf (alloc.vec.Vec.deref realAd) =
      Model.Messages.concatAd model.identityAd
        (Model.CompositeHeader.encode modelComposite) := by
    change vecOf realAd = _
    exact hrealAdValue
  have haeadModel := aead_open_error_refines rngCore cryptoRng dh kem trace
    oracle oracleOf encKey macKey ivKey
    (alloc.vec.Vec.deref decoded.ciphertext) (alloc.vec.Vec.deref realAd)
    aeadError haead
  rw [hk1, hk2, hk3, hcipher, had] at haeadModel
  have hreal : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, real, rngNext) := by
    unfold lifecycle.Session.decrypt_ratchet
    cases hsparse with
    | none hout =>
        simp [hrealReady, hdecodeReal, hmessageCall, hreceive, hout, hpeerCall,
          hfirstCall, hwrapRecv, hderefRecv, hrandomCall, hcandidateCall,
          hsecondCall, hwrapSend, hderefSend, hbeforeCall, hheaderCall,
          hpublicCall, hpublicBytesCall, htripleReal, hwrapMk, hderefMk,
          hkeysCall, hwrapKeys, hderefKeys, hrealAd, haead]
    | some realSparse converted hout hconverted =>
        simp [hrealReady, hdecodeReal, hmessageCall, hreceive, hout, hconverted,
          hpeerCall, hfirstCall, hwrapRecv, hderefRecv, hrandomCall,
          hcandidateCall, hsecondCall, hwrapSend, hderefSend, hbeforeCall,
          hheaderCall, hpublicCall, hpublicBytesCall, htripleReal, hwrapMk,
          hderefMk, hkeysCall, hwrapKeys, hderefKeys, hrealAd, haead]
  have hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session := model, result := .error .aead, oracle := oracleNext } := by
    have hmodelTriple' := hmodelTriple
    rw [hmodelPublic] at hmodelTriple'
    simp [Model.Lifecycle.decryptRatchet, hready, hdecodeModel, hmodelFirst,
      hmodelDraw, hmodelSecond, hmodelPublic, hmodelTriple', haeadModel]
  refine ⟨hreal, ?_⟩
  rw [hmodel]
  exact ⟨rfl, hrel, htraceNext⟩

/-- When a successful receive keeps the existing sending public key, the
candidate Triple and Braid states commit while the ratchet private key and all
session metadata retain their existing refinement witnesses. -/
theorem receive_success_next_refines_same
    (dh : DhView) (K : Model.Braid.Kem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (realTriple : tacenta_triple.State) (realBraid : tacenta_braid.Braid)
    (modelTriple : Model.Triple.State) (modelBraid : Model.Braid.BraidState)
    (hrel : SessionRefines dh K real model)
    (htriple : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realTriple modelTriple)
    (hbraid : Tacenta.SessionUnitBraidT3.StateRefines K realBraid.state modelBraid) :
    SessionRefines dh K
      { real with triple := realTriple, braid := realBraid }
      { model with triple := modelTriple, braid := modelBraid } := by
  exact ⟨htriple, hbraid, hrel.ratchetPrivate, hrel.identityAd,
    hrel.ourIdentityPublic, hrel.peerIdentityPublic, hrel.pendingInitial,
    hrel.establishedEphemeral⟩

/-- When a successful receive rotates the sending public key, the fresh
translated private key and the consumed model draw become the new related
ratchet-private fields; all other metadata retains its prior witness. -/
theorem receive_success_next_refines_rotated
    (dh : DhView) (K : Model.Braid.Kem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (realTriple : tacenta_triple.State) (realBraid : tacenta_braid.Braid)
    (realPrivate : tacenta_boundary.dh.PrivateKey)
    (modelTriple : Model.Triple.State) (modelBraid : Model.Braid.BraidState)
    (modelPrivate : Model.Lifecycle.Key)
    (hrel : SessionRefines dh K real model)
    (htriple : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realTriple modelTriple)
    (hbraid : Tacenta.SessionUnitBraidT3.StateRefines K realBraid.state modelBraid)
    (hprivate : dh.privateKey realPrivate = modelPrivate) :
    SessionRefines dh K
      { { real with triple := realTriple, braid := realBraid } with
        ratchet_private := realPrivate }
      { { model with triple := modelTriple, braid := modelBraid } with
        ratchetPrivate := modelPrivate } := by
  exact ⟨htriple, hbraid, hprivate, hrel.identityAd, hrel.ourIdentityPublic,
    hrel.peerIdentityPublic, hrel.pendingInitial, hrel.establishedEphemeral⟩

/-- Lift the final successful receive computation once its concrete and model
results, byte correspondence, state relation and draw-trace relation have
been established. Keeping this bookkeeping separate prevents the lifecycle
proof from hiding a success/refusal mismatch inside simplification. -/
theorem decrypt_ratchet_success_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (plaintext : alloc.vec.Vec Std.U8) (modelPlaintext : Bytes)
    (realNext : lifecycle.Session) (modelNext : Model.Lifecycle.Session)
    (hreal : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext, realNext, rngNext))
    (hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session := modelNext, result := .ok modelPlaintext, oracle := oracleNext })
    (hbytes : vecOf plaintext = modelPlaintext)
    (hnext : SessionRefines dh K realNext modelNext)
    (htrace : trace rngNext = oracleNext.draws) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  refine ⟨(.Ok plaintext, realNext, rngNext), hreal, ?_⟩
  rw [hmodel]
  exact ⟨by simpa [ResultRefines] using hbytes, hnext, htrace⟩

set_option maxHeartbeats 4000000 in
/-- Successful established-session encryption refines the executable lifecycle
model all the way to the returned wire bytes. The leaf send relations supply
the candidate state/header/message key; this theorem composes them with the
proved serializers and the AEAD oracle contract. -/
theorem encrypt_success_no_initial_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (codewordView : CodewordViewSendOf view)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng rngNext : R)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output) (realBraidNext : tacenta_braid.Braid)
    (modelMessage : Model.Braid.Msg) (modelEpoch : Nat)
    (modelOutput : Option Model.Braid.Output) (modelBraidNext : Model.Braid.BraidState)
    (candidate : tacenta_triple.State) (realHeader : tacenta_triple.Header)
    (realMk : Array Std.U8 32#usize) (modelTripleNext : Model.Triple.State)
    (modelHeader : Model.Triple.Header) (modelMk : Model.Lifecycle.Key)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hsendReal : tacenta_braid.Braid.send rngCore cryptoRng real.braid rng =
      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
    (hsendModel : Model.Lifecycle.sendAgreement oracle model.braid =
      some ((some modelMessage, modelEpoch, modelOutput, modelBraidNext), oracleNext))
    (hmessage : Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage)
    (hbraidNext : Tacenta.SessionUnitBraidT3.StateRefines K
      realBraidNext.state modelBraidNext)
    (hnotFailed : Model.Lifecycle.braidFailed modelBraidNext = false)
    (htripleReal : RealTripleSuccess real.triple realEpoch realOutput candidate
      realHeader realMk)
    (htripleModel : Model.Triple.sendDetailed model.triple modelEpoch
      (Model.Lifecycle.sparseOutputOf modelOutput) =
        .ok (modelTripleNext, modelHeader, modelMk))
    (htripleNext : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      candidate modelTripleNext)
    (hheader : Tacenta.SessionUnitTripleT3.TripleHeaderR realHeader modelHeader)
    (hmk : arrayOf realMk = modelMk)
    (hpending : real.pending_initial = none)
    (htrace : trace rngNext = oracleNext.draws)
    (hadRoom : model.identityAd.length + 106 ≤ Usize.max)
    (hcipherRoom : let keys := Model.State.messageKeys modelMk .tacenta
      let ad := Model.Messages.concatAd model.identityAd
        (Model.CompositeHeader.encode
          (Model.Lifecycle.compositeOf view model.braid modelHeader modelMessage).get!)
      102 + (oracle.aeadSeal keys.1 keys.2.1 keys.2.2
        (sliceOf plaintext) ad).length ≤ Usize.max) :
    ∃ output,
      lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext)) := by
  have hrealReady := braid_failed_refines K real.braid model.braid hrel.braid
  have hmodelReady : Model.Lifecycle.braidFailed model.braid = false := by
    cases hb : model.braid <;>
      simp [Model.Lifecycle.agreementFailed, Model.Lifecycle.braidFailed, hb] at hready ⊢
  rw [hmodelReady] at hrealReady
  have hrealNext := braid_failed_refines K realBraidNext modelBraidNext hbraidNext
  rw [hnotFailed] at hrealNext
  obtain ⟨realComposite, modelComposite, hcompositeReal, hcompositeModel,
      hcompositeRel⟩ :=
    composite_of_refines view model.braid realHeader modelHeader realMessage
      modelMessage hheader hmessage codewordView
  have hpendingModel : model.pendingInitial = none := by
    have h := hrel.pendingInitial
    simp [hpending] at h
    exact h.symm
  obtain ⟨realKeys, hkeysCall, hkeysValue⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitT3.message_keys_refines hkdf hz80 realMk
      tacenta_ratchet.LabelSet.Tacenta)
  have hkeysValue' :
      (arrayOf realKeys.1, arrayOf realKeys.2.1, arrayOf realKeys.2.2) =
        Model.State.messageKeys modelMk .tacenta := by
    change (arrayOf realKeys.1, arrayOf realKeys.2.1, arrayOf realKeys.2.2) =
      Model.State.messageKeys (arrayOf realMk) .tacenta at hkeysValue
    rw [hmk] at hkeysValue
    exact hkeysValue
  rcases realKeys with ⟨encKey, macKey, ivKey⟩
  let inst32 := Array.Insts.ZeroizeZeroize 32#usize
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
  let instKeys : zeroize.Zeroize
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize) :=
    TupleABC.Insts.ZeroizeZeroize inst32 inst32
      (Array.Insts.ZeroizeZeroize 16#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
  obtain ⟨wrappedMk, hwrapMk, hderefMk⟩ := zeroizing_roundtrip hz32 inst32 realMk
  obtain ⟨wrappedKeys, hwrapKeys, hderefKeys⟩ :=
    zeroizing_roundtrip hzKeys instKeys (encKey, macKey, ivKey)
  have hadRoomReal : real.identity_ad.val.length + 106 ≤ Usize.max := by
    have hlen := congrArg List.length hrel.identityAd
    simp [vecOf] at hlen
    omega
  obtain ⟨realAd, hrealAd, hrealAdValue⟩ := Std.WP.spec_imp_exists
    (concat_ad_refines (alloc.vec.Vec.deref real.identity_ad) realComposite
      modelComposite hcompositeRel hadRoomReal)
  obtain ⟨ciphertext, hciphertext, hciphertextValue⟩ :=
    oracleOf.aeadSeal encKey macKey ivKey
      plaintext (alloc.vec.Vec.deref realAd)
  have hciphertextValue' : vecOf ciphertext =
      let keys := Model.State.messageKeys modelMk .tacenta
      oracle.aeadSeal keys.1 keys.2.1 keys.2.2 (sliceOf plaintext)
        (Model.Messages.concatAd model.identityAd
          (Model.CompositeHeader.encode modelComposite)) := by
    have hk1 : arrayOf encKey =
        (Model.State.messageKeys modelMk .tacenta).1 := by
      simpa only using congrArg Prod.fst hkeysValue'
    have hk2 : arrayOf macKey =
        (Model.State.messageKeys modelMk .tacenta).2.1 := by
      simpa only using congrArg (fun keys => keys.2.1) hkeysValue'
    have hk3 : arrayOf ivKey =
        (Model.State.messageKeys modelMk .tacenta).2.2 := by
      simpa only using congrArg (fun keys => keys.2.2) hkeysValue'
    have had : sliceOf (alloc.vec.Vec.deref realAd) =
        Model.Messages.concatAd model.identityAd
          (Model.CompositeHeader.encode modelComposite) := by
      change vecOf realAd = _
      rw [hrealAdValue]
      change Model.Messages.concatAd (vecOf real.identity_ad)
        (Model.CompositeHeader.encode modelComposite) = _
      rw [hrel.identityAd]
    rw [hciphertextValue, hk1, hk2, hk3, had]
  have hcipherRoomReal : 102 + ciphertext.val.length ≤ Usize.max := by
    have hlen := congrArg List.length hciphertextValue'
    simp [vecOf] at hlen
    rw [hcompositeModel] at hcipherRoom
    simp only [Option.get!_some] at hcipherRoom
    omega
  obtain ⟨ratchetMessage, hratchet, hratchetValue⟩ := Std.WP.spec_imp_exists
    (encode_message_refines realComposite modelComposite
      (alloc.vec.Vec.deref ciphertext) hcompositeRel hcipherRoomReal)
  let realNext : lifecycle.Session :=
    { real with triple := candidate, braid := realBraidNext }
  let modelNext : Model.Lifecycle.Session :=
    { model with triple := modelTripleNext, braid := modelBraidNext }
  have hnextSession : SessionRefines dh K realNext modelNext := by
    exact ⟨htripleNext, hbraidNext, hrel.ratchetPrivate, hrel.identityAd,
      hrel.ourIdentityPublic, hrel.peerIdentityPublic,
      by simp [realNext, modelNext, hpending, hpendingModel],
      hrel.establishedEphemeral⟩
  have hreal : lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng =
      ok (.Ok ratchetMessage, realNext, rngNext) := by
    unfold lifecycle.Session.encrypt
    cases htripleReal with
    | none hout hsend =>
        simp [hrealReady, hsendReal, hrealNext, hout, hsend, hcompositeReal,
          hwrapMk, hderefMk, hkeysCall, hwrapKeys, hderefKeys, hrealAd,
          hciphertext, hratchet, hpending, realNext, inst32, instKeys]
    | some realSparse converted hout hconverted hsend =>
        simp [hrealReady, hsendReal, hrealNext, hout, hconverted, hsend,
          hcompositeReal, hwrapMk, hderefMk, hkeysCall, hwrapKeys, hderefKeys,
          hrealAd, hciphertext, hratchet, hpending, realNext, inst32, instKeys]
  have hmodel : Model.Lifecycle.encrypt view oracle model (sliceOf plaintext) =
      { session := modelNext,
        result := .ok (Model.CompositeHeader.encodeMessage modelComposite
          (let keys := Model.State.messageKeys modelMk .tacenta
           oracle.aeadSeal keys.1 keys.2.1 keys.2.2 (sliceOf plaintext)
             (Model.Messages.concatAd model.identityAd
               (Model.CompositeHeader.encode modelComposite))))
        oracle := oracleNext } := by
    simp [Model.Lifecycle.encrypt, hready, hsendModel, hnotFailed,
      htripleModel, hcompositeModel, hpendingModel, modelNext]
  refine ⟨(.Ok ratchetMessage, realNext, rngNext), hreal, ?_⟩
  rw [hmodel]
  have hratchetValue' : vecOf ratchetMessage =
      Model.CompositeHeader.encodeMessage modelComposite
        (let keys := Model.State.messageKeys modelMk .tacenta
         oracle.aeadSeal keys.1 keys.2.1 keys.2.2 (sliceOf plaintext)
           (Model.Messages.concatAd model.identityAd
             (Model.CompositeHeader.encode modelComposite))) := by
    rw [hratchetValue]
    change Model.CompositeHeader.encodeMessage modelComposite (vecOf ciphertext) = _
    rw [hciphertextValue']
  exact ⟨by simpa [ResultRefines] using hratchetValue', hnextSession, htrace⟩




/-- The established-session success leaf with the Triple candidate supplied by
the exact generated send_candidate result. -/
theorem encrypt_success_no_initial_of_exact_candidate {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (codewordView : CodewordViewSendOf view)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng rngNext : R)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output) (realBraidNext : tacenta_braid.Braid)
    (modelMessage : Model.Braid.Msg) (modelEpoch : Nat)
    (modelOutput : Option Model.Braid.Output) (modelBraidNext : Model.Braid.BraidState)
    (candidate : tacenta_triple.State) (realHeader : tacenta_triple.Header)
    (realMk : Array Std.U8 32#usize) (sparseOutput : Option tacenta_spqr.Output)
    (modelTripleNext : Model.Triple.State)
    (modelHeader : Model.Triple.Header) (modelMk : Model.Lifecycle.Key)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hsendReal : tacenta_braid.Braid.send rngCore cryptoRng real.braid rng =
      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
    (hsendModel : Model.Lifecycle.sendAgreement oracle model.braid =
      some ((some modelMessage, modelEpoch, modelOutput, modelBraidNext), oracleNext))
    (hmessage : Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage)
    (hbraidNext : Tacenta.SessionUnitBraidT3.StateRefines K
      realBraidNext.state modelBraidNext)
    (hnotFailed : Model.Lifecycle.braidFailed modelBraidNext = false)
    (hsparse : RealSparseConversion realOutput sparseOutput)
    (hsendCandidate : lifecycle.send_candidate real.triple realEpoch sparseOutput =
      ok (candidate, .Ok (realHeader, realMk)))
    (htripleModel : Model.Triple.sendDetailed model.triple modelEpoch
      (Model.Lifecycle.sparseOutputOf modelOutput) =
        .ok (modelTripleNext, modelHeader, modelMk))
    (htripleNext : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      candidate modelTripleNext)
    (hheader : Tacenta.SessionUnitTripleT3.TripleHeaderR realHeader modelHeader)
    (hmk : arrayOf realMk = modelMk)
    (hpending : real.pending_initial = none)
    (htrace : trace rngNext = oracleNext.draws)
    (hadRoom : model.identityAd.length + 106 ≤ Usize.max)
    (hcipherRoom : let keys := Model.State.messageKeys modelMk .tacenta
      let ad := Model.Messages.concatAd model.identityAd
        (Model.CompositeHeader.encode
          (Model.Lifecycle.compositeOf view model.braid modelHeader modelMessage).get!)
      102 + (oracle.aeadSeal keys.1 keys.2.1 keys.2.2
        (sliceOf plaintext) ad).length ≤ Usize.max) :
    ∃ output,
      lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext)) := by
  apply encrypt_success_no_initial_step_refines
    (htripleReal := real_triple_success_of_exact_candidate hsparse hsendCandidate)
  all_goals assumption



/-- Established-session encryption after the Triple result has been obtained
from the generated candidate and contract-backed model adapter. -/
theorem public_encrypt_success_no_initial_of_contracts {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (codewordView : CodewordViewSendOf view)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng rngNext : R)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output) (realBraidNext : tacenta_braid.Braid)
    (modelMessage : Model.Braid.Msg) (modelEpoch : Nat)
    (modelOutput : Option Model.Braid.Output) (modelBraidNext : Model.Braid.BraidState)
    (candidate : tacenta_triple.State) (realHeader : tacenta_triple.Header)
    (realMk : Array Std.U8 32#usize) (sparseOutput : Option tacenta_spqr.Output)
    (modelTripleNext : Model.Triple.State)
    (modelHeader : Model.Triple.Header) (modelMk : Model.Lifecycle.Key)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hsendReal : tacenta_braid.Braid.send rngCore cryptoRng real.braid rng =
      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
    (hsendModel : Model.Lifecycle.sendAgreement oracle model.braid =
      some ((some modelMessage, modelEpoch, modelOutput, modelBraidNext), oracleNext))
    (hmessage : Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage)
    (hbraidNext : Tacenta.SessionUnitBraidT3.StateRefines K
      realBraidNext.state modelBraidNext)
    (hnotFailed : Model.Lifecycle.braidFailed modelBraidNext = false)
    (contracts : TripleSendRefinementContracts)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hroom : model.triple.postQuantum.chains.length + 1 < Usize.max)
    (hcb : ∀ p ∈ model.triple.postQuantum.chains,
      p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ model.triple.postQuantum.skipped,
      sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, sparseOutput = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hepoch : model.triple.postQuantum.epoch + 1 < Std.U64.max)
    (hcounter : ∀ p ∈ model.triple.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max)
    (hsparse : RealSparseConversion realOutput sparseOutput)
    (hsendCandidate : lifecycle.send_candidate real.triple realEpoch sparseOutput =
      ok (candidate, .Ok (realHeader, realMk)))
    (hmodelEpoch : realEpoch.val = modelEpoch)
    (hmodelOutput : Model.Lifecycle.sparseOutputOf modelOutput =
      Option.map Tacenta.SessionUnitTripleT3.spqrOutputOf sparseOutput)
    (htripleModel : Model.Triple.sendDetailed model.triple modelEpoch
      (Model.Lifecycle.sparseOutputOf modelOutput) =
        .ok (modelTripleNext, modelHeader, modelMk))
    (htripleNext : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      candidate modelTripleNext)
    (hheader : Tacenta.SessionUnitTripleT3.TripleHeaderR realHeader modelHeader)
    (hmk : arrayOf realMk = modelMk)
    (hpending : real.pending_initial = none)
    (htrace : trace rngNext = oracleNext.draws)
    (hadRoom : model.identityAd.length + 106 ≤ Usize.max)
    (hcipherRoom : let keys := Model.State.messageKeys modelMk .tacenta
      let ad := Model.Messages.concatAd model.identityAd
        (Model.CompositeHeader.encode
          (Model.Lifecycle.compositeOf view model.braid modelHeader modelMessage).get!)
      102 + (oracle.aeadSeal keys.1 keys.2.1 keys.2.2
        (sliceOf plaintext) ad).length ≤ Usize.max) :
    ∃ output,
      lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext)) := by
  obtain ⟨modelTripleNext', modelHeader', modelMk', hdetail, _hstate, _hheader, _hkey⟩ :=
    triple_success_evidence_of_exact_candidate_and_contracts contracts hrel.triple
      realEpoch sparseOutput hroom hcb hsb hnewb hepoch hcounter hsendCandidate
  have htripleModelExact := htripleModel
  rw [← hmodelEpoch, hmodelOutput] at htripleModelExact
  have heq : (modelTripleNext', modelHeader', modelMk') =
      (modelTripleNext, modelHeader, modelMk) := by
    apply Except.ok.inj
    exact hdetail.symm.trans htripleModelExact
  cases heq
  apply encrypt_success_no_initial_of_exact_candidate <;> assumption

set_option maxHeartbeats 4000000 in
/-- Successful pending-initial encryption refines the executable lifecycle
model all the way to the returned wire bytes. The leaf send relations supply
the candidate state/header/message key; this theorem composes them with the
proved serializers and the AEAD oracle contract. -/
theorem encrypt_success_initial_step_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng rngNext : R)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output) (realBraidNext : tacenta_braid.Braid)
    (modelMessage : Model.Braid.Msg) (modelEpoch : Nat)
    (modelOutput : Option Model.Braid.Output) (modelBraidNext : Model.Braid.BraidState)
    (candidate : tacenta_triple.State) (realHeader : tacenta_triple.Header)
    (realMk : Array Std.U8 32#usize) (modelTripleNext : Model.Triple.State)
    (modelHeader : Model.Triple.Header) (modelMk : Model.Lifecycle.Key)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hsendReal : tacenta_braid.Braid.send rngCore cryptoRng real.braid rng =
      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
    (hsendModel : Model.Lifecycle.sendAgreement oracle model.braid =
      some ((some modelMessage, modelEpoch, modelOutput, modelBraidNext), oracleNext))
    (hmessage : Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage)
    (hbraidNext : Tacenta.SessionUnitBraidT3.StateRefines K
      realBraidNext.state modelBraidNext)
    (hnotFailed : Model.Lifecycle.braidFailed modelBraidNext = false)
    (htripleReal : RealTripleSuccess real.triple realEpoch realOutput candidate
      realHeader realMk)
    (htripleModel : Model.Triple.sendDetailed model.triple modelEpoch
      (Model.Lifecycle.sparseOutputOf modelOutput) =
        .ok (modelTripleNext, modelHeader, modelMk))
    (htripleNext : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      candidate modelTripleNext)
    (hheader : Tacenta.SessionUnitTripleT3.TripleHeaderR realHeader modelHeader)
    (hmk : arrayOf realMk = modelMk)
    (pending : lifecycle.PendingInitial)
    (hpending : real.pending_initial = some pending)
    (htrace : trace rngNext = oracleNext.draws)
    (hadRoom : model.identityAd.length + 106 ≤ Usize.max)
    (hcipherRoom : let keys := Model.State.messageKeys modelMk .tacenta
      let ad := Model.Messages.concatAd model.identityAd
        (Model.CompositeHeader.encode
          (Model.Lifecycle.compositeOf view model.braid modelHeader modelMessage).get!)
      102 + (oracle.aeadSeal keys.1 keys.2.1 keys.2.2
        (sliceOf plaintext) ad).length ≤ Usize.max)
    (hinitialRoom :
      let composite :=
        (Model.Lifecycle.compositeOf view model.braid modelHeader modelMessage).get!
      let keys := Model.State.messageKeys modelMk .tacenta
      let ad := Model.Messages.concatAd model.identityAd
        (Model.CompositeHeader.encode composite)
      let ratchetMessage := Model.CompositeHeader.encodeMessage composite
        (oracle.aeadSeal keys.1 keys.2.1 keys.2.2 (sliceOf plaintext) ad)
      84 + (pendingInitialOf dh pending).kemCiphertext.length
        + ratchetMessage.length ≤ Usize.max) :
    ∃ output,
      lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext)) := by
  have hrealReady := braid_failed_refines K real.braid model.braid hrel.braid
  have hmodelReady : Model.Lifecycle.braidFailed model.braid = false := by
    cases hb : model.braid <;>
      simp [Model.Lifecycle.agreementFailed, Model.Lifecycle.braidFailed, hb] at hready ⊢
  rw [hmodelReady] at hrealReady
  have hrealNext := braid_failed_refines K realBraidNext modelBraidNext hbraidNext
  rw [hnotFailed] at hrealNext
  obtain ⟨realComposite, modelComposite, hcompositeReal, hcompositeModel,
      hcompositeRel⟩ :=
    composite_of_refines view model.braid realHeader modelHeader realMessage
      modelMessage hheader hmessage codewordView
  have hpendingModel :
      model.pendingInitial = some (pendingInitialOf dh pending) := by
    have h := hrel.pendingInitial
    simp [hpending] at h
    exact h.symm
  obtain ⟨realKeys, hkeysCall, hkeysValue⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitT3.message_keys_refines hkdf hz80 realMk
      tacenta_ratchet.LabelSet.Tacenta)
  have hkeysValue' :
      (arrayOf realKeys.1, arrayOf realKeys.2.1, arrayOf realKeys.2.2) =
        Model.State.messageKeys modelMk .tacenta := by
    change (arrayOf realKeys.1, arrayOf realKeys.2.1, arrayOf realKeys.2.2) =
      Model.State.messageKeys (arrayOf realMk) .tacenta at hkeysValue
    rw [hmk] at hkeysValue
    exact hkeysValue
  rcases realKeys with ⟨encKey, macKey, ivKey⟩
  let inst32 := Array.Insts.ZeroizeZeroize 32#usize
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
  let instKeys : zeroize.Zeroize
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize) :=
    TupleABC.Insts.ZeroizeZeroize inst32 inst32
      (Array.Insts.ZeroizeZeroize 16#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
  obtain ⟨wrappedMk, hwrapMk, hderefMk⟩ := zeroizing_roundtrip hz32 inst32 realMk
  obtain ⟨wrappedKeys, hwrapKeys, hderefKeys⟩ :=
    zeroizing_roundtrip hzKeys instKeys (encKey, macKey, ivKey)
  have hadRoomReal : real.identity_ad.val.length + 106 ≤ Usize.max := by
    have hlen := congrArg List.length hrel.identityAd
    simp [vecOf] at hlen
    omega
  obtain ⟨realAd, hrealAd, hrealAdValue⟩ := Std.WP.spec_imp_exists
    (concat_ad_refines (alloc.vec.Vec.deref real.identity_ad) realComposite
      modelComposite hcompositeRel hadRoomReal)
  obtain ⟨ciphertext, hciphertext, hciphertextValue⟩ :=
    oracleOf.aeadSeal encKey macKey ivKey
      plaintext (alloc.vec.Vec.deref realAd)
  have hciphertextValue' : vecOf ciphertext =
      let keys := Model.State.messageKeys modelMk .tacenta
      oracle.aeadSeal keys.1 keys.2.1 keys.2.2 (sliceOf plaintext)
        (Model.Messages.concatAd model.identityAd
          (Model.CompositeHeader.encode modelComposite)) := by
    have hk1 : arrayOf encKey =
        (Model.State.messageKeys modelMk .tacenta).1 := by
      simpa only using congrArg Prod.fst hkeysValue'
    have hk2 : arrayOf macKey =
        (Model.State.messageKeys modelMk .tacenta).2.1 := by
      simpa only using congrArg (fun keys => keys.2.1) hkeysValue'
    have hk3 : arrayOf ivKey =
        (Model.State.messageKeys modelMk .tacenta).2.2 := by
      simpa only using congrArg (fun keys => keys.2.2) hkeysValue'
    have had : sliceOf (alloc.vec.Vec.deref realAd) =
        Model.Messages.concatAd model.identityAd
          (Model.CompositeHeader.encode modelComposite) := by
      change vecOf realAd = _
      rw [hrealAdValue]
      change Model.Messages.concatAd (vecOf real.identity_ad)
        (Model.CompositeHeader.encode modelComposite) = _
      rw [hrel.identityAd]
    rw [hciphertextValue, hk1, hk2, hk3, had]
  have hcipherRoomReal : 102 + ciphertext.val.length ≤ Usize.max := by
    have hlen := congrArg List.length hciphertextValue'
    simp [vecOf] at hlen
    rw [hcompositeModel] at hcipherRoom
    simp only [Option.get!_some] at hcipherRoom
    omega
  obtain ⟨ratchetMessage, hratchet, hratchetValue⟩ := Std.WP.spec_imp_exists
    (encode_message_refines realComposite modelComposite
      (alloc.vec.Vec.deref ciphertext) hcompositeRel hcipherRoomReal)
  have hratchetValue' : vecOf ratchetMessage =
      Model.CompositeHeader.encodeMessage modelComposite
        (let keys := Model.State.messageKeys modelMk .tacenta
         oracle.aeadSeal keys.1 keys.2.1 keys.2.2 (sliceOf plaintext)
           (Model.Messages.concatAd model.identityAd
             (Model.CompositeHeader.encode modelComposite))) := by
    rw [hratchetValue]
    change Model.CompositeHeader.encodeMessage modelComposite (vecOf ciphertext) = _
    rw [hciphertextValue']
  obtain ⟨identityEncoded, hidentityEncoded, hidentityValue⟩ :=
    encode_ec_refines dh codec real.our_identity_public
  obtain ⟨ephemeralEncoded, hephemeralEncoded, hephemeralValue⟩ :=
    encode_ec_refines dh codec pending.ephemeral_public
  obtain ⟨identityRaw, _hidentityRawCall, hidentityRaw⟩ :=
    codec.asBytes real.our_identity_public
  obtain ⟨ephemeralRaw, _hephemeralRawCall, hephemeralRaw⟩ :=
    codec.asBytes pending.ephemeral_public
  have hidentityPublicLen : (dh.publicKey real.our_identity_public).length = 32 := by
    have h := congrArg List.length hidentityRaw
    simp [arrayOf] at h
    omega
  have hephemeralPublicLen : (dh.publicKey pending.ephemeral_public).length = 32 := by
    have h := congrArg List.length hephemeralRaw
    simp [arrayOf] at h
    omega
  have hidentityEncodedLen : identityEncoded.val.length = 33 := by
    have h := congrArg List.length hidentityValue
    simp [vecOf, Model.PersistedState.SessionState.encodeEc,
      hidentityPublicLen] at h
    omega
  have hephemeralEncodedLen : ephemeralEncoded.val.length = 33 := by
    have h := congrArg List.length hephemeralValue
    simp [vecOf, Model.PersistedState.SessionState.encodeEc,
      hephemeralPublicLen] at h
    omega
  have hkemLen : pending.kem_ciphertext.val.length =
      (pendingInitialOf dh pending).kemCiphertext.length := by
    simp [pendingInitialOf, vecOf]
  have hratchetLen : ratchetMessage.val.length =
      (Model.CompositeHeader.encodeMessage modelComposite
        (let keys := Model.State.messageKeys modelMk .tacenta
         oracle.aeadSeal keys.1 keys.2.1 keys.2.2 (sliceOf plaintext)
           (Model.Messages.concatAd model.identityAd
             (Model.CompositeHeader.encode modelComposite)))).length := by
    have h := congrArg List.length hratchetValue'
    simpa [vecOf] using h
  have hinitialRoomReal : identityEncoded.val.length + ephemeralEncoded.val.length
      + pending.kem_ciphertext.val.length + ratchetMessage.val.length + 18 ≤
        Usize.max := by
    rw [hcompositeModel] at hinitialRoom
    simp only [Option.get!_some] at hinitialRoom
    dsimp only at hinitialRoom hratchetLen
    omega
  obtain ⟨initialMessage, hinitial, hinitialValue⟩ := Std.WP.spec_imp_exists
    (encode_initial_refines (alloc.vec.Vec.deref identityEncoded)
      (alloc.vec.Vec.deref ephemeralEncoded)
      (alloc.vec.Vec.deref pending.kem_ciphertext)
      (alloc.vec.Vec.deref ratchetMessage) pending.signed_prekey_id
      pending.one_time_prekey_id pending.kem_prekey_id hinitialRoomReal)
  have hinitialValue' : vecOf initialMessage =
      Model.Messages.encodeInitial
        (Model.PersistedState.SessionState.encodeEc model.ourIdentityPublic)
        (Model.PersistedState.SessionState.encodeEc
          (pendingInitialOf dh pending).ephemeralPublic)
        (pendingInitialOf dh pending).kemCiphertext
        (UInt32.ofNat (pendingInitialOf dh pending).signedPrekeyId)
        (UInt32.ofNat (pendingInitialOf dh pending).oneTimePrekeyId)
        (UInt32.ofNat (pendingInitialOf dh pending).kemPrekeyId)
        (Model.CompositeHeader.encodeMessage modelComposite
          (let keys := Model.State.messageKeys modelMk .tacenta
           oracle.aeadSeal keys.1 keys.2.1 keys.2.2 (sliceOf plaintext)
             (Model.Messages.concatAd model.identityAd
               (Model.CompositeHeader.encode modelComposite)))) := by
    rw [hinitialValue]
    change Model.Messages.encodeInitial (vecOf identityEncoded)
      (vecOf ephemeralEncoded) (vecOf pending.kem_ciphertext)
      (UInt32.ofNat pending.signed_prekey_id.val)
      (UInt32.ofNat pending.one_time_prekey_id.val)
      (UInt32.ofNat pending.kem_prekey_id.val) (vecOf ratchetMessage) = _
    rw [hidentityValue, hephemeralValue, hratchetValue', hrel.ourIdentityPublic]
    rfl
  let realNext : lifecycle.Session :=
    { real with triple := candidate, braid := realBraidNext }
  let modelNext : Model.Lifecycle.Session :=
    { model with triple := modelTripleNext, braid := modelBraidNext }
  have hnextSession : SessionRefines dh K realNext modelNext := by
    exact ⟨htripleNext, hbraidNext, hrel.ratchetPrivate, hrel.identityAd,
      hrel.ourIdentityPublic, hrel.peerIdentityPublic,
      by simp [realNext, modelNext, hpending, hpendingModel],
      hrel.establishedEphemeral⟩
  have hreal : lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng =
      ok (.Ok initialMessage, realNext, rngNext) := by
    unfold lifecycle.Session.encrypt
    cases htripleReal with
    | none hout hsend =>
        simp [hrealReady, hsendReal, hrealNext, hout, hsend, hcompositeReal,
          hwrapMk, hderefMk, hkeysCall, hwrapKeys, hderefKeys, hrealAd,
          hciphertext, hratchet, hpending, hidentityEncoded, hephemeralEncoded,
          hinitial, realNext, inst32, instKeys]
    | some realSparse converted hout hconverted hsend =>
        simp [hrealReady, hsendReal, hrealNext, hout, hconverted, hsend,
          hcompositeReal, hwrapMk, hderefMk, hkeysCall, hwrapKeys, hderefKeys,
          hrealAd, hciphertext, hratchet, hpending, hidentityEncoded,
          hephemeralEncoded, hinitial, realNext, inst32, instKeys]
  have hmodel : Model.Lifecycle.encrypt view oracle model (sliceOf plaintext) =
      { session := modelNext,
        result := .ok (Model.Messages.encodeInitial
          (Model.PersistedState.SessionState.encodeEc model.ourIdentityPublic)
          (Model.PersistedState.SessionState.encodeEc
            (pendingInitialOf dh pending).ephemeralPublic)
          (pendingInitialOf dh pending).kemCiphertext
          (UInt32.ofNat (pendingInitialOf dh pending).signedPrekeyId)
          (UInt32.ofNat (pendingInitialOf dh pending).oneTimePrekeyId)
          (UInt32.ofNat (pendingInitialOf dh pending).kemPrekeyId)
          (Model.CompositeHeader.encodeMessage modelComposite
            (let keys := Model.State.messageKeys modelMk .tacenta
             oracle.aeadSeal keys.1 keys.2.1 keys.2.2 (sliceOf plaintext)
               (Model.Messages.concatAd model.identityAd
                 (Model.CompositeHeader.encode modelComposite)))))
        oracle := oracleNext } := by
    simp [Model.Lifecycle.encrypt, hready, hsendModel, hnotFailed,
      htripleModel, hcompositeModel, hpendingModel, modelNext]
  refine ⟨(.Ok initialMessage, realNext, rngNext), hreal, ?_⟩
  rw [hmodel]
  exact ⟨by simpa [ResultRefines] using hinitialValue', hnextSession, htrace⟩



/-- The pending-initial success leaf with the Triple candidate supplied by
the exact generated send_candidate result. -/
theorem encrypt_success_initial_of_exact_candidate {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng rngNext : R)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output) (realBraidNext : tacenta_braid.Braid)
    (modelMessage : Model.Braid.Msg) (modelEpoch : Nat)
    (modelOutput : Option Model.Braid.Output) (modelBraidNext : Model.Braid.BraidState)
    (candidate : tacenta_triple.State) (realHeader : tacenta_triple.Header)
    (realMk : Array Std.U8 32#usize) (sparseOutput : Option tacenta_spqr.Output)
    (modelTripleNext : Model.Triple.State)
    (modelHeader : Model.Triple.Header) (modelMk : Model.Lifecycle.Key)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hsendReal : tacenta_braid.Braid.send rngCore cryptoRng real.braid rng =
      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
    (hsendModel : Model.Lifecycle.sendAgreement oracle model.braid =
      some ((some modelMessage, modelEpoch, modelOutput, modelBraidNext), oracleNext))
    (hmessage : Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage)
    (hbraidNext : Tacenta.SessionUnitBraidT3.StateRefines K
      realBraidNext.state modelBraidNext)
    (hnotFailed : Model.Lifecycle.braidFailed modelBraidNext = false)
    (hsparse : RealSparseConversion realOutput sparseOutput)
    (hsendCandidate : lifecycle.send_candidate real.triple realEpoch sparseOutput =
      ok (candidate, .Ok (realHeader, realMk)))
    (htripleModel : Model.Triple.sendDetailed model.triple modelEpoch
      (Model.Lifecycle.sparseOutputOf modelOutput) =
        .ok (modelTripleNext, modelHeader, modelMk))
    (htripleNext : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      candidate modelTripleNext)
    (hheader : Tacenta.SessionUnitTripleT3.TripleHeaderR realHeader modelHeader)
    (hmk : arrayOf realMk = modelMk)
    (pending : lifecycle.PendingInitial)
    (hpending : real.pending_initial = some pending)
    (htrace : trace rngNext = oracleNext.draws)
    (hadRoom : model.identityAd.length + 106 ≤ Usize.max)
    (hcipherRoom : let keys := Model.State.messageKeys modelMk .tacenta
      let ad := Model.Messages.concatAd model.identityAd
        (Model.CompositeHeader.encode
          (Model.Lifecycle.compositeOf view model.braid modelHeader modelMessage).get!)
      102 + (oracle.aeadSeal keys.1 keys.2.1 keys.2.2
        (sliceOf plaintext) ad).length ≤ Usize.max)
    (hinitialRoom :
      let composite :=
        (Model.Lifecycle.compositeOf view model.braid modelHeader modelMessage).get!
      let keys := Model.State.messageKeys modelMk .tacenta
      let ad := Model.Messages.concatAd model.identityAd
        (Model.CompositeHeader.encode composite)
      let ratchetMessage := Model.CompositeHeader.encodeMessage composite
        (oracle.aeadSeal keys.1 keys.2.1 keys.2.2 (sliceOf plaintext) ad)
      84 + (pendingInitialOf dh pending).kemCiphertext.length
        + ratchetMessage.length ≤ Usize.max) :
    ∃ output,
      lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext)) := by
  apply encrypt_success_initial_step_refines
    (htripleReal := real_triple_success_of_exact_candidate hsparse hsendCandidate)
  all_goals assumption



/-- Pending-initial encryption after the Triple result has been obtained from
the generated candidate and contract-backed model adapter. -/
theorem public_encrypt_success_initial_of_contracts {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng rngNext : R)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output) (realBraidNext : tacenta_braid.Braid)
    (modelMessage : Model.Braid.Msg) (modelEpoch : Nat)
    (modelOutput : Option Model.Braid.Output) (modelBraidNext : Model.Braid.BraidState)
    (candidate : tacenta_triple.State) (realHeader : tacenta_triple.Header)
    (realMk : Array Std.U8 32#usize) (sparseOutput : Option tacenta_spqr.Output)
    (modelTripleNext : Model.Triple.State)
    (modelHeader : Model.Triple.Header) (modelMk : Model.Lifecycle.Key)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hsendReal : tacenta_braid.Braid.send rngCore cryptoRng real.braid rng =
      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
    (hsendModel : Model.Lifecycle.sendAgreement oracle model.braid =
      some ((some modelMessage, modelEpoch, modelOutput, modelBraidNext), oracleNext))
    (hmessage : Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage)
    (hbraidNext : Tacenta.SessionUnitBraidT3.StateRefines K
      realBraidNext.state modelBraidNext)
    (hnotFailed : Model.Lifecycle.braidFailed modelBraidNext = false)
    (contracts : TripleSendRefinementContracts)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hroom : model.triple.postQuantum.chains.length + 1 < Usize.max)
    (hcb : ∀ p ∈ model.triple.postQuantum.chains,
      p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ model.triple.postQuantum.skipped,
      sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, sparseOutput = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hepoch : model.triple.postQuantum.epoch + 1 < Std.U64.max)
    (hcounter : ∀ p ∈ model.triple.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max)
    (hsparse : RealSparseConversion realOutput sparseOutput)
    (hsendCandidate : lifecycle.send_candidate real.triple realEpoch sparseOutput =
      ok (candidate, .Ok (realHeader, realMk)))
    (hmodelEpoch : realEpoch.val = modelEpoch)
    (hmodelOutput : Model.Lifecycle.sparseOutputOf modelOutput =
      Option.map Tacenta.SessionUnitTripleT3.spqrOutputOf sparseOutput)
    (htripleModel : Model.Triple.sendDetailed model.triple modelEpoch
      (Model.Lifecycle.sparseOutputOf modelOutput) =
        .ok (modelTripleNext, modelHeader, modelMk))
    (htripleNext : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      candidate modelTripleNext)
    (hheader : Tacenta.SessionUnitTripleT3.TripleHeaderR realHeader modelHeader)
    (hmk : arrayOf realMk = modelMk)
    (pending : lifecycle.PendingInitial)
    (hpending : real.pending_initial = some pending)
    (htrace : trace rngNext = oracleNext.draws)
    (hadRoom : model.identityAd.length + 106 ≤ Usize.max)
    (hcipherRoom : let keys := Model.State.messageKeys modelMk .tacenta
      let ad := Model.Messages.concatAd model.identityAd
        (Model.CompositeHeader.encode
          (Model.Lifecycle.compositeOf view model.braid modelHeader modelMessage).get!)
      102 + (oracle.aeadSeal keys.1 keys.2.1 keys.2.2
        (sliceOf plaintext) ad).length ≤ Usize.max)
    (hinitialRoom :
      let composite :=
        (Model.Lifecycle.compositeOf view model.braid modelHeader modelMessage).get!
      let keys := Model.State.messageKeys modelMk .tacenta
      let ad := Model.Messages.concatAd model.identityAd
        (Model.CompositeHeader.encode composite)
      let ratchetMessage := Model.CompositeHeader.encodeMessage composite
        (oracle.aeadSeal keys.1 keys.2.1 keys.2.2 (sliceOf plaintext) ad)
      84 + (pendingInitialOf dh pending).kemCiphertext.length
        + ratchetMessage.length ≤ Usize.max) :
    ∃ output,
      lifecycle.Session.encrypt rngCore cryptoRng real plaintext rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext)) := by
  obtain ⟨modelTripleNext', modelHeader', modelMk', hdetail, _hstate, _hheader, _hkey⟩ :=
    triple_success_evidence_of_exact_candidate_and_contracts contracts hrel.triple
      realEpoch sparseOutput hroom hcb hsb hnewb hepoch hcounter hsendCandidate
  have htripleModelExact := htripleModel
  rw [← hmodelEpoch, hmodelOutput] at htripleModelExact
  have heq : (modelTripleNext', modelHeader', modelMk') =
      (modelTripleNext, modelHeader, modelMk) := by
    apply Except.ok.inj
    exact hdetail.symm.trans htripleModelExact
  cases heq
  apply encrypt_success_initial_of_exact_candidate <;> assumption


/-! ## Public encryption route evidence

The branch theorems above are result-indexed.  This indexed route package is
the composition boundary: it carries the concrete generated `Braid.send`
result and the model correspondence facts, then the dispatcher selects the
matching branch theorem.  It does not accept a pre-built public witness. -/
inductive EncryptRouteEvidence {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (plaintext : Slice Std.U8) (rng : R) : Type where
  | terminal
      (hrel : SessionRefines dh K real model)
      (htrace : trace rng = oracle.draws)
      (hfailed : Model.Lifecycle.agreementFailed model = true) :
      EncryptRouteEvidence rc crc trace dh K view oracle real model plaintext rng
  | braidNoDraw
      {rngNext : R} {realMessage : tacenta_braid.Msg}
      {realEpoch : Std.U64} {realOutput : Option tacenta_braid.Output}
      {realBraidNext : tacenta_braid.Braid}
      (contracts : BraidSendRefinementContracts rc K)
      (hlive : Tacenta.SessionUnitBraidT3.EncodersLive model.braid)
      (hkem : oracle.braidKem = K)
      (hrel : SessionRefines dh K real model)
      (hready : Model.Lifecycle.agreementFailed model = false)
      (htrace : trace rng = oracle.draws)
      (hnoDraw : Model.Lifecycle.braidSendNeedsDraw model.braid = false)
      (hsend : tacenta_braid.Braid.send rc crc real.braid rng =
        ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
      (hfailed : ∀ modelNext : Model.Braid.BraidState,
        Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state modelNext →
          Model.Lifecycle.braidFailed modelNext = true)
      (htraceNext : trace rngNext = oracle.draws) :
      EncryptRouteEvidence rc crc trace dh K view oracle real model plaintext rng
  | braidDraw
      {rngNext : R} {realMessage : tacenta_braid.Msg}
      {realEpoch : Std.U64} {realOutput : Option tacenta_braid.Output}
      {realBraidNext : tacenta_braid.Braid}
      (contracts : BraidSendRefinementContracts rc K)
      (hkem : oracle.braidKem = K)
      (hrel : SessionRefines dh K real model)
      (hready : Model.Lifecycle.agreementFailed model = false)
      (htrace : trace rng = oracle.draws)
      (hneedsDraw : Model.Lifecycle.braidSendNeedsDraw model.braid = true)
      (hsend : tacenta_braid.Braid.send rc crc real.braid rng =
        ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
      (hdraw : ∃ draws rest, draws.length = Model.Lifecycle.braidSendDrawCount model.braid ∧
        trace rng = draws ++ rest ∧ trace rngNext = rest)
      (hpost : ∀ draws rest, draws.length = Model.Lifecycle.braidSendDrawCount model.braid →
        trace rng = draws ++ rest → ∃ rand,
        rand = Model.Lifecycle.braidRandomness draws.flatten ∧
        (∀ modelMessage,
          (Model.Braid.send K rand model.braid).1 = some modelMessage →
            Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage) ∧
        realEpoch.val = (Model.Braid.send K rand model.braid).2.2.2.epoch - 1 ∧
        Tacenta.SessionUnitBraidT3.OptionOutputRefines realOutput
          (Model.Braid.send K rand model.braid).2.2.1 ∧
        Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state
          (Model.Braid.send K rand model.braid).2.2.2)
      (hfailed : ∀ modelNext : Model.Braid.BraidState,
        Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state modelNext →
          Model.Lifecycle.braidFailed modelNext = true) :
      EncryptRouteEvidence rc crc trace dh K view oracle real model plaintext rng

/-- Consume the typed terminal and Braid route evidence at the public
`Session::encrypt` boundary.  Triple refusal and the two success constructors
are added below with the same result-indexed shape. -/
theorem public_encrypt_of_braid_route
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {plaintext : Slice Std.U8} {rng : R}
    (evidence : EncryptRouteEvidence rc crc trace dh K view oracle real model
      plaintext rng) :
    PublicEncryptWitness rc crc trace dh K view oracle real model plaintext rng := by
  cases evidence with
  | terminal hrel htrace hfailed =>
      exact public_encrypt_terminal_witness rc crc trace dh K view oracle real model
        plaintext rng hrel htrace hfailed
  | braidNoDraw contracts hlive hkem hrel hready htrace hnoDraw hsend hfailed htraceNext =>
      exact encrypt_braid_failure_of_no_draw_contracts
        (rngCore := rc) (cryptoRng := crc) (trace := trace) (dh := dh) (K := K)
        (view := view) (oracle := oracle) (real := real) (model := model)
        (plaintext := plaintext) (rng := _) (rngNext := _)
        (realMessage := _) (realEpoch := _) (realOutput := _)
        (realBraidNext := _) contracts hlive hkem hrel hready hsend hnoDraw
        (fun modelNext hnext => hfailed modelNext hnext) htraceNext
  | braidDraw contracts hkem hrel hready htrace hneedsDraw hsend hdraw hpost hfailed =>
      exact encrypt_braid_failure_of_draw_send
        (rngCore := rc) (cryptoRng := crc) (trace := trace) (dh := dh) (K := K)
        (view := view) (oracle := oracle) (real := real) (model := model)
        (plaintext := plaintext) (rng := _) (rngNext := _)
        (realMessage := _) (realEpoch := _) (realOutput := _)
        (realBraidNext := _) hkem hrel hready hsend htrace hdraw hneedsDraw hpost
        (fun modelNext hnext => hfailed modelNext hnext)

/-! Triple-side route evidence.  The generated candidate result, its model
`sendDetailed` result, and the state/header/key relations are all fields of a
constructor; the route theorem below merely feeds those fields to the
corresponding public leaf. -/
inductive EncryptTripleRouteEvidence {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
    (model : Model.Lifecycle.Session) (plaintext : Slice Std.U8) (rng : R) : Type where
  | refusal
      {rngNext : R} {oracleNext : Model.Lifecycle.Oracle}
      {realMessage : tacenta_braid.Msg} {realEpoch : Std.U64}
      {realOutput : Option tacenta_braid.Output} {realBraidNext : tacenta_braid.Braid}
      {candidate : tacenta_triple.State} {sparseOutput : Option tacenta_spqr.Output}
      {realReason : tacenta_triple.TripleError}
      {modelMessage : Model.Braid.Msg} {modelEpoch : Nat}
      {modelOutput : Option Model.Braid.Output}
      {modelBraidNext : Model.Braid.BraidState} {modelReason : Model.Triple.SendRefusal}
      (contracts : TripleSendRefinementContracts)
      [Tacenta.SessionUnitT1.DerivedKeysModel]
      (hroom : model.triple.postQuantum.chains.length + 1 < Usize.max)
      (hcb : ∀ p ∈ model.triple.postQuantum.chains,
        p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
      (hsb : ∀ sk ∈ model.triple.postQuantum.skipped,
        sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
      (hnewb : ∀ o : tacenta_spqr.Output, sparseOutput = some o →
        o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
      (hepoch : model.triple.postQuantum.epoch + 1 < Std.U64.max)
      (hcounter : ∀ p ∈ model.triple.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
        (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max)
      (hsparse : RealSparseConversion realOutput sparseOutput)
      (hrel : SessionRefines dh K real model)
      (hready : Model.Lifecycle.agreementFailed model = false)
      (hsendReal : tacenta_braid.Braid.send rc crc real.braid rng =
        ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
      (hsendCandidate : lifecycle.send_candidate real.triple realEpoch sparseOutput =
        ok (candidate, .Err realReason))
      (hsendModel : Model.Lifecycle.sendAgreement oracle model.braid =
        some ((some modelMessage, modelEpoch, modelOutput, modelBraidNext), oracleNext))
      (hnext : Tacenta.SessionUnitBraidT3.StateRefines K realBraidNext.state modelBraidNext)
      (hnotFailed : Model.Lifecycle.braidFailed modelBraidNext = false)
      (hmodelOf : ∀ modelReason,
        Model.Triple.sendDetailed model.triple realEpoch.val
            (Option.map Tacenta.SessionUnitTripleT3.spqrOutputOf sparseOutput) =
            .error modelReason →
        Model.Triple.sendDetailed model.triple modelEpoch
            (Model.Lifecycle.sparseOutputOf modelOutput) = .error modelReason)
      (htrace : trace rngNext = oracleNext.draws) :
      EncryptTripleRouteEvidence rc crc trace dh kem K view oracle real model plaintext rng
  | successNoInitial
      {rngNext : R} {oracleNext : Model.Lifecycle.Oracle}
      {realMessage : tacenta_braid.Msg} {realEpoch : Std.U64}
      {realOutput : Option tacenta_braid.Output} {realBraidNext : tacenta_braid.Braid}
      {candidate : tacenta_triple.State} {realHeader : tacenta_triple.Header}
      {realMk : Array Std.U8 32#usize} {sparseOutput : Option tacenta_spqr.Output}
      {modelTripleNext : Model.Triple.State} {modelHeader : Model.Triple.Header}
      {modelMk : Model.Lifecycle.Key} {modelMessage : Model.Braid.Msg}
      {modelEpoch : Nat} {modelOutput : Option Model.Braid.Output}
      {modelBraidNext : Model.Braid.BraidState}
      (contracts : TripleSendRefinementContracts)
      [Tacenta.SessionUnitT1.DerivedKeysModel]
      (hroom : model.triple.postQuantum.chains.length + 1 < Usize.max)
      (hcb : ∀ p ∈ model.triple.postQuantum.chains,
        p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
      (hsb : ∀ sk ∈ model.triple.postQuantum.skipped,
        sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
      (hnewb : ∀ o : tacenta_spqr.Output, sparseOutput = some o →
        o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
      (hepoch : model.triple.postQuantum.epoch + 1 < Std.U64.max)
      (hcounter : ∀ p ∈ model.triple.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
        (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max)
      (hsparse : RealSparseConversion realOutput sparseOutput)
      (hrel : SessionRefines dh K real model)
      (hready : Model.Lifecycle.agreementFailed model = false)
      (hsendReal : tacenta_braid.Braid.send rc crc real.braid rng =
        ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
      (hsendCandidate : lifecycle.send_candidate real.triple realEpoch sparseOutput =
        ok (candidate, .Ok (realHeader, realMk)))
      (hsendModel : Model.Lifecycle.sendAgreement oracle model.braid =
        some ((some modelMessage, modelEpoch, modelOutput, modelBraidNext), oracleNext))
      (hmessage : Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage)
      (hbraidNext : Tacenta.SessionUnitBraidT3.StateRefines K
        realBraidNext.state modelBraidNext)
      (hnotFailed : Model.Lifecycle.braidFailed modelBraidNext = false)
      (hmodelEpoch : realEpoch.val = modelEpoch)
      (hmodelOutput : Model.Lifecycle.sparseOutputOf modelOutput =
        Option.map Tacenta.SessionUnitTripleT3.spqrOutputOf sparseOutput)
      (htripleModel : Model.Triple.sendDetailed model.triple modelEpoch
        (Model.Lifecycle.sparseOutputOf modelOutput) =
          .ok (modelTripleNext, modelHeader, modelMk))
      (htripleNext : Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        candidate modelTripleNext)
      (hheader : Tacenta.SessionUnitTripleT3.TripleHeaderR realHeader modelHeader)
      (hmk : arrayOf realMk = modelMk)
      (hpending : real.pending_initial = none)
      (htrace : trace rngNext = oracleNext.draws)
      (hadRoom : model.identityAd.length + 106 ≤ Usize.max)
      (hcipherRoom : let keys := Model.State.messageKeys modelMk .tacenta
        let ad := Model.Messages.concatAd model.identityAd
          (Model.CompositeHeader.encode
            (Model.Lifecycle.compositeOf view model.braid modelHeader modelMessage).get!)
        102 + (oracle.aeadSeal keys.1 keys.2.1 keys.2.2
          (sliceOf plaintext) ad).length ≤ Usize.max) :
      EncryptTripleRouteEvidence rc crc trace dh kem K view oracle real model plaintext rng
  | successInitial
      {rngNext : R} {oracleNext : Model.Lifecycle.Oracle}
      {realMessage : tacenta_braid.Msg} {realEpoch : Std.U64}
      {realOutput : Option tacenta_braid.Output} {realBraidNext : tacenta_braid.Braid}
      {candidate : tacenta_triple.State} {realHeader : tacenta_triple.Header}
      {realMk : Array Std.U8 32#usize} {sparseOutput : Option tacenta_spqr.Output}
      {modelTripleNext : Model.Triple.State} {modelHeader : Model.Triple.Header}
      {modelMk : Model.Lifecycle.Key} {modelMessage : Model.Braid.Msg}
      {modelEpoch : Nat} {modelOutput : Option Model.Braid.Output}
      {modelBraidNext : Model.Braid.BraidState} {pending : lifecycle.PendingInitial}
      (contracts : TripleSendRefinementContracts)
      [Tacenta.SessionUnitT1.DerivedKeysModel]
      (hroom : model.triple.postQuantum.chains.length + 1 < Usize.max)
      (hcb : ∀ p ∈ model.triple.postQuantum.chains,
        p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
      (hsb : ∀ sk ∈ model.triple.postQuantum.skipped,
        sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
      (hnewb : ∀ o : tacenta_spqr.Output, sparseOutput = some o →
        o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
      (hepoch : model.triple.postQuantum.epoch + 1 < Std.U64.max)
      (hcounter : ∀ p ∈ model.triple.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
        (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max)
      (hsparse : RealSparseConversion realOutput sparseOutput)
      (hrel : SessionRefines dh K real model)
      (hready : Model.Lifecycle.agreementFailed model = false)
      (hsendReal : tacenta_braid.Braid.send rc crc real.braid rng =
        ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
      (hsendCandidate : lifecycle.send_candidate real.triple realEpoch sparseOutput =
        ok (candidate, .Ok (realHeader, realMk)))
      (hsendModel : Model.Lifecycle.sendAgreement oracle model.braid =
        some ((some modelMessage, modelEpoch, modelOutput, modelBraidNext), oracleNext))
      (hmessage : Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage)
      (hbraidNext : Tacenta.SessionUnitBraidT3.StateRefines K
        realBraidNext.state modelBraidNext)
      (hnotFailed : Model.Lifecycle.braidFailed modelBraidNext = false)
      (hmodelEpoch : realEpoch.val = modelEpoch)
      (hmodelOutput : Model.Lifecycle.sparseOutputOf modelOutput =
        Option.map Tacenta.SessionUnitTripleT3.spqrOutputOf sparseOutput)
      (htripleModel : Model.Triple.sendDetailed model.triple modelEpoch
        (Model.Lifecycle.sparseOutputOf modelOutput) =
          .ok (modelTripleNext, modelHeader, modelMk))
      (htripleNext : Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        candidate modelTripleNext)
      (hheader : Tacenta.SessionUnitTripleT3.TripleHeaderR realHeader modelHeader)
      (hmk : arrayOf realMk = modelMk)
      (hpending : real.pending_initial = some pending)
      (htrace : trace rngNext = oracleNext.draws)
      (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
      (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
      (hzKeys : ZeroizingRoundTrips
        (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
      (hadRoom : model.identityAd.length + 106 ≤ Usize.max)
      (hcipherRoom : let keys := Model.State.messageKeys modelMk .tacenta
        let ad := Model.Messages.concatAd model.identityAd
          (Model.CompositeHeader.encode
            (Model.Lifecycle.compositeOf view model.braid modelHeader modelMessage).get!)
        102 + (oracle.aeadSeal keys.1 keys.2.1 keys.2.2
          (sliceOf plaintext) ad).length ≤ Usize.max)
      (hinitialRoom : let composite :=
          (Model.Lifecycle.compositeOf view model.braid modelHeader modelMessage).get!
        let keys := Model.State.messageKeys modelMk .tacenta
        let ad := Model.Messages.concatAd model.identityAd
          (Model.CompositeHeader.encode composite)
        let ratchetMessage := Model.CompositeHeader.encodeMessage composite
          (oracle.aeadSeal keys.1 keys.2.1 keys.2.2 (sliceOf plaintext) ad)
        84 + (pendingInitialOf dh pending).kemCiphertext.length +
          ratchetMessage.length ≤ Usize.max) :
      EncryptTripleRouteEvidence rc crc trace dh kem K view oracle real model plaintext rng

/-- Dispatch the three typed Triple routes to their concrete public leaves. -/
theorem public_encrypt_of_triple_route
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
    {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
    {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session}
    {model : Model.Lifecycle.Session} {plaintext : Slice Std.U8} {rng : R}
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (codec : DhCodecOf dh) (codewordView : CodewordViewSendOf view)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (evidence : EncryptTripleRouteEvidence rc crc trace dh kem K view oracle real model
      plaintext rng) :
    PublicEncryptWitness rc crc trace dh K view oracle real model plaintext rng := by
  cases evidence with
  | @refusal rngNext oracleNext realMessage realEpoch realOutput realBraidNext candidate
      sparseOutput realReason modelMessage modelEpoch modelOutput modelBraidNext modelReason
      contracts derivedKeys hroom hcb hsb hnewb hepoch hcounter hsparse hrel hready
      hsendReal hsendCandidate hsendModel hnext hnotFailed hmodelOf htrace =>
      exact public_encrypt_triple_refusal_of_contracts rc crc trace dh K view oracle oracleNext
        real model plaintext rng rngNext realMessage realEpoch realOutput realBraidNext candidate
        sparseOutput realReason modelMessage modelEpoch modelOutput modelBraidNext contracts hroom
        hcb hsb hnewb hepoch hcounter hsparse hrel hready hsendReal hsendCandidate
        hsendModel hnext hnotFailed hmodelOf htrace
  | @successNoInitial rngNext oracleNext realMessage realEpoch realOutput realBraidNext candidate
      realHeader realMk sparseOutput modelTripleNext modelHeader modelMk modelMessage modelEpoch
      modelOutput modelBraidNext contracts derivedKeys hroom hcb hsb hnewb hepoch hcounter hsparse hrel hready
      hsendReal hsendCandidate hsendModel hmessage hbraidNext hnotFailed hmodelEpoch
      hmodelOutput htripleModel htripleNext hheader hmk hpending htrace hadRoom hcipherRoom =>
      exact public_encrypt_success_no_initial_of_contracts rc crc trace dh kem K view oracle
        oracleNext oracleOf codewordView hkdf hz80 hz32 hzKeys real model plaintext rng rngNext
        realMessage realEpoch realOutput realBraidNext
        modelMessage modelEpoch modelOutput modelBraidNext candidate realHeader realMk sparseOutput
        modelTripleNext modelHeader modelMk hrel hready hsendReal hsendModel hmessage hbraidNext
        hnotFailed contracts hroom hcb hsb hnewb hepoch hcounter hsparse hsendCandidate
        hmodelEpoch hmodelOutput htripleModel htripleNext hheader hmk hpending htrace hadRoom
        hcipherRoom
  | @successInitial rngNext oracleNext realMessage realEpoch realOutput realBraidNext candidate
      realHeader realMk sparseOutput modelTripleNext modelHeader modelMk modelMessage modelEpoch
      modelOutput modelBraidNext pending contracts derivedKeys hroom hcb hsb hnewb hepoch hcounter hsparse hrel hready
      hsendReal hsendCandidate hsendModel hmessage hbraidNext hnotFailed hmodelEpoch
      hmodelOutput htripleModel htripleNext hheader hmk hpending htrace hz80 hz32 hzKeys
      hadRoom hcipherRoom hinitialRoom =>
      exact public_encrypt_success_initial_of_contracts rc crc trace dh kem K view oracle oracleNext
        oracleOf codec codewordView hkdf hz80 hz32 hzKeys real model plaintext rng rngNext
        realMessage realEpoch realOutput realBraidNext modelMessage modelEpoch modelOutput
        modelBraidNext candidate realHeader realMk sparseOutput modelTripleNext modelHeader modelMk
        hrel hready hsendReal hsendModel hmessage hbraidNext hnotFailed contracts hroom hcb hsb
        hnewb hepoch hcounter hsparse hsendCandidate hmodelEpoch hmodelOutput htripleModel
        htripleNext hheader hmk pending hpending htrace hadRoom hcipherRoom hinitialRoom

/-! Final public encrypt composition.  The outer package is a sum of the
terminal/Braid and Triple-side route packages, so every public route reaches a
concrete branch theorem and no branch is represented by an untyped callback. -/
inductive EncryptEndToEndEvidence {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
    (model : Model.Lifecycle.Session) (plaintext : Slice Std.U8) (rng : R) : Type where
  | braid
      (evidence : EncryptRouteEvidence rc crc trace dh K view oracle real model plaintext rng) :
      EncryptEndToEndEvidence rc crc trace dh kem K view oracle real model plaintext rng
  | triple
      (evidence : EncryptTripleRouteEvidence rc crc trace dh kem K view oracle real model
        plaintext rng) :
      EncryptEndToEndEvidence rc crc trace dh kem K view oracle real model plaintext rng

theorem public_encrypt_end_to_end
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
    {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
    {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session}
    {model : Model.Lifecycle.Session} {plaintext : Slice Std.U8} {rng : R}
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (codec : DhCodecOf dh) (codewordView : CodewordViewSendOf view)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (evidence : EncryptEndToEndEvidence rc crc trace dh kem K view oracle real model plaintext rng) :
    PublicEncryptWitness rc crc trace dh K view oracle real model plaintext rng := by
  cases evidence with
  | braid evidence => exact public_encrypt_of_braid_route evidence
  | triple evidence =>
      exact public_encrypt_of_triple_route oracleOf codec codewordView hkdf hz80 hz32 hzKeys evidence

/-! ## The run's candidate key

The Triple and AEAD refusal evidence used to carry, as fields, that the public bytes of the candidate
ratchet key equal `oracle.dhPublic` of every draw, which asks `dhPublic` to take one value over all
draws, and the real X25519 public key is not constant (a property tested and not proved here).  For
the run's own draw the equation is a consequence of the oracle's `random32`, `dhPublic` clauses and
the key codec. -/

/-- The 32 bytes `random_secret` returned are the model oracle's next draw. -/
theorem candidate_bytes_of_draw {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (rng rng1 : R) (draw : Model.Lifecycle.Key)
    (candidateBytes : Array Std.U8 32#usize)
    (htrace : trace rng = oracle.draws)
    (hdraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hrandom : lifecycle.random_secret rc crc rng = ok (candidateBytes, rng1)) :
    arrayOf candidateBytes = draw := by
  cases hd : oracle.draws with
  | nil => simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hd] at hdraw
  | cons head rest =>
      simp only [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hd, Option.some.injEq,
        Prod.mk.injEq] at hdraw
      obtain ⟨rfl, _⟩ := hdraw
      obtain ⟨value, rng', hcall, hvalue, _⟩ :=
        oracleOf.random32 rng head rest (by rw [htrace, hd])
      rw [hrandom] at hcall
      have hpair := Result.ok.inj hcall
      have hv : candidateBytes = value := (Prod.mk.inj hpair).1
      rw [hv]
      exact hvalue

/-- The public bytes of the run's candidate key are the oracle's public key of the run's draw. -/
theorem candidate_public_eq_draw {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (rng rng1 : R) (draw : Model.Lifecycle.Key)
    (candidateBytes : Array Std.U8 32#usize)
    (candidatePrivate : tacenta_boundary.dh.PrivateKey)
    (candidatePublic : tacenta_boundary.dh.PublicKeyBytes)
    (newPublicBytes : Array Std.U8 32#usize)
    (htrace : trace rng = oracle.draws)
    (hdraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hrandom : lifecycle.random_secret rc crc rng = ok (candidateBytes, rng1))
    (hcandidate : tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate)
    (hpublic : tacenta_boundary.dh.PrivateKey.public_key candidatePrivate = ok candidatePublic)
    (hpublicBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic =
      ok newPublicBytes) :
    oracle.dhPublic draw = arrayOf newPublicBytes := by
  rw [← candidate_bytes_of_draw rc crc trace dh kem oracle oracleNext oracleOf rng rng1 draw
    candidateBytes htrace hdraw hrandom]
  obtain ⟨pk, hpk, hpkv⟩ := codec.privateFromBytes candidateBytes
  rw [hcandidate] at hpk
  have hpk' : candidatePrivate = pk := Result.ok.inj hpk
  subst hpk'
  obtain ⟨pub, hpub, hpubv⟩ := oracleOf.dhPublic candidatePrivate
  rw [hpublic] at hpub
  have hpub' : candidatePublic = pub := Result.ok.inj hpub
  subst hpub'
  obtain ⟨bytes, hbytes, hbytesv⟩ := codec.asBytes candidatePublic
  rw [hpublicBytes] at hbytes
  have hb' : newPublicBytes = bytes := Result.ok.inj hbytes
  subst hb'
  rw [hbytesv, hpubv, hpkv]

end Tacenta.UnitLifecycleT3
