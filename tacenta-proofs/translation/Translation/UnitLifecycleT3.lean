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

/-! ## Primitive oracle agreement

The lifecycle model has nine primitive functions.  Each clause below names
the complete translated argument list.  Randomness is one ordered trace:
`random_secret`, KEM encapsulation and signing must each consume exactly its
head and return a state interpreted by the tail. -/

def arrayOf {n : Usize} (a : Array Std.U8 n) : Bytes :=
  a.val.map Tacenta.SessionUnitBraidT3.u8

/-- The opaque public-key byte projection agrees with the interpretation used
by `DhView`.  This is a representation relation for a boundary already present
in T1, rather than a new cryptographic primitive contract. -/
structure DhCodecOf (view : DhView) : Prop where
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
    (hview : CodewordViewOf view) :
    WireCodewordRefines { index := real.index, data := real.data }
      (view.send state model) := by
  have hmodel : modelChunkOf model.source real = model := by
    cases model
    simp [modelChunkOf, hindex]
  rw [← hmodel, hview.send state model.source real hcodeword]
  exact ⟨(uint16_ofNat_toNat_of_u16 real.index real.index.val rfl).symm, rfl⟩

/-- The translated header constructor agrees with the lifecycle model's wire
header.  The codeword bytes are fixed by the honest Braid chunk relation and
the shared `CodewordViewOf`, rather than chosen independently here. -/
theorem composite_of_refines (view : Model.Lifecycle.CodewordView)
    (braidBefore : Model.Braid.BraidState)
    (realHeader : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (realMessage : tacenta_braid.Msg) (modelMessage : Model.Braid.Msg)
    (hheader : Tacenta.SessionUnitTripleT3.TripleHeaderR realHeader modelHeader)
    (hmessage : Tacenta.SessionUnitBraidT3.MsgRefines realMessage modelMessage)
    (hview : CodewordViewOf view) :
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

/-- The two concrete checks for an accepted repeated-initial wrapper agree
with the model predicate.  The result exposes the exact translated call
equations needed by the public decrypt proof. -/
theorem repeated_initial_checks_refine (dh : DhView) (codec : DhCodecOf dh)
    (K : Model.Braid.Kem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (established : alloc.vec.Vec Std.U8)
    (decoded : tacenta_wire.DecodedInitial)
    (hrel : SessionRefines dh K real model)
    (hestablished : real.established_ephemeral = some established)
    (hephemeral : vecOf established = vecOf decoded.ephemeral)
    (hidentity : vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc
        (dh.publicKey real.peer_identity_public)) :
    ∃ encoded,
      encode_ec real.peer_identity_public = ok encoded ∧
      alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8
        established decoded.ephemeral = ok true ∧
      alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8
        decoded.identity encoded = ok true ∧
      Model.Lifecycle.repeatedInitial model
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
  have hmodelRepeat : Model.Lifecycle.repeatedInitial model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded) = true := by
    apply (Model.Lifecycle.repeatedInitial_iff _ _).2
    refine ⟨vecOf established, hmodelEstablished, ?_, ?_⟩
    · change vecOf established =
        Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val
      rw [wire_bytesOf_eq_vecOf]
      exact hephemeral
    · change Tacenta.SessionUnitWireT3.bytesOf decoded.identity.val =
        Model.PersistedState.SessionState.encodeEc model.peerIdentityPublic
      rw [wire_bytesOf_eq_vecOf, ← hrel.peerIdentityPublic]
      exact hidentity
  exact ⟨encoded, hencoded, hephemeralCall, hidentityCall, hmodelRepeat⟩

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
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
        ok output ∧
      StepRefines trace dh K output
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
  refine ⟨(.Err lifecycle.Error.AgreementFailed, real, rng), hreal, ?_⟩
  rw [hmodel]
  exact ⟨rfl, hrel, htrace⟩

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
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
        ok output ∧
      StepRefines trace dh K output
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
  refine ⟨(.Err (.Decode realReason), real, rng), hreal, ?_⟩
  rw [hmodel]
  exact ⟨congrArg Model.Lifecycle.Refusal.decode hreason, hrel, htrace⟩

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
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
        ok output ∧
      StepRefines trace dh K output
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
  exact decrypt_ratchet_decode_refusal_step_refines rngCore cryptoRng trace dh K
    view oracle real model message rng realReason (decodeRefusalOf realReason)
    hrel htrace hready hdecodeReal hmodelDecode rfl

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
  have hdispatch := Model.Lifecycle.dispatchDecrypt_passthrough model
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
    ∃ output,
      lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.decrypt view oracle model (sliceOf message)) := by
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
    ∃ output,
      lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.decrypt view oracle model (sliceOf message)) := by
  have htypeRel := message_type_refines message
  rw [htype] at htypeRel
  have hmodelType : Model.Lifecycle.messageType (sliceOf message) = some .initial := by
    simpa [messageTypeOf] using htypeRel.symm
  have hdispatch := Model.Lifecycle.dispatchDecrypt_decode_refusal model
    (sliceOf message) modelReason hmodelType hdecodeModel
  have hmodel := Model.Lifecycle.decrypt_dispatch_refusal_keeps_state view oracle
    model (sliceOf message) (.decode modelReason) hdispatch
  let output : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error ×
      lifecycle.Session × R :=
    (core.result.Result.Err (.Decode realReason), real, rng)
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok output := by
    simp [lifecycle.Session.decrypt, htype, hdecodeReal, output]
  refine ⟨output, hreal, ?_⟩
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
    ∃ output,
      lifecycle.Session.decrypt rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.decrypt view oracle model (sliceOf message)) := by
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
  exact decrypt_initial_decode_refusal_step_refines rngCore cryptoRng trace dh K
    view oracle real model message rng realReason (decodeRefusalOf realReason)
    hrel htrace htype hdecodeReal hdecodeModel rfl

/-- An initial frame cannot be a repeat when the established Session has no
recorded establishment ephemeral.  Both implementations refuse it before the
inner ratchet receive and leave state and randomness unchanged. -/
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
  have hmodelNone : model.establishedEphemeral = none := by
    have h := hrel.establishedEphemeral
    rw [hnone] at h
    exact h.symm
  have hrepeat : Model.Lifecycle.repeatedInitial model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded) = false := by
    simp [Model.Lifecycle.repeatedInitial, hmodelNone]
  have hdispatch := Model.Lifecycle.dispatchDecrypt_not_repeat model
    (sliceOf message) (Tacenta.SessionUnitWireInitialT3.initialOf decoded)
    hmodelType hdecodeRel hrepeat
  have hmodel := Model.Lifecycle.decrypt_dispatch_refusal_keeps_state view oracle
    model (sliceOf message) .notARepeatedInitial hdispatch
  let output : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error ×
      lifecycle.Session × R :=
    (core.result.Result.Err lifecycle.Error.NotARepeatedInitial, real, rng)
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok output := by
    simp [lifecycle.Session.decrypt, htype, hdecode, hnone, output]
  refine ⟨output, hreal, ?_⟩
  rw [hmodel]
  exact ⟨rfl, hrel, htrace⟩

/-- A decoded initial wrapper with the wrong establishment ephemeral is refused
before public-key encoding or the inner ratchet receive. -/
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
    (hmismatch : vecOf established ≠ vecOf decoded.ephemeral) :
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
  have hrepeat : Model.Lifecycle.repeatedInitial model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded) = false := by
    cases hr : Model.Lifecycle.repeatedInitial model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded) with
    | false => rfl
    | true =>
        obtain ⟨ephemeral, he, heq, _⟩ :=
          (Model.Lifecycle.repeatedInitial_iff _ _).1 hr
        rw [hmodelEstablished] at he
        cases he
        have hcontra : False := by
          apply hmismatch
          change vecOf established =
            Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val at heq
          rw [wire_bytesOf_eq_vecOf] at heq
          exact heq
        exact hcontra.elim
  have hdispatch := Model.Lifecycle.dispatchDecrypt_not_repeat model
    (sliceOf message) (Tacenta.SessionUnitWireInitialT3.initialOf decoded)
    hmodelType hdecodeRel hrepeat
  have hmodel := Model.Lifecycle.decrypt_dispatch_refusal_keeps_state view oracle
    model (sliceOf message) .notARepeatedInitial hdispatch
  let output : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error ×
      lifecycle.Session × R :=
    (core.result.Result.Err lifecycle.Error.NotARepeatedInitial, real, rng)
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok output := by
    simp [lifecycle.Session.decrypt, htype, hdecode, hestablished,
      hephemeralCall, output]
  refine ⟨output, hreal, ?_⟩
  rw [hmodel]
  exact ⟨rfl, hrel, htrace⟩

/-- A wrapper with the right establishment ephemeral but the wrong peer
identity is refused after the exact EncodeEC comparison and before the inner
ratchet receive. -/
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
        (dh.publicKey real.peer_identity_public)) :
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
  have hrepeat : Model.Lifecycle.repeatedInitial model
      (Tacenta.SessionUnitWireInitialT3.initialOf decoded) = false := by
    cases hr : Model.Lifecycle.repeatedInitial model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded) with
    | false => rfl
    | true =>
        obtain ⟨_, _, _, hmodelIdentity⟩ :=
          (Model.Lifecycle.repeatedInitial_iff _ _).1 hr
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
  have hdispatch := Model.Lifecycle.dispatchDecrypt_not_repeat model
    (sliceOf message) (Tacenta.SessionUnitWireInitialT3.initialOf decoded)
    hmodelType hdecodeRel hrepeat
  have hmodel := Model.Lifecycle.decrypt_dispatch_refusal_keeps_state view oracle
    model (sliceOf message) .notARepeatedInitial hdispatch
  let output : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error ×
      lifecycle.Session × R :=
    (core.result.Result.Err lifecycle.Error.NotARepeatedInitial, real, rng)
  have hreal : lifecycle.Session.decrypt rngCore cryptoRng real message rng =
      ok output := by
    simp [lifecycle.Session.decrypt, htype, hdecode, hestablished,
      hephemeralCall, hencoded, hidentityCall, output]
  refine ⟨output, hreal, ?_⟩
  rw [hmodel]
  exact ⟨rfl, hrel, htrace⟩

/-- Lift an accepted repeated-initial wrapper through public decrypt.  The two
wrapper identity checks are derived from the shared byte representation; the
inner receive relation supplies the authenticated ratchet transition. -/
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
    (hinner : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real
      (alloc.vec.Vec.deref decoded.message) rng = ok innerOutput)
    (hstep : StepRefines trace dh K innerOutput
      (Model.Lifecycle.decryptRatchet view oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage)) :
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
  obtain ⟨encoded, hencoded, hephemeralCall, hidentityCall, hrepeat⟩ :=
    repeated_initial_checks_refine dh codec K real model established decoded hrel
      hestablished hephemeral hidentity
  have hdispatch := Model.Lifecycle.dispatchDecrypt_repeat model
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
                  hephemeralCall, hencoded, hidentityCall, hinner, output,
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
                  hephemeralCall, hencoded, hidentityCall, hinner, output, realFinal,
                  core.result.Result.Insts.CoreOpsTry.branch]
              have hmodel : Model.Lifecycle.decrypt view oracle model (sliceOf message) =
                  { session := modelFinal, result := .ok modelBytes,
                    oracle := oracleNext } := by
                simp [Model.Lifecycle.decrypt, hdispatch, hmodelStep, modelFinal]
              refine ⟨output, hreal, ?_⟩
              rw [hmodel]
              exact ⟨hstep.result, hfinal, hstep.draws⟩

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
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
        ok output ∧
      StepRefines trace dh K output
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
  refine ⟨(.Err (.Handshake SessionError.NonContributoryAgreement), real, rng),
    hreal, ?_⟩
  rw [hmodel]
  exact ⟨rfl, hrel, htrace⟩

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
    (codewordView : CodewordViewOf view)
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
    (codewordView : CodewordViewOf view)
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

end Tacenta.UnitLifecycleT3
