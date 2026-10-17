import Translation.UnitLifecycleEstablishInitiatorShape

/-!
# `decrypt_ratchet` and the public `Session::decrypt` at an established initiator session

`UnitLifecycleEstablishInitiatorShape` derives, at every successful `establish_initiator_for` output `s`,
`Session::invariant` (under two assumed laws and `OptionEqU64Shape`), `CounterHeadroom` and
`SessionRefines dh K s (establishedModelOf dh s)` (the last by definition at a `KeysUnsampled` Braid).  This module feeds them to the `decrypt_ratchet`
refinement of `UnitLifecycleDecryptRunBounds` and, for ratchet-type frames, to the public `decrypt` through
`UnitLifecycleT3.decrypt_ratchet_message_refines`.

## What is shown

* `honestChunk_established` (no hypothesis beyond the establishment): `HonestChunk` of the model state's
  Braid for every model message, since a `keysUnsampled` Braid holds no decoder.
* `established_initiator_decrypt_ratchet_hypotheses`: the record `DecryptOfInvariantHypotheses` at `s` and
  `establishedModelOf dh s`, for every message and source state.  Its session fields (`invariant`,
  `related`, `counters`, and `inputs.honest`) are derived; its boundary fields (`oracleOf`, `codec`,
  `contracts`, `derivedKeys`, `agreements`), `trace_eq`, `inputs.chunk` and `inputs.draw` are the
  caller's, taken as `decrypt_ratchet_refines_of_invariant` takes them.
* `established_initiator_decrypt_ratchet_refines`: `decrypt_ratchet` at `s` returns and its result refines
  `Model.Lifecycle.decryptRatchet` at `establishedModelOf dh s`, refusals included.
* `established_initiator_decrypt_refines`: the same for the public `Session::decrypt`, for every message whose
  type byte is the ratchet type (`serialization::message_type message = ok (some Ratchet)`).
* `EstablishedDecryptHypotheses`, `EstablishedDecryptHypotheses.refines`: that theorem's hypotheses as one
  record, and the theorem applied to it.
* `established_decrypt_hypotheses_jointly_satisfiable`: at the real constants, under the decrypt laws of
  `UnitLifecycleDecryptScreen`, the initiator contract axioms, `InitiatorSuccessShape` and the two laws, every
  field of the record holds together, at the sample ratchet frame and source.
* `established_decrypt_laws_model`: one interpretation, `Interp.modelEstablished`, satisfies the shapes of all
  of those hypotheses together.  `Interp.modelDecrypt`, the model of the decrypt laws, does not satisfy
  `DhPublicValidShape` (its public key is the private key's bytes), so the variant fixes the public key at a
  canonical constant.

What a step's refinement says is `StepRefines`: the result, the post-state and the draws left refine the
model's step; for `decrypt_ratchet`, the model step keeps the session on a refusal
(`Model.Lifecycle.decryptRatchet_refusal_keeps_session`).

## What it does not show

* A proof that the success arm is reached.  It is reached in an honest run through a copy of the session: a
  snapshot exported before the initiator's first `encrypt` and restored after the responder replied decrypts
  the reply (`tacenta-core/tests/restored_initiator_receives_reply.rs`, a test on the seeds it tries).  A
  session value never copied leaves this state at its own first `encrypt`, which the peer needs first.
* Initial-type frames, `encrypt`, `establish_responder` and `import`.
* The chunk relation for a frame that carries a Braid agreement chunk, and the draw: the caller's.  The
  chunk premise is not benign for a frame from a sender who is not honest: a spliced or inconsistent chunk
  is outside the theorem whether the frame is refused or accepted.
* That the real primitives meet the boundary records or the laws: assumed.
-/

namespace Tacenta.UnitLifecycleEstablishedDecrypt

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3
open Tacenta.UnitLifecycleDecryptRatchetT3
open Tacenta.UnitLifecycleDecryptRunBounds
open Tacenta.UnitLifecycleEstablishInitiatorShape

/-- `HonestChunk` holds at the model state of every successful output, for every model message: the Braid is
at `keysUnsampled`, which holds no decoder, so the condition is `True`. -/
theorem honestChunk_established {E : Type} (rc : rand_core_1.RngCore E)
    (crc : rand_core_1.CryptoRng E) (dh : DhView)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (msg : Model.Braid.Msg) :
    Tacenta.SessionUnitBraidT3.HonestChunk (establishedModelOf dh s).braid msg := by
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rc crc our bundle expected rng0 rng1 s h
  intro mc _ _
  simp [establishedModelOf, InitiatorOutputParts.session, unsampledModelOf]

/-- **Every hypothesis of `decrypt_ratchet_refines_of_invariant` that concerns the session holds at every
successful `establish_initiator_for` output**, with the model state `establishedModelOf dh s`: the invariant
(under `DhPublicValid`, `KemCiphertextLenOf` and `OptionEqU64Shape`), the relation, the four ceilings and
`HonestChunk`.  The boundary records, the trace equation, the chunk relation and the draw are the caller's,
and they are taken here as they are taken there. -/
theorem established_initiator_decrypt_ratchet_hypotheses {R E : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (rc : rand_core_1.RngCore E) (crc : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (message : Slice Std.U8) (rng : R)
    (htrace : trace rng = oracle.draws)
    (hchunk : ∀ (realComposite : tacenta_wire.Composite)
      (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (modelComposite, ciphertext) →
      CompositeRefines realComposite modelComposite →
      IncomingChunkRefines view (establishedModelOf dh s).braid realComposite modelComposite)
    (hdraw : ∃ draw rest, trace rng = draw :: rest) :
    DecryptOfInvariantHypotheses rngCore cryptoRng trace dh view oracle s (establishedModelOf dh s)
      message rng :=
  { oracleOf := oracleOf
    codec := codec
    contracts := contracts
    derivedKeys := ⟨inferInstance⟩
    agreements := agreements
    invariant := establish_initiator_for_admissible rc crc hpub hct hoeq our bundle expected rng0 rng1 s h
    related := sessionRefines_established rc crc dh oracle.braidKem our bundle expected rng0 rng1 s h
    counters := counterHeadroom_of_established rc crc our bundle expected rng0 rng1 s h
    trace_eq := htrace
    inputs :=
      { chunk := hchunk
        honest := fun _ _ _ =>
          honestChunk_established rc crc dh our bundle expected rng0 rng1 s h _
        draw := hdraw } }

/-- **`decrypt_ratchet` at an established initiator session refines the model's step**, for every message
and source of randomness, under the caller's boundary records, trace equation, chunk relation and draw, and
the laws `DhPublicValid`, `KemCiphertextLenOf` and `OptionEqU64Shape`. -/
theorem established_initiator_decrypt_ratchet_refines {R E : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (rc : rand_core_1.RngCore E) (crc : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (message : Slice Std.U8) (rng : R)
    (htrace : trace rng = oracle.draws)
    (hchunk : ∀ (realComposite : tacenta_wire.Composite)
      (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (modelComposite, ciphertext) →
      CompositeRefines realComposite modelComposite →
      IncomingChunkRefines view (establishedModelOf dh s).braid realComposite modelComposite)
    (hdraw : ∃ draw rest, trace rng = draw :: rest) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng s message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decryptRatchet view oracle (establishedModelOf dh s) (sliceOf message)) :=
  (established_initiator_decrypt_ratchet_hypotheses rngCore cryptoRng trace dh view oracle oracleOf
    codec contracts agreements hpub hct hoeq rc crc our bundle expected rng0 rng1 s h message rng
    htrace hchunk hdraw).refines

/-- **The public `Session::decrypt` at an established initiator session refines the model's `decrypt`**, for
every message whose type byte is the ratchet type, under the hypotheses of
`established_initiator_decrypt_ratchet_refines`.  It composes that theorem with
`decrypt_ratchet_message_refines`. -/
theorem established_initiator_decrypt_refines {R E : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (rc : rand_core_1.RngCore E) (crc : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (message : Slice Std.U8) (rng : R)
    (htype : serialization.message_type message = ok (some serialization.MessageType.Ratchet))
    (htrace : trace rng = oracle.draws)
    (hchunk : ∀ (realComposite : tacenta_wire.Composite)
      (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (modelComposite, ciphertext) →
      CompositeRefines realComposite modelComposite →
      IncomingChunkRefines view (establishedModelOf dh s).braid realComposite modelComposite)
    (hdraw : ∃ draw rest, trace rng = draw :: rest) :
    PublicDecryptWitness rngCore cryptoRng trace dh oracle.braidKem view oracle s
      (establishedModelOf dh s) message rng := by
  obtain ⟨output, hout, hstep⟩ := established_initiator_decrypt_ratchet_refines rngCore cryptoRng
    trace dh view oracle oracleOf codec contracts agreements hpub hct hoeq rc crc our bundle expected
    rng0 rng1 s h message rng htrace hchunk hdraw
  exact decrypt_ratchet_message_refines rngCore cryptoRng trace dh oracle.braidKem view oracle s
    (establishedModelOf dh s) message rng output htype hout hstep

/-! ## The premises of the connected theorem hold together -/

open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real InitiatorAxiom)

/-- The hypotheses of `established_initiator_decrypt_refines` at one choice of every binder, the class
`DerivedKeysModel` as a `Nonempty`. -/
structure EstablishedDecryptHypotheses {R E : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (rc : rand_core_1.RngCore E) (crc : rand_core_1.CryptoRng E) (our : lifecycle.Identity)
    (bundle : lifecycle.PublishedBundle) (expected : tacenta_boundary.dh.PublicKeyBytes)
    (rng0 rng1 : E) (s : lifecycle.Session) (message : Slice Std.U8) (rng : R) : Prop where
  oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle
  codec : DhCodecOf dh
  contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore
  derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel
  agreements : DecryptRatchetAgreements oracle.braidKem
  dhPublicValid : DhPublicValid
  kemCiphertextLen : KemCiphertextLenOf
  optionEq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
    (@core.option.Option.Insts.CoreCmpPartialEqOption.eq)
  established : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
    ok (core.result.Result.Ok s, rng1)
  messageType : serialization.message_type message = ok (some serialization.MessageType.Ratchet)
  trace_eq : trace rng = oracle.draws
  chunk : ∀ (realComposite : tacenta_wire.Composite)
      (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (modelComposite, ciphertext) →
      CompositeRefines realComposite modelComposite →
      IncomingChunkRefines view (establishedModelOf dh s).braid realComposite modelComposite
  draw : ∃ draw rest, trace rng = draw :: rest

/-- The record is the hypothesis list of `established_initiator_decrypt_refines`: from it, that theorem
applies. -/
theorem EstablishedDecryptHypotheses.refines {R E : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {rc : rand_core_1.RngCore E} {crc : rand_core_1.CryptoRng E} {our : lifecycle.Identity}
    {bundle : lifecycle.PublishedBundle} {expected : tacenta_boundary.dh.PublicKeyBytes}
    {rng0 rng1 : E} {s : lifecycle.Session} {message : Slice Std.U8} {rng : R}
    (h : EstablishedDecryptHypotheses rngCore cryptoRng trace dh view oracle rc crc our bundle expected
      rng0 rng1 s message rng) :
    PublicDecryptWitness rngCore cryptoRng trace dh oracle.braidKem view oracle s
      (establishedModelOf dh s) message rng := by
  obtain ⟨inst⟩ := h.derivedKeys
  exact established_initiator_decrypt_refines rngCore cryptoRng trace dh view oracle h.oracleOf h.codec
    h.contracts h.agreements h.dhPublicValid h.kemCiphertextLen h.optionEq rc crc our bundle expected
    rng0 rng1 s h.established message rng h.messageType h.trace_eq h.chunk h.draw

/-- The translated `message_type` reads the sample message of `UnitLifecycleDecryptRatchetScreen` as a
ratchet frame. -/
theorem sampleMessage_real_type :
    serialization.message_type Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage =
      ok (some serialization.MessageType.Ratchet) := by
  obtain ⟨r, hr, hmap⟩ := Std.WP.spec_imp_exists
    (message_type_refines Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage)
  rw [Tacenta.UnitLifecycleDecryptScreen.sampleMessage_type] at hmap
  rw [hr]
  rcases r with _ | t
  · simp at hmap
  · cases t
    · rfl
    · simp [messageTypeOf] at hmap

/-- The chunk relation holds for the sample message at every model Braid state: it carries no
agreement chunk. -/
theorem sampleMessage_chunk (view : Model.Lifecycle.CodewordView) (braid : Model.Braid.BraidState)
    (realComposite : tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
    (ciphertext : Bytes)
    (hdecode : Model.CompositeHeader.decodeDetailed
      (sliceOf Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage) = .ok (modelComposite, ciphertext))
    (hcomposite : CompositeRefines realComposite modelComposite) :
    IncomingChunkRefines view braid realComposite modelComposite := by
  rw [Tacenta.UnitLifecycleDecryptRatchetScreen.sample_decode_model] at hdecode
  have hmc : Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite = modelComposite :=
    (Prod.mk.inj (Except.ok.inj hdecode)).1
  subst hmc
  have hchunk := hcomposite.agChunk
  unfold IncomingChunkRefines
  cases hr : realComposite.ag_chunk with
  | none => simp [Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite]
  | some c => simp [hr, Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite] at hchunk

/-- **Every hypothesis of `established_initiator_decrypt_refines` holds together at the real constants**,
under the decrypt laws `DecryptJointLaws K dh` of `UnitLifecycleDecryptScreen`, the axiom part of the
initiator contract record and `InitiatorSuccessShape` at the byte-stream source, `DhPublicValid` and
`KemCiphertextLenOf`, all assumed: for every identity there are an oracle with `braidKem = K`, a bundle, a
successful establishment from the empty source, and, at the sample ratchet frame and source of
`UnitLifecycleDecryptRatchetScreen`, every field of `EstablishedDecryptHypotheses`, for every codeword view. -/
theorem established_decrypt_hypotheses_jointly_satisfiable (K : Model.Braid.Kem) (dh : DhView)
    (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (our : lifecycle.Identity) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle) (s : lifecycle.Session)
      (rng1 : List Std.U8),
      oracle.braidKem = K ∧
      ∀ view : Model.Lifecycle.CodewordView,
        EstablishedDecryptHypotheses byteRng byteCrc byteTrace dh view oracle byteRng byteCrc our bundle
          bundle.bundle.identity_key [] rng1 s Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
          Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng := by
  obtain ⟨oracle, hdraws, hK, horacle⟩ :=
    Tacenta.UnitOracleDecrypt.decryptOracleOf_of_laws dh L.dhCodec L.dhAgree L.aeadOpen L.viewInjective
      (byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng) K
  obtain ⟨k, pkb, a, hpk, hbytes, hcan, hprime⟩ := L.validKey
  obtain ⟨ad, had, hlen⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_ad_length L.dhCodec pkb pkb)
  obtain ⟨bundle, s, rng1, hest⟩ := establish_initiator_for_succeeds byteRng byteCrc A S our []
  refine ⟨oracle, bundle, s, rng1, hK, fun view => ?_⟩
  have h0 := Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_at_invReal K dh L oracle hK hdraws
    horacle k pkb a hpk hbytes hcan hprime ad had hlen view
  exact
    { oracleOf := h0.oracleOf
      codec := h0.codec
      contracts := h0.contracts
      derivedKeys := h0.derivedKeys
      agreements := h0.agreements
      dhPublicValid := hpub
      kemCiphertextLen := hct
      optionEq := L.optionEq
      established := hest
      messageType := sampleMessage_real_type
      trace_eq := h0.trace_eq
      chunk := fun rc mc ct hd hc => sampleMessage_chunk view _ rc mc ct hd hc
      draw := h0.run.draw }

/-! ### One interpretation satisfies every law the statement above takes -/

/-- `Interp.modelDecrypt` with a constant public key, the 32 zero bytes, so that every public key the
interpretation returns is canonical; every other field is `Interp.modelDecrypt`'s.  Its agreement still
refuses the zero public key, so the agreement the success case needs is with another key, `oneKey`. -/
noncomputable def Interp.modelEstablished : Interp :=
  { Tacenta.UnitLifecycleDecryptRatchetScreen.Interp.modelDecrypt with
    dhPrivPublicKey := fun _ => ok Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32 }

/-- The view of `Interp.modelEstablished`: both key types are their bytes. -/
def viewEstablished : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape Interp.modelEstablished :=
  ⟨arrayOf, arrayOf⟩

/-- The side condition of `oneKey`. -/
theorem oneKey_length : (1#u8 :: List.replicate 31 0#u8).length = (32#usize).val := by simp

/-- The key with bytes `1, 0, ..., 0`: canonical and not the zero key. -/
def oneKey : Array U8 32#usize := ⟨1#u8 :: List.replicate 31 0#u8, oneKey_length⟩

theorem oneKey_canonical : Tacenta.SessionUnitT1.canonicalX25519 oneKey = true := by decide

theorem oneKey_ne_zero : oneKey.val ≠ Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val := by
  decide

open Tacenta.UnitLifecycleDecryptRatchetScreen (modelDecrypt_allT1 modelDecrypt_zeroizingModel) in
/-- **The decrypt laws, the initiator contract axioms, `InitiatorSuccessShape` and the two establishment
laws hold together in one interpretation**, `Interp.modelEstablished`, with its view, the KEM model
`toyKem`, `optionEqImpl` for `Option::eq`, the constant `ok 0` for `kem::ciphertext_len` and the byte-stream
source: the shapes of every hypothesis `established_decrypt_hypotheses_jointly_satisfiable` takes.  In the
substitution sense of `UnitSatisfiabilityRecords`; not a statement that the real primitives meet them. -/
theorem established_decrypt_laws_model :
    Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape Interp.modelEstablished viewEstablished
        Model.Braid.toyKem @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
      Nonempty (InitiatorAxiom Interp.modelEstablished byteRng) ∧
      InitiatorSuccessShape Interp.modelEstablished byteRng byteCrc ∧
      DhPublicValidShape Interp.modelEstablished ∧
      KemCiphertextLenLawShape (ok 0#usize) Interp.modelEstablished := by
  have M := Tacenta.UnitLifecycleDecryptScreen.decrypt_joint_laws_model
  have hcodec : Tacenta.UnitSatisfiabilityJoint.DhCodecShape Interp.modelEstablished :=
    ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩,
      fun _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩⟩
  refine ⟨?_, ⟨?_⟩, ?_, ?_, ?_⟩
  · exact
      { dhCodec := hcodec
        dhAgree := M.dhAgree
        aeadOpen := M.aeadOpen
        viewInjective := M.viewInjective
        codec := by have h := M.codec; cases h; constructor <;> assumption
        braid := by have h := M.braid; cases h; constructor <;> assumption
        triple := by have h := M.triple; cases h; constructor <;> assumption
        messageKeyMaterial := M.messageKeyMaterial
        laws := by have h := M.laws; cases h; constructor <;> assumption
        truncatePrefix := M.truncatePrefix
        derivedKeys := by
          obtain ⟨h⟩ := M.derivedKeys; cases h; exact ⟨by constructor <;> assumption⟩
        agreements := by have h := M.agreements; cases h; constructor <;> assumption
        roundTrips := by have h := M.roundTrips; cases h; constructor <;> assumption
        validKey := ⟨Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32,
          Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32,
          Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32, rfl, rfl,
          Tacenta.SessionUnitRatchetImportInv.Ratchet.canonical_zeros, rfl⟩
        optionEq := M.optionEq }
  · exact
      { dhCodec := hcodec
        dhIdentity := modelDecrypt_allT1.dhIdentity
        dhAgree := modelDecrypt_allT1.dhAgree
        kemEncapsulate := modelDecrypt_allT1.kemEncapsulate
        xeddsaVerify := modelDecrypt_allT1.xeddsaVerify
        rngTotal := Tacenta.UnitOracleModel.byteRng_total
        random32 := fun _ _ _ => ⟨_, rfl⟩
        sessionHkdf := modelDecrypt_allT1.hkdf
        sessionZeroizing := by
          have h := modelDecrypt_zeroizingModel Tacenta.UnitSatisfiabilityJoint.SessionZ
          cases h; constructor <;> assumption
        tripleZeroizing := modelDecrypt_allT1.zeroizingTotal
        spqrZeroize := modelDecrypt_allT1.spqrZeroize
        braidHkdf := modelDecrypt_allT1.hkdf
        zeroizingArray := modelDecrypt_allT1.zeroizingArray
        rangeFullIndex := modelDecrypt_allT1.rangeFullIndex }
  · refine ⟨⟨oneKey, oneKey, rfl, oneKey_canonical, rfl, ?_, fun _ => ⟨Array.repeat 64#usize 0#u8, rfl⟩,
      fun k => ⟨k, ?_⟩⟩, ⟨alloc.vec.Vec.new U8, by simp; scalar_tac, fun rng => ⟨_, _, _, rfl⟩⟩⟩
    · show ok (decide (oneKey.val = oneKey.val)) = ok true
      simp
    · show ok (if oneKey.val = Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none else some k) =
        ok (some k)
      simp [oneKey_ne_zero]
  · intro k pkb h
    have hp : pkb = Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32 := by
      simpa [Interp.modelEstablished] using h.symm
    subst hp
    exact ⟨Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32, rfl,
      Tacenta.SessionUnitRatchetImportInv.Ratchet.canonical_zeros, rfl⟩
  · intro R rc crc pk rng ct ss rng' h
    simp only [Interp.modelEstablished, Tacenta.UnitLifecycleDecryptRatchetScreen.Interp.modelDecrypt,
      Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3, Tacenta.UnitSatisfiabilityJoint.Interp.model,
      ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact ⟨0#usize, rfl, by simp⟩

end Tacenta.UnitLifecycleEstablishedDecrypt


/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleEstablishedDecrypt.honestChunk_established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedDecrypt.honestChunk_established

/--
info: 'Tacenta.UnitLifecycleEstablishedDecrypt.established_initiator_decrypt_ratchet_hypotheses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedDecrypt.established_initiator_decrypt_ratchet_hypotheses

/--
info: 'Tacenta.UnitLifecycleEstablishedDecrypt.established_initiator_decrypt_ratchet_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedDecrypt.established_initiator_decrypt_ratchet_refines

/--
info: 'Tacenta.UnitLifecycleEstablishedDecrypt.established_initiator_decrypt_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedDecrypt.established_initiator_decrypt_refines

/--
info: 'Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.refines

/--
info: 'Tacenta.UnitLifecycleEstablishedDecrypt.sampleMessage_real_type' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedDecrypt.sampleMessage_real_type

/--
info: 'Tacenta.UnitLifecycleEstablishedDecrypt.sampleMessage_chunk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedDecrypt.sampleMessage_chunk

/--
info: 'Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable

/-- info: 'Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_length

/-- info: 'Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_canonical

/-- info: 'Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_ne_zero

/--
info: 'Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_laws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_laws_model

/--
info: @Tacenta.UnitLifecycleEstablishedDecrypt.honestChunk_established : ∀ {E : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore E) (crc : tacenta_session_unit.rand_core_1.CryptoRng E)
  (dh : Tacenta.UnitLifecycleT3.DhView) (our : tacenta_session_unit.lifecycle.Identity)
  (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
  (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
  (s : tacenta_session_unit.lifecycle.Session),
  tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
    ∀ (msg : Model.Braid.Msg),
      Tacenta.SessionUnitBraidT3.HonestChunk
        (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s).braid msg
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedDecrypt.honestChunk_established

/--
info: @Tacenta.UnitLifecycleEstablishedDecrypt.established_initiator_decrypt_ratchet_hypotheses : ∀ {R E : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
            Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
              Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                    @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                  ∀ (rc : tacenta_session_unit.rand_core_1.RngCore E)
                    (crc : tacenta_session_unit.rand_core_1.CryptoRng E) (our : tacenta_session_unit.lifecycle.Identity)
                    (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                    (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                    (s : tacenta_session_unit.lifecycle.Session),
                    tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
                        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                      ∀ (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
                        trace rng = oracle.draws →
                          (∀ (realComposite : tacenta_session_unit.tacenta_wire.Composite)
                              (modelComposite : Model.CompositeHeader.Composite)
                              (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
                              Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
                                  Except.ok (modelComposite, ciphertext) →
                                Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
                                  Tacenta.UnitLifecycleT3.IncomingChunkRefines view
                                    (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s).braid
                                    realComposite modelComposite) →
                            (∃ draw rest, trace rng = draw :: rest) →
                              Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses rngCore cryptoRng trace
                                dh view oracle s (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s)
                                message rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedDecrypt.established_initiator_decrypt_ratchet_hypotheses

/--
info: @Tacenta.UnitLifecycleEstablishedDecrypt.established_initiator_decrypt_ratchet_refines : ∀ {R E : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
            Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
              Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                    @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                  ∀ (rc : tacenta_session_unit.rand_core_1.RngCore E)
                    (crc : tacenta_session_unit.rand_core_1.CryptoRng E) (our : tacenta_session_unit.lifecycle.Identity)
                    (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                    (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                    (s : tacenta_session_unit.lifecycle.Session),
                    tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
                        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                      ∀ (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
                        trace rng = oracle.draws →
                          (∀ (realComposite : tacenta_session_unit.tacenta_wire.Composite)
                              (modelComposite : Model.CompositeHeader.Composite)
                              (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
                              Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
                                  Except.ok (modelComposite, ciphertext) →
                                Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
                                  Tacenta.UnitLifecycleT3.IncomingChunkRefines view
                                    (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s).braid
                                    realComposite modelComposite) →
                            (∃ draw rest, trace rng = draw :: rest) →
                              ∃ output,
                                tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng s message rng =
                                    Aeneas.Std.Result.ok output ∧
                                  Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                                    (Model.Lifecycle.decryptRatchet view oracle
                                      (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s)
                                      (Tacenta.UnitLifecycleT3.sliceOf message))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedDecrypt.established_initiator_decrypt_ratchet_refines

/--
info: @Tacenta.UnitLifecycleEstablishedDecrypt.established_initiator_decrypt_refines : ∀ {R E : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
            Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
              Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                    @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                  ∀ (rc : tacenta_session_unit.rand_core_1.RngCore E)
                    (crc : tacenta_session_unit.rand_core_1.CryptoRng E) (our : tacenta_session_unit.lifecycle.Identity)
                    (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                    (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                    (s : tacenta_session_unit.lifecycle.Session),
                    tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
                        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                      ∀ (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
                        tacenta_session_unit.serialization.message_type message =
                            Aeneas.Std.Result.ok (some tacenta_session_unit.serialization.MessageType.Ratchet) →
                          trace rng = oracle.draws →
                            (∀ (realComposite : tacenta_session_unit.tacenta_wire.Composite)
                                (modelComposite : Model.CompositeHeader.Composite)
                                (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
                                Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
                                    Except.ok (modelComposite, ciphertext) →
                                  Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
                                    Tacenta.UnitLifecycleT3.IncomingChunkRefines view
                                      (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s).braid
                                      realComposite modelComposite) →
                              (∃ draw rest, trace rng = draw :: rest) →
                                Tacenta.UnitLifecycleT3.PublicDecryptWitness rngCore cryptoRng trace dh oracle.braidKem
                                  view oracle s (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s)
                                  message rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedDecrypt.established_initiator_decrypt_refines

/--
info: @Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.refines : ∀ {R E : Type}
  {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {view : Model.Lifecycle.CodewordView}
  {oracle : Model.Lifecycle.Oracle} {rc : tacenta_session_unit.rand_core_1.RngCore E}
  {crc : tacenta_session_unit.rand_core_1.CryptoRng E} {our : tacenta_session_unit.lifecycle.Identity}
  {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  {expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes} {rng0 rng1 : E}
  {s : tacenta_session_unit.lifecycle.Session} {message : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R},
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses rngCore cryptoRng trace dh view oracle rc crc our
      bundle expected rng0 rng1 s message rng →
    Tacenta.UnitLifecycleT3.PublicDecryptWitness rngCore cryptoRng trace dh oracle.braidKem view oracle s
      (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s) message rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.refines

/--
info: Tacenta.UnitLifecycleEstablishedDecrypt.sampleMessage_real_type : tacenta_session_unit.serialization.message_type
    Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage =
  Aeneas.Std.Result.ok (some tacenta_session_unit.serialization.MessageType.Ratchet)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedDecrypt.sampleMessage_real_type

/--
info: Tacenta.UnitLifecycleEstablishedDecrypt.sampleMessage_chunk : ∀ (view : Model.Lifecycle.CodewordView)
  (braid : Model.Braid.BraidState) (realComposite : tacenta_session_unit.tacenta_wire.Composite)
  (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
  Model.CompositeHeader.decodeDetailed
        (Tacenta.UnitLifecycleT3.sliceOf Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage) =
      Except.ok (modelComposite, ciphertext) →
    Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
      Tacenta.UnitLifecycleT3.IncomingChunkRefines view braid realComposite modelComposite
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedDecrypt.sampleMessage_chunk

/--
info: Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable : ∀ (K : Model.Braid.Kem)
  (dh : Tacenta.UnitLifecycleT3.DhView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    Nonempty
        (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
      Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc →
        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
            ∀ (our : tacenta_session_unit.lifecycle.Identity),
              ∃ oracle bundle s rng1,
                oracle.braidKem = K ∧
                  ∀ (view : Model.Lifecycle.CodewordView),
                    Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses
                      Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                      Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh view oracle
                      Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc our
                      bundle bundle.bundle.identity_key [] rng1 s
                      Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
                      Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable

/-- info: Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_length : (1#u8 :: List.replicate 31 0#u8).length = ↑32#usize -/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_length

/--
info: Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_canonical : Tacenta.SessionUnitT1.canonicalX25519
    Tacenta.UnitLifecycleEstablishedDecrypt.oneKey =
  true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_canonical

/--
info: Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_ne_zero : ↑Tacenta.UnitLifecycleEstablishedDecrypt.oneKey ≠
  ↑Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_ne_zero

/--
info: Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_laws_model : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape
    Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished
    Tacenta.UnitLifecycleEstablishedDecrypt.viewEstablished Model.Braid.toyKem
    @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
  Nonempty
      (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished
        Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
    Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape
        Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc ∧
      Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape
          Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenLawShape (Aeneas.Std.Result.ok 0#usize)
          Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_laws_model

/--
info: structure Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses {R E : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (rc : tacenta_session_unit.rand_core_1.RngCore E)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng E) (our : tacenta_session_unit.lifecycle.Identity)
  (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
  (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
  (s : tacenta_session_unit.lifecycle.Session) (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) : Prop
number of parameters: 18
fields:
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.oracleOf : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf
      rngCore cryptoRng dh trace oracle
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.codec : Tacenta.UnitLifecycleT3.DhCodecOf dh
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts
      rngCore
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.derivedKeys : Nonempty
      Tacenta.SessionUnitT1.DerivedKeysModel
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.agreements : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
      oracle.braidKem
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.dhPublicValid : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.kemCiphertextLen : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.optionEq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.established : tacenta_session_unit.lifecycle.establish_initiator_for
        rc crc our bundle expected rng0 =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1)
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.messageType : tacenta_session_unit.serialization.message_type
        message =
      Aeneas.Std.Result.ok (some tacenta_session_unit.serialization.MessageType.Ratchet)
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.trace_eq : trace rng = oracle.draws
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.chunk : ∀
      (realComposite : tacenta_session_unit.tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
      (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
      Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
          Except.ok (modelComposite, ciphertext) →
        Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
          Tacenta.UnitLifecycleT3.IncomingChunkRefines view
            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s).braid realComposite modelComposite
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.draw : ∃ draw rest, trace rng = draw :: rest
constructor:
  Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses.mk {R E : Type}
    {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {view : Model.Lifecycle.CodewordView}
    {oracle : Model.Lifecycle.Oracle} {rc : tacenta_session_unit.rand_core_1.RngCore E}
    {crc : tacenta_session_unit.rand_core_1.CryptoRng E} {our : tacenta_session_unit.lifecycle.Identity}
    {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
    {expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes} {rng0 rng1 : E}
    {s : tacenta_session_unit.lifecycle.Session} {message : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R}
    (oracleOf : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : Tacenta.UnitLifecycleT3.DhCodecOf dh) (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    (derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel)
    (agreements : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem)
    (dhPublicValid : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid)
    (kemCiphertextLen : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (optionEq :
      Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
        @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq)
    (established :
      tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1))
    (messageType :
      tacenta_session_unit.serialization.message_type message =
        Aeneas.Std.Result.ok (some tacenta_session_unit.serialization.MessageType.Ratchet))
    (trace_eq : trace rng = oracle.draws)
    (chunk :
      ∀ (realComposite : tacenta_session_unit.tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
        (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
        Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
            Except.ok (modelComposite, ciphertext) →
          Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
            Tacenta.UnitLifecycleT3.IncomingChunkRefines view
              (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s).braid realComposite modelComposite)
    (draw : ∃ draw rest, trace rng = draw :: rest) :
    Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses rngCore cryptoRng trace dh view oracle rc crc
      our bundle expected rng0 rng1 s message rng
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedDecrypt.EstablishedDecryptHypotheses

/--
info: def Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished : Tacenta.UnitSatisfiabilityJoint.Interp :=
let __src := Tacenta.UnitLifecycleDecryptRatchetScreen.Interp.modelDecrypt;
{ PrivateKey := __src.PrivateKey, PublicKeyBytes := __src.PublicKeyBytes, KemKeyPair := __src.KemKeyPair,
  IncrementalKeyPair := __src.IncrementalKeyPair, EncapsState := __src.EncapsState, Zeroizing := __src.Zeroizing,
  dhPrivFromBytes := __src.dhPrivFromBytes,
  dhPrivPublicKey := fun x => Aeneas.Std.Result.ok Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32,
  dhPrivAgree := __src.dhPrivAgree, dhPrivToBytes := __src.dhPrivToBytes, dhPubFromBytes := __src.dhPubFromBytes,
  dhPubAsBytes := __src.dhPubAsBytes, dhPubEq := __src.dhPubEq, dhIsPrimeOrderPublic := __src.dhIsPrimeOrderPublic,
  aeadEncrypt := __src.aeadEncrypt, aeadDecrypt := __src.aeadDecrypt,
  kemEncapsulate := @Tacenta.UnitSatisfiabilityJoint.Interp.kemEncapsulate __src,
  kemDecapsulate := __src.kemDecapsulate, xeddsaVerify := __src.xeddsaVerify, hkdfSha256 := __src.hkdfSha256,
  hmacSha256 := __src.hmacSha256, HEADER_LEN := __src.HEADER_LEN, EK_VECTOR_LEN := __src.EK_VECTOR_LEN,
  CT1_LEN := __src.CT1_LEN, CT2_LEN := __src.CT2_LEN, ikpClone := __src.ikpClone,
  ikpGenerate := @Tacenta.UnitSatisfiabilityJoint.Interp.ikpGenerate __src, ikpHeader := __src.ikpHeader,
  ikpEkVector := __src.ikpEkVector, ikpDecapsulate := __src.ikpDecapsulate, esClone := __src.esClone,
  encapsulate1 := @Tacenta.UnitSatisfiabilityJoint.Interp.encapsulate1 __src, encapsulate2 := __src.encapsulate2,
  validateEk := __src.validateEk, blanketZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.blanketZeroize __src,
  arrayZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.arrayZeroize __src,
  tupleZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.tupleZeroize __src,
  pairZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.pairZeroize __src,
  vecZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.vecZeroize __src,
  zNew := @Tacenta.UnitSatisfiabilityJoint.Interp.zNew __src,
  zDeref := @Tacenta.UnitSatisfiabilityJoint.Interp.zDeref __src,
  zDerefMut := @Tacenta.UnitSatisfiabilityJoint.Interp.zDerefMut __src,
  vecPop := @Tacenta.UnitSatisfiabilityJoint.Interp.vecPop __src,
  vecCapacity := @Tacenta.UnitSatisfiabilityJoint.Interp.vecCapacity __src,
  vecTruncate := @Tacenta.UnitSatisfiabilityJoint.Interp.vecTruncate __src,
  optionClone := @Tacenta.UnitSatisfiabilityJoint.Interp.optionClone __src,
  optionAsMut := @Tacenta.UnitSatisfiabilityJoint.Interp.optionAsMut __src,
  rangeFullIndex := @Tacenta.UnitSatisfiabilityJoint.Interp.rangeFullIndex __src, divCeil := __src.divCeil }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished

/--
info: def Tacenta.UnitLifecycleEstablishedDecrypt.viewEstablished : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape
  Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished :=
{ privateKey := Tacenta.UnitLifecycleT3.arrayOf, publicKey := Tacenta.UnitLifecycleT3.arrayOf }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedDecrypt.viewEstablished

/--
info: def Tacenta.UnitLifecycleEstablishedDecrypt.oneKey : Aeneas.Std.Array Aeneas.Std.U8 32#usize :=
⟨1#u8 :: List.replicate 31 0#u8, Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_length⟩
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedDecrypt.oneKey
