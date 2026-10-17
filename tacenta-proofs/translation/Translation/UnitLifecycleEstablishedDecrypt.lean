import Translation.UnitLifecycleEstablishInitiatorShape

/-!
# `decrypt_ratchet` and the public `Session::decrypt` at an established initiator session

`UnitLifecycleEstablishInitiatorShape` derives, at every successful `establish_initiator_for` output `s`,
`Session::invariant` (under two assumed laws and `OptionEqU64Shape`), `CounterHeadroom` and
`SessionRefines dh K s (establishedModelOf dh s)`.  This module feeds them to the `decrypt_ratchet`
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

## What it does not show

* That an honest peer can produce a frame this session accepts.  A freshly established initiator holds no
  receiving chain; the only peer that could send it an accepted ratchet frame is a responder established
  from this session's initial message, which only this session's first `encrypt` produces, and that call
  moves the Braid out of `KeysUnsampled`.  So the success arm is covered by the theorem and not shown
  reachable in an honest run; what this establishes at a real state is every refusal and its effects.
* Initial-type frames, `encrypt`, `establish_responder` and `import`.
* The chunk relation for a frame that carries a Braid agreement chunk, and the draw: the caller's.
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
