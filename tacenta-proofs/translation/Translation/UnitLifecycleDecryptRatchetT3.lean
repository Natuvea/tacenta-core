import Translation.UnitLifecycleInitialDispatch
import Translation.UnitSatisfiabilityErasureAgrees

/-!
# `decrypt_ratchet` refines the model's decrypt step, with the eviction retry loop

`Session::decrypt_ratchet` is the transaction the shipped `Session::decrypt` calls on a ratchet
message.  It checks the Braid's terminal state, decodes the message, runs the Braid receive, two
Diffie-Hellman agreements around one random draw, the Triple receive with the eviction retry loop
of `receive_with_eviction`, the message-key derivation and the AEAD open, and commits only after
the tag verifies.  The model's twin is `Model.Lifecycle.decryptRatchet`, whose retry loop is the
fuel-indexed `receiveWithEvictionLoop` behind the public relation
`Model.Lifecycle.ReceiveWithEvictionLoopResult`.

This module states the refinement and its hypotheses (section "Statement"), and proves it.

## The hypotheses, by kind

* **About opaque operations (assumed; `LIMITATIONS.md`).**  `DecryptOracleOf`, the four clauses
  of `OracleOf` this transaction uses (the public key and the agreement of the DH boundary, the
  AEAD open, the 32-byte draw); `DhCodecOf`, the byte views of the two opaque key types; the
  axiom-level fields of `DecryptRatchetContracts`; and the agreements of `DecryptRatchetAgreements`
  about the KDFs, the zeroizing wrappers and the KEM.  `SessionUnitSpqrT3.VecRetainAgrees` and
  `SessionUnitSpqrT3.RemoveSkippedAtAgrees` in that record are statements about translated
  functions that the session unit takes as assumptions (`GAP-REGISTER.md`, row
  `SESSION-SPARSE-AGREEMENTS`).
* **About the run (per run).**  `SessionRefines`, `DecryptRatchetHeadroom`, the trace equation, and
  `DecryptRatchetRun`, whose fields are asked of the composite the run's message decodes to (the
  model's decoder is a function, so each field speaks about one value): the Braid chunk relation
  and `HonestChunk`, the Braid epoch headroom, one draw left in the trace, and the receive bounds
  `RetryRunBounds` of the model Triple state.

`UnitLifecycleDecryptRatchetScreen.lean` shows these hypotheses satisfiable.

## The conclusion

For every input that meets them, the generated function returns, and either its result, the
session it leaves and the trace refine the model's step (`StepRefines`), or the run is a Triple
refusal whose reason is not a full skipped-key store (`TripleRefusalOpen`).  The second disjunct
is the one path this module leaves open: no theorem of this tree relates a concrete Triple receive
refusal other than a full store to the model's detailed refusal, so neither a direct refusal of
that kind nor one returned by a retry inside the loop is related to the model.  The loop theorem
below reduces the retry case to that one statement about a single Triple receive.
-/

namespace Tacenta.UnitLifecycleDecryptRatchetT3

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3

/-! ## Statement -/

/-- The conservative bound Aeneas gives every `usize`, at both platform widths. -/
theorem cMax_usize : UScalar.cMax UScalarTy.Usize = 4294967295 := by decide

/-- The four clauses of `OracleOf` that `decrypt_ratchet` uses, word for word.  `OracleOf` implies
this record (`DecryptOracleOf.of_oracleOf`); the other clauses of `OracleOf` (KEM, signing,
identity, AEAD seal) are not hypotheses of this module. -/
structure DecryptOracleOf {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (dh : DhView) (trace : R → List Model.Lifecycle.Key)
    (oracle : Model.Lifecycle.Oracle) : Prop where
  dhPublic : ∀ secret,
    ∃ publicKey, tacenta_boundary.dh.PrivateKey.public_key secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)
  dhAgree : ∀ secret publicKey,
    ∃ result, tacenta_boundary.dh.PrivateKey.agree secret publicKey = ok result ∧
      result.map arrayOf = oracle.dhAgree (dh.privateKey secret) (dh.publicKey publicKey)
  aeadOpen : ∀ key1 key2 iv ciphertext associatedData,
    ∃ result,
      tacenta_boundary.aead.decrypt key1 key2 iv ciphertext associatedData = ok result ∧
      resultOptionOf vecOf result = oracle.aeadOpen (arrayOf key1) (arrayOf key2)
        (arrayOf iv) (sliceOf ciphertext) (sliceOf associatedData)
  random32 : ∀ rng draw rest, trace rng = draw :: rest →
    ∃ value rng',
      lifecycle.random_secret rngCore cryptoRng rng = ok (value, rng') ∧
      arrayOf value = draw ∧ trace rng' = rest

theorem DecryptOracleOf.of_oracleOf {R : Type}
    {rngCore : rand_core_1.RngCore R} {cryptoRng : rand_core_1.CryptoRng R}
    {dh : DhView} {kem : KemView} {trace : R → List Model.Lifecycle.Key}
    {oracle : Model.Lifecycle.Oracle}
    (h : OracleOf rngCore cryptoRng dh kem trace oracle) :
    DecryptOracleOf rngCore cryptoRng dh trace oracle :=
  ⟨h.dhPublic, h.dhAgree, h.aeadOpen, h.random32⟩

/-- The receive bounds of one run, stated of the model Triple state, the model header and the
model's sparse output.  The first nine fields are `RetryReceiveBounds` read through the header
and output relations; the last two bound each skipped-key store by `2^32 - 1 - 2000`, so the
saturating arithmetic of `receive_shortfall` and the classical eviction scan stay exact enough at
both platform widths (`RetryRunBounds.toRetryReceiveBounds`). -/
structure RetryRunBounds (state : Model.Triple.State) (header : Model.Triple.Header)
    (output : Option Model.SparseRatchet.Output) : Prop where
  classicalMatch : (state.classical.skipped.filter
    (fun x => x.1 == header.dr.dh && x.2.1 == header.dr.n)).length ≤ 1
  classicalEvents : state.classical.events + 1 < Std.U32.max
  sparseEpoch : state.postQuantum.epoch + 1 < Std.U64.max
  sparseChainsRoom : state.postQuantum.chains.length + 2 < Usize.max
  sparseChainEpochs : ∀ p ∈ state.postQuantum.chains,
    p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max
  sparseSkippedEpochs : ∀ sk ∈ state.postQuantum.skipped,
    sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max
  sparseOutputEpoch : ∀ o, output = some o →
    o.keyEpoch + Model.SparseRatchet.epochsKept ≤ Std.U64.max
  sparseMatch : (state.postQuantum.skipped.filter
    (fun x => x.1 == header.epoch && x.2.1 == header.pqN)).length ≤ 1
  sparseCounters : ∀ p ∈ state.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
    (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max
  classicalStore : state.classical.skipped.length + Model.State.maxSkippedStore ≤
    UScalar.cMax UScalarTy.Usize
  sparseStore : state.postQuantum.skipped.length + Model.SparseRatchet.maxSkippedStore ≤
    UScalar.cMax UScalarTy.Usize

/-- The agreements `decrypt_ratchet`'s refinement takes beyond the T1 contract record: the KDF,
zeroizing-wrapper and sparse-store agreements of the Triple receive and the message keys, the KEM
and erasure agreements of the Braid receive, and the 32-byte wrapper round trip of the lifecycle.
`ErasureCloneAgrees` is not here: it is a theorem of the unit
(`UnitSatisfiabilityErasureAgrees.erasureCloneAgrees`). -/
structure DecryptRatchetAgreements (K : Model.Braid.Kem) : Prop where
  hmac : Tacenta.SessionUnitT3.HmacAgrees
  hkdf : Tacenta.SessionUnitT3.HkdfAgrees
  zeroizing64 : Tacenta.SessionUnitT3.ZeroizingRoundTrips
  zeroizing80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80
  zeroizing96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96
  zeroizingSparse64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64
  vecRetain : Tacenta.SessionUnitSpqrT3.VecRetainAgrees
  removeSkipped : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees
  kem : Tacenta.SessionUnitBraidT3.KemAgreesFor K
  erasure : Tacenta.SessionUnitBraidT3.ErasureAgrees
  kemLen : Tacenta.SessionUnitBraidT3.KemLenAgrees K
  validateEk : Tacenta.SessionUnitBraidT3.ValidateEkAgrees K
  kemClone : Tacenta.SessionUnitBraidT3.KemCloneAgrees
  zeroizing32 : ZeroizingRoundTrips (Array Std.U8 32#usize)

/-- The per-run conditions of one `decrypt_ratchet` call.  Every field that mentions a composite
is asked of the composite `message` decodes to, and `Model.CompositeHeader.decodeDetailed` is a
function, so each speaks about one value; for a message that does not decode they say nothing,
and the decode refusal needs nothing from them. -/
structure DecryptRatchetRun {R : Type} (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (trace : R → List Model.Lifecycle.Key)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R) : Prop where
  chunk : ∀ (realComposite : tacenta_wire.Composite)
      (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (modelComposite, ciphertext) →
      CompositeRefines realComposite modelComposite →
      IncomingChunkRefines view model.braid realComposite modelComposite
  honest : ∀ (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (modelComposite, ciphertext) →
      Tacenta.SessionUnitBraidT3.HonestChunk model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)
  braidEpoch : (Tacenta.SessionUnitBraidT1.State.epoch_val real.braid.state).val + 1 <
    Std.U64.max
  draw : ∃ draw rest, trace rng = draw :: rest
  retry : ∀ (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (modelComposite, ciphertext) →
      RetryRunBounds model.triple (Model.Lifecycle.tripleHeaderOf modelComposite)
        (Model.Lifecycle.sparseOutputOf
          (Model.Braid.receive oracle.braidKem model.braid
            (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1)

/-- The path this module leaves open: the generated function refused with a Triple error that is
not a full skipped-key store. -/
def TripleRefusalOpen {R : Type}
    (output : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error ×
      lifecycle.Session × R) : Prop :=
  ∃ reason, output.1 = .Err (.Triple reason) ∧ lifecycle.full_store reason = ok none

/-- The statement of `decrypt_ratchet_refines`, as a proposition.  Kept beside the theorem so that
the screen module can name it. -/
def DecryptRatchetRefinesStatement : Prop :=
  ∀ {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
    DecryptOracleOf rngCore cryptoRng dh trace oracle →
    DhCodecOf dh →
    Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
    ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
    DecryptRatchetAgreements oracle.braidKem →
    ∀ (real : lifecycle.Session) (model : Model.Lifecycle.Session)
      (message : Slice Std.U8) (rng : R),
      SessionRefines dh oracle.braidKem real model →
      Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real →
      trace rng = oracle.draws →
      DecryptRatchetRun view oracle trace real model message rng →
      ∃ output,
        lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng = ok output ∧
        (StepRefines trace dh oracle.braidKem output
            (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) ∨
          TripleRefusalOpen output)

end Tacenta.UnitLifecycleDecryptRatchetT3

/-! ## Pins

The bodies of the records and of the statement are pinned, so a field added, removed or changed
fails the build here. -/

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf.of_oracleOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.sign,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf.of_oracleOf

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetT3.cMax_usize' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetT3.cMax_usize

/--
info: @Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf.of_oracleOf : ∀ {R : Type}
  {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
  {dh : Tacenta.UnitLifecycleT3.DhView} {kem : Tacenta.UnitLifecycleT3.KemView} {trace : R → List Model.Lifecycle.Key}
  {oracle : Model.Lifecycle.Oracle},
  Tacenta.UnitLifecycleT3.OracleOf rngCore cryptoRng dh kem trace oracle →
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf.of_oracleOf

/--
info: structure Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (dh : Tacenta.UnitLifecycleT3.DhView) (trace : R → List Model.Lifecycle.Key) (oracle : Model.Lifecycle.Oracle) : Prop
number of parameters: 6
fields:
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf.dhPublic : ∀
      (secret : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
      ∃ publicKey,
        secret.public_key = Aeneas.Std.Result.ok publicKey ∧
          dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf.dhAgree : ∀
      (secret : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
      (publicKey : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
      ∃ result,
        secret.agree publicKey = Aeneas.Std.Result.ok result ∧
          Option.map Tacenta.UnitLifecycleT3.arrayOf result =
            oracle.dhAgree (dh.privateKey secret) (dh.publicKey publicKey)
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf.aeadOpen : ∀
      (key1 key2 : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (iv : Aeneas.Std.Array Aeneas.Std.U8 16#usize)
      (ciphertext associatedData : Aeneas.Std.Slice Aeneas.Std.U8),
      ∃ result,
        tacenta_session_unit.tacenta_boundary.aead.decrypt key1 key2 iv ciphertext associatedData =
            Aeneas.Std.Result.ok result ∧
          Tacenta.UnitLifecycleT3.resultOptionOf Tacenta.UnitLifecycleT3.vecOf result =
            oracle.aeadOpen (Tacenta.UnitLifecycleT3.arrayOf key1) (Tacenta.UnitLifecycleT3.arrayOf key2)
              (Tacenta.UnitLifecycleT3.arrayOf iv) (Tacenta.UnitLifecycleT3.sliceOf ciphertext)
              (Tacenta.UnitLifecycleT3.sliceOf associatedData)
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf.random32 : ∀ (rng : R) (draw : Model.Lifecycle.Key)
      (rest : List Model.Lifecycle.Key),
      trace rng = draw :: rest →
        ∃ value rng',
          tacenta_session_unit.lifecycle.random_secret rngCore cryptoRng rng = Aeneas.Std.Result.ok (value, rng') ∧
            Tacenta.UnitLifecycleT3.arrayOf value = draw ∧ trace rng' = rest
constructor:
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf.mk {R : Type}
    {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
    {dh : Tacenta.UnitLifecycleT3.DhView} {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle}
    (dhPublic :
      ∀ (secret : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
        ∃ publicKey,
          secret.public_key = Aeneas.Std.Result.ok publicKey ∧
            dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret))
    (dhAgree :
      ∀ (secret : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
        (publicKey : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
        ∃ result,
          secret.agree publicKey = Aeneas.Std.Result.ok result ∧
            Option.map Tacenta.UnitLifecycleT3.arrayOf result =
              oracle.dhAgree (dh.privateKey secret) (dh.publicKey publicKey))
    (aeadOpen :
      ∀ (key1 key2 : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (iv : Aeneas.Std.Array Aeneas.Std.U8 16#usize)
        (ciphertext associatedData : Aeneas.Std.Slice Aeneas.Std.U8),
        ∃ result,
          tacenta_session_unit.tacenta_boundary.aead.decrypt key1 key2 iv ciphertext associatedData =
              Aeneas.Std.Result.ok result ∧
            Tacenta.UnitLifecycleT3.resultOptionOf Tacenta.UnitLifecycleT3.vecOf result =
              oracle.aeadOpen (Tacenta.UnitLifecycleT3.arrayOf key1) (Tacenta.UnitLifecycleT3.arrayOf key2)
                (Tacenta.UnitLifecycleT3.arrayOf iv) (Tacenta.UnitLifecycleT3.sliceOf ciphertext)
                (Tacenta.UnitLifecycleT3.sliceOf associatedData))
    (random32 :
      ∀ (rng : R) (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
        trace rng = draw :: rest →
          ∃ value rng',
            tacenta_session_unit.lifecycle.random_secret rngCore cryptoRng rng = Aeneas.Std.Result.ok (value, rng') ∧
              Tacenta.UnitLifecycleT3.arrayOf value = draw ∧ trace rng' = rest) :
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf

/--
info: structure Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds (state : Model.Triple.State)
  (header : Model.Triple.Header) (output : Option Model.SparseRatchet.Output) : Prop
number of parameters: 3
fields:
  Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.classicalMatch : (List.filter
          (fun x => x.1 == header.dr.dh && x.2.1 == header.dr.n) state.classical.skipped).length ≤
      1
  Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.classicalEvents : state.classical.events + 1 < Aeneas.Std.U32.max
  Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.sparseEpoch : state.postQuantum.epoch + 1 < Aeneas.Std.U64.max
  Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.sparseChainsRoom : state.postQuantum.chains.length + 2 <
      Aeneas.Std.Usize.max
  Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.sparseChainEpochs : ∀ p ∈ state.postQuantum.chains,
      p.1 + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max
  Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.sparseSkippedEpochs : ∀ sk ∈ state.postQuantum.skipped,
      sk.1 + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max
  Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.sparseOutputEpoch : ∀ (o : Model.SparseRatchet.Output),
      output = some o → o.keyEpoch + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max
  Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.sparseMatch : (List.filter
          (fun x => x.1 == header.epoch && x.2.1 == header.pqN) state.postQuantum.skipped).length ≤
      1
  Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.sparseCounters : ∀ p ∈ state.postQuantum.chains,
      ∀ (ch : Model.SparseRatchet.Chain), p.2.send = some ch ∨ p.2.receive = some ch → ch.n < Aeneas.Std.U64.max
  Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.classicalStore : state.classical.skipped.length +
        Model.State.maxSkippedStore ≤
      Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize
  Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.sparseStore : state.postQuantum.skipped.length +
        Model.SparseRatchet.maxSkippedStore ≤
      Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize
constructor:
  Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.mk {state : Model.Triple.State} {header : Model.Triple.Header}
    {output : Option Model.SparseRatchet.Output}
    (classicalMatch :
      (List.filter (fun x => x.1 == header.dr.dh && x.2.1 == header.dr.n) state.classical.skipped).length ≤ 1)
    (classicalEvents : state.classical.events + 1 < Aeneas.Std.U32.max)
    (sparseEpoch : state.postQuantum.epoch + 1 < Aeneas.Std.U64.max)
    (sparseChainsRoom : state.postQuantum.chains.length + 2 < Aeneas.Std.Usize.max)
    (sparseChainEpochs : ∀ p ∈ state.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max)
    (sparseSkippedEpochs : ∀ sk ∈ state.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max)
    (sparseOutputEpoch :
      ∀ (o : Model.SparseRatchet.Output),
        output = some o → o.keyEpoch + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max)
    (sparseMatch :
      (List.filter (fun x => x.1 == header.epoch && x.2.1 == header.pqN) state.postQuantum.skipped).length ≤ 1)
    (sparseCounters :
      ∀ p ∈ state.postQuantum.chains,
        ∀ (ch : Model.SparseRatchet.Chain), p.2.send = some ch ∨ p.2.receive = some ch → ch.n < Aeneas.Std.U64.max)
    (classicalStore :
      state.classical.skipped.length + Model.State.maxSkippedStore ≤ Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize)
    (sparseStore :
      state.postQuantum.skipped.length + Model.SparseRatchet.maxSkippedStore ≤
        Aeneas.Std.UScalar.cMax Aeneas.Std.UScalarTy.Usize) :
    Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds state header output
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds

/--
info: structure Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements (K : Model.Braid.Kem) : Prop
number of parameters: 1
fields:
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.hmac : Tacenta.SessionUnitT3.HmacAgrees
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.hkdf : Tacenta.SessionUnitT3.HkdfAgrees
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.zeroizing64 : Tacenta.SessionUnitT3.ZeroizingRoundTrips
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.zeroizing80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.zeroizing96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.zeroizingSparse64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.vecRetain : Tacenta.SessionUnitSpqrT3.VecRetainAgrees
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.removeSkipped : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.kem : Tacenta.SessionUnitBraidT3.KemAgreesFor K
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.erasure : Tacenta.SessionUnitBraidT3.ErasureAgrees
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.kemLen : Tacenta.SessionUnitBraidT3.KemLenAgrees K
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.validateEk : Tacenta.SessionUnitBraidT3.ValidateEkAgrees
      K
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.kemClone : Tacenta.SessionUnitBraidT3.KemCloneAgrees
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.zeroizing32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)
constructor:
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements.mk {K : Model.Braid.Kem}
    (hmac : Tacenta.SessionUnitT3.HmacAgrees) (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (zeroizing64 : Tacenta.SessionUnitT3.ZeroizingRoundTrips)
    (zeroizing80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (zeroizing96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96)
    (zeroizingSparse64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64)
    (vecRetain : Tacenta.SessionUnitSpqrT3.VecRetainAgrees)
    (removeSkipped : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees) (kem : Tacenta.SessionUnitBraidT3.KemAgreesFor K)
    (erasure : Tacenta.SessionUnitBraidT3.ErasureAgrees) (kemLen : Tacenta.SessionUnitBraidT3.KemLenAgrees K)
    (validateEk : Tacenta.SessionUnitBraidT3.ValidateEkAgrees K) (kemClone : Tacenta.SessionUnitBraidT3.KemCloneAgrees)
    (zeroizing32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Aeneas.Std.Array Aeneas.Std.U8 32#usize)) :
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements K
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements

/--
info: structure Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun {R : Type} (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (trace : R → List Model.Lifecycle.Key)
  (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session)
  (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) : Prop
number of parameters: 8
fields:
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun.chunk : ∀
      (realComposite : tacenta_session_unit.tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
      (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
      Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
          Except.ok (modelComposite, ciphertext) →
        Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
          Tacenta.UnitLifecycleT3.IncomingChunkRefines view model.braid realComposite modelComposite
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun.honest : ∀ (modelComposite : Model.CompositeHeader.Composite)
      (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
      Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
          Except.ok (modelComposite, ciphertext) →
        Tacenta.SessionUnitBraidT3.HonestChunk model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun.braidEpoch : ↑(Tacenta.SessionUnitBraidT1.State.epoch_val
            real.braid.state) +
        1 <
      Aeneas.Std.U64.max
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun.draw : ∃ draw rest, trace rng = draw :: rest
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun.retry : ∀ (modelComposite : Model.CompositeHeader.Composite)
      (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
      Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
          Except.ok (modelComposite, ciphertext) →
        Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds model.triple
          (Model.Lifecycle.tripleHeaderOf modelComposite)
          (Model.Lifecycle.sparseOutputOf
            (Model.Braid.receive oracle.braidKem model.braid
                  (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1)
constructor:
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun.mk {R : Type} {view : Model.Lifecycle.CodewordView}
    {oracle : Model.Lifecycle.Oracle} {trace : R → List Model.Lifecycle.Key}
    {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R}
    (chunk :
      ∀ (realComposite : tacenta_session_unit.tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
        (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
        Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
            Except.ok (modelComposite, ciphertext) →
          Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
            Tacenta.UnitLifecycleT3.IncomingChunkRefines view model.braid realComposite modelComposite)
    (honest :
      ∀ (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
        Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
            Except.ok (modelComposite, ciphertext) →
          Tacenta.SessionUnitBraidT3.HonestChunk model.braid
            (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (braidEpoch : ↑(Tacenta.SessionUnitBraidT1.State.epoch_val real.braid.state) + 1 < Aeneas.Std.U64.max)
    (draw : ∃ draw rest, trace rng = draw :: rest)
    (retry :
      ∀ (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
        Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
            Except.ok (modelComposite, ciphertext) →
          Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds model.triple
            (Model.Lifecycle.tripleHeaderOf modelComposite)
            (Model.Lifecycle.sparseOutputOf
              (Model.Braid.receive oracle.braidKem model.braid
                    (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1)) :
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun view oracle trace real model message rng
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun

/--
info: def Tacenta.UnitLifecycleDecryptRatchetT3.TripleRefusalOpen : {R : Type} →
  Aeneas.Std.core.result.Result (Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8) tacenta_session_unit.lifecycle.Error ×
      tacenta_session_unit.lifecycle.Session × R →
    Prop :=
fun {R} output =>
  ∃ reason,
    output.1 = Aeneas.Std.core.result.Result.Err (tacenta_session_unit.lifecycle.Error.Triple reason) ∧
      tacenta_session_unit.lifecycle.full_store reason = Aeneas.Std.Result.ok none
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetT3.TripleRefusalOpen

/--
info: def Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRefinesStatement : Prop :=
∀ {R : Type} (rngCore : tacenta_session_unit.rand_core_1.RngCore R)
  (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
  (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
            ∀ (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session)
              (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
              Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem real model →
                Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real →
                  trace rng = oracle.draws →
                    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun view oracle trace real model message rng →
                      ∃ output,
                        tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
                            Aeneas.Std.Result.ok output ∧
                          (Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                              (Model.Lifecycle.decryptRatchet view oracle model
                                (Tacenta.UnitLifecycleT3.sliceOf message)) ∨
                            Tacenta.UnitLifecycleDecryptRatchetT3.TripleRefusalOpen output)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRefinesStatement
