import Translation.UnitLifecycleInitialDispatch
import Translation.UnitLifecycleRetryLoopT3
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



/-! ## The generated call, up to the Triple receive

`DecryptPrefix` holds the result of every generated call `decrypt_ratchet` makes before the Triple
receive with eviction.  The three theorems after it give the generated function's result from the
Triple receive's: a refusal, an AEAD refusal, a success. -/

structure DecryptPrefix {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R) (real : lifecycle.Session) (message : Slice Std.U8)
    (rng rngNext : R) where
  decoded : tacenta_wire.DecodedMessage
  msg : tacenta_braid.Msg
  epoch : Std.U64
  out : Option tacenta_braid.Output
  next : tacenta_braid.Braid
  sparse : Option tacenta_spqr.Output
  peer : tacenta_boundary.dh.PublicKeyBytes
  recvSecret : Array Std.U8 32#usize
  sendSecret : Array Std.U8 32#usize
  candidateBytes : Array Std.U8 32#usize
  newPublicBytes : Array Std.U8 32#usize
  before : Array Std.U8 32#usize
  candidatePrivate : tacenta_boundary.dh.PrivateKey
  candidatePublic : tacenta_boundary.dh.PublicKeyBytes
  header : tacenta_triple.Header
  wrappedRecv : zeroize.Zeroizing (Array Std.U8 32#usize)
  wrappedSend : zeroize.Zeroizing (Array Std.U8 32#usize)
  hready : tacenta_braid.Braid.failed real.braid = ok false
  hdecode : tacenta_wire.decode_message message = ok (.Ok decoded)
  hmsg : lifecycle.msg_of decoded.header = ok msg
  hreceive : tacenta_braid.Braid.receive real.braid msg = ok (epoch, out, next)
  hsparse : RealSparseConversion out sparse
  hpeer : tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer
  hfirst : tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret)
  hwrapRecv : zeroize.Zeroizing.new
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv
  hderefRecv : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret
  hrandom : lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rngNext)
  hcandidate : tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate
  hsecond : tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer = ok (some sendSecret)
  hwrapSend : zeroize.Zeroizing.new
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret = ok wrappedSend
  hderefSend : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend = ok sendSecret
  hbefore : tacenta_triple.State.sending_public real.triple = ok before
  hheader : lifecycle.triple_header_of decoded.header = ok header
  hpublic : tacenta_boundary.dh.PrivateKey.public_key candidatePrivate = ok candidatePublic
  hpublicBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic = ok newPublicBytes

theorem DecryptPrefix.triple_refusal {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R} {real : lifecycle.Session} {message : Slice Std.U8}
    {rng rngNext : R} (P : DecryptPrefix rngCore cryptoRng real message rng rngNext)
    (reason : tacenta_triple.TripleError)
    (htriple : lifecycle.receive_with_eviction real.triple P.decoded.header P.header
      P.recvSecret P.sendSecret P.newPublicBytes P.sparse = ok (.Err reason)) :
    lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Triple reason), real, rngNext) := by
  rcases P with ⟨decoded, msg, epoch, out, next, sparse, peer, recvSecret, sendSecret,
    candidateBytes, newPublicBytes, before, candidatePrivate, candidatePublic, header, wrappedRecv,
    wrappedSend, hready, hdecode, hmsg, hreceive, hsparse, hpeer, hfirst, hwrapRecv, hderefRecv,
    hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader, hpublic, hpublicBytes⟩
  unfold lifecycle.Session.decrypt_ratchet
  cases hsparse with
  | none hout =>
      simp [hready, hdecode, hmsg, hreceive, hout, hpeer, hfirst, hwrapRecv,
        hderefRecv, hrandom, hcandidate, hsecond, hwrapSend, hderefSend,
        hbefore, hheader, hpublic, hpublicBytes, htriple]
  | some realSparse converted hout hconverted =>
      simp [hready, hdecode, hmsg, hreceive, hout, hconverted, hpeer, hfirst,
        hwrapRecv, hderefRecv, hrandom, hcandidate, hsecond, hwrapSend,
        hderefSend, hbefore, hheader, hpublic, hpublicBytes, htriple]


noncomputable abbrev wrap32 : zeroize.Zeroize (Array Std.U8 32#usize) :=
  Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)

theorem DecryptPrefix.aead_refusal {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R} {real : lifecycle.Session} {message : Slice Std.U8}
    {rng rngNext : R} (P : DecryptPrefix rngCore cryptoRng real message rng rngNext)
    (tripleCandidate : tacenta_triple.State) (mk : Array Std.U8 32#usize)
    (wrappedMk : zeroize.Zeroizing (Array Std.U8 32#usize))
    (keys : Tacenta.UnitLifecycleT1.MessageKeyMaterial)
    (wrappedKeys : zeroize.Zeroizing Tacenta.UnitLifecycleT1.MessageKeyMaterial)
    (ad : alloc.vec.Vec Std.U8) (aeadError : Unit)
    (htriple : lifecycle.receive_with_eviction real.triple P.decoded.header P.header
      P.recvSecret P.sendSecret P.newPublicBytes P.sparse = ok (.Ok (tripleCandidate, mk)))
    (hwrapMk : zeroize.Zeroizing.new wrap32 mk = ok wrappedMk)
    (hderefMk : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref wrap32 wrappedMk = ok mk)
    (hkeys : tacenta_ratchet.message_keys mk tacenta_ratchet.LabelSet.Tacenta = ok keys)
    (hwrapKeys : zeroize.Zeroizing.new Tacenta.UnitLifecycleT1.messageKeyMaterialZeroize keys =
      ok wrappedKeys)
    (hderefKeys : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      Tacenta.UnitLifecycleT1.messageKeyMaterialZeroize wrappedKeys = ok keys)
    (had : serialization.concat_ad (alloc.vec.Vec.deref real.identity_ad) P.decoded.header =
      ok ad)
    (haead : tacenta_boundary.aead.decrypt keys.1 keys.2.1 keys.2.2
      (alloc.vec.Vec.deref P.decoded.ciphertext) (alloc.vec.Vec.deref ad) = ok (.Err aeadError)) :
    lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, real, rngNext) := by
  rcases P with ⟨decoded, msg, epoch, out, next, sparse, peer, recvSecret, sendSecret,
    candidateBytes, newPublicBytes, before, candidatePrivate, candidatePublic, header, wrappedRecv,
    wrappedSend, hready, hdecode, hmsg, hreceive, hsparse, hpeer, hfirst, hwrapRecv, hderefRecv,
    hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader, hpublic, hpublicBytes⟩
  rcases keys with ⟨encKey, macKey, ivKey⟩
  unfold lifecycle.Session.decrypt_ratchet
  cases hsparse with
  | none hout =>
      simp [hready, hdecode, hmsg, hreceive, hout, hpeer, hfirst, hwrapRecv,
        hderefRecv, hrandom, hcandidate, hsecond, hwrapSend, hderefSend,
        hbefore, hheader, hpublic, hpublicBytes, htriple, hwrapMk, hderefMk, hkeys,
        hwrapKeys, hderefKeys, had, haead]
  | some realSparse converted hout hconverted =>
      simp [hready, hdecode, hmsg, hreceive, hout, hconverted, hpeer, hfirst,
        hwrapRecv, hderefRecv, hrandom, hcandidate, hsecond, hwrapSend,
        hderefSend, hbefore, hheader, hpublic, hpublicBytes, htriple, hwrapMk, hderefMk, hkeys,
        hwrapKeys, hderefKeys, had, haead]

theorem DecryptPrefix.success {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R} {real : lifecycle.Session} {message : Slice Std.U8}
    {rng rngNext : R} (P : DecryptPrefix rngCore cryptoRng real message rng rngNext)
    (tripleCandidate : tacenta_triple.State) (mk : Array Std.U8 32#usize)
    (wrappedMk : zeroize.Zeroizing (Array Std.U8 32#usize))
    (keys : Tacenta.UnitLifecycleT1.MessageKeyMaterial)
    (wrappedKeys : zeroize.Zeroizing Tacenta.UnitLifecycleT1.MessageKeyMaterial)
    (ad : alloc.vec.Vec Std.U8) (plaintext : alloc.vec.Vec Std.U8)
    (htriple : lifecycle.receive_with_eviction real.triple P.decoded.header P.header
      P.recvSecret P.sendSecret P.newPublicBytes P.sparse = ok (.Ok (tripleCandidate, mk)))
    (hwrapMk : zeroize.Zeroizing.new wrap32 mk = ok wrappedMk)
    (hderefMk : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref wrap32 wrappedMk = ok mk)
    (hkeys : tacenta_ratchet.message_keys mk tacenta_ratchet.LabelSet.Tacenta = ok keys)
    (hwrapKeys : zeroize.Zeroizing.new Tacenta.UnitLifecycleT1.messageKeyMaterialZeroize keys =
      ok wrappedKeys)
    (hderefKeys : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      Tacenta.UnitLifecycleT1.messageKeyMaterialZeroize wrappedKeys = ok keys)
    (had : serialization.concat_ad (alloc.vec.Vec.deref real.identity_ad) P.decoded.header =
      ok ad)
    (haead : tacenta_boundary.aead.decrypt keys.1 keys.2.1 keys.2.2
      (alloc.vec.Vec.deref P.decoded.ciphertext) (alloc.vec.Vec.deref ad) = ok (.Ok plaintext)) :
    lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext,
        { { real with triple := tripleCandidate, braid := P.next } with
          ratchet_private :=
            if tripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
              real.ratchet_private else P.candidatePrivate }, rngNext) := by
  rcases P with ⟨decoded, msg, epoch, out, next, sparse, peer, recvSecret, sendSecret,
    candidateBytes, newPublicBytes, before, candidatePrivate, candidatePublic, header, wrappedRecv,
    wrappedSend, hready, hdecode, hmsg, hreceive, hsparse, hpeer, hfirst, hwrapRecv, hderefRecv,
    hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader, hpublic, hpublicBytes⟩
  rcases keys with ⟨encKey, macKey, ivKey⟩
  have hbeforeEq : before = real.triple.classical.dhs_pub := by
    simp [tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public] at hbefore
    exact hbefore.symm
  subst hbeforeEq
  have hne : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      tripleCandidate.classical.dhs_pub real.triple.classical.dhs_pub =
      ok (decide (tripleCandidate.classical.dhs_pub ≠ real.triple.classical.dhs_pub)) := by
    obtain ⟨b, hb, hiff⟩ := Std.WP.spec_imp_exists
      (Tacenta.SessionUnitT3.array_ne_val
        tripleCandidate.classical.dhs_pub real.triple.classical.dhs_pub)
    rw [hb]
    cases b <;> simp_all
  unfold lifecycle.Session.decrypt_ratchet
  cases hsparse with
  | none hout =>
      by_cases hsame : tripleCandidate.classical.dhs_pub = real.triple.classical.dhs_pub <;>
        (try rw [hsame] at hne ⊢) <;>
        simp [hne, hsame, hready, hdecode, hmsg, hreceive, hout, hpeer, hfirst, hwrapRecv,
          hderefRecv, hrandom, hcandidate, hsecond, hwrapSend, hderefSend,
          hheader, hpublic, hpublicBytes, htriple, hwrapMk, hderefMk, hkeys,
          hwrapKeys, hderefKeys, had, haead, tacenta_triple.State.sending_public,
          tacenta_ratchet.State.sending_public]
  | some realSparse converted hout hconverted =>
      by_cases hsame : tripleCandidate.classical.dhs_pub = real.triple.classical.dhs_pub <;>
        (try rw [hsame] at hne ⊢) <;>
        simp [hne, hsame, hready, hdecode, hmsg, hreceive, hout, hconverted, hpeer, hfirst,
          hwrapRecv, hderefRecv, hrandom, hcandidate, hsecond, hwrapSend,
          hderefSend, hheader, hpublic, hpublicBytes, htriple, hwrapMk, hderefMk, hkeys,
          hwrapKeys, hderefKeys, had, haead, tacenta_triple.State.sending_public,
          tacenta_ratchet.State.sending_public]


/-! ## The model-side receive bounds give the generated-side ones -/

theorem RetryRunBounds.toRetryReceiveBounds {state : Model.Triple.State}
    {modelHeader : Model.Triple.Header} {modelOutput : Option Model.SparseRatchet.Output}
    (b : RetryRunBounds state modelHeader modelOutput) (header : tacenta_triple.Header)
    (output : Option tacenta_spqr.Output)
    (hheader : Tacenta.SessionUnitTripleT3.TripleHeaderR header modelHeader)
    (hout : modelOutput = output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) :
    RetryReceiveBounds state header modelHeader.dr output := by
  have hcm := Tacenta.UnitLifecycleRetryLoopT3.cMax_le_usize_max
  have hc := cMax_usize
  have hcs := b.classicalStore
  have hps := b.sparseStore
  simp only [Model.State.maxSkippedStore, Model.SparseRatchet.maxSkippedStore] at hcs hps
  refine
    { classicalMatch := b.classicalMatch
      classicalStoreRoom := ?_
      classicalEvents := b.classicalEvents
      sparseEpoch := b.sparseEpoch
      sparseChainsRoom := b.sparseChainsRoom
      sparseChainEpochs := b.sparseChainEpochs
      sparseSkippedEpochs := b.sparseSkippedEpochs
      sparseOutputEpoch := ?_
      sparseStoreRoom := ?_
      sparseMatch := ?_
      sparseCounters := b.sparseCounters }
  · simp only [Model.State.maxSkippedStore, Model.State.maxSkip]
    omega
  · intro o ho
    have := b.sparseOutputEpoch (Tacenta.SessionUnitTripleT3.spqrOutputOf o) (by rw [hout, ho]; rfl)
    simpa [Tacenta.SessionUnitTripleT3.spqrOutputOf] using this
  · simp only [Model.SparseRatchet.maxSkip, Model.State.maxSkip]
    omega
  · rw [hheader.epoch, hheader.pq_n]
    exact b.sparseMatch

/-! ## The refinement -/

set_option maxHeartbeats 4000000 in
/-- **`decrypt_ratchet` refines `Model.Lifecycle.decryptRatchet`, with the eviction retry loop.**
For every input that meets the hypotheses of `DecryptRatchetRefinesStatement`, the generated
function returns, and either its result, the session it leaves and the remaining trace refine the
model's step, or the run is a Triple refusal whose reason is not a full skipped-key store
(`TripleRefusalOpen`), the one path this module leaves open.  Covered: the terminal guard, a decode
refusal, either DH refusal, a Triple refusal whose reason is a full store (after an empty
eviction), an AEAD refusal and a success, with or without eviction rounds.  A refusal returns the
given session; a success commits the Triple and Braid candidates and, when the sending key
changed, the drawn private key. -/
theorem decrypt_ratchet_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (hrel : SessionRefines dh oracle.braidKem real model)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (htrace : trace rng = oracle.draws)
    (run : DecryptRatchetRun view oracle trace real model message rng) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng = ok output ∧
      (StepRefines trace dh oracle.braidKem output
          (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) ∨
        TripleRefusalOpen output) := by
  -- The terminal guard.
  by_cases hterm : Model.Lifecycle.agreementFailed model = true
  · obtain ⟨h1, h2⟩ := decrypt_ratchet_terminal_guard_step_refines rngCore cryptoRng trace dh
      oracle.braidKem view oracle real model message rng hrel htrace hterm
    exact ⟨_, h1, Or.inl h2⟩
  have hready : Model.Lifecycle.agreementFailed model = false := by simpa using hterm
  have hrealReady := braid_failed_refines oracle.braidKem real.braid model.braid hrel.braid
  have hmodelReady : Model.Lifecycle.braidFailed model.braid = false := by
    cases hb : model.braid <;>
      simp [Model.Lifecycle.agreementFailed, Model.Lifecycle.braidFailed, hb] at hready ⊢
  rw [hmodelReady] at hrealReady
  -- Decoding.
  obtain ⟨decodedResult, hdecCall, hdecPost⟩ :=
    Std.WP.spec_imp_exists (decode_message_refines_lifecycle message)
  cases decodedResult with
  | Err e =>
      obtain ⟨h1, h2⟩ := decrypt_ratchet_decode_refusal_refines rngCore cryptoRng trace dh
        oracle.braidKem view oracle real model message rng e hrel htrace hready hdecCall
      exact ⟨_, h1, Or.inl h2⟩
  | Ok decoded =>
  obtain ⟨mc, hmodelDec, hcomp⟩ := hdecPost
  have hdetail : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (mc, vecOf decoded.ciphertext) :=
    (Model.CompositeHeader.decodeDetailed_ok_iff _ _).mpr hmodelDec
  -- The Braid receive.
  have hchunk := run.chunk decoded.header mc _ hdetail hcomp
  have hhonest := run.honest mc _ hdetail
  obtain ⟨msg, hmsgCall, hmsgRel⟩ := msg_of_refines view model.braid decoded.header mc hcomp hchunk
  obtain ⟨⟨ep, out, next⟩, hrecvCall, hrecvPost⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitBraidT3.Braid.receive_refines (K := oracle.braidKem)
      agreements.kem agreements.erasure agreements.hmac agreements.hkdf agreements.kemLen
      agreements.validateEk contracts.braid.encapsulate2 contracts.braid.decoderAdd
      contracts.braid.decoderMessage contracts.braid.ct1Len contracts.braid.ct2Len
      contracts.braid.headerLen agreements.kemClone
      Tacenta.UnitSatisfiabilityErasureAgrees.erasureCloneAgrees contracts.braid.encoderClone
      contracts.braid.decoderClone contracts.braid.keyPairClone contracts.braid.encapsStateClone
      contracts.braid.optionClone contracts.braid.zeroizingArray contracts.braid.arrayZeroize
      contracts.braid.rangeFullIndex real.braid msg
      (Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom.braid headroom) (Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom.braidDecoders headroom)
      run.braidEpoch hrel.braid hmsgRel hhonest)
  obtain ⟨-, houtRel, hnextRel⟩ := hrecvPost
  have hsparseEx : ∃ sparse, RealSparseConversion out sparse := by
    cases out with
    | none => exact ⟨none, .none rfl⟩
    | some o =>
        exact ⟨_, .some o { key_epoch := o.key_epoch, key := o.key } rfl
          (by simp [tacenta_spqr.Output.new])⟩
  obtain ⟨sparse, hsparse⟩ := hsparseEx
  have hsparseModel := sparse_output_of_conversion houtRel hsparse
  -- The first agreement.
  obtain ⟨peer, hpeerCall, hpeerVal⟩ := codec.fromBytes decoded.header.dh
  have hpeerModel : dh.publicKey peer = mc.dh := by rw [hpeerVal, hcomp.dh]
  obtain ⟨a1, ha1Call, ha1Val⟩ := oracleOf.dhAgree real.ratchet_private peer
  rw [hrel.ratchetPrivate, hpeerModel] at ha1Val
  cases a1 with
  | none =>
      have hmodelDh : oracle.dhAgree model.ratchetPrivate mc.dh = none := by
        simpa using ha1Val.symm
      refine ⟨(.Err (.Handshake SessionError.NonContributoryAgreement), real, rng), ?_,
        Or.inl ?_⟩
      · unfold lifecycle.Session.decrypt_ratchet
        cases hsparse with
        | none hout =>
            simp [hrealReady, hdecCall, hmsgCall, hrecvCall, hout, hpeerCall, ha1Call]
        | some realSparse converted hout hconverted =>
            simp [hrealReady, hdecCall, hmsgCall, hrecvCall, hout, hconverted, hpeerCall, ha1Call]
      · have hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
            { session := model, result := .error (.handshake .nonContributoryAgreement),
              oracle := oracle } := by
          simp [Model.Lifecycle.decryptRatchet, hready, hdetail, hmodelDh]
        rw [hmodel]
        exact ⟨rfl, hrel, htrace⟩
  | some recvSecret =>
  have hmodelFirst : oracle.dhAgree model.ratchetPrivate mc.dh = some (arrayOf recvSecret) := by
    simpa using ha1Val.symm
  obtain ⟨wrappedRecv, hwrapRecv, hderefRecv⟩ :=
    zeroizing_roundtrip agreements.zeroizing32 wrap32 recvSecret
  -- The draw.
  obtain ⟨d, rest, htr⟩ := run.draw
  have hdraws : oracle.draws = d :: rest := by rw [← htrace, htr]
  obtain ⟨candidateBytes, rng1, hrand, hcandVal, htr1⟩ := oracleOf.random32 rng d rest htr
  have hmodelDraw : Model.Lifecycle.random32 oracle =
      some (d, { oracle with draws := rest }) := by
    simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hdraws]
  obtain ⟨cpriv, hcpCall, hcpVal⟩ := codec.privateFromBytes candidateBytes
  have hcpDraw : dh.privateKey cpriv = d := by rw [hcpVal, hcandVal]
  -- The second agreement.
  obtain ⟨a2, ha2Call, ha2Val⟩ := oracleOf.dhAgree cpriv peer
  rw [hcpDraw, hpeerModel] at ha2Val
  cases a2 with
  | none =>
      have hmodelDh : oracle.dhAgree d mc.dh = none := by simpa using ha2Val.symm
      refine ⟨(.Err (.Handshake SessionError.NonContributoryAgreement), real, rng1), ?_,
        Or.inl ?_⟩
      · unfold lifecycle.Session.decrypt_ratchet
        cases hsparse with
        | none hout =>
            simp [hrealReady, hdecCall, hmsgCall, hrecvCall, hout, hpeerCall, ha1Call,
              hwrapRecv, hrand, hcpCall, ha2Call]
        | some realSparse converted hout hconverted =>
            simp [hrealReady, hdecCall, hmsgCall, hrecvCall, hout, hconverted, hpeerCall,
              ha1Call, hwrapRecv, hrand, hcpCall, ha2Call]
      · have hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
            { session := model, result := .error (.handshake .nonContributoryAgreement),
              oracle := { oracle with draws := rest } } := by
          simp [Model.Lifecycle.decryptRatchet, hready, hdetail, hmodelFirst, hmodelDraw,
            hmodelDh]
        rw [hmodel]
        exact ⟨rfl, hrel, htr1⟩
  | some sendSecret =>
  have hmodelSecond : oracle.dhAgree d mc.dh = some (arrayOf sendSecret) := by
    simpa using ha2Val.symm
  obtain ⟨wrappedSend, hwrapSend, hderefSend⟩ :=
    zeroizing_roundtrip agreements.zeroizing32 wrap32 sendSecret
  have hbefore : tacenta_triple.State.sending_public real.triple =
      ok real.triple.classical.dhs_pub := by
    simp [tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public]
  obtain ⟨header, hheaderCall, hheaderRel⟩ := triple_header_of_refines decoded.header mc hcomp
  obtain ⟨cpub, hcpubCall, hcpubVal⟩ := oracleOf.dhPublic cpriv
  obtain ⟨newPub, hnewPubCall, hnewPubVal⟩ := codec.asBytes cpub
  have hmodelPublic : oracle.dhPublic d = arrayOf newPub := by
    rw [hnewPubVal, hcpubVal, hcpDraw]
  let P : DecryptPrefix rngCore cryptoRng real message rng rng1 :=
    { decoded, msg, epoch := ep, out, next, sparse, peer, recvSecret, sendSecret, candidateBytes,
      newPublicBytes := newPub, before := real.triple.classical.dhs_pub, candidatePrivate := cpriv,
      candidatePublic := cpub, header, wrappedRecv, wrappedSend, hready := hrealReady,
      hdecode := hdecCall, hmsg := hmsgCall, hreceive := hrecvCall, hsparse, hpeer := hpeerCall,
      hfirst := ha1Call, hwrapRecv, hderefRecv, hrandom := hrand, hcandidate := hcpCall,
      hsecond := ha2Call, hwrapSend, hderefSend, hbefore, hheader := hheaderCall,
      hpublic := hcpubCall, hpublicBytes := hnewPubCall }
  -- The Triple receive with eviction.
  have hbounds := (run.retry mc _ hdetail).toRetryReceiveBounds header sparse hheaderRel
    hsparseModel
  have hstores := run.retry mc _ hdetail
  obtain ⟨tripleOut, htripleCall, htripleRel⟩ :=
    Tacenta.UnitLifecycleRetryLoopT3.receive_with_eviction_refines contracts.triple
      agreements.hmac agreements.hkdf agreements.zeroizing64 agreements.zeroizing96
      agreements.zeroizingSparse64 agreements.vecRetain agreements.removeSkipped decoded.header mc
      hcomp header (Model.Lifecycle.tripleHeaderOf mc).dr hheaderRel.dr recvSecret sendSecret newPub
      sparse real.triple model.triple hrel.triple
      (Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom.triple headroom) hbounds hstores.classicalStore
      hstores.sparseStore
  have hheaderEq : Model.Triple.Header.mk (Model.Lifecycle.tripleHeaderOf mc).dr header.epoch.val
      header.pq_n.val = Model.Lifecycle.tripleHeaderOf mc := by
    rw [hheaderRel.epoch, hheaderRel.pq_n]
  have hmodelRWE : Model.Lifecycle.receiveWithEviction model.triple mc
      (Model.Lifecycle.tripleHeaderOf mc) (arrayOf recvSecret) (arrayOf sendSecret)
      (oracle.dhPublic d)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid mc)).2.1) =
      Model.Lifecycle.receiveWithEviction model.triple mc
        (Model.Triple.Header.mk (Model.Lifecycle.tripleHeaderOf mc).dr header.epoch.val
          header.pq_n.val)
        (Tacenta.SessionUnitTripleT3.keyOf recvSecret)
        (Tacenta.SessionUnitTripleT3.keyOf sendSecret)
        (Tacenta.SessionUnitTripleT3.keyOf newPub)
        (sparse.map Tacenta.SessionUnitTripleT3.spqrOutputOf) := by
    rw [hheaderEq, hmodelPublic, hsparseModel]
    rfl
  rw [← hmodelRWE] at htripleRel
  rcases htripleRel with hrefines | hopen
  · cases tripleOut with
    | Err e =>
        cases hm : Model.Lifecycle.receiveWithEviction model.triple mc
            (Model.Lifecycle.tripleHeaderOf mc) (arrayOf recvSecret) (arrayOf sendSecret)
            (oracle.dhPublic d)
            (Model.Lifecycle.sparseOutputOf
              (Model.Braid.receive oracle.braidKem model.braid
                (Model.Lifecycle.braidMessageOf view model.braid mc)).2.1) with
        | ok v => rw [hm] at hrefines; exact absurd hrefines (by simp [Tacenta.UnitLifecycleRetryLoopT3.OutcomeRefines])
        | error r =>
            rw [hm] at hrefines
            have hmap : tripleReceiveRefusalOfReal e = some r := hrefines
            refine ⟨_, P.triple_refusal e htripleCall, Or.inl ?_⟩
            have hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
                { session := model, result := .error (Model.Lifecycle.tripleReceiveRefusalOf r),
                  oracle := { oracle with draws := rest } } := by
              simp [Model.Lifecycle.decryptRatchet, hready, hdetail, hmodelFirst, hmodelDraw,
                hmodelSecond, hm]
            rw [hmodel]
            exact ⟨tripleReceiveRefusalOfReal_sound hmap, hrel, htr1⟩
    | Ok value =>
        obtain ⟨tripleCandidate, mk⟩ := value
        cases hm : Model.Lifecycle.receiveWithEviction model.triple mc
            (Model.Lifecycle.tripleHeaderOf mc) (arrayOf recvSecret) (arrayOf sendSecret)
            (oracle.dhPublic d)
            (Model.Lifecycle.sparseOutputOf
              (Model.Braid.receive oracle.braidKem model.braid
                (Model.Lifecycle.braidMessageOf view model.braid mc)).2.1) with
        | error r => rw [hm] at hrefines; exact absurd hrefines (by simp [Tacenta.UnitLifecycleRetryLoopT3.OutcomeRefines])
        | ok v =>
        obtain ⟨modelCandidate, modelMk⟩ := v
        rw [hm] at hrefines
        obtain ⟨hcandRel, hmkRel⟩ := hrefines
        obtain ⟨wrappedMk, hwrapMk, hderefMk⟩ :=
          zeroizing_roundtrip agreements.zeroizing32 wrap32 mk
        obtain ⟨keys, hkeysCall, hkeysVal⟩ := Std.WP.spec_imp_exists
          (Tacenta.SessionUnitT3.message_keys_refines agreements.hkdf agreements.zeroizing80 mk
            tacenta_ratchet.LabelSet.Tacenta)
        obtain ⟨wrappedKeys, hwrapKeys, hderefKeys⟩ := contracts.messageKeyMaterial keys
        obtain ⟨ad, hadCall, hadVal⟩ := Std.WP.spec_imp_exists
          (concat_ad_refines (alloc.vec.Vec.deref real.identity_ad) decoded.header mc hcomp
            (Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom.associatedData headroom))
        have hadModel : vecOf ad = Model.Messages.concatAd model.identityAd
            (Model.CompositeHeader.encode mc) := by
          rw [hadVal, ← hrel.identityAd]
          rfl
        have hkeysModel : (arrayOf keys.1, arrayOf keys.2.1, arrayOf keys.2.2) =
            Model.State.messageKeys modelMk .tacenta := by
          have hmk : Tacenta.SessionUnitTripleT3.keyOf mk = modelMk := hmkRel
          have h := hkeysVal
          simp only [Tacenta.SessionUnitT3.labelsOf] at h
          rw [← hmk]
          exact h
        obtain ⟨aeadResult, haeadCall, haeadVal⟩ :=
          oracleOf.aeadOpen keys.1 keys.2.1 keys.2.2 (alloc.vec.Vec.deref decoded.ciphertext)
            (alloc.vec.Vec.deref ad)
        have hk1 : arrayOf keys.1 = (Model.State.messageKeys modelMk .tacenta).1 :=
          congrArg Prod.fst hkeysModel
        have hk2 : arrayOf keys.2.1 = (Model.State.messageKeys modelMk .tacenta).2.1 :=
          congrArg (fun k => k.2.1) hkeysModel
        have hk3 : arrayOf keys.2.2 = (Model.State.messageKeys modelMk .tacenta).2.2 :=
          congrArg (fun k => k.2.2) hkeysModel
        have hcipher : sliceOf (alloc.vec.Vec.deref decoded.ciphertext) =
            vecOf decoded.ciphertext := rfl
        have had : sliceOf (alloc.vec.Vec.deref ad) = Model.Messages.concatAd model.identityAd
            (Model.CompositeHeader.encode mc) := hadModel
        rw [hk1, hk2, hk3, hcipher, had] at haeadVal
        cases aeadResult with
        | Err err =>
            have hmodelAead : oracle.aeadOpen (Model.State.messageKeys modelMk .tacenta).1
                (Model.State.messageKeys modelMk .tacenta).2.1
                (Model.State.messageKeys modelMk .tacenta).2.2 (vecOf decoded.ciphertext)
                (Model.Messages.concatAd model.identityAd (Model.CompositeHeader.encode mc)) =
                none := by
              simpa [resultOptionOf] using haeadVal.symm
            refine ⟨_, P.aead_refusal tripleCandidate mk wrappedMk keys wrappedKeys ad err
              htripleCall hwrapMk hderefMk hkeysCall hwrapKeys hderefKeys hadCall haeadCall,
              Or.inl ?_⟩
            have hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
                { session := model, result := .error .aead,
                  oracle := { oracle with draws := rest } } := by
              simp [Model.Lifecycle.decryptRatchet, hready, hdetail, hmodelFirst, hmodelDraw,
                hmodelSecond, hm, hmodelAead]
            rw [hmodel]
            exact ⟨rfl, hrel, htr1⟩
        | Ok plaintext =>
            have hmodelAead : oracle.aeadOpen (Model.State.messageKeys modelMk .tacenta).1
                (Model.State.messageKeys modelMk .tacenta).2.1
                (Model.State.messageKeys modelMk .tacenta).2.2 (vecOf decoded.ciphertext)
                (Model.Messages.concatAd model.identityAd (Model.CompositeHeader.encode mc)) =
                some (vecOf plaintext) := by
              simpa [resultOptionOf] using haeadVal.symm
            have hreal := P.success tripleCandidate mk wrappedMk keys wrappedKeys ad plaintext
              htripleCall hwrapMk hderefMk hkeysCall hwrapKeys hderefKeys hadCall haeadCall
            have hmodel := decrypt_ratchet_success_model_result view oracle
              { oracle with draws := rest } model message mc (vecOf decoded.ciphertext)
              (vecOf plaintext) (arrayOf recvSecret) d (arrayOf sendSecret) modelCandidate modelMk
              hready hdetail hmodelFirst hmodelDraw hmodelSecond hm hmodelAead
            exact ⟨_, hreal, Or.inl (decrypt_ratchet_success_step_from_results rngCore cryptoRng
              trace dh oracle.braidKem view oracle { oracle with draws := rest } real model message
              rng rng1 plaintext (vecOf plaintext) tripleCandidate next cpriv d modelCandidate
              (Model.Braid.receive oracle.braidKem model.braid
                (Model.Lifecycle.braidMessageOf view model.braid mc)).2.2
              hrel hreal hmodel hcandRel hnextRel hcpDraw rfl htr1)⟩
  · obtain ⟨e, -, -, hout, hfull, -⟩ := hopen
    subst hout
    exact ⟨_, P.triple_refusal e htripleCall, Or.inr ⟨e, rfl, hfull⟩⟩

/-- The theorem has exactly the statement recorded in `DecryptRatchetRefinesStatement`. -/
theorem decrypt_ratchet_refines_statement : DecryptRatchetRefinesStatement := by
  intro R rngCore cryptoRng trace dh view oracle oracleOf codec contracts inst agreements real
    model message rng hrel headroom htrace run
  exact decrypt_ratchet_refines rngCore cryptoRng trace dh view oracle oracleOf codec contracts
    agreements real model message rng hrel headroom htrace run

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

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetT3.decrypt_ratchet_refines' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetT3.decrypt_ratchet_refines

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetT3.decrypt_ratchet_refines_statement' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetT3.decrypt_ratchet_refines_statement

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.toRetryReceiveBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.toRetryReceiveBounds

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.triple_refusal' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.triple_refusal

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.aead_refusal' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.aead_refusal

/--
info: 'Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.success' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.success

/--
info: @Tacenta.UnitLifecycleDecryptRatchetT3.decrypt_ratchet_refines : ∀ {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
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
#check @Tacenta.UnitLifecycleDecryptRatchetT3.decrypt_ratchet_refines

/--
info: @Tacenta.UnitLifecycleDecryptRatchetT3.decrypt_ratchet_refines_statement : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRefinesStatement
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetT3.decrypt_ratchet_refines_statement

/--
info: @Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.toRetryReceiveBounds : ∀ {state : Model.Triple.State}
  {modelHeader : Model.Triple.Header} {modelOutput : Option Model.SparseRatchet.Output},
  Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds state modelHeader modelOutput →
    ∀ (header : tacenta_session_unit.tacenta_triple.Header) (output : Option tacenta_session_unit.tacenta_spqr.Output),
      Tacenta.SessionUnitTripleT3.TripleHeaderR header modelHeader →
        modelOutput = Option.map Tacenta.SessionUnitTripleT3.spqrOutputOf output →
          Tacenta.UnitLifecycleT3.RetryReceiveBounds state header modelHeader.dr output
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds.toRetryReceiveBounds

/--
info: @Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.triple_refusal : ∀ {R : Type}
  {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
  {real : tacenta_session_unit.lifecycle.Session} {message : Aeneas.Std.Slice Aeneas.Std.U8} {rng rngNext : R}
  (P : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix rngCore cryptoRng real message rng rngNext)
  (reason : tacenta_session_unit.tacenta_triple.TripleError),
  tacenta_session_unit.lifecycle.receive_with_eviction real.triple P.decoded.header P.header P.recvSecret P.sendSecret
        P.newPublicBytes P.sparse =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err reason) →
    tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      Aeneas.Std.Result.ok
        (Aeneas.Std.core.result.Result.Err (tacenta_session_unit.lifecycle.Error.Triple reason), real, rngNext)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.triple_refusal

/--
info: @Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.aead_refusal : ∀ {R : Type}
  {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
  {real : tacenta_session_unit.lifecycle.Session} {message : Aeneas.Std.Slice Aeneas.Std.U8} {rng rngNext : R}
  (P : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix rngCore cryptoRng real message rng rngNext)
  (tripleCandidate : tacenta_session_unit.tacenta_triple.State) (mk : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  (wrappedMk : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize))
  (keys : Tacenta.UnitLifecycleT1.MessageKeyMaterial)
  (wrappedKeys : tacenta_session_unit.zeroize.Zeroizing Tacenta.UnitLifecycleT1.MessageKeyMaterial)
  (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8) (aeadError : Unit),
  tacenta_session_unit.lifecycle.receive_with_eviction real.triple P.decoded.header P.header P.recvSecret P.sendSecret
        P.newPublicBytes P.sparse =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (tripleCandidate, mk)) →
    tacenta_session_unit.zeroize.Zeroizing.new Tacenta.UnitLifecycleDecryptRatchetT3.wrap32 mk =
        Aeneas.Std.Result.ok wrappedMk →
      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleDecryptRatchetT3.wrap32
            wrappedMk =
          Aeneas.Std.Result.ok mk →
        tacenta_session_unit.tacenta_ratchet.message_keys mk tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
            Aeneas.Std.Result.ok keys →
          tacenta_session_unit.zeroize.Zeroizing.new Tacenta.UnitLifecycleT1.messageKeyMaterialZeroize keys =
              Aeneas.Std.Result.ok wrappedKeys →
            tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                  Tacenta.UnitLifecycleT1.messageKeyMaterialZeroize wrappedKeys =
                Aeneas.Std.Result.ok keys →
              tacenta_session_unit.serialization.concat_ad real.identity_ad.deref P.decoded.header =
                  Aeneas.Std.Result.ok ad →
                tacenta_session_unit.tacenta_boundary.aead.decrypt keys.1 keys.2.1 keys.2.2 P.decoded.ciphertext.deref
                      ad.deref =
                    Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err aeadError) →
                  tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
                    Aeneas.Std.Result.ok
                      (Aeneas.Std.core.result.Result.Err tacenta_session_unit.lifecycle.Error.Aead, real, rngNext)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.aead_refusal

/--
info: @Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.success : ∀ {R : Type}
  {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
  {real : tacenta_session_unit.lifecycle.Session} {message : Aeneas.Std.Slice Aeneas.Std.U8} {rng rngNext : R}
  (P : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix rngCore cryptoRng real message rng rngNext)
  (tripleCandidate : tacenta_session_unit.tacenta_triple.State) (mk : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  (wrappedMk : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize))
  (keys : Tacenta.UnitLifecycleT1.MessageKeyMaterial)
  (wrappedKeys : tacenta_session_unit.zeroize.Zeroizing Tacenta.UnitLifecycleT1.MessageKeyMaterial)
  (ad plaintext : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
  tacenta_session_unit.lifecycle.receive_with_eviction real.triple P.decoded.header P.header P.recvSecret P.sendSecret
        P.newPublicBytes P.sparse =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (tripleCandidate, mk)) →
    tacenta_session_unit.zeroize.Zeroizing.new Tacenta.UnitLifecycleDecryptRatchetT3.wrap32 mk =
        Aeneas.Std.Result.ok wrappedMk →
      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleDecryptRatchetT3.wrap32
            wrappedMk =
          Aeneas.Std.Result.ok mk →
        tacenta_session_unit.tacenta_ratchet.message_keys mk tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
            Aeneas.Std.Result.ok keys →
          tacenta_session_unit.zeroize.Zeroizing.new Tacenta.UnitLifecycleT1.messageKeyMaterialZeroize keys =
              Aeneas.Std.Result.ok wrappedKeys →
            tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                  Tacenta.UnitLifecycleT1.messageKeyMaterialZeroize wrappedKeys =
                Aeneas.Std.Result.ok keys →
              tacenta_session_unit.serialization.concat_ad real.identity_ad.deref P.decoded.header =
                  Aeneas.Std.Result.ok ad →
                tacenta_session_unit.tacenta_boundary.aead.decrypt keys.1 keys.2.1 keys.2.2 P.decoded.ciphertext.deref
                      ad.deref =
                    Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok plaintext) →
                  tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
                    Aeneas.Std.Result.ok
                      (Aeneas.Std.core.result.Result.Ok plaintext,
                        have __src :=
                          { triple := tripleCandidate, braid := P.next, ratchet_private := real.ratchet_private,
                            identity_ad := real.identity_ad, our_identity_public := real.our_identity_public,
                            peer_identity_public := real.peer_identity_public, pending_initial := real.pending_initial,
                            established_ephemeral := real.established_ephemeral };
                        { triple := __src.triple, braid := __src.braid,
                          ratchet_private :=
                            if (tripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub) = true then
                              real.ratchet_private
                            else P.candidatePrivate,
                          identity_ad := __src.identity_ad, our_identity_public := __src.our_identity_public,
                          peer_identity_public := __src.peer_identity_public, pending_initial := __src.pending_initial,
                          established_ephemeral := __src.established_ephemeral },
                        rngNext)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.success

/--
info: structure Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (real : tacenta_session_unit.lifecycle.Session) (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng rngNext : R) : Type
number of parameters: 7
fields:
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.decoded : tacenta_session_unit.tacenta_wire.DecodedMessage
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.msg : tacenta_session_unit.tacenta_braid.Msg
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.epoch : Aeneas.Std.U64
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.out : Option tacenta_session_unit.tacenta_braid.Output
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.next : tacenta_session_unit.tacenta_braid.Braid
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.sparse : Option tacenta_session_unit.tacenta_spqr.Output
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.peer : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.recvSecret : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.sendSecret : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.candidateBytes : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.newPublicBytes : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.before : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.candidatePrivate : tacenta_session_unit.tacenta_boundary.dh.PrivateKey
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.candidatePublic : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.header : tacenta_session_unit.tacenta_triple.Header
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.wrappedRecv : tacenta_session_unit.zeroize.Zeroizing
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.wrappedSend : tacenta_session_unit.zeroize.Zeroizing
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hready : real.braid.failed = Aeneas.Std.Result.ok false
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hdecode : tacenta_session_unit.tacenta_wire.decode_message
        message =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok self.decoded)
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hmsg : tacenta_session_unit.lifecycle.msg_of self.decoded.header =
      Aeneas.Std.Result.ok self.msg
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hreceive : real.braid.receive self.msg =
      Aeneas.Std.Result.ok (self.epoch, self.out, self.next)
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hsparse : Tacenta.UnitLifecycleT3.RealSparseConversion self.out
      self.sparse
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hpeer : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes
        self.decoded.header.dh =
      Aeneas.Std.Result.ok self.peer
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hfirst : real.ratchet_private.agree self.peer =
      Aeneas.Std.Result.ok (some self.recvSecret)
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hwrapRecv : tacenta_session_unit.zeroize.Zeroizing.new
        (tacenta_session_unit.Array.Insts.ZeroizeZeroize 32#usize
          (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U8.Insts.ZeroizeDefaultIsZeroes))
        self.recvSecret =
      Aeneas.Std.Result.ok self.wrappedRecv
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hderefRecv : tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (tacenta_session_unit.Array.Insts.ZeroizeZeroize 32#usize
          (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U8.Insts.ZeroizeDefaultIsZeroes))
        self.wrappedRecv =
      Aeneas.Std.Result.ok self.recvSecret
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hrandom : tacenta_session_unit.lifecycle.random_secret rngCore
        cryptoRng rng =
      Aeneas.Std.Result.ok (self.candidateBytes, rngNext)
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hcandidate : tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes
        self.candidateBytes =
      Aeneas.Std.Result.ok self.candidatePrivate
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hsecond : self.candidatePrivate.agree self.peer =
      Aeneas.Std.Result.ok (some self.sendSecret)
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hwrapSend : tacenta_session_unit.zeroize.Zeroizing.new
        (tacenta_session_unit.Array.Insts.ZeroizeZeroize 32#usize
          (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U8.Insts.ZeroizeDefaultIsZeroes))
        self.sendSecret =
      Aeneas.Std.Result.ok self.wrappedSend
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hderefSend : tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (tacenta_session_unit.Array.Insts.ZeroizeZeroize 32#usize
          (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U8.Insts.ZeroizeDefaultIsZeroes))
        self.wrappedSend =
      Aeneas.Std.Result.ok self.sendSecret
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hbefore : real.triple.sending_public =
      Aeneas.Std.Result.ok self.before
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hheader : tacenta_session_unit.lifecycle.triple_header_of
        self.decoded.header =
      Aeneas.Std.Result.ok self.header
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hpublic : self.candidatePrivate.public_key =
      Aeneas.Std.Result.ok self.candidatePublic
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.hpublicBytes : self.candidatePublic.as_bytes =
      Aeneas.Std.Result.ok self.newPublicBytes
constructor:
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix.mk {R : Type}
    {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
    {real : tacenta_session_unit.lifecycle.Session} {message : Aeneas.Std.Slice Aeneas.Std.U8} {rng rngNext : R}
    (decoded : tacenta_session_unit.tacenta_wire.DecodedMessage) (msg : tacenta_session_unit.tacenta_braid.Msg)
    (epoch : Aeneas.Std.U64) (out : Option tacenta_session_unit.tacenta_braid.Output)
    (next : tacenta_session_unit.tacenta_braid.Braid) (sparse : Option tacenta_session_unit.tacenta_spqr.Output)
    (peer : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes)
    (recvSecret sendSecret candidateBytes newPublicBytes before : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
    (candidatePrivate : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
    (candidatePublic : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes)
    (header : tacenta_session_unit.tacenta_triple.Header)
    (wrappedRecv wrappedSend : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize))
    (hready : real.braid.failed = Aeneas.Std.Result.ok false)
    (hdecode :
      tacenta_session_unit.tacenta_wire.decode_message message =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok decoded))
    (hmsg : tacenta_session_unit.lifecycle.msg_of decoded.header = Aeneas.Std.Result.ok msg)
    (hreceive : real.braid.receive msg = Aeneas.Std.Result.ok (epoch, out, next))
    (hsparse : Tacenta.UnitLifecycleT3.RealSparseConversion out sparse)
    (hpeer :
      tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = Aeneas.Std.Result.ok peer)
    (hfirst : real.ratchet_private.agree peer = Aeneas.Std.Result.ok (some recvSecret))
    (hwrapRecv :
      tacenta_session_unit.zeroize.Zeroizing.new
          (tacenta_session_unit.Array.Insts.ZeroizeZeroize 32#usize
            (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U8.Insts.ZeroizeDefaultIsZeroes))
          recvSecret =
        Aeneas.Std.Result.ok wrappedRecv)
    (hderefRecv :
      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
          (tacenta_session_unit.Array.Insts.ZeroizeZeroize 32#usize
            (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U8.Insts.ZeroizeDefaultIsZeroes))
          wrappedRecv =
        Aeneas.Std.Result.ok recvSecret)
    (hrandom :
      tacenta_session_unit.lifecycle.random_secret rngCore cryptoRng rng =
        Aeneas.Std.Result.ok (candidateBytes, rngNext))
    (hcandidate :
      tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes =
        Aeneas.Std.Result.ok candidatePrivate)
    (hsecond : candidatePrivate.agree peer = Aeneas.Std.Result.ok (some sendSecret))
    (hwrapSend :
      tacenta_session_unit.zeroize.Zeroizing.new
          (tacenta_session_unit.Array.Insts.ZeroizeZeroize 32#usize
            (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U8.Insts.ZeroizeDefaultIsZeroes))
          sendSecret =
        Aeneas.Std.Result.ok wrappedSend)
    (hderefSend :
      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
          (tacenta_session_unit.Array.Insts.ZeroizeZeroize 32#usize
            (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U8.Insts.ZeroizeDefaultIsZeroes))
          wrappedSend =
        Aeneas.Std.Result.ok sendSecret)
    (hbefore : real.triple.sending_public = Aeneas.Std.Result.ok before)
    (hheader : tacenta_session_unit.lifecycle.triple_header_of decoded.header = Aeneas.Std.Result.ok header)
    (hpublic : candidatePrivate.public_key = Aeneas.Std.Result.ok candidatePublic)
    (hpublicBytes : candidatePublic.as_bytes = Aeneas.Std.Result.ok newPublicBytes) :
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix rngCore cryptoRng real message rng rngNext
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptRatchetT3.DecryptPrefix
