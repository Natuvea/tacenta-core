import Translation.UnitLifecycleT3
import Translation.UnitLifecyclePublicT1

/-!
# Initial-message dispatcher composition

The selector derives the four wrapper guards, constructs the corresponding
route, and splits the actual inner receive result. Its only remaining semantic
premise is refinement of the inner ratchet receive on a matching initial frame.
This is a conditional composition theorem, not the full session T3 theorem.
The T1 bridge below derives existence of the inner result from the existing
boundary contracts and headroom theorem. No public-decrypt witness or route
is accepted as an input.
-/

namespace Tacenta.UnitLifecycleT3
open Aeneas Aeneas.Std Result
open tacenta_session_unit

/-! ## Braid receive adapter

This adapter is the first concrete part of the nonterminal aggregate. It
discharges the translated `msg_of` and `Braid.receive` calls from the existing
Braid T3 theorem and the lifecycle's boundary contracts. The Triple, DH and
AEAD branches remain separate obligations below; this record deliberately
does not assert that a receive succeeded or that it contributed an agreement.
-/

structure BraidReceiveEvidence
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (realComposite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite) : Type where
  message : tacenta_braid.Msg
  receivedEpoch : Std.U64
  output : Option tacenta_braid.Output
  next : tacenta_braid.Braid
  sparseOutput : Option tacenta_spqr.Output
  hmessageCall : lifecycle.msg_of realComposite = ok message
  hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines message
    (Model.Lifecycle.braidMessageOf view model.braid modelComposite)
  hreceive : tacenta_braid.Braid.receive real.braid message =
    ok (receivedEpoch, output, next)
  hsparse : RealSparseConversion output sparseOutput
  hnext : Tacenta.SessionUnitBraidT3.StateRefines K next.state
    (Model.Braid.receive K model.braid
      (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2

theorem braid_receive_evidence
    {K : Model.Braid.Kem}
    (view : Model.Lifecycle.CodewordView)
    (contracts : Tacenta.UnitLifecycleT1.BraidReceiveContracts)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (realComposite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (hka : Tacenta.SessionUnitBraidT3.KemAgreesFor K)
    (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees)
    (hmac : Tacenta.SessionUnitBraidT3.BraidHmacAgrees)
    (hkdf : Tacenta.SessionUnitBraidT3.BraidHkdfAgrees)
    (hlens : Tacenta.SessionUnitBraidT3.KemLenAgrees K)
    (hvalek : Tacenta.SessionUnitBraidT3.ValidateEkAgrees K)
    (hct1len : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2len : Tacenta.SessionUnitBraidT1.Ct2LenTotal)
    (hheaderlen : Tacenta.SessionUnitBraidT1.HeaderLenTotal)
    (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees)
    (hecl : Tacenta.SessionUnitBraidT3.ErasureCloneAgrees)
    (hrel : SessionRefines dh K real model)
    (hcomposite : CompositeRefines realComposite modelComposite)
    (hchunk : IncomingChunkRefines view model.braid realComposite modelComposite)
    (hhonest : Tacenta.SessionUnitBraidT3.HonestChunk model.braid
      (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hepoch : (Tacenta.SessionUnitBraidT1.State.epoch_val real.braid.state).val + 1
      < Std.U64.max) :
    Nonempty (BraidReceiveEvidence K view real model realComposite modelComposite) := by
  obtain ⟨message, hmessageCall, hmessageRel⟩ :=
    msg_of_refines view model.braid realComposite modelComposite hcomposite hchunk
  obtain ⟨result, hreceiveCall, hreceivePost⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitBraidT3.Braid.receive_refines
      (K := K)
      hka hea hmac hkdf hlens hvalek contracts.encapsulate2
      contracts.decoderAdd contracts.decoderMessage hct1len hct2len hheaderlen
      hkcl hecl contracts.encoderClone contracts.decoderClone contracts.keyPairClone
      contracts.encapsStateClone contracts.optionClone contracts.zeroizingArray
      contracts.arrayZeroize contracts.rangeFullIndex
      real.braid message
        (Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom.braid headroom)
        hepoch hrel.braid
      hmessageRel hhonest)
  rcases result with ⟨receivedEpoch, output, next⟩
  have hreceive : tacenta_braid.Braid.receive real.braid message =
      ok (receivedEpoch, output, next) := hreceiveCall
  have hpost := hreceivePost
  have hnext : Tacenta.SessionUnitBraidT3.StateRefines K next.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2 := hpost.2.2
  cases output with
  | none =>
      exact ⟨⟨message, receivedEpoch, none, next, none, hmessageCall, hmessageRel,
        hreceive, .none rfl, hnext⟩⟩
  | some output =>
      let converted : tacenta_spqr.Output :=
        { key_epoch := output.key_epoch, key := output.key }
      have hconverted : tacenta_spqr.Output.new output.key_epoch output.key = ok converted := by
        simp [converted, tacenta_spqr.Output.new]
      exact ⟨⟨message, receivedEpoch, some output, next, some converted,
        hmessageCall, hmessageRel, hreceive,
        .some output converted rfl hconverted, hnext⟩⟩

/-! The first nonterminal branch can now consume the Braid adapter directly.
The only remaining branch-specific fact is the model's first DH result; the
adapter has discharged message construction, Braid receive, and sparse-output
conversion from the shared contracts above. -/

theorem decrypt_ratchet_first_dh_refusal_from_braid
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (codec : DhCodecOf dh)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (decoded : tacenta_wire.DecodedMessage)
    (modelComposite : Model.CompositeHeader.Composite)
    (realComposite : tacenta_wire.Composite)
    (evidence : BraidReceiveEvidence K view real model realComposite modelComposite)
    (hrealComposite : realComposite = decoded.header)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Ok decoded))
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf decoded.ciphertext))
    (hcomposite : CompositeRefines decoded.header modelComposite)
    (hmodelDhNone : oracle.dhAgree model.ratchetPrivate modelComposite.dh = none) :
    lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
        ok (.Err (.Handshake SessionError.NonContributoryAgreement), real, rng) ∧
      StepRefines trace dh K
        (.Err (.Handshake SessionError.NonContributoryAgreement), real, rng)
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  subst realComposite
  exact decrypt_ratchet_first_dh_refusal_step_refines rngCore cryptoRng trace dh kem K view
    oracle oracleOf codec real model message rng decoded modelComposite evidence.message
    evidence.receivedEpoch evidence.output evidence.next evidence.sparseOutput hrel htrace
    hready hdecodeReal hdecodeModel hcomposite evidence.hmessageCall evidence.hmessageRel
    evidence.hreceive evidence.hsparse hmodelDhNone

theorem decrypt_ratchet_second_dh_refusal_from_braid
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
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
    (realComposite : tacenta_wire.Composite)
    (evidence : BraidReceiveEvidence K view real model realComposite modelComposite)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Ok decoded))
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf decoded.ciphertext))
    (hrealComposite : realComposite = decoded.header)
    (hcomposite : CompositeRefines decoded.header modelComposite)
    (draw modelDhOutRecv : Model.Lifecycle.Key)
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
  subst realComposite
  exact decrypt_ratchet_second_dh_refusal_step_refines rngCore cryptoRng trace dh kem K view
    oracle oracleNext oracleOf codec hz32 real model message rng decoded modelComposite
    evidence.message evidence.receivedEpoch evidence.output evidence.next evidence.sparseOutput
    draw modelDhOutRecv hrel htrace hready hdecodeReal hdecodeModel hcomposite
    evidence.hmessageCall evidence.hmessageRel evidence.hreceive evidence.hsparse
    hmodelFirst hmodelDraw hmodelSecond

/-! The Triple branch consumes the same Braid evidence as the two DH
refusal adapters.  Keeping this splice explicit prevents the caller from
silently replacing the translated `msg_of`/`Braid.receive` result with an
unrelated model candidate; the remaining arguments are the complete Triple
boundary call and model refusal facts required by the leaf theorem. -/

theorem decrypt_ratchet_triple_refusal_from_braid
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (decoded : tacenta_wire.DecodedMessage)
    (modelComposite : Model.CompositeHeader.Composite)
    (realComposite : tacenta_wire.Composite)
    (evidence : BraidReceiveEvidence K view real model realComposite modelComposite)
    (hrealComposite : realComposite = decoded.header)
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
    (hcomposite : CompositeRefines decoded.header modelComposite)
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
      recvSecret sendSecret newPublicBytes evidence.sparseOutput = ok (.Err realReason))
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
  subst realComposite
  obtain ⟨derivedHeader, hderivedCall, _⟩ :=
    triple_header_of_refines decoded.header modelComposite hcomposite
  have hheaderEq : derivedHeader = realHeader := by
    injection (hderivedCall.symm.trans hheaderCall)
  cases hheaderEq
  exact decrypt_ratchet_triple_refusal_step_refines rngCore cryptoRng trace dh K view
    oracle oracleNext real model message rng rngNext decoded modelComposite
    evidence.message evidence.receivedEpoch evidence.output evidence.next evidence.sparseOutput
    peer recvSecret sendSecret candidateBytes newPublicBytes before candidatePrivate candidatePublic
    realHeader wrappedRecv wrappedSend realReason modelReason draw modelDhOutRecv modelDhOutSend
    hrel htraceNext hready hdecodeReal hdecodeModel evidence.hmessageCall evidence.hreceive
    evidence.hsparse hpeerCall hfirstCall hwrapRecv hderefRecv hrandomCall hcandidateCall
    hsecondCall hwrapSend hderefSend hbeforeCall hheaderCall hpublicCall hpublicBytesCall
    htripleReal hmodelFirst hmodelDraw hmodelSecond hmodelPublic hmodelTriple hreason


/-! The AEAD refusal adapter keeps its Triple and Braid values independent
so the `RealSparseConversion` split remains eliminable. Explicit equalities
tie those values back to the shared Braid evidence before the translated
receive body is simplified. -/

theorem decrypt_ratchet_aead_refusal_from_braid {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (decoded : tacenta_wire.DecodedMessage)
    (modelComposite : Model.CompositeHeader.Composite)
    (realComposite : tacenta_wire.Composite)
    (evidence : BraidReceiveEvidence K view real model realComposite modelComposite)
    (hrealComposite : realComposite = decoded.header)
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
    (hmessageEq : realBraidMessage = evidence.message)
    (hreceivedEpochEq : receivedEpoch = evidence.receivedEpoch)
    (houtputEq : realOutput = evidence.output)
    (hcandidateEq : realBraidCandidate = evidence.next)
    (hsparseEq : realSparseOutput = evidence.sparseOutput)
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
  subst realComposite
  have hmessageCall : lifecycle.msg_of decoded.header = ok realBraidMessage := by
    rw [hmessageEq]
    exact evidence.hmessageCall
  have hreceive : tacenta_braid.Braid.receive real.braid realBraidMessage =
      ok (receivedEpoch, realOutput, realBraidCandidate) := by
    rw [hmessageEq, hreceivedEpochEq, houtputEq, hcandidateEq]
    exact evidence.hreceive
  have hsparse : RealSparseConversion realOutput realSparseOutput := by
    rw [houtputEq, hsparseEq]
    exact evidence.hsparse
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


/-! A successful concrete ratchet result determines the generated prefix that
the success adapter must consume.  This inversion is deliberately over the
translated computation itself: it cannot be satisfied by supplying an
unrelated decoded frame or Braid candidate, and it records the sparse-output
conversion in the same form used by `BraidReceiveEvidence`. -/

theorem decrypt_ratchet_success_braid_prefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext, next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m =
        ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput := by
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases hd : tacenta_wire.decode_message message with
    | fail err => simp [hf, hd] at hcall; cases b <;> simp_all
    | div => simp [hf, hd] at hcall; cases b <;> simp_all
    | ok r =>
      cases r with
      | Err err => simp [hf, hd] at hcall; cases b <;> simp_all
      | Ok decoded =>
        cases hm : lifecycle.msg_of decoded.header with
        | fail err => simp [hf, hd, hm] at hcall; cases b <;> simp_all
        | div => simp [hf, hd, hm] at hcall; cases b <;> simp_all
        | ok m =>
          cases hr : tacenta_braid.Braid.receive real.braid m with
          | fail err => simp [hf, hd, hm, hr] at hcall; cases b <;> simp_all
          | div => simp [hf, hd, hm, hr] at hcall; cases b <;> simp_all
          | ok result =>
            rcases result with ⟨receivedEpoch, output, braidCandidate⟩
            cases output with
            | none =>
              exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none,
                by simpa using hd, by simpa using hm, by simpa using hr, .none rfl⟩
            | some output =>
              cases hs : tacenta_spqr.Output.new output.key_epoch output.key with
              | fail err => simp [hf, hd, hm, hr, hs] at hcall; cases b <;> simp_all
              | div => simp [hf, hd, hm, hr, hs] at hcall; cases b <;> simp_all
              | ok converted =>
                have hconverted : tacenta_spqr.Output.new output.key_epoch output.key =
                    ok converted := by simpa using hs
                have hsparse : RealSparseConversion (some output) (some converted) := by
                  exact .some output converted rfl hconverted
                exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted,
                  by simpa using hd, by simpa using hm, by simpa using hr, hsparse⟩

/-! A concrete Triple refusal still has to pass the same decode, message and
Braid stages as a successful receive.  This inversion records those values
from the exact refusal result so the later Triple adapter cannot accept a
caller-selected Braid candidate. -/
theorem decrypt_ratchet_triple_refusal_braid_prefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (realReason : tacenta_triple.TripleError) (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Triple realReason), next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m =
        ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput := by
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases hd : tacenta_wire.decode_message message with
    | fail err => simp [hf, hd] at hcall; cases b <;> simp_all
    | div => simp [hf, hd] at hcall; cases b <;> simp_all
    | ok r =>
      cases r with
      | Err err => simp [hf, hd] at hcall; cases b <;> simp_all
      | Ok decoded =>
        cases hm : lifecycle.msg_of decoded.header with
        | fail err => simp [hf, hd, hm] at hcall; cases b <;> simp_all
        | div => simp [hf, hd, hm] at hcall; cases b <;> simp_all
        | ok m =>
          cases hr : tacenta_braid.Braid.receive real.braid m with
          | fail err => simp [hf, hd, hm, hr] at hcall; cases b <;> simp_all
          | div => simp [hf, hd, hm, hr] at hcall; cases b <;> simp_all
          | ok result =>
            rcases result with ⟨receivedEpoch, output, braidCandidate⟩
            cases output with
            | none =>
              exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none,
                by simpa using hd, by simpa using hm, by simpa using hr, .none rfl⟩
            | some output =>
              cases hs : tacenta_spqr.Output.new output.key_epoch output.key with
              | fail err => simp [hf, hd, hm, hr, hs] at hcall; cases b <;> simp_all
              | div => simp [hf, hd, hm, hr, hs] at hcall; cases b <;> simp_all
              | ok converted =>
                have hconverted : tacenta_spqr.Output.new output.key_epoch output.key =
                    ok converted := by simpa using hs
                have hsparse : RealSparseConversion (some output) (some converted) := by
                  exact .some output converted rfl hconverted
                exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted,
                  by simpa using hd, by simpa using hm, by simpa using hr, hsparse⟩

theorem decrypt_ratchet_triple_refusal_dh_prefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (realReason : tacenta_triple.TripleError) (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Triple realReason), next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m =
        ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput,
      hdecode, hmessage, hreceive, hsparse⟩ :=
    decrypt_ratchet_triple_refusal_braid_prefix rngCore cryptoRng real message rng rngNext
      realReason next hcall
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout] at hcall
          cases hp : tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh with
          | fail e => simp [hp] at hcall
          | div => simp [hp] at hcall
          | ok peer =>
            cases ha : tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer with
            | fail e => simp [hp, ha] at hcall
            | div => simp [hp, ha] at hcall
            | ok result =>
              cases result with
              | none => simp [hp, ha] at hcall
              | some recvSecret =>
                exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
                  hdecode, hmessage, hreceive, .none rfl, by simpa using hp, by simpa using ha⟩
        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          cases hs : tacenta_spqr.Output.new output.key_epoch output.key with
          | fail e => simp [hf, hdecode, hmessage, hreceive, hs] at hcall
          | div => simp [hf, hdecode, hmessage, hreceive, hs] at hcall
          | ok converted' =>
            simp [hf, hdecode, hmessage, hreceive, hs] at hcall
            cases hp : tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh with
            | fail e => simp [hp] at hcall
            | div => simp [hp] at hcall
            | ok peer =>
              cases ha : tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer with
              | fail e => simp [hp, ha] at hcall
              | div => simp [hp, ha] at hcall
              | ok result =>
                cases result with
                | none => simp [hp, ha] at hcall
                | some recvSecret =>
                  exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted', peer,
                    recvSecret, hdecode, hmessage, hreceive, .some output converted' rfl hs,
                    by simpa using hp, by simpa using ha⟩

theorem decrypt_ratchet_triple_refusal_random_prefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (realReason : tacenta_triple.TripleError) (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Triple realReason), next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret
      wrappedRecv candidateBytes rng1,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m =
        ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret ∧
      lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1) := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
      hdecode, hmessage, hreceive, hsparse, hpeer, hfirst⟩ :=
    decrypt_ratchet_triple_refusal_dh_prefix rngCore cryptoRng real message rng rngNext
      realReason next hcall
  let inst32 := Array.Insts.ZeroizeZeroize 32#usize
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
  obtain ⟨wrappedRecv, hwrap, hderef⟩ := zeroizing_roundtrip hz32 inst32 recvSecret
  dsimp [inst32] at hwrap hderef
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout, hpeer, hfirst, hwrap, hderef] at hcall
          cases hr : lifecycle.random_secret rngCore cryptoRng rng with
          | fail e => simp [hwrap, hderef, hr] at hcall
          | div => simp [hwrap, hderef, hr] at hcall
          | ok draw =>
            rcases draw with ⟨candidateBytes, rng1⟩
            exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
              wrappedRecv, candidateBytes, rng1, hdecode, hmessage, hreceive, .none rfl, hpeer, hfirst,
              hwrap, hderef, by simpa using hr⟩
        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          simp [hf, hdecode, hmessage, hreceive, hconverted, hpeer, hfirst, hwrap, hderef] at hcall
          cases hr : lifecycle.random_secret rngCore cryptoRng rng with
          | fail e => simp [hwrap, hderef, hr] at hcall
          | div => simp [hwrap, hderef, hr] at hcall
          | ok draw =>
            rcases draw with ⟨candidateBytes, rng1⟩
            exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted, peer,
              recvSecret, wrappedRecv, candidateBytes, rng1, hdecode, hmessage, hreceive,
              .some output converted rfl hconverted, hpeer, hfirst, hwrap, hderef,
              by simpa using hr⟩

theorem decrypt_ratchet_triple_refusal_second_dh_prefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (realReason : tacenta_triple.TripleError) (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Triple realReason), next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret wrappedRecv
      candidateBytes rng1 candidatePrivate sendSecret wrappedSend,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m =
        ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret ∧
      lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1) ∧
      tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate ∧
      tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer = ok (some sendSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret = ok wrappedSend ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend = ok sendSecret := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
      wrappedRecv, candidateBytes, rng1, hdecode, hmessage, hreceive, hsparse, hpeer, hfirst,
      hwrap, hderef, hrandom⟩ :=
    decrypt_ratchet_triple_refusal_random_prefix rngCore cryptoRng hz32 real message rng rngNext
      realReason next hcall
  let inst32 := Array.Insts.ZeroizeZeroize 32#usize
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout, hpeer, hfirst, hwrap, hderef, hrandom] at hcall
          cases hc : tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes with
          | fail e => simp [hc] at hcall
          | div => simp [hc] at hcall
          | ok candidatePrivate =>
            cases ha : tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer with
            | fail e => simp [hc, ha] at hcall
            | div => simp [hc, ha] at hcall
            | ok result =>
              cases result with
              | none => simp [hc, ha] at hcall
              | some sendSecret =>
                obtain ⟨wrappedSend, hwrapSend, hderefSend⟩ :=
                  zeroizing_roundtrip hz32 inst32 sendSecret
                dsimp [inst32] at hwrapSend hderefSend
                exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
                  wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend,
                  hdecode, hmessage, hreceive, .none rfl, hpeer, hfirst, hwrap, hderef, hrandom,
                  by simpa using hc, by simpa using ha, hwrapSend, hderefSend⟩
        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          simp [hf, hdecode, hmessage, hreceive, hconverted, hpeer, hfirst, hwrap, hderef, hrandom]
            at hcall
          cases hc : tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes with
          | fail e => simp [hc] at hcall
          | div => simp [hc] at hcall
          | ok candidatePrivate =>
            cases ha : tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer with
            | fail e => simp [hc, ha] at hcall
            | div => simp [hc, ha] at hcall
            | ok result =>
              cases result with
              | none => simp [hc, ha] at hcall
              | some sendSecret =>
                obtain ⟨wrappedSend, hwrapSend, hderefSend⟩ :=
                  zeroizing_roundtrip hz32 inst32 sendSecret
                dsimp [inst32] at hwrapSend hderefSend
                exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted, peer,
                  recvSecret, wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret,
                  wrappedSend, hdecode, hmessage, hreceive, .some output converted rfl hconverted,
                  hpeer, hfirst, hwrap, hderef, hrandom, by simpa using hc, by simpa using ha,
                  hwrapSend, hderefSend⟩

theorem decrypt_ratchet_aead_refusal_braid_prefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m =
        ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput := by
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases hd : tacenta_wire.decode_message message with
    | fail err => simp [hf, hd] at hcall; cases b <;> simp_all
    | div => simp [hf, hd] at hcall; cases b <;> simp_all
    | ok r =>
      cases r with
      | Err err => simp [hf, hd] at hcall; cases b <;> simp_all
      | Ok decoded =>
        cases hm : lifecycle.msg_of decoded.header with
        | fail err => simp [hf, hd, hm] at hcall; cases b <;> simp_all
        | div => simp [hf, hd, hm] at hcall; cases b <;> simp_all
        | ok m =>
          cases hr : tacenta_braid.Braid.receive real.braid m with
          | fail err => simp [hf, hd, hm, hr] at hcall; cases b <;> simp_all
          | div => simp [hf, hd, hm, hr] at hcall; cases b <;> simp_all
          | ok result =>
            rcases result with ⟨receivedEpoch, output, braidCandidate⟩
            cases output with
            | none =>
              exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none,
                by simpa using hd, by simpa using hm, by simpa using hr, .none rfl⟩
            | some output =>
              cases hs : tacenta_spqr.Output.new output.key_epoch output.key with
              | fail err => simp [hf, hd, hm, hr, hs] at hcall; cases b <;> simp_all
              | div => simp [hf, hd, hm, hr, hs] at hcall; cases b <;> simp_all
              | ok converted =>
                have hconverted : tacenta_spqr.Output.new output.key_epoch output.key =
                    ok converted := by simpa using hs
                have hsparse : RealSparseConversion (some output) (some converted) := by
                  exact .some output converted rfl hconverted
                exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted,
                  by simpa using hd, by simpa using hm, by simpa using hr, hsparse⟩


theorem decrypt_ratchet_aead_refusal_dh_prefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m =
        ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput,
      hdecode, hmessage, hreceive, hsparse⟩ :=
    decrypt_ratchet_aead_refusal_braid_prefix rngCore cryptoRng real message rng rngNext
      next hcall
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout] at hcall
          cases hp : tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh with
          | fail e => simp [hp] at hcall
          | div => simp [hp] at hcall
          | ok peer =>
            cases ha : tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer with
            | fail e => simp [hp, ha] at hcall
            | div => simp [hp, ha] at hcall
            | ok result =>
              cases result with
              | none => simp [hp, ha] at hcall
              | some recvSecret =>
                exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
                  hdecode, hmessage, hreceive, .none rfl, by simpa using hp, by simpa using ha⟩
        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          cases hs : tacenta_spqr.Output.new output.key_epoch output.key with
          | fail e => simp [hf, hdecode, hmessage, hreceive, hs] at hcall
          | div => simp [hf, hdecode, hmessage, hreceive, hs] at hcall
          | ok converted' =>
            simp [hf, hdecode, hmessage, hreceive, hs] at hcall
            cases hp : tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh with
            | fail e => simp [hp] at hcall
            | div => simp [hp] at hcall
            | ok peer =>
              cases ha : tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer with
              | fail e => simp [hp, ha] at hcall
              | div => simp [hp, ha] at hcall
              | ok result =>
                cases result with
                | none => simp [hp, ha] at hcall
                | some recvSecret =>
                  exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted', peer,
                    recvSecret, hdecode, hmessage, hreceive, .some output converted' rfl hs,
                    by simpa using hp, by simpa using ha⟩


theorem decrypt_ratchet_aead_refusal_random_prefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret
      wrappedRecv candidateBytes rng1,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m =
        ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret ∧
      lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1) := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
      hdecode, hmessage, hreceive, hsparse, hpeer, hfirst⟩ :=
    decrypt_ratchet_aead_refusal_dh_prefix rngCore cryptoRng real message rng rngNext
      next hcall
  let inst32 := Array.Insts.ZeroizeZeroize 32#usize
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
  obtain ⟨wrappedRecv, hwrap, hderef⟩ := zeroizing_roundtrip hz32 inst32 recvSecret
  dsimp [inst32] at hwrap hderef
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout, hpeer, hfirst, hwrap, hderef] at hcall
          cases hr : lifecycle.random_secret rngCore cryptoRng rng with
          | fail e => simp [hwrap, hderef, hr] at hcall
          | div => simp [hwrap, hderef, hr] at hcall
          | ok draw =>
            rcases draw with ⟨candidateBytes, rng1⟩
            exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
              wrappedRecv, candidateBytes, rng1, hdecode, hmessage, hreceive, .none rfl, hpeer, hfirst,
              hwrap, hderef, by simpa using hr⟩
        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          simp [hf, hdecode, hmessage, hreceive, hconverted, hpeer, hfirst, hwrap, hderef] at hcall
          cases hr : lifecycle.random_secret rngCore cryptoRng rng with
          | fail e => simp [hwrap, hderef, hr] at hcall
          | div => simp [hwrap, hderef, hr] at hcall
          | ok draw =>
            rcases draw with ⟨candidateBytes, rng1⟩
            exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted, peer,
              recvSecret, wrappedRecv, candidateBytes, rng1, hdecode, hmessage, hreceive,
              .some output converted rfl hconverted, hpeer, hfirst, hwrap, hderef,
              by simpa using hr⟩


theorem decrypt_ratchet_aead_refusal_second_dh_prefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret wrappedRecv
      candidateBytes rng1 candidatePrivate sendSecret wrappedSend,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m =
        ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret ∧
      lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1) ∧
      tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate ∧
      tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer = ok (some sendSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret = ok wrappedSend ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend = ok sendSecret := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
      wrappedRecv, candidateBytes, rng1, hdecode, hmessage, hreceive, hsparse, hpeer, hfirst,
      hwrap, hderef, hrandom⟩ :=
    decrypt_ratchet_aead_refusal_random_prefix rngCore cryptoRng hz32 real message rng rngNext
      next hcall
  let inst32 := Array.Insts.ZeroizeZeroize 32#usize
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout, hpeer, hfirst, hwrap, hderef, hrandom] at hcall
          cases hc : tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes with
          | fail e => simp [hc] at hcall
          | div => simp [hc] at hcall
          | ok candidatePrivate =>
            cases ha : tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer with
            | fail e => simp [hc, ha] at hcall
            | div => simp [hc, ha] at hcall
            | ok result =>
              cases result with
              | none => simp [hc, ha] at hcall
              | some sendSecret =>
                obtain ⟨wrappedSend, hwrapSend, hderefSend⟩ :=
                  zeroizing_roundtrip hz32 inst32 sendSecret
                dsimp [inst32] at hwrapSend hderefSend
                exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
                  wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend,
                  hdecode, hmessage, hreceive, .none rfl, hpeer, hfirst, hwrap, hderef, hrandom,
                  by simpa using hc, by simpa using ha, hwrapSend, hderefSend⟩
        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          simp [hf, hdecode, hmessage, hreceive, hconverted, hpeer, hfirst, hwrap, hderef, hrandom]
            at hcall
          cases hc : tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes with
          | fail e => simp [hc] at hcall
          | div => simp [hc] at hcall
          | ok candidatePrivate =>
            cases ha : tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer with
            | fail e => simp [hc, ha] at hcall
            | div => simp [hc, ha] at hcall
            | ok result =>
              cases result with
              | none => simp [hc, ha] at hcall
              | some sendSecret =>
                obtain ⟨wrappedSend, hwrapSend, hderefSend⟩ :=
                  zeroizing_roundtrip hz32 inst32 sendSecret
                dsimp [inst32] at hwrapSend hderefSend
                exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted, peer,
                  recvSecret, wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret,
                  wrappedSend, hdecode, hmessage, hreceive, .some output converted rfl hconverted,
                  hpeer, hfirst, hwrap, hderef, hrandom, by simpa using hc, by simpa using ha,
                  hwrapSend, hderefSend⟩


theorem decrypt_ratchet_triple_refusal_prefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (realReason : tacenta_triple.TripleError) (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Triple realReason), next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret wrappedRecv
      candidateBytes rng1 candidatePrivate sendSecret wrappedSend before realHeader candidatePublic
      newPublicBytes,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m =
        ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret ∧
      lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1) ∧
      rng1 = rngNext ∧
      tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate ∧
      tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer = ok (some sendSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret = ok wrappedSend ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend = ok sendSecret ∧
      tacenta_triple.State.sending_public real.triple = ok before ∧
      lifecycle.triple_header_of decoded.header = ok realHeader ∧
      tacenta_boundary.dh.PrivateKey.public_key candidatePrivate = ok candidatePublic ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic = ok newPublicBytes ∧
      lifecycle.receive_with_eviction real.triple decoded.header realHeader
        recvSecret sendSecret newPublicBytes sparseOutput = ok (.Err realReason) := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
      wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend,
      hdecode, hmessage, hreceive, hsparse, hpeer, hfirst, hwrapRecv, hderefRecv,
      hrandom, hcandidate, hsecond, hwrapSend, hderefSend⟩ :=
    decrypt_ratchet_triple_refusal_second_dh_prefix rngCore cryptoRng hz32 real message rng rngNext
      realReason next hcall
  let inst32 := Array.Insts.ZeroizeZeroize 32#usize
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout, hpeer, hfirst, hwrapRecv, hderefRecv,
            hrandom, hcandidate, hsecond, hwrapSend, hderefSend] at hcall
          cases hb : tacenta_triple.State.sending_public real.triple with
          | fail e => simp [hb] at hcall
          | div => simp [hb] at hcall
          | ok before =>
            cases hh : lifecycle.triple_header_of decoded.header with
            | fail e => simp [hb, hh] at hcall
            | div => simp [hb, hh] at hcall
            | ok realHeader =>
              cases hp : tacenta_boundary.dh.PrivateKey.public_key candidatePrivate with
              | fail e => simp [hb, hh, hp] at hcall
              | div => simp [hb, hh, hp] at hcall
              | ok candidatePublic =>
                cases hpb : tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic with
                | fail e => simp [hb, hh, hp, hpb] at hcall
                | div => simp [hb, hh, hp, hpb] at hcall
                | ok newPublicBytes =>
                  cases htr : lifecycle.receive_with_eviction real.triple decoded.header realHeader
                      recvSecret sendSecret newPublicBytes none with
                  | fail e => simp [hb, hh, hp, hpb, htr] at hcall
                  | div => simp [hb, hh, hp, hpb, htr] at hcall
                  | ok result =>
                    cases result with
                    | Err e =>
                      simp [hb, hh, hp, hpb, htr] at hcall
                      have he : e = realReason := by
                        exact hcall.1
                      subst e
                      exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
                        wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend,
                        before, realHeader, candidatePublic, newPublicBytes, hdecode, hmessage, hreceive,
                        .none rfl, hpeer, hfirst, hwrapRecv, hderefRecv, hrandom, hcall.2.2, hcandidate, hsecond,
                        hwrapSend, hderefSend, by simpa using hb, by simpa using hh, by simpa using hp,
                        by simpa using hpb, by simpa using htr⟩
                    | Ok pair =>
                      rcases pair with ⟨realTripleCandidate, realMk⟩
                      cases hmkz : zeroize.Zeroizing.new
                          (Array.Insts.ZeroizeZeroize 32#usize
                            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) realMk with
                      | fail e => simp [hb, hh, hp, hpb, htr, hmkz] at hcall
                      | div => simp [hb, hh, hp, hpb, htr, hmkz] at hcall
                      | ok wrappedMk =>
                        cases hmkd : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                            (Array.Insts.ZeroizeZeroize 32#usize
                              (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedMk with
                        | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd] at hcall
                        | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd] at hcall
                        | ok mkBytes =>
                          cases hk : tacenta_ratchet.message_keys mkBytes tacenta_ratchet.LabelSet.Tacenta with
                          | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk] at hcall
                          | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk] at hcall
                          | ok realKeys =>
                            cases hkeys : zeroize.Zeroizing.new
                                (TupleABC.Insts.ZeroizeZeroize
                                  (Array.Insts.ZeroizeZeroize 32#usize
                                    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
                                  (Array.Insts.ZeroizeZeroize 32#usize
                                    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
                                  (Array.Insts.ZeroizeZeroize 16#usize
                                    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) realKeys with
                            | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys] at hcall
                            | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys] at hcall
                            | ok wrappedKeys =>
                              cases hdkeys : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                  (TupleABC.Insts.ZeroizeZeroize
                                    (Array.Insts.ZeroizeZeroize 32#usize
                                      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
                                    (Array.Insts.ZeroizeZeroize 32#usize
                                      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
                                    (Array.Insts.ZeroizeZeroize 16#usize
                                      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) wrappedKeys with
                              | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys] at hcall
                              | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys] at hcall
                              | ok keyTuple =>
                                rcases keyTuple with ⟨k1, k2, k3⟩
                                cases had : serialization.concat_ad (alloc.vec.Vec.deref real.identity_ad) decoded.header with
                                | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had] at hcall
                                | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had] at hcall
                                | ok realAd =>
                                  cases ha : tacenta_boundary.aead.decrypt k1 k2 k3
                                      (alloc.vec.Vec.deref decoded.ciphertext) (alloc.vec.Vec.deref realAd) with
                                  | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha] at hcall
                                  | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha] at hcall
                                  | ok result =>
                                    cases result with
                                    | Err e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha] at hcall
                                    | Ok value1 =>
                                      cases hsend : tacenta_triple.State.sending_public realTripleCandidate with
                                      | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha, hsend] at hcall
                                      | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha, hsend] at hcall
                                      | ok candidatePublic' =>
                                        cases hne : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
                                            candidatePublic' before with
                                        | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha, hsend, hne] at hcall
                                        | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha, hsend, hne] at hcall
                                        | ok b1 => cases b1 <;>
                                            simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha, hsend, hne] at hcall

        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          simp [hf, hdecode, hmessage, hreceive, hconverted, hpeer, hfirst, hwrapRecv, hderefRecv,
            hrandom, hcandidate, hsecond, hwrapSend, hderefSend] at hcall
          cases hb : tacenta_triple.State.sending_public real.triple with
          | fail e => simp [hb] at hcall
          | div => simp [hb] at hcall
          | ok before =>
            cases hh : lifecycle.triple_header_of decoded.header with
            | fail e => simp [hb, hh] at hcall
            | div => simp [hb, hh] at hcall
            | ok realHeader =>
              cases hp : tacenta_boundary.dh.PrivateKey.public_key candidatePrivate with
              | fail e => simp [hb, hh, hp] at hcall
              | div => simp [hb, hh, hp] at hcall
              | ok candidatePublic =>
                cases hpb : tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic with
                | fail e => simp [hb, hh, hp, hpb] at hcall
                | div => simp [hb, hh, hp, hpb] at hcall
                | ok newPublicBytes =>
                  cases htr : lifecycle.receive_with_eviction real.triple decoded.header realHeader
                      recvSecret sendSecret newPublicBytes (some converted) with
                  | fail e => simp [hb, hh, hp, hpb, htr] at hcall
                  | div => simp [hb, hh, hp, hpb, htr] at hcall
                  | ok result =>
                    cases result with
                    | Err e =>
                      simp [hb, hh, hp, hpb, htr] at hcall
                      have he : e = realReason := by
                        exact hcall.1
                      subst e
                      exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted,
                        peer, recvSecret, wrappedRecv, candidateBytes, rng1, candidatePrivate,
                        sendSecret, wrappedSend, before, realHeader, candidatePublic, newPublicBytes,
                        hdecode, hmessage, hreceive, .some output converted rfl hconverted, hpeer,
                        hfirst, hwrapRecv, hderefRecv, hrandom, hcall.2.2, hcandidate, hsecond, hwrapSend,
                        hderefSend, by simpa using hb, by simpa using hh, by simpa using hp,
                        by simpa using hpb, by simpa using htr⟩
                    | Ok pair =>
                      rcases pair with ⟨realTripleCandidate, realMk⟩
                      cases hmkz : zeroize.Zeroizing.new
                          (Array.Insts.ZeroizeZeroize 32#usize
                            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) realMk with
                      | fail e => simp [hb, hh, hp, hpb, htr, hmkz] at hcall
                      | div => simp [hb, hh, hp, hpb, htr, hmkz] at hcall
                      | ok wrappedMk =>
                        cases hmkd : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                            (Array.Insts.ZeroizeZeroize 32#usize
                              (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedMk with
                        | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd] at hcall
                        | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd] at hcall
                        | ok mkBytes =>
                          cases hk : tacenta_ratchet.message_keys mkBytes tacenta_ratchet.LabelSet.Tacenta with
                          | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk] at hcall
                          | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk] at hcall
                          | ok realKeys =>
                            cases hkeys : zeroize.Zeroizing.new
                                (TupleABC.Insts.ZeroizeZeroize
                                  (Array.Insts.ZeroizeZeroize 32#usize
                                    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
                                  (Array.Insts.ZeroizeZeroize 32#usize
                                    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
                                  (Array.Insts.ZeroizeZeroize 16#usize
                                    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) realKeys with
                            | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys] at hcall
                            | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys] at hcall
                            | ok wrappedKeys =>
                              cases hdkeys : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                  (TupleABC.Insts.ZeroizeZeroize
                                    (Array.Insts.ZeroizeZeroize 32#usize
                                      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
                                    (Array.Insts.ZeroizeZeroize 32#usize
                                      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
                                    (Array.Insts.ZeroizeZeroize 16#usize
                                      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) wrappedKeys with
                              | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys] at hcall
                              | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys] at hcall
                              | ok keyTuple =>
                                rcases keyTuple with ⟨k1, k2, k3⟩
                                cases had : serialization.concat_ad (alloc.vec.Vec.deref real.identity_ad) decoded.header with
                                | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had] at hcall
                                | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had] at hcall
                                | ok realAd =>
                                  cases ha : tacenta_boundary.aead.decrypt k1 k2 k3
                                      (alloc.vec.Vec.deref decoded.ciphertext) (alloc.vec.Vec.deref realAd) with
                                  | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha] at hcall
                                  | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha] at hcall
                                  | ok result =>
                                    cases result with
                                    | Err e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha] at hcall
                                    | Ok value1 =>
                                      cases hsend : tacenta_triple.State.sending_public realTripleCandidate with
                                      | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha, hsend] at hcall
                                      | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha, hsend] at hcall
                                      | ok candidatePublic' =>
                                        cases hne : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
                                            candidatePublic' before with
                                        | fail e => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha, hsend, hne] at hcall
                                        | div => simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha, hsend, hne] at hcall
                                        | ok b1 => cases b1 <;>
                                            simp [hb, hh, hp, hpb, htr, hmkz, hmkd, hk, hkeys, hdkeys, had, ha, hsend, hne] at hcall

/-! Package the generated Triple-refusal inversion so the branch adapter can
consume it without re-selecting any intermediate value. -/
structure InitialRatchetTripleRefusalPrefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (realReason : tacenta_triple.TripleError) (next : lifecycle.Session) : Type where
  decoded : tacenta_wire.DecodedMessage
  m : tacenta_braid.Msg
  receivedEpoch : Std.U64
  output : Option tacenta_braid.Output
  braidCandidate : tacenta_braid.Braid
  sparseOutput : Option tacenta_spqr.Output
  peer : tacenta_boundary.dh.PublicKeyBytes
  recvSecret : Array Std.U8 32#usize
  candidateBytes : Array Std.U8 32#usize
  wrappedRecv : zeroize.Zeroizing (Array Std.U8 32#usize)
  rng1 : R
  candidatePrivate : tacenta_boundary.dh.PrivateKey
  sendSecret : Array Std.U8 32#usize
  wrappedSend : zeroize.Zeroizing (Array Std.U8 32#usize)
  before : Array Std.U8 32#usize
  realHeader : tacenta_triple.Header
  candidatePublic : tacenta_boundary.dh.PublicKeyBytes
  newPublicBytes : Array Std.U8 32#usize
  hdecode : tacenta_wire.decode_message message = ok (.Ok decoded)
  hmessage : lifecycle.msg_of decoded.header = ok m
  hreceive : tacenta_braid.Braid.receive real.braid m =
    ok (receivedEpoch, output, braidCandidate)
  hsparse : RealSparseConversion output sparseOutput
  hpeer : tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer
  hfirst : tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer =
    ok (some recvSecret)
  hwrapRecv : zeroize.Zeroizing.new
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv
  hderefRecv : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret
  hrandom : lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1)
  hrng : rng1 = rngNext
  hcandidate : tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate
  hsecond : tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer =
    ok (some sendSecret)
  hwrapSend : zeroize.Zeroizing.new
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret = ok wrappedSend
  hderefSend : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend = ok sendSecret
  hbefore : tacenta_triple.State.sending_public real.triple = ok before
  hheader : lifecycle.triple_header_of decoded.header = ok realHeader
  hpublic : tacenta_boundary.dh.PrivateKey.public_key candidatePrivate = ok candidatePublic
  hpublicBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic = ok newPublicBytes
  htriple : lifecycle.receive_with_eviction real.triple decoded.header realHeader
    recvSecret sendSecret newPublicBytes sparseOutput = ok (.Err realReason)

noncomputable def initial_ratchet_triple_refusal_prefix_of_result {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (realReason : tacenta_triple.TripleError) (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Triple realReason), next, rngNext)) :
    InitialRatchetTripleRefusalPrefix rngCore cryptoRng real message rng rngNext
      realReason next := Classical.choice (show Nonempty
        (InitialRatchetTripleRefusalPrefix rngCore cryptoRng real message rng rngNext
          realReason next) from by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
      wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
      realHeader, candidatePublic, newPublicBytes, hdecode, hmessage, hreceive, hsparse, hpeer,
      hfirst, hwrapRecv, hderefRecv, hrandom, hrng, hcandidate, hsecond, hwrapSend,
      hderefSend, hbefore, hheader, hpublic, hpublicBytes, htriple⟩ :=
    decrypt_ratchet_triple_refusal_prefix rngCore cryptoRng hz32 real message rng rngNext
      realReason next hcall
  exact ⟨{
    decoded := decoded, m := m, receivedEpoch := receivedEpoch, output := output,
    braidCandidate := braidCandidate, sparseOutput := sparseOutput, peer := peer,
    recvSecret := recvSecret, wrappedRecv := wrappedRecv, candidateBytes := candidateBytes,
    rng1 := rng1, candidatePrivate := candidatePrivate, sendSecret := sendSecret,
    wrappedSend := wrappedSend, before := before, realHeader := realHeader,
    candidatePublic := candidatePublic, newPublicBytes := newPublicBytes,
    hdecode := hdecode, hmessage := hmessage, hreceive := hreceive, hsparse := hsparse,
    hpeer := hpeer, hfirst := hfirst, hwrapRecv := hwrapRecv, hderefRecv := hderefRecv,
    hrandom := hrandom, hrng := hrng, hcandidate := hcandidate, hsecond := hsecond,
    hwrapSend := hwrapSend, hderefSend := hderefSend, hbefore := hbefore,
    hheader := hheader, hpublic := hpublic, hpublicBytes := hpublicBytes, htriple := htriple }⟩)

def initial_ratchet_braid_evidence_of_triple_refusal_prefix
    {R : Type} {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {rngCore : rand_core_1.RngCore R} {cryptoRng : rand_core_1.CryptoRng R}
    {realReason : tacenta_triple.TripleError} {next : lifecycle.Session}
    (pref : InitialRatchetTripleRefusalPrefix rngCore cryptoRng real message rng rngNext
      realReason next)
    (modelComposite : Model.CompositeHeader.Composite)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines pref.m
      (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hnext : Tacenta.SessionUnitBraidT3.StateRefines K pref.braidCandidate.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2) :
    BraidReceiveEvidence K view real model pref.decoded.header modelComposite :=
  { message := pref.m
    receivedEpoch := pref.receivedEpoch
    output := pref.output
    next := pref.braidCandidate
    sparseOutput := pref.sparseOutput
    hmessageCall := pref.hmessage
    hmessageRel := hmessageRel
    hreceive := pref.hreceive
    hsparse := pref.hsparse
    hnext := hnext }

theorem triple_refusal_prefix_trace_next
    {R : Type} {rngCore : rand_core_1.RngCore R} {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
    {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {message : Slice Std.U8} {rng rngNext : R}
    {realReason : tacenta_triple.TripleError} {next : lifecycle.Session}
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (pref : InitialRatchetTripleRefusalPrefix rngCore cryptoRng real message rng rngNext
      realReason next)
    (htrace : trace rng = oracle.draws)
    (draw : Model.Lifecycle.Key)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext)) :
    trace rngNext = oracleNext.draws := by
  cases hd : oracle.draws with
  | nil =>
      simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hd] at hmodelDraw
  | cons head rest =>
      simp only [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hd,
        Option.some.injEq, Prod.mk.injEq] at hmodelDraw
      have hdrawHead : head = draw := hmodelDraw.1
      have hdrawRest : rest = oracleNext.draws := by
        have hrest := congrArg Model.Lifecycle.Oracle.draws hmodelDraw.2
        simpa using hrest
      have htraceDraw : trace rng = draw :: rest := by simpa [htrace, hd, hdrawHead]
      obtain ⟨candidateBytes, realRngNext, hrandomCall, hdrawBytes, htraceNext⟩ :=
        oracleOf.random32 rng draw rest htraceDraw
      have heq := pref.hrandom.symm.trans hrandomCall
      have hrngEq : realRngNext = pref.rng1 := by
        have hpair : (pref.candidateBytes, pref.rng1) = (candidateBytes, realRngNext) := by
          injection heq
        exact (Prod.mk.inj hpair).2.symm
      subst realRngNext
      simpa [pref.hrng, hdrawRest] using htraceNext

/-! The concrete Triple prefix now feeds the existing leaf adapter.  This is
the first fully composed nonterminal refusal route: the prefix supplies the
real execution witnesses, while the Braid adapter supplies the model-side
message and state relation. -/

theorem decrypt_ratchet_triple_refusal_from_prefix
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (decoded : tacenta_wire.DecodedMessage)
    (modelComposite : Model.CompositeHeader.Composite)
    (realReason : tacenta_triple.TripleError) (next : lifecycle.Session)
    (pref : InitialRatchetTripleRefusalPrefix rngCore cryptoRng real message rng rngNext
      realReason next)
    (htrace : trace rng = oracle.draws)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines pref.m
      (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hnext : Tacenta.SessionUnitBraidT3.StateRefines K pref.braidCandidate.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf pref.decoded.ciphertext))
    (hcomposite : CompositeRefines pref.decoded.header modelComposite)
    (draw modelDhOutRecv modelDhOutSend : Model.Lifecycle.Key)
    (modelReason : Model.Triple.ReceiveRefusal)
    (hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
      some modelDhOutRecv)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hmodelSecond : oracle.dhAgree draw modelComposite.dh = some modelDhOutSend)
    (hmodelPublic : oracle.dhPublic draw = arrayOf pref.newPublicBytes)
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
  let evidence := initial_ratchet_braid_evidence_of_triple_refusal_prefix
    pref modelComposite hmessageRel hnext
  have htraceNext : trace rngNext = oracleNext.draws :=
    triple_refusal_prefix_trace_next oracleOf pref htrace draw hmodelDraw
  have hrandomCall : lifecycle.random_secret rngCore cryptoRng rng =
      ok (pref.candidateBytes, rngNext) := by
    simpa [pref.hrng] using pref.hrandom
  have htripleReal : lifecycle.receive_with_eviction real.triple pref.decoded.header
      pref.realHeader pref.recvSecret pref.sendSecret pref.newPublicBytes
      pref.sparseOutput = ok (.Err realReason) := pref.htriple
  have hresult := decrypt_ratchet_triple_refusal_from_braid
    rngCore cryptoRng trace dh K view oracle oracleNext real model message rng rngNext
    pref.decoded modelComposite pref.decoded.header evidence rfl pref.peer pref.recvSecret
    pref.sendSecret pref.candidateBytes pref.newPublicBytes pref.before pref.candidatePrivate
    pref.candidatePublic pref.realHeader pref.wrappedRecv pref.wrappedSend realReason
    modelReason draw modelDhOutRecv modelDhOutSend hrel htraceNext hready pref.hdecode
    hdecodeModel hcomposite pref.hpeer pref.hfirst
    pref.hwrapRecv pref.hderefRecv hrandomCall pref.hcandidate pref.hsecond pref.hwrapSend
    pref.hderefSend pref.hbefore pref.hheader pref.hpublic pref.hpublicBytes htripleReal
    hmodelFirst hmodelDraw hmodelSecond hmodelPublic hmodelTriple hreason
  simpa [evidence, initial_ratchet_braid_evidence_of_triple_refusal_prefix] using hresult

/-! Continue inversion through the first public-key decode and DH agreement.
The result is still tied to the same concrete success equation; a failed or
diverging boundary call cannot be hidden behind a caller-supplied witness. -/

theorem decrypt_ratchet_success_dh_prefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext, next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m =
        ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer =
        ok (some recvSecret) := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput,
      hdecode, hmessage, hreceive, hsparse⟩ :=
    decrypt_ratchet_success_braid_prefix rngCore cryptoRng real message rng rngNext plaintext next hcall
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout] at hcall
          cases hp : tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh with
          | fail e => simp [hp] at hcall
          | div => simp [hp] at hcall
          | ok peer =>
            cases ha : tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer with
            | fail e => simp [hp, ha] at hcall
            | div => simp [hp, ha] at hcall
            | ok result =>
              cases result with
              | none => simp [hp, ha] at hcall
              | some recvSecret =>
                exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
                  hdecode, hmessage, hreceive, .none rfl, by simpa using hp, by simpa using ha⟩
        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          cases hs : tacenta_spqr.Output.new output.key_epoch output.key with
          | fail e => simp [hf, hdecode, hmessage, hreceive, hs] at hcall
          | div => simp [hf, hdecode, hmessage, hreceive, hs] at hcall
          | ok converted' =>
            simp [hf, hdecode, hmessage, hreceive, hs] at hcall
            cases hp : tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh with
            | fail e => simp [hp] at hcall
            | div => simp [hp] at hcall
            | ok peer =>
              cases ha : tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer with
              | fail e => simp [hp, ha] at hcall
              | div => simp [hp, ha] at hcall
              | ok result =>
                cases result with
                | none => simp [hp, ha] at hcall
                | some recvSecret =>
                  exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted', peer, recvSecret,
                    hdecode, hmessage, hreceive, .some output converted' rfl hs,
                    by simpa using hp, by simpa using ha⟩

/-! The random draw is the next generated boundary.  Here the stated
zeroizing round-trip contract is used to justify that the value dereferenced
by the translated code is the DH secret recovered above; execution alone does
not provide that representation fact. -/

theorem decrypt_ratchet_success_random_prefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext, next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret
      wrappedRecv candidateBytes rng1,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m = ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret ∧
      lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1) := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
      hdecode, hmessage, hreceive, hsparse, hpeer, hfirst⟩ :=
    decrypt_ratchet_success_dh_prefix rngCore cryptoRng real message rng rngNext plaintext next hcall
  let inst32 := Array.Insts.ZeroizeZeroize 32#usize
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
  obtain ⟨wrappedRecv, hwrap, hderef⟩ := zeroizing_roundtrip hz32 inst32 recvSecret
  dsimp [inst32] at hwrap hderef
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout, hpeer, hfirst, hwrap, hderef] at hcall
          cases hr : lifecycle.random_secret rngCore cryptoRng rng with
          | fail e => simp [hwrap, hderef, hr] at hcall
          | div => simp [hwrap, hderef, hr] at hcall
          | ok draw =>
            rcases draw with ⟨candidateBytes, rng1⟩
            exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
              wrappedRecv, candidateBytes, rng1, hdecode, hmessage, hreceive, .none rfl, hpeer, hfirst,
              hwrap, hderef, by simpa using hr⟩
        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          simp [hf, hdecode, hmessage, hreceive, hconverted, hpeer, hfirst, hwrap, hderef] at hcall
          cases hr : lifecycle.random_secret rngCore cryptoRng rng with
          | fail e => simp [hwrap, hderef, hr] at hcall
          | div => simp [hwrap, hderef, hr] at hcall
          | ok draw =>
            rcases draw with ⟨candidateBytes, rng1⟩
            exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted, peer, recvSecret,
              wrappedRecv, candidateBytes, rng1, hdecode, hmessage, hreceive,
              .some output converted rfl hconverted, hpeer, hfirst, hwrap, hderef,
              by simpa using hr⟩

/-! Candidate-key decoding and the second DH agreement are likewise inverted
from the concrete successful call.  This leaves the remaining Triple and AEAD
calls as the only generated success-prefix work before the existing result
adapter can be invoked. -/

theorem decrypt_ratchet_success_second_dh_prefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext, next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret
      wrappedRecv candidateBytes rng1 candidatePrivate sendSecret,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m = ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret ∧
      lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1) ∧
      tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate ∧
      tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer = ok (some sendSecret) := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
      wrappedRecv, candidateBytes, rng1, hdecode, hmessage, hreceive, hsparse, hpeer, hfirst,
      hwrap, hderef, hrandom⟩ :=
    decrypt_ratchet_success_random_prefix rngCore cryptoRng hz32 real message rng rngNext plaintext next hcall
  let inst32 := Array.Insts.ZeroizeZeroize 32#usize
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout, hpeer, hfirst, hwrap, hderef, hrandom] at hcall
          cases hc : tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes with
          | fail e => simp [hc] at hcall
          | div => simp [hc] at hcall
          | ok candidatePrivate =>
            cases ha : tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer with
            | fail e => simp [hc, ha] at hcall
            | div => simp [hc, ha] at hcall
            | ok result =>
              cases result with
              | none => simp [hc, ha] at hcall
              | some sendSecret =>
                exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
                  wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret,
                  hdecode, hmessage, hreceive, .none rfl, hpeer, hfirst, hwrap, hderef,
                  hrandom, by simpa using hc, by simpa using ha⟩
        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          simp [hf, hdecode, hmessage, hreceive, hconverted, hpeer, hfirst, hwrap, hderef, hrandom] at hcall
          cases hc : tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes with
          | fail e => simp [hc] at hcall
          | div => simp [hc] at hcall
          | ok candidatePrivate =>
            cases ha : tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer with
            | fail e => simp [hc, ha] at hcall
            | div => simp [hc, ha] at hcall
            | ok result =>
              cases result with
              | none => simp [hc, ha] at hcall
              | some sendSecret =>
                exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted, peer, recvSecret,
                  wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret,
                  hdecode, hmessage, hreceive, .some output converted rfl hconverted,
                  hpeer, hfirst, hwrap, hderef, hrandom, by simpa using hc, by simpa using ha⟩

theorem decrypt_ratchet_aead_refusal_triple_prefix {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret wrappedRecv
      candidateBytes rng1 candidatePrivate sendSecret wrappedSend before realHeader candidatePublic
      newPublicBytes realTripleCandidate realMk,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m = ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret ∧
      lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1) ∧
      tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate ∧
      tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer = ok (some sendSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret = ok wrappedSend ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend = ok sendSecret ∧
      tacenta_triple.State.sending_public real.triple = ok before ∧
      lifecycle.triple_header_of decoded.header = ok realHeader ∧
      tacenta_boundary.dh.PrivateKey.public_key candidatePrivate = ok candidatePublic ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic = ok newPublicBytes ∧
      lifecycle.receive_with_eviction real.triple decoded.header realHeader
        recvSecret sendSecret newPublicBytes sparseOutput =
        ok (.Ok (realTripleCandidate, realMk)) := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
      wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend,
      hdecode, hmessage, hreceive, hsparse, hpeer, hfirst, hwrapRecv, hderefRecv,
      hrandom, hcandidate, hsecond, hwrapSend, hderefSend⟩ :=
    decrypt_ratchet_aead_refusal_second_dh_prefix rngCore cryptoRng hz32 real message rng rngNext next hcall
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      revert hcall hreceive
      cases hsparse with
      | none hout =>
        intro hcall hreceive
        cases output with
        | none =>
            simp [hf, hdecode, hmessage, hreceive, hout, hpeer, hfirst, hwrapRecv, hderefRecv,
              hrandom, hcandidate, hsecond, hwrapSend, hderefSend] at hcall
            cases hb : tacenta_triple.State.sending_public real.triple with
            | fail e => simp [hb] at hcall
            | div => simp [hb] at hcall
            | ok before =>
              cases hh : lifecycle.triple_header_of decoded.header with
              | fail e => simp [hb, hh] at hcall
              | div => simp [hb, hh] at hcall
              | ok realHeader =>
                cases hp : tacenta_boundary.dh.PrivateKey.public_key candidatePrivate with
                | fail e => simp [hb, hh, hp] at hcall
                | div => simp [hb, hh, hp] at hcall
                | ok candidatePublic =>
                  cases hpb : tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic with
                  | fail e => simp [hb, hh, hp, hpb] at hcall
                  | div => simp [hb, hh, hp, hpb] at hcall
                  | ok newPublicBytes =>
                    cases htr : lifecycle.receive_with_eviction real.triple decoded.header realHeader
                        recvSecret sendSecret newPublicBytes none with
                    | fail e => simp [hb, hh, hp, hpb, htr] at hcall
                    | div => simp [hb, hh, hp, hpb, htr] at hcall
                    | ok result =>
                      cases result with
                      | Err e => simp [hb, hh, hp, hpb, htr] at hcall
                      | Ok pair =>
                        rcases pair with ⟨realTripleCandidate, realMk⟩
                        exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
                          wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
                          realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk,
                          hdecode, hmessage, hreceive, .none rfl, hpeer, hfirst, hwrapRecv, hderefRecv,
                          hrandom, hcandidate, hsecond, hwrapSend, hderefSend, by simpa using hb,
                          by simpa using hh, by simpa using hp, by simpa using hpb, by simpa using htr⟩
        | some output => simp_all
      | some realOutput converted hout hconverted =>
        intro hcall hreceive
        cases hout
        simp [hf, hdecode, hmessage, hreceive, hconverted, hpeer, hfirst, hwrapRecv, hderefRecv,
          hrandom, hcandidate, hsecond, hwrapSend, hderefSend] at hcall
        cases hb : tacenta_triple.State.sending_public real.triple with
        | fail e => simp [hb] at hcall
        | div => simp [hb] at hcall
        | ok before =>
          cases hh : lifecycle.triple_header_of decoded.header with
          | fail e => simp [hb, hh] at hcall
          | div => simp [hb, hh] at hcall
          | ok realHeader =>
            cases hp : tacenta_boundary.dh.PrivateKey.public_key candidatePrivate with
            | fail e => simp [hb, hh, hp] at hcall
            | div => simp [hb, hh, hp] at hcall
            | ok candidatePublic =>
              cases hpb : tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic with
              | fail e => simp [hb, hh, hp, hpb] at hcall
              | div => simp [hb, hh, hp, hpb] at hcall
              | ok newPublicBytes =>
                cases htr : lifecycle.receive_with_eviction real.triple decoded.header realHeader
                    recvSecret sendSecret newPublicBytes (some converted) with
                | fail e => simp [hb, hh, hp, hpb, htr] at hcall
                | div => simp [hb, hh, hp, hpb, htr] at hcall
                | ok result =>
                  cases result with
                  | Err e => simp [hb, hh, hp, hpb, htr] at hcall
                  | Ok pair =>
                    rcases pair with ⟨realTripleCandidate, realMk⟩
                    exact ⟨decoded, m, receivedEpoch, some realOutput, braidCandidate, some converted, peer, recvSecret,
                      wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
                      realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk,
                      hdecode, hmessage, hreceive, .some realOutput converted rfl hconverted, hpeer, hfirst,
                      hwrapRecv, hderefRecv, hrandom, hcandidate, hsecond, hwrapSend, hderefSend,
                      by simpa using hb, by simpa using hh, by simpa using hp, by simpa using hpb, by simpa using htr⟩


theorem decrypt_ratchet_success_triple_prefix {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext, next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret wrappedRecv
      candidateBytes rng1 candidatePrivate sendSecret wrappedSend before realHeader candidatePublic
      newPublicBytes realTripleCandidate realMk,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m = ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret ∧
      lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1) ∧
      tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate ∧
      tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer = ok (some sendSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret = ok wrappedSend ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend = ok sendSecret ∧
      tacenta_triple.State.sending_public real.triple = ok before ∧
      lifecycle.triple_header_of decoded.header = ok realHeader ∧
      tacenta_boundary.dh.PrivateKey.public_key candidatePrivate = ok candidatePublic ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic = ok newPublicBytes ∧
      lifecycle.receive_with_eviction real.triple decoded.header realHeader
        recvSecret sendSecret newPublicBytes sparseOutput =
        ok (.Ok (realTripleCandidate, realMk)) := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
      wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret,
      hdecode, hmessage, hreceive, hsparse, hpeer, hfirst, hwrapRecv, hderefRecv,
      hrandom, hcandidate, hsecond⟩ :=
    decrypt_ratchet_success_second_dh_prefix rngCore cryptoRng hz32 real message rng rngNext plaintext next hcall
  let inst32 := Array.Insts.ZeroizeZeroize 32#usize
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
  obtain ⟨wrappedSend, hwrapSend, hderefSend⟩ := zeroizing_roundtrip hz32 inst32 sendSecret
  dsimp [inst32] at hwrapSend hderefSend
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout, hpeer, hfirst, hwrapRecv, hderefRecv,
            hrandom, hcandidate, hsecond, hwrapSend, hderefSend] at hcall
          cases hb : tacenta_triple.State.sending_public real.triple with
          | fail e => simp [hb] at hcall
          | div => simp [hb] at hcall
          | ok before =>
            cases hh : lifecycle.triple_header_of decoded.header with
            | fail e => simp [hb, hh] at hcall
            | div => simp [hb, hh] at hcall
            | ok realHeader =>
              cases hp : tacenta_boundary.dh.PrivateKey.public_key candidatePrivate with
              | fail e => simp [hb, hh, hp] at hcall
              | div => simp [hb, hh, hp] at hcall
              | ok candidatePublic =>
                cases hpb : tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic with
                | fail e => simp [hb, hh, hp, hpb] at hcall
                | div => simp [hb, hh, hp, hpb] at hcall
                | ok newPublicBytes =>
                  cases htr : lifecycle.receive_with_eviction real.triple decoded.header realHeader
                      recvSecret sendSecret newPublicBytes none with
                  | fail e => simp [hb, hh, hp, hpb, htr] at hcall
                  | div => simp [hb, hh, hp, hpb, htr] at hcall
                  | ok result =>
                    cases result with
                    | Err e => simp [hb, hh, hp, hpb, htr] at hcall
                    | Ok pair =>
                      rcases pair with ⟨realTripleCandidate, realMk⟩
                      exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
                        wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
                        realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk,
                        hdecode, hmessage, hreceive, .none rfl, hpeer, hfirst, hwrapRecv, hderefRecv,
                        hrandom, hcandidate, hsecond, hwrapSend, hderefSend, by simpa using hb,
                        by simpa using hh, by simpa using hp, by simpa using hpb, by simpa using htr⟩
        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          simp [hf, hdecode, hmessage, hreceive, hconverted, hpeer, hfirst, hwrapRecv, hderefRecv,
            hrandom, hcandidate, hsecond, hwrapSend, hderefSend] at hcall
          cases hb : tacenta_triple.State.sending_public real.triple with
          | fail e => simp [hb] at hcall
          | div => simp [hb] at hcall
          | ok before =>
            cases hh : lifecycle.triple_header_of decoded.header with
            | fail e => simp [hb, hh] at hcall
            | div => simp [hb, hh] at hcall
            | ok realHeader =>
              cases hp : tacenta_boundary.dh.PrivateKey.public_key candidatePrivate with
              | fail e => simp [hb, hh, hp] at hcall
              | div => simp [hb, hh, hp] at hcall
              | ok candidatePublic =>
                cases hpb : tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic with
                | fail e => simp [hb, hh, hp, hpb] at hcall
                | div => simp [hb, hh, hp, hpb] at hcall
                | ok newPublicBytes =>
                  cases htr : lifecycle.receive_with_eviction real.triple decoded.header realHeader
                      recvSecret sendSecret newPublicBytes (some converted) with
                  | fail e => simp [hb, hh, hp, hpb, htr] at hcall
                  | div => simp [hb, hh, hp, hpb, htr] at hcall
                  | ok result =>
                    cases result with
                    | Err e => simp [hb, hh, hp, hpb, htr] at hcall
                    | Ok pair =>
                      rcases pair with ⟨realTripleCandidate, realMk⟩
                      exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted, peer, recvSecret,
                        wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
                        realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk,
                        hdecode, hmessage, hreceive, .some output converted rfl hconverted, hpeer, hfirst,
                        hwrapRecv, hderefRecv, hrandom, hcandidate, hsecond, hwrapSend, hderefSend,
                        by simpa using hb, by simpa using hh, by simpa using hp, by simpa using hpb, by simpa using htr⟩

theorem decrypt_ratchet_aead_refusal_keys_prefix {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret wrappedRecv
      candidateBytes rng1 candidatePrivate sendSecret wrappedSend before realHeader candidatePublic
      newPublicBytes realTripleCandidate realMk wrappedMk realKeys wrappedKeys,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m = ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret ∧
      lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1) ∧
      tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate ∧
      tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer = ok (some sendSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret = ok wrappedSend ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend = ok sendSecret ∧
      tacenta_triple.State.sending_public real.triple = ok before ∧
      lifecycle.triple_header_of decoded.header = ok realHeader ∧
      tacenta_boundary.dh.PrivateKey.public_key candidatePrivate = ok candidatePublic ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic = ok newPublicBytes ∧
      lifecycle.receive_with_eviction real.triple decoded.header realHeader
        recvSecret sendSecret newPublicBytes sparseOutput = ok (.Ok (realTripleCandidate, realMk)) ∧
      tacenta_ratchet.message_keys realMk tacenta_ratchet.LabelSet.Tacenta = ok realKeys ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) realMk = ok wrappedMk ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedMk = ok realMk ∧
      zeroize.Zeroizing.new
        (TupleABC.Insts.ZeroizeZeroize
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 16#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) realKeys = ok wrappedKeys ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (TupleABC.Insts.ZeroizeZeroize
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 16#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) wrappedKeys = ok realKeys := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
      wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
      realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk,
      hdecode, hmessage, hreceive, hsparse, hpeer, hfirst, hwrapRecv, hderefRecv,
      hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader,
      hpublic, hpublicBytes, htripleReal⟩ :=
    decrypt_ratchet_aead_refusal_triple_prefix rngCore cryptoRng hz32 real message rng rngNext next hcall
  let inst32 := Array.Insts.ZeroizeZeroize 32#usize
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
  let instKeys := TupleABC.Insts.ZeroizeZeroize
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
    (Array.Insts.ZeroizeZeroize 16#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
  obtain ⟨wrappedMk, hwrapMk, hderefMk⟩ := zeroizing_roundtrip hz32 inst32 realMk
  dsimp [inst32] at hwrapMk hderefMk
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout, hpeer, hfirst, hwrapRecv, hderefRecv,
            hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader, hpublic,
            hpublicBytes, htripleReal, hwrapMk, hderefMk] at hcall
          cases hk : tacenta_ratchet.message_keys realMk tacenta_ratchet.LabelSet.Tacenta with
          | fail e => simp [hk] at hcall
          | div => simp [hk] at hcall
          | ok realKeys =>
            obtain ⟨wrappedKeys, hwrapKeys, hderefKeys⟩ := zeroizing_roundtrip hzKeys instKeys realKeys
            dsimp [instKeys] at hwrapKeys hderefKeys
            exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
              wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
              realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk, wrappedMk,
              realKeys, wrappedKeys, hdecode, hmessage, hreceive, .none rfl, hpeer, hfirst,
              hwrapRecv, hderefRecv, hrandom, hcandidate, hsecond, hwrapSend, hderefSend,
              by simpa using hbefore, by simpa using hheader, by simpa using hpublic,
              by simpa using hpublicBytes, htripleReal, by simpa using hk, hwrapMk, hderefMk,
              hwrapKeys, hderefKeys⟩
        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          simp [hf, hdecode, hmessage, hreceive, hconverted, hpeer, hfirst, hwrapRecv, hderefRecv,
            hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader, hpublic,
            hpublicBytes, htripleReal, hwrapMk, hderefMk] at hcall
          cases hk : tacenta_ratchet.message_keys realMk tacenta_ratchet.LabelSet.Tacenta with
          | fail e => simp [hk] at hcall
          | div => simp [hk] at hcall
          | ok realKeys =>
            obtain ⟨wrappedKeys, hwrapKeys, hderefKeys⟩ := zeroizing_roundtrip hzKeys instKeys realKeys
            dsimp [instKeys] at hwrapKeys hderefKeys
            exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted, peer, recvSecret,
              wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
              realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk, wrappedMk,
              realKeys, wrappedKeys, hdecode, hmessage, hreceive, .some output converted rfl hconverted,
              hpeer, hfirst, hwrapRecv, hderefRecv, hrandom, hcandidate, hsecond, hwrapSend, hderefSend,
              by simpa using hbefore, by simpa using hheader, by simpa using hpublic,
              by simpa using hpublicBytes, htripleReal, by simpa using hk, hwrapMk, hderefMk,
              hwrapKeys, hderefKeys⟩


theorem decrypt_ratchet_success_keys_prefix {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext, next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret wrappedRecv
      candidateBytes rng1 candidatePrivate sendSecret wrappedSend before realHeader candidatePublic
      newPublicBytes realTripleCandidate realMk wrappedMk realKeys wrappedKeys,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m = ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret ∧
      lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1) ∧
      tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate ∧
      tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer = ok (some sendSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret = ok wrappedSend ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend = ok sendSecret ∧
      tacenta_triple.State.sending_public real.triple = ok before ∧
      lifecycle.triple_header_of decoded.header = ok realHeader ∧
      tacenta_boundary.dh.PrivateKey.public_key candidatePrivate = ok candidatePublic ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic = ok newPublicBytes ∧
      lifecycle.receive_with_eviction real.triple decoded.header realHeader
        recvSecret sendSecret newPublicBytes sparseOutput = ok (.Ok (realTripleCandidate, realMk)) ∧
      tacenta_ratchet.message_keys realMk tacenta_ratchet.LabelSet.Tacenta = ok realKeys ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) realMk = ok wrappedMk ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedMk = ok realMk ∧
      zeroize.Zeroizing.new
        (TupleABC.Insts.ZeroizeZeroize
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 16#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) realKeys = ok wrappedKeys ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (TupleABC.Insts.ZeroizeZeroize
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 16#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) wrappedKeys = ok realKeys := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
      wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
      realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk,
      hdecode, hmessage, hreceive, hsparse, hpeer, hfirst, hwrapRecv, hderefRecv,
      hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader,
      hpublic, hpublicBytes, htripleReal⟩ :=
    decrypt_ratchet_success_triple_prefix rngCore cryptoRng hz32 real message rng rngNext plaintext next hcall
  let inst32 := Array.Insts.ZeroizeZeroize 32#usize
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
  let instKeys := TupleABC.Insts.ZeroizeZeroize
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
    (Array.Insts.ZeroizeZeroize 16#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
  obtain ⟨wrappedMk, hwrapMk, hderefMk⟩ := zeroizing_roundtrip hz32 inst32 realMk
  dsimp [inst32] at hwrapMk hderefMk
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout, hpeer, hfirst, hwrapRecv, hderefRecv,
            hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader, hpublic,
            hpublicBytes, htripleReal, hwrapMk, hderefMk] at hcall
          cases hk : tacenta_ratchet.message_keys realMk tacenta_ratchet.LabelSet.Tacenta with
          | fail e => simp [hk] at hcall
          | div => simp [hk] at hcall
          | ok realKeys =>
            obtain ⟨wrappedKeys, hwrapKeys, hderefKeys⟩ := zeroizing_roundtrip hzKeys instKeys realKeys
            dsimp [instKeys] at hwrapKeys hderefKeys
            exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
              wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
              realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk, wrappedMk,
              realKeys, wrappedKeys, hdecode, hmessage, hreceive, .none rfl, hpeer, hfirst,
              hwrapRecv, hderefRecv, hrandom, hcandidate, hsecond, hwrapSend, hderefSend,
              by simpa using hbefore, by simpa using hheader, by simpa using hpublic,
              by simpa using hpublicBytes, htripleReal, by simpa using hk, hwrapMk, hderefMk,
              hwrapKeys, hderefKeys⟩
        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          simp [hf, hdecode, hmessage, hreceive, hconverted, hpeer, hfirst, hwrapRecv, hderefRecv,
            hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader, hpublic,
            hpublicBytes, htripleReal, hwrapMk, hderefMk] at hcall
          cases hk : tacenta_ratchet.message_keys realMk tacenta_ratchet.LabelSet.Tacenta with
          | fail e => simp [hk] at hcall
          | div => simp [hk] at hcall
          | ok realKeys =>
            obtain ⟨wrappedKeys, hwrapKeys, hderefKeys⟩ := zeroizing_roundtrip hzKeys instKeys realKeys
            dsimp [instKeys] at hwrapKeys hderefKeys
            exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted, peer, recvSecret,
              wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
              realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk, wrappedMk,
              realKeys, wrappedKeys, hdecode, hmessage, hreceive, .some output converted rfl hconverted,
              hpeer, hfirst, hwrapRecv, hderefRecv, hrandom, hcandidate, hsecond, hwrapSend, hderefSend,
              by simpa using hbefore, by simpa using hheader, by simpa using hpublic,
              by simpa using hpublicBytes, htripleReal, by simpa using hk, hwrapMk, hderefMk,
              hwrapKeys, hderefKeys⟩

theorem decrypt_ratchet_aead_refusal_final_prefix {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret wrappedRecv
      candidateBytes rng1 candidatePrivate sendSecret wrappedSend before realHeader candidatePublic
      newPublicBytes realTripleCandidate realMk wrappedMk realKeys wrappedKeys realAd aeadError,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m = ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret ∧
      lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1) ∧
      rng1 = rngNext ∧
      tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate ∧
      tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer = ok (some sendSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret = ok wrappedSend ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend = ok sendSecret ∧
      tacenta_triple.State.sending_public real.triple = ok before ∧
      lifecycle.triple_header_of decoded.header = ok realHeader ∧
      tacenta_boundary.dh.PrivateKey.public_key candidatePrivate = ok candidatePublic ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic = ok newPublicBytes ∧
      lifecycle.receive_with_eviction real.triple decoded.header realHeader
        recvSecret sendSecret newPublicBytes sparseOutput = ok (.Ok (realTripleCandidate, realMk)) ∧
      tacenta_ratchet.message_keys realMk tacenta_ratchet.LabelSet.Tacenta = ok realKeys ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) realMk = ok wrappedMk ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedMk = ok realMk ∧
      zeroize.Zeroizing.new
        (TupleABC.Insts.ZeroizeZeroize
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 16#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) realKeys = ok wrappedKeys ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (TupleABC.Insts.ZeroizeZeroize
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 16#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) wrappedKeys = ok realKeys ∧
      serialization.concat_ad (alloc.vec.Vec.deref real.identity_ad) decoded.header = ok realAd ∧
      tacenta_boundary.aead.decrypt realKeys.1 realKeys.2.1 realKeys.2.2
        (alloc.vec.Vec.deref decoded.ciphertext) (alloc.vec.Vec.deref realAd) = ok (.Err aeadError) := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
      wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
      realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk, wrappedMk,
      realKeys, wrappedKeys, hdecode, hmessage, hreceive, hsparse, hpeer, hfirst, hwrapRecv,
      hderefRecv, hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader,
      hpublic, hpublicBytes, htripleReal, hkeys, hwrapMk, hderefMk, hwrapKeys, hderefKeys⟩ :=
    decrypt_ratchet_aead_refusal_keys_prefix rngCore cryptoRng hz32 hzKeys real message rng rngNext next hcall
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      let keyTuple := realKeys
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout, hpeer, hfirst, hwrapRecv, hderefRecv,
            hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader, hpublic,
            hpublicBytes, htripleReal, hkeys, hwrapMk, hderefMk, hwrapKeys, hderefKeys] at hcall
          rcases realKeys with ⟨k1, k2, k3⟩
          cases had : serialization.concat_ad (alloc.vec.Vec.deref real.identity_ad) decoded.header with
          | fail e => simp [had] at hcall
          | div => simp [had] at hcall
          | ok realAd =>
            cases ha : tacenta_boundary.aead.decrypt k1 k2 k3
                (alloc.vec.Vec.deref decoded.ciphertext) (alloc.vec.Vec.deref realAd) with
            | fail e => simp [had, ha] at hcall
            | div => simp [had, ha] at hcall
            | ok result =>
              cases result with
              | Err aeadError =>
                refine ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
                  wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
                  realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk, wrappedMk,
                  (k1, k2, k3), wrappedKeys, realAd, aeadError, ?_⟩
                exact ⟨hdecode, hmessage, hreceive, .none rfl, hpeer, hfirst, hwrapRecv,
                  hderefRecv, hrandom,
                    (show real = next ∧ rng1 = rngNext from by simpa [had, ha] using hcall).2,
                    hcandidate, hsecond, hwrapSend, hderefSend,
                  by simpa using hbefore, by simpa using hheader, by simpa using hpublic,
                  by simpa using hpublicBytes, htripleReal, hkeys, hwrapMk, hderefMk,
                  hwrapKeys, hderefKeys, by simpa using had, ha⟩
              | Ok value1 =>
                cases hsend : tacenta_triple.State.sending_public realTripleCandidate with
                | fail e => simp [had, ha, hsend] at hcall
                | div => simp [had, ha, hsend] at hcall
                | ok candidatePublic' =>
                  cases hne : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
                      candidatePublic' before with
                  | fail e => simp [had, ha, hsend, hne] at hcall
                  | div => simp [had, ha, hsend, hne] at hcall
                  | ok b1 => cases b1 <;> simp [had, ha, hsend, hne] at hcall
        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          simp [hf, hdecode, hmessage, hreceive, hconverted, hpeer, hfirst, hwrapRecv, hderefRecv,
            hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader, hpublic,
            hpublicBytes, htripleReal, hkeys, hwrapMk, hderefMk, hwrapKeys, hderefKeys] at hcall
          rcases realKeys with ⟨k1, k2, k3⟩
          cases had : serialization.concat_ad (alloc.vec.Vec.deref real.identity_ad) decoded.header with
          | fail e => simp [had] at hcall
          | div => simp [had] at hcall
          | ok realAd =>
            cases ha : tacenta_boundary.aead.decrypt k1 k2 k3
                (alloc.vec.Vec.deref decoded.ciphertext) (alloc.vec.Vec.deref realAd) with
            | fail e => simp [had, ha] at hcall
            | div => simp [had, ha] at hcall
            | ok result =>
              cases result with
              | Err aeadError =>
                refine ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted, peer, recvSecret,
                  wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
                  realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk, wrappedMk,
                  (k1, k2, k3), wrappedKeys, realAd, aeadError, ?_⟩
                exact ⟨hdecode, hmessage, hreceive, .some output converted rfl hconverted,
                  hpeer, hfirst, hwrapRecv, hderefRecv, hrandom,
                    (show real = next ∧ rng1 = rngNext from by simpa [had, ha] using hcall).2,
                    hcandidate, hsecond,
                  hwrapSend, hderefSend, by simpa using hbefore, by simpa using hheader,
                  by simpa using hpublic, by simpa using hpublicBytes, htripleReal, hkeys,
                  hwrapMk, hderefMk, hwrapKeys, hderefKeys, by simpa using had, ha⟩
              | Ok value1 =>
                cases hsend : tacenta_triple.State.sending_public realTripleCandidate with
                | fail e => simp [had, ha, hsend] at hcall
                | div => simp [had, ha, hsend] at hcall
                | ok candidatePublic' =>
                  cases hne : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
                      candidatePublic' before with
                  | fail e => simp [had, ha, hsend, hne] at hcall
                  | div => simp [had, ha, hsend, hne] at hcall
                  | ok b1 => cases b1 <;> simp [had, ha, hsend, hne] at hcall

/-! Package the concrete AEAD-refusal inversion.  Keeping the complete call
trace in one value lets the later adapter consume the exact same witnesses as
the generated inversion, rather than reconstructing a branch by hand. -/
structure InitialRatchetAeadRefusalPrefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (next : lifecycle.Session) : Type where
  decoded : tacenta_wire.DecodedMessage
  m : tacenta_braid.Msg
  receivedEpoch : Std.U64
  output : Option tacenta_braid.Output
  braidCandidate : tacenta_braid.Braid
  sparseOutput : Option tacenta_spqr.Output
  peer : tacenta_boundary.dh.PublicKeyBytes
  recvSecret : Array Std.U8 32#usize
  wrappedRecv : zeroize.Zeroizing (Array Std.U8 32#usize)
  candidateBytes : Array Std.U8 32#usize
  rng1 : R
  candidatePrivate : tacenta_boundary.dh.PrivateKey
  sendSecret : Array Std.U8 32#usize
  wrappedSend : zeroize.Zeroizing (Array Std.U8 32#usize)
  before : Array Std.U8 32#usize
  realHeader : tacenta_triple.Header
  candidatePublic : tacenta_boundary.dh.PublicKeyBytes
  newPublicBytes : Array Std.U8 32#usize
  realTripleCandidate : tacenta_triple.State
  realMk : Array Std.U8 32#usize
  wrappedMk : zeroize.Zeroizing (Array Std.U8 32#usize)
  realKeys : Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize
  wrappedKeys : zeroize.Zeroizing
    (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize)
  realAd : alloc.vec.Vec Std.U8
  aeadError : Unit
  hdecode : tacenta_wire.decode_message message = ok (.Ok decoded)
  hmessage : lifecycle.msg_of decoded.header = ok m
  hreceive : tacenta_braid.Braid.receive real.braid m =
    ok (receivedEpoch, output, braidCandidate)
  hsparse : RealSparseConversion output sparseOutput
  hpeer : tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer
  hfirst : tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer =
    ok (some recvSecret)
  hwrapRecv : zeroize.Zeroizing.new
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv
  hderefRecv : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret
  hrandom : lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1)
  hrng : rng1 = rngNext
  hcandidate : tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate
  hsecond : tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer = ok (some sendSecret)
  hwrapSend : zeroize.Zeroizing.new
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret = ok wrappedSend
  hderefSend : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend = ok sendSecret
  hbefore : tacenta_triple.State.sending_public real.triple = ok before
  hheader : lifecycle.triple_header_of decoded.header = ok realHeader
  hpublic : tacenta_boundary.dh.PrivateKey.public_key candidatePrivate = ok candidatePublic
  hpublicBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic = ok newPublicBytes
  htriple : lifecycle.receive_with_eviction real.triple decoded.header realHeader
    recvSecret sendSecret newPublicBytes sparseOutput = ok (.Ok (realTripleCandidate, realMk))
  hkeys : tacenta_ratchet.message_keys realMk tacenta_ratchet.LabelSet.Tacenta = ok realKeys
  hwrapMk : zeroize.Zeroizing.new
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) realMk = ok wrappedMk
  hderefMk : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedMk = ok realMk
  hwrapKeys : zeroize.Zeroizing.new
    (TupleABC.Insts.ZeroizeZeroize
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
      (Array.Insts.ZeroizeZeroize 16#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) realKeys = ok wrappedKeys
  hderefKeys : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
    (TupleABC.Insts.ZeroizeZeroize
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
      (Array.Insts.ZeroizeZeroize 16#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) wrappedKeys = ok realKeys
  had : serialization.concat_ad (alloc.vec.Vec.deref real.identity_ad) decoded.header = ok realAd
  haead : tacenta_boundary.aead.decrypt realKeys.1 realKeys.2.1 realKeys.2.2
    (alloc.vec.Vec.deref decoded.ciphertext) (alloc.vec.Vec.deref realAd) = ok (.Err aeadError)

noncomputable def initial_ratchet_aead_refusal_prefix_of_result {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, next, rngNext)) :
    InitialRatchetAeadRefusalPrefix rngCore cryptoRng real message rng rngNext next :=
  Classical.choice (show Nonempty
    (InitialRatchetAeadRefusalPrefix rngCore cryptoRng real message rng rngNext next) from by
      obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
          wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
          realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk, wrappedMk,
          realKeys, wrappedKeys, realAd, aeadError, hdecode, hmessage, hreceive, hsparse, hpeer,
          hfirst, hwrapRecv, hderefRecv, hrandom, hrng, hcandidate, hsecond, hwrapSend, hderefSend,
          hbefore, hheader, hpublic, hpublicBytes, htriple, hkeys, hwrapMk, hderefMk,
          hwrapKeys, hderefKeys, had, haead⟩ :=
        decrypt_ratchet_aead_refusal_final_prefix rngCore cryptoRng hz32 hzKeys real message rng rngNext next hcall
      exact ⟨{
        decoded := decoded, m := m, receivedEpoch := receivedEpoch, output := output,
        braidCandidate := braidCandidate, sparseOutput := sparseOutput, peer := peer,
        recvSecret := recvSecret, wrappedRecv := wrappedRecv, candidateBytes := candidateBytes,
        rng1 := rng1, candidatePrivate := candidatePrivate, sendSecret := sendSecret,
        wrappedSend := wrappedSend, before := before, realHeader := realHeader,
        candidatePublic := candidatePublic, newPublicBytes := newPublicBytes,
        realTripleCandidate := realTripleCandidate, realMk := realMk, wrappedMk := wrappedMk,
        realKeys := realKeys, wrappedKeys := wrappedKeys, realAd := realAd, aeadError := aeadError,
        hdecode := hdecode, hmessage := hmessage, hreceive := hreceive, hsparse := hsparse,
        hpeer := hpeer, hfirst := hfirst, hwrapRecv := hwrapRecv, hderefRecv := hderefRecv,
        hrandom := hrandom, hrng := hrng, hcandidate := hcandidate, hsecond := hsecond,
        hwrapSend := hwrapSend, hderefSend := hderefSend, hbefore := hbefore,
        hheader := hheader, hpublic := hpublic, hpublicBytes := hpublicBytes,
        htriple := htriple, hkeys := hkeys, hwrapMk := hwrapMk, hderefMk := hderefMk,
        hwrapKeys := hwrapKeys, hderefKeys := hderefKeys, had := had, haead := haead }⟩)

def initial_ratchet_braid_evidence_of_aead_refusal_prefix
    {R : Type} {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {rngCore : rand_core_1.RngCore R} {cryptoRng : rand_core_1.CryptoRng R}
    {next : lifecycle.Session}
    (pref : InitialRatchetAeadRefusalPrefix rngCore cryptoRng real message rng rngNext next)
    (modelComposite : Model.CompositeHeader.Composite)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines pref.m
      (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hnext : Tacenta.SessionUnitBraidT3.StateRefines K pref.braidCandidate.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2) :
    BraidReceiveEvidence K view real model pref.decoded.header modelComposite :=
  { message := pref.m
    receivedEpoch := pref.receivedEpoch
    output := pref.output
    next := pref.braidCandidate
    sparseOutput := pref.sparseOutput
    hmessageCall := pref.hmessage
    hmessageRel := hmessageRel
    hreceive := pref.hreceive
    hsparse := pref.hsparse
    hnext := hnext }

theorem aead_refusal_prefix_trace_next
    {R : Type} {rngCore : rand_core_1.RngCore R} {cryptoRng : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
    {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {message : Slice Std.U8} {rng rngNext : R}
    {next : lifecycle.Session}
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (pref : InitialRatchetAeadRefusalPrefix rngCore cryptoRng real message rng rngNext next)
    (htrace : trace rng = oracle.draws)
    (draw : Model.Lifecycle.Key)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext)) :
    trace pref.rng1 = oracleNext.draws := by
  cases hd : oracle.draws with
  | nil =>
      simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hd] at hmodelDraw
  | cons head rest =>
      simp only [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hd,
        Option.some.injEq, Prod.mk.injEq] at hmodelDraw
      have hdrawHead : head = draw := hmodelDraw.1
      have hdrawRest : rest = oracleNext.draws := by
        have hrest := congrArg Model.Lifecycle.Oracle.draws hmodelDraw.2
        simpa using hrest
      have htraceDraw : trace rng = draw :: rest := by simpa [htrace, hd, hdrawHead]
      obtain ⟨candidateBytes, realRngNext, hrandomCall, hdrawBytes, htraceNext⟩ :=
        oracleOf.random32 rng draw rest htraceDraw
      have heq := pref.hrandom.symm.trans hrandomCall
      have hrngEq : realRngNext = pref.rng1 := by
        have hpair : (pref.candidateBytes, pref.rng1) = (candidateBytes, realRngNext) := by
          injection heq
        exact (Prod.mk.inj hpair).2.symm
      subst realRngNext
      simpa [hdrawRest] using htraceNext

theorem decrypt_ratchet_aead_refusal_from_prefix
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (modelComposite : Model.CompositeHeader.Composite)
    (next : lifecycle.Session)
    (pref : InitialRatchetAeadRefusalPrefix rngCore cryptoRng real message rng rngNext next)
    (htrace : trace rng = oracle.draws)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines pref.m
      (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hnext : Tacenta.SessionUnitBraidT3.StateRefines K pref.braidCandidate.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf pref.decoded.ciphertext))
    (hcomposite : CompositeRefines pref.decoded.header modelComposite)
    (draw modelDhOutRecv modelDhOutSend : Model.Lifecycle.Key)
    (modelTripleCandidate : Model.Triple.State) (modelMk : Model.Lifecycle.Key)
    (hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
      some modelDhOutRecv)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hmodelSecond : oracle.dhAgree draw modelComposite.dh = some modelDhOutSend)
    (hmodelPublic : oracle.dhPublic draw = arrayOf pref.newPublicBytes)
    (hmodelTriple : Model.Lifecycle.receiveWithEviction model.triple modelComposite
      (Model.Lifecycle.tripleHeaderOf modelComposite) modelDhOutRecv modelDhOutSend
      (oracle.dhPublic draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1) =
      .ok (modelTripleCandidate, modelMk))
    (hkeysValue : (arrayOf pref.realKeys.1, arrayOf pref.realKeys.2.1,
      arrayOf pref.realKeys.2.2) = Model.State.messageKeys modelMk .tacenta)
    (hrealAdValue : vecOf pref.realAd = Model.Messages.concatAd model.identityAd
      (Model.CompositeHeader.encode modelComposite)) :
    lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
        ok (.Err .Aead, real, rngNext) ∧
      StepRefines trace dh K
        (.Err .Aead, real, rngNext)
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  let evidence := initial_ratchet_braid_evidence_of_aead_refusal_prefix
    pref modelComposite hmessageRel hnext
  have htraceNext1 : trace pref.rng1 = oracleNext.draws :=
    aead_refusal_prefix_trace_next oracleOf pref htrace draw hmodelDraw
  have htraceNext : trace rngNext = oracleNext.draws := by
    simpa [pref.hrng] using htraceNext1
  have hrandomCall : lifecycle.random_secret rngCore cryptoRng rng =
      ok (pref.candidateBytes, rngNext) := by
    simpa [pref.hrng] using pref.hrandom
  have htripleReal : lifecycle.receive_with_eviction real.triple pref.decoded.header
      pref.realHeader pref.recvSecret pref.sendSecret pref.newPublicBytes pref.sparseOutput =
      ok (.Ok (pref.realTripleCandidate, pref.realMk)) := pref.htriple
  have hresult := decrypt_ratchet_aead_refusal_from_braid
    rngCore cryptoRng trace dh kem K view oracle oracleNext oracleOf real model message rng rngNext
    pref.decoded modelComposite pref.decoded.header evidence rfl pref.m pref.receivedEpoch
    pref.output pref.braidCandidate pref.sparseOutput pref.peer pref.recvSecret
    pref.sendSecret pref.candidateBytes pref.newPublicBytes pref.before pref.realMk pref.candidatePrivate
    pref.candidatePublic pref.realHeader pref.wrappedRecv pref.wrappedSend pref.wrappedMk
    pref.realTripleCandidate modelTripleCandidate modelMk draw modelDhOutRecv modelDhOutSend
    pref.realKeys pref.wrappedKeys pref.realAd pref.aeadError hrel htraceNext hready pref.hdecode
    hdecodeModel rfl rfl rfl rfl rfl pref.hpeer pref.hfirst
    pref.hwrapRecv pref.hderefRecv hrandomCall pref.hcandidate pref.hsecond pref.hwrapSend
    pref.hderefSend pref.hbefore pref.hheader pref.hpublic pref.hpublicBytes htripleReal
    hmodelFirst hmodelDraw hmodelSecond hmodelPublic hmodelTriple pref.hkeys hkeysValue
    pref.hwrapMk pref.hderefMk pref.hwrapKeys pref.hderefKeys pref.had hrealAdValue pref.haead
  simpa [evidence, initial_ratchet_braid_evidence_of_aead_refusal_prefix] using hresult

theorem decrypt_ratchet_success_aead_prefix {R : Type} (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext, next, rngNext)) :
    ∃ decoded m receivedEpoch output braidCandidate sparseOutput peer recvSecret wrappedRecv
      candidateBytes rng1 candidatePrivate sendSecret wrappedSend before realHeader candidatePublic
      newPublicBytes realTripleCandidate realMk wrappedMk realKeys wrappedKeys aeadPlaintext realAd,
      tacenta_wire.decode_message message = ok (.Ok decoded) ∧
      lifecycle.msg_of decoded.header = ok m ∧
      tacenta_braid.Braid.receive real.braid m = ok (receivedEpoch, output, braidCandidate) ∧
      RealSparseConversion output sparseOutput ∧
      tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer ∧
      tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer = ok (some recvSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret ∧
      lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1) ∧
      tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate ∧
      tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer = ok (some sendSecret) ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret = ok wrappedSend ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend = ok sendSecret ∧
      tacenta_triple.State.sending_public real.triple = ok before ∧
      lifecycle.triple_header_of decoded.header = ok realHeader ∧
      tacenta_boundary.dh.PrivateKey.public_key candidatePrivate = ok candidatePublic ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic = ok newPublicBytes ∧
      lifecycle.receive_with_eviction real.triple decoded.header realHeader
        recvSecret sendSecret newPublicBytes sparseOutput = ok (.Ok (realTripleCandidate, realMk)) ∧
      tacenta_ratchet.message_keys realMk tacenta_ratchet.LabelSet.Tacenta = ok realKeys ∧
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) realMk = ok wrappedMk ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedMk = ok realMk ∧
      zeroize.Zeroizing.new
        (TupleABC.Insts.ZeroizeZeroize
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 16#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) realKeys = ok wrappedKeys ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (TupleABC.Insts.ZeroizeZeroize
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
          (Array.Insts.ZeroizeZeroize 16#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) wrappedKeys = ok realKeys ∧
      serialization.concat_ad (alloc.vec.Vec.deref real.identity_ad) decoded.header = ok realAd ∧
      tacenta_boundary.aead.decrypt realKeys.1 realKeys.2.1 realKeys.2.2
        (alloc.vec.Vec.deref decoded.ciphertext) (alloc.vec.Vec.deref realAd) = ok (.Ok aeadPlaintext) := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer, recvSecret,
      wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
      realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk, wrappedMk,
      realKeys, wrappedKeys, hdecode, hmessage, hreceive, hsparse, hpeer, hfirst, hwrapRecv,
      hderefRecv, hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader,
      hpublic, hpublicBytes, htripleReal, hkeys, hwrapMk, hderefMk, hwrapKeys, hderefKeys⟩ :=
    decrypt_ratchet_success_keys_prefix rngCore cryptoRng hz32 hzKeys real message rng rngNext plaintext next hcall
  unfold lifecycle.Session.decrypt_ratchet at hcall
  cases hf : real.braid.failed with
  | fail e => simp [hf] at hcall
  | div => simp [hf] at hcall
  | ok b =>
    cases b with
    | true => simp_all
    | false =>
      cases output with
      | none =>
        cases hsparse with
        | none hout =>
          simp [hf, hdecode, hmessage, hreceive, hout, hpeer, hfirst, hwrapRecv, hderefRecv,
            hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader, hpublic,
            hpublicBytes, htripleReal, hkeys, hwrapMk, hderefMk, hwrapKeys, hderefKeys] at hcall
          cases had : serialization.concat_ad (alloc.vec.Vec.deref real.identity_ad) decoded.header with
          | fail e => rcases realKeys with ⟨k1, k2, k3⟩ <;> simp [had] at hcall
          | div => rcases realKeys with ⟨k1, k2, k3⟩ <;> simp [had] at hcall
          | ok realAd =>
            cases ha : tacenta_boundary.aead.decrypt realKeys.1 realKeys.2.1 realKeys.2.2
                (alloc.vec.Vec.deref decoded.ciphertext) (alloc.vec.Vec.deref realAd) with
            | fail e => rcases realKeys with ⟨k1, k2, k3⟩ <;> simp [had, ha] at hcall
            | div => rcases realKeys with ⟨k1, k2, k3⟩ <;> simp [had, ha] at hcall
            | ok result =>
              cases result with
              | Err e => rcases realKeys with ⟨k1, k2, k3⟩ <;> simp [had, ha] at hcall
              | Ok value1 =>
                exact ⟨decoded, m, receivedEpoch, none, braidCandidate, none, peer, recvSecret,
                  wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
                  realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk, wrappedMk,
                  realKeys, wrappedKeys, value1, realAd, hdecode, hmessage, hreceive, .none rfl, hpeer, hfirst,
                  hwrapRecv, hderefRecv, hrandom, hcandidate, hsecond, hwrapSend, hderefSend,
                  by simpa using hbefore, by simpa using hheader, by simpa using hpublic,
                  by simpa using hpublicBytes, htripleReal, hkeys, hwrapMk, hderefMk, hwrapKeys,
                  hderefKeys, by simpa using had, by simpa using ha⟩
        | some realOutput converted hout hconverted => simp_all
      | some output =>
        cases hsparse with
        | none hout => simp_all
        | some realOutput converted hout hconverted =>
          cases hout
          simp [hf, hdecode, hmessage, hreceive, hconverted, hpeer, hfirst, hwrapRecv, hderefRecv,
            hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore, hheader, hpublic,
            hpublicBytes, htripleReal, hkeys, hwrapMk, hderefMk, hwrapKeys, hderefKeys] at hcall
          cases had : serialization.concat_ad (alloc.vec.Vec.deref real.identity_ad) decoded.header with
          | fail e => rcases realKeys with ⟨k1, k2, k3⟩ <;> simp [had] at hcall
          | div => rcases realKeys with ⟨k1, k2, k3⟩ <;> simp [had] at hcall
          | ok realAd =>
            cases ha : tacenta_boundary.aead.decrypt realKeys.1 realKeys.2.1 realKeys.2.2
                (alloc.vec.Vec.deref decoded.ciphertext) (alloc.vec.Vec.deref realAd) with
            | fail e => rcases realKeys with ⟨k1, k2, k3⟩ <;> simp [had, ha] at hcall
            | div => rcases realKeys with ⟨k1, k2, k3⟩ <;> simp [had, ha] at hcall
            | ok result =>
              cases result with
              | Err e => rcases realKeys with ⟨k1, k2, k3⟩ <;> simp [had, ha] at hcall
              | Ok value1 =>
                exact ⟨decoded, m, receivedEpoch, some output, braidCandidate, some converted, peer, recvSecret,
                  wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret, wrappedSend, before,
                  realHeader, candidatePublic, newPublicBytes, realTripleCandidate, realMk, wrappedMk,
                  realKeys, wrappedKeys, value1, realAd, hdecode, hmessage, hreceive, .some output converted rfl hconverted,
                  hpeer, hfirst, hwrapRecv, hderefRecv, hrandom, hcandidate, hsecond, hwrapSend, hderefSend,
                  by simpa using hbefore, by simpa using hheader, by simpa using hpublic,
                  by simpa using hpublicBytes, htripleReal, hkeys, hwrapMk, hderefMk, hwrapKeys,
                  hderefKeys, by simpa using had, by simpa using ha⟩

theorem decrypt_ratchet_success_aead_bytes_from_oracle {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (dh : DhView) (kem : KemView) (trace : R → List Model.Lifecycle.Key)
    (oracle : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (key1 key2 : Array Std.U8 32#usize) (iv : Array Std.U8 16#usize)
    (ciphertext associatedData : Slice Std.U8)
    (aeadPlaintext : alloc.vec.Vec Std.U8) (modelCiphertext modelAd modelPlaintext : Bytes)
    (haead : tacenta_boundary.aead.decrypt key1 key2 iv ciphertext associatedData =
      ok (.Ok aeadPlaintext))
    (hcipher : sliceOf ciphertext = modelCiphertext)
    (had : sliceOf associatedData = modelAd)
    (hmodelAead : oracle.aeadOpen (arrayOf key1) (arrayOf key2) (arrayOf iv)
      modelCiphertext modelAd = some modelPlaintext) :
    vecOf aeadPlaintext = modelPlaintext := by
  have hreal := aead_open_success_refines rngCore cryptoRng dh kem trace oracle oracleOf
    key1 key2 iv ciphertext associatedData aeadPlaintext haead
  rw [hcipher, had] at hreal
  have heq := hmodelAead.symm.trans hreal
  cases heq
  rfl

/-- The model-byte correspondence identifies the concrete successful AEAD
plaintext before it is fed into the lifecycle result theorem. -/
theorem aead_success_plaintext_eq_of_model_bytes
    (aeadPlaintext plaintext : alloc.vec.Vec Std.U8)
    (modelPlaintext : Bytes)
    (haeadBytes : vecOf aeadPlaintext = modelPlaintext)
    (hplaintextBytes : vecOf plaintext = modelPlaintext) :
    aeadPlaintext = plaintext := by
  apply vecOf_injective
  exact haeadBytes.trans hplaintextBytes.symm

/-- Compose the oracle boundary and vector injectivity into the exact
plaintext fact consumed by the successful receive result adapter. -/
theorem decrypt_ratchet_success_aead_exact
    {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (dh : DhView) (kem : KemView) (trace : R → List Model.Lifecycle.Key)
    (oracle : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (key1 key2 : Array Std.U8 32#usize) (iv : Array Std.U8 16#usize)
    (ciphertext associatedData : Slice Std.U8)
    (aeadPlaintext plaintext : alloc.vec.Vec Std.U8)
    (modelCiphertext modelAd modelPlaintext : Bytes)
    (haead : tacenta_boundary.aead.decrypt key1 key2 iv ciphertext associatedData =
      ok (.Ok aeadPlaintext))
    (hcipher : sliceOf ciphertext = modelCiphertext)
    (had : sliceOf associatedData = modelAd)
    (hmodelAead : oracle.aeadOpen (arrayOf key1) (arrayOf key2) (arrayOf iv)
      modelCiphertext modelAd = some modelPlaintext)
    (hplaintextBytes : vecOf plaintext = modelPlaintext) :
    vecOf aeadPlaintext = modelPlaintext ∧ aeadPlaintext = plaintext := by
  have haeadBytes := decrypt_ratchet_success_aead_bytes_from_oracle
    rngCore cryptoRng dh kem trace oracle oracleOf key1 key2 iv ciphertext associatedData
    aeadPlaintext modelCiphertext modelAd modelPlaintext haead hcipher had hmodelAead
  exact ⟨haeadBytes, aead_success_plaintext_eq_of_model_bytes aeadPlaintext plaintext
    modelPlaintext haeadBytes hplaintextBytes⟩

/-! The successful receive adapter keeps the concrete commit visible.  It
reuses the same Braid evidence and primitive call facts as the refusal
adapters, but returns the exact post-AEAD session selected by the lifecycle's
ratchet-private branch.  The model relation and plaintext correspondence are
left to the next composition theorem. -/

theorem decrypt_ratchet_success_result_from_braid {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (dh : DhView) (K : Model.Braid.Kem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (decoded : tacenta_wire.DecodedMessage)
    (modelComposite : Model.CompositeHeader.Composite)
    (realComposite : tacenta_wire.Composite)
    (evidence : BraidReceiveEvidence K view real model realComposite modelComposite)
    (hrealComposite : realComposite = decoded.header)
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
    (realKeys : Array Std.U8 32#usize × Array Std.U8 32#usize ×
      Array Std.U8 16#usize)
    (wrappedKeys : zeroize.Zeroizing
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (realAd : alloc.vec.Vec Std.U8) (plaintext : alloc.vec.Vec Std.U8)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Ok decoded))
    (hmessageEq : realBraidMessage = evidence.message)
    (hreceivedEpochEq : receivedEpoch = evidence.receivedEpoch)
    (houtputEq : realOutput = evidence.output)
    (hcandidateEq : realBraidCandidate = evidence.next)
    (hsparseEq : realSparseOutput = evidence.sparseOutput)
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
    (hbeforeCall : tacenta_triple.State.sending_public real.triple = ok before)
    (hwrapSend : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret =
      ok wrappedSend)
    (hderefSend : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend =
      ok sendSecret)
    (hheaderCall : lifecycle.triple_header_of decoded.header = ok realHeader)
    (hpublicCall : tacenta_boundary.dh.PrivateKey.public_key candidatePrivate =
      ok candidatePublic)
    (hpublicBytesCall : tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic =
      ok newPublicBytes)
    (htripleReal : lifecycle.receive_with_eviction real.triple decoded.header realHeader
      recvSecret sendSecret newPublicBytes realSparseOutput =
        ok (.Ok (realTripleCandidate, realMk)))
    (hkeysCall : tacenta_ratchet.message_keys realMk tacenta_ratchet.LabelSet.Tacenta =
      ok realKeys)
    (hwrapMk : zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) realMk = ok wrappedMk)
    (hderefMk : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedMk =
      ok realMk)
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
    (haead : tacenta_boundary.aead.decrypt realKeys.1 realKeys.2.1 realKeys.2.2
      (alloc.vec.Vec.deref decoded.ciphertext) (alloc.vec.Vec.deref realAd) =
        ok (.Ok plaintext)) :
    lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext,
        { { real with triple := realTripleCandidate, braid := evidence.next } with
          ratchet_private :=
            if realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
              real.ratchet_private else candidatePrivate }, rngNext) := by
  subst realComposite
  have hmessageCall : lifecycle.msg_of decoded.header = ok realBraidMessage := by
    rw [hmessageEq]
    exact evidence.hmessageCall
  have hreceive : tacenta_braid.Braid.receive real.braid realBraidMessage =
      ok (receivedEpoch, realOutput, realBraidCandidate) := by
    rw [hmessageEq, hreceivedEpochEq, houtputEq, hcandidateEq]
    exact evidence.hreceive
  have hsparse : RealSparseConversion realOutput realSparseOutput := by
    rw [houtputEq, hsparseEq]
    exact evidence.hsparse
  have hrealReady := braid_failed_refines K real.braid model.braid hrel.braid
  have hmodelReady : Model.Lifecycle.braidFailed model.braid = false := by
    cases hb : model.braid <;>
      simp [Model.Lifecycle.agreementFailed, Model.Lifecycle.braidFailed, hb] at hready hrealReady ⊢
  rw [hmodelReady] at hrealReady
  rcases realKeys with ⟨encKey, macKey, ivKey⟩
  have hne : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      realTripleCandidate.classical.dhs_pub real.triple.classical.dhs_pub =
      ok (decide (realTripleCandidate.classical.dhs_pub ≠ real.triple.classical.dhs_pub)) := by
    obtain ⟨b, hb, hiff⟩ := Std.WP.spec_imp_exists
      (Tacenta.SessionUnitT3.array_ne_val
        realTripleCandidate.classical.dhs_pub real.triple.classical.dhs_pub)
    rw [hb]
    cases b <;> simp_all
  have hreal : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext,
        { { real with triple := realTripleCandidate, braid := realBraidCandidate } with
          ratchet_private :=
            if realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
              real.ratchet_private else candidatePrivate }, rngNext) := by
    unfold lifecycle.Session.decrypt_ratchet
    cases hsparse with
    | none hout =>
        by_cases hsame : realTripleCandidate.classical.dhs_pub = real.triple.classical.dhs_pub <;>
          (try rw [hsame] at hne ⊢) <;>
          simp [hne, hsame, hrealReady, hdecodeReal, hmessageCall, hreceive, hout, hpeerCall,
          hfirstCall, hwrapRecv, hderefRecv, hrandomCall, hcandidateCall,
          hsecondCall, hwrapSend, hderefSend, hbeforeCall, hheaderCall,
          hpublicCall, hpublicBytesCall, htripleReal, tacenta_triple.State.sending_public,
          tacenta_ratchet.State.sending_public, hwrapMk, hderefMk,
          hkeysCall, hwrapKeys, hderefKeys, hrealAd, haead]
    | some realSparse converted hout hconverted =>
        by_cases hsame : realTripleCandidate.classical.dhs_pub = real.triple.classical.dhs_pub <;>
          (try rw [hsame] at hne ⊢) <;>
          simp [hne, hsame, hrealReady, hdecodeReal, hmessageCall, hreceive, hout, hconverted,
          hpeerCall, hfirstCall, hwrapRecv, hderefRecv, hrandomCall,
          hcandidateCall, hsecondCall, hwrapSend, hderefSend, hbeforeCall,
          hheaderCall, hpublicCall, hpublicBytesCall, htripleReal,
          tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public, hwrapMk,
          hderefMk, hkeysCall, hwrapKeys, hderefKeys, hrealAd, haead]
  rw [← hcandidateEq]
  exact hreal

/-- The discharged Triple contracts turn an actual successful classical/SpQR
receive into the exact model receive result and its state/key witnesses. -/
theorem triple_receive_success_from_contracts
    (hmac : Tacenta.SessionUnitT3.HmacAgrees)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hzr : Tacenta.SessionUnitT3.ZeroizingRoundTrips)
    (hvr : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hz96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.SessionUnitSpqrT3.VecRetainAgrees)
    (happ : Tacenta.SessionUnitSpqrT3.VecAppendAgrees)
    (hrm : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees)
    (hzs : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hopt : Tacenta.SessionUnitSpqrT1.OptionCloneTotal)
    {s : tacenta_triple.State}
    {m : Model.Triple.State}
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (header : tacenta_triple.Header)
    (mh : Model.State.Header)
    (hheader : Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr mh)
    (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (hone : (m.classical.skipped.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n)).length ≤ 1)
    (hs : max m.classical.skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤ Usize.max)
    (hevents : m.classical.events + 1 < Std.U32.max)
    (hepoch : m.postQuantum.epoch + 1 < Std.U64.max)
    (hroom : m.postQuantum.chains.length + 2 < Usize.max)
    (hcb : ∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, output = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hskiproom : m.postQuantum.skipped.length + Model.SparseRatchet.maxSkip ≤ Usize.max)
    (hone2 : (m.postQuantum.skipped.filter (fun x => x.1 == header.epoch.val && x.2.1 == header.pq_n.val)).length ≤ 1)
    (hcounter : ∀ p ∈ m.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max)
    (realCandidate : tacenta_triple.State)
    (realKey : Array Std.U8 32#usize)
    (hcall : tacenta_triple.State.receive s header dh_out_recv dh_out_send
      new_dhs_pub output = ok (.Ok (realCandidate, realKey))) :
    ∃ modelCandidate modelKey,
      Model.Triple.receive m
          { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
          (Tacenta.SessionUnitTripleT3.keyOf dh_out_recv)
          (Tacenta.SessionUnitTripleT3.keyOf dh_out_send)
          (Tacenta.SessionUnitTripleT3.keyOf new_dhs_pub)
          (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) = some (modelCandidate, modelKey) ∧
      Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        realCandidate modelCandidate ∧
      Tacenta.SessionUnitTripleT3.keyOf realKey = modelKey := by
  have hpost := Tacenta.SessionUnitTripleT3.receive_refines_discharged
    hmac hkdf hzr hvr hz96 hz64 hret happ hrm hzs hopt hrel header mh hheader
    dh_out_recv dh_out_send new_dhs_pub output hone hs hevents hepoch hroom hcb hsb
    hnewb hskiproom hone2 hcounter
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists hpost
  rw [hcall] at hr
  cases hr
  obtain ⟨modelCandidate, modelKey, hmodel, hstate, hkey⟩ := hpost realCandidate realKey rfl
  exact ⟨modelCandidate, modelKey, hmodel, hstate, hkey⟩

/-! `receive_attempt` is only the generated lifecycle name for the same
    Triple receive.  Keep this adapter next to the contract theorem so retry
    callers can obtain the model success result without unfolding that wrapper
    themselves. -/
theorem concrete_receive_attempt_success_from_contracts
    (hmac : Tacenta.SessionUnitT3.HmacAgrees)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hzr : Tacenta.SessionUnitT3.ZeroizingRoundTrips)
    (hvr : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hz96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.SessionUnitSpqrT3.VecRetainAgrees)
    (happ : Tacenta.SessionUnitSpqrT3.VecAppendAgrees)
    (hrm : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees)
    (hzs : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hopt : Tacenta.SessionUnitSpqrT1.OptionCloneTotal)
    {s : tacenta_triple.State}
    {m : Model.Triple.State}
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (header : tacenta_triple.Header)
    (mh : Model.State.Header)
    (hheader : Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr mh)
    (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (hone : (m.classical.skipped.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n)).length ≤ 1)
    (hs : max m.classical.skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤ Usize.max)
    (hevents : m.classical.events + 1 < Std.U32.max)
    (hepoch : m.postQuantum.epoch + 1 < Std.U64.max)
    (hroom : m.postQuantum.chains.length + 2 < Usize.max)
    (hcb : ∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, output = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hskiproom : m.postQuantum.skipped.length + Model.SparseRatchet.maxSkip ≤ Usize.max)
    (hone2 : (m.postQuantum.skipped.filter (fun x => x.1 == header.epoch.val && x.2.1 == header.pq_n.val)).length ≤ 1)
    (hcounter : ∀ p ∈ m.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max)
    (realCandidate : tacenta_triple.State)
    (realKey : Array Std.U8 32#usize)
    (hcall : lifecycle.receive_attempt s header dh_out_recv dh_out_send new_dhs_pub output =
      ok (.Ok (realCandidate, realKey))) :
    ∃ modelCandidate modelKey,
      Model.Triple.receive m
          { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
          (Tacenta.SessionUnitTripleT3.keyOf dh_out_recv)
          (Tacenta.SessionUnitTripleT3.keyOf dh_out_send)
          (Tacenta.SessionUnitTripleT3.keyOf new_dhs_pub)
          (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) = some (modelCandidate, modelKey) ∧
      Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        realCandidate modelCandidate ∧
      Tacenta.SessionUnitTripleT3.keyOf realKey = modelKey := by
  apply triple_receive_success_from_contracts hmac hkdf hzr hvr hz96 hz64 hret happ hrm hzs hopt
    hrel header mh hheader dh_out_recv dh_out_send new_dhs_pub output hone hs hevents hepoch hroom
    hcb hsb hnewb hskiproom hone2 hcounter realCandidate realKey
  simpa [lifecycle.receive_attempt] using hcall

/-- Expose the generated retry entry: a successful lifecycle receive that is
not the direct attempt must first produce a full-store refusal and select a
retry half. -/
theorem concrete_receive_with_eviction_retry_case
    (state : tacenta_triple.State)
    (composite : tacenta_wire.Composite)
    (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (result : tacenta_triple.State × Array Std.U8 32#usize)
    (h : lifecycle.receive_with_eviction state composite header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok result))
    (hnot : lifecycle.receive_attempt state header dhOutRecv dhOutSend newDhsPub output ≠
      ok (.Ok result)) :
    ∃ reason half,
      lifecycle.receive_attempt state header dhOutRecv dhOutSend newDhsPub output =
        ok (.Err reason) ∧
      lifecycle.full_store reason = ok (some half) := by
  unfold lifecycle.receive_with_eviction at h
  cases ha : lifecycle.receive_attempt state header dhOutRecv dhOutSend newDhsPub output with
  | fail e => simp [ha] at h
  | div => simp [ha] at h
  | ok value =>
      cases value with
      | Err reason =>
          cases hs : lifecycle.full_store reason with
          | fail e => simp [ha, hs] at h
          | div => simp [ha, hs] at h
          | ok store =>
              cases hstore : store with
              | none => simp [ha, hs, hstore] at h
              | some half => exact ⟨reason, half, by simp [ha], by simp [hs, hstore]⟩
      | Ok value =>
          have hv : value = result := by simpa [ha] using h
          exact False.elim (hnot (by simp [ha, hv]))

/-! A successful generated lifecycle receive is either a direct Triple result
    or an actual full-store refusal that entered the retry loop. -/
theorem concrete_receive_with_eviction_success_cases
    (state : tacenta_triple.State)
    (composite : tacenta_wire.Composite)
    (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (result : tacenta_triple.State × Array Std.U8 32#usize)
    (h : lifecycle.receive_with_eviction state composite header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok result)) :
    (∃ direct,
      lifecycle.receive_attempt state header dhOutRecv dhOutSend newDhsPub output =
        ok (.Ok direct) ∧ direct = result) ∨
    (∃ reason half,
      lifecycle.receive_attempt state header dhOutRecv dhOutSend newDhsPub output =
        ok (.Err reason) ∧ lifecycle.full_store reason = ok (some half)) := by
  unfold lifecycle.receive_with_eviction at h
  cases ha : lifecycle.receive_attempt state header dhOutRecv dhOutSend newDhsPub output with
  | fail e => simp [ha] at h
  | div => simp [ha] at h
  | ok value =>
      cases value with
      | Err reason =>
          cases hs : lifecycle.full_store reason with
          | fail e => simp [ha, hs] at h
          | div => simp [ha, hs] at h
          | ok store =>
              cases hstore : store with
              | none => simp [ha, hs, hstore] at h
              | some half =>
                  exact Or.inr ⟨reason, half, by simp [ha], by simp [hs, hstore]⟩
      | Ok value =>
          have hv : value = result := by simpa [ha] using h
          exact Or.inl ⟨value, by simp [ha], hv⟩

/-- A successful direct Triple receive is returned unchanged by the generated
lifecycle wrapper; the eviction loop is entered only after an error. -/
theorem concrete_receive_with_eviction_of_receive
    (state : tacenta_triple.State)
    (composite : tacenta_wire.Composite)
    (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (result : tacenta_triple.State × Array Std.U8 32#usize)
    (hcall : tacenta_triple.State.receive state header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok result)) :
    lifecycle.receive_with_eviction state composite header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok result) := by
  unfold lifecycle.receive_with_eviction lifecycle.receive_attempt
  rw [hcall]
  simp

/-! The first inner eviction loop chooses an index by scanning the skipped-key
vector.  This safety lemma is the concrete fact needed before relating that
index to the model's `oldestSkipped?`; it keeps the scan's termination and
in-range result visible instead of treating the whole eviction helper as an
opaque successful call. -/
theorem concrete_evict_oldest_scan_bound
    (v : alloc.vec.Vec tacenta_ratchet.SkippedKey)
    (oldest i : Std.Usize)
    (hi : i.val ≤ v.val.length)
    (ho : oldest.val < v.val.length) :
    tacenta_ratchet.State.evict_oldest_loop0_loop0 v oldest i ⦃ fun r =>
      r.val < v.val.length ⦄ := by
  unfold tacenta_ratchet.State.evict_oldest_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun x => v.val.length - x.2.val)
    (inv := fun x => x.2.val ≤ v.val.length ∧ x.1.val < v.val.length)
  · rintro ⟨oldest1, i1⟩ ⟨hi1, ho1⟩
    simp only at hi1 ho1 ⊢
    simp only [tacenta_ratchet.State.evict_oldest_loop0_loop0.body]
    by_cases hlt : i1.val < v.val.length
    · step*
      by_cases hs : sk.stored_at < sk1.stored_at
      · simp [hs]
        repeat' (first | simp only [Aeneas.Std.WP.spec_ok] | step | split)
        all_goals simp_all
        all_goals try omega
      · simp [hs]
        repeat' (first | simp only [Aeneas.Std.WP.spec_ok] | step | split)
        all_goals simp_all
        all_goals try omega
    · have hge : v.val.length ≤ i1.val := by omega
      simp [alloc.vec.Vec.len, hge, hlt]
      exact ho1
  · exact ⟨hi, ho⟩

/-! The same scan also preserves the semantic minimum.  The postcondition is
stated with explicit index proofs because `SkippedKey` has no arbitrary default
value: every comparison is against an element known to be in the vector. -/
theorem concrete_evict_oldest_scan_min
    (v : alloc.vec.Vec tacenta_ratchet.SkippedKey)
    (oldest i : Std.Usize)
    (hi : i.val ≤ v.val.length)
    (ho : oldest.val < v.val.length)
    (hmin : ∀ (j : Std.Usize) (hj : j.val < i.val)
      (hjlen : j.val < v.val.length),
      (v.val[oldest.val]'ho).stored_at.val ≤
        (v.val[j.val]'hjlen).stored_at.val) :
    tacenta_ratchet.State.evict_oldest_loop0_loop0 v oldest i ⦃ fun r =>
      r.val < v.val.length ∧
      ∀ (hr : r.val < v.val.length) (j : Std.Usize)
        (hj : j.val < v.val.length),
        (v.val[r.val]'hr).stored_at.val ≤
          (v.val[j.val]'hj).stored_at.val ⦄ := by
  unfold tacenta_ratchet.State.evict_oldest_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun x => v.val.length - x.2.val)
    (inv := fun x => x.2.val ≤ v.val.length ∧ x.1.val < v.val.length ∧
      ∀ (hc : x.1.val < v.val.length) (j : Std.Usize)
        (hj : j.val < x.2.val) (hjlen : j.val < v.val.length),
        (v.val[x.1.val]'hc).stored_at.val ≤
          (v.val[j.val]'hjlen).stored_at.val)
  · rintro ⟨oldest1, i1⟩ ⟨hi1, ho1, hmin1⟩
    simp only at hi1 ho1 hmin1 ⊢
    simp only [tacenta_ratchet.State.evict_oldest_loop0_loop0.body]
    by_cases hlt : i1.val < v.val.length
    · step*
      by_cases hs : sk.stored_at < sk1.stored_at
      · simp [hs]
        repeat' (first | simp only [Aeneas.Std.WP.spec_ok] | step | split)
        all_goals simp_all
        all_goals try omega
        all_goals
          constructor
          · intro (j : Std.Usize) hj hjlen
            by_cases hji : j.val < i1.val
            · have hold := hmin1 j hji hjlen
              have hnewold : (v.val[i1.val]'(by omega)).stored_at.val ≤
                  (v.val[oldest1.val]'ho1).stored_at.val := Nat.le_of_lt hs
              exact Nat.le_trans hnewold hold
            · have hjeq : j.val = i1.val := by omega
              simpa [hjeq] using
                (Nat.le_refl ((v.val[i1.val]'(by omega)).stored_at.val))
          · omega
      · simp [hs]
        repeat' (first | simp only [Aeneas.Std.WP.spec_ok] | step | split)
        all_goals simp_all
        all_goals try omega
        all_goals
          constructor
          · intro (j : Std.Usize) hj hjlen
            by_cases hji : j.val < i1.val
            · exact hmin1 j hji hjlen
            · have hjeq : j.val = i1.val := by omega
              simpa [hjeq] using hs
          · omega
    · have hge : v.val.length ≤ i1.val := by omega
      simp [alloc.vec.Vec.len, hge, hlt]
      constructor
      · exact ho1
      · intro _hr (j : Std.Usize) hj
        exact hmin1 ho1 j (by omega) hj
  · constructor
    · exact hi
    · constructor
      · exact ho
      · intro (hc : oldest.val < v.val.length) (j : Std.Usize) hj hjlen
        exact hmin j hj hjlen

/-! The same induction records the tie rule: when a candidate has the same
    clock as the current minimum, the generated scan keeps the earlier index.
    Thus the returned minimum is the first minimum, which is the fact needed
    to match `oldestSkipped?` rather than merely its clock value. -/
theorem concrete_evict_oldest_scan_first
    (v : alloc.vec.Vec tacenta_ratchet.SkippedKey)
    (oldest i : Std.Usize)
    (hi : i.val ≤ v.val.length)
    (ho : oldest.val < v.val.length)
    (hmin : ∀ (j : Std.Usize) (hj : j.val < i.val)
      (hjlen : j.val < v.val.length),
      (v.val[oldest.val]'ho).stored_at.val ≤
        (v.val[j.val]'hjlen).stored_at.val)
    (hfirst : ∀ (hc : oldest.val < v.val.length) (j : Std.Usize)
      (hj : j.val < oldest.val) (hjlen : j.val < v.val.length),
      (v.val[oldest.val]'hc).stored_at.val <
        (v.val[j.val]'hjlen).stored_at.val) :
    tacenta_ratchet.State.evict_oldest_loop0_loop0 v oldest i ⦃ fun r =>
      r.val < v.val.length ∧
      (∀ (hr : r.val < v.val.length) (j : Std.Usize)
        (hj : j.val < v.val.length) (hjlen : j.val < v.val.length),
        (v.val[r.val]'hr).stored_at.val ≤
          (v.val[j.val]'hjlen).stored_at.val) ∧
      (∀ (hr : r.val < v.val.length) (j : Std.Usize)
        (hj : j.val < r.val) (hjlen : j.val < v.val.length),
        (v.val[r.val]'hr).stored_at.val <
          (v.val[j.val]'hjlen).stored_at.val) ⦄ := by
  unfold tacenta_ratchet.State.evict_oldest_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun x => v.val.length - x.2.val)
    (inv := fun x =>
      x.2.val ≤ v.val.length ∧
      x.1.val < v.val.length ∧
      (∀ (hc : x.1.val < v.val.length) (j : Std.Usize) (hj : j.val < x.2.val)
        (hjlen : j.val < v.val.length),
        (v.val[x.1.val]'hc).stored_at.val ≤
          (v.val[j.val]'hjlen).stored_at.val) ∧
      (∀ (hc : x.1.val < v.val.length) (j : Std.Usize)
        (hj : j.val < x.1.val) (hjlen : j.val < v.val.length),
        (v.val[x.1.val]'hc).stored_at.val <
          (v.val[j.val]'hjlen).stored_at.val))
  · rintro ⟨oldest1, i1⟩ ⟨hi1, ho1, hmin1, hfirst1⟩
    simp only at hi1 ho1 hmin1 hfirst1 ⊢
    simp only [tacenta_ratchet.State.evict_oldest_loop0_loop0.body]
    by_cases hlt : i1.val < v.val.length
    · step*
      by_cases hs : sk.stored_at < sk1.stored_at
      · simp [hs]
        repeat' (first | simp only [Aeneas.Std.WP.spec_ok] | step | split)
        all_goals simp_all
        all_goals try omega
        all_goals
          refine ⟨?_, ?_, ?_⟩
          · intro (j : Std.Usize) hj hjlen
            by_cases hji : j.val < oldest1.val
            · have hold := hfirst1 j hji hjlen
              have hnewold : (v.val[i1.val]'(by omega)).stored_at.val <
                  (v.val[oldest1.val]'ho1).stored_at.val := by
                simpa using hs
              exact Nat.le_of_lt (Nat.lt_trans hnewold hold)
            · by_cases hji1 : j.val < i1.val
              · have hold : (v.val[oldest1.val]'ho1).stored_at.val ≤
                    (v.val[j.val]'hjlen).stored_at.val :=
                  hmin1 j hji1 hjlen
                have hnewold : (v.val[i1.val]'(by omega)).stored_at.val ≤
                    (v.val[oldest1.val]'ho1).stored_at.val := by
                  exact Nat.le_of_lt (by simpa using hs)
                exact Nat.le_trans hnewold hold
              · have hjeq : j.val = i1.val := by omega
                simpa [hjeq] using
                  (Nat.le_refl ((v.val[i1.val]'(by omega)).stored_at.val))
          · intro (j : Std.Usize) hj hjlen
            by_cases hji : j.val < oldest1.val
            · have hold := hfirst1 j hji hjlen
              have hnewold : (v.val[i1.val]'(by omega)).stored_at.val <
                  (v.val[oldest1.val]'ho1).stored_at.val := by
                simpa using hs
              exact Nat.lt_trans hnewold hold
            · have hnewold : (v.val[i1.val]'(by omega)).stored_at.val <
                  (v.val[oldest1.val]'ho1).stored_at.val := by
                simpa using hs
              have hold : (v.val[oldest1.val]'ho1).stored_at.val ≤
                  (v.val[j.val]'hjlen).stored_at.val :=
                hmin1 j hj hjlen
              exact Nat.lt_of_lt_of_le hnewold hold
          · omega
      · simp [hs]
        repeat' (first | simp only [Aeneas.Std.WP.spec_ok] | step | split)
        all_goals simp_all
        all_goals try omega
        all_goals
          constructor
          · intro (j : Std.Usize) hj hjlen
            by_cases hji : j.val < i1.val
            · exact hmin1 j hji hjlen
            · have hjeq : j.val = i1.val := by omega
              simpa [hjeq] using hs
          · omega
    · have hge : v.val.length ≤ i1.val := by omega
      simp [alloc.vec.Vec.len, hge, hlt]
      refine ⟨ho1, ?_, hfirst1⟩
      intro _hc j hjlen
      exact hmin1 (by omega) j (by omega) hjlen
  · refine ⟨hi, ho, ?_, ?_⟩
    · intro _hc j hj hjlen
      exact hmin j hj hjlen
    · intro hc j hj hjlen
      exact hfirst hc j hj hjlen

/-! Once the scan postcondition is viewed through `StateR`, its returned
    index is exactly the model selector.  The small width premise is the
    concrete vector bound needed to reify a model list index as `Usize`; the
    ratchet headroom invariant supplies it at the outer eviction call. -/
theorem concrete_scan_selector_refines_oldest
    (s : tacenta_ratchet.State) (m : Model.State.State)
    (hrel : Tacenta.SessionUnitT3.StateR s m)
    (r : Std.Usize)
    (hwidth : s.skipped.val.length ≤ UScalar.cMax UScalarTy.Usize)
    (hr : r.val < s.skipped.val.length)
    (hmin : ∀ (hr : r.val < s.skipped.val.length) (j : Std.Usize)
      (hj : j.val < s.skipped.val.length) (hjlen : j.val < s.skipped.val.length),
      (s.skipped.val[r.val]'hr).stored_at.val ≤
        (s.skipped.val[j.val]'hjlen).stored_at.val)
    (hfirst : ∀ (hr : r.val < s.skipped.val.length) (j : Std.Usize)
      (hj : j.val < r.val) (hjlen : j.val < s.skipped.val.length),
      (s.skipped.val[r.val]'hr).stored_at.val <
        (s.skipped.val[j.val]'hjlen).stored_at.val) :
    Model.Ratchet.oldestSkipped? m.skipped =
      some ((s.skipped.val.map Tacenta.SessionUnitT3.skippedOf)[r.val]'
        (by simpa [List.length_map] using hr)) := by
  rw [← hrel.skipped]
  apply Model.Ratchet.oldestSkipped?_eq_of_index_first_min
    (hi := by simpa [List.length_map] using hr)
  · intro j hj
    let ju : Std.Usize := UScalar.ofNat j (by omega)
    have hju : ju.val = j := by simp [ju]
    have hjlen : j < s.skipped.val.length := by omega
    have hju_lt : ju.val < r.val := by simpa [hju] using hj
    have hju_len : ju.val < s.skipped.val.length := by simpa [hju] using hjlen
    simpa [Tacenta.SessionUnitT3.skippedOf, hju] using
      hfirst hr ju hju_lt hju_len
  · intro j hj hjlen
    have hjlen' : j < s.skipped.val.length := by
      simpa [List.length_map] using hjlen
    let ju : Std.Usize := UScalar.ofNat j (by omega)
    have hju : ju.val = j := by simp [ju]
    have hju_len : ju.val < s.skipped.val.length := by simpa [hju] using hjlen'
    have hju_ge : r.val ≤ ju.val := by simpa [hju] using hj
    simpa [Tacenta.SessionUnitT3.skippedOf, hju] using
      hmin hr ju (by omega) hju_len

/-! The opaque removal boundary now has the exact list-level shape needed by
the model bridge: after `remove_skipped_at` returns, mapping the resulting
vector is the original mapped skipped list with the selected index erased. -/
theorem concrete_remove_skipped_at_map_eraseIdx
    (hvr : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    (v : alloc.vec.Vec tacenta_ratchet.SkippedKey) (i : Std.Usize)
    (hi : i.val < v.val.length) :
    ∃ r, tacenta_ratchet.remove_skipped_at v i = ok r ∧
      r.2.val.map Tacenta.SessionUnitT3.skippedOf =
        (v.val.map Tacenta.SessionUnitT3.skippedOf).eraseIdx i.val := by
  obtain ⟨r, hcall, _, hv⟩ := hvr Global v i hi
  refine ⟨r, hcall, ?_⟩
  rw [hv, Tacenta.SessionUnitT3.map_eraseIdx]

/-! The concrete deletion boundary now composes with the model's first-match
erasure rule.  The first-occurrence premise is explicit: this theorem does
not silently identify an arbitrary vector index with the model's selector. -/
theorem concrete_remove_skipped_at_matches_eraseFirst
    (hvr : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    (v : alloc.vec.Vec tacenta_ratchet.SkippedKey) (i : Std.Usize)
    (target : Model.State.Key × Nat × Nat × Model.State.Key)
    (hi : i.val < v.val.length)
    (hentry : (v.val.map Tacenta.SessionUnitT3.skippedOf)[i.val]? = some target)
    (hfirst : ∀ j, j < i.val →
      (v.val.map Tacenta.SessionUnitT3.skippedOf)[j]? ≠ some target) :
    ∃ r, tacenta_ratchet.remove_skipped_at v i = ok r ∧
      r.2.val.map Tacenta.SessionUnitT3.skippedOf =
        Model.Ratchet.eraseFirstSkipped target
          (v.val.map Tacenta.SessionUnitT3.skippedOf) := by
  obtain ⟨r, hcall, hmap⟩ :=
    concrete_remove_skipped_at_map_eraseIdx hvr v i hi
  have hmodel := Model.Ratchet.eraseFirstSkipped_eq_eraseIdx_of_first
    (v.val.map Tacenta.SessionUnitT3.skippedOf) target i.val
    (by simpa using hi) hentry hfirst
  exact ⟨r, hcall, hmap.trans hmodel.symm⟩

/-! The concrete deletion and the selector bridge compose into one ratchet
    state step.  This is the reusable body of the classical outer eviction
    induction; it leaves the loop fuel and count arithmetic to that induction.
    Every state field other than the mapped skipped store is carried by the
    existing `StateR` relation. -/
theorem concrete_remove_oldest_state_refines
    (hvr : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    {s : tacenta_ratchet.State} {m : Model.State.State}
    (hrel : Tacenta.SessionUnitT3.StateR s m)
    (i : Std.Usize) (target : Model.State.Key × Nat × Nat × Model.State.Key)
    (hi : i.val < s.skipped.val.length)
    (hentry : (s.skipped.val.map Tacenta.SessionUnitT3.skippedOf)[i.val]? = some target)
    (hfirst : ∀ j, j < i.val →
      (s.skipped.val.map Tacenta.SessionUnitT3.skippedOf)[j]? ≠ some target) :
    ∃ discarded v,
      tacenta_ratchet.remove_skipped_at s.skipped i = ok (discarded, v) ∧
      Tacenta.SessionUnitT3.StateR { s with skipped := v }
        { m with skipped := Model.Ratchet.eraseFirstSkipped target m.skipped } := by
  obtain ⟨r, hcall, hmap⟩ := concrete_remove_skipped_at_matches_eraseFirst
    hvr s.skipped i target hi hentry hfirst
  rcases r with ⟨discarded, v⟩
  refine ⟨discarded, v, hcall, ?_⟩
  refine ⟨hrel.dhs_pub, hrel.dhr_pub, hrel.rk, hrel.cks, hrel.ckr,
    hrel.ns, hrel.nr, hrel.pn, ?_, hrel.events, hrel.labels⟩
  rw [hmap, ← hrel.skipped]

/-! A scan certificate can now be consumed in one step.  The certificate is
the exact global-minimum and strict-before-index postcondition produced by
`concrete_evict_oldest_scan_first`; this theorem turns it into the mapped
model entry and then applies the deletion bridge.  The outer fuel induction
still supplies the loop arithmetic and the recursive model state. -/
theorem concrete_classical_evict_one_step
    (hvr : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    {s : tacenta_ratchet.State} {m : Model.State.State}
    (hrel : Tacenta.SessionUnitT3.StateR s m)
    (oldest : Std.Usize)
    (hwidth : s.skipped.val.length ≤ UScalar.cMax UScalarTy.Usize)
    (hr : oldest.val < s.skipped.val.length)
    (hmin : ∀ (hr0 : oldest.val < s.skipped.val.length) (j : Std.Usize)
      (hj : j.val < s.skipped.val.length)
      (hjlen : j.val < s.skipped.val.length),
      (s.skipped.val[oldest.val]'hr).stored_at.val ≤
        (s.skipped.val[j.val]'hjlen).stored_at.val)
    (hfirst : ∀ (hr0 : oldest.val < s.skipped.val.length) (j : Std.Usize)
      (hj : j.val < oldest.val) (hjlen : j.val < s.skipped.val.length),
      (s.skipped.val[oldest.val]'hr).stored_at.val <
        (s.skipped.val[j.val]'hjlen).stored_at.val) :
    ∃ target discarded v,
      target = ((s.skipped.val.map Tacenta.SessionUnitT3.skippedOf)[oldest.val]'
        (by simpa [List.length_map] using hr)) ∧
      tacenta_ratchet.remove_skipped_at s.skipped oldest = ok (discarded, v) ∧
      Tacenta.SessionUnitT3.StateR { s with skipped := v }
        { m with skipped := Model.Ratchet.eraseFirstSkipped target m.skipped } := by
  let mapped := s.skipped.val.map Tacenta.SessionUnitT3.skippedOf
  let target := Tacenta.SessionUnitT3.skippedOf (s.skipped.val[oldest.val]'hr)
  have htarget : target = mapped[oldest.val]'
      (by simpa [mapped, List.length_map] using hr) := by
    simp [target, mapped, List.getElem_map]
  have hsel : Model.Ratchet.oldestSkipped? m.skipped = some target := by
    rw [htarget]
    apply concrete_scan_selector_refines_oldest s m hrel oldest hwidth hr hmin hfirst
  have hentry : mapped[oldest.val]? = some target := by
    rw [List.getElem?_eq_getElem (by simpa [mapped, List.length_map] using hr)]
    simp [mapped, target, List.getElem_map]
  have hfirst_model : ∀ j, j < oldest.val → mapped[j]? ≠ some target := by
    intro j hj hEq
    have hjlen : j < mapped.length := by
      simpa [mapped, List.length_map] using (lt_trans hj hr)
    let ju : Std.Usize := UScalar.ofNat j (by omega)
    have hju : ju.val = j := by simp [ju]
    have hju_lt : ju.val < oldest.val := by simpa [hju] using hj
    have hjlen' : j < s.skipped.val.length := by
      simpa [mapped, List.length_map] using hjlen
    have hju_len : ju.val < s.skipped.val.length := by
      simpa [ju, hju] using hjlen'
    have hc := hfirst hr ju hju_lt hju_len
    have hEq' : mapped[j] = target := by
      rw [List.getElem?_eq_getElem hjlen] at hEq
      exact Option.some.inj hEq
    have heqclock := congrArg (fun x => x.2.2.1) hEq'
    have hEqClock : (s.skipped.val[oldest.val]'hr).stored_at.val =
        (s.skipped.val[ju.val]'hju_len).stored_at.val := by
      simpa [mapped, target, Tacenta.SessionUnitT3.skippedOf, ju, hju,
        List.getElem_map] using heqclock.symm
    omega
  obtain ⟨discarded, v, hcall, hstate⟩ := concrete_remove_oldest_state_refines
    hvr hrel oldest target hr hentry hfirst_model
  exact ⟨target, discarded, v, htarget, hcall, hstate⟩

/-! The one-entry bridge also exposes the model selector and packages the
result as the model's one-fuel `evictOldest` state.  This is the semantic
step consumed by the arbitrary-fuel StateR invariant; callers still provide
the scan certificates that establish the concrete index and tie rule. -/
theorem concrete_classical_evict_one_step_model
    (hvr : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    {s : tacenta_ratchet.State} {m : Model.State.State}
    (hrel : Tacenta.SessionUnitT3.StateR s m)
    (oldest : Std.Usize)
    (hwidth : s.skipped.val.length ≤ UScalar.cMax UScalarTy.Usize)
    (hr : oldest.val < s.skipped.val.length)
    (hmin : ∀ (hr : oldest.val < s.skipped.val.length) (j : Std.Usize)
      (hj : j.val < s.skipped.val.length) (hjlen : j.val < s.skipped.val.length),
      (s.skipped.val[oldest.val]'hr).stored_at.val ≤
        (s.skipped.val[j.val]'hjlen).stored_at.val)
    (hfirst : ∀ (hr : oldest.val < s.skipped.val.length) (j : Std.Usize)
      (hj : j.val < oldest.val) (hjlen : j.val < s.skipped.val.length),
      (s.skipped.val[oldest.val]'hr).stored_at.val <
        (s.skipped.val[j.val]'hjlen).stored_at.val) :
    ∃ target discarded v,
      target = ((s.skipped.val.map Tacenta.SessionUnitT3.skippedOf)[oldest.val]'
        (by simpa [List.length_map] using hr)) ∧
      Model.Ratchet.oldestSkipped? m.skipped = some target ∧
      tacenta_ratchet.remove_skipped_at s.skipped oldest = ok (discarded, v) ∧
      Tacenta.SessionUnitT3.StateR { s with skipped := v }
        (Model.Ratchet.evictOldest m 1).1 := by
  have hsel := concrete_scan_selector_refines_oldest s m hrel oldest hwidth hr hmin hfirst
  obtain ⟨target, discarded, v, htarget, hcall, hstate⟩ :=
    concrete_classical_evict_one_step hvr hrel oldest hwidth hr hmin hfirst
  have hsel' : Model.Ratchet.oldestSkipped? m.skipped = some target := by
    simpa [htarget] using hsel
  have hevict := Model.Ratchet.evictOldest_one_some_state m target hsel'
  refine ⟨target, discarded, v, htarget, hsel', hcall, ?_⟩
  rw [hevict]
  exact hstate

/-! The generated outer body consumes exactly one classical eviction: once the
scan and removal boundaries return, it increments the `evicted` fuel and
continues with the updated state.  This is the concrete body fact used by the
fuel-decreasing loop proof below. -/
theorem concrete_classical_evict_body_one
    (s : tacenta_ratchet.State) (oldest : Std.Usize)
    (discarded : Array Std.U8 32#usize)
    (v : alloc.vec.Vec tacenta_ratchet.SkippedKey)
    (hscan : tacenta_ratchet.State.evict_oldest_loop0_loop0
      s.skipped 0#usize 1#usize = ok oldest)
    (hremove : tacenta_ratchet.remove_skipped_at s.skipped oldest =
      ok (discarded, v))
    (hlen : s.skipped.val.length ≠ 0) :
    tacenta_ratchet.State.evict_oldest_loop0.body 1#usize s 0#usize ⦃ fun r =>
      r = ControlFlow.cont ({ s with skipped := v }, 1#usize) ⦄ := by
  unfold tacenta_ratchet.State.evict_oldest_loop0.body
  have hlenU : alloc.vec.Vec.len s.skipped ≠ 0#usize := by
    intro hz
    apply hlen
    simpa [alloc.vec.Vec.len] using congrArg UScalar.val hz
  have hlenU' : (alloc.vec.Vec.len s.skipped != 0#usize) = true := by
    simp [bne_iff_ne, hlenU]
  simp [hlenU', hscan, hremove]
  step with Usize.add_spec
    (by scalar_tac : (0#usize).val + (1#usize).val ≤ Usize.max)
  have hevicted : evicted1 = 1#usize :=
    UScalar.eq_of_val_eq (by simpa using evicted1_post)
  simp [hevicted]

/-! The same generated-body fact with symbolic fuel and counter.  Keeping the
successful addition as an explicit result hypothesis lets the outer-loop
induction reuse this theorem without unfolding the fallible `Usize` addition
at every step. -/
theorem concrete_classical_evict_body_step
    (s : tacenta_ratchet.State) (count evicted evicted1 oldest : Std.Usize)
    (discarded : Array Std.U8 32#usize)
    (v : alloc.vec.Vec tacenta_ratchet.SkippedKey)
    (hcount : evicted.val < count.val)
    (hscan : tacenta_ratchet.State.evict_oldest_loop0_loop0
      s.skipped 0#usize 1#usize = ok oldest)
    (hremove : tacenta_ratchet.remove_skipped_at s.skipped oldest =
      ok (discarded, v))
    (hadd : evicted + 1#usize = ok evicted1)
    (hlen : s.skipped.val.length ≠ 0) :
    tacenta_ratchet.State.evict_oldest_loop0.body count s evicted
      ⦃ fun r => r = ControlFlow.cont ({ s with skipped := v }, evicted1) ⦄ := by
  unfold tacenta_ratchet.State.evict_oldest_loop0.body
  have hlenU : alloc.vec.Vec.len s.skipped ≠ 0#usize := by
    intro hz
    apply hlen
    simpa [alloc.vec.Vec.len] using congrArg UScalar.val hz
  have hlenU' : (alloc.vec.Vec.len s.skipped != 0#usize) = true := by
    simp [bne_iff_ne, hlenU]
  simp [hcount, hlenU', hscan, hremove, hadd]

theorem concrete_classical_evict_body_empty
    (s : tacenta_ratchet.State) (count evicted : Std.Usize)
    (hcount : evicted.val < count.val)
    (hlen : s.skipped.val.length = 0) :
    tacenta_ratchet.State.evict_oldest_loop0.body count s evicted ⦃ fun r =>
      r = ControlFlow.done (evicted, s) ⦄ := by
  unfold tacenta_ratchet.State.evict_oldest_loop0.body
  have hlenU : alloc.vec.Vec.len s.skipped = 0#usize := by
    simp [alloc.vec.Vec.len, hlen]
    rfl
  simp [hcount, hlenU]

/-! With one unit of fuel, the outer loop consumes the certified scan/removal
and then terminates on its second body turn.  This is the first bounded case
of the arbitrary-fuel invariant: the first turn performs one eviction, and
the second sees the empty skipped-key vector. -/
theorem concrete_classical_evict_outer_one
    (s : tacenta_ratchet.State) (oldest : Std.Usize)
    (discarded : Array Std.U8 32#usize)
    (v : alloc.vec.Vec tacenta_ratchet.SkippedKey)
    (hscan : tacenta_ratchet.State.evict_oldest_loop0_loop0
      s.skipped 0#usize 1#usize = ok oldest)
    (hremove : tacenta_ratchet.remove_skipped_at s.skipped oldest =
      ok (discarded, v))
    (hlen : s.skipped.val.length ≠ 0) :
    tacenta_ratchet.State.evict_oldest_loop0 s 1#usize 0#usize
      ⦃ fun r => r = (1#usize, { s with skipped := v }) ⦄ := by
  unfold tacenta_ratchet.State.evict_oldest_loop0
  apply loop.spec_decr_nat
    (measure := fun p => 1 - (Prod.snd p).val)
    (inv := fun p =>
      (Prod.snd p).val = 0 ∧ Prod.fst p = s ∨
      (Prod.snd p).val = 1 ∧ Prod.fst p = { s with skipped := v })
  · rintro ⟨state, evicted⟩ hinv
    simp only at hinv
    rcases hinv with hzero | hone
    · rcases hzero with ⟨he, hs⟩
      have hev : evicted = 0#usize := UScalar.eq_of_val_eq he
      rw [hs, hev]
      unfold tacenta_ratchet.State.evict_oldest_loop0.body
      have hlenU : alloc.vec.Vec.len s.skipped ≠ 0#usize := by
        intro hz
        apply hlen
        simpa [alloc.vec.Vec.len] using congrArg UScalar.val hz
      have hlenU' : (alloc.vec.Vec.len s.skipped != 0#usize) = true := by
        simp [bne_iff_ne, hlenU]
      simp [hlenU', hscan, hremove]
      step with Usize.add_spec
        (by scalar_tac : (0#usize).val + (1#usize).val ≤ Usize.max)
      have hevicted : evicted1 = 1#usize :=
        UScalar.eq_of_val_eq (by simpa using evicted1_post)
      simp [hevicted]
    · rcases hone with ⟨he, hs⟩
      have hev : evicted = 1#usize := UScalar.eq_of_val_eq he
      rw [hs, hev]
      simp [tacenta_ratchet.State.evict_oldest_loop0.body]
  · exact Or.inl ⟨rfl, rfl⟩

/-! Under a per-state scan/removal witness, the generated outer loop either
reaches its requested count or stops when the skipped-key store is empty.
This is the termination and progress shell for the later StateR/model
refinement; the witness deliberately leaves the semantic selected entry to
the one-step bridge above. -/
theorem concrete_classical_evict_outer_progress
    (s : tacenta_ratchet.State) (count : Std.Usize)
    (hstep : ∀ (state : tacenta_ratchet.State) (evicted : Std.Usize),
      evicted.val < count.val → state.skipped.val.length ≠ 0 →
      ∃ (oldest : Std.Usize) (discarded : Array Std.U8 32#usize)
        (v : alloc.vec.Vec tacenta_ratchet.SkippedKey) (evicted1 : Std.Usize),
        tacenta_ratchet.State.evict_oldest_loop0_loop0
          state.skipped 0#usize 1#usize = ok oldest ∧
        tacenta_ratchet.remove_skipped_at state.skipped oldest =
          ok (discarded, v) ∧
        evicted + 1#usize = ok evicted1 ∧
        evicted1.val = evicted.val + 1) :
    tacenta_ratchet.State.evict_oldest_loop0 s count 0#usize
      ⦃ fun r => r.1.val = count.val ∨ r.2.skipped.val.length = 0 ⦄ := by
  unfold tacenta_ratchet.State.evict_oldest_loop0
  apply loop.spec_decr_nat
    (measure := fun p => count.val - (Prod.snd p).val)
    (inv := fun p => (Prod.snd p).val ≤ count.val)
  · rintro ⟨state, evicted⟩ hinv
    simp only at hinv
    by_cases hdone : count.val ≤ evicted.val
    · have heq : evicted.val = count.val := by omega
      have hev : evicted = count := UScalar.eq_of_val_eq heq
      simp [tacenta_ratchet.State.evict_oldest_loop0.body, hev, hdone]
    · have hlt : evicted.val < count.val := by omega
      by_cases hempty : state.skipped.val.length = 0
      · unfold tacenta_ratchet.State.evict_oldest_loop0.body
        have hlenU : alloc.vec.Vec.len state.skipped = 0#usize := by
          simp [alloc.vec.Vec.len, hempty]
          rfl
        simp [hlt, hlenU]
        exact Or.inr (List.eq_nil_of_length_eq_zero hempty)
      · obtain ⟨oldest, discarded, v, evicted1, hscan, hremove, hadd, hval⟩ :=
          hstep state evicted hlt hempty
        unfold tacenta_ratchet.State.evict_oldest_loop0.body
        have hlenU : alloc.vec.Vec.len state.skipped ≠ 0#usize := by
          intro hz
          apply hempty
          simpa [alloc.vec.Vec.len] using congrArg UScalar.val hz
        have hlenU' : (alloc.vec.Vec.len state.skipped != 0#usize) = true := by
          simp [bne_iff_ne, hlenU]
        simp [hlt, hlenU', hscan, hremove, hadd]
        omega
  · simp

/-! The progress shell can preserve the concrete/model relation as well as
    its counter invariant.  The per-state witness is intentionally stated in
    terms of the generated body: the next semantic step can discharge it with
    `concrete_classical_evict_one_step_model` without reopening the loop
    arithmetic. -/
theorem concrete_classical_evict_outer_stateR
    (s : tacenta_ratchet.State) (m : Model.State.State) (count : Std.Usize)
    (hrel : Tacenta.SessionUnitT3.StateR s m)
    (hstep : ∀ (state : tacenta_ratchet.State) (mstate : Model.State.State)
      (evicted : Std.Usize),
      Tacenta.SessionUnitT3.StateR state mstate →
      evicted.val < count.val → state.skipped.val.length ≠ 0 →
      ∃ (nextState : tacenta_ratchet.State) (nextModel : Model.State.State)
        (evicted1 : Std.Usize),
        tacenta_ratchet.State.evict_oldest_loop0.body count state evicted
          ⦃ fun r => r = ControlFlow.cont (nextState, evicted1) ⦄ ∧
        Tacenta.SessionUnitT3.StateR nextState nextModel ∧
        evicted1.val ≤ count.val ∧ evicted.val < evicted1.val) :
    tacenta_ratchet.State.evict_oldest_loop0 s count 0#usize
      ⦃ fun r => ∃ mstate, Tacenta.SessionUnitT3.StateR r.2 mstate ⦄ := by
  unfold tacenta_ratchet.State.evict_oldest_loop0
  apply loop.spec_decr_nat
    (measure := fun p => count.val - (Prod.snd p).val)
    (inv := fun p => ∃ mstate, Tacenta.SessionUnitT3.StateR p.1 mstate ∧
      p.2.val ≤ count.val)
  · rintro ⟨state, evicted⟩ ⟨mstate, hstate, hbound⟩
    change evicted.val ≤ count.val at hbound
    by_cases hdone : count.val ≤ evicted.val
    · have heq : evicted.val = count.val := by omega
      have hev : evicted = count := UScalar.eq_of_val_eq heq
      simp [tacenta_ratchet.State.evict_oldest_loop0.body, hev]
      exact ⟨mstate, hstate⟩
    · have hlt : evicted.val < count.val := by omega
      by_cases hempty : state.skipped.val.length = 0
      · unfold tacenta_ratchet.State.evict_oldest_loop0.body
        have hlenU : alloc.vec.Vec.len state.skipped = 0#usize := by
          simp [alloc.vec.Vec.len, hempty]
          rfl
        simp [hlt, hlenU]
        exact ⟨mstate, hstate⟩
      · obtain ⟨nextState, nextModel, evicted1, hbody, hnext, ⟨hbound1, hinc⟩⟩ :=
          hstep state mstate evicted hstate hlt hempty
        refine Std.WP.spec_mono hbody ?_
        intro r hr
        simp [hr]
        exact ⟨⟨nextModel, hnext⟩, hbound1, by omega⟩
  · refine ⟨m, hrel, by simp⟩

/-! A concrete scan/removal certificate now supplies the per-state witness
    expected by `concrete_classical_evict_outer_stateR`.  This is the first
    fully composed step: the generated body, the one-entry selector bridge,
    and the StateR relation all agree on the same post-state. -/
theorem concrete_classical_evict_stateR_step
    (hvr : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    {s : tacenta_ratchet.State} {m : Model.State.State}
    (hrel : Tacenta.SessionUnitT3.StateR s m)
    (count evicted evicted1 oldest : Std.Usize)
    (discarded : Array Std.U8 32#usize)
    (v : alloc.vec.Vec tacenta_ratchet.SkippedKey)
    (hcount : evicted.val < count.val)
    (hwidth : s.skipped.val.length ≤ UScalar.cMax UScalarTy.Usize)
    (hr : oldest.val < s.skipped.val.length)
    (hmin : ∀ (hr : oldest.val < s.skipped.val.length) (j : Std.Usize)
      (hj : j.val < s.skipped.val.length) (hjlen : j.val < s.skipped.val.length),
      (s.skipped.val[oldest.val]'hr).stored_at.val ≤
        (s.skipped.val[j.val]'hjlen).stored_at.val)
    (hfirst : ∀ (hr : oldest.val < s.skipped.val.length) (j : Std.Usize)
      (hj : j.val < oldest.val) (hjlen : j.val < s.skipped.val.length),
      (s.skipped.val[oldest.val]'hr).stored_at.val <
        (s.skipped.val[j.val]'hjlen).stored_at.val)
    (hscan : tacenta_ratchet.State.evict_oldest_loop0_loop0
      s.skipped 0#usize 1#usize = ok oldest)
    (hremove : tacenta_ratchet.remove_skipped_at s.skipped oldest =
      ok (discarded, v))
    (hadd : evicted + 1#usize = ok evicted1)
    (hval : evicted1.val = evicted.val + 1)
    (hbound : evicted1.val ≤ count.val) :
    ∃ nextState nextModel,
      tacenta_ratchet.State.evict_oldest_loop0.body count s evicted
        ⦃ fun r => r = ControlFlow.cont (nextState, evicted1) ⦄ ∧
      Tacenta.SessionUnitT3.StateR nextState nextModel ∧
      nextModel = (Model.Ratchet.evictOldest m 1).1 ∧
      evicted1.val ≤ count.val ∧ evicted.val < evicted1.val := by
  have hlen : s.skipped.val.length ≠ 0 := by omega
  obtain ⟨target, discarded', v', htarget, hsel, hremove', hstate⟩ :=
    concrete_classical_evict_one_step_model hvr hrel oldest hwidth hr hmin hfirst
  have hpair : (discarded', v') = (discarded, v) := by
    have hEq := hremove'.symm.trans hremove
    injection hEq
  rcases hpair with ⟨rfl, rfl⟩
  have hbody := concrete_classical_evict_body_step s count evicted evicted1 oldest
    discarded v hcount hscan hremove hadd hlen
  refine ⟨{ s with skipped := v }, (Model.Ratchet.evictOldest m 1).1,
    ?_, ?_, rfl, hbound, by omega⟩
  · exact hbody
  · exact hstate

/-! The StateR loop invariant can now retain the model's exact fuel state.
    After each concrete eviction, `evictOldest_append` identifies the model
    post-state with the same initial state run for the returned counter. -/
theorem concrete_classical_evict_outer_model_stateR
    (s : tacenta_ratchet.State) (base : Model.State.State) (count : Std.Usize)
    (hrel : Tacenta.SessionUnitT3.StateR s base)
    (hstep : ∀ (state : tacenta_ratchet.State) (mstate : Model.State.State)
      (evicted : Std.Usize),
      Tacenta.SessionUnitT3.StateR state mstate →
      evicted.val < count.val → state.skipped.val.length ≠ 0 →
      ∃ (nextState : tacenta_ratchet.State) (nextModel : Model.State.State)
        (evicted1 : Std.Usize),
        tacenta_ratchet.State.evict_oldest_loop0.body count state evicted
          ⦃ fun r => r = ControlFlow.cont (nextState, evicted1) ⦄ ∧
        Tacenta.SessionUnitT3.StateR nextState nextModel ∧
        nextModel = (Model.Ratchet.evictOldest mstate 1).1 ∧
        evicted1.val ≤ count.val ∧ evicted1.val = evicted.val + 1) :
    tacenta_ratchet.State.evict_oldest_loop0 s count 0#usize
      ⦃ fun r => ∃ mstate, Tacenta.SessionUnitT3.StateR r.2 mstate ∧
        mstate = (Model.Ratchet.evictOldest base r.1.val).1 ⦄ := by
  unfold tacenta_ratchet.State.evict_oldest_loop0
  apply loop.spec_decr_nat
    (measure := fun p => count.val - (Prod.snd p).val)
    (inv := fun p => ∃ mstate, Tacenta.SessionUnitT3.StateR p.1 mstate ∧
      mstate = (Model.Ratchet.evictOldest base p.2.val).1 ∧
      p.2.val ≤ count.val)
  · rintro ⟨state, evicted⟩ ⟨mstate, hstate, hmodel, hbound⟩
    change evicted.val ≤ count.val at hbound
    change mstate = (Model.Ratchet.evictOldest base evicted.val).1 at hmodel
    by_cases hdone : count.val ≤ evicted.val
    · have heq : evicted.val = count.val := by omega
      have hev : evicted = count := UScalar.eq_of_val_eq heq
      simp [tacenta_ratchet.State.evict_oldest_loop0.body, hev]
      have hmodel' : mstate = (Model.Ratchet.evictOldest base count.val).1 := by
        simpa [hev] using hmodel
      rw [← hmodel']
      exact hstate
    · have hlt : evicted.val < count.val := by omega
      by_cases hempty : state.skipped.val.length = 0
      · unfold tacenta_ratchet.State.evict_oldest_loop0.body
        have hlenU : alloc.vec.Vec.len state.skipped = 0#usize := by
          simp [alloc.vec.Vec.len, hempty]
          rfl
        simp [hlt, hlenU]
        rw [← hmodel]
        exact hstate
      · obtain ⟨nextState, nextModel, evicted1, hbody, hnext, hnextModel,
          hbound1, hval⟩ := hstep state mstate evicted hstate hlt hempty
        refine Std.WP.spec_mono hbody ?_
        intro r hr
        simp [hr]
        have happend := congrArg Prod.fst
          (Model.Ratchet.evictOldest_append base evicted.val 1)
        simp only at happend
        have hnextModel' : nextModel =
            (Model.Ratchet.evictOldest
              (Model.Ratchet.evictOldest base evicted.val).1 1).1 := by
          calc
            nextModel = (Model.Ratchet.evictOldest mstate 1).1 := hnextModel
            _ = (Model.Ratchet.evictOldest
              (Model.Ratchet.evictOldest base evicted.val).1 1).1 := by
                rw [hmodel]
        have hmodel1 : nextModel =
            (Model.Ratchet.evictOldest base evicted1.val).1 := by
          calc
            nextModel = (Model.Ratchet.evictOldest
              (Model.Ratchet.evictOldest base evicted.val).1 1).1 := hnextModel'
            _ = (Model.Ratchet.evictOldest base (evicted.val + 1)).1 := happend.symm
            _ = (Model.Ratchet.evictOldest base evicted1.val).1 := by rw [hval]
        rw [← hmodel1]
        exact ⟨hnext, hbound1, by omega⟩
  · refine ⟨base, hrel, by rfl, by simp⟩

/-! Strengthening the previous shell, this variant preserves the complete
    model pair `(state, returned count)` for the requested fuel.  The
    early-empty branch uses the model's empty-suffix law; the progressing
    branch uses the one-step non-empty count law. -/
theorem concrete_classical_evict_outer_model_pair
    (s : tacenta_ratchet.State) (base : Model.State.State) (count : Std.Usize)
    (hrel : Tacenta.SessionUnitT3.StateR s base)
    (hstep : ∀ (state : tacenta_ratchet.State) (mstate : Model.State.State)
      (evicted : Std.Usize),
      Tacenta.SessionUnitT3.StateR state mstate →
      evicted.val < count.val → state.skipped.val.length ≠ 0 →
      ∃ (nextState : tacenta_ratchet.State) (nextModel : Model.State.State)
        (evicted1 : Std.Usize),
        tacenta_ratchet.State.evict_oldest_loop0.body count state evicted
          ⦃ fun r => r = ControlFlow.cont (nextState, evicted1) ⦄ ∧
        Tacenta.SessionUnitT3.StateR nextState nextModel ∧
        nextModel = (Model.Ratchet.evictOldest mstate 1).1 ∧
        evicted1.val ≤ count.val ∧ evicted1.val = evicted.val + 1) :
    tacenta_ratchet.State.evict_oldest_loop0 s count 0#usize
      ⦃ fun r => ∃ mstate, Tacenta.SessionUnitT3.StateR r.2 mstate ∧
        (Model.Ratchet.evictOldest base count.val) = (mstate, r.1.val) ⦄ := by
  unfold tacenta_ratchet.State.evict_oldest_loop0
  apply loop.spec_decr_nat
    (measure := fun p => count.val - (Prod.snd p).val)
    (inv := fun p => ∃ mstate, Tacenta.SessionUnitT3.StateR p.1 mstate ∧
      (Model.Ratchet.evictOldest base p.2.val) = (mstate, p.2.val) ∧
      p.2.val ≤ count.val)
  · rintro ⟨state, evicted⟩ ⟨mstate, hstate, hmodel, hbound⟩
    change evicted.val ≤ count.val at hbound
    by_cases hdone : count.val ≤ evicted.val
    · have heq : evicted.val = count.val := by omega
      have hev : evicted = count := UScalar.eq_of_val_eq heq
      simp [tacenta_ratchet.State.evict_oldest_loop0.body, hev]
      refine ⟨mstate, hstate, ?_⟩
      simpa [hev] using hmodel
    · have hlt : evicted.val < count.val := by omega
      by_cases hempty : state.skipped.val.length = 0
      · unfold tacenta_ratchet.State.evict_oldest_loop0.body
        have hlenU : alloc.vec.Vec.len state.skipped = 0#usize := by
          simp [alloc.vec.Vec.len, hempty]
          rfl
        simp [hlt, hlenU]
        have hs_nil : state.skipped.val = [] := List.eq_nil_of_length_eq_zero hempty
        have hmempty : mstate.skipped = [] := by
          rw [← hstate.skipped, hs_nil]
          rfl
        have hsuffix := Model.Ratchet.evictOldest_empty_suffix base mstate
          evicted.val (count.val - evicted.val) hmodel hmempty
        have hadd : evicted.val + (count.val - evicted.val) = count.val := by omega
        rw [hadd] at hsuffix
        exact ⟨mstate, hstate, hsuffix⟩
      · obtain ⟨nextState, nextModel, evicted1, hbody, hnext, hnextModel,
          hbound1, hval⟩ := hstep state mstate evicted hstate hlt hempty
        refine Std.WP.spec_mono hbody ?_
        intro r hr
        simp [hr]
        have happend := Model.Ratchet.evictOldest_append base evicted.val 1
        have hmnonempty : mstate.skipped ≠ [] := by
          intro hmempty
          apply hempty
          have hmap : state.skipped.val.map Tacenta.SessionUnitT3.skippedOf = [] := by
            simpa [hmempty] using hstate.skipped
          have hlen : state.skipped.val.length = 0 := by
            simpa [List.length_map] using congrArg List.length hmap
          exact hlen
        have hone : (Model.Ratchet.evictOldest mstate 1).2 = 1 :=
          Model.Ratchet.evictOldest_one_nonempty mstate hmnonempty
        have hfull1 : Model.Ratchet.evictOldest base (evicted.val + 1) =
            (nextModel, evicted.val + 1) := by
          rw [happend, hmodel]
          simp [hnextModel, hone]
        have hfull1' : Model.Ratchet.evictOldest base evicted1.val =
            (nextModel, evicted1.val) := by
          simpa [hval] using hfull1
        refine ⟨⟨nextModel, hnext, hfull1', hbound1⟩, by omega⟩
  · refine ⟨base, hrel, by rfl, by simp⟩

/-! The triple wrapper lifts the classical ratchet result into the lifecycle
    StateRefines relation.  Once the ratchet loop supplies its exact model
    fuel state, the untouched post-quantum component is carried verbatim. -/
theorem concrete_triple_evict_oldest_classical_refines
    (s : tacenta_triple.State) (m : Model.Triple.State) (count : Std.Usize)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (hratchet : tacenta_ratchet.State.evict_oldest s.classical count
      ⦃ fun r => ∃ mstate, Tacenta.SessionUnitT3.StateR r.2 mstate ∧
        mstate = (Model.Ratchet.evictOldest m.classical r.1.val).1 ⦄) :
    tacenta_triple.State.evict_oldest_classical s count
      ⦃ fun r => ∃ mstate, Tacenta.SessionUnitTripleT3.StateRefines
          Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs r.2 mstate ∧
        mstate = (Model.Triple.evictOldestClassical m r.1.val).1 ⦄ := by
  unfold tacenta_triple.State.evict_oldest_classical
  apply Aeneas.Std.WP.spec_bind
  · exact hratchet
  · intro r hr
    rcases r with ⟨i, s1⟩
    change ∃ mstate, Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      { classical := s1, post_quantum := s.post_quantum } mstate ∧
      mstate = (Model.Triple.evictOldestClassical m i.val).1
    obtain ⟨mclass, hclass, hclassEq⟩ := hr
    refine ⟨{ m with classical := mclass }, ?_, ?_⟩
    · constructor
      · rw [Tacenta.SessionUnitTripleT3.ratchetAbs_eq hclass]
      · exact hrel.2
    · simpa [Model.Triple.evictOldestClassical, hclassEq]

/-! With the requested-fuel pair theorem, the classical Triple wrapper also
    exposes the model's exact returned count. -/
theorem concrete_triple_evict_oldest_classical_requested_refines
    (s : tacenta_triple.State) (m : Model.Triple.State) (count : Std.Usize)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (hratchet : tacenta_ratchet.State.evict_oldest s.classical count
      ⦃ fun r => ∃ mstate, Tacenta.SessionUnitT3.StateR r.2 mstate ∧
        (Model.Ratchet.evictOldest m.classical count.val) = (mstate, r.1.val) ⦄) :
    tacenta_triple.State.evict_oldest_classical s count
      ⦃ fun r => ∃ mstate, Tacenta.SessionUnitTripleT3.StateRefines
          Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs r.2 mstate ∧
        (Model.Triple.evictOldestClassical m count.val) = (mstate, r.1.val) ⦄ := by
  unfold tacenta_triple.State.evict_oldest_classical
  apply Aeneas.Std.WP.spec_bind
  · exact hratchet
  · intro r hr
    rcases r with ⟨i, s1⟩
    change ∃ mstate, Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      { classical := s1, post_quantum := s.post_quantum } mstate ∧
      (Model.Triple.evictOldestClassical m count.val) = (mstate, i.val)
    obtain ⟨mclass, hclass, hclassEq⟩ := hr
    refine ⟨{ m with classical := mclass }, ?_, ?_⟩
    · constructor
      · rw [Tacenta.SessionUnitTripleT3.ratchetAbs_eq hclass]
      · exact hrel.2
    · simpa [Model.Triple.evictOldestClassical, hclassEq]

/-! The post-quantum eviction wrapper is the analogous lift for the SPQR
    branch.  Its inner T3 result already includes the returned count and the
    sparse StateRefines relation; the triple relation adds the unchanged
    classical component. -/
theorem concrete_triple_evict_oldest_post_quantum_refines
    (s : tacenta_triple.State) (m : Model.Triple.State) (count : Std.Usize)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (hspqr : tacenta_spqr.State.evict_oldest s.post_quantum count
      ⦃ fun r => r.1.val = (Model.SparseRatchet.evictOldest m.postQuantum count.val).2 ∧
        Tacenta.SessionUnitSpqrT3.StateRefines r.2
          (Model.SparseRatchet.evictOldest m.postQuantum count.val).1 ⦄) :
    tacenta_triple.State.evict_oldest_post_quantum s count
      ⦃ fun r => r.1.val = (Model.Triple.evictOldestPostQuantum m count.val).2 ∧
        Tacenta.SessionUnitTripleT3.StateRefines
          Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs r.2
          (Model.Triple.evictOldestPostQuantum m count.val).1 ⦄ := by
  unfold tacenta_triple.State.evict_oldest_post_quantum
  apply Aeneas.Std.WP.spec_bind
  · exact hspqr
  · intro r hr
    rcases r with ⟨i, s1⟩
    change i.val = (Model.Triple.evictOldestPostQuantum m count.val).2 ∧
      Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        { classical := s.classical, post_quantum := s1 }
        (Model.Triple.evictOldestPostQuantum m count.val).1
    rcases hr with ⟨hcount, hspqrState⟩
    constructor
    · simpa [Model.Triple.evictOldestPostQuantum] using hcount
    · exact ⟨hrel.1, Tacenta.SessionUnitTripleT3.spqrAbs_eq hspqrState⟩

/-! The lifecycle wrapper swaps the generated ratchet result from
    `(evicted, state)` to `(state, evicted)`.  These two small adapters keep
    the exact requested-fuel pair visible at that boundary for the retry
    composition below. -/
theorem concrete_lifecycle_evict_for_retry_classical_requested_refines
    (s : tacenta_triple.State) (m : Model.Triple.State) (count : Std.Usize)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (hratchet : tacenta_ratchet.State.evict_oldest s.classical count
      ⦃ fun r => ∃ mstate, Tacenta.SessionUnitT3.StateR r.2 mstate ∧
        (Model.Ratchet.evictOldest m.classical count.val) = (mstate, r.1.val) ⦄) :
    lifecycle.evict_for_retry s lifecycle.FullStore.Classical count
      ⦃ fun r => ∃ mstate, Tacenta.SessionUnitTripleT3.StateRefines
          Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs r.1 mstate ∧
        (Model.Triple.evictOldestClassical m count.val) = (mstate, r.2.val) ⦄ := by
  unfold lifecycle.evict_for_retry
  apply Aeneas.Std.WP.spec_bind
  · exact concrete_triple_evict_oldest_classical_requested_refines s m count hrel hratchet
  · intro r hr
    rcases r with ⟨evicted, state1⟩
    rcases hr with ⟨mstate, hstate, hpair⟩
    simp [hpair]
    simpa using hstate

theorem concrete_lifecycle_evict_for_retry_post_quantum_requested_refines
    (s : tacenta_triple.State) (m : Model.Triple.State) (count : Std.Usize)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (hspqr : tacenta_spqr.State.evict_oldest s.post_quantum count
      ⦃ fun r => r.1.val = (Model.SparseRatchet.evictOldest m.postQuantum count.val).2 ∧
        Tacenta.SessionUnitSpqrT3.StateRefines r.2
          (Model.SparseRatchet.evictOldest m.postQuantum count.val).1 ⦄) :
    lifecycle.evict_for_retry s lifecycle.FullStore.PostQuantum count
      ⦃ fun r => ∃ mstate, Tacenta.SessionUnitTripleT3.StateRefines
          Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs r.1 mstate ∧
        (Model.Triple.evictOldestPostQuantum m count.val) = (mstate, r.2.val) ⦄ := by
  unfold lifecycle.evict_for_retry
  apply Aeneas.Std.WP.spec_bind
  · exact concrete_triple_evict_oldest_post_quantum_refines s m count hrel hspqr
  · intro r hr
    rcases r with ⟨evicted, state1⟩
    rcases hr with ⟨hcount, hstate⟩
    simp [hcount]
    refine ⟨{ m with postQuantum := (Model.SparseRatchet.evictOldest m.postQuantum count.val).1 }, ?_, ?_⟩
    · exact ⟨hstate.1, hstate.2⟩
    · simpa [Model.Triple.evictOldestPostQuantum] using And.intro hcount hstate

theorem model_evict_for_retry_classical_of_concrete
    (s : tacenta_triple.State) (m : Model.Triple.State) (count : Std.Usize)
    (state1 : tacenta_triple.State) (evicted : Std.Usize)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (hratchet : tacenta_ratchet.State.evict_oldest s.classical count
      ⦃ fun r => ∃ mstate, Tacenta.SessionUnitT3.StateR r.2 mstate ∧
        (Model.Ratchet.evictOldest m.classical count.val) = (mstate, r.1.val) ⦄)
    (hconcrete : lifecycle.evict_for_retry s lifecycle.FullStore.Classical count =
      ok (state1, evicted)) :
    ∃ mstate, Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs state1 mstate ∧
      Model.Triple.evictOldestClassical m count.val = (mstate, evicted.val) := by
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists
    (concrete_lifecycle_evict_for_retry_classical_requested_refines s m count hrel hratchet)
  rw [hconcrete] at hr
  cases hr
  exact hpost

theorem model_evict_for_retry_post_quantum_of_concrete
    (s : tacenta_triple.State) (m : Model.Triple.State) (count : Std.Usize)
    (state1 : tacenta_triple.State) (evicted : Std.Usize)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (hspqr : tacenta_spqr.State.evict_oldest s.post_quantum count
      ⦃ fun r => r.1.val = (Model.SparseRatchet.evictOldest m.postQuantum count.val).2 ∧
        Tacenta.SessionUnitSpqrT3.StateRefines r.2
          (Model.SparseRatchet.evictOldest m.postQuantum count.val).1 ⦄)
    (hconcrete : lifecycle.evict_for_retry s lifecycle.FullStore.PostQuantum count =
      ok (state1, evicted)) :
    ∃ mstate, Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs state1 mstate ∧
      Model.Triple.evictOldestPostQuantum m count.val = (mstate, evicted.val) := by
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists
    (concrete_lifecycle_evict_for_retry_post_quantum_requested_refines s m count hrel hspqr)
  rw [hconcrete] at hr
  cases hr
  exact hpost

/-! A one-retry loop has a concrete postcondition.  Keeping this as a Hoare
specification is deliberate: the generated `loop` is a partial computation,
so the theorem states the exact result of every terminating run while the
existing T1 loop obligations establish that the run cannot fail. -/
theorem concrete_receive_with_eviction_one_retry_spec
    (composite : tacenta_wire.Composite) (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output) (half : lifecycle.FullStore)
    (state evictedState : tacenta_triple.State) (batch batch1 evicted : Std.Usize)
    (pending : tacenta_triple.TripleError)
    (result : tacenta_triple.State × Array Std.U8 32#usize)
    (hEvict : lifecycle.evict_for_retry state half batch = ok (evictedState, evicted))
    (hNonzero : evicted ≠ 0#usize)
    (hBatch : core.num.Usize.saturating_add batch batch = batch1)
    (hRetry : lifecycle.receive_attempt evictedState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok result)) :
    lifecycle.receive_with_eviction_loop composite header dhOutRecv dhOutSend
      newDhsPub output half state batch pending none ⦃
        fun r => r = (pending, some (core.result.Result.Ok result)) ⦄ := by
  unfold lifecycle.receive_with_eviction_loop
  have hlo : loop
      (fun x =>
        match x with
        | (half1, work1, batch1, pending1, outcome1) =>
          lifecycle.receive_with_eviction_loop.body composite header dhOutRecv dhOutSend
            newDhsPub output half1 work1 batch1 pending1 outcome1)
      (half, state, batch, pending, none) ⦃
        fun r => r = (pending, some (core.result.Result.Ok result)) ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun x => match x.2.2.2.2 with | none => 1 | some _ => 0)
      (inv := fun x =>
        match x.2.2.2.2 with
        | none => x.1 = half ∧ x.2.1 = state ∧ x.2.2.1 = batch ∧
            x.2.2.2.1 = pending
        | some o => o = core.result.Result.Ok result ∧ x.2.2.2.1 = pending)
    · intro x hx
      rcases x with ⟨halfX, workX, batchX, pendingX, outcomeX⟩
      simp only at hx ⊢
      unfold lifecycle.receive_with_eviction_loop.body
      cases outcomeX with
      | none =>
        simp_all [lifecycle.receive_with_eviction_loop.body, Aeneas.Std.lift,
          hEvict, hNonzero, hBatch, hRetry]
      | some o =>
        simp_all [lifecycle.receive_with_eviction_loop.body]
    · simp
  exact hlo

/-! Reattach a proved loop result to the generated public wrapper.  The outer
    function clones the Triple state and computes the initial shortfall before
    entering the loop; this adapter records those three concrete equalities so
    the retry refinement can be consumed by the Session theorem. -/
theorem concrete_receive_with_eviction_from_retry_loop
    (state cloned : tacenta_triple.State)
    (composite : tacenta_wire.Composite) (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (reason : tacenta_triple.TripleError) (half : lifecycle.FullStore)
    (batch : Std.Usize) (result : tacenta_triple.State × Array Std.U8 32#usize)
    (hAttempt : lifecycle.receive_attempt state header dhOutRecv dhOutSend
      newDhsPub output = ok (.Err reason))
    (hFull : lifecycle.full_store reason = ok (some half))
    (hClone : tacenta_triple.State.Insts.CoreCloneClone.clone state = ok cloned)
    (hShortfall : lifecycle.receive_shortfall half cloned composite = ok batch)
    (hLoop : lifecycle.receive_with_eviction_loop composite header dhOutRecv dhOutSend
      newDhsPub output half cloned batch reason none =
        ok (reason, some (core.result.Result.Ok result))) :
    lifecycle.receive_with_eviction state composite header dhOutRecv dhOutSend
      newDhsPub output = ok (core.result.Result.Ok result) := by
  unfold lifecycle.receive_with_eviction
  simp [hAttempt, hFull, hClone, hShortfall, hLoop]

/-! The measured variant uses the same fuel accounting as the totality proof in
    `UnitLifecycleT1`.  It is the form needed when this one-step result is
    inserted into the enclosing retry induction: the evicted working copy
    must strictly reduce the skipped-key measure, rather than merely reducing
    the outcome flag. -/
theorem concrete_receive_with_eviction_one_retry_spec_measured
    (composite : tacenta_wire.Composite) (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output) (half : lifecycle.FullStore)
    (state evictedState : tacenta_triple.State) (batch batch1 evicted : Std.Usize)
    (pending : tacenta_triple.TripleError)
    (result : tacenta_triple.State × Array Std.U8 32#usize)
    (hEvict : lifecycle.evict_for_retry state half batch = ok (evictedState, evicted))
    (hNonzero : evicted ≠ 0#usize)
    (hMeasure : Tacenta.UnitLifecycleT1.skippedTotal evictedState <
      Tacenta.UnitLifecycleT1.skippedTotal state)
    (hBatch : core.num.Usize.saturating_add batch batch = batch1)
    (hRetry : lifecycle.receive_attempt evictedState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok result)) :
    lifecycle.receive_with_eviction_loop composite header dhOutRecv dhOutSend
      newDhsPub output half state batch pending none ⦃
        fun r => r = (pending, some (core.result.Result.Ok result)) ⦄ := by
  unfold lifecycle.receive_with_eviction_loop
  have hlo : loop
      (fun x =>
        match x with
        | (half1, work1, batch1, pending1, outcome1) =>
          lifecycle.receive_with_eviction_loop.body composite header dhOutRecv dhOutSend
            newDhsPub output half1 work1 batch1 pending1 outcome1)
      (half, state, batch, pending, none) ⦃
        fun r => r = (pending, some (core.result.Result.Ok result)) ⦄ := by
    apply loop.spec_decr_nat
      (measure := Tacenta.UnitLifecycleT1.retryMeasure)
      (inv := fun x =>
        match x.2.2.2.2 with
        | none => x.1 = half ∧ x.2.1 = state ∧ x.2.2.1 = batch ∧
            x.2.2.2.1 = pending
        | some o => o = core.result.Result.Ok result ∧
            x.2.2.2.1 = pending)
    · intro x hx
      rcases x with ⟨halfX, workX, batchX, pendingX, outcomeX⟩
      simp only at hx ⊢
      unfold lifecycle.receive_with_eviction_loop.body
      cases outcomeX with
      | none =>
        simp_all [lifecycle.receive_with_eviction_loop.body, Aeneas.Std.lift,
          hEvict, hNonzero, hBatch, hRetry, Tacenta.UnitLifecycleT1.retryMeasure]
        exact Nat.le_of_lt hMeasure
      | some o =>
        simp_all [lifecycle.receive_with_eviction_loop.body,
          Tacenta.UnitLifecycleT1.retryMeasure]
    · simp [Tacenta.UnitLifecycleT1.retryMeasure]
  exact hlo

/-! Discharge the measured-step premise from the existing T1 eviction
    contract.  This is the adapter that turns the generated `Usize` count into
    the natural-number decrease used by `retryMeasure`. -/
theorem concrete_evict_for_retry_measure_decreases
    (state : tacenta_triple.State) (half : lifecycle.FullStore)
    (batch : Std.Usize) (evictedState : tacenta_triple.State)
    (evicted : Std.Usize)
    (hrmRatchet : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    (hrmSpqr : Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal)
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hroom : Tacenta.UnitLifecycleT1.ReceiveHeadroom state)
    (hEvict : lifecycle.evict_for_retry state half batch = ok (evictedState, evicted))
    (hNonzero : evicted ≠ 0#usize) :
    Tacenta.UnitLifecycleT1.skippedTotal evictedState <
    Tacenta.UnitLifecycleT1.skippedTotal state := by
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.evict_for_retry_no_panic
      hrmRatchet hrmSpqr hz
      state half batch hroom)
  rw [hEvict] at hr
  cases hr
  have hevicted : 0 < evicted.val := by scalar_tac
  exact hpost.2.2 hevicted

/-! Package the classical eviction's two induction facts together: the
    translated working copy still refines a model state, and the retry measure
    decreases.  The post-quantum adapter below has the same shape; keeping the
    halves separate preserves the leaf-specific contracts at the call site. -/
theorem model_evict_for_retry_classical_measured
    (s : tacenta_triple.State) (m : Model.Triple.State) (count : Std.Usize)
    (state1 : tacenta_triple.State) (evicted : Std.Usize)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (hratchet : tacenta_ratchet.State.evict_oldest s.classical count
      ⦃ fun r => ∃ mstate, Tacenta.SessionUnitT3.StateR r.2 mstate ∧
        (Model.Ratchet.evictOldest m.classical count.val) = (mstate, r.1.val) ⦄)
    (hrmRatchet : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    (hrmSpqr : Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal)
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hroom : Tacenta.UnitLifecycleT1.ReceiveHeadroom s)
    (hconcrete : lifecycle.evict_for_retry s lifecycle.FullStore.Classical count =
      ok (state1, evicted))
    (hNonzero : evicted ≠ 0#usize) :
    ∃ mstate, Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        state1 mstate ∧
      Model.Triple.evictOldestClassical m count.val = (mstate, evicted.val) ∧
      Tacenta.UnitLifecycleT1.skippedTotal state1 <
        Tacenta.UnitLifecycleT1.skippedTotal s := by
  obtain ⟨mstate, hstate, hpair⟩ :=
    model_evict_for_retry_classical_of_concrete s m count state1 evicted hrel hratchet
      hconcrete
  have hmeasure := concrete_evict_for_retry_measure_decreases s lifecycle.FullStore.Classical
    count state1 evicted hrmRatchet hrmSpqr hz hroom hconcrete hNonzero
  exact ⟨mstate, hstate, hpair, hmeasure⟩

theorem model_evict_for_retry_post_quantum_measured
    (s : tacenta_triple.State) (m : Model.Triple.State) (count : Std.Usize)
    (state1 : tacenta_triple.State) (evicted : Std.Usize)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m)
    (hspqr : tacenta_spqr.State.evict_oldest s.post_quantum count
      ⦃ fun r => r.1.val = (Model.SparseRatchet.evictOldest m.postQuantum count.val).2 ∧
        Tacenta.SessionUnitSpqrT3.StateRefines r.2
          (Model.SparseRatchet.evictOldest m.postQuantum count.val).1 ⦄)
    (hrmRatchet : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    (hrmSpqr : Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal)
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hroom : Tacenta.UnitLifecycleT1.ReceiveHeadroom s)
    (hconcrete : lifecycle.evict_for_retry s lifecycle.FullStore.PostQuantum count =
      ok (state1, evicted))
    (hNonzero : evicted ≠ 0#usize) :
    ∃ mstate, Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        state1 mstate ∧
      Model.Triple.evictOldestPostQuantum m count.val = (mstate, evicted.val) ∧
      Tacenta.UnitLifecycleT1.skippedTotal state1 <
        Tacenta.UnitLifecycleT1.skippedTotal s := by
  obtain ⟨mstate, hstate, hpair⟩ :=
    model_evict_for_retry_post_quantum_of_concrete s m count state1 evicted hrel hspqr
      hconcrete
  have hmeasure := concrete_evict_for_retry_measure_decreases s lifecycle.FullStore.PostQuantum
    count state1 evicted hrmRatchet hrmSpqr hz hroom hconcrete hNonzero
  exact ⟨mstate, hstate, hpair, hmeasure⟩

/-! One generated loop-body step mirrors the model continuation equation when
    the retry fails with another refusal from the same full-store half. -/
theorem concrete_receive_with_eviction_loop_same_half_step
    (composite : tacenta_wire.Composite) (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (half : lifecycle.FullStore)
    (state evictedState : tacenta_triple.State)
    (batch batch1 evicted : Std.Usize)
    (pending reason : tacenta_triple.TripleError)
    (hEvict : lifecycle.evict_for_retry state half batch = ok (evictedState, evicted))
    (hNonzero : evicted ≠ 0#usize)
    (hBatch : core.num.Usize.saturating_add batch batch = batch1)
    (hRetry : lifecycle.receive_attempt evictedState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Err reason))
    (hFull : lifecycle.full_store reason = ok (some half))
    (hSame : core.cmp.PartialEq.ne.trait_default
      lifecycle.FullStore.Insts.CoreCmpPartialEqFullStore half half = ok false) :
    lifecycle.receive_with_eviction_loop.body composite header dhOutRecv dhOutSend
      newDhsPub output half state batch pending none =
      ok (ControlFlow.cont (half, evictedState, batch1, reason, none)) := by
  simp [lifecycle.receive_with_eviction_loop.body, Aeneas.Std.lift,
    hEvict, hNonzero, hBatch, hRetry, hFull, hSame,
    lifecycle.FullStore.Insts.CoreCmpPartialEqFullStore]

theorem concrete_receive_with_eviction_loop_switch_half_step
    (composite : tacenta_wire.Composite) (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (half nextHalf : lifecycle.FullStore)
    (state evictedState : tacenta_triple.State)
    (batch batch2 evicted : Std.Usize)
    (pending reason : tacenta_triple.TripleError)
    (hEvict : lifecycle.evict_for_retry state half batch = ok (evictedState, evicted))
    (hNonzero : evicted ≠ 0#usize)
    (hRetry : lifecycle.receive_attempt evictedState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Err reason))
    (hFull : lifecycle.full_store reason = ok (some nextHalf))
    (hDifferent : core.cmp.PartialEq.ne.trait_default
      lifecycle.FullStore.Insts.CoreCmpPartialEqFullStore nextHalf half = ok true)
    (hShortfall : lifecycle.receive_shortfall nextHalf evictedState composite = ok batch2) :
    lifecycle.receive_with_eviction_loop.body composite header dhOutRecv dhOutSend
      newDhsPub output half state batch pending none =
      ok (ControlFlow.cont (nextHalf, evictedState, batch2, reason, none)) := by
  simp [lifecycle.receive_with_eviction_loop.body, Aeneas.Std.lift,
    hEvict, hNonzero, hRetry, hFull, hDifferent, hShortfall]

theorem concrete_receive_with_eviction_loop_zero_evict
    (composite : tacenta_wire.Composite) (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (half : lifecycle.FullStore)
    (state : tacenta_triple.State)
    (batch : Std.Usize)
    (pending : tacenta_triple.TripleError)
    (hEvict : lifecycle.evict_for_retry state half batch = ok (state, 0#usize)) :
    lifecycle.receive_with_eviction_loop.body composite header dhOutRecv dhOutSend
      newDhsPub output half state batch pending none =
      ok (ControlFlow.cont (half, state, batch, pending,
        some (core.result.Result.Err pending))) := by
  simp [lifecycle.receive_with_eviction_loop.body, Aeneas.Std.lift, hEvict]

/-! The zero-eviction body theorem above is also enough to discharge the
    complete generated loop.  Keeping this whole-loop fact explicit prevents
    callers from treating a zero count as an ordinary retry: the Rust loop
    returns the pending refusal immediately and never calls receive again. -/
theorem concrete_receive_with_eviction_loop_zero_evict_spec
    (composite : tacenta_wire.Composite) (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (output : Option tacenta_spqr.Output)
    (half : lifecycle.FullStore) (state : tacenta_triple.State)
    (batch : Std.Usize) (pending : tacenta_triple.TripleError)
    (hEvict : lifecycle.evict_for_retry state half batch = ok (state, 0#usize)) :
    lifecycle.receive_with_eviction_loop composite header dhOutRecv dhOutSend
      newDhsPub output half state batch pending none ⦃
        fun r => r = (pending, some (core.result.Result.Err pending)) ⦄ := by
  unfold lifecycle.receive_with_eviction_loop
  have hlo : loop
      (fun x =>
        match x with
        | (half1, work1, batch1, pending1, outcome1) =>
          lifecycle.receive_with_eviction_loop.body composite header dhOutRecv dhOutSend
            newDhsPub output half1 work1 batch1 pending1 outcome1)
      (half, state, batch, pending, none) ⦃
        fun r => r = (pending, some (core.result.Result.Err pending)) ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun x => match x.2.2.2.2 with | none => 1 | some _ => 0)
      (inv := fun x =>
        match x.2.2.2.2 with
        | none => x.1 = half ∧ x.2.1 = state ∧ x.2.2.1 = batch ∧
            x.2.2.2.1 = pending
        | some o => o = core.result.Result.Err pending ∧
            x.2.2.2.1 = pending)
    · intro x hx
      rcases x with ⟨halfX, workX, batchX, pendingX, outcomeX⟩
      simp only at hx ⊢
      unfold lifecycle.receive_with_eviction_loop.body
      cases outcomeX with
      | none =>
        simp_all [lifecycle.receive_with_eviction_loop.body, Aeneas.Std.lift,
          hEvict]
      | some o =>
        simp_all [lifecycle.receive_with_eviction_loop.body]
    · simp
  exact hlo

/-- Expose the model retry branch: a successful `receiveWithEviction` that is
not the direct `receiveDetailed` success must enter the bounded eviction loop. -/
theorem model_receive_with_eviction_retry_case
    (state : Model.Triple.State)
    (composite : Model.CompositeHeader.Composite)
    (header : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Model.Lifecycle.Key)
    (output : Option Model.SparseRatchet.Output)
    (result : Model.Triple.State × Model.Lifecycle.Key)
    (h : Model.Lifecycle.receiveWithEviction state composite header dhOutRecv dhOutSend
      newDhsPub output = .ok result)
    (hnot : Model.Triple.receiveDetailed state header dhOutRecv dhOutSend newDhsPub output ≠
      .ok result) :
    ∃ reason half,
      Model.Triple.receiveDetailed state header dhOutRecv dhOutSend newDhsPub output =
        .error reason ∧
      Model.Lifecycle.fullStore reason = some half := by
  unfold Model.Lifecycle.receiveWithEviction at h
  cases hd : Model.Triple.receiveDetailed state header dhOutRecv dhOutSend newDhsPub output with
  | error reason =>
      cases hs : Model.Lifecycle.fullStore reason with
      | none => simp [hd, hs] at h
      | some half =>
          simp [hd, hs] at h
          exact ⟨reason, half, by simpa [hd], by simpa [hs]⟩
  | ok value =>
      have hv : value = result := by simpa [hd] using h
      exfalso
      apply hnot
      rw [hd, hv]

/-! The model lifecycle success has the same direct-or-retry partition. -/
theorem model_receive_with_eviction_success_cases
    (state : Model.Triple.State)
    (composite : Model.CompositeHeader.Composite)
    (header : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Model.Lifecycle.Key)
    (output : Option Model.SparseRatchet.Output)
    (result : Model.Triple.State × Model.Lifecycle.Key)
    (h : Model.Lifecycle.receiveWithEviction state composite header dhOutRecv dhOutSend
      newDhsPub output = .ok result) :
    (∃ direct,
      Model.Triple.receiveDetailed state header dhOutRecv dhOutSend newDhsPub output =
        .ok direct ∧ direct = result) ∨
    (∃ reason half,
      Model.Triple.receiveDetailed state header dhOutRecv dhOutSend newDhsPub output =
        .error reason ∧ Model.Lifecycle.fullStore reason = some half) := by
  unfold Model.Lifecycle.receiveWithEviction at h
  cases hd : Model.Triple.receiveDetailed state header dhOutRecv dhOutSend newDhsPub output with
  | error reason =>
      cases hs : Model.Lifecycle.fullStore reason with
      | none => simp [hd, hs] at h
      | some half =>
          simp [hd, hs] at h
          exact Or.inr ⟨reason, half, by simpa [hd], by simpa [hs]⟩
  | ok value =>
      have hv : value = result := by simpa [hd] using h
      exact Or.inl ⟨value, by simpa [hd], hv⟩

/-- A successful direct model Triple receive never enters the retry loop; the
lifecycle model returns the same state/key pair unchanged. -/
theorem model_receive_with_eviction_of_receive
    (state : Model.Triple.State)
    (composite : Model.CompositeHeader.Composite)
    (header : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Model.Lifecycle.Key)
    (output : Option Model.SparseRatchet.Output)
    (result : Model.Triple.State × Model.Lifecycle.Key)
    (h : Model.Triple.receive state header dhOutRecv dhOutSend newDhsPub output = some result) :
    Model.Lifecycle.receiveWithEviction state composite header dhOutRecv dhOutSend
      newDhsPub output = .ok result := by
  have hd := (Model.Triple.receiveDetailed_ok_iff state header dhOutRecv dhOutSend
    newDhsPub output result).2 h
  simp [Model.Lifecycle.receiveWithEviction, hd]

theorem model_receive_detailed_of_receive
    (state : Model.Triple.State) (header : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Model.Lifecycle.Key)
    (output : Option Model.SparseRatchet.Output)
    (result : Model.Triple.State × Model.Lifecycle.Key)
    (h : Model.Triple.receive state header dhOutRecv dhOutSend newDhsPub output =
      some result) :
    Model.Triple.receiveDetailed state header dhOutRecv dhOutSend newDhsPub output =
      .ok result :=
  (Model.Triple.receiveDetailed_ok_iff state header dhOutRecv dhOutSend newDhsPub output result).2 h

/-! Classical retry composition with an explicit shortfall equality.  Keeping
    the half fixed avoids dependent elimination over the two full-store
    constructors while making the model's requested count visible. -/
theorem concrete_classical_retry_loop_matches_model_one_retry
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (state evictedState : tacenta_triple.State)
    (modelState modelEvictedState : Model.Triple.State)
    (batch : Std.Usize) (batch1 evicted : Std.Usize)
    (pending : tacenta_triple.TripleError)
    (reason : Model.Triple.ReceiveRefusal)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hDirect : Model.Triple.receiveDetailed modelState modelHeader
      modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput = .error reason)
    (hFull : Model.Lifecycle.fullStore reason = some .classical)
    (hBatchModel : batch.val = Model.Lifecycle.receiveShortfall
      .classical modelState modelComposite)
    (hEvictModel : Model.Triple.evictOldestClassical modelState batch.val =
      (modelEvictedState, evicted.val))
    (hNonzero : evicted ≠ 0#usize)
    (hNonzeroModel : evicted.val ≠ 0)
    (hEvict : lifecycle.evict_for_retry state lifecycle.FullStore.Classical batch =
      ok (evictedState, evicted))
    (hBatch : core.num.Usize.saturating_add batch batch = batch1)
    (hRetry : lifecycle.receive_attempt evictedState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok realResult))
    (hRetryModel : Model.Triple.receiveDetailed modelEvictedState modelHeader
      modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput = .ok modelResult)
    (hState : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realResult.1 modelResult.1)
    (hKey : Tacenta.SessionUnitTripleT3.keyOf realResult.2 = modelResult.2) :
    lifecycle.receive_with_eviction_loop composite header dhOutRecv dhOutSend
      newDhsPub output lifecycle.FullStore.Classical state batch pending none ⦃
        fun r => r = (pending, some (core.result.Result.Ok realResult)) ⦄ ∧
      Model.Lifecycle.receiveWithEviction modelState modelComposite modelHeader
        modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput = .ok modelResult ∧
      Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        realResult.1 modelResult.1 ∧
      Tacenta.SessionUnitTripleT3.keyOf realResult.2 = modelResult.2 := by
  have hloop := concrete_receive_with_eviction_one_retry_spec composite header
    dhOutRecv dhOutSend newDhsPub output lifecycle.FullStore.Classical state evictedState
    batch batch1 evicted pending realResult hEvict hNonzero hBatch hRetry
  have hmodel := Model.Lifecycle.receiveWithEviction_one_retry modelState
    modelComposite modelHeader modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput
    modelResult modelEvictedState reason .classical evicted.val hDirect hFull
    (by simpa [hBatchModel] using hEvictModel) hNonzeroModel hRetryModel
  exact ⟨hloop, hmodel, hState, hKey⟩

/-! The non-direct classical retry can now be reattached to both public
    lifecycle wrappers.  The concrete side starts from the cloned working
    state, while the model side starts from the original model state; the
    theorem keeps that distinction explicit and carries the refusal mapping
    alongside the successful successor witnesses. -/
theorem concrete_classical_receive_with_eviction_retry_matches_model
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState work evictedState : tacenta_triple.State)
    (modelState modelEvictedState : Model.Triple.State)
    (batch : Std.Usize) (batch1 evicted : Std.Usize)
    (realReason : tacenta_triple.TripleError)
    (modelReason : Model.Triple.ReceiveRefusal)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hAttempt : lifecycle.receive_attempt realState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Err realReason))
    (hFullReal : lifecycle.full_store realReason = ok (some lifecycle.FullStore.Classical))
    (hClone : tacenta_triple.State.Insts.CoreCloneClone.clone realState = ok work)
    (hBatchReal : lifecycle.receive_shortfall lifecycle.FullStore.Classical work composite =
      ok batch)
    (hDirect : Model.Triple.receiveDetailed modelState modelHeader
      modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput = .error modelReason)
    (hFull : Model.Lifecycle.fullStore modelReason = some .classical)
    (hBatchModel : batch.val = Model.Lifecycle.receiveShortfall
      .classical modelState modelComposite)
    (hEvictModel : Model.Triple.evictOldestClassical modelState batch.val =
      (modelEvictedState, evicted.val))
    (hNonzero : evicted ≠ 0#usize)
    (hNonzeroModel : evicted.val ≠ 0)
    (hEvict : lifecycle.evict_for_retry work lifecycle.FullStore.Classical batch =
      ok (evictedState, evicted))
    (hBatch : core.num.Usize.saturating_add batch batch = batch1)
    (hRetry : lifecycle.receive_attempt evictedState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok realResult))
    (hRetryModel : Model.Triple.receiveDetailed modelEvictedState modelHeader
      modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput = .ok modelResult)
    (hState : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realResult.1 modelResult.1)
    (hKey : Tacenta.SessionUnitTripleT3.keyOf realResult.2 = modelResult.2)
    (hReason : tripleReceiveRefusalOfReal realReason = some modelReason) :
    lifecycle.receive_with_eviction realState composite header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok realResult) ∧
      Model.Lifecycle.receiveWithEviction modelState modelComposite modelHeader
        modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput = .ok modelResult ∧
      Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        realResult.1 modelResult.1 ∧
      Tacenta.SessionUnitTripleT3.keyOf realResult.2 = modelResult.2 ∧
      Tacenta.UnitLifecycleT3.refusalOf (.Triple realReason) =
        Model.Lifecycle.tripleReceiveRefusalOf modelReason := by
  have hloop := concrete_classical_retry_loop_matches_model_one_retry composite
    modelComposite header modelHeader dhOutRecv dhOutSend newDhsPub modelDhOutRecv
    modelDhOutSend modelNewDhsPub output modelOutput work evictedState modelState
    modelEvictedState batch batch1 evicted realReason modelReason realResult modelResult
    hDirect hFull hBatchModel hEvictModel hNonzero hNonzeroModel hEvict hBatch hRetry
    hRetryModel hState hKey
  obtain ⟨loopResult, hLoopCall, hLoopPost⟩ :=
    Std.WP.spec_imp_exists hloop.1
  have hLoop : lifecycle.receive_with_eviction_loop composite header dhOutRecv
      dhOutSend newDhsPub output lifecycle.FullStore.Classical work batch realReason none =
      ok (realReason, some (core.result.Result.Ok realResult)) := by
    rw [hLoopPost] at hLoopCall
    exact hLoopCall
  have houter := concrete_receive_with_eviction_from_retry_loop realState work composite
    header dhOutRecv dhOutSend newDhsPub output realReason lifecycle.FullStore.Classical
    batch realResult hAttempt hFullReal hClone hBatchReal hLoop
  exact ⟨houter, hloop.2.1, hloop.2.2.1, hloop.2.2.2, 
    Tacenta.UnitLifecycleT3.tripleReceiveRefusalOfReal_sound hReason⟩

theorem concrete_post_quantum_retry_loop_matches_model_one_retry
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (state evictedState : tacenta_triple.State)
    (modelState modelEvictedState : Model.Triple.State)
    (batch : Std.Usize) (batch1 evicted : Std.Usize)
    (pending : tacenta_triple.TripleError)
    (reason : Model.Triple.ReceiveRefusal)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hDirect : Model.Triple.receiveDetailed modelState modelHeader
      modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput = .error reason)
    (hFull : Model.Lifecycle.fullStore reason = some .postQuantum)
    (hBatchModel : batch.val = Model.Lifecycle.receiveShortfall
      .postQuantum modelState modelComposite)
    (hEvictModel : Model.Triple.evictOldestPostQuantum modelState batch.val =
      (modelEvictedState, evicted.val))
    (hNonzero : evicted ≠ 0#usize)
    (hNonzeroModel : evicted.val ≠ 0)
    (hEvict : lifecycle.evict_for_retry state lifecycle.FullStore.PostQuantum batch =
      ok (evictedState, evicted))
    (hBatch : core.num.Usize.saturating_add batch batch = batch1)
    (hRetry : lifecycle.receive_attempt evictedState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok realResult))
    (hRetryModel : Model.Triple.receiveDetailed modelEvictedState modelHeader
      modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput = .ok modelResult)
    (hState : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realResult.1 modelResult.1)
    (hKey : Tacenta.SessionUnitTripleT3.keyOf realResult.2 = modelResult.2) :
    lifecycle.receive_with_eviction_loop composite header dhOutRecv dhOutSend
      newDhsPub output lifecycle.FullStore.PostQuantum state batch pending none ⦃
        fun r => r = (pending, some (core.result.Result.Ok realResult)) ⦄ ∧
      Model.Lifecycle.receiveWithEviction modelState modelComposite modelHeader
        modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput = .ok modelResult ∧
      Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        realResult.1 modelResult.1 ∧
      Tacenta.SessionUnitTripleT3.keyOf realResult.2 = modelResult.2 := by
  have hloop := concrete_receive_with_eviction_one_retry_spec composite header
    dhOutRecv dhOutSend newDhsPub output lifecycle.FullStore.PostQuantum state evictedState
    batch batch1 evicted pending realResult hEvict hNonzero hBatch hRetry
  have hmodel := Model.Lifecycle.receiveWithEviction_one_retry modelState
    modelComposite modelHeader modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput
    modelResult modelEvictedState reason .postQuantum evicted.val hDirect hFull
    (by simpa [hBatchModel] using hEvictModel) hNonzeroModel hRetryModel
  exact ⟨hloop, hmodel, hState, hKey⟩

theorem concrete_post_quantum_receive_with_eviction_retry_matches_model
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState work evictedState : tacenta_triple.State)
    (modelState modelEvictedState : Model.Triple.State)
    (batch : Std.Usize) (batch1 evicted : Std.Usize)
    (realReason : tacenta_triple.TripleError)
    (modelReason : Model.Triple.ReceiveRefusal)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hAttempt : lifecycle.receive_attempt realState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Err realReason))
    (hFullReal : lifecycle.full_store realReason = ok (some lifecycle.FullStore.PostQuantum))
    (hClone : tacenta_triple.State.Insts.CoreCloneClone.clone realState = ok work)
    (hBatchReal : lifecycle.receive_shortfall lifecycle.FullStore.PostQuantum work composite =
      ok batch)
    (hDirect : Model.Triple.receiveDetailed modelState modelHeader
      modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput = .error modelReason)
    (hFull : Model.Lifecycle.fullStore modelReason = some .postQuantum)
    (hBatchModel : batch.val = Model.Lifecycle.receiveShortfall
      .postQuantum modelState modelComposite)
    (hEvictModel : Model.Triple.evictOldestPostQuantum modelState batch.val =
      (modelEvictedState, evicted.val))
    (hNonzero : evicted ≠ 0#usize)
    (hNonzeroModel : evicted.val ≠ 0)
    (hEvict : lifecycle.evict_for_retry work lifecycle.FullStore.PostQuantum batch =
      ok (evictedState, evicted))
    (hBatch : core.num.Usize.saturating_add batch batch = batch1)
    (hRetry : lifecycle.receive_attempt evictedState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok realResult))
    (hRetryModel : Model.Triple.receiveDetailed modelEvictedState modelHeader
      modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput = .ok modelResult)
    (hState : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realResult.1 modelResult.1)
    (hKey : Tacenta.SessionUnitTripleT3.keyOf realResult.2 = modelResult.2)
    (hReason : tripleReceiveRefusalOfReal realReason = some modelReason) :
    lifecycle.receive_with_eviction realState composite header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok realResult) ∧
      Model.Lifecycle.receiveWithEviction modelState modelComposite modelHeader
        modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput = .ok modelResult ∧
      Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        realResult.1 modelResult.1 ∧
      Tacenta.SessionUnitTripleT3.keyOf realResult.2 = modelResult.2 ∧
      Tacenta.UnitLifecycleT3.refusalOf (.Triple realReason) =
        Model.Lifecycle.tripleReceiveRefusalOf modelReason := by
  have hloop := concrete_post_quantum_retry_loop_matches_model_one_retry composite
    modelComposite header modelHeader dhOutRecv dhOutSend newDhsPub modelDhOutRecv
    modelDhOutSend modelNewDhsPub output modelOutput work evictedState modelState
    modelEvictedState batch batch1 evicted realReason modelReason realResult modelResult
    hDirect hFull hBatchModel hEvictModel hNonzero hNonzeroModel hEvict hBatch hRetry
    hRetryModel hState hKey
  obtain ⟨loopResult, hLoopCall, hLoopPost⟩ :=
    Std.WP.spec_imp_exists hloop.1
  have hLoop : lifecycle.receive_with_eviction_loop composite header dhOutRecv
      dhOutSend newDhsPub output lifecycle.FullStore.PostQuantum work batch realReason none =
      ok (realReason, some (core.result.Result.Ok realResult)) := by
    rw [hLoopPost] at hLoopCall
    exact hLoopCall
  have houter := concrete_receive_with_eviction_from_retry_loop realState work composite
    header dhOutRecv dhOutSend newDhsPub output realReason lifecycle.FullStore.PostQuantum
    batch realResult hAttempt hFullReal hClone hBatchReal hLoop
  exact ⟨houter, hloop.2.1, hloop.2.2.1, hloop.2.2.2,
    Tacenta.UnitLifecycleT3.tripleReceiveRefusalOfReal_sound hReason⟩

/-! The two full-store proofs above have the same public conclusion.  Keep
    that conclusion in one proposition so the enclosing lifecycle proof can
    select the generated store half once and then consume either branch
    without duplicating the Session-level result plumbing. -/
def AggregateReceiveCoreRefinement
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key) : Prop :=
  lifecycle.receive_with_eviction realState composite header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok realResult) ∧
    Model.Lifecycle.receiveWithEviction modelState modelComposite modelHeader
      modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput = .ok modelResult ∧
    Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realResult.1 modelResult.1 ∧
    Tacenta.SessionUnitTripleT3.keyOf realResult.2 = modelResult.2

def AggregateReceiveRetryRefinement
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realReason : tacenta_triple.TripleError)
    (modelReason : Model.Triple.ReceiveRefusal)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key) : Prop :=
  AggregateReceiveCoreRefinement composite modelComposite header modelHeader
    dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
    output modelOutput realState modelState realResult modelResult ∧
    Tacenta.UnitLifecycleT3.refusalOf (.Triple realReason) =
      Model.Lifecycle.tripleReceiveRefusalOf modelReason

/-! The direct Triple path has no full-store refusal to classify, but it feeds
    the same core result relation used by the retry path. -/
theorem aggregate_receive_core_refinement_of_direct
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hreal : tacenta_triple.State.receive realState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok realResult))
    (hmodel : Model.Triple.receive modelState modelHeader modelDhOutRecv modelDhOutSend
      modelNewDhsPub modelOutput = some modelResult)
    (hstate : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realResult.1 modelResult.1)
    (hkey : Tacenta.SessionUnitTripleT3.keyOf realResult.2 = modelResult.2) :
    AggregateReceiveCoreRefinement composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realResult modelResult := by
  exact ⟨concrete_receive_with_eviction_of_receive realState composite header
    dhOutRecv dhOutSend newDhsPub output realResult hreal,
    model_receive_with_eviction_of_receive modelState modelComposite modelHeader
      modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput modelResult hmodel,
    hstate, hkey⟩

/-! Match the concrete and model lifecycle partitions before exposing the
    branch-independent receive core.  The direct arm contains the raw Triple
    receive facts needed by `aggregate_receive_core_refinement_of_direct`; the
    retry arm contains the already-composed full-store adapter.  This keeps the
    branch choice tied to the actual generated/model results instead of
    allowing a caller to choose a convenient route independently. -/
def AggregateReceiveAlignedCase
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hreal : lifecycle.receive_with_eviction realState composite header
      dhOutRecv dhOutSend newDhsPub output = ok (.Ok realResult))
    (hmodel : Model.Lifecycle.receiveWithEviction modelState modelComposite
      modelHeader modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput =
      .ok modelResult) : Prop :=
  (∃ directReal directModel,
    tacenta_triple.State.receive realState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok directReal) ∧
    Model.Triple.receive modelState modelHeader modelDhOutRecv
      modelDhOutSend modelNewDhsPub modelOutput = some directModel ∧
    directReal = realResult ∧ directModel = modelResult ∧
    Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      directReal.1 directModel.1 ∧
    Tacenta.SessionUnitTripleT3.keyOf directReal.2 = directModel.2) ∨
  (∃ realReason modelReason,
    AggregateReceiveRetryRefinement composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realReason modelReason realResult
      modelResult)

theorem aggregate_receive_aligned_case_of_direct
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hreal : lifecycle.receive_with_eviction realState composite header
      dhOutRecv dhOutSend newDhsPub output = ok (.Ok realResult))
    (hmodel : Model.Lifecycle.receiveWithEviction modelState modelComposite
      modelHeader modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput =
      .ok modelResult)
    (hrealDirect : tacenta_triple.State.receive realState header dhOutRecv
      dhOutSend newDhsPub output = ok (.Ok realResult))
    (hmodelDirect : Model.Triple.receive modelState modelHeader modelDhOutRecv
      modelDhOutSend modelNewDhsPub modelOutput = some modelResult)
    (hstate : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realResult.1 modelResult.1)
    (hkey : Tacenta.SessionUnitTripleT3.keyOf realResult.2 = modelResult.2) :
    AggregateReceiveAlignedCase composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realResult modelResult hreal hmodel := by
  exact Or.inl ⟨realResult, modelResult, hrealDirect, hmodelDirect, rfl, rfl, hstate, hkey⟩

theorem aggregate_receive_aligned_case_of_direct_receive
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hrealDirect : tacenta_triple.State.receive realState header dhOutRecv
      dhOutSend newDhsPub output = ok (.Ok realResult))
    (hmodelDirect : Model.Triple.receive modelState modelHeader modelDhOutRecv
      modelDhOutSend modelNewDhsPub modelOutput = some modelResult)
    (hstate : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realResult.1 modelResult.1)
    (hkey : Tacenta.SessionUnitTripleT3.keyOf realResult.2 = modelResult.2) :
    AggregateReceiveAlignedCase composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realResult modelResult
      (concrete_receive_with_eviction_of_receive realState composite header
        dhOutRecv dhOutSend newDhsPub output realResult hrealDirect)
      (model_receive_with_eviction_of_receive modelState modelComposite modelHeader
        modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput modelResult hmodelDirect) := by
  exact aggregate_receive_aligned_case_of_direct composite modelComposite header modelHeader
    dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub output
    modelOutput realState modelState realResult modelResult
    (concrete_receive_with_eviction_of_receive realState composite header
      dhOutRecv dhOutSend newDhsPub output realResult hrealDirect)
    (model_receive_with_eviction_of_receive modelState modelComposite modelHeader
      modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput modelResult hmodelDirect)
    hrealDirect hmodelDirect hstate hkey

/-! A direct receive can be constructed from the discharged Triple contracts,
    rather than supplied as an already-composed lifecycle proposition.  The
    generated direct call is fed to the contract refinement theorem; its model
    result is then lifted through both lifecycle wrappers and indexed into the
    shared aggregate case. -/
theorem aggregate_receive_aligned_case_of_direct_contracts
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (hmac : Tacenta.SessionUnitT3.HmacAgrees)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hzr : Tacenta.SessionUnitT3.ZeroizingRoundTrips)
    (hvr : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hz96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.SessionUnitSpqrT3.VecRetainAgrees)
    (happ : Tacenta.SessionUnitSpqrT3.VecAppendAgrees)
    (hrm : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees)
    (hzs : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hopt : Tacenta.SessionUnitSpqrT1.OptionCloneTotal)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realState modelState)
    (hrecvKey : modelDhOutRecv = Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
    (hsendKey : modelDhOutSend = Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
    (hnewKey : modelNewDhsPub = Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
    (hmodelOutput : modelOutput = output.map Tacenta.SessionUnitTripleT3.spqrOutputOf)
    (mh : Model.State.Header)
    (hmodelHeader : modelHeader =
      { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val })
    (hheader : Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr mh)
    (hone : (modelState.classical.skipped.filter
      (fun x => x.1 == mh.dh && x.2.1 == mh.n)).length ≤ 1)
    (hs : max modelState.classical.skipped.length Model.State.maxSkippedStore +
      Model.State.maxSkip ≤ Usize.max)
    (hevents : modelState.classical.events + 1 < Std.U32.max)
    (hepoch : modelState.postQuantum.epoch + 1 < Std.U64.max)
    (hroom : modelState.postQuantum.chains.length + 2 < Usize.max)
    (hcb : ∀ p ∈ modelState.postQuantum.chains,
      p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ modelState.postQuantum.skipped,
      sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, output = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hskiproom : modelState.postQuantum.skipped.length +
      Model.SparseRatchet.maxSkip ≤ Usize.max)
    (hone2 : (modelState.postQuantum.skipped.filter
      (fun x => x.1 == header.epoch.val && x.2.1 == header.pq_n.val)).length ≤ 1)
    (hcounter : ∀ p ∈ modelState.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max)
    (hcall : tacenta_triple.State.receive realState header dhOutRecv dhOutSend
      newDhsPub output = ok (.Ok realResult)) :
    ∃ modelCandidate modelKey,
      ∃ hmodelDirect : Model.Triple.receive modelState modelHeader modelDhOutRecv
        modelDhOutSend modelNewDhsPub modelOutput = some (modelCandidate, modelKey),
      AggregateReceiveAlignedCase composite modelComposite header modelHeader
        dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
        output modelOutput realState modelState realResult (modelCandidate, modelKey)
        (concrete_receive_with_eviction_of_receive realState composite header
          dhOutRecv dhOutSend newDhsPub output realResult hcall)
        (model_receive_with_eviction_of_receive modelState modelComposite modelHeader
          modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput
          (modelCandidate, modelKey) hmodelDirect) := by
  subst modelHeader
  subst modelDhOutRecv
  subst modelDhOutSend
  subst modelNewDhsPub
  subst modelOutput
  obtain ⟨modelCandidate, modelKey, hmodelDirect, hstate, hkey⟩ :=
    triple_receive_success_from_contracts hmac hkdf hzr hvr hz96 hz64 hret happ hrm hzs hopt
      hrel header mh hheader dhOutRecv dhOutSend newDhsPub output hone hs hevents hepoch hroom
      hcb hsb hnewb hskiproom hone2 hcounter realResult.1 realResult.2 hcall
  refine ⟨modelCandidate, modelKey, ?_, ?_⟩
  · simpa using hmodelDirect
  exact aggregate_receive_aligned_case_of_direct_receive composite modelComposite header
    { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
    dhOutRecv dhOutSend newDhsPub (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
    (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
    (Tacenta.SessionUnitTripleT3.keyOf newDhsPub) output
    (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf)
    realState modelState realResult (modelCandidate, modelKey)
    hcall hmodelDirect hstate hkey

theorem aggregate_receive_aligned_case_of_retry_refinement
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realReason : tacenta_triple.TripleError)
    (modelReason : Model.Triple.ReceiveRefusal)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hretry : AggregateReceiveRetryRefinement composite modelComposite header
      modelHeader dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend
      modelNewDhsPub output modelOutput realState modelState realReason modelReason
      realResult modelResult) :
    AggregateReceiveAlignedCase composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realResult modelResult
      hretry.1.1 hretry.1.2.1 := by
  exact Or.inr ⟨realReason, modelReason, hretry⟩

theorem aggregate_receive_aligned_case_of_retry
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hreal : lifecycle.receive_with_eviction realState composite header
      dhOutRecv dhOutSend newDhsPub output = ok (.Ok realResult))
    (hmodel : Model.Lifecycle.receiveWithEviction modelState modelComposite
      modelHeader modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput =
      .ok modelResult)
    (realReason : tacenta_triple.TripleError)
    (modelReason : Model.Triple.ReceiveRefusal)
    (hretry : AggregateReceiveRetryRefinement composite modelComposite header
      modelHeader dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend
      modelNewDhsPub output modelOutput realState modelState realReason modelReason
      realResult modelResult) :
    AggregateReceiveAlignedCase composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realResult modelResult hreal hmodel := by
  exact Or.inr ⟨realReason, modelReason, hretry⟩

theorem aggregate_receive_core_refinement_of_aligned_success_cases
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hreal : lifecycle.receive_with_eviction realState composite header
      dhOutRecv dhOutSend newDhsPub output = ok (.Ok realResult))
    (hmodel : Model.Lifecycle.receiveWithEviction modelState modelComposite
      modelHeader modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput =
      .ok modelResult)
    (hcase : AggregateReceiveAlignedCase composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realResult modelResult hreal hmodel) :
    AggregateReceiveCoreRefinement composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realResult modelResult := by
  unfold AggregateReceiveAlignedCase at hcase
  rcases hcase with hdirect | hretry
  · obtain ⟨directReal, directModel, hrealDirect, hmodelDirect, hrealEq,
      hmodelEq, hstate, hkey⟩ := hdirect
    subst directReal
    subst directModel
    exact aggregate_receive_core_refinement_of_direct composite modelComposite header
      modelHeader dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend
      modelNewDhsPub output modelOutput realState modelState realResult modelResult
      hrealDirect hmodelDirect hstate hkey
  · obtain ⟨_, _, haggregate⟩ := hretry
    exact haggregate.1

/-! Select the branch reported by the generated `full_store` classifier.  The
    branch callbacks are deliberately supplied by the concrete classical and
    post-quantum adapters above; this theorem only performs the shared
    elimination and exposes their common result to the public decrypt route. -/
theorem aggregate_receive_retry_refinement_of_full_store
    (half : lifecycle.FullStore)
    (realReason : tacenta_triple.TripleError)
    (hFullReal : lifecycle.full_store realReason = ok (some half))
    (hclassical : half = lifecycle.FullStore.Classical →
      lifecycle.full_store realReason = ok (some lifecycle.FullStore.Classical) →
      AggregateReceiveRetryRefinement composite modelComposite header modelHeader
        dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
        output modelOutput realState modelState realReason modelReason realResult modelResult)
    (hpostQuantum : half = lifecycle.FullStore.PostQuantum →
      lifecycle.full_store realReason = ok (some lifecycle.FullStore.PostQuantum) →
      AggregateReceiveRetryRefinement composite modelComposite header modelHeader
        dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
        output modelOutput realState modelState realReason modelReason realResult modelResult) :
    AggregateReceiveRetryRefinement composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realReason modelReason realResult modelResult := by
  cases half with
  | Classical => exact hclassical rfl hFullReal
  | PostQuantum => exact hpostQuantum rfl hFullReal

/-! Reattach the shared full-store adapter to the indexed lifecycle case.  The
    caller supplies the leaf-specific classical and post-quantum retry proofs,
    while this theorem performs the only branch elimination and keeps the
    resulting `StateRefines` witness tied to the exact successful calls. -/
theorem aggregate_receive_aligned_case_of_full_store_retry
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realReason : tacenta_triple.TripleError)
    (modelReason : Model.Triple.ReceiveRefusal)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hreal : lifecycle.receive_with_eviction realState composite header
      dhOutRecv dhOutSend newDhsPub output = ok (.Ok realResult))
    (hmodel : Model.Lifecycle.receiveWithEviction modelState modelComposite
      modelHeader modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput =
      .ok modelResult)
    (half : lifecycle.FullStore)
    (hFullReal : lifecycle.full_store realReason = ok (some half))
    (hclassical : half = lifecycle.FullStore.Classical →
      lifecycle.full_store realReason = ok (some lifecycle.FullStore.Classical) →
      AggregateReceiveRetryRefinement composite modelComposite header modelHeader
        dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
        output modelOutput realState modelState realReason modelReason realResult
        modelResult)
    (hpostQuantum : half = lifecycle.FullStore.PostQuantum →
      lifecycle.full_store realReason = ok (some lifecycle.FullStore.PostQuantum) →
      AggregateReceiveRetryRefinement composite modelComposite header modelHeader
        dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
        output modelOutput realState modelState realReason modelReason realResult
        modelResult) :
    AggregateReceiveAlignedCase composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realResult modelResult hreal hmodel := by
  have hretry := aggregate_receive_retry_refinement_of_full_store
    (composite := composite) (modelComposite := modelComposite) (header := header)
    (modelHeader := modelHeader) (dhOutRecv := dhOutRecv) (dhOutSend := dhOutSend)
    (newDhsPub := newDhsPub) (modelDhOutRecv := modelDhOutRecv)
    (modelDhOutSend := modelDhOutSend) (modelNewDhsPub := modelNewDhsPub)
    (output := output) (modelOutput := modelOutput) (realState := realState)
    (modelState := modelState) (modelReason := modelReason)
    (realResult := realResult) (modelResult := modelResult) half realReason hFullReal
    hclassical hpostQuantum
  exact aggregate_receive_aligned_case_of_retry composite modelComposite header
    modelHeader dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend
    modelNewDhsPub output modelOutput realState modelState realResult modelResult
    hreal hmodel realReason modelReason hretry

/-! The model-side half of the successful receive is kept separate from the
concrete adapter above.  This is the exact result that the aggregate T3
composition will consume; in particular, it leaves the conditional
ratchet-private update visible instead of hiding it behind an existential. -/

theorem decrypt_ratchet_success_model_result
    (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (model : Model.Lifecycle.Session) (message : Slice Std.U8)
    (modelComposite : Model.CompositeHeader.Composite)
    (ciphertext modelPlaintext : Bytes)
    (modelDhOutRecv draw modelDhOutSend : Model.Lifecycle.Key)
    (modelTripleCandidate : Model.Triple.State)
    (modelMk : Model.Lifecycle.Key)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, ciphertext))
    (hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
      some modelDhOutRecv)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hmodelSecond : oracle.dhAgree draw modelComposite.dh =
      some modelDhOutSend)
    (hmodelTriple : Model.Lifecycle.receiveWithEviction model.triple modelComposite
      (Model.Lifecycle.tripleHeaderOf modelComposite) modelDhOutRecv modelDhOutSend
      (oracle.dhPublic draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1) =
        .ok (modelTripleCandidate, modelMk))
    (hmodelAead : oracle.aeadOpen
      (Model.State.messageKeys modelMk .tacenta).1
      (Model.State.messageKeys modelMk .tacenta).2.1
      (Model.State.messageKeys modelMk .tacenta).2.2
      ciphertext
      (Model.Messages.concatAd model.identityAd
        (Model.CompositeHeader.encode modelComposite)) = some modelPlaintext) :
    Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session :=
          { model with
            triple := modelTripleCandidate
            braid := (Model.Braid.receive oracle.braidKem model.braid
              (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2
            ratchetPrivate :=
              if modelTripleCandidate.classical.dhsPub == model.triple.classical.dhsPub then
                model.ratchetPrivate else draw }
        result := .ok modelPlaintext
        oracle := oracleNext } := by
  simp [Model.Lifecycle.decryptRatchet, hready, hdecodeModel, hmodelFirst,
    hmodelDraw, hmodelSecond, hmodelTriple, hmodelAead]

/-- The aggregate model result can consume the direct Triple receive fact
returned by the contract bridge; the lifecycle retry policy is discharged by
its successful-direct-result lemma. -/
theorem decrypt_ratchet_success_model_result_from_direct_triple
    (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (model : Model.Lifecycle.Session) (message : Slice Std.U8)
    (modelComposite : Model.CompositeHeader.Composite)
    (ciphertext modelPlaintext : Bytes)
    (modelDhOutRecv draw modelDhOutSend : Model.Lifecycle.Key)
    (modelTripleCandidate : Model.Triple.State)
    (modelMk : Model.Lifecycle.Key)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, ciphertext))
    (hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
      some modelDhOutRecv)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hmodelSecond : oracle.dhAgree draw modelComposite.dh = some modelDhOutSend)
    (hmodelReceive : Model.Triple.receive model.triple
      (Model.Lifecycle.tripleHeaderOf modelComposite)
      modelDhOutRecv modelDhOutSend (oracle.dhPublic draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1) =
      some (modelTripleCandidate, modelMk))
    (hmodelAead : oracle.aeadOpen
      (Model.State.messageKeys modelMk .tacenta).1
      (Model.State.messageKeys modelMk .tacenta).2.1
      (Model.State.messageKeys modelMk .tacenta).2.2
      ciphertext
      (Model.Messages.concatAd model.identityAd
        (Model.CompositeHeader.encode modelComposite)) = some modelPlaintext) :
    Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session :=
          { model with
            triple := modelTripleCandidate
            braid := (Model.Braid.receive oracle.braidKem model.braid
              (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2
            ratchetPrivate :=
              if modelTripleCandidate.classical.dhsPub == model.triple.classical.dhsPub then
                model.ratchetPrivate else draw }
        result := .ok modelPlaintext
        oracle := oracleNext } := by
  have hmodelTriple := model_receive_with_eviction_of_receive model.triple modelComposite
    (Model.Lifecycle.tripleHeaderOf modelComposite) modelDhOutRecv modelDhOutSend
    (oracle.dhPublic draw)
    (Model.Lifecycle.sparseOutputOf
      (Model.Braid.receive oracle.braidKem model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1)
    (modelTripleCandidate, modelMk) hmodelReceive
  exact decrypt_ratchet_success_model_result view oracle oracleNext model message modelComposite
    ciphertext modelPlaintext modelDhOutRecv draw modelDhOutSend modelTripleCandidate modelMk
    hready hdecodeModel hmodelFirst hmodelDraw hmodelSecond hmodelTriple hmodelAead

/-! The concrete and model success states use the same public-key branch, but
the translated state carries byte arrays while the model carries `Key`s.  This
small bridge makes that branch explicit for the aggregate receive theorem. -/

theorem receive_success_session_refines
    (dh : DhView) (K : Model.Braid.Kem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (realTripleCandidate : tacenta_triple.State)
    (realBraidCandidate : tacenta_braid.Braid)
    (candidatePrivate : tacenta_boundary.dh.PrivateKey)
    (draw : Model.Lifecycle.Key)
    (modelTripleCandidate : Model.Triple.State)
    (modelBraidCandidate : Model.Braid.BraidState)
    (hrel : SessionRefines dh K real model)
    (htriple : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realTripleCandidate modelTripleCandidate)
    (hbraid : Tacenta.SessionUnitBraidT3.StateRefines K
      realBraidCandidate.state modelBraidCandidate)
    (hprivate : dh.privateKey candidatePrivate = draw) :
    SessionRefines dh K
      { { real with triple := realTripleCandidate, braid := realBraidCandidate } with
        ratchet_private :=
          if realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
            real.ratchet_private else candidatePrivate }
      { model with
        triple := modelTripleCandidate
        braid := modelBraidCandidate
        ratchetPrivate :=
          if modelTripleCandidate.classical.dhsPub == model.triple.classical.dhsPub then
            model.ratchetPrivate else draw } := by
  have hsameModel :
      modelTripleCandidate.classical.dhsPub = model.triple.classical.dhsPub ↔
      realTripleCandidate.classical.dhs_pub = real.triple.classical.dhs_pub := by
    constructor
    · intro h
      have hc := congrArg (fun s => s.dhsPub) htriple.1
      have hp := congrArg (fun s => s.dhsPub) hrel.triple.1
      change Tacenta.SessionUnitT3.keyOf realTripleCandidate.classical.dhs_pub =
        modelTripleCandidate.classical.dhsPub at hc
      change Tacenta.SessionUnitT3.keyOf real.triple.classical.dhs_pub =
        model.triple.classical.dhsPub at hp
      have hk : Tacenta.SessionUnitT3.keyOf realTripleCandidate.classical.dhs_pub =
          Tacenta.SessionUnitT3.keyOf real.triple.classical.dhs_pub := by
        rw [hc, hp]
        exact h
      exact (Tacenta.SessionUnitT3.keyOf_eq_iff _ _).mp hk
    · intro h
      have hc := congrArg (fun s => s.dhsPub) htriple.1
      have hp := congrArg (fun s => s.dhsPub) hrel.triple.1
      change Tacenta.SessionUnitT3.keyOf realTripleCandidate.classical.dhs_pub =
        modelTripleCandidate.classical.dhsPub at hc
      change Tacenta.SessionUnitT3.keyOf real.triple.classical.dhs_pub =
        model.triple.classical.dhsPub at hp
      have hk := congrArg Tacenta.SessionUnitT3.keyOf h
      calc
        modelTripleCandidate.classical.dhsPub =
            Tacenta.SessionUnitT3.keyOf realTripleCandidate.classical.dhs_pub := hc.symm
        _ = Tacenta.SessionUnitT3.keyOf real.triple.classical.dhs_pub := hk
        _ = model.triple.classical.dhsPub := hp
  by_cases hsame : realTripleCandidate.classical.dhs_pub =
      real.triple.classical.dhs_pub
  · have hsameModel' := hsameModel.mpr hsame
    simpa [hsame, hsameModel'] using
      (receive_success_next_refines_same dh K real model realTripleCandidate
        realBraidCandidate modelTripleCandidate modelBraidCandidate hrel htriple hbraid)
  · have hsameModel' : ¬ modelTripleCandidate.classical.dhsPub =
        model.triple.classical.dhsPub := fun h => hsame (hsameModel.mp h)
    simpa [hsame, hsameModel'] using
      (receive_success_next_refines_rotated dh K real model realTripleCandidate
        realBraidCandidate candidatePrivate modelTripleCandidate modelBraidCandidate
        draw hrel htriple hbraid hprivate)

/-! Final bookkeeping for the successful receive branch.  The concrete and
model computations are supplied by the branch adapters; this theorem supplies
the missing `StepRefines` package and makes the successor relation above part
of the result rather than a caller-side assertion. -/

theorem decrypt_ratchet_success_step_from_results {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (plaintext : alloc.vec.Vec Std.U8) (modelPlaintext : Bytes)
    (realTripleCandidate : tacenta_triple.State)
    (realBraidCandidate : tacenta_braid.Braid)
    (candidatePrivate : tacenta_boundary.dh.PrivateKey)
    (draw : Model.Lifecycle.Key)
    (modelTripleCandidate : Model.Triple.State)
    (modelBraidCandidate : Model.Braid.BraidState)
    (hrel : SessionRefines dh K real model)
    (hreal : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext,
        { { real with triple := realTripleCandidate, braid := realBraidCandidate } with
          ratchet_private :=
            if realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
              real.ratchet_private else candidatePrivate }, rngNext))
    (hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session :=
          { model with
            triple := modelTripleCandidate
            braid := modelBraidCandidate
            ratchetPrivate :=
              if modelTripleCandidate.classical.dhsPub == model.triple.classical.dhsPub then
                model.ratchetPrivate else draw }
        result := .ok modelPlaintext
        oracle := oracleNext })
    (htriple : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      realTripleCandidate modelTripleCandidate)
    (hbraid : Tacenta.SessionUnitBraidT3.StateRefines K
      realBraidCandidate.state modelBraidCandidate)
    (hprivate : dh.privateKey candidatePrivate = draw)
    (hbytes : vecOf plaintext = modelPlaintext)
    (htrace : trace rngNext = oracleNext.draws) :
    StepRefines trace dh K
      (.Ok plaintext,
        { { real with triple := realTripleCandidate, braid := realBraidCandidate } with
          ratchet_private :=
            if realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
              real.ratchet_private else candidatePrivate }, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  have hnext := receive_success_session_refines dh K real model
    realTripleCandidate realBraidCandidate candidatePrivate draw
    modelTripleCandidate modelBraidCandidate hrel htriple hbraid hprivate
  obtain ⟨output, hcall, hstep⟩ := decrypt_ratchet_success_step_refines
    rngCore cryptoRng trace dh K view oracle
    oracleNext real model message rng rngNext plaintext modelPlaintext
    ({ { real with triple := realTripleCandidate, braid := realBraidCandidate } with
      ratchet_private :=
        if realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
          real.ratchet_private else candidatePrivate })
    ({ model with
      triple := modelTripleCandidate
      braid := modelBraidCandidate
      ratchetPrivate :=
        if modelTripleCandidate.classical.dhsPub == model.triple.classical.dhsPub then
      model.ratchetPrivate else draw })
    hreal hmodel hbytes hnext htrace
  have hout : output =
      (.Ok plaintext,
        { { real with triple := realTripleCandidate, braid := realBraidCandidate } with
          ratchet_private :=
            if realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
              real.ratchet_private else candidatePrivate }, rngNext) := by
    have heq := hreal.symm.trans hcall
    injection heq with htarget
    exact htarget.symm
  subst output
  exact hstep

/-! The aggregate core result is the Triple part of the public decrypt
    success route.  This adapter projects its `StateRefines` witness into the
    existing Session `StepRefines` constructor, so callers no longer have to
    unpack the classical/post-quantum branch result by hand. -/
theorem decrypt_ratchet_success_step_from_aggregate_core {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (plaintext : alloc.vec.Vec Std.U8) (modelPlaintext : Bytes)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realTripleCandidate : tacenta_triple.State)
    (realBraidCandidate : tacenta_braid.Braid)
    (candidatePrivate : tacenta_boundary.dh.PrivateKey)
    (draw : Model.Lifecycle.Key)
    (modelTripleCandidate : Model.Triple.State)
    (modelBraidCandidate : Model.Braid.BraidState)
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realMk : Array Std.U8 32#usize) (modelMk : Model.Lifecycle.Key)
    (haggregate : AggregateReceiveCoreRefinement composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState
      (realTripleCandidate, realMk) (modelTripleCandidate, modelMk))
    (hrel : SessionRefines dh K real model)
    (hreal : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext,
        { { real with triple := realTripleCandidate, braid := realBraidCandidate } with
          ratchet_private :=
            if realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
              real.ratchet_private else candidatePrivate }, rngNext))
    (hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session :=
          { model with
            triple := modelTripleCandidate
            braid := modelBraidCandidate
            ratchetPrivate :=
              if modelTripleCandidate.classical.dhsPub == model.triple.classical.dhsPub then
                model.ratchetPrivate else draw }
        result := .ok modelPlaintext
        oracle := oracleNext })
    (hbraid : Tacenta.SessionUnitBraidT3.StateRefines K
      realBraidCandidate.state modelBraidCandidate)
    (hprivate : dh.privateKey candidatePrivate = draw)
    (hbytes : vecOf plaintext = modelPlaintext)
    (htrace : trace rngNext = oracleNext.draws) :
    StepRefines trace dh K
      (.Ok plaintext,
        { { real with triple := realTripleCandidate, braid := realBraidCandidate } with
          ratchet_private :=
            if realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
              real.ratchet_private else candidatePrivate }, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  exact decrypt_ratchet_success_step_from_results rngCore cryptoRng trace dh K view
    oracle oracleNext real model message rng rngNext plaintext modelPlaintext
    realTripleCandidate realBraidCandidate candidatePrivate draw modelTripleCandidate
    modelBraidCandidate hrel hreal hmodel haggregate.2.2.1 hbraid hprivate hbytes htrace


/-! The aggregate retry result is the Triple part of the public decrypt
    success route.  This adapter projects its `StateRefines` witness into the
    existing Session `StepRefines` constructor, so callers no longer have to
    unpack the classical/post-quantum branch result by hand. -/
theorem decrypt_ratchet_success_step_from_aggregate_retry {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (plaintext : alloc.vec.Vec Std.U8) (modelPlaintext : Bytes)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realTripleCandidate : tacenta_triple.State)
    (realBraidCandidate : tacenta_braid.Braid)
    (candidatePrivate : tacenta_boundary.dh.PrivateKey)
    (draw : Model.Lifecycle.Key)
    (modelTripleCandidate : Model.Triple.State)
    (modelBraidCandidate : Model.Braid.BraidState)
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realReason : tacenta_triple.TripleError)
    (modelReason : Model.Triple.ReceiveRefusal)
    (realMk : Array Std.U8 32#usize) (modelMk : Model.Lifecycle.Key)
    (haggregate : AggregateReceiveRetryRefinement composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realReason modelReason
      (realTripleCandidate, realMk) (modelTripleCandidate, modelMk))
    (hrel : SessionRefines dh K real model)
    (hreal : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext,
        { { real with triple := realTripleCandidate, braid := realBraidCandidate } with
          ratchet_private :=
            if realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
              real.ratchet_private else candidatePrivate }, rngNext))
    (hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session :=
          { model with
            triple := modelTripleCandidate
            braid := modelBraidCandidate
            ratchetPrivate :=
              if modelTripleCandidate.classical.dhsPub == model.triple.classical.dhsPub then
                model.ratchetPrivate else draw }
        result := .ok modelPlaintext
        oracle := oracleNext })
    (hbraid : Tacenta.SessionUnitBraidT3.StateRefines K
      realBraidCandidate.state modelBraidCandidate)
    (hprivate : dh.privateKey candidatePrivate = draw)
    (hbytes : vecOf plaintext = modelPlaintext)
    (htrace : trace rngNext = oracleNext.draws) :
    StepRefines trace dh K
      (.Ok plaintext,
        { { real with triple := realTripleCandidate, braid := realBraidCandidate } with
          ratchet_private :=
            if realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
              real.ratchet_private else candidatePrivate }, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  exact decrypt_ratchet_success_step_from_results rngCore cryptoRng trace dh K view
    oracle oracleNext real model message rng rngNext plaintext modelPlaintext
    realTripleCandidate realBraidCandidate candidatePrivate draw modelTripleCandidate
    modelBraidCandidate hrel hreal hmodel haggregate.1.2.2.1 hbraid hprivate hbytes htrace


theorem decrypt_ratchet_success_step_from_aligned_receive_cases {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (plaintext : alloc.vec.Vec Std.U8) (modelPlaintext : Bytes)
    (realState : tacenta_triple.State)
    (realTripleCandidate : tacenta_triple.State)
    (realBraidCandidate : tacenta_braid.Braid)
    (candidatePrivate : tacenta_boundary.dh.PrivateKey)
    (draw : Model.Lifecycle.Key)
    (modelTripleCandidate : Model.Triple.State)
    (modelBraidCandidate : Model.Braid.BraidState)
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realMk : Array Std.U8 32#usize) (modelMk : Model.Lifecycle.Key)
    (hreceiveReal : lifecycle.receive_with_eviction realState composite header
      dhOutRecv dhOutSend newDhsPub output =
      ok (.Ok (realTripleCandidate, realMk)))
    (hreceiveModel : Model.Lifecycle.receiveWithEviction model.triple modelComposite
      modelHeader modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput =
      .ok (modelTripleCandidate, modelMk))
    (hcase : AggregateReceiveAlignedCase composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState model.triple
      (realTripleCandidate, realMk) (modelTripleCandidate, modelMk)
      hreceiveReal hreceiveModel)
    (hrel : SessionRefines dh K real model)
    (hreal : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext,
        { { real with triple := realTripleCandidate, braid := realBraidCandidate } with
          ratchet_private :=
            if realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
              real.ratchet_private else candidatePrivate }, rngNext))
    (hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session :=
          { model with
            triple := modelTripleCandidate
            braid := modelBraidCandidate
            ratchetPrivate :=
              if modelTripleCandidate.classical.dhsPub == model.triple.classical.dhsPub then
                model.ratchetPrivate else draw }
        result := .ok modelPlaintext
        oracle := oracleNext })
    (hbraid : Tacenta.SessionUnitBraidT3.StateRefines K
      realBraidCandidate.state modelBraidCandidate)
    (hprivate : dh.privateKey candidatePrivate = draw)
    (hbytes : vecOf plaintext = modelPlaintext)
    (htrace : trace rngNext = oracleNext.draws) :
    StepRefines trace dh K
      (.Ok plaintext,
        { { real with triple := realTripleCandidate, braid := realBraidCandidate } with
          ratchet_private :=
            if realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
              real.ratchet_private else candidatePrivate }, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  unfold AggregateReceiveAlignedCase at hcase
  rcases hcase with hdirect | hretry
  · have haggregate := aggregate_receive_core_refinement_of_aligned_success_cases
      composite modelComposite header modelHeader dhOutRecv dhOutSend newDhsPub
      modelDhOutRecv modelDhOutSend modelNewDhsPub output modelOutput
      realState model.triple (realTripleCandidate, realMk)
      (modelTripleCandidate, modelMk) hreceiveReal hreceiveModel
      (Or.inl hdirect)
    exact decrypt_ratchet_success_step_from_aggregate_core rngCore cryptoRng trace dh K view
      oracle oracleNext real model message rng rngNext plaintext modelPlaintext
      realState model.triple realTripleCandidate realBraidCandidate candidatePrivate draw modelTripleCandidate
      modelBraidCandidate composite modelComposite header modelHeader dhOutRecv dhOutSend
      newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub output modelOutput realMk modelMk
      haggregate hrel hreal hmodel hbraid hprivate hbytes htrace
  · obtain ⟨realReason, modelReason, haggregate⟩ := hretry
    exact decrypt_ratchet_success_step_from_aggregate_retry rngCore cryptoRng trace dh K view
      oracle oracleNext real model message rng rngNext plaintext modelPlaintext
      realState model.triple realTripleCandidate realBraidCandidate candidatePrivate draw modelTripleCandidate
      modelBraidCandidate composite modelComposite header modelHeader dhOutRecv dhOutSend
      newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub output modelOutput
      realReason modelReason realMk modelMk haggregate hrel hreal hmodel hbraid
      hprivate hbytes htrace


/-! Model-side success facts are kept separate from the generated prefix.  The
    record is exactly the premise set of the model lifecycle success theorem,
    so a caller cannot replace one model draw or successor with an unrelated
    value. -/
structure InitialRatchetModelSuccessFacts
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleNext : Model.Lifecycle.Oracle) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) : Type where
  modelComposite : Model.CompositeHeader.Composite
  ciphertext : Bytes
  modelPlaintext : Bytes
  modelDhOutRecv : Model.Lifecycle.Key
  draw : Model.Lifecycle.Key
  modelDhOutSend : Model.Lifecycle.Key
  modelTripleCandidate : Model.Triple.State
  modelMk : Model.Lifecycle.Key
  hready : Model.Lifecycle.agreementFailed model = false
  hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
    .ok (modelComposite, ciphertext)
  hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
    some modelDhOutRecv
  hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext)
  hmodelSecond : oracle.dhAgree draw modelComposite.dh = some modelDhOutSend
  hmodelTriple : Model.Lifecycle.receiveWithEviction model.triple modelComposite
    (Model.Lifecycle.tripleHeaderOf modelComposite) modelDhOutRecv modelDhOutSend
    (oracle.dhPublic draw)
    (Model.Lifecycle.sparseOutputOf
      (Model.Braid.receive oracle.braidKem model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1) =
    .ok (modelTripleCandidate, modelMk)
  hmodelAead : oracle.aeadOpen
    (Model.State.messageKeys modelMk .tacenta).1
    (Model.State.messageKeys modelMk .tacenta).2.1
    (Model.State.messageKeys modelMk .tacenta).2.2
    ciphertext
    (Model.Messages.concatAd model.identityAd
      (Model.CompositeHeader.encode modelComposite)) = some modelPlaintext

/-! Invert the pure model success result into the exact facts consumed by the
    translated success splice.  The case split follows the model's actual
    decoder, Braid, DH, randomness, Triple and AEAD matches; a successful
    result makes every refusal arm impossible and exposes the corresponding
    equations without choosing an unrelated model candidate. -/
theorem initial_ratchet_model_success_facts_of_result
    (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (model modelNext : Model.Lifecycle.Session) (message : Slice Std.U8)
    (modelPlaintext : Bytes)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session := modelNext, result := .ok modelPlaintext, oracle := oracleNext}) :
    Nonempty (InitialRatchetModelSuccessFacts view oracle oracleNext model message) := by
  simp only [Model.Lifecycle.decryptRatchet, hready] at hmodel
  cases hd : Model.CompositeHeader.decodeDetailed (sliceOf message) with
  | error e => simp [hd] at hmodel
  | ok pair =>
    obtain ⟨composite, ciphertext⟩ := pair
    cases hb : Model.Braid.receive oracle.braidKem model.braid
      (Model.Lifecycle.braidMessageOf view model.braid composite) with
    | mk epoch rest =>
      cases hr : oracle.dhAgree model.ratchetPrivate composite.dh with
      | none => simp [hd, hb, hr] at hmodel
      | some dhOutRecv =>
        cases hdraw : Model.Lifecycle.random32 oracle with
        | none => simp [hd, hb, hr, hdraw] at hmodel
        | some pair =>
          obtain ⟨candidatePrivate, oracleNext'⟩ := pair
          cases hs : oracle.dhAgree candidatePrivate composite.dh with
          | none => simp [hd, hb, hr, hdraw, hs] at hmodel
          | some dhOutSend =>
            cases ht : Model.Lifecycle.receiveWithEviction model.triple composite
              (Model.Lifecycle.tripleHeaderOf composite) dhOutRecv dhOutSend
              (oracle.dhPublic candidatePrivate) (Model.Lifecycle.sparseOutputOf rest.1) with
            | error e => simp [hd, hb, hr, hdraw, hs, ht] at hmodel
            | ok pair =>
              obtain ⟨tripleCandidate, messageKey⟩ := pair
              cases ha : oracle.aeadOpen
                (Model.State.messageKeys messageKey .tacenta).1
                (Model.State.messageKeys messageKey .tacenta).2.1
                (Model.State.messageKeys messageKey .tacenta).2.2 ciphertext
                (Model.Messages.concatAd model.identityAd
                  (Model.CompositeHeader.encode composite)) with
              | none => simp [hd, hb, hr, hdraw, hs, ht, ha] at hmodel
              | some plaintext =>
                simp [hd, hb, hr, hdraw, hs, ht, ha] at hmodel
                have horacle : oracleNext' = oracleNext := hmodel.2.2
                subst oracleNext'
                let facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message := {
                  modelComposite := composite,
                  ciphertext := ciphertext,
                  modelPlaintext := modelPlaintext,
                  modelDhOutRecv := dhOutRecv,
                  draw := candidatePrivate,
                  modelDhOutSend := dhOutSend,
                  modelTripleCandidate := tripleCandidate,
                  modelMk := messageKey,
                  hready := hready,
                  hdecodeModel := hd,
                  hmodelFirst := hr,
                  hmodelDraw := hdraw,
                  hmodelSecond := hs,
                  hmodelTriple := by simpa [hb] using ht,
                  hmodelAead := by simpa [hmodel.2.1] using ha }
                exact ⟨facts⟩

theorem initial_ratchet_model_success_result_of_facts
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message) :
    Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session :=
          { model with
            triple := facts.modelTripleCandidate
            braid := (Model.Braid.receive oracle.braidKem model.braid
              (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.2
            ratchetPrivate :=
              if facts.modelTripleCandidate.classical.dhsPub == model.triple.classical.dhsPub then
                model.ratchetPrivate else facts.draw }
        result := .ok facts.modelPlaintext
        oracle := oracleNext } := by
  exact decrypt_ratchet_success_model_result view oracle oracleNext model message
    facts.modelComposite facts.ciphertext facts.modelPlaintext facts.modelDhOutRecv
    facts.draw facts.modelDhOutSend facts.modelTripleCandidate facts.modelMk
    facts.hready facts.hdecodeModel facts.hmodelFirst facts.hmodelDraw facts.hmodelSecond
    facts.hmodelTriple facts.hmodelAead

theorem initial_ratchet_model_success_result_of_direct_receive
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (hmodelReceive : Model.Triple.receive model.triple
      (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
      facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1) =
      some (facts.modelTripleCandidate, facts.modelMk)) :
    Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session :=
          { model with
            triple := facts.modelTripleCandidate
            braid := (Model.Braid.receive oracle.braidKem model.braid
              (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.2
            ratchetPrivate :=
              if facts.modelTripleCandidate.classical.dhsPub == model.triple.classical.dhsPub then
                model.ratchetPrivate else facts.draw }
        result := .ok facts.modelPlaintext
        oracle := oracleNext } := by
  have hmodelTriple := model_receive_with_eviction_of_receive model.triple facts.modelComposite
    (Model.Lifecycle.tripleHeaderOf facts.modelComposite) facts.modelDhOutRecv
    facts.modelDhOutSend (oracle.dhPublic facts.draw)
    (Model.Lifecycle.sparseOutputOf
      (Model.Braid.receive oracle.braidKem model.braid
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
    (facts.modelTripleCandidate, facts.modelMk) hmodelReceive
  exact decrypt_ratchet_success_model_result view oracle oracleNext model message
    facts.modelComposite facts.ciphertext facts.modelPlaintext facts.modelDhOutRecv
    facts.draw facts.modelDhOutSend facts.modelTripleCandidate facts.modelMk facts.hready
    facts.hdecodeModel facts.hmodelFirst facts.hmodelDraw facts.hmodelSecond hmodelTriple
    facts.hmodelAead

/-! The generated success inversion is kept as a typed record so the later
    model/contract splice consumes facts from this exact computation. -/
structure InitialRatchetSuccessPrefix {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) : Type where
  decoded : tacenta_wire.DecodedMessage
  m : tacenta_braid.Msg
  receivedEpoch : Std.U64
  output : Option tacenta_braid.Output
  braidCandidate : tacenta_braid.Braid
  sparseOutput : Option tacenta_spqr.Output
  peer : tacenta_boundary.dh.PublicKeyBytes
  recvSecret : Array Std.U8 32#usize
  wrappedRecv : zeroize.Zeroizing (Array Std.U8 32#usize)
  candidateBytes : Array Std.U8 32#usize
  rng1 : R
  candidatePrivate : tacenta_boundary.dh.PrivateKey
  sendSecret : Array Std.U8 32#usize
  wrappedSend : zeroize.Zeroizing (Array Std.U8 32#usize)
  before : Array Std.U8 32#usize
  realHeader : tacenta_triple.Header
  candidatePublic : tacenta_boundary.dh.PublicKeyBytes
  newPublicBytes : Array Std.U8 32#usize
  realTripleCandidate : tacenta_triple.State
  realMk : Array Std.U8 32#usize
  wrappedMk : zeroize.Zeroizing (Array Std.U8 32#usize)
  realKeys : Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize
  wrappedKeys : zeroize.Zeroizing
    (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize)
  aeadPlaintext : alloc.vec.Vec Std.U8
  realAd : alloc.vec.Vec Std.U8
  hdecode : tacenta_wire.decode_message message = ok (.Ok decoded)
  hmessage : lifecycle.msg_of decoded.header = ok m
  hreceive : tacenta_braid.Braid.receive real.braid m =
    ok (receivedEpoch, output, braidCandidate)
  hsparse : RealSparseConversion output sparseOutput
  hpeer : tacenta_boundary.dh.PublicKeyBytes.from_bytes decoded.header.dh = ok peer
  hfirst : tacenta_boundary.dh.PrivateKey.agree real.ratchet_private peer =
    ok (some recvSecret)
  hwrapRecv : zeroize.Zeroizing.new
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) recvSecret = ok wrappedRecv
  hderefRecv : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedRecv = ok recvSecret
  hrandom : lifecycle.random_secret rngCore cryptoRng rng = ok (candidateBytes, rng1)
  hcandidate : tacenta_boundary.dh.PrivateKey.from_bytes candidateBytes = ok candidatePrivate
  hsecond : tacenta_boundary.dh.PrivateKey.agree candidatePrivate peer =
    ok (some sendSecret)
  hwrapSend : zeroize.Zeroizing.new
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) sendSecret = ok wrappedSend
  hderefSend : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedSend = ok sendSecret
  hbefore : tacenta_triple.State.sending_public real.triple = ok before
  hheader : lifecycle.triple_header_of decoded.header = ok realHeader
  hpublic : tacenta_boundary.dh.PrivateKey.public_key candidatePrivate = ok candidatePublic
  hpublicBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes candidatePublic = ok newPublicBytes
  htriple : lifecycle.receive_with_eviction real.triple decoded.header realHeader
    recvSecret sendSecret newPublicBytes sparseOutput = ok (.Ok (realTripleCandidate, realMk))
  hkeys : tacenta_ratchet.message_keys realMk tacenta_ratchet.LabelSet.Tacenta = ok realKeys
  hwrapMk : zeroize.Zeroizing.new
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) realMk = ok wrappedMk
  hderefMk : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
    (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) wrappedMk = ok realMk
  hwrapKeys : zeroize.Zeroizing.new
    (TupleABC.Insts.ZeroizeZeroize
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
      (Array.Insts.ZeroizeZeroize 16#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) realKeys = ok wrappedKeys
  hderefKeys : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
    (TupleABC.Insts.ZeroizeZeroize
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
      (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
      (Array.Insts.ZeroizeZeroize 16#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))) wrappedKeys = ok realKeys
  hrealAd : serialization.concat_ad (alloc.vec.Vec.deref real.identity_ad)
    decoded.header = ok realAd
  haead : tacenta_boundary.aead.decrypt realKeys.1 realKeys.2.1 realKeys.2.2
    (alloc.vec.Vec.deref decoded.ciphertext) (alloc.vec.Vec.deref realAd) =
    ok (.Ok aeadPlaintext)

/-! The generated success prefix fixes the exact Triple lifecycle input.  These
    two projections expose the concrete and model direct/full-store partitions
    that the caller-level splice must align before choosing a refinement
    adapter; neither projection invents a branch or replaces the returned
    candidate. -/
theorem initial_ratchet_success_prefix_receive_cases {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {real : lifecycle.Session} {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next) :
    (∃ direct,
      lifecycle.receive_attempt real.triple successPrefix.realHeader
        successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
        successPrefix.sparseOutput = ok (.Ok direct) ∧
      direct = (successPrefix.realTripleCandidate, successPrefix.realMk)) ∨
    (∃ reason half,
      lifecycle.receive_attempt real.triple successPrefix.realHeader
        successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
        successPrefix.sparseOutput = ok (.Err reason) ∧
      lifecycle.full_store reason = ok (some half)) := by
  exact concrete_receive_with_eviction_success_cases real.triple
    successPrefix.decoded.header successPrefix.realHeader successPrefix.recvSecret
    successPrefix.sendSecret successPrefix.newPublicBytes successPrefix.sparseOutput
    (successPrefix.realTripleCandidate, successPrefix.realMk) successPrefix.htriple

theorem initial_ratchet_model_success_receive_cases
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message) :
    (∃ direct,
      Model.Triple.receiveDetailed model.triple (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
        facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
        (Model.Lifecycle.sparseOutputOf
          (Model.Braid.receive oracle.braidKem model.braid
            (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1) =
        .ok direct ∧ direct = (facts.modelTripleCandidate, facts.modelMk)) ∨
    (∃ reason half,
      Model.Triple.receiveDetailed model.triple (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
        facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
        (Model.Lifecycle.sparseOutputOf
          (Model.Braid.receive oracle.braidKem model.braid
            (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1) =
        .error reason ∧ Model.Lifecycle.fullStore reason = some half) := by
  exact model_receive_with_eviction_success_cases model.triple facts.modelComposite
    (Model.Lifecycle.tripleHeaderOf facts.modelComposite) facts.modelDhOutRecv
    facts.modelDhOutSend (oracle.dhPublic facts.draw)
    (Model.Lifecycle.sparseOutputOf
    (Model.Braid.receive oracle.braidKem model.braid
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
    (facts.modelTripleCandidate, facts.modelMk) facts.hmodelTriple

theorem initial_ratchet_success_prefix_direct_receive
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {real : lifecycle.Session} {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (hcase : lifecycle.receive_attempt real.triple successPrefix.realHeader
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      successPrefix.sparseOutput = ok
        (.Ok (successPrefix.realTripleCandidate, successPrefix.realMk))) :
    tacenta_triple.State.receive real.triple successPrefix.realHeader
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      successPrefix.sparseOutput = ok
        (.Ok (successPrefix.realTripleCandidate, successPrefix.realMk)) := by
  simpa [lifecycle.receive_attempt] using hcase

theorem initial_ratchet_model_success_direct_receive
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (hcase : Model.Triple.receiveDetailed model.triple
      (Model.Lifecycle.tripleHeaderOf facts.modelComposite) facts.modelDhOutRecv
      facts.modelDhOutSend (oracle.dhPublic facts.draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1) =
      .ok (facts.modelTripleCandidate, facts.modelMk)) :
    Model.Triple.receive model.triple
      (Model.Lifecycle.tripleHeaderOf facts.modelComposite) facts.modelDhOutRecv
      facts.modelDhOutSend (oracle.dhPublic facts.draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1) =
      some (facts.modelTripleCandidate, facts.modelMk) := by
  exact (Model.Triple.receiveDetailed_ok_iff model.triple
    (Model.Lifecycle.tripleHeaderOf facts.modelComposite) facts.modelDhOutRecv
    facts.modelDhOutSend (oracle.dhPublic facts.draw)
    (Model.Lifecycle.sparseOutputOf
      (Model.Braid.receive oracle.braidKem model.braid
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
    (facts.modelTripleCandidate, facts.modelMk)).1 hcase

/-! The generated success prefix already contains the complete Braid receive
computation.  This constructor exposes it as the shared evidence record used
by the refusal and success adapters; only the message/state relation to the
model remains a caller obligation. -/
def initial_ratchet_braid_evidence_of_success_prefix {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {view : Model.Lifecycle.CodewordView} {K : Model.Braid.Kem}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (modelComposite : Model.CompositeHeader.Composite)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines successPrefix.m
      (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hnext : Tacenta.SessionUnitBraidT3.StateRefines K
      successPrefix.braidCandidate.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2) :
    BraidReceiveEvidence K view real model successPrefix.decoded.header modelComposite :=
  { message := successPrefix.m
    receivedEpoch := successPrefix.receivedEpoch
    output := successPrefix.output
    next := successPrefix.braidCandidate
    sparseOutput := successPrefix.sparseOutput
    hmessageCall := successPrefix.hmessage
    hmessageRel := hmessageRel
    hreceive := successPrefix.hreceive
    hsparse := successPrefix.hsparse
    hnext := hnext }

theorem initial_ratchet_success_prefix_of_result {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (real : lifecycle.Session) (message : Slice Std.U8) (rng rngNext : R)
    (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Ok plaintext, next, rngNext)) :
    Nonempty (InitialRatchetSuccessPrefix rngCore cryptoRng real message rng rngNext
      plaintext next) := by
  obtain ⟨decoded, m, receivedEpoch, output, braidCandidate, sparseOutput, peer,
      recvSecret, wrappedRecv, candidateBytes, rng1, candidatePrivate, sendSecret,
      wrappedSend, before, realHeader, candidatePublic, newPublicBytes,
      realTripleCandidate, realMk, wrappedMk, realKeys, wrappedKeys, aeadPlaintext,
      realAd, hdecode, hmessage, hreceive, hsparse, hpeer, hfirst, hwrapRecv,
      hderefRecv, hrandom, hcandidate, hsecond, hwrapSend, hderefSend, hbefore,
      hheader, hpublic, hpublicBytes, htriple, hkeys, hwrapMk, hderefMk,
      hwrapKeys, hderefKeys, hrealAd, haead⟩ :=
    decrypt_ratchet_success_aead_prefix rngCore cryptoRng hz32 hzKeys real message
      rng rngNext plaintext next hcall
  exact ⟨{
    decoded := decoded, m := m, receivedEpoch := receivedEpoch, output := output,
    braidCandidate := braidCandidate, sparseOutput := sparseOutput, peer := peer,
    recvSecret := recvSecret, wrappedRecv := wrappedRecv, candidateBytes := candidateBytes,
    rng1 := rng1, candidatePrivate := candidatePrivate, sendSecret := sendSecret,
    wrappedSend := wrappedSend, before := before, realHeader := realHeader,
    candidatePublic := candidatePublic, newPublicBytes := newPublicBytes,
    realTripleCandidate := realTripleCandidate, realMk := realMk, wrappedMk := wrappedMk,
    realKeys := realKeys, wrappedKeys := wrappedKeys, aeadPlaintext := aeadPlaintext,
    realAd := realAd, hdecode := hdecode, hmessage := hmessage, hreceive := hreceive,
    hsparse := hsparse, hpeer := hpeer, hfirst := hfirst, hwrapRecv := hwrapRecv,
    hderefRecv := hderefRecv, hrandom := hrandom, hcandidate := hcandidate,
    hsecond := hsecond, hwrapSend := hwrapSend, hderefSend := hderefSend,
    hbefore := hbefore, hheader := hheader, hpublic := hpublic,
    hpublicBytes := hpublicBytes, htriple := htriple, hkeys := hkeys,
    hwrapMk := hwrapMk, hderefMk := hderefMk, hwrapKeys := hwrapKeys,
    hderefKeys := hderefKeys, hrealAd := hrealAd, haead := haead }⟩

/-! The generated prefix is extracted from an actual successful call, so its
    successor equation is recoverable by replaying that same translated call.
    Keeping this equality here prevents a later splice from choosing a
    convenient successor session independently of `decrypt_ratchet`. -/
theorem initial_ratchet_success_next_of_prefix
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {view : Model.Lifecycle.CodewordView} {dh : DhView} {K : Model.Braid.Kem}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (hcall : lifecycle.Session.decrypt_ratchet rc crc real message rng =
      ok (.Ok plaintext, next, rngNext))
    (hrel : SessionRefines dh K real model)
    (modelComposite : Model.CompositeHeader.Composite)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines successPrefix.m
      (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hbraid : Tacenta.SessionUnitBraidT3.StateRefines K
      successPrefix.braidCandidate.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2)
    (hready : Model.Lifecycle.agreementFailed model = false) :
    vecOf successPrefix.aeadPlaintext = vecOf plaintext ∧
      next =
        { { real with triple := successPrefix.realTripleCandidate, braid :=
            successPrefix.braidCandidate } with
          ratchet_private :=
            if successPrefix.realTripleCandidate.classical.dhs_pub ==
                real.triple.classical.dhs_pub then
              real.ratchet_private else successPrefix.candidatePrivate } := by
  let evidence := initial_ratchet_braid_evidence_of_success_prefix
    successPrefix modelComposite hmessageRel hbraid
  have hcomputed := decrypt_ratchet_success_result_from_braid
    rc crc dh K real model message rng successPrefix.rng1 successPrefix.decoded
    modelComposite successPrefix.decoded.header evidence rfl successPrefix.m
    successPrefix.receivedEpoch successPrefix.output successPrefix.braidCandidate
    successPrefix.sparseOutput successPrefix.peer successPrefix.recvSecret
    successPrefix.sendSecret successPrefix.candidateBytes successPrefix.newPublicBytes
    successPrefix.before successPrefix.realMk successPrefix.candidatePrivate
    successPrefix.candidatePublic successPrefix.realHeader successPrefix.wrappedRecv
    successPrefix.wrappedSend successPrefix.wrappedMk successPrefix.realTripleCandidate
    successPrefix.realKeys successPrefix.wrappedKeys successPrefix.realAd
    successPrefix.aeadPlaintext hrel hready successPrefix.hdecode
    rfl rfl rfl rfl rfl successPrefix.hpeer successPrefix.hfirst
    successPrefix.hwrapRecv successPrefix.hderefRecv successPrefix.hrandom
    successPrefix.hcandidate successPrefix.hsecond successPrefix.hbefore
    successPrefix.hwrapSend successPrefix.hderefSend successPrefix.hheader
    successPrefix.hpublic successPrefix.hpublicBytes successPrefix.htriple
    successPrefix.hkeys successPrefix.hwrapMk successPrefix.hderefMk
    successPrefix.hwrapKeys successPrefix.hderefKeys successPrefix.hrealAd
    successPrefix.haead
  have heq := hcall.symm.trans hcomputed
  have hvalue := Result.ok.inj heq
  injection hvalue with hplain hnext
  have hplain' : plaintext = successPrefix.aeadPlaintext := by
    simpa only [core.result.Result.Ok.injEq] using hplain
  have hnext' := (Prod.mk.inj hnext).1
  dsimp [evidence, initial_ratchet_braid_evidence_of_success_prefix] at hnext'
  exact ⟨congrArg vecOf hplain'.symm, hnext'⟩

/-! The nonterminal success callback carries the actual generated result and the
    exact model alignment needed by the direct/retry router.  Keeping these as
    fields prevents a caller from supplying a `StepRefines` proof detached from
    the result returned by `decrypt_ratchet`. -/
structure InitialRatchetSuccessEvidence {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R) : Type where
  modelPlaintext : Bytes
  oracleNext : Model.Lifecycle.Oracle
  realTripleCandidate : tacenta_triple.State
  realBraidCandidate : tacenta_braid.Braid
  candidatePrivate : tacenta_boundary.dh.PrivateKey
  draw : Model.Lifecycle.Key
  modelTripleCandidate : Model.Triple.State
  modelBraidCandidate : Model.Braid.BraidState
  composite : tacenta_wire.Composite
  modelComposite : Model.CompositeHeader.Composite
  header : tacenta_triple.Header
  modelHeader : Model.Triple.Header
  dhOutRecv : Array Std.U8 32#usize
  dhOutSend : Array Std.U8 32#usize
  newDhsPub : Array Std.U8 32#usize
  modelDhOutRecv : Model.Lifecycle.Key
  modelDhOutSend : Model.Lifecycle.Key
  modelNewDhsPub : Model.Lifecycle.Key
  output : Option tacenta_spqr.Output
  modelOutput : Option Model.SparseRatchet.Output
  realMk : Array Std.U8 32#usize
  modelMk : Model.Lifecycle.Key
  hreceiveReal : lifecycle.receive_with_eviction real.triple composite header
    dhOutRecv dhOutSend newDhsPub output = ok (.Ok (realTripleCandidate, realMk))
  hreceiveModel : Model.Lifecycle.receiveWithEviction model.triple modelComposite
    modelHeader modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput =
    .ok (modelTripleCandidate, modelMk)
  hcase : AggregateReceiveAlignedCase composite modelComposite header modelHeader
    dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
    output modelOutput real.triple model.triple
    (realTripleCandidate, realMk) (modelTripleCandidate, modelMk)
    hreceiveReal hreceiveModel
  hrel : SessionRefines dh K real model
  hreal : lifecycle.Session.decrypt_ratchet rc crc real message rng =
    ok (.Ok plaintext, next, rngNext)
  hnext : next =
      { { real with triple := realTripleCandidate, braid := realBraidCandidate } with
        ratchet_private :=
          if realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
            real.ratchet_private else candidatePrivate }
  hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
    { session :=
        { model with
          triple := modelTripleCandidate
          braid := modelBraidCandidate
          ratchetPrivate :=
            if modelTripleCandidate.classical.dhsPub == model.triple.classical.dhsPub then
              model.ratchetPrivate else draw }
      result := .ok modelPlaintext
      oracle := oracleNext }
  hbraid : Tacenta.SessionUnitBraidT3.StateRefines K
    realBraidCandidate.state modelBraidCandidate
  hprivate : dh.privateKey candidatePrivate = draw
  hbytes : vecOf plaintext = modelPlaintext
  htrace : trace rngNext = oracleNext.draws

/-! This is the branch fact consumed by the success router.  Its direct arm
    names the raw concrete and model Triple successes; its retry arm carries
    the shared full-store relation.  In particular, callers cannot select a
    retry proof for a direct result (or vice versa) and then hide that choice
    behind the lifecycle wrapper. -/
def InitialRatchetSuccessReceiveBranch
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key) : Prop :=
  (∃ hrealDirect : tacenta_triple.State.receive realState header dhOutRecv
      dhOutSend newDhsPub output = ok (.Ok realResult),
    ∃ hmodelDirect : Model.Triple.receive modelState modelHeader modelDhOutRecv
      modelDhOutSend modelNewDhsPub modelOutput = some modelResult,
      Tacenta.SessionUnitTripleT3.StateRefines
        Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
        realResult.1 modelResult.1 ∧
      Tacenta.SessionUnitTripleT3.keyOf realResult.2 = modelResult.2) ∨
  (∃ realReason modelReason,
    AggregateReceiveRetryRefinement composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realReason modelReason realResult
      modelResult)

/-! Short index for the branch belonging to a particular generated prefix and
    model-success record.  Keeping this alias named makes the concrete
    direct/retry dispatcher below readable without hiding any of its indices. -/
abbrev InitialRatchetSuccessBranchAt {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message) : Prop :=
  InitialRatchetSuccessReceiveBranch
    successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
    (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
    successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
    facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
    successPrefix.sparseOutput
    (Model.Lifecycle.sparseOutputOf
      (Model.Braid.receive oracle.braidKem model.braid
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
    real.triple model.triple
    (successPrefix.realTripleCandidate, successPrefix.realMk)
    (facts.modelTripleCandidate, facts.modelMk)

/-! Select the success adapter from the actual generated Triple receive result.
    The direct callback receives the exact `receive_attempt = Ok` equation; the
    retry callback receives the exact refusal and full-store classification.
    Thus the caller cannot choose the retry adapter for a direct result (or
    vice versa). -/
theorem initial_ratchet_success_branch_of_concrete_receive_case {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (hdirect : ∀ (direct : tacenta_triple.State × Array Std.U8 32#usize),
      lifecycle.receive_attempt real.triple successPrefix.realHeader
        successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
        successPrefix.sparseOutput = ok (.Ok direct) →
      direct = (successPrefix.realTripleCandidate, successPrefix.realMk) →
      InitialRatchetSuccessBranchAt successPrefix facts)
    (hretry : ∀ (realReason : tacenta_triple.TripleError) (half : lifecycle.FullStore),
      lifecycle.receive_attempt real.triple successPrefix.realHeader
        successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
        successPrefix.sparseOutput = ok (.Err realReason) →
      lifecycle.full_store realReason = ok (some half) →
      InitialRatchetSuccessBranchAt successPrefix facts) :
    InitialRatchetSuccessBranchAt successPrefix facts := by
  rcases initial_ratchet_success_prefix_receive_cases successPrefix with
    ⟨direct, hdirectCall, hdirectEq⟩ | ⟨realReason, half, hretryCall, hfull⟩
  · exact hdirect direct hdirectCall hdirectEq
  · exact hretry realReason half hretryCall hfull

/-! The concrete and model receive partitions are part of the successful
    lifecycle computations, rather than caller-selected labels.  This small
    bridge makes that fact explicit at the branch-provider boundary: a caller
    may still supply the semantic relation for each pair of cases, but it
    cannot supply a branch relation without first exposing the two actual
    `receive`/`receiveDetailed` results. -/
theorem initial_ratchet_success_branch_of_actual_receive_cases {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (hcases :
      ∀ (realCase :
          (∃ direct,
            lifecycle.receive_attempt real.triple successPrefix.realHeader
              successPrefix.recvSecret successPrefix.sendSecret
              successPrefix.newPublicBytes successPrefix.sparseOutput =
              ok (.Ok direct) ∧
            direct = (successPrefix.realTripleCandidate, successPrefix.realMk)) ∨
          (∃ reason half,
            lifecycle.receive_attempt real.triple successPrefix.realHeader
              successPrefix.recvSecret successPrefix.sendSecret
              successPrefix.newPublicBytes successPrefix.sparseOutput =
              ok (.Err reason) ∧
            lifecycle.full_store reason = ok (some half)))
      (modelCase :
          (∃ direct,
            Model.Triple.receiveDetailed model.triple
              (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
              facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
              (Model.Lifecycle.sparseOutputOf
                (Model.Braid.receive oracle.braidKem model.braid
                  (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1) =
              .ok direct ∧ direct = (facts.modelTripleCandidate, facts.modelMk)) ∨
          (∃ reason half,
            Model.Triple.receiveDetailed model.triple
              (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
              facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
              (Model.Lifecycle.sparseOutputOf
                (Model.Braid.receive oracle.braidKem model.braid
                  (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1) =
              .error reason ∧ Model.Lifecycle.fullStore reason = some half)) ,
      InitialRatchetSuccessReceiveBranch
        successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
        (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
        successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
        facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
        successPrefix.sparseOutput
        (Model.Lifecycle.sparseOutputOf
          (Model.Braid.receive oracle.braidKem model.braid
            (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
        real.triple model.triple
        (successPrefix.realTripleCandidate, successPrefix.realMk)
        (facts.modelTripleCandidate, facts.modelMk)) :
    InitialRatchetSuccessReceiveBranch
      successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
      (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
      successPrefix.sparseOutput
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
      real.triple model.triple
      (successPrefix.realTripleCandidate, successPrefix.realMk)
      (facts.modelTripleCandidate, facts.modelMk) := by
  exact hcases (initial_ratchet_success_prefix_receive_cases successPrefix)
    (initial_ratchet_model_success_receive_cases facts)


theorem initial_ratchet_aligned_case_of_branch
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hreal : lifecycle.receive_with_eviction realState composite header
      dhOutRecv dhOutSend newDhsPub output = ok (.Ok realResult))
    (hmodel : Model.Lifecycle.receiveWithEviction modelState modelComposite
      modelHeader modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput =
      .ok modelResult)
    (hbranch : InitialRatchetSuccessReceiveBranch composite modelComposite header
      modelHeader dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend
      modelNewDhsPub output modelOutput realState modelState realResult modelResult) :
    AggregateReceiveAlignedCase composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realResult modelResult hreal hmodel := by
  unfold InitialRatchetSuccessReceiveBranch at hbranch
  rcases hbranch with ⟨hrealDirect, hmodelDirect, hstate, hkey⟩ | ⟨realReason,
    modelReason, hretry⟩
  · exact aggregate_receive_aligned_case_of_direct composite modelComposite header
      modelHeader dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend
      modelNewDhsPub output modelOutput realState modelState realResult modelResult
      hreal hmodel hrealDirect hmodelDirect hstate hkey
  · exact aggregate_receive_aligned_case_of_retry composite modelComposite header
      modelHeader dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend
      modelNewDhsPub output modelOutput realState modelState realResult modelResult
      hreal hmodel realReason modelReason hretry

/-! Convert the aggregate receive result, already indexed by both lifecycle
    calls, back into the branch consumed by the session success splice.  This
    direction is intentionally separate from `initial_ratchet_aligned_case_of_branch`:
    the splice must be able to consume a case extracted from the actual result,
    rather than a branch proposition supplied independently of those results. -/
theorem initial_ratchet_success_branch_of_aligned_case
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hreal : lifecycle.receive_with_eviction realState composite header
      dhOutRecv dhOutSend newDhsPub output = ok (.Ok realResult))
    (hmodel : Model.Lifecycle.receiveWithEviction modelState modelComposite
      modelHeader modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput =
      .ok modelResult)
    (hcase : AggregateReceiveAlignedCase composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realResult modelResult hreal hmodel) :
    InitialRatchetSuccessReceiveBranch composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realResult modelResult := by
  unfold AggregateReceiveAlignedCase at hcase
  rcases hcase with hdirect | hretry
  · obtain ⟨directReal, directModel, hrealDirect, hmodelDirect, hrealEq,
      hmodelEq, hstate, hkey⟩ := hdirect
    subst directReal
    subst directModel
    exact Or.inl ⟨hrealDirect, hmodelDirect, hstate, hkey⟩
  · obtain ⟨realReason, modelReason, hretry⟩ := hretry
    exact Or.inr ⟨realReason, modelReason, hretry⟩

/-! Public success-router entry for a full-store retry.  This keeps the
    classical/post-quantum choice below the router: the shared adapter first
    builds the indexed aggregate case, and only then is it projected into the
    branch consumed by `InitialRatchetSuccessSplice`. -/
/-! Direct Triple success adapter.  The raw `State.receive` result is taken
    from the generated success prefix, while the model candidate and its
    `StateRefines` witness come from the direct contract theorem.  The final
    projection is deliberately performed through `aggregate_receive_core_refinement_of_direct`
    so the branch consumed by the session step is the same core relation used
    by the retry path. -/
theorem initial_ratchet_success_branch_of_direct_contracts {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (hAttempt : lifecycle.receive_attempt real.triple successPrefix.realHeader
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      successPrefix.sparseOutput = ok
        (.Ok (successPrefix.realTripleCandidate, successPrefix.realMk)))
    (hmodelAttempt : Model.Triple.receiveDetailed model.triple
      (Model.Lifecycle.tripleHeaderOf facts.modelComposite) facts.modelDhOutRecv
      facts.modelDhOutSend (oracle.dhPublic facts.draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1) =
      .ok (facts.modelTripleCandidate, facts.modelMk))
    (hmac : Tacenta.SessionUnitT3.HmacAgrees)
    (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hzr : Tacenta.SessionUnitT3.ZeroizingRoundTrips)
    (hvr : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hz96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96)
    (hz64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64)
    (hret : Tacenta.SessionUnitSpqrT3.VecRetainAgrees)
    (happ : Tacenta.SessionUnitSpqrT3.VecAppendAgrees)
    (hrm : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees)
    (hzs : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hopt : Tacenta.SessionUnitSpqrT1.OptionCloneTotal)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs
      real.triple model.triple)
    (hrecvKey : facts.modelDhOutRecv = Tacenta.SessionUnitTripleT3.keyOf successPrefix.recvSecret)
    (hsendKey : facts.modelDhOutSend = Tacenta.SessionUnitTripleT3.keyOf successPrefix.sendSecret)
    (hnewKey : oracle.dhPublic facts.draw = Tacenta.SessionUnitTripleT3.keyOf
      successPrefix.newPublicBytes)
    (hmodelOutput :
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1) =
      successPrefix.sparseOutput.map Tacenta.SessionUnitTripleT3.spqrOutputOf)
    (mh : Model.State.Header)
    (hmodelHeader : Model.Lifecycle.tripleHeaderOf facts.modelComposite =
      { dr := mh, epoch := successPrefix.realHeader.epoch.val, pqN := successPrefix.realHeader.pq_n.val })
    (hheader : Tacenta.SessionUnitTripleT3.RatchetHeaderR successPrefix.realHeader.dr mh)
    (hone : (model.triple.classical.skipped.filter
      (fun x => x.1 == mh.dh && x.2.1 == mh.n)).length ≤ 1)
    (hs : max model.triple.classical.skipped.length Model.State.maxSkippedStore +
      Model.State.maxSkip ≤ Usize.max)
    (hevents : model.triple.classical.events + 1 < Std.U32.max)
    (hepoch : model.triple.postQuantum.epoch + 1 < Std.U64.max)
    (hroom : model.triple.postQuantum.chains.length + 2 < Usize.max)
    (hcb : ∀ p ∈ model.triple.postQuantum.chains,
      p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ model.triple.postQuantum.skipped,
      sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : tacenta_spqr.Output, successPrefix.sparseOutput = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hskiproom : model.triple.postQuantum.skipped.length +
      Model.SparseRatchet.maxSkip ≤ Usize.max)
    (hone2 : (model.triple.postQuantum.skipped.filter
      (fun x => x.1 == successPrefix.realHeader.epoch.val &&
        x.2.1 == successPrefix.realHeader.pq_n.val)).length ≤ 1)
    (hcounter : ∀ p ∈ model.triple.postQuantum.chains,
      ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max) :
    InitialRatchetSuccessReceiveBranch
      successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
      (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
      successPrefix.sparseOutput
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
      real.triple model.triple
      (successPrefix.realTripleCandidate, successPrefix.realMk)
      (facts.modelTripleCandidate, facts.modelMk) := by
  have hrealDirect := initial_ratchet_success_prefix_direct_receive successPrefix hAttempt
  have hmodelDirect := initial_ratchet_model_success_direct_receive facts hmodelAttempt
  obtain ⟨modelCandidate, modelKey, hmodelCandidate, hcase⟩ :=
    aggregate_receive_aligned_case_of_direct_contracts
      successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
      (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
      successPrefix.sparseOutput
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
      real.triple model.triple
      (successPrefix.realTripleCandidate, successPrefix.realMk)
      hmac hkdf hzr hvr hz96 hz64 hret happ hrm hzs hopt hrel
      hrecvKey hsendKey hnewKey hmodelOutput mh hmodelHeader hheader hone hs hevents hepoch hroom
      hcb hsb hnewb hskiproom hone2 hcounter hrealDirect
  have hmodelEq : (modelCandidate, modelKey) =
      (facts.modelTripleCandidate, facts.modelMk) := by
    apply Option.some.inj
    exact hmodelCandidate.symm.trans hmodelDirect
  cases hmodelEq
  unfold AggregateReceiveAlignedCase at hcase
  rcases hcase with hdirect | hretry
  · obtain ⟨directReal, directModel, hrealDirect', hmodelDirect', hrealEq,
      hmodelEq', hstate, hkey⟩ := hdirect
    subst directReal
    subst directModel
    have hcore := aggregate_receive_core_refinement_of_direct
      successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
      (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
      successPrefix.sparseOutput
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
      real.triple model.triple
      (successPrefix.realTripleCandidate, successPrefix.realMk)
      (facts.modelTripleCandidate, facts.modelMk)
      hrealDirect' hmodelDirect' hstate hkey
    exact Or.inl ⟨hrealDirect', hmodelDirect', hcore.2.2.1, hcore.2.2.2⟩
  · exact Or.inr hretry

theorem initial_ratchet_success_branch_of_full_store_retry
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (realState : tacenta_triple.State)
    (modelState : Model.Triple.State)
    (realReason : tacenta_triple.TripleError)
    (modelReason : Model.Triple.ReceiveRefusal)
    (realResult : tacenta_triple.State × Array Std.U8 32#usize)
    (modelResult : Model.Triple.State × Model.Lifecycle.Key)
    (hreal : lifecycle.receive_with_eviction realState composite header
      dhOutRecv dhOutSend newDhsPub output = ok (.Ok realResult))
    (hmodel : Model.Lifecycle.receiveWithEviction modelState modelComposite
      modelHeader modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput =
      .ok modelResult)
    (half : lifecycle.FullStore)
    (hFullReal : lifecycle.full_store realReason = ok (some half))
    (hclassical : half = lifecycle.FullStore.Classical →
      lifecycle.full_store realReason = ok (some lifecycle.FullStore.Classical) →
      AggregateReceiveRetryRefinement composite modelComposite header modelHeader
        dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
        output modelOutput realState modelState realReason modelReason realResult
        modelResult)
    (hpostQuantum : half = lifecycle.FullStore.PostQuantum →
      lifecycle.full_store realReason = ok (some lifecycle.FullStore.PostQuantum) →
      AggregateReceiveRetryRefinement composite modelComposite header modelHeader
        dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
        output modelOutput realState modelState realReason modelReason realResult
        modelResult) :
    InitialRatchetSuccessReceiveBranch composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput realState modelState realResult modelResult := by
  apply initial_ratchet_success_branch_of_aligned_case composite modelComposite header
    modelHeader dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend
    modelNewDhsPub output modelOutput realState modelState realResult modelResult
    hreal hmodel
  exact aggregate_receive_aligned_case_of_full_store_retry composite modelComposite
    header modelHeader dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend
    modelNewDhsPub output modelOutput realState modelState realReason modelReason
    realResult modelResult hreal hmodel half hFullReal hclassical hpostQuantum

/-! Instantiate the branch provider with the exact generated/model success
    witnesses.  The aggregate equalities come from the typed prefix and model
    facts, while the branch relation supplies only the direct-vs-retry
    semantic splice. -/
/-! Prefix-indexed retry adapter.  The concrete and model successful outer
    calls come directly from the generated success prefix and model facts;
    only the full-store classification callbacks remain, and those are
    consumed by the shared Classical/PostQuantum adapter. -/
theorem initial_ratchet_success_branch_of_full_store_retry_from_prefix {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (realReason : tacenta_triple.TripleError)
    (modelReason : Model.Triple.ReceiveRefusal)
    (half : lifecycle.FullStore)
    (hFullReal : lifecycle.full_store realReason = ok (some half))
    (hclassical : half = lifecycle.FullStore.Classical →
      lifecycle.full_store realReason = ok (some lifecycle.FullStore.Classical) →
      AggregateReceiveRetryRefinement successPrefix.decoded.header facts.modelComposite
        successPrefix.realHeader (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
        successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
        facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
        successPrefix.sparseOutput
        (Model.Lifecycle.sparseOutputOf
          (Model.Braid.receive oracle.braidKem model.braid
            (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
        real.triple model.triple realReason modelReason
        (successPrefix.realTripleCandidate, successPrefix.realMk)
        (facts.modelTripleCandidate, facts.modelMk))
    (hpostQuantum : half = lifecycle.FullStore.PostQuantum →
      lifecycle.full_store realReason = ok (some lifecycle.FullStore.PostQuantum) →
      AggregateReceiveRetryRefinement successPrefix.decoded.header facts.modelComposite
        successPrefix.realHeader (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
        successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
        facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
        successPrefix.sparseOutput
        (Model.Lifecycle.sparseOutputOf
          (Model.Braid.receive oracle.braidKem model.braid
            (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
        real.triple model.triple realReason modelReason
        (successPrefix.realTripleCandidate, successPrefix.realMk)
        (facts.modelTripleCandidate, facts.modelMk)) :
    InitialRatchetSuccessReceiveBranch
      successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
      (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
      successPrefix.sparseOutput
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
      real.triple model.triple
      (successPrefix.realTripleCandidate, successPrefix.realMk)
      (facts.modelTripleCandidate, facts.modelMk) := by
  exact initial_ratchet_success_branch_of_full_store_retry
    successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
    (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
    successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
    facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
    successPrefix.sparseOutput
    (Model.Lifecycle.sparseOutputOf
      (Model.Braid.receive oracle.braidKem model.braid
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
    real.triple model.triple realReason modelReason
    (successPrefix.realTripleCandidate, successPrefix.realMk)
    (facts.modelTripleCandidate, facts.modelMk)
    successPrefix.htriple facts.hmodelTriple half hFullReal hclassical hpostQuantum

theorem initial_ratchet_success_aligned_case_of_prefix_and_branch {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext plaintext next)
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (hbranch : InitialRatchetSuccessReceiveBranch
      successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
      (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
      successPrefix.sparseOutput
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
      real.triple model.triple
      (successPrefix.realTripleCandidate, successPrefix.realMk)
      (facts.modelTripleCandidate, facts.modelMk)) :
    AggregateReceiveAlignedCase successPrefix.decoded.header facts.modelComposite
      successPrefix.realHeader (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes facts.modelDhOutRecv
      facts.modelDhOutSend (oracle.dhPublic facts.draw) successPrefix.sparseOutput
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
      real.triple model.triple
      (successPrefix.realTripleCandidate, successPrefix.realMk)
      (facts.modelTripleCandidate, facts.modelMk) successPrefix.htriple facts.hmodelTriple := by
  exact initial_ratchet_aligned_case_of_branch
    successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
    (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
    successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
    facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
    successPrefix.sparseOutput
    (Model.Lifecycle.sparseOutputOf
      (Model.Braid.receive oracle.braidKem model.braid
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
    real.triple model.triple
    (successPrefix.realTripleCandidate, successPrefix.realMk)
    (facts.modelTripleCandidate, facts.modelMk)
    successPrefix.htriple facts.hmodelTriple hbranch

def initial_ratchet_success_evidence_of_prefix {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext plaintext next)
    (modelPlaintext : Bytes) (oracleNext : Model.Lifecycle.Oracle)
    (candidatePrivate : tacenta_boundary.dh.PrivateKey)
    (draw : Model.Lifecycle.Key)
    (modelTripleCandidate : Model.Triple.State)
    (modelBraidCandidate : Model.Braid.BraidState)
    (composite : tacenta_wire.Composite)
    (modelComposite : Model.CompositeHeader.Composite)
    (header : tacenta_triple.Header) (modelHeader : Model.Triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array Std.U8 32#usize)
    (modelDhOutRecv modelDhOutSend modelNewDhsPub : Model.Lifecycle.Key)
    (output : Option tacenta_spqr.Output)
    (modelOutput : Option Model.SparseRatchet.Output)
    (modelMk : Model.Lifecycle.Key)
    (hreceiveReal : lifecycle.receive_with_eviction real.triple composite header
      dhOutRecv dhOutSend newDhsPub output = ok (.Ok (successPrefix.realTripleCandidate, successPrefix.realMk)))
    (hreceiveModel : Model.Lifecycle.receiveWithEviction model.triple modelComposite
      modelHeader modelDhOutRecv modelDhOutSend modelNewDhsPub modelOutput =
      .ok (modelTripleCandidate, modelMk))
    (hcase : AggregateReceiveAlignedCase composite modelComposite header modelHeader
      dhOutRecv dhOutSend newDhsPub modelDhOutRecv modelDhOutSend modelNewDhsPub
      output modelOutput real.triple model.triple
      (successPrefix.realTripleCandidate, successPrefix.realMk) (modelTripleCandidate, modelMk)
      hreceiveReal hreceiveModel)
    (hrel : SessionRefines dh K real model)
    (hreal : lifecycle.Session.decrypt_ratchet rc crc real message rng =
      ok (.Ok plaintext, next, rngNext))
    (hnext : next =
      { { real with triple := successPrefix.realTripleCandidate, braid := successPrefix.braidCandidate } with
        ratchet_private :=
          if successPrefix.realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
            real.ratchet_private else candidatePrivate })
    (hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session :=
          { model with
            triple := modelTripleCandidate
            braid := modelBraidCandidate
            ratchetPrivate :=
              if modelTripleCandidate.classical.dhsPub == model.triple.classical.dhsPub then
                model.ratchetPrivate else draw }
        result := .ok modelPlaintext
        oracle := oracleNext })
    (hbraid : Tacenta.SessionUnitBraidT3.StateRefines K
      successPrefix.braidCandidate.state modelBraidCandidate)
    (hprivate : dh.privateKey candidatePrivate = draw)
    (hbytes : vecOf plaintext = modelPlaintext)
    (htrace : trace rngNext = oracleNext.draws) :
    InitialRatchetSuccessEvidence rc crc trace dh K view oracle real model message rng
      plaintext next rngNext := by
  exact {
    modelPlaintext := modelPlaintext, oracleNext := oracleNext,
    realTripleCandidate := successPrefix.realTripleCandidate,
    realBraidCandidate := successPrefix.braidCandidate,
    candidatePrivate := candidatePrivate, draw := draw,
    modelTripleCandidate := modelTripleCandidate,
    modelBraidCandidate := modelBraidCandidate,
    composite := composite, modelComposite := modelComposite,
    header := header, modelHeader := modelHeader,
    dhOutRecv := dhOutRecv, dhOutSend := dhOutSend, newDhsPub := newDhsPub,
    modelDhOutRecv := modelDhOutRecv, modelDhOutSend := modelDhOutSend,
    modelNewDhsPub := modelNewDhsPub, output := output, modelOutput := modelOutput,
    realMk := successPrefix.realMk, modelMk := modelMk,
    hreceiveReal := hreceiveReal, hreceiveModel := hreceiveModel,
    hcase := hcase, hrel := hrel, hreal := hreal, hnext := hnext,
    hmodel := hmodel, hbraid := hbraid, hprivate := hprivate,
    hbytes := hbytes, htrace := htrace }

/-! Final success-evidence constructor.  This is the intended public splice:
    the generated prefix and model facts fix every value at the call site, and
    only the direct/retry branch relation remains to be supplied. -/
def initial_ratchet_success_evidence_of_prefix_and_branch {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext plaintext next)
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (candidatePrivate : tacenta_boundary.dh.PrivateKey)
    (modelBraidCandidate : Model.Braid.BraidState)
    (hbranch : InitialRatchetSuccessReceiveBranch
      successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
      (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
      successPrefix.sparseOutput
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
      real.triple model.triple
      (successPrefix.realTripleCandidate, successPrefix.realMk)
      (facts.modelTripleCandidate, facts.modelMk))
    (hrel : SessionRefines dh K real model)
    (hreal : lifecycle.Session.decrypt_ratchet rc crc real message rng =
      ok (.Ok plaintext, next, rngNext))
    (hnext : next =
      { { real with triple := successPrefix.realTripleCandidate, braid := successPrefix.braidCandidate } with
        ratchet_private :=
          if successPrefix.realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
            real.ratchet_private else candidatePrivate })
    (hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session :=
          { model with
            triple := facts.modelTripleCandidate
            braid := modelBraidCandidate
            ratchetPrivate :=
              if facts.modelTripleCandidate.classical.dhsPub == model.triple.classical.dhsPub then
                model.ratchetPrivate else facts.draw }
        result := .ok facts.modelPlaintext
        oracle := oracleNext })
    (hbraid : Tacenta.SessionUnitBraidT3.StateRefines K
      successPrefix.braidCandidate.state modelBraidCandidate)
    (hprivate : dh.privateKey candidatePrivate = facts.draw)
    (hbytes : vecOf plaintext = facts.modelPlaintext)
    (htrace : trace rngNext = oracleNext.draws) :
    InitialRatchetSuccessEvidence rc crc trace dh K view oracle real model message rng
      plaintext next rngNext := by
  have hcase := initial_ratchet_success_aligned_case_of_prefix_and_branch
    successPrefix facts hbranch
  exact initial_ratchet_success_evidence_of_prefix successPrefix facts.modelPlaintext
    oracleNext candidatePrivate facts.draw facts.modelTripleCandidate modelBraidCandidate
    successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
    (Model.Lifecycle.tripleHeaderOf facts.modelComposite) successPrefix.recvSecret
    successPrefix.sendSecret successPrefix.newPublicBytes facts.modelDhOutRecv
    facts.modelDhOutSend (oracle.dhPublic facts.draw) successPrefix.sparseOutput
    (Model.Lifecycle.sparseOutputOf
      (Model.Braid.receive oracle.braidKem model.braid
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
    facts.modelMk successPrefix.htriple facts.hmodelTriple hcase hrel hreal hnext hmodel
    hbraid hprivate hbytes htrace

/-! The model successor Braid is fixed by the model success facts themselves.
This convenience constructor removes the last arbitrary model-successor
parameter from the common success path; callers only prove that the concrete
successor refines this exact `Model.Braid.receive` result. -/
def initial_ratchet_success_evidence_of_prefix_and_branch_of_facts {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (candidatePrivate : tacenta_boundary.dh.PrivateKey)
    (hbranch : InitialRatchetSuccessReceiveBranch
      successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
      (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
      successPrefix.sparseOutput
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
      real.triple model.triple
      (successPrefix.realTripleCandidate, successPrefix.realMk)
      (facts.modelTripleCandidate, facts.modelMk))
    (hrel : SessionRefines dh K real model)
    (hreal : lifecycle.Session.decrypt_ratchet rc crc real message rng =
      ok (.Ok plaintext, next, rngNext))
    (hnext : next =
      { { real with triple := successPrefix.realTripleCandidate, braid :=
          successPrefix.braidCandidate } with
        ratchet_private :=
          if successPrefix.realTripleCandidate.classical.dhs_pub == real.triple.classical.dhs_pub then
            real.ratchet_private else candidatePrivate })
    (hbraid : Tacenta.SessionUnitBraidT3.StateRefines K
      successPrefix.braidCandidate.state
      (Model.Braid.receive oracle.braidKem model.braid
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.2)
    (hprivate : dh.privateKey candidatePrivate = facts.draw)
    (hbytes : vecOf plaintext = facts.modelPlaintext)
    (htrace : trace rngNext = oracleNext.draws) :
    InitialRatchetSuccessEvidence rc crc trace dh K view oracle real model message rng
      plaintext next rngNext := by
  let modelBraidCandidate :=
    (Model.Braid.receive oracle.braidKem model.braid
      (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.2
  have hmodel := initial_ratchet_model_success_result_of_facts facts
  simpa [modelBraidCandidate] using
    (initial_ratchet_success_evidence_of_prefix_and_branch successPrefix facts
      candidatePrivate modelBraidCandidate hbranch hrel hreal hnext hmodel hbraid
      hprivate hbytes htrace)

/-! Package the semantic facts that are still supplied by the caller after the
generated success prefix and model success facts have fixed every concrete
receive input.  The package is indexed by both records, so a branch proof for
one generated result cannot be reused for another result or another model
oracle successor. -/
structure InitialRatchetSuccessSplice {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message) : Type where
  modelBraidCandidate : Model.Braid.BraidState
  hcase : AggregateReceiveAlignedCase successPrefix.decoded.header facts.modelComposite
      successPrefix.realHeader (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
      successPrefix.sparseOutput
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
      real.triple model.triple
      (successPrefix.realTripleCandidate, successPrefix.realMk)
      (facts.modelTripleCandidate, facts.modelMk)
      successPrefix.htriple facts.hmodelTriple
  hrel : SessionRefines dh K real model
  hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines successPrefix.m
      (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)
  hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session :=
          { model with
            triple := facts.modelTripleCandidate
            braid := modelBraidCandidate
            ratchetPrivate :=
              if facts.modelTripleCandidate.classical.dhsPub == model.triple.classical.dhsPub then
                model.ratchetPrivate else facts.draw }
        result := .ok facts.modelPlaintext
        oracle := oracleNext }
  hready : Model.Lifecycle.agreementFailed model = false
  hbraidReceive : Tacenta.SessionUnitBraidT3.StateRefines K
    successPrefix.braidCandidate.state
    (Model.Braid.receive K model.braid
      (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.2
  hbraid : Tacenta.SessionUnitBraidT3.StateRefines K
    successPrefix.braidCandidate.state modelBraidCandidate
  hprivate : dh.privateKey successPrefix.candidatePrivate = facts.draw
  hbytes : vecOf plaintext = facts.modelPlaintext
  htrace : trace rngNext = oracleNext.draws

/-! Build the success splice from the aligned direct/retry branch and the
    generated/model prefixes.  This is the concrete constructor used by the
    public result split: the branch is already indexed by the actual Triple
    results, while the remaining arguments are only the message, Braid, key,
    plaintext, and oracle trace relations needed to lift that branch to the
    session step. -/
def initial_ratchet_success_splice_of_aligned_branch {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (hbranch : InitialRatchetSuccessReceiveBranch
      successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
      (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
      successPrefix.sparseOutput
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
      real.triple model.triple
      (successPrefix.realTripleCandidate, successPrefix.realMk)
      (facts.modelTripleCandidate, facts.modelMk))
    (hrel : SessionRefines dh K real model)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines successPrefix.m
      (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite))
    (hkem : K = oracle.braidKem)
    (hbraidReceive : Tacenta.SessionUnitBraidT3.StateRefines K
      successPrefix.braidCandidate.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.2)
    (hprivate : dh.privateKey successPrefix.candidatePrivate = facts.draw)
    (hbytes : vecOf plaintext = facts.modelPlaintext)
    (htrace : trace rngNext = oracleNext.draws) :
    InitialRatchetSuccessSplice (dh := dh) (K := K) (trace := trace)
      successPrefix facts := by
  let modelBraidCandidate :=
    (Model.Braid.receive oracle.braidKem model.braid
      (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.2
  have hcase := initial_ratchet_success_aligned_case_of_prefix_and_branch
    successPrefix facts hbranch
  have hmodel := initial_ratchet_model_success_result_of_facts facts
  have hbraidReceive' : Tacenta.SessionUnitBraidT3.StateRefines K
      successPrefix.braidCandidate.state
      (Model.Braid.receive oracle.braidKem model.braid
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.2 := by
    simpa [hkem] using hbraidReceive
  have hbraid : Tacenta.SessionUnitBraidT3.StateRefines K
      successPrefix.braidCandidate.state modelBraidCandidate := by
    simpa [modelBraidCandidate] using hbraidReceive'
  exact {
    modelBraidCandidate := modelBraidCandidate,
    hcase := hcase,
    hrel := hrel,
    hmessageRel := hmessageRel,
    hmodel := by simpa [modelBraidCandidate] using hmodel,
    hready := facts.hready,
    hbraidReceive := by simpa [hkem] using hbraidReceive',
    hbraid := hbraid,
    hprivate := hprivate,
    hbytes := hbytes,
    htrace := htrace }

/-! Public success-splice entry that makes the result split unavoidable.  The
    caller's semantic provider is indexed by the concrete and model receive
    partitions extracted from the same successful prefixes; the resulting
    branch is then passed to the common splice constructor, whose aligned-case
    projection feeds the direct core or shared retry `StateRefines` witness
    into the session step theorem. -/
def initial_ratchet_success_splice_of_actual_receive_cases {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (hcases :
      ∀ (realCase :
          (∃ direct,
            lifecycle.receive_attempt real.triple successPrefix.realHeader
              successPrefix.recvSecret successPrefix.sendSecret
              successPrefix.newPublicBytes successPrefix.sparseOutput =
              ok (.Ok direct) ∧
            direct = (successPrefix.realTripleCandidate, successPrefix.realMk)) ∨
          (∃ reason half,
            lifecycle.receive_attempt real.triple successPrefix.realHeader
              successPrefix.recvSecret successPrefix.sendSecret
              successPrefix.newPublicBytes successPrefix.sparseOutput =
              ok (.Err reason) ∧
            lifecycle.full_store reason = ok (some half)))
      (modelCase :
          (∃ direct,
            Model.Triple.receiveDetailed model.triple
              (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
              facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
              (Model.Lifecycle.sparseOutputOf
                (Model.Braid.receive oracle.braidKem model.braid
                  (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1) =
              .ok direct ∧ direct = (facts.modelTripleCandidate, facts.modelMk)) ∨
          (∃ reason half,
            Model.Triple.receiveDetailed model.triple
              (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
              facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
              (Model.Lifecycle.sparseOutputOf
                (Model.Braid.receive oracle.braidKem model.braid
                  (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1) =
              .error reason ∧ Model.Lifecycle.fullStore reason = some half)) ,
      InitialRatchetSuccessReceiveBranch
        successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
        (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
        successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
        facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
        successPrefix.sparseOutput
        (Model.Lifecycle.sparseOutputOf
          (Model.Braid.receive oracle.braidKem model.braid
            (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
        real.triple model.triple
        (successPrefix.realTripleCandidate, successPrefix.realMk)
        (facts.modelTripleCandidate, facts.modelMk))
    (hrel : SessionRefines dh K real model)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines successPrefix.m
      (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite))
    (hkem : K = oracle.braidKem)
    (hbraidReceive : Tacenta.SessionUnitBraidT3.StateRefines K
      successPrefix.braidCandidate.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.2)
    (hprivate : dh.privateKey successPrefix.candidatePrivate = facts.draw)
    (hbytes : vecOf plaintext = facts.modelPlaintext)
    (htrace : trace rngNext = oracleNext.draws) :
    InitialRatchetSuccessSplice (dh := dh) (K := K) (trace := trace)
      successPrefix facts := by
  exact initial_ratchet_success_splice_of_aligned_branch successPrefix facts
    (initial_ratchet_success_branch_of_actual_receive_cases successPrefix facts hcases)
    hrel hmessageRel hkem hbraidReceive hprivate hbytes htrace

/-! Concrete-result variant of the splice constructor.  This is the shortest
    route for the final public composition: direct and retry providers are
    selected from the generated `receive_attempt` result, then the common
    aligned splice performs the direct-core/shared-retry projection. -/
def initial_ratchet_success_splice_of_concrete_receive_case {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (hdirect : ∀ (direct : tacenta_triple.State × Array Std.U8 32#usize),
      lifecycle.receive_attempt real.triple successPrefix.realHeader
        successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
        successPrefix.sparseOutput = ok (.Ok direct) →
      direct = (successPrefix.realTripleCandidate, successPrefix.realMk) →
      InitialRatchetSuccessBranchAt successPrefix facts)
    (hretry : ∀ (realReason : tacenta_triple.TripleError) (half : lifecycle.FullStore),
      lifecycle.receive_attempt real.triple successPrefix.realHeader
        successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
        successPrefix.sparseOutput = ok (.Err realReason) →
      lifecycle.full_store realReason = ok (some half) →
      InitialRatchetSuccessBranchAt successPrefix facts)
    (hrel : SessionRefines dh K real model)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines successPrefix.m
      (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite))
    (hkem : K = oracle.braidKem)
    (hbraidReceive : Tacenta.SessionUnitBraidT3.StateRefines K
      successPrefix.braidCandidate.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.2)
    (hprivate : dh.privateKey successPrefix.candidatePrivate = facts.draw)
    (hbytes : vecOf plaintext = facts.modelPlaintext)
    (htrace : trace rngNext = oracleNext.draws) :
    InitialRatchetSuccessSplice (dh := dh) (K := K) (trace := trace)
      successPrefix facts := by
  exact initial_ratchet_success_splice_of_aligned_branch successPrefix facts
    (initial_ratchet_success_branch_of_concrete_receive_case successPrefix facts
      hdirect hretry)
    hrel hmessageRel hkem hbraidReceive hprivate hbytes htrace

/-! Package the concrete success obligations that remain after the generated
    prefix and model facts have fixed the receive inputs.  Keeping the direct
    and full-store providers in one indexed record makes it possible to pass
    the complete success contract through the public result split without an
    untyped existential callback. -/
structure InitialRatchetConcreteSuccessProvider {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message) : Type where
  hdirect : ∀ (successPrefix : InitialRatchetSuccessPrefix rc crc real message
      rng rngNext plaintext next)
    (direct : tacenta_triple.State × Array Std.U8 32#usize),
    lifecycle.receive_attempt real.triple successPrefix.realHeader
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      successPrefix.sparseOutput = ok (.Ok direct) →
    direct = (successPrefix.realTripleCandidate, successPrefix.realMk) →
    InitialRatchetSuccessBranchAt successPrefix facts
  hretry : ∀ (successPrefix : InitialRatchetSuccessPrefix rc crc real message
      rng rngNext plaintext next)
    (realReason : tacenta_triple.TripleError) (half : lifecycle.FullStore),
    lifecycle.receive_attempt real.triple successPrefix.realHeader
      successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
      successPrefix.sparseOutput = ok (.Err realReason) →
    lifecycle.full_store realReason = ok (some half) →
    InitialRatchetSuccessBranchAt successPrefix facts
  hrel : ∀ (successPrefix : InitialRatchetSuccessPrefix rc crc real message
      rng rngNext plaintext next), SessionRefines dh K real model
  hmessageRel : ∀ (successPrefix : InitialRatchetSuccessPrefix rc crc real message
      rng rngNext plaintext next),
    Tacenta.SessionUnitBraidT3.MsgRefines successPrefix.m
      (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)
  hkem : K = oracle.braidKem
  hbraidReceive : ∀ (successPrefix : InitialRatchetSuccessPrefix rc crc real
      message rng rngNext plaintext next),
    Tacenta.SessionUnitBraidT3.StateRefines K successPrefix.braidCandidate.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.2
  hprivate : ∀ (successPrefix : InitialRatchetSuccessPrefix rc crc real message
      rng rngNext plaintext next), dh.privateKey successPrefix.candidatePrivate = facts.draw
  hbytes : ∀ (successPrefix : InitialRatchetSuccessPrefix rc crc real message
      rng rngNext plaintext next), vecOf plaintext = facts.modelPlaintext
  htrace : trace rngNext = oracleNext.draws

def initial_ratchet_success_splice_of_concrete_provider {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (provider : InitialRatchetConcreteSuccessProvider
      (rc := rc) (crc := crc) (trace := trace) (dh := dh) (K := K)
      (view := view) (oracle := oracle) (oracleNext := oracleNext)
      (real := real) (model := model) (message := message) (rng := rng)
      (rngNext := rngNext) (plaintext := plaintext) (next := next) facts) :
    InitialRatchetSuccessSplice (dh := dh) (K := K) (trace := trace)
      successPrefix facts := by
  exact initial_ratchet_success_splice_of_concrete_receive_case successPrefix facts
    (provider.hdirect successPrefix) (provider.hretry successPrefix)
    (provider.hrel successPrefix) (provider.hmessageRel successPrefix) provider.hkem
    (provider.hbraidReceive successPrefix) (provider.hprivate successPrefix)
    (provider.hbytes successPrefix) provider.htrace

/-! Lift a model-facts/provider pair into the existential success callback
    expected by the result splitter.  The callback still receives the exact
    generated `Ok` result first; neither the model successor nor the concrete
    provider can be selected independently of that result. -/
theorem initial_ratchet_success_callback_of_concrete_provider
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (hmodel : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∃ oracleNext, Nonempty (InitialRatchetModelSuccessFacts view oracle oracleNext
          model decoded.message.deref))
    (hprovider : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∀ (oracleNext : Model.Lifecycle.Oracle)
          (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model
            decoded.message.deref),
          InitialRatchetConcreteSuccessProvider
            (rc := rc) (crc := crc) (trace := trace) (dh := dh) (K := K)
            (view := view) (oracle := oracle) (oracleNext := oracleNext)
            (real := real) (model := model) (message := decoded.message.deref)
            (rng := rng) (rngNext := rngNext) (plaintext := plaintext) (next := next)
            facts) :
    ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∃ oracleNext, ∃ facts : InitialRatchetModelSuccessFacts view oracle oracleNext
          model decoded.message.deref,
          Nonempty (∀ successPrefix : InitialRatchetSuccessPrefix rc crc real
              decoded.message.deref rng rngNext plaintext next,
            InitialRatchetSuccessSplice (dh := dh) (K := K) (trace := trace)
              successPrefix facts) := by
  intro decoded established hdecode hestablished he hi plaintext next rngNext hcall
  obtain ⟨oracleNext, ⟨facts⟩⟩ := hmodel decoded established hdecode hestablished he hi
    plaintext next rngNext hcall
  refine ⟨oracleNext, facts, ⟨?_⟩⟩
  intro successPrefix
  exact initial_ratchet_success_splice_of_concrete_provider successPrefix facts
    (hprovider decoded established hdecode hestablished he hi plaintext next rngNext hcall
      oracleNext facts)

/-! Stronger success callback entry: the model-facts record is obtained by
    inverting the exact model `decryptRatchet` success result, rather than
    being supplied as an independent existential. -/
theorem initial_ratchet_success_callback_of_model_step_and_provider
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (hmodel : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∃ (modelNext : Model.Lifecycle.Session) (modelPlaintext : Bytes)
          (oracleNext : Model.Lifecycle.Oracle),
          Model.Lifecycle.decryptRatchet view oracle model (sliceOf decoded.message.deref) =
            { session := modelNext, result := .ok modelPlaintext, oracle := oracleNext })
    (hprovider : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∀ (modelNext : Model.Lifecycle.Session) (modelPlaintext : Bytes)
          (oracleNext : Model.Lifecycle.Oracle)
          (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model
            decoded.message.deref),
          InitialRatchetConcreteSuccessProvider
            (rc := rc) (crc := crc) (trace := trace) (dh := dh) (K := K)
            (view := view) (oracle := oracle) (oracleNext := oracleNext)
            (real := real) (model := model) (message := decoded.message.deref)
            (rng := rng) (rngNext := rngNext) (plaintext := plaintext) (next := next)
            facts) :
    ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∃ oracleNext, ∃ facts : InitialRatchetModelSuccessFacts view oracle oracleNext
          model decoded.message.deref,
          Nonempty (∀ successPrefix : InitialRatchetSuccessPrefix rc crc real
              decoded.message.deref rng rngNext plaintext next,
            InitialRatchetSuccessSplice (dh := dh) (K := K) (trace := trace)
              successPrefix facts) := by
  intro decoded established hdecode hestablished he hi plaintext next rngNext hcall
  obtain ⟨modelNext, modelPlaintext, oracleNext, hmodelStep⟩ :=
    hmodel decoded established hdecode hestablished he hi plaintext next rngNext hcall
  have hready : Model.Lifecycle.agreementFailed model = false := by
    by_cases hfailed : Model.Lifecycle.agreementFailed model = true
    · simp [Model.Lifecycle.decryptRatchet, hfailed] at hmodelStep
    · cases h : Model.Lifecycle.agreementFailed model <;> simp_all
  obtain ⟨facts⟩ := initial_ratchet_model_success_facts_of_result view oracle oracleNext
    model modelNext decoded.message.deref modelPlaintext
    hready hmodelStep
  refine ⟨oracleNext, facts, ⟨?_⟩⟩
  intro successPrefix
  exact initial_ratchet_success_splice_of_concrete_provider successPrefix facts
    (hprovider decoded established hdecode hestablished he hi plaintext next rngNext hcall
      modelNext modelPlaintext oracleNext facts)

def initial_ratchet_success_evidence_of_splice {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (successPrefix : InitialRatchetSuccessPrefix rc crc real message rng rngNext
      plaintext next)
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (splice : InitialRatchetSuccessSplice (dh := dh) (K := K) (trace := trace)
      successPrefix facts)
    (hreal : lifecycle.Session.decrypt_ratchet rc crc real message rng =
      ok (.Ok plaintext, next, rngNext)) :
    InitialRatchetSuccessEvidence rc crc trace dh K view oracle real model message rng
      plaintext next rngNext := by
  let hbranch := initial_ratchet_success_branch_of_aligned_case
    successPrefix.decoded.header facts.modelComposite successPrefix.realHeader
    (Model.Lifecycle.tripleHeaderOf facts.modelComposite)
    successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
    facts.modelDhOutRecv facts.modelDhOutSend (oracle.dhPublic facts.draw)
    successPrefix.sparseOutput
    (Model.Lifecycle.sparseOutputOf
      (Model.Braid.receive oracle.braidKem model.braid
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.1)
    real.triple model.triple
    (successPrefix.realTripleCandidate, successPrefix.realMk)
    (facts.modelTripleCandidate, facts.modelMk)
    successPrefix.htriple facts.hmodelTriple splice.hcase
  obtain ⟨_, hnext⟩ := initial_ratchet_success_next_of_prefix successPrefix hreal
    splice.hrel facts.modelComposite splice.hmessageRel splice.hbraidReceive splice.hready
  exact initial_ratchet_success_evidence_of_prefix_and_branch successPrefix facts
    successPrefix.candidatePrivate splice.modelBraidCandidate hbranch splice.hrel hreal
    hnext splice.hmodel splice.hbraid splice.hprivate splice.hbytes splice.htrace

/-! Derive the indexed splice from the actual generated success result.  The
caller still supplies only the model/branch facts; the prefix itself must come
from the exact `decrypt_ratchet = Ok` equation. -/
noncomputable def initial_ratchet_success_evidence_of_result_and_splice {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hreal : lifecycle.Session.decrypt_ratchet rc crc real message rng =
      ok (.Ok plaintext, next, rngNext))
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (hsplice : ∀ successPrefix : InitialRatchetSuccessPrefix rc crc real message rng
      rngNext plaintext next,
      InitialRatchetSuccessSplice (dh := dh) (K := K) (trace := trace)
        successPrefix facts) :
    InitialRatchetSuccessEvidence rc crc trace dh K view oracle real model message rng
      plaintext next rngNext := by
  let successPrefix := Classical.choice (initial_ratchet_success_prefix_of_result
    rc crc hz32 hzKeys real message rng rngNext plaintext next hreal)
  exact initial_ratchet_success_evidence_of_splice successPrefix facts
    (hsplice successPrefix) hreal

/-! Result-indexed success construction with no abstract splice callback.  The
    generated `Ok` result fixes the success prefix; the two branch providers
    below are therefore indexed by that exact prefix and select only from the
    concrete `receive_attempt` result.  This is the adapter used when wiring
    the success arm into `InitialRatchetRefines`. -/
noncomputable def initial_ratchet_success_evidence_of_result_and_concrete_case
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hreal : lifecycle.Session.decrypt_ratchet rc crc real message rng =
      ok (.Ok plaintext, next, rngNext))
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (hdirect : ∀ (successPrefix : InitialRatchetSuccessPrefix rc crc real message
        rng rngNext plaintext next)
      (direct : tacenta_triple.State × Array Std.U8 32#usize),
      lifecycle.receive_attempt real.triple successPrefix.realHeader
        successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
        successPrefix.sparseOutput = ok (.Ok direct) →
      direct = (successPrefix.realTripleCandidate, successPrefix.realMk) →
      InitialRatchetSuccessBranchAt successPrefix facts)
    (hretry : ∀ (successPrefix : InitialRatchetSuccessPrefix rc crc real message
        rng rngNext plaintext next)
      (realReason : tacenta_triple.TripleError) (half : lifecycle.FullStore),
      lifecycle.receive_attempt real.triple successPrefix.realHeader
        successPrefix.recvSecret successPrefix.sendSecret successPrefix.newPublicBytes
        successPrefix.sparseOutput = ok (.Err realReason) →
      lifecycle.full_store realReason = ok (some half) →
      InitialRatchetSuccessBranchAt successPrefix facts)
    (hrel : ∀ (successPrefix : InitialRatchetSuccessPrefix rc crc real message
        rng rngNext plaintext next), SessionRefines dh K real model)
    (hmessageRel : ∀ (successPrefix : InitialRatchetSuccessPrefix rc crc real message
        rng rngNext plaintext next),
      Tacenta.SessionUnitBraidT3.MsgRefines successPrefix.m
        (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite))
    (hkem : K = oracle.braidKem)
    (hbraidReceive : ∀ (successPrefix : InitialRatchetSuccessPrefix rc crc real
        message rng rngNext plaintext next),
      Tacenta.SessionUnitBraidT3.StateRefines K successPrefix.braidCandidate.state
        (Model.Braid.receive K model.braid
          (Model.Lifecycle.braidMessageOf view model.braid facts.modelComposite)).2.2)
    (hprivate : ∀ (successPrefix : InitialRatchetSuccessPrefix rc crc real message
        rng rngNext plaintext next), dh.privateKey successPrefix.candidatePrivate = facts.draw)
    (hbytes : ∀ (successPrefix : InitialRatchetSuccessPrefix rc crc real message
        rng rngNext plaintext next), vecOf plaintext = facts.modelPlaintext)
    (htrace : trace rngNext = oracleNext.draws) :
    InitialRatchetSuccessEvidence rc crc trace dh K view oracle real model message rng
      plaintext next rngNext := by
  let successPrefix := Classical.choice (initial_ratchet_success_prefix_of_result
    rc crc hz32 hzKeys real message rng rngNext plaintext next hreal)
  have hsplice : InitialRatchetSuccessSplice (dh := dh) (K := K) (trace := trace)
      successPrefix facts :=
    initial_ratchet_success_splice_of_concrete_receive_case successPrefix facts
      (hdirect successPrefix) (hretry successPrefix) (hrel successPrefix)
      (hmessageRel successPrefix) hkem (hbraidReceive successPrefix)
      (hprivate successPrefix) (hbytes successPrefix) htrace
  exact initial_ratchet_success_evidence_of_splice successPrefix facts hsplice hreal

noncomputable def initial_ratchet_success_evidence_of_result_and_concrete_provider
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle oracleNext : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng rngNext : R}
    {plaintext : alloc.vec.Vec Std.U8} {next : lifecycle.Session}
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hreal : lifecycle.Session.decrypt_ratchet rc crc real message rng =
      ok (.Ok plaintext, next, rngNext))
    (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model message)
    (provider : InitialRatchetConcreteSuccessProvider
      (rc := rc) (crc := crc) (trace := trace) (dh := dh) (K := K)
      (view := view) (oracle := oracle) (oracleNext := oracleNext)
      (real := real) (model := model) (message := message) (rng := rng)
      (rngNext := rngNext) (plaintext := plaintext) (next := next) facts) :
    InitialRatchetSuccessEvidence rc crc trace dh K view oracle real model message rng
      plaintext next rngNext := by
  let successPrefix := Classical.choice (initial_ratchet_success_prefix_of_result
    rc crc hz32 hzKeys real message rng rngNext plaintext next hreal)
  exact initial_ratchet_success_evidence_of_splice successPrefix facts
    (initial_ratchet_success_splice_of_concrete_provider successPrefix facts provider)
    hreal

theorem initial_ratchet_success_step_from_evidence {R : Type}
    (evidence : InitialRatchetSuccessEvidence rc crc trace dh K view oracle real model
      message rng plaintext next rngNext) :
    StepRefines trace dh K (.Ok plaintext, next, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  have hreal := evidence.hreal
  rw [evidence.hnext] at hreal
  have hstep := decrypt_ratchet_success_step_from_aligned_receive_cases
    rc crc trace dh K view oracle evidence.oracleNext real model message rng rngNext
    plaintext evidence.modelPlaintext real.triple evidence.realTripleCandidate
    evidence.realBraidCandidate evidence.candidatePrivate evidence.draw
    evidence.modelTripleCandidate evidence.modelBraidCandidate evidence.composite
    evidence.modelComposite evidence.header evidence.modelHeader evidence.dhOutRecv
    evidence.dhOutSend evidence.newDhsPub evidence.modelDhOutRecv
    evidence.modelDhOutSend evidence.modelNewDhsPub evidence.output evidence.modelOutput
    evidence.realMk evidence.modelMk evidence.hreceiveReal evidence.hreceiveModel
    evidence.hcase evidence.hrel hreal evidence.hmodel evidence.hbraid
    evidence.hprivate evidence.hbytes evidence.htrace
  simpa [evidence.hnext] using hstep

/-- Inner-call evidence is needed only after all initial-wrapper guards pass. -/
def InitialRatchetRefines {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R) : Prop :=
  ∀ (decoded : tacenta_wire.DecodedInitial) (established : alloc.vec.Vec Std.U8),
    tacenta_wire.decode_initial message = ok (.Ok decoded) →
    real.established_ephemeral = some established →
    vecOf established = vecOf decoded.ephemeral →
    vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
    ∃ output,
      lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng = ok output ∧
      StepRefines trace dh K output (Model.Lifecycle.decryptRatchet view oracle model
        (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage)

/-! ## T1-to-T3 bridge for the inner ratchet call

The generated T1 theorem proves that `decrypt_ratchet` returns some concrete
result under the boundary contracts and headroom conditions.  Keeping that
existence step separate means the aggregate T3 work only has to establish the
semantic relation for the result selected by the translated computation.
-/

theorem decrypt_ratchet_refines_of_t1
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (boundary : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (hrefines : ∀ output,
      lifecycle.Session.decrypt_ratchet rc crc real message rng = ok output →
      StepRefines trace dh K output
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet rc crc real message rng = ok output ∧
      StepRefines trace dh K output
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  obtain ⟨output, hcall, _⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.decrypt_ratchet_no_panic rc crc boundary real message rng headroom)
  exact ⟨output, hcall, hrefines output hcall⟩

/-- Construct all six routes from the decoded input and state. The existential
route is a proposition so decoder proofs can be eliminated without choosing a
route supplied by the caller. -/
theorem initial_dispatch_route_from_ratchet
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (codec : DhCodecOf dh)
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (hreceive : InitialRatchetRefines rc crc trace dh K view oracle real model message rng) :
    Nonempty (InitialDispatchRoute rc crc trace dh K view oracle real model message rng) := by
  rcases initial_decode_cases message with ⟨reason, hdecode⟩ | ⟨decoded, hdecode⟩
  · exact ⟨.decodeRefusal (decrypt_initial_decode_refusal_refines rc crc trace dh K view
      oracle real model message rng reason ctx.hrel ctx.htrace ctx.htype hdecode)⟩
  · cases hestablished : real.established_ephemeral with
    | none =>
        exact ⟨initial_dispatch_no_established_from_premises ctx decoded hdecode hestablished⟩
    | some established =>
        by_cases he : vecOf established = vecOf decoded.ephemeral
        · by_cases hi : vecOf decoded.identity =
            Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public)
          · obtain ⟨⟨result, next, rngNext⟩, hcall, hstep⟩ :=
              hreceive decoded established hdecode hestablished he hi
            have hw := decrypt_initial_repeat_step_refines rc crc trace dh codec K view oracle
              real model message rng established decoded (result, next, rngNext)
              ctx.hrel ctx.htype hdecode hestablished he hi hcall hstep
            cases result with
            | Err reason => exact ⟨.repeatRefusal hw⟩
            | Ok plaintext => exact ⟨.repeatSuccess hw⟩
          · exact ⟨initial_dispatch_identity_mismatch_from_premises (codec := codec)
              ctx established decoded hdecode hestablished he hi⟩
        · exact ⟨initial_dispatch_ephemeral_mismatch_from_premises
            ctx established decoded hdecode hestablished he⟩

/-- Initial-wrapper T3, conditional only on inner ratchet refinement and the
codec contract. No route or branch callback is an input. -/
theorem decrypt_initial_refines_from_ratchet
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (codec : DhCodecOf dh)
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (hreceive : InitialRatchetRefines rc crc trace dh K view oracle real model message rng) :
    PublicDecryptWitness rc crc trace dh K view oracle real model message rng := by
  obtain ⟨route⟩ := initial_dispatch_route_from_ratchet codec ctx hreceive
  exact initial_dispatch_join route

/-! Split the T1-produced inner result before applying its semantic adapter.
    The two callbacks are intentionally result-shaped: a refusal proof cannot
    be reused for a success result, and vice versa.  This is the outer
    `InitialRatchetRefines` case split that the direct/retry receive adapters
    feed once their actual Triple branch has been classified. -/
theorem initial_ratchet_refines_of_t1_result_split
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (boundary : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (hrefusal : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Err reason, next, rngNext) →
        StepRefines trace dh K (.Err reason, next, rngNext)
          (Model.Lifecycle.decryptRatchet view oracle model
            (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage))
    (hsuccess : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        StepRefines trace dh K (.Ok plaintext, next, rngNext)
          (Model.Lifecycle.decryptRatchet view oracle model
            (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage)) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  intro decoded established hdecode hestablished he hi
  obtain ⟨output, hcall, _⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.decrypt_ratchet_no_panic rc crc boundary real
      decoded.message.deref rng headroom)
  rcases output with ⟨result, next, rngNext⟩
  cases result with
  | Err reason =>
      exact ⟨(.Err reason, next, rngNext), hcall,
        hrefusal decoded established hdecode hestablished he hi reason next rngNext hcall⟩
  | Ok plaintext =>
      exact ⟨(.Ok plaintext, next, rngNext), hcall,
        hsuccess decoded established hdecode hestablished he hi plaintext next rngNext hcall⟩

/-! Refusal evidence uses the same actual-result boundary.  The refusal
    family is intentionally left open to the four concrete adapters (DH,
    Triple, AEAD and decode); each adapter must provide this exact call/result
    pair before the dispatcher can consume it. -/
structure InitialRatchetRefusalEvidence {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R) : Type where
  hcall : lifecycle.Session.decrypt_ratchet rc crc real message rng =
    ok (.Err reason, next, rngNext)
  hstep : StepRefines trace dh K (.Err reason, next, rngNext)
    (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))

def initial_ratchet_refusal_evidence_of_pair {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err reason, next, rngNext))
    (hstep : StepRefines trace dh K (.Err reason, next, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))) :
    InitialRatchetRefusalEvidence rngCore cryptoRng trace dh K view oracle real model
      message rng reason next rngNext :=
  { hcall := hcall, hstep := hstep }

/-! A model random-source ceiling is only compatible with an empty draw
trace.  This small contradiction lemma makes the missing ceiling premise
explicit: any caller that proves the receive path starts with a concrete draw
may eliminate the model `.ceiling` case before constructing a public refusal
route. -/
theorem model_random32_none_impossible_of_trace_head
    (trace : R → List Model.Lifecycle.Key)
    (oracle : Model.Lifecycle.Oracle) (rng : R)
    (htrace : trace rng = oracle.draws)
    (hhead : ∃ draw rest, trace rng = draw :: rest)
    (hnone : Model.Lifecycle.random32 oracle = none) : False := by
  obtain ⟨draw, rest, hhead⟩ := hhead
  have horacle : oracle.draws = draw :: rest := htrace.symm.trans hhead
  simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, horacle] at hnone

theorem model_ceiling_result_impossible_of_trace_head
    {R : Type} (trace : R → List Model.Lifecycle.Key)
    (oracle oracleResult : Model.Lifecycle.Oracle) (rng : R)
    (view : Model.Lifecycle.CodewordView) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecoded : ∃ composite ciphertext,
      Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (composite, ciphertext))
    (hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session := model, result := .error .ceiling, oracle := oracleResult })
    (htrace : trace rng = oracle.draws)
    (hhead : ∃ draw rest, trace rng = draw :: rest) : False := by
  obtain ⟨composite, ciphertext, hdecode⟩ := hdecoded
  simp only [Model.Lifecycle.decryptRatchet, hready, hdecode] at hmodel
  cases hdh : oracle.dhAgree model.ratchetPrivate composite.dh with
  | none => simp [hdh] at hmodel
  | some dhOutRecv =>
      cases hdraw : Model.Lifecycle.random32 oracle with
      | none =>
              exact model_random32_none_impossible_of_trace_head trace oracle rng
                htrace hhead hdraw
      | some pair =>
          obtain ⟨draw, oracleNext⟩ := pair
          cases hsecond : oracle.dhAgree draw composite.dh with
          | none =>
              have hresult := congrArg (fun output => output.result) hmodel
              simp [hdh, hdraw, hsecond] at hresult
          | some dhOutSend =>
              cases htriple : Model.Lifecycle.receiveWithEviction model.triple composite
                  (Model.Lifecycle.tripleHeaderOf composite) dhOutRecv dhOutSend
                  (oracle.dhPublic draw)
                  (Model.Lifecycle.sparseOutputOf
                    (Model.Braid.receive oracle.braidKem model.braid
                      (Model.Lifecycle.braidMessageOf view model.braid composite)).2.1) with
              | error modelReason =>
                  have hresult := congrArg (fun output => output.result) hmodel
                  simp [hdh, hdraw, hsecond, htriple, Model.Lifecycle.tripleReceiveRefusalOf]
                    at hresult
                  cases modelReason <;> simp at hresult
              | ok triplePair =>
                  obtain ⟨tripleCandidate, messageKey⟩ := triplePair
                  cases haead : oracle.aeadOpen
                      (Model.State.messageKeys messageKey .tacenta).1
                      (Model.State.messageKeys messageKey .tacenta).2.1
                      (Model.State.messageKeys messageKey .tacenta).2.2 ciphertext
                      (Model.Messages.concatAd model.identityAd
                        (Model.CompositeHeader.encode composite)) with
                  | none =>
                      have hresult := congrArg (fun output => output.result) hmodel
                      simp [hdh, hdraw, hsecond, htriple, haead] at hresult
                  | some plaintext =>
                      have hresult := congrArg (fun output => output.result) hmodel
                      simp [hdh, hdraw, hsecond, htriple, haead] at hresult

/-! Invert an exact model refusal after a valid composite decode. The
    classifier preserves the branch-local composite, DH draws, Triple result,
    AEAD verdict and oracle successor; the ceiling arm is explicit so a caller
    cannot silently omit a failed model random draw. -/
inductive InitialRatchetModelRefusalCase
    (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle)
    (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) :
    Model.Lifecycle.Refusal → Model.Lifecycle.Oracle → Prop where
  | firstDh (composite : Model.CompositeHeader.Composite)
      (ciphertext : Bytes)
      (hdecode : Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (composite, ciphertext))
      (hfirst : oracle.dhAgree model.ratchetPrivate composite.dh = none) :
      InitialRatchetModelRefusalCase view oracle model message
        (.handshake .nonContributoryAgreement) oracle
  | secondDh (composite : Model.CompositeHeader.Composite)
      (ciphertext : Bytes) (draw : Model.Lifecycle.Key)
      (oracleNext : Model.Lifecycle.Oracle)
      (hdecode : Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (composite, ciphertext))
      (hfirst : ∃ dhOutRecv, oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv)
      (hdraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
      (hsecond : ∃ dhOutRecv : Model.Lifecycle.Key, oracle.dhAgree draw composite.dh = none) :
      InitialRatchetModelRefusalCase view oracle model message
        (.handshake .nonContributoryAgreement) oracleNext
  | ceiling (composite : Model.CompositeHeader.Composite)
      (ciphertext : Bytes) (dhOutRecv : Model.Lifecycle.Key)
      (hdecode : Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (composite, ciphertext))
      (hfirst : oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv)
      (hdraw : Model.Lifecycle.random32 oracle = none) :
      InitialRatchetModelRefusalCase view oracle model message .ceiling oracle
  | triple (composite : Model.CompositeHeader.Composite)
      (ciphertext : Bytes) (draw : Model.Lifecycle.Key)
      (oracleNext : Model.Lifecycle.Oracle)
      (modelReason : Model.Triple.ReceiveRefusal)
      (dhOutRecv dhOutSend : Model.Lifecycle.Key)
      (hdecode : Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (composite, ciphertext))
      (hfirst : oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv)
      (hdraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
      (hsecond : oracle.dhAgree draw composite.dh = some dhOutSend)
      (htriple : Model.Lifecycle.receiveWithEviction model.triple composite
          (Model.Lifecycle.tripleHeaderOf composite) dhOutRecv dhOutSend
          (oracle.dhPublic draw)
          (Model.Lifecycle.sparseOutputOf
            (Model.Braid.receive oracle.braidKem model.braid
              (Model.Lifecycle.braidMessageOf view model.braid composite)).2.1) =
          .error modelReason) :
      InitialRatchetModelRefusalCase view oracle model message
        (Model.Lifecycle.tripleReceiveRefusalOf modelReason) oracleNext
  | aead (composite : Model.CompositeHeader.Composite)
      (ciphertext : Bytes) (draw : Model.Lifecycle.Key)
      (oracleNext : Model.Lifecycle.Oracle)
      (messageKey : Model.Lifecycle.Key)
      (dhOutRecv dhOutSend : Model.Lifecycle.Key)
      (tripleCandidate : Model.Triple.State)
      (hdecode : Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (composite, ciphertext))
      (hfirst : oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv)
      (hdraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
      (hsecond : oracle.dhAgree draw composite.dh = some dhOutSend)
      (htriple : Model.Lifecycle.receiveWithEviction model.triple composite
          (Model.Lifecycle.tripleHeaderOf composite) dhOutRecv dhOutSend
          (oracle.dhPublic draw)
          (Model.Lifecycle.sparseOutputOf
            (Model.Braid.receive oracle.braidKem model.braid
              (Model.Lifecycle.braidMessageOf view model.braid composite)).2.1) =
          .ok (tripleCandidate, messageKey))
      (haead : oracle.aeadOpen
        (Model.State.messageKeys messageKey .tacenta).1
        (Model.State.messageKeys messageKey .tacenta).2.1
        (Model.State.messageKeys messageKey .tacenta).2.2 ciphertext
        (Model.Messages.concatAd model.identityAd
          (Model.CompositeHeader.encode composite)) = none) :
      InitialRatchetModelRefusalCase view oracle model message .aead oracleNext

 theorem initial_ratchet_model_refusal_case_of_result
    (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (model : Model.Lifecycle.Session) (message : Slice Std.U8)
    (reason : Model.Lifecycle.Refusal)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecoded : ∃ composite ciphertext, Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (composite, ciphertext))
    (hmodel : Model.Lifecycle.decryptRatchet view oracle model (sliceOf message) =
      { session := model, result := .error reason, oracle := oracleNext}) :
    Nonempty (InitialRatchetModelRefusalCase view oracle model message reason oracleNext) := by
  obtain ⟨composite, ciphertext, hd⟩ := hdecoded
  simp only [Model.Lifecycle.decryptRatchet, hready, hd] at hmodel
  cases hr : oracle.dhAgree model.ratchetPrivate composite.dh with
    | none =>
      simp [hd, hr] at hmodel
      have hreason : reason = .handshake .nonContributoryAgreement := hmodel.1.symm
      have horacle : oracleNext = oracle := hmodel.2.symm
      subst reason
      subst oracleNext
      exact ⟨.firstDh composite ciphertext hd hr⟩
    | some dhOutRecv =>
      cases hdraw : Model.Lifecycle.random32 oracle with
      | none =>
        simp [hd, hr, hdraw] at hmodel
        have hreason : reason = .ceiling := hmodel.1.symm
        have horacle : oracleNext = oracle := hmodel.2.symm
        subst reason
        subst oracleNext
        exact ⟨.ceiling composite ciphertext dhOutRecv hd hr hdraw⟩
      | some pair =>
        obtain ⟨draw, oracleNext'⟩ := pair
        cases hs : oracle.dhAgree draw composite.dh with
        | none =>
          simp [hd, hr, hdraw, hs] at hmodel
          have hreason : reason = .handshake .nonContributoryAgreement := hmodel.1.symm
          have horacle : oracleNext = oracleNext' := hmodel.2.symm
          subst reason
          subst oracleNext
          exact ⟨.secondDh composite ciphertext draw oracleNext' hd
            ⟨dhOutRecv, hr⟩ hdraw ⟨draw, hs⟩⟩
        | some dhOutSend =>
          cases ht : Model.Lifecycle.receiveWithEviction model.triple composite
              (Model.Lifecycle.tripleHeaderOf composite) dhOutRecv dhOutSend
              (oracle.dhPublic draw)
              (Model.Lifecycle.sparseOutputOf
                (Model.Braid.receive oracle.braidKem model.braid
                  (Model.Lifecycle.braidMessageOf view model.braid composite)).2.1) with
          | error modelReason =>
            simp [hd, hr, hdraw, hs, ht] at hmodel
            have hreason : reason = Model.Lifecycle.tripleReceiveRefusalOf modelReason := hmodel.1.symm
            have horacle : oracleNext = oracleNext' := hmodel.2.symm
            subst reason
            subst oracleNext
            exact ⟨.triple composite ciphertext draw oracleNext' modelReason
              dhOutRecv dhOutSend hd hr hdraw hs ht⟩
          | ok pair =>
            obtain ⟨tripleCandidate, messageKey⟩ := pair
            cases ha : oracle.aeadOpen
                (Model.State.messageKeys messageKey .tacenta).1
                (Model.State.messageKeys messageKey .tacenta).2.1
                (Model.State.messageKeys messageKey .tacenta).2.2 ciphertext
                (Model.Messages.concatAd model.identityAd
                  (Model.CompositeHeader.encode composite)) with
            | none =>
              simp [hd, hr, hdraw, hs, ht, ha] at hmodel
              have hreason : reason = .aead := hmodel.1.symm
              have horacle : oracleNext = oracleNext' := hmodel.2.symm
              subst reason
              subst oracleNext
              exact ⟨.aead composite ciphertext draw oracleNext' messageKey
                dhOutRecv dhOutSend tripleCandidate hd hr hdraw hs ht ha⟩
            | some plaintext => simp [hd, hr, hdraw, hs, ht, ha] at hmodel


/-! Typed sum of the five refusal route families.  The index carries the
    exact public error, successor session, and randomness state, so a route
    cannot be re-labelled or detached from the generated refusal result when
    it is handed to the T1 result splitter. -/
inductive InitialRatchetRefusalRoute
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R) :
    lifecycle.Error → lifecycle.Session → R → Type where
  | terminal
      (e : InitialRatchetRefusalEvidence rc crc trace dh K view oracle real model
        message rng .AgreementFailed real rng) :
      InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        message rng .AgreementFailed real rng
  | decode (realReason : tacenta_wire.DecodeError)
      (e : InitialRatchetRefusalEvidence rc crc trace dh K view oracle real model
        message rng (.Decode realReason) real rng) :
      InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        message rng (.Decode realReason) real rng
  | dh (rngAfter : R)
      (e : InitialRatchetRefusalEvidence rc crc trace dh K view oracle real model
        message rng (.Handshake SessionError.NonContributoryAgreement) real rngAfter) :
      InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        message rng (.Handshake SessionError.NonContributoryAgreement) real rngAfter
  | triple (realReason : tacenta_triple.TripleError)
      (next : lifecycle.Session) (rngNext : R)
      (e : InitialRatchetRefusalEvidence rc crc trace dh K view oracle real model
        message rng (.Triple realReason) next rngNext) :
      InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        message rng (.Triple realReason) next rngNext
  | aead (next : lifecycle.Session) (rngNext : R)
      (e : InitialRatchetRefusalEvidence rc crc trace dh K view oracle real model
        message rng .Aead next rngNext) :
      InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        message rng .Aead next rngNext

/-! Split the classifier into named branch providers before constructing a
    route.  Keeping the five callbacks separate prevents a provider for one
    refusal family from silently serving another family; the ceiling callback
    must discharge the explicit impossible-random-source case. -/
theorem initial_ratchet_refusal_case_dispatch
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    {reason : lifecycle.Error} {next : lifecycle.Session} {rngNext : R}
    (hcase : ∃ (modelReason : Model.Lifecycle.Refusal) (oracleNext : Model.Lifecycle.Oracle),
      InitialRatchetModelRefusalCase view oracle model message modelReason oracleNext)
    (hceiling : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (dhOutRecv : Model.Lifecycle.Key),
      Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (composite, ciphertext) →
      oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →
      Model.Lifecycle.random32 oracle = none → False)
    (hfirstDh : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (composite, ciphertext) →
      oracle.dhAgree model.ratchetPrivate composite.dh = none →
      Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        message rng reason next rngNext))
    (hsecondDh : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (draw : Model.Lifecycle.Key) (oracleAfter : Model.Lifecycle.Oracle),
      Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (composite, ciphertext) →
      (∃ dhOutRecv, oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv) →
      Model.Lifecycle.random32 oracle = some (draw, oracleAfter) →
      (∃ dhOutRecv : Model.Lifecycle.Key, oracle.dhAgree draw composite.dh = none) →
      Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        message rng reason next rngNext))
    (htripleProvider : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (draw : Model.Lifecycle.Key) (oracleAfter : Model.Lifecycle.Oracle)
      (modelReason : Model.Triple.ReceiveRefusal)
      (dhOutRecv dhOutSend : Model.Lifecycle.Key),
      Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (composite, ciphertext) →
      oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →
      Model.Lifecycle.random32 oracle = some (draw, oracleAfter) →
      oracle.dhAgree draw composite.dh = some dhOutSend →
      Model.Lifecycle.receiveWithEviction model.triple composite
        (Model.Lifecycle.tripleHeaderOf composite) dhOutRecv dhOutSend
        (oracle.dhPublic draw)
        (Model.Lifecycle.sparseOutputOf
          (Model.Braid.receive oracle.braidKem model.braid
            (Model.Lifecycle.braidMessageOf view model.braid composite)).2.1) =
        .error modelReason →
      Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        message rng reason next rngNext))
    (haeadProvider : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (draw : Model.Lifecycle.Key) (oracleAfter : Model.Lifecycle.Oracle)
      (messageKey : Model.Lifecycle.Key)
      (dhOutRecv dhOutSend : Model.Lifecycle.Key)
      (tripleCandidate : Model.Triple.State),
      Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (composite, ciphertext) →
      oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →
      Model.Lifecycle.random32 oracle = some (draw, oracleAfter) →
      oracle.dhAgree draw composite.dh = some dhOutSend →
      Model.Lifecycle.receiveWithEviction model.triple composite
        (Model.Lifecycle.tripleHeaderOf composite) dhOutRecv dhOutSend
        (oracle.dhPublic draw)
        (Model.Lifecycle.sparseOutputOf
          (Model.Braid.receive oracle.braidKem model.braid
            (Model.Lifecycle.braidMessageOf view model.braid composite)).2.1) =
        .ok (tripleCandidate, messageKey) →
      oracle.aeadOpen
        (Model.State.messageKeys messageKey .tacenta).1
        (Model.State.messageKeys messageKey .tacenta).2.1
        (Model.State.messageKeys messageKey .tacenta).2.2 ciphertext
        (Model.Messages.concatAd model.identityAd
          (Model.CompositeHeader.encode composite)) = none →
      Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        message rng reason next rngNext)) :
    Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
      message rng reason next rngNext) := by
  obtain ⟨modelReason, oracleNext, hcase⟩ := hcase
  cases hcase with
  | firstDh composite ciphertext hdecode hfirst =>
      exact hfirstDh composite ciphertext hdecode hfirst
  | secondDh composite ciphertext draw oracleAfter hdecode hfirst hdraw hsecond =>
      exact hsecondDh composite ciphertext draw oracleNext hdecode hfirst hdraw hsecond
  | ceiling composite ciphertext dhOutRecv hdecode hfirst hdraw =>
      exact False.elim (hceiling composite ciphertext dhOutRecv hdecode hfirst hdraw)
  | triple composite ciphertext draw oracleAfter modelReason dhOutRecv dhOutSend
      hdecode hfirst hdraw hsecond htriple =>
      exact htripleProvider composite ciphertext draw oracleNext modelReason dhOutRecv dhOutSend
        hdecode hfirst hdraw hsecond htriple
  | aead composite ciphertext draw oracleAfter messageKey dhOutRecv dhOutSend
      tripleCandidate hdecode hfirst hdraw hsecond htriple haead =>
      exact haeadProvider composite ciphertext draw oracleNext messageKey dhOutRecv dhOutSend
        tripleCandidate hdecode hfirst hdraw hsecond htriple haead

/-! Package the complete result-shaped refusal evidence once, so the public
    splitter can consume branch-specific providers without passing an
    unindexed route callback through every layer. -/
structure InitialRatchetRefusalBranchInput
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    (message : Slice Std.U8) (rng : R) where
  decoded : tacenta_wire.DecodedInitial
  established : alloc.vec.Vec Std.U8
  reason : lifecycle.Error
  next : lifecycle.Session
  rngNext : R
  hnotbad : ∀ realReason,
    tacenta_wire.decode_message decoded.message.deref ≠ ok (.Err realReason)
  hcall : lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
    ok (.Err reason, next, rngNext)
  oracleNext : Model.Lifecycle.Oracle
  modelReason : Model.Lifecycle.Refusal
  modelComposite : Model.CompositeHeader.Composite
  ciphertext : Bytes
  hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf decoded.message.deref) =
    .ok (modelComposite, ciphertext)
  hmodelStep : Model.Lifecycle.decryptRatchet view oracle model
      (sliceOf decoded.message.deref) =
      { session := model, result := .error modelReason, oracle := oracleNext }
  hcase : InitialRatchetModelRefusalCase view oracle model decoded.message.deref
    modelReason oracleNext

structure InitialRatchetRefusalBranchProviders
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
      (trace := trace) (dh := dh) (K := K)
      (view := view) (oracle := oracle) (real := real) (model := model) message rng) where
  ceiling : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (dhOutRecv : Model.Lifecycle.Key),
      Model.CompositeHeader.decodeDetailed (sliceOf input.decoded.message.deref) =
        .ok (composite, ciphertext) →
      oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →
      Model.Lifecycle.random32 oracle = none → False
  firstDh : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf input.decoded.message.deref) =
        .ok (composite, ciphertext) →
      oracle.dhAgree model.ratchetPrivate composite.dh = none →
      Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        input.decoded.message.deref rng input.reason input.next input.rngNext)
  secondDh : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (draw : Model.Lifecycle.Key) (oracleAfter : Model.Lifecycle.Oracle),
      Model.CompositeHeader.decodeDetailed (sliceOf input.decoded.message.deref) =
        .ok (composite, ciphertext) →
      (∃ dhOutRecv, oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv) →
      Model.Lifecycle.random32 oracle = some (draw, oracleAfter) →
      (∃ dhOutRecv : Model.Lifecycle.Key, oracle.dhAgree draw composite.dh = none) →
      Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        input.decoded.message.deref rng input.reason input.next input.rngNext)
  tripleProvider : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (draw : Model.Lifecycle.Key) (oracleAfter : Model.Lifecycle.Oracle)
      (modelReason : Model.Triple.ReceiveRefusal)
      (dhOutRecv dhOutSend : Model.Lifecycle.Key),
      Model.CompositeHeader.decodeDetailed (sliceOf input.decoded.message.deref) =
        .ok (composite, ciphertext) →
      oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →
      Model.Lifecycle.random32 oracle = some (draw, oracleAfter) →
      oracle.dhAgree draw composite.dh = some dhOutSend →
      Model.Lifecycle.receiveWithEviction model.triple composite
        (Model.Lifecycle.tripleHeaderOf composite) dhOutRecv dhOutSend
        (oracle.dhPublic draw)
        (Model.Lifecycle.sparseOutputOf
          (Model.Braid.receive oracle.braidKem model.braid
            (Model.Lifecycle.braidMessageOf view model.braid composite)).2.1) =
        .error modelReason →
      Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        input.decoded.message.deref rng input.reason input.next input.rngNext)
  aeadProvider : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (draw : Model.Lifecycle.Key) (oracleAfter : Model.Lifecycle.Oracle)
      (messageKey : Model.Lifecycle.Key)
      (dhOutRecv dhOutSend : Model.Lifecycle.Key)
      (tripleCandidate : Model.Triple.State),
      Model.CompositeHeader.decodeDetailed (sliceOf input.decoded.message.deref) =
        .ok (composite, ciphertext) →
      oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →
      Model.Lifecycle.random32 oracle = some (draw, oracleAfter) →
      oracle.dhAgree draw composite.dh = some dhOutSend →
      Model.Lifecycle.receiveWithEviction model.triple composite
        (Model.Lifecycle.tripleHeaderOf composite) dhOutRecv dhOutSend
        (oracle.dhPublic draw)
        (Model.Lifecycle.sparseOutputOf
          (Model.Braid.receive oracle.braidKem model.braid
            (Model.Lifecycle.braidMessageOf view model.braid composite)).2.1) =
        .ok (tripleCandidate, messageKey) →
      oracle.aeadOpen
        (Model.State.messageKeys messageKey .tacenta).1
        (Model.State.messageKeys messageKey .tacenta).2.1
        (Model.State.messageKeys messageKey .tacenta).2.2 ciphertext
        (Model.Messages.concatAd model.identityAd
          (Model.CompositeHeader.encode composite)) = none →
      Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        input.decoded.message.deref rng input.reason input.next input.rngNext)


theorem initial_ratchet_refusal_route_of_branch_providers
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
      (trace := trace) (dh := dh) (K := K)
      (view := view) (oracle := oracle) (real := real) (model := model) message rng)
    (providers : InitialRatchetRefusalBranchProviders input) :
    Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
      input.decoded.message.deref rng input.reason input.next input.rngNext) := by
  exact initial_ratchet_refusal_case_dispatch
    (hcase := ⟨input.modelReason, input.oracleNext, input.hcase⟩)
    providers.ceiling providers.firstDh providers.secondDh providers.tripleProvider
    providers.aeadProvider

/-! Build the nonterminal route from the actual model refusal result.  The
    provider is indexed by the classifier above, so it must handle the exact
    model branch and cannot relabel a concrete refusal as a different family.
    The random-source ceiling remains an explicit provider case until the
    concrete RNG contract rules it out. -/
theorem initial_ratchet_nonterminal_route_of_model_result
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hmodel : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R),
        (∀ realReason,
          tacenta_wire.decode_message decoded.message.deref ≠ ok (.Err realReason)) →
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Err reason, next, rngNext) →
        ∃ (oracleNext : Model.Lifecycle.Oracle)
          (modelReason : Model.Lifecycle.Refusal)
          (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
          Model.CompositeHeader.decodeDetailed (sliceOf decoded.message.deref) =
            .ok (modelComposite, ciphertext) ∧
          Model.Lifecycle.decryptRatchet view oracle model
              (sliceOf decoded.message.deref) =
            { session := model, result := .error modelReason, oracle := oracleNext })
    (hproviders : ∀ {innerMessage : Slice Std.U8} {innerRng : R}
      (input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
        (trace := trace) (dh := dh) (K := K) (view := view) (oracle := oracle)
        (real := real) (model := model) innerMessage innerRng),
      InitialRatchetRefusalBranchProviders input) :
    ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R),
        (∀ realReason,
          tacenta_wire.decode_message decoded.message.deref ≠ ok (.Err realReason)) →
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Err reason, next, rngNext) →
        Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
          decoded.message.deref rng reason next rngNext) := by
  intro decoded established hdecode hestablished he hi reason next rngNext hnotbad hcall
  obtain ⟨oracleNext, modelReason, modelComposite, ciphertext, hdecodeModel, hmodelStep⟩ :=
    hmodel decoded established hdecode hestablished he hi reason next rngNext hnotbad hcall
  obtain ⟨modelCase⟩ := initial_ratchet_model_refusal_case_of_result
    view oracle oracleNext model decoded.message.deref modelReason hready
    (by exact ⟨modelComposite, ciphertext, hdecodeModel⟩) hmodelStep
  let input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
      (trace := trace) (dh := dh) (K := K) (view := view) (oracle := oracle)
      (real := real) (model := model) decoded.message.deref rng :=
    { decoded := decoded, established := established, reason := reason,
      next := next, rngNext := rngNext, hnotbad := hnotbad, hcall := hcall,
      oracleNext := oracleNext, modelReason := modelReason,
      modelComposite := modelComposite, ciphertext := ciphertext,
      hdecodeModel := hdecodeModel, hmodelStep := hmodelStep, hcase := modelCase }
  exact initial_ratchet_refusal_route_of_branch_providers input (hproviders input)



def initial_ratchet_refusal_evidence_of_route
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    {reason : lifecycle.Error} {next : lifecycle.Session} {rngNext : R}
    (route : InitialRatchetRefusalRoute rc crc trace dh K view oracle
      real model message rng reason next rngNext) :
    InitialRatchetRefusalEvidence rc crc trace dh K view oracle real model
      message rng reason next rngNext := by
  cases route with
  | terminal e => exact e
  | decode realReason e => exact e
  | dh rngAfter e => exact e
  | triple realReason next rngNext e => exact e
  | aead next rngNext e => exact e

/-! Exhaust the indexed refusal sum once at the public boundary.  This is a
    useful audit lemma as well as a routing aid: any route supplied to the T1
    result splitter is one of the five named families, with the terminal and
    decoder successors fixed to the original session and RNG state. -/
theorem initial_ratchet_refusal_route_family_cases
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    {reason : lifecycle.Error} {next : lifecycle.Session} {rngNext : R}
    (route : InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
      message rng reason next rngNext) :
    (reason = .AgreementFailed ∧ next = real ∧ rngNext = rng) ∨
    (∃ decodeReason, reason = .Decode decodeReason ∧ next = real ∧ rngNext = rng) ∨
    (∃ rngAfter, reason = .Handshake SessionError.NonContributoryAgreement ∧
      next = real ∧ rngNext = rngAfter) ∨
    (∃ tripleReason, reason = .Triple tripleReason) ∨
    reason = .Aead := by
  cases route with
  | terminal e => exact Or.inl ⟨rfl, rfl, rfl⟩
  | decode decodeReason e =>
      exact Or.inr (Or.inl ⟨decodeReason, rfl, rfl, rfl⟩)
  | dh _ e =>
      exact Or.inr (Or.inr (Or.inl ⟨rngNext, rfl, rfl, rfl⟩))
  | triple tripleReason next rngNext e =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨tripleReason, rfl⟩)))
  | aead next rngNext e =>
      exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

def initial_ratchet_triple_refusal_evidence_of_pair {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (realReason : tacenta_triple.TripleError)
    (next : lifecycle.Session) (rngNext : R)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Triple realReason), next, rngNext))
    (hstep : StepRefines trace dh K (.Err (.Triple realReason), next, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))) :
    InitialRatchetRefusalEvidence rngCore cryptoRng trace dh K view oracle real model
      message rng (.Triple realReason) next rngNext :=
  initial_ratchet_refusal_evidence_of_pair rngCore cryptoRng trace dh K view oracle
    real model message rng (.Triple realReason) next rngNext hcall hstep

def initial_ratchet_aead_refusal_evidence_of_pair {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (next : lifecycle.Session) (rngNext : R)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, next, rngNext))
    (hstep : StepRefines trace dh K (.Err .Aead, next, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))) :
    InitialRatchetRefusalEvidence rngCore cryptoRng trace dh K view oracle real model
      message rng .Aead next rngNext :=
  initial_ratchet_refusal_evidence_of_pair rngCore cryptoRng trace dh K view oracle
    real model message rng .Aead next rngNext hcall hstep

def initial_ratchet_first_dh_refusal_evidence
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (codec : DhCodecOf dh)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (decoded : tacenta_wire.DecodedMessage)
    (modelComposite : Model.CompositeHeader.Composite)
    (realComposite : tacenta_wire.Composite)
    (evidence : BraidReceiveEvidence K view real model realComposite modelComposite)
    (hrealComposite : realComposite = decoded.header)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Ok decoded))
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf decoded.ciphertext))
    (hcomposite : CompositeRefines decoded.header modelComposite)
    (hmodelDhNone : oracle.dhAgree model.ratchetPrivate modelComposite.dh = none) :
    InitialRatchetRefusalEvidence rngCore cryptoRng trace dh K view oracle real model
      message rng (.Handshake SessionError.NonContributoryAgreement) real rng := by
  obtain ⟨hcall, hstep⟩ := decrypt_ratchet_first_dh_refusal_from_braid
    rngCore cryptoRng trace dh kem K view oracle oracleOf codec real model message rng
    decoded modelComposite realComposite evidence hrealComposite hrel htrace hready
    hdecodeReal hdecodeModel hcomposite hmodelDhNone
  exact ⟨hcall, hstep⟩

theorem initial_ratchet_second_dh_refusal_evidence
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
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
    (realComposite : tacenta_wire.Composite)
    (evidence : BraidReceiveEvidence K view real model realComposite modelComposite)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Ok decoded))
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf decoded.ciphertext))
    (hrealComposite : realComposite = decoded.header)
    (hcomposite : CompositeRefines decoded.header modelComposite)
    (draw modelDhOutRecv : Model.Lifecycle.Key)
    (hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
      some modelDhOutRecv)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hmodelSecond : oracle.dhAgree draw modelComposite.dh = none) :
    ∃ rngAfter, Nonempty (InitialRatchetRefusalEvidence rngCore cryptoRng trace dh K view oracle
      real model message rng (.Handshake SessionError.NonContributoryAgreement) real rngAfter) := by
  obtain ⟨rngAfter, hcall, hstep⟩ := decrypt_ratchet_second_dh_refusal_from_braid
    rngCore cryptoRng trace dh kem K view oracle oracleNext oracleOf codec hz32 real model
    message rng decoded modelComposite realComposite evidence hrel htrace hready hdecodeReal
    hdecodeModel hrealComposite hcomposite draw modelDhOutRecv hmodelFirst hmodelDraw
    hmodelSecond
  exact ⟨rngAfter, ⟨⟨hcall, hstep⟩⟩⟩

/-! The two non-contributory DH routes share one refusal kind but differ in
    whether the random draw has happened.  This adapter performs that split
    from the model's actual DH results and preserves the corresponding
    randomness successor in the second-DH arm. -/
theorem initial_ratchet_dh_refusal_evidence
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
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
    (realComposite : tacenta_wire.Composite)
    (evidence : BraidReceiveEvidence K view real model realComposite modelComposite)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Ok decoded))
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf decoded.ciphertext))
    (hrealComposite : realComposite = decoded.header)
    (hcomposite : CompositeRefines decoded.header modelComposite)
    (hdh : oracle.dhAgree model.ratchetPrivate modelComposite.dh = none ∨
      ∃ draw modelDhOutRecv,
        oracle.dhAgree model.ratchetPrivate modelComposite.dh = some modelDhOutRecv ∧
        Model.Lifecycle.random32 oracle = some (draw, oracleNext) ∧
        oracle.dhAgree draw modelComposite.dh = none) :
    ∃ rngAfter, Nonempty (InitialRatchetRefusalEvidence rngCore cryptoRng trace dh K view
      oracle real model message rng (.Handshake SessionError.NonContributoryAgreement) real rngAfter) := by
  rcases hdh with hnone | ⟨draw, modelDhOutRecv, hmodelFirst, hmodelDraw, hmodelSecond⟩
  · exact ⟨rng, ⟨initial_ratchet_first_dh_refusal_evidence rngCore cryptoRng trace dh kem K
      view oracle oracleOf codec real model message rng decoded modelComposite realComposite
      evidence hrealComposite hrel htrace hready hdecodeReal hdecodeModel hcomposite hnone⟩⟩
  · exact initial_ratchet_second_dh_refusal_evidence rngCore cryptoRng trace dh kem K view
      oracle oracleNext oracleOf codec hz32 real model message rng decoded modelComposite
      realComposite evidence hrel htrace hready hdecodeReal hdecodeModel hrealComposite
      hcomposite draw modelDhOutRecv hmodelFirst hmodelDraw hmodelSecond

/-! Route-level DH adapter.  This is the first nonterminal refusal family
    exposed directly to the indexed route sum; the first/second-DH split and
    its RNG successor remain supplied by `initial_ratchet_dh_refusal_evidence`.
    No error or successor is re-labelled at this boundary. -/
theorem initial_ratchet_dh_refusal_route
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
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
    (realComposite : tacenta_wire.Composite)
    (evidence : BraidReceiveEvidence K view real model realComposite modelComposite)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Ok decoded))
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf decoded.ciphertext))
    (hrealComposite : realComposite = decoded.header)
    (hcomposite : CompositeRefines decoded.header modelComposite)
    (hdh : oracle.dhAgree model.ratchetPrivate modelComposite.dh = none ∨
      ∃ draw modelDhOutRecv,
        oracle.dhAgree model.ratchetPrivate modelComposite.dh = some modelDhOutRecv ∧
        Model.Lifecycle.random32 oracle = some (draw, oracleNext) ∧
        oracle.dhAgree draw modelComposite.dh = none) :
    ∃ rngAfter, Nonempty (InitialRatchetRefusalRoute rngCore cryptoRng trace dh K view oracle
      real model message rng (.Handshake SessionError.NonContributoryAgreement) real rngAfter) := by
  obtain ⟨rngAfter, ⟨evidence⟩⟩ := initial_ratchet_dh_refusal_evidence
    rngCore cryptoRng trace dh kem K view oracle oracleNext oracleOf codec hz32 real model
    message rng decoded modelComposite realComposite evidence hrel htrace hready hdecodeReal
    hdecodeModel hrealComposite hcomposite hdh
  exact ⟨rngAfter, ⟨.dh rngAfter evidence⟩⟩

/-! Concrete DH provider adapter.  The model/Braid/DH evidence is supplied at
    the branch that selected the exact generated result; this adapter only
    reconciles the evidence-producing call with that result before attaching
    the indexed DH route. -/
theorem initial_ratchet_dh_refusal_provider_of_evidence
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (codec : DhCodecOf dh)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err reason, next, rngNext))
    (decoded : tacenta_wire.DecodedMessage)
    (modelComposite : Model.CompositeHeader.Composite)
    (realComposite : tacenta_wire.Composite)
    (evidence : BraidReceiveEvidence K view real model realComposite modelComposite)
    (hrealComposite : realComposite = decoded.header)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeReal : tacenta_wire.decode_message message = ok (.Ok decoded))
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf decoded.ciphertext))
    (hcomposite : CompositeRefines decoded.header modelComposite)
    (hdh : oracle.dhAgree model.ratchetPrivate modelComposite.dh = none ∨
      ∃ draw modelDhOutRecv,
        oracle.dhAgree model.ratchetPrivate modelComposite.dh = some modelDhOutRecv ∧
        Model.Lifecycle.random32 oracle = some (draw, oracleNext) ∧
        oracle.dhAgree draw modelComposite.dh = none) :
    Nonempty (InitialRatchetRefusalRoute rngCore cryptoRng trace dh K view oracle
      real model message rng reason next rngNext) := by
  obtain ⟨rngAfter, ⟨e⟩⟩ := initial_ratchet_dh_refusal_evidence
    rngCore cryptoRng trace dh kem K view oracle oracleNext oracleOf codec hz32
    real model message rng decoded modelComposite realComposite evidence hrel htrace hready
    hdecodeReal hdecodeModel hrealComposite hcomposite hdh
  have hresult : (core.result.Result.Err reason, next, rngNext) =
      (core.result.Result.Err (.Handshake SessionError.NonContributoryAgreement), real, rngAfter) :=
    Result.ok.inj (hcall.symm.trans e.hcall)
  cases hresult
  exact ⟨.dh _ e⟩
/-! Concrete DH evidence package for the branch dispatcher.  The package
    carries the decoded message and Braid receive evidence for the exact model
    composite selected by the classifier; the route-producing adapter below
    supplies the model DH arm and reconciles it with `input.hcall`. -/
structure InitialRatchetDhConcreteEvidence
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
      (trace := trace) (dh := dh) (K := K) (view := view) (oracle := oracle)
      (real := real) (model := model) message rng)
    (modelComposite : Model.CompositeHeader.Composite)
    (ciphertext : Bytes) where
  decoded : tacenta_wire.DecodedMessage
  realComposite : tacenta_wire.Composite
  evidence : BraidReceiveEvidence K view real model realComposite modelComposite
  hrealComposite : realComposite = decoded.header
  hdecodeReal : tacenta_wire.decode_message input.decoded.message.deref =
    ok (.Ok decoded)
  hdecodeModel : Model.CompositeHeader.decodeDetailed
      (sliceOf input.decoded.message.deref) =
    .ok (modelComposite, vecOf decoded.ciphertext)
  hcomposite : CompositeRefines decoded.header modelComposite

structure InitialRatchetDhConcreteProviders
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
      (trace := trace) (dh := dh) (K := K) (view := view) (oracle := oracle)
      (real := real) (model := model) message rng) where
  first : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf input.decoded.message.deref) =
        .ok (composite, ciphertext) →
      oracle.dhAgree model.ratchetPrivate composite.dh = none →
      InitialRatchetDhConcreteEvidence input composite ciphertext
  second : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (draw : Model.Lifecycle.Key) (oracleAfter : Model.Lifecycle.Oracle),
      Model.CompositeHeader.decodeDetailed (sliceOf input.decoded.message.deref) =
        .ok (composite, ciphertext) →
      (∃ dhOutRecv, oracle.dhAgree model.ratchetPrivate composite.dh =
        some dhOutRecv) →
      Model.Lifecycle.random32 oracle = some (draw, oracleAfter) →
      (∃ dhOutRecv : Model.Lifecycle.Key, oracle.dhAgree draw composite.dh = none) →
      InitialRatchetDhConcreteEvidence input composite ciphertext

structure InitialRatchetDhRouteProviders
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
      (trace := trace) (dh := dh) (K := K) (view := view) (oracle := oracle)
      (real := real) (model := model) message rng) where
  firstDh : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf input.decoded.message.deref) =
        .ok (composite, ciphertext) →
      oracle.dhAgree model.ratchetPrivate composite.dh = none →
      Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        input.decoded.message.deref rng input.reason input.next input.rngNext)
  secondDh : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (draw : Model.Lifecycle.Key) (oracleAfter : Model.Lifecycle.Oracle),
      Model.CompositeHeader.decodeDetailed (sliceOf input.decoded.message.deref) =
        .ok (composite, ciphertext) →
      (∃ dhOutRecv, oracle.dhAgree model.ratchetPrivate composite.dh =
        some dhOutRecv) →
      Model.Lifecycle.random32 oracle = some (draw, oracleAfter) →
      (∃ dhOutRecv : Model.Lifecycle.Key, oracle.dhAgree draw composite.dh = none) →
      Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        input.decoded.message.deref rng input.reason input.next input.rngNext)

/-! Convert concrete first/second-DH evidence into the exact route callbacks
    consumed by `initial_ratchet_refusal_case_dispatch`. -/
def initial_ratchet_dh_route_providers_of_concrete_evidence
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
      (trace := trace) (dh := dh) (K := K) (view := view) (oracle := oracle)
      (real := real) (model := model) message rng)
    (kem : KemView) (codec : DhCodecOf dh)
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (evidence : InitialRatchetDhConcreteProviders input) :
    InitialRatchetDhRouteProviders input := by
  refine { firstDh := ?_, secondDh := ?_ }
  · intro composite ciphertext hdecode hfirst
    let ev := evidence.first composite ciphertext hdecode hfirst
    exact initial_ratchet_dh_refusal_provider_of_evidence
      rc crc trace dh kem K view oracle oracle oracleOf codec hz32 real model
      input.decoded.message.deref rng input.reason input.next input.rngNext
      input.hcall ev.decoded composite ev.realComposite ev.evidence ev.hrealComposite
      hrel htrace hready ev.hdecodeReal ev.hdecodeModel ev.hcomposite (Or.inl hfirst)
  · intro composite ciphertext draw oracleAfter hdecode hfirst hdraw hsecond
    let ev := evidence.second composite ciphertext draw oracleAfter hdecode hfirst hdraw hsecond
    obtain ⟨dhOutRecv, hfirst'⟩ := hfirst
    obtain ⟨dhOutSend, hsecond'⟩ := hsecond
    exact initial_ratchet_dh_refusal_provider_of_evidence
      rc crc trace dh kem K view oracle oracleAfter oracleOf codec hz32 real model
      input.decoded.message.deref rng input.reason input.next input.rngNext
      input.hcall ev.decoded composite ev.realComposite ev.evidence ev.hrealComposite
      hrel htrace hready ev.hdecodeReal ev.hdecodeModel ev.hcomposite
      (Or.inr ⟨draw, dhOutRecv, hfirst', hdraw, hsecond'⟩)

/-! Assemble the concrete DH callbacks with the remaining leaf callbacks at
    the exact branch-provider boundary.  Triple and AEAD callbacks remain
    explicit because their model receive/key facts are branch-specific. -/
def initial_ratchet_refusal_branch_providers_of_dh
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
      (trace := trace) (dh := dh) (K := K) (view := view) (oracle := oracle)
      (real := real) (model := model) message rng)
    (dhProviders : InitialRatchetDhRouteProviders input)
    (ceiling : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (dhOutRecv : Model.Lifecycle.Key),
      Model.CompositeHeader.decodeDetailed (sliceOf input.decoded.message.deref) =
        .ok (composite, ciphertext) →
      oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →
      Model.Lifecycle.random32 oracle = none → False)
    (tripleProvider : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (draw : Model.Lifecycle.Key) (oracleAfter : Model.Lifecycle.Oracle)
      (modelReason : Model.Triple.ReceiveRefusal)
      (dhOutRecv dhOutSend : Model.Lifecycle.Key),
      Model.CompositeHeader.decodeDetailed (sliceOf input.decoded.message.deref) =
        .ok (composite, ciphertext) →
      oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →
      Model.Lifecycle.random32 oracle = some (draw, oracleAfter) →
      oracle.dhAgree draw composite.dh = some dhOutSend →
      Model.Lifecycle.receiveWithEviction model.triple composite
        (Model.Lifecycle.tripleHeaderOf composite) dhOutRecv dhOutSend
        (oracle.dhPublic draw)
        (Model.Lifecycle.sparseOutputOf
          (Model.Braid.receive oracle.braidKem model.braid
            (Model.Lifecycle.braidMessageOf view model.braid composite)).2.1) =
        .error modelReason →
      Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        input.decoded.message.deref rng input.reason input.next input.rngNext))
    (aeadProvider : ∀ (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (draw : Model.Lifecycle.Key) (oracleAfter : Model.Lifecycle.Oracle)
      (messageKey : Model.Lifecycle.Key)
      (dhOutRecv dhOutSend : Model.Lifecycle.Key)
      (tripleCandidate : Model.Triple.State),
      Model.CompositeHeader.decodeDetailed (sliceOf input.decoded.message.deref) =
        .ok (composite, ciphertext) →
      oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →
      Model.Lifecycle.random32 oracle = some (draw, oracleAfter) →
      oracle.dhAgree draw composite.dh = some dhOutSend →
      Model.Lifecycle.receiveWithEviction model.triple composite
        (Model.Lifecycle.tripleHeaderOf composite) dhOutRecv dhOutSend
        (oracle.dhPublic draw)
        (Model.Lifecycle.sparseOutputOf
          (Model.Braid.receive oracle.braidKem model.braid
            (Model.Lifecycle.braidMessageOf view model.braid composite)).2.1) =
        .ok (tripleCandidate, messageKey) →
      oracle.aeadOpen
        (Model.State.messageKeys messageKey .tacenta).1
        (Model.State.messageKeys messageKey .tacenta).2.1
        (Model.State.messageKeys messageKey .tacenta).2.2 ciphertext
        (Model.Messages.concatAd model.identityAd
          (Model.CompositeHeader.encode composite)) = none →
      Nonempty (InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
        input.decoded.message.deref rng input.reason input.next input.rngNext)) :
    InitialRatchetRefusalBranchProviders input :=
  { ceiling := ceiling
    firstDh := dhProviders.firstDh
    secondDh := dhProviders.secondDh
    tripleProvider := tripleProvider
    aeadProvider := aeadProvider }


/-! Small route constructors for the two result-indexed leaf families.  The
    evidence package still requires the exact generated call and model step;
    these definitions only attach the corresponding typed route tag. -/
def initial_ratchet_triple_refusal_route_of_pair {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (realReason : tacenta_triple.TripleError)
    (next : lifecycle.Session) (rngNext : R)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Triple realReason), next, rngNext))
    (hstep : StepRefines trace dh K (.Err (.Triple realReason), next, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))) :
    InitialRatchetRefusalRoute rngCore cryptoRng trace dh K view oracle real model
      message rng (.Triple realReason) next rngNext :=
  .triple realReason next rngNext
    (initial_ratchet_triple_refusal_evidence_of_pair rngCore cryptoRng trace dh K view
      oracle real model message rng realReason next rngNext hcall hstep)

def initial_ratchet_aead_refusal_route_of_pair {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (next : lifecycle.Session) (rngNext : R)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, next, rngNext))
    (hstep : StepRefines trace dh K (.Err .Aead, next, rngNext)
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))) :
    InitialRatchetRefusalRoute rngCore cryptoRng trace dh K view oracle real model
      message rng .Aead next rngNext :=
  .aead next rngNext
    (initial_ratchet_aead_refusal_evidence_of_pair rngCore cryptoRng trace dh K view oracle
      real model message rng next rngNext hcall hstep)
/-! Close the concrete Triple refusal leaf against the indexed route sum.  The
    model case supplies the exact DH draw, public-key, Triple refusal and
    oracle successor; the generated prefix supplies the real call. -/
def initial_ratchet_triple_refusal_route_of_prefix
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (realReason : tacenta_triple.TripleError) (next : lifecycle.Session)
    (pref : InitialRatchetTripleRefusalPrefix rngCore cryptoRng real message rng
      rngNext realReason next)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Triple realReason), next, rngNext))
    (modelComposite : Model.CompositeHeader.Composite)
    (draw modelDhOutRecv modelDhOutSend : Model.Lifecycle.Key)
    (modelReason : Model.Triple.ReceiveRefusal)
    (htrace : trace rng = oracle.draws)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines pref.m
      (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hnext : Tacenta.SessionUnitBraidT3.StateRefines K pref.braidCandidate.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf pref.decoded.ciphertext))
    (hcomposite : CompositeRefines pref.decoded.header modelComposite)
    (hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
      some modelDhOutRecv)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hmodelSecond : oracle.dhAgree draw modelComposite.dh = some modelDhOutSend)
    (hmodelPublic : oracle.dhPublic draw = arrayOf pref.newPublicBytes)
    (hmodelTriple : Model.Lifecycle.receiveWithEviction model.triple modelComposite
      (Model.Lifecycle.tripleHeaderOf modelComposite) modelDhOutRecv modelDhOutSend
      (oracle.dhPublic draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1) =
      .error modelReason)
    (hreason : tripleReceiveRefusalOfReal realReason = some modelReason) :
    InitialRatchetRefusalRoute rngCore cryptoRng trace dh K view oracle real model
      message rng (.Triple realReason) next rngNext := by
  obtain ⟨hresult, hstep⟩ := decrypt_ratchet_triple_refusal_from_prefix
    rngCore cryptoRng trace dh kem K view oracle oracleNext oracleOf real model message
    rng rngNext pref.decoded modelComposite realReason next pref htrace hmessageRel hnext
    hrel hready hdecodeModel hcomposite draw modelDhOutRecv modelDhOutSend modelReason
    hmodelFirst hmodelDraw hmodelSecond hmodelPublic hmodelTriple hreason
  have hvalue := Result.ok.inj (hcall.symm.trans hresult)
  injection hvalue with _ hpair
  have hnextEq : next = real := congrArg Prod.fst hpair
  cases hnextEq
  exact initial_ratchet_triple_refusal_route_of_pair rngCore cryptoRng trace dh K view
    oracle real model message rng realReason real rngNext hresult hstep

/-! Close the concrete AEAD refusal leaf against the indexed route sum.  The
    result inversion is kept explicit because the prefix adapter establishes
    that this refusal leaves the session unchanged. -/
def initial_ratchet_aead_refusal_route_of_prefix
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (next : lifecycle.Session)
    (pref : InitialRatchetAeadRefusalPrefix rngCore cryptoRng real message rng
      rngNext next)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, next, rngNext))
    (modelComposite : Model.CompositeHeader.Composite)
    (draw modelDhOutRecv modelDhOutSend : Model.Lifecycle.Key)
    (modelTripleCandidate : Model.Triple.State) (modelMk : Model.Lifecycle.Key)
    (htrace : trace rng = oracle.draws)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines pref.m
      (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hnext : Tacenta.SessionUnitBraidT3.StateRefines K pref.braidCandidate.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf pref.decoded.ciphertext))
    (hcomposite : CompositeRefines pref.decoded.header modelComposite)
    (hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
      some modelDhOutRecv)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hmodelSecond : oracle.dhAgree draw modelComposite.dh = some modelDhOutSend)
    (hmodelPublic : oracle.dhPublic draw = arrayOf pref.newPublicBytes)
    (hmodelTriple : Model.Lifecycle.receiveWithEviction model.triple modelComposite
      (Model.Lifecycle.tripleHeaderOf modelComposite) modelDhOutRecv modelDhOutSend
      (oracle.dhPublic draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1) =
      .ok (modelTripleCandidate, modelMk))
    (hkeysValue : (arrayOf pref.realKeys.1, arrayOf pref.realKeys.2.1,
      arrayOf pref.realKeys.2.2) = Model.State.messageKeys modelMk .tacenta)
    (hrealAdValue : vecOf pref.realAd = Model.Messages.concatAd model.identityAd
      (Model.CompositeHeader.encode modelComposite)) :
    InitialRatchetRefusalRoute rngCore cryptoRng trace dh K view oracle real model
      message rng .Aead next rngNext := by
  obtain ⟨hresult, hstep⟩ := decrypt_ratchet_aead_refusal_from_prefix
    rngCore cryptoRng trace dh kem K view oracle oracleNext oracleOf real model message
    rng rngNext modelComposite next pref htrace hmessageRel hnext hrel hready
    hdecodeModel hcomposite draw modelDhOutRecv modelDhOutSend modelTripleCandidate modelMk
    hmodelFirst hmodelDraw hmodelSecond hmodelPublic hmodelTriple hkeysValue hrealAdValue
  have hvalue := Result.ok.inj (hcall.symm.trans hresult)
  injection hvalue with _ hpair
  have hnextEq : next = real := congrArg Prod.fst hpair
  cases hnextEq
  exact initial_ratchet_aead_refusal_route_of_pair rngCore cryptoRng trace dh K view
    oracle real model message rng real rngNext hresult hstep

/-! Result-indexed Triple provider wrapper.  The prefix is derived from the
    exact generated refusal equation; callers provide only the model/Braid and
    Triple relations consumed by the existing leaf adapter. -/
noncomputable def initial_ratchet_triple_refusal_route_of_result
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (realReason : tacenta_triple.TripleError) (next : lifecycle.Session)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Triple realReason), next, rngNext))
    (modelComposite : Model.CompositeHeader.Composite)
    (draw modelDhOutRecv modelDhOutSend : Model.Lifecycle.Key)
    (modelReason : Model.Triple.ReceiveRefusal)
    (htrace : trace rng = oracle.draws)
    (hmessageRel : ∀ (pref : InitialRatchetTripleRefusalPrefix rngCore cryptoRng
        real message rng rngNext realReason next),
      Tacenta.SessionUnitBraidT3.MsgRefines pref.m
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hnext : ∀ (pref : InitialRatchetTripleRefusalPrefix rngCore cryptoRng
        real message rng rngNext realReason next),
      Tacenta.SessionUnitBraidT3.StateRefines K pref.braidCandidate.state
        (Model.Braid.receive K model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeModel : ∀ (pref : InitialRatchetTripleRefusalPrefix rngCore cryptoRng
        real message rng rngNext realReason next),
      Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (modelComposite, vecOf pref.decoded.ciphertext))
    (hcomposite : ∀ (pref : InitialRatchetTripleRefusalPrefix rngCore cryptoRng
        real message rng rngNext realReason next),
      CompositeRefines pref.decoded.header modelComposite)
    (hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
      some modelDhOutRecv)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hmodelSecond : oracle.dhAgree draw modelComposite.dh = some modelDhOutSend)
    (hmodelPublic : ∀ (pref : InitialRatchetTripleRefusalPrefix rngCore cryptoRng
        real message rng rngNext realReason next),
      oracle.dhPublic draw = arrayOf pref.newPublicBytes)
    (hmodelTriple : Model.Lifecycle.receiveWithEviction model.triple modelComposite
      (Model.Lifecycle.tripleHeaderOf modelComposite) modelDhOutRecv modelDhOutSend
      (oracle.dhPublic draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1) =
      .error modelReason)
    (hreason : tripleReceiveRefusalOfReal realReason = some modelReason) :
    Nonempty (InitialRatchetRefusalRoute rngCore cryptoRng trace dh K view oracle real model
      message rng (.Triple realReason) next rngNext) := by
  let pref := initial_ratchet_triple_refusal_prefix_of_result
    rngCore cryptoRng hz32 real message rng rngNext realReason next hcall
  exact ⟨initial_ratchet_triple_refusal_route_of_prefix
    rngCore cryptoRng trace dh kem K view oracle oracleNext oracleOf real model message
    rng rngNext realReason next pref hcall modelComposite draw modelDhOutRecv modelDhOutSend
    modelReason htrace (hmessageRel pref) (hnext pref) hrel hready
    (hdecodeModel pref) (hcomposite pref) hmodelFirst hmodelDraw hmodelSecond
    (hmodelPublic pref) hmodelTriple hreason⟩

/-! Consume a classified Triple refusal through the concrete prefix adapter.
    The classifier is retained as an indexed premise, while the branch facts
    are explicit so the caller must provide the exact message, state, DH and
    public-key relations used by the generated proof. -/
theorem initial_ratchet_triple_refusal_route_of_model_case
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (realReason : tacenta_triple.TripleError) (next : lifecycle.Session)
    (pref : InitialRatchetTripleRefusalPrefix rngCore cryptoRng real message rng
      rngNext realReason next)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err (.Triple realReason), next, rngNext))
    (modelComposite : Model.CompositeHeader.Composite)
    (draw modelDhOutRecv modelDhOutSend : Model.Lifecycle.Key)
    (modelReason : Model.Triple.ReceiveRefusal)
    (hcase : InitialRatchetModelRefusalCase view oracle model message
      (Model.Lifecycle.tripleReceiveRefusalOf modelReason) oracleNext)
    (htrace : trace rng = oracle.draws)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines pref.m
      (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hnext : Tacenta.SessionUnitBraidT3.StateRefines K pref.braidCandidate.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf pref.decoded.ciphertext))
    (hcomposite : CompositeRefines pref.decoded.header modelComposite)
    (hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
      some modelDhOutRecv)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hmodelSecond : oracle.dhAgree draw modelComposite.dh = some modelDhOutSend)
    (hmodelPublic : oracle.dhPublic draw = arrayOf pref.newPublicBytes)
    (hmodelTriple : Model.Lifecycle.receiveWithEviction model.triple modelComposite
      (Model.Lifecycle.tripleHeaderOf modelComposite) modelDhOutRecv modelDhOutSend
      (oracle.dhPublic draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1) =
      .error modelReason)
    (hreason : tripleReceiveRefusalOfReal realReason = some modelReason) :
    Nonempty (InitialRatchetRefusalRoute rngCore cryptoRng trace dh K view oracle real model
      message rng (.Triple realReason) next rngNext) := by
  exact ⟨initial_ratchet_triple_refusal_route_of_prefix
    rngCore cryptoRng trace dh kem K view oracle oracleNext oracleOf real model message
    rng rngNext realReason next pref hcall modelComposite draw modelDhOutRecv modelDhOutSend
    modelReason htrace hmessageRel hnext hrel hready hdecodeModel hcomposite hmodelFirst
    hmodelDraw hmodelSecond hmodelPublic hmodelTriple hreason⟩

/-! Result-indexed AEAD provider wrapper.  As with Triple, the generated
    prefix is reconstructed from the exact refusal result before any model
    key/ad relation is accepted. -/
noncomputable def initial_ratchet_aead_refusal_route_of_result
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R) (next : lifecycle.Session)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, next, rngNext))
    (modelComposite : Model.CompositeHeader.Composite)
    (draw modelDhOutRecv modelDhOutSend : Model.Lifecycle.Key)
    (modelTripleCandidate : Model.Triple.State) (modelMk : Model.Lifecycle.Key)
    (htrace : trace rng = oracle.draws)
    (hmessageRel : ∀ (pref : InitialRatchetAeadRefusalPrefix rngCore cryptoRng
        real message rng rngNext next),
      Tacenta.SessionUnitBraidT3.MsgRefines pref.m
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hnext : ∀ (pref : InitialRatchetAeadRefusalPrefix rngCore cryptoRng
        real message rng rngNext next),
      Tacenta.SessionUnitBraidT3.StateRefines K pref.braidCandidate.state
        (Model.Braid.receive K model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeModel : ∀ (pref : InitialRatchetAeadRefusalPrefix rngCore cryptoRng
        real message rng rngNext next),
      Model.CompositeHeader.decodeDetailed (sliceOf message) =
        .ok (modelComposite, vecOf pref.decoded.ciphertext))
    (hcomposite : ∀ (pref : InitialRatchetAeadRefusalPrefix rngCore cryptoRng
        real message rng rngNext next),
      CompositeRefines pref.decoded.header modelComposite)
    (hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
      some modelDhOutRecv)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hmodelSecond : oracle.dhAgree draw modelComposite.dh = some modelDhOutSend)
    (hmodelPublic : ∀ (pref : InitialRatchetAeadRefusalPrefix rngCore cryptoRng
        real message rng rngNext next),
      oracle.dhPublic draw = arrayOf pref.newPublicBytes)
    (hmodelTriple : Model.Lifecycle.receiveWithEviction model.triple modelComposite
      (Model.Lifecycle.tripleHeaderOf modelComposite) modelDhOutRecv modelDhOutSend
      (oracle.dhPublic draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1) =
      .ok (modelTripleCandidate, modelMk))
    (hkeysValue : ∀ (pref : InitialRatchetAeadRefusalPrefix rngCore cryptoRng
        real message rng rngNext next),
      (arrayOf pref.realKeys.1, arrayOf pref.realKeys.2.1,
        arrayOf pref.realKeys.2.2) = Model.State.messageKeys modelMk .tacenta)
    (hrealAdValue : ∀ (pref : InitialRatchetAeadRefusalPrefix rngCore cryptoRng
        real message rng rngNext next),
      vecOf pref.realAd = Model.Messages.concatAd model.identityAd
        (Model.CompositeHeader.encode modelComposite)) :
    Nonempty (InitialRatchetRefusalRoute rngCore cryptoRng trace dh K view oracle real model
      message rng .Aead next rngNext) := by
  let pref := initial_ratchet_aead_refusal_prefix_of_result
    rngCore cryptoRng hz32 hzKeys real message rng rngNext next hcall
  exact ⟨initial_ratchet_aead_refusal_route_of_prefix
    rngCore cryptoRng trace dh kem K view oracle oracleNext oracleOf real model message
    rng rngNext next pref hcall modelComposite draw modelDhOutRecv modelDhOutSend
    modelTripleCandidate modelMk htrace (hmessageRel pref) (hnext pref) hrel hready
    (hdecodeModel pref) (hcomposite pref) hmodelFirst hmodelDraw hmodelSecond
    (hmodelPublic pref) hmodelTriple (hkeysValue pref) (hrealAdValue pref)⟩

/-! The AEAD counterpart of the classified Triple adapter.  The exact model
    case remains an indexed premise; the caller must additionally provide the
    message-key and associated-data equalities consumed by the generated
    AEAD-refusal leaf proof. -/
theorem initial_ratchet_aead_refusal_route_of_model_case
    {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (oracle oracleNext : Model.Lifecycle.Oracle)
    (oracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng rngNext : R)
    (next : lifecycle.Session)
    (pref : InitialRatchetAeadRefusalPrefix rngCore cryptoRng real message rng
      rngNext next)
    (hcall : lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
      ok (.Err .Aead, next, rngNext))
    (modelComposite : Model.CompositeHeader.Composite)
    (draw modelDhOutRecv modelDhOutSend : Model.Lifecycle.Key)
    (modelTripleCandidate : Model.Triple.State) (modelMk : Model.Lifecycle.Key)
    (hcase : InitialRatchetModelRefusalCase view oracle model message .aead oracleNext)
    (htrace : trace rng = oracle.draws)
    (hmessageRel : Tacenta.SessionUnitBraidT3.MsgRefines pref.m
      (Model.Lifecycle.braidMessageOf view model.braid modelComposite))
    (hnext : Tacenta.SessionUnitBraidT3.StateRefines K pref.braidCandidate.state
      (Model.Braid.receive K model.braid
        (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.2)
    (hrel : SessionRefines dh K real model)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hdecodeModel : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (modelComposite, vecOf pref.decoded.ciphertext))
    (hcomposite : CompositeRefines pref.decoded.header modelComposite)
    (hmodelFirst : oracle.dhAgree model.ratchetPrivate modelComposite.dh =
      some modelDhOutRecv)
    (hmodelDraw : Model.Lifecycle.random32 oracle = some (draw, oracleNext))
    (hmodelSecond : oracle.dhAgree draw modelComposite.dh = some modelDhOutSend)
    (hmodelPublic : oracle.dhPublic draw = arrayOf pref.newPublicBytes)
    (hmodelTriple : Model.Lifecycle.receiveWithEviction model.triple modelComposite
      (Model.Lifecycle.tripleHeaderOf modelComposite) modelDhOutRecv modelDhOutSend
      (oracle.dhPublic draw)
      (Model.Lifecycle.sparseOutputOf
        (Model.Braid.receive oracle.braidKem model.braid
          (Model.Lifecycle.braidMessageOf view model.braid modelComposite)).2.1) =
      .ok (modelTripleCandidate, modelMk))
    (hkeysValue : (arrayOf pref.realKeys.1, arrayOf pref.realKeys.2.1,
      arrayOf pref.realKeys.2.2) = Model.State.messageKeys modelMk .tacenta)
    (hrealAdValue : vecOf pref.realAd = Model.Messages.concatAd model.identityAd
      (Model.CompositeHeader.encode modelComposite)) :
    Nonempty (InitialRatchetRefusalRoute rngCore cryptoRng trace dh K view oracle real model
      message rng .Aead next rngNext) := by
  exact ⟨initial_ratchet_aead_refusal_route_of_prefix
    rngCore cryptoRng trace dh kem K view oracle oracleNext oracleOf real model message
    rng rngNext next pref hcall modelComposite draw modelDhOutRecv modelDhOutSend
    modelTripleCandidate modelMk htrace hmessageRel hnext hrel hready hdecodeModel
    hcomposite hmodelFirst
    hmodelDraw hmodelSecond hmodelPublic hmodelTriple hkeysValue hrealAdValue⟩

def initial_ratchet_terminal_refusal_evidence {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (hrel : SessionRefines dh K real model)
    (htrace : trace rng = oracle.draws)
    (hfailed : Model.Lifecycle.agreementFailed model = true) :
    InitialRatchetRefusalEvidence rngCore cryptoRng trace dh K view oracle real model
      message rng .AgreementFailed real rng := by
  obtain ⟨hcall, hstep⟩ := decrypt_ratchet_terminal_guard_step_refines rngCore cryptoRng
    trace dh K view oracle real model message rng hrel htrace hfailed
  exact ⟨hcall, hstep⟩

def initial_ratchet_decode_refusal_evidence {R : Type}
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
    InitialRatchetRefusalEvidence rngCore cryptoRng trace dh K view oracle real model
      message rng (.Decode realReason) real rng := by
  obtain ⟨hcall, hstep⟩ := decrypt_ratchet_decode_refusal_refines rngCore cryptoRng
    trace dh K view oracle real model message rng realReason hrel htrace hready hdecodeReal
  exact ⟨hcall, hstep⟩

/-! Close the two wrapper-level refusal routes at the same actual-result
    boundary used by the T1 splitter.  The terminal and malformed adapters
    each compute their own exact `decrypt_ratchet` result; the equality of that
    result with the caller's `Err` result is used to identify the requested
    reason, successor session, and randomness before packaging the evidence. -/
noncomputable def initial_ratchet_terminal_or_decode_refusal_evidence
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (hbad : ∀ decoded : tacenta_wire.DecodedInitial,
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      ∃ reason, tacenta_wire.decode_message decoded.message.deref = ok (.Err reason))
    (decoded : tacenta_wire.DecodedInitial)
    (established : alloc.vec.Vec Std.U8)
    (hdecode : tacenta_wire.decode_initial message = ok (.Ok decoded))
    (hestablished : real.established_ephemeral = some established)
    (he : vecOf established = vecOf decoded.ephemeral)
    (hi : vecOf decoded.identity =
      Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public))
    (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R)
    (hcall : lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
      ok (.Err reason, next, rngNext)) :
    InitialRatchetRefusalEvidence rc crc trace dh K view oracle real model
      decoded.message.deref rng reason next rngNext := by
  by_cases hfailed : Model.Lifecycle.agreementFailed model = true
  · obtain ⟨hterminal, hstep⟩ := decrypt_ratchet_terminal_guard_step_refines rc crc trace dh K
      view oracle real model decoded.message.deref rng ctx.hrel ctx.htrace hfailed
    have heq := Result.ok.inj (hcall.symm.trans hterminal)
    cases heq
    exact ⟨hcall, hstep⟩
  · have hready : Model.Lifecycle.agreementFailed model = false := by
      cases h : Model.Lifecycle.agreementFailed model <;> simp_all
    let decodeReason := Classical.choose (hbad decoded hdecode)
    have hbadDecode := Classical.choose_spec (hbad decoded hdecode)
    obtain ⟨hdecodeCall, hdecodeStep⟩ := decrypt_ratchet_decode_refusal_refines rc crc
      trace dh K view oracle real model decoded.message.deref rng decodeReason ctx.hrel
      ctx.htrace hready hbadDecode
    have heq := Result.ok.inj (hcall.symm.trans hdecodeCall)
    cases heq
    exact ⟨hcall, hdecodeStep⟩

/-! Result-shaped T1 composition with the concrete success router and the
    refusal-family evidence boundary. -/
theorem initial_ratchet_refines_of_t1_result_split_with_evidence
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (boundary : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (hrefusal : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Err reason, next, rngNext) →
        InitialRatchetRefusalEvidence rc crc trace dh K view oracle real model
          decoded.message.deref rng reason next rngNext)
    (hsuccess : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        InitialRatchetSuccessEvidence rc crc trace dh K view oracle real model
          decoded.message.deref rng plaintext next rngNext) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  apply initial_ratchet_refines_of_t1_result_split boundary headroom
  · intro decoded established hdecode hestablished he hi reason next rngNext hcall
    exact (hrefusal decoded established hdecode hestablished he hi reason next rngNext hcall).hstep
  · intro decoded established hdecode hestablished he hi plaintext next rngNext hcall
    exact initial_ratchet_success_step_from_evidence (R := R)
      (hsuccess decoded established hdecode hestablished he hi plaintext next rngNext hcall)

/-! Result-shaped T1 composition with the concrete success router.  The
    success callback now returns typed evidence for the actual result, so the
    callback cannot silently replace it with an independently chosen route. -/
theorem initial_ratchet_refines_of_t1_result_split_with_success_evidence
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (boundary : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (hrefusal : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Err reason, next, rngNext) →
        StepRefines trace dh K (.Err reason, next, rngNext)
          (Model.Lifecycle.decryptRatchet view oracle model
            (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage))
    (hsuccess : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        InitialRatchetSuccessEvidence rc crc trace dh K view oracle real model
          decoded.message.deref rng plaintext next rngNext) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  apply initial_ratchet_refines_of_t1_result_split boundary headroom hrefusal
  intro decoded established hdecode hestablished he hi plaintext next rngNext hcall
  exact initial_ratchet_success_step_from_evidence (R := R)
    (hsuccess decoded established hdecode hestablished he hi plaintext next rngNext hcall)

/-! The caller-facing success composition.  The success callback is no longer
allowed to hand this theorem an already-built evidence record: it must first
return model facts indexed by the same decoded message and then a splice
indexed by the generated success prefix extracted from the actual result. -/
theorem initial_ratchet_refines_of_t1_result_split_with_result_splice
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (boundary : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hrefusal : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Err reason, next, rngNext) →
        InitialRatchetRefusalEvidence rc crc trace dh K view oracle real model
          decoded.message.deref rng reason next rngNext)
    (hsuccess : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∃ oracleNext, ∃ facts : InitialRatchetModelSuccessFacts view oracle oracleNext
          model decoded.message.deref,
          Nonempty (∀ successPrefix : InitialRatchetSuccessPrefix rc crc real
              decoded.message.deref rng rngNext plaintext next,
            InitialRatchetSuccessSplice (dh := dh) (K := K) (trace := trace)
              successPrefix facts)) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  apply initial_ratchet_refines_of_t1_result_split_with_evidence boundary headroom
  · exact hrefusal
  · intro decoded established hdecode hestablished he hi plaintext next rngNext hcall
    have hdata :=
      hsuccess decoded established hdecode hestablished he hi plaintext next rngNext hcall
    let oracleNext := Classical.choose hdata
    have hfactsData := Classical.choose_spec hdata
    let facts : InitialRatchetModelSuccessFacts view oracle oracleNext model
        decoded.message.deref := Classical.choose hfactsData
    have hspliceData := Classical.choose_spec hfactsData
    let hsplice := Classical.choice hspliceData
    exact initial_ratchet_success_evidence_of_result_and_splice hz32 hzKeys hcall
      facts hsplice

/-! Convenience composition for the two wrapper-level refusal routes.  The
    caller supplies only the malformed-input predicate and the typed success
    splice; terminal/decode refusal evidence is now derived from the actual
    `Err` result by the adapter above. -/
theorem initial_ratchet_refines_of_t1_result_split_with_terminal_decode_evidence
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (boundary : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hbad : ∀ decoded : tacenta_wire.DecodedInitial,
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      ∃ reason, tacenta_wire.decode_message decoded.message.deref = ok (.Err reason))
    (hsuccess : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∃ oracleNext, ∃ facts : InitialRatchetModelSuccessFacts view oracle oracleNext
          model decoded.message.deref,
          Nonempty (∀ successPrefix : InitialRatchetSuccessPrefix rc crc real
              decoded.message.deref rng rngNext plaintext next,
            InitialRatchetSuccessSplice (dh := dh) (K := K) (trace := trace)
              successPrefix facts)) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  apply initial_ratchet_refines_of_t1_result_split_with_result_splice boundary headroom hz32 hzKeys
  · intro decoded established hdecode hestablished he hi reason next rngNext hcall
    exact initial_ratchet_terminal_or_decode_refusal_evidence ctx hbad decoded established
      hdecode hestablished he hi reason next rngNext hcall
  · exact hsuccess

/-! General result-split entry for a fully typed refusal route.  Each callback
    must construct the indexed route, after which the splitter can consume one
    uniform refusal evidence record. -/
theorem initial_ratchet_refines_of_t1_result_split_with_route_evidence
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (boundary : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hrefusalRoute : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Err reason, next, rngNext) →
        InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
          decoded.message.deref rng reason next rngNext)
    (hsuccess : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∃ oracleNext, ∃ facts : InitialRatchetModelSuccessFacts view oracle oracleNext
          model decoded.message.deref,
          Nonempty (∀ successPrefix : InitialRatchetSuccessPrefix rc crc real
              decoded.message.deref rng rngNext plaintext next,
            InitialRatchetSuccessSplice (dh := dh) (K := K) (trace := trace)
              successPrefix facts)) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  apply initial_ratchet_refines_of_t1_result_split_with_result_splice boundary headroom hz32 hzKeys
  · intro decoded established hdecode hestablished he hi reason next rngNext hcall
    exact initial_ratchet_refusal_evidence_of_route
      (hrefusalRoute decoded established hdecode hestablished he hi reason next rngNext hcall)
  · exact hsuccess

/-! Final wrapper composition for the result-shaped split.  The model guard
    and decoder are classified here from the actual input, so callers only
    provide the genuinely nonterminal DH/Triple/AEAD route.  Each wrapper
    branch is reconciled with the caller's exact `Err` result before it is
    injected into the indexed route sum. -/
theorem initial_ratchet_refines_of_t1_result_split_with_nonterminal_route
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (boundary : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hnonterminalRoute : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R),
        (∀ realReason,
          tacenta_wire.decode_message decoded.message.deref ≠ ok (.Err realReason)) →
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Err reason, next, rngNext) →
        InitialRatchetRefusalRoute rc crc trace dh K view oracle real model
          decoded.message.deref rng reason next rngNext)
    (hsuccess : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∃ oracleNext, ∃ facts : InitialRatchetModelSuccessFacts view oracle oracleNext
          model decoded.message.deref,
          Nonempty (∀ successPrefix : InitialRatchetSuccessPrefix rc crc real
              decoded.message.deref rng rngNext plaintext next,
            InitialRatchetSuccessSplice (dh := dh) (K := K) (trace := trace)
              successPrefix facts)) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  apply initial_ratchet_refines_of_t1_result_split_with_route_evidence boundary headroom hz32 hzKeys
  · intro decoded established hdecode hestablished he hi reason next rngNext hcall
    by_cases hfailed : Model.Lifecycle.agreementFailed model = true
    · obtain ⟨hterminal, hstep⟩ := decrypt_ratchet_terminal_guard_step_refines rc crc
        trace dh K view oracle real model decoded.message.deref rng
        ctx.hrel ctx.htrace hfailed
      have heq := Result.ok.inj (hcall.symm.trans hterminal)
      cases heq
      exact .terminal ⟨hcall, hstep⟩
    · have hready : Model.Lifecycle.agreementFailed model = false := by
        cases h : Model.Lifecycle.agreementFailed model <;> simp_all
      by_cases hbad : ∃ realReason,
          tacenta_wire.decode_message decoded.message.deref = ok (.Err realReason)
      · let realReason := Classical.choose hbad
        have hbadDecode := Classical.choose_spec hbad
        obtain ⟨hdecodeCall, hdecodeStep⟩ := decrypt_ratchet_decode_refusal_refines rc crc
          trace dh K view oracle real model decoded.message.deref rng realReason
          ctx.hrel ctx.htrace hready hbadDecode
        have heq := Result.ok.inj (hcall.symm.trans hdecodeCall)
        cases heq
        exact .decode realReason ⟨hcall, hdecodeStep⟩
      · exact hnonterminalRoute decoded established hdecode hestablished he hi
          reason next rngNext (by simpa using hbad) hcall
  · exact hsuccess

/-! Compose the ready-state refusal provider with the actual result split. The
    terminal guard is handled before the provider is called; malformed messages
    are handled inside the nonterminal splitter. -/
theorem initial_ratchet_refines_of_t1_result_split_with_model_refusal_provider
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (boundary : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hmodelRefusal : ∀ (hready : Model.Lifecycle.agreementFailed model = false)
      (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R),
        (∀ realReason,
          tacenta_wire.decode_message decoded.message.deref ≠ ok (.Err realReason)) →
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Err reason, next, rngNext) →
        ∃ (oracleNext : Model.Lifecycle.Oracle)
          (modelReason : Model.Lifecycle.Refusal)
          (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
          Model.CompositeHeader.decodeDetailed (sliceOf decoded.message.deref) =
            .ok (modelComposite, ciphertext) ∧
          Model.Lifecycle.decryptRatchet view oracle model
              (sliceOf decoded.message.deref) =
            { session := model, result := .error modelReason, oracle := oracleNext })
    (hproviders : ∀ {innerMessage : Slice Std.U8} {innerRng : R}
      (input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
        (trace := trace) (dh := dh) (K := K) (view := view) (oracle := oracle)
        (real := real) (model := model) innerMessage innerRng),
      InitialRatchetRefusalBranchProviders input)
    (hsuccess : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∃ oracleNext, ∃ facts : InitialRatchetModelSuccessFacts view oracle oracleNext
          model decoded.message.deref,
          Nonempty (∀ successPrefix : InitialRatchetSuccessPrefix rc crc real
              decoded.message.deref rng rngNext plaintext next,
            InitialRatchetSuccessSplice (dh := dh) (K := K) (trace := trace)
              successPrefix facts)) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  apply initial_ratchet_refines_of_t1_result_split_with_route_evidence boundary headroom hz32 hzKeys
  · intro decoded established hdecode hestablished he hi reason next rngNext hcall
    by_cases hfailed : Model.Lifecycle.agreementFailed model = true
    · obtain ⟨hterminal, hstep⟩ := decrypt_ratchet_terminal_guard_step_refines rc crc
        trace dh K view oracle real model decoded.message.deref rng
        ctx.hrel ctx.htrace hfailed
      have heq := Result.ok.inj (hcall.symm.trans hterminal)
      cases heq
      exact .terminal ⟨hcall, hstep⟩
    · have hready : Model.Lifecycle.agreementFailed model = false := by
        cases h : Model.Lifecycle.agreementFailed model <;> simp_all
      by_cases hbad : ∃ realReason,
          tacenta_wire.decode_message decoded.message.deref = ok (.Err realReason)
      · let realReason := Classical.choose hbad
        have hbadDecode := Classical.choose_spec hbad
        obtain ⟨hdecodeCall, hdecodeStep⟩ := decrypt_ratchet_decode_refusal_refines rc crc
          trace dh K view oracle real model decoded.message.deref rng realReason
          ctx.hrel ctx.htrace hready hbadDecode
        have heq := Result.ok.inj (hcall.symm.trans hdecodeCall)
        cases heq
        exact .decode realReason ⟨hcall, hdecodeStep⟩
      · let hnotbad : ∀ realReason,
          tacenta_wire.decode_message decoded.message.deref ≠ ok (.Err realReason) := by
            simpa using hbad
        exact Classical.choice (initial_ratchet_nonterminal_route_of_model_result hready
          (hmodelRefusal hready) hproviders decoded established hdecode hestablished he hi
          reason next rngNext hnotbad hcall)
  · exact hsuccess


/-! Public result-split bridge for a concrete success provider.  The model
    success equation is inverted first, then the provider is indexed by that
    exact model successor and by the generated `Ok` result.  This is the
    composition point at which the direct Triple route or the full-store retry
    route reaches `decrypt_ratchet_success_step_from_aligned_receive_cases`. -/
theorem initial_ratchet_refines_of_t1_result_split_with_model_step_and_concrete_provider
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (boundary : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hmodelRefusal : ∀ (hready : Model.Lifecycle.agreementFailed model = false)
      (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R),
        (∀ realReason,
          tacenta_wire.decode_message decoded.message.deref ≠ ok (.Err realReason)) →
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Err reason, next, rngNext) →
        ∃ (oracleNext : Model.Lifecycle.Oracle)
          (modelReason : Model.Lifecycle.Refusal)
          (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
          Model.CompositeHeader.decodeDetailed (sliceOf decoded.message.deref) =
            .ok (modelComposite, ciphertext) ∧
          Model.Lifecycle.decryptRatchet view oracle model
              (sliceOf decoded.message.deref) =
            { session := model, result := .error modelReason, oracle := oracleNext })
    (hproviders : ∀ {innerMessage : Slice Std.U8} {innerRng : R}
      (input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
        (trace := trace) (dh := dh) (K := K) (view := view) (oracle := oracle)
        (real := real) (model := model) innerMessage innerRng),
      InitialRatchetRefusalBranchProviders input)
    (hmodelStep : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∃ (modelNext : Model.Lifecycle.Session) (modelPlaintext : Bytes)
          (oracleNext : Model.Lifecycle.Oracle),
          Model.Lifecycle.decryptRatchet view oracle model
              (sliceOf decoded.message.deref) =
            { session := modelNext, result := .ok modelPlaintext, oracle := oracleNext })
    (hprovider : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∀ (modelNext : Model.Lifecycle.Session) (modelPlaintext : Bytes)
          (oracleNext : Model.Lifecycle.Oracle)
          (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model
            decoded.message.deref),
          InitialRatchetConcreteSuccessProvider
            (rc := rc) (crc := crc) (trace := trace) (dh := dh) (K := K)
            (view := view) (oracle := oracle) (oracleNext := oracleNext)
            (real := real) (model := model) (message := decoded.message.deref)
            (rng := rng) (rngNext := rngNext) (plaintext := plaintext) (next := next)
            facts) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  apply initial_ratchet_refines_of_t1_result_split_with_model_refusal_provider ctx boundary
    headroom hz32 hzKeys hmodelRefusal hproviders
  · exact initial_ratchet_success_callback_of_model_step_and_provider hmodelStep hprovider


/-! Public initial-message bridge for the completed result split.  The refusal
    side is now indexed by the concrete model result and its five typed branch
    providers; the success side is indexed by the generated `Ok` result and a
    concrete receive provider.  Thus this boundary no longer accepts an
    unindexed `hnonterminalRoute` or an independently chosen `hsuccess`. -/
theorem decrypt_initial_refines_of_t1_with_model_step_and_concrete_provider
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (codec : DhCodecOf dh)
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (boundary : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hmodelRefusal : ∀ (hready : Model.Lifecycle.agreementFailed model = false)
      (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (reason : lifecycle.Error) (next : lifecycle.Session) (rngNext : R),
        (∀ realReason,
          tacenta_wire.decode_message decoded.message.deref ≠ ok (.Err realReason)) →
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Err reason, next, rngNext) →
        ∃ (oracleNext : Model.Lifecycle.Oracle)
          (modelReason : Model.Lifecycle.Refusal)
          (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
          Model.CompositeHeader.decodeDetailed (sliceOf decoded.message.deref) =
            .ok (modelComposite, ciphertext) ∧
          Model.Lifecycle.decryptRatchet view oracle model
              (sliceOf decoded.message.deref) =
            { session := model, result := .error modelReason, oracle := oracleNext })
    (hproviders : ∀ {innerMessage : Slice Std.U8} {innerRng : R}
      (input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
        (trace := trace) (dh := dh) (K := K) (view := view) (oracle := oracle)
        (real := real) (model := model) innerMessage innerRng),
      InitialRatchetRefusalBranchProviders input)
    (hmodelStep : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∃ (modelNext : Model.Lifecycle.Session) (modelPlaintext : Bytes)
          (oracleNext : Model.Lifecycle.Oracle),
          Model.Lifecycle.decryptRatchet view oracle model
              (sliceOf decoded.message.deref) =
            { session := modelNext, result := .ok modelPlaintext, oracle := oracleNext })
    (hprovider : ∀ (decoded : tacenta_wire.DecodedInitial)
      (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ (plaintext : alloc.vec.Vec Std.U8) (next : lifecycle.Session) (rngNext : R),
        lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng =
          ok (.Ok plaintext, next, rngNext) →
        ∀ (modelNext : Model.Lifecycle.Session) (modelPlaintext : Bytes)
          (oracleNext : Model.Lifecycle.Oracle)
          (facts : InitialRatchetModelSuccessFacts view oracle oracleNext model
            decoded.message.deref),
          InitialRatchetConcreteSuccessProvider
            (rc := rc) (crc := crc) (trace := trace) (dh := dh) (K := K)
            (view := view) (oracle := oracle) (oracleNext := oracleNext)
            (real := real) (model := model) (message := decoded.message.deref)
            (rng := rng) (rngNext := rngNext) (plaintext := plaintext) (next := next)
            facts) :
    PublicDecryptWitness rc crc trace dh K view oracle real model message rng := by
  exact decrypt_initial_refines_from_ratchet codec ctx
    (initial_ratchet_refines_of_t1_result_split_with_model_step_and_concrete_provider
      ctx boundary headroom hz32 hzKeys hmodelRefusal hproviders hmodelStep hprovider)

/-- Derive the inner call's existence from T1. The supplied semantic relation
must hold for every actual output; it cannot assume the call succeeds or pick
an output independently of the generated call. -/
theorem initial_ratchet_refines_of_t1
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (boundary : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (hrefines : ∀ (decoded : tacenta_wire.DecodedInitial) (established : alloc.vec.Vec Std.U8),
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      real.established_ephemeral = some established →
      vecOf established = vecOf decoded.ephemeral →
      vecOf decoded.identity =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public) →
      ∀ output, lifecycle.Session.decrypt_ratchet rc crc real decoded.message.deref rng = ok output →
        StepRefines trace dh K output (Model.Lifecycle.decryptRatchet view oracle model
          (Tacenta.SessionUnitWireInitialT3.initialOf decoded).ratchetMessage)) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  apply initial_ratchet_refines_of_t1_result_split boundary headroom
  · intro decoded established hdecode hestablished he hi reason next rngNext hcall
    exact hrefines decoded established hdecode hestablished he hi
      (.Err reason, next, rngNext) hcall
  · intro decoded established hdecode hestablished he hi plaintext next rngNext hcall
    exact hrefines decoded established hdecode hestablished he hi
      (.Ok plaintext, next, rngNext) hcall

/-- A concrete discharge of the inner semantic premise for terminal Braid
states, with no assumed inner output or StepRefines witness. -/
theorem initial_ratchet_refines_terminal
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (hfailed : Model.Lifecycle.agreementFailed model = true) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  intro decoded established hdecode hestablished he hi
  obtain ⟨hcall, hstep⟩ := decrypt_ratchet_terminal_guard_step_refines rc crc trace dh K view
    oracle real model decoded.message.deref rng ctx.hrel ctx.htrace hfailed
  exact ⟨_, hcall, hstep⟩

/-- Terminal-state initial decrypt: every wrapper guard and the inner receive
are discharged from the generated code and existing refinements. -/
theorem decrypt_initial_terminal_refines
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (codec : DhCodecOf dh)
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (hfailed : Model.Lifecycle.agreementFailed model = true) :
    PublicDecryptWitness rc crc trace dh K view oracle real model message rng :=
  decrypt_initial_refines_from_ratchet codec ctx (initial_ratchet_refines_terminal ctx hfailed)

/-- The selector's pending-state consequences follow from the same constructed
route: refusal preserves the pending projection, success clears it. -/
theorem initial_dispatch_atomicity_from_ratchet
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (codec : DhCodecOf dh)
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (hreceive : InitialRatchetRefines rc crc trace dh K view oracle real model message rng) :
    (∃ reason output,
      (Model.Lifecycle.decrypt view oracle model (sliceOf message)).result = .error reason ∧
      lifecycle.Session.decrypt rc crc real message rng = ok output ∧
      output.2.1.pending_initial.map (pendingInitialOf dh) = model.pendingInitial) ∨
    (∃ plaintext output,
      (Model.Lifecycle.decrypt view oracle model (sliceOf message)).result = .ok plaintext ∧
      lifecycle.Session.decrypt rc crc real message rng = ok output ∧
      output.2.1.pending_initial.map (pendingInitialOf dh) = none) := by
  obtain ⟨route⟩ := initial_dispatch_route_from_ratchet codec ctx hreceive
  exact initial_dispatch_select_atomicity route

/-- The inner premise is also discharged for malformed ratchet payloads. This
requires a decoder result, not a hypothesized ratchet output or refinement. -/
theorem initial_ratchet_refines_decode_refusal
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (hready : Model.Lifecycle.agreementFailed model = false)
    (hbad : ∀ decoded : tacenta_wire.DecodedInitial,
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      ∃ reason, tacenta_wire.decode_message decoded.message.deref = ok (.Err reason)) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  intro decoded established hdecode hestablished he hi
  obtain ⟨reason, hbad⟩ := hbad decoded hdecode
  obtain ⟨hcall, hstep⟩ := decrypt_ratchet_decode_refusal_refines rc crc trace dh K view
    oracle real model decoded.message.deref rng reason ctx.hrel ctx.htrace hready hbad
  exact ⟨_, hcall, hstep⟩

/-! The terminal and malformed branches share the same inner-result boundary.
    This wrapper chooses the terminal guard first and otherwise consumes the
    proved decoder refusal; neither branch accepts a hypothesized ratchet
    result. -/
theorem initial_ratchet_refines_terminal_or_decode_refusal
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    (ctx : InitialDispatchContext rc crc trace dh K view oracle real model message rng)
    (hbad : ∀ decoded : tacenta_wire.DecodedInitial,
      tacenta_wire.decode_initial message = ok (.Ok decoded) →
      ∃ reason, tacenta_wire.decode_message decoded.message.deref = ok (.Err reason)) :
    InitialRatchetRefines rc crc trace dh K view oracle real model message rng := by
  by_cases hfailed : Model.Lifecycle.agreementFailed model = true
  · exact initial_ratchet_refines_terminal ctx hfailed
  · have hready : Model.Lifecycle.agreementFailed model = false := by
      cases h : Model.Lifecycle.agreementFailed model <;> simp_all
    exact initial_ratchet_refines_decode_refusal ctx hready hbad

end Tacenta.UnitLifecycleT3
