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
  intro decoded established hdecode hestablished he hi
  exact decrypt_ratchet_refines_of_t1 boundary headroom (fun output hcall =>
    hrefines decoded established hdecode hestablished he hi output hcall)

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

end Tacenta.UnitLifecycleT3
