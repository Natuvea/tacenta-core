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
