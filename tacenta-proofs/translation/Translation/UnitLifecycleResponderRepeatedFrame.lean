import Translation.UnitLifecycleResponderSuccessor
import Translation.UnitLifecycleInitialAgreementT3
import Translation.UnitLifecycleAtomicity

/-!
# The initiator's first frame again, through `Session::decrypt` at the responder's session after its first receipt

`UnitLifecycleResponderFirstReceipt` shows that `establish_responder` on the bytes the initiator's first `encrypt`
emits succeeds (or the store refuses) and returns a session `sB'` related to the model's step, and
`UnitLifecycleResponderSuccessor` that `sB'` passes `Session::invariant` and meets the four counter ceilings.  An
initiator repeats its initial message until it hears back, so the responder can receive the same bytes again on the
session it now holds.  This module takes that second delivery on the same run: the responder's public
`Session::decrypt` of the same bytes at `sB'`.  The call recognises the repeat (the message's ephemeral key is in the
same agreement class as the one the session kept, and its identity is the peer's), strips the wrapper, and its inner
`decrypt_ratchet` refuses the first frame as out of order, because the receiving chain already stands past message 0.
The refusal has no durable effect: the session returned is `sB'` itself, and the source loses exactly one draw, the
candidate key the inner receive draws before the Triple's receive.  The code's step refines the model's public
`decrypt` step, which recognises the repeat, consumes the draw, refuses `triple (classical outOfOrder)` and leaves
the model session as it was.

## What is shown

* `repeat_receive_outOfOrder`, `repeat_receive_with_eviction`, `repeat_frame_model_refused` (model only): the model
  Triple's receive of the first header at the receiver after the first message refuses `outOfOrder` (the header's
  ratchet key is the peer key held, no stored key matches, and 0 is below the receive count 1), whatever the
  agreements and the sparse output; the session's receive with eviction refuses the same without evicting; and the
  model's `decryptRatchet` of the first frame at a session with that Triple, when its agreement has not failed and
  both agreements with the frame's key return, consumes one draw, refuses `triple (classical outOfOrder)` and keeps
  the session, at every codeword view.
* `key_agreement_ratchet`, `same_ephemeral_repeat` (bridges, under `DhAgreeContributory`): every private key agrees
  with the initiator's ratchet key in the responder's oracle; the code's comparison of the ephemeral copy the session
  keeps with the same message's ephemeral key returns `true` under any private key.
* `responder_first_frame_repeat_refused`: at every successful return of `establish_responder` on the initiator's
  initial message (the hypotheses of `responder_first_frame_successor` and the success equation), for every source
  whose trace holds a draw `dB2`, the model's `decrypt` of the same bytes at the related model session, at every view,
  is the refusal above with `dB2` consumed, and the translated `decrypt` of the same bytes at `sB'` returns
  `Triple(Classical(OutOfOrder))`, `sB'` itself and a source whose trace is the rest after `dB2`.  The inner
  receive's refinement is `decrypt_ratchet_refines_of_invariant` at `sB'`, with the invariant and the ceilings from
  `first_receipt_successor_facts` and the run inputs at the view that attributes the frame's codeword to the header
  source (the decoder at `sB'` already holds that chunk, which then fits it); the wrapper is
  `decrypt_initial_repeat_agreement_refusal_exact`.
* `initiator_first_send_responder_repeat_refused` (the composed statement): the same from a successful first
  `encrypt` at an establishment output, on the bytes it emitted, under the hypotheses of
  `initiator_first_send_responder_successor_hypotheses`, with the model session written as `firstReceiptSession` at
  the header source of the initiator's key generation.
* Non-vacuity.  `first_send_repeat_refused_reachable`: at the real constants, under the laws of
  `first_send_receive_reachable` (all assumed), one run from `publish` through the first send and the responder's
  success, after which the responder's `decrypt` of the same bytes, from the source the first call left, is refused
  as above.

## The laws and premises

No new law and no new per-run premise beyond the second source's draw.  The statements take the hypotheses of the
successor theorems (the receipt's laws `AeadRoundTrip`, `DhAgreeContributory`, `DhAgreeSymmetric`, and
`DhPublicValid`, `OptionEqU64Shape`, the responder's contracts, oracle record and decrypt agreements, the initiator's
send hypotheses) and the success equation of the first call.  `DhAgreeContributory` is used twice more here: for the
repeat recognition's two agreements with the initiator's ephemeral key, and for the session key's and the second
draw's agreements with the initiator's ratchet key, without which the model and the code would refuse
`handshake nonContributoryAgreement` instead.  The second source's draw is a per-run premise, as the first's is: with
no draw left the model refuses `ceiling` and the code's draw is not described.

## Non-vacuity

`first_send_repeat_refused_reachable` exhibits every premise of the composed statement on one run at the real
constants, under the laws of `first_send_receive_reachable`, assumed and modelled together in `first_receipt_laws_model`
(a toy interpretation, as recorded there).  The second delivery's source there is the one the first call left.

## What it does not show

* That the refusal consumes nothing: it consumes one draw of the source (the inner receive's candidate key, drawn
  before the Triple's receive), as the model step does; only the session is left as it was.
* A repeat at any later session: after the responder's reply, after the initiator's second message, or on a restored
  copy of the session; a repeat of the reply at the initiator (refused, right after a first receipt that succeeded, by
  `initiator_repeated_reply_refused` in `UnitLifecycleInitiatorRepeatedReply`).
* A repeat that differs in its bytes (a re-encoded ephemeral key, a changed KEM ciphertext or identifier, a tampered
  inner frame): the recognition passes on such a message by the model's rule, but the statement is about the same
  bytes.
* A non-repeat initial message (`NotARepeatedInitial`), and the arms the two agreements' refusal or an empty source
  would give (`handshake nonContributoryAgreement`, `ceiling`): excluded here by `DhAgreeContributory` and the draw.
* That the agreement's receive of the duplicate chunk leaves the decoder as it was: its candidate is discarded with
  the refusal, so the statement does not need it, and it is not stated.
* The second delivery to `establish_responder` at the committed store (`UnitLifecycleResponderEstablishReplay` takes
  that); that the real primitives meet the laws the run rests on; the one-time path in a run.  A source with no
  state of its own, such as `OsRng`, is outside the statements about draws.
-/

namespace Tacenta.UnitLifecycleResponderRepeatedFrame

open Aeneas Aeneas.Std Result
open tacenta_session_unit

open Tacenta.UnitLifecycleResponderFirstReceipt (firstSenderTriple receiverAfterFirst firstHeader firstAd
  decode_encodeMessage)
open Tacenta.UnitLifecycleEstablishedEncrypt (firstFrame firstComposite)

/-- **The model Triple's receive of the first header again, at the receiver after the first message**: the header's
ratchet key is the peer key held, no stored key matches, and its number 0 is below the receive count 1, so the
classical half refuses `outOfOrder`, whatever the agreements, the candidate key and the sparse output.  Model only. -/
theorem repeat_receive_outOfOrder (a4 ec prk k1 k2 d dSend newPub dR dS np : Model.State.Key)
    (out : Option Model.SparseRatchet.Output) :
    Model.Triple.receiveDetailed (receiverAfterFirst ec prk k1 k2 a4 d dSend newPub) (firstHeader a4) dR dS np out =
      .error (.classical .outOfOrder) := by
  simp [Model.Triple.receiveDetailed, Model.Ratchet.receiveDetailed, Model.Ratchet.trySkipped,
    Model.Ratchet.skipMessageKeysDetailed, Model.State.skipMessageKeys, receiverAfterFirst, firstHeader]

/-- The same through the session's receive with eviction: `outOfOrder` names no full store, so no eviction is
tried.  Model only. -/
theorem repeat_receive_with_eviction (a4 ec prk k1 k2 d dSend newPub dR dS np : Model.State.Key)
    (composite : Model.CompositeHeader.Composite) (out : Option Model.SparseRatchet.Output) :
    Model.Lifecycle.receiveWithEviction (receiverAfterFirst ec prk k1 k2 a4 d dSend newPub) composite
      (firstHeader a4) dR dS np out = .error (.classical .outOfOrder) := by
  unfold Model.Lifecycle.receiveWithEviction
  rw [repeat_receive_outOfOrder]
  rfl

/-- **The model's `decryptRatchet` of the first frame again, at a session whose Triple is the receiver after the
first message**: when the agreement has not failed, the frame's ratchet key is 32 canonical bytes, the session's
ratchet key and the draw `c` both agree with it, the step consumes `c`, refuses `triple (classical outOfOrder)` and
leaves the session as it was, at every codeword view: the agreement's receive is computed but its output and
candidate are discarded with the refusal.  Model only. -/
theorem repeat_frame_model_refused (viewA viewB : Model.Lifecycle.CodewordView)
    (oracleA oracleB : Model.Lifecycle.Oracle) (mA mB : Model.Lifecycle.Session)
    (a4 peer rkA cksA prk k1 k2 ec d dSend newPub : Model.State.Key) (pt : Model.Lifecycle.Bytes)
    (mk : Model.State.Key) (chunk : Model.Braid.Chunk)
    (hA : mA.triple = firstSenderTriple a4 peer rkA cksA prk k1 k2)
    (hB : mB.triple = receiverAfterFirst ec prk k1 k2 a4 d dSend newPub)
    (hfail : Model.Lifecycle.agreementFailed mB = false)
    (hlen : a4.length = 32) (hkey : Model.Messages.checkKey a4 = some ())
    (hchunk : (viewA.send mA.braid chunk).data.length = 32)
    (dR : Model.State.Key) (hagree : oracleB.dhAgree mB.ratchetPrivate a4 = some dR)
    (c : Model.State.Key) (rest : List Model.State.Key) (hdraw : oracleB.draws = c :: rest)
    (dS : Model.State.Key) (hcand : oracleB.dhAgree c a4 = some dS) :
    Model.Lifecycle.decryptRatchet viewB oracleB mB (firstFrame viewA oracleA mA pt mk chunk) =
      { session := mB, result := .error (.triple (.classical .outOfOrder)),
        oracle := { oracleB with draws := rest } } := by
  have hdh : (firstComposite viewA mA chunk).dh = a4 := by
    simp [firstComposite, hA, firstSenderTriple]
  have hdec : Model.CompositeHeader.decodeDetailed (firstFrame viewA oracleA mA pt mk chunk) =
      .ok (firstComposite viewA mA chunk,
        oracleA.aeadSeal (Model.State.messageKeys mk .tacenta).1 (Model.State.messageKeys mk .tacenta).2.1
          (Model.State.messageKeys mk .tacenta).2.2 pt (firstAd viewA mA chunk)) := by
    rw [Model.CompositeHeader.decodeDetailed_ok_iff]
    exact decode_encodeMessage _ _ (by rw [hdh]; exact hlen) (by rw [hdh]; exact hkey)
      (fun c hc => by simp [firstComposite] at hc; subst hc; exact hchunk)
  have hhdr : Model.Lifecycle.tripleHeaderOf (firstComposite viewA mA chunk) = firstHeader a4 := by
    simp [Model.Lifecycle.tripleHeaderOf, firstComposite, hA, firstSenderTriple, firstHeader]
  have hrand : Model.Lifecycle.random32 oracleB = some (c, { oracleB with draws := rest }) := by
    simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hdraw]
  unfold Model.Lifecycle.decryptRatchet
  rw [hfail, if_neg (by simp), hdec]
  dsimp only
  rw [hdh, hagree]
  dsimp only
  rw [hrand]
  dsimp only
  rw [hcand]
  dsimp only
  rw [hhdr, hB, repeat_receive_with_eviction]
  rfl


section Inner
variable {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
  {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}

open Tacenta.UnitLifecycleT3 (DhView DhCodecOf vecOf sliceOf arrayOf SessionRefines StepRefines ResultRefines
  modelChunkOf modelCodewordOf CodewordViewSendOf)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid establishedModelOf InitiatorOutputParts
  dhPublicValid_canonical)
open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts responderModelOf)
open Tacenta.UnitLifecycleEstablishedEncrypt (initialWire)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees responder_first_frame_prepares)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleDecryptRunBounds (DecryptRatchetRunInputs CounterHeadroom)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstKey firstReceiptSession DhAgreeContributory
  dhAgreeContributory_is AeadRoundTrip attributedView parts_of_first_frame responder_first_frame_inner_succeeds
  establish_responder_commit_of_inner established_triple_first view_ratchet_public responder_candidate_agreement)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)

/-- Every private key agrees contributorily with the initiator's ratchet key, in the responder's oracle, under
`DhAgreeContributory`, the oracle record and the view's codec relation. -/
theorem key_agreement_ratchet (hcon : DhAgreeContributory) {E : Type} {rcB : rand_core_1.RngCore E}
    {crcB : rand_core_1.CryptoRng E} {dh : DhView} (codec : DhCodecOf dh) {traceB : E → List Model.Lifecycle.Key}
    {oracleB : Model.Lifecycle.Oracle} (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (q : InitiatorSecretParts rc crc our bundle) (k : tacenta_boundary.dh.PrivateKey) :
    ∃ x, oracleB.dhAgree (dh.privateKey k) (arrayOf q.ratchetBytes) = some x := by
  obtain ⟨res, hres, hmap⟩ := oracleOfB.dhAgree k q.ratchetPublic
  obtain ⟨x, hx⟩ := (dhAgreeContributory_is.mp hcon) k q.ratchetPrivate q.ratchetPublic q.hRatchetPublic
  rw [hx] at hres
  cases hres
  refine ⟨arrayOf x, ?_⟩
  rw [← view_ratchet_public codec q, ← hmap]
  rfl

/-- **The ephemeral half of the repeat recognition passes on the same message**: for parts `p` of the first call,
the code's comparison of the copy of the message's ephemeral key the session keeps with the message's own, under
any private key, returns `true`: the two are the same bytes, they decode to the initiator's ephemeral public key, and
the agreement with it is not refused, under `DhAgreeContributory`. -/
theorem same_ephemeral_repeat (hcon : DhAgreeContributory) {ourB : lifecycle.Identity}
    {storeB : lifecycle.PrekeyStore} {msg : Slice U8} (p : ResponderPreparedParts ourB storeB msg)
    (q : InitiatorSecretParts rc crc our bundle) (hpe : p.peerEphemeral = q.ephemeralPublic)
    (k : tacenta_boundary.dh.PrivateKey) :
    lifecycle.same_ephemeral_agreement k p.ephemeralCopy.deref p.decoded.ephemeral.deref = ok true := by
  obtain ⟨-, -, hdecEph⟩ := Tacenta.UnitLifecycleEstablishResponder.curve_inputs_ok _ _ _ _ p.hCurve
  rw [p.ephemeralCopy_eq]
  obtain ⟨x, hx⟩ := (dhAgreeContributory_is.mp hcon) k q.ephemeral p.peerEphemeral (hpe ▸ q.hEphemeralPublic)
  simp [lifecycle.same_ephemeral_agreement, hdecEph, hx, Tacenta.UnitLifecycleEstablishResponder.array_eq_self]


open Tacenta.UnitHeadroomInvariant (OptionEqU64Shape) in
/-- **The initiator's first frame, delivered again through `Session::decrypt` at the session `establish_responder`
returned on it, is refused with no durable effect.**  Under the hypotheses of `responder_first_frame_successor`
(those of `responder_first_frame_succeeds` without the store bound) and the call's success equation, for every source
`rngB2` whose trace holds a draw `dB2`: the returned session `sB'` refines `firstReceiptSession`; the model's public
`decrypt` of the same bytes at that model session, at every codeword view, with the oracle holding `dB2` first,
recognises the repeat, consumes `dB2`, refuses `triple (classical outOfOrder)` and leaves the session as it was; and
the translated `decrypt` of the same bytes at `sB'` from `rngB2` returns `Triple(Classical(OutOfOrder))`, `sB'` itself
and a source whose trace is the rest after `dB2`.  The code step refines the model step: the refusal maps to the
model's, the session is the related one, and the draws agree.  The repeat recognition passes by `DhAgreeContributory`
(the session's ratchet key agrees with the initiator's ephemeral key) and the decoded identity; the inner receive is
`decrypt_ratchet_refines_of_invariant` at `sB'`, whose session-side premises `first_receipt_successor_facts` gives. -/
theorem responder_first_frame_repeat_refused [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type}
    (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {dh : DhView} (codec : DhCodecOf dh) (view : Model.Lifecycle.CodewordView)
    (oracleA : Model.Lifecycle.Oracle) (hsealA : Tacenta.UnitOracleShape.AeadSealClause Interp.real oracleA)
    (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (q : InitiatorSecretParts rc crc our bundle) (pending : Model.Lifecycle.PendingInitial)
    (hpend : (establishedModelOf dh q.session).pendingInitial = some pending)
    (plaintext : Slice U8) (hroom : plaintext.val.length + 48 ≤ Usize.max)
    (src : Model.Lifecycle.Bytes) (hsrc : src.length = Model.Braid.headerSize + Model.Braid.macSize)
    (c : tacenta_erasure.Chunk) (hcw : Tacenta.SessionUnitBraidT3.CodewordOf src c)
    (hsend : view.send (establishedModelOf dh q.session).braid (modelChunkOf src c) = modelCodewordOf c)
    (msg : Slice U8)
    (hmsg : sliceOf msg = initialWire (establishedModelOf dh q.session) pending
      (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame view oracleA (establishedModelOf dh q.session)
        (sliceOf plaintext) (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) (modelChunkOf src c)))
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundle)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundle.kem_prekey_id q.kemCiphertext q.kemSecret)
    (rngB : E) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (storeB' : lifecycle.PrekeyStore) (rngB' : E)
    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB'))
    (rngB2 : E) (dB2 : Model.Lifecycle.Key) (restB2 : List Model.Lifecycle.Key)
    (hdrawB2 : traceB rngB2 = dB2 :: restB2) :
    ∃ (p : ResponderPreparedParts ourB storeB msg) (ec : Array U8 32#usize) (dSend : Model.Lifecycle.Key)
      (rngB3 : E),
      SessionRefines dh oracleB.braidKem sB'
        (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)
          (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
          (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) ∧
      (∀ viewB : Model.Lifecycle.CodewordView,
        Model.Lifecycle.decrypt viewB { oracleB with draws := dB2 :: restB2 }
            (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)
              (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
              (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) (sliceOf msg) =
          { session := firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)
              (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
              (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB
            result := .error (.triple (.classical .outOfOrder))
            oracle := { oracleB with draws := restB2 } }) ∧
      lifecycle.Session.decrypt rcB crcB sB' msg rngB2 =
        ok (core.result.Result.Err (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical
          tacenta_ratchet.RatchetError.OutOfOrder)), sB', rngB3) ∧
      traceB rngB3 = restB2 := by
  rcases responder_first_frame_prepares rcB crcB contracts hpub hsym hrt hct hbound codec q pending hpend _ msg
      hmsg ourB storeB hpublish hidentity hdistinct hkem rngB with ⟨-, e, -, hrefuse⟩ |
    ⟨p, -, -, h3, -, h5, h6, -, h8, -⟩
  · rw [hrefuse] at hcallB
    cases hcallB
  obtain ⟨-, -, hsp, hop⟩ := parts_of_first_frame contracts.decrypt.braid.zeroizingArray hpub codec hct
    hbound q pending hpend _ msg hmsg ourB storeB hpublish hidentity p
  obtain ⟨ec, dSend, ptB0, sB0, rngB0, -, -, hinner, -, -, hrel⟩ :=
    responder_first_frame_inner_succeeds rcB crcB contracts hpub hsym hcon haead hoeq codec view oracleA hsealA
      traceB oracleB oracleOfB agreements q plaintext hroom src hsrc c hcw hsend p h3 h5 hsp hop h8 rngB
      htraceB dB restB hdrawB
  obtain ⟨storeB0, -, hout⟩ := establish_responder_commit_of_inner rcB crcB p rngB ptB0 sB0 rngB0 hinner _ hcallB
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at hout
  obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ := hout
  have ha4 := dhPublicValid_canonical hpub q.hRatchetPublic q.hRatchetBytes
  obtain ⟨hinv, hhead⟩ := Tacenta.UnitLifecycleResponderSuccessor.first_receipt_successor_facts hpub hoeq
    contracts.divCeilValue contracts.decrypt.braid.headerLen rcB crcB codec oracleOfB p rngB dB restB hdrawB _ _ _
    hinner _ _ _ _ _ _ _ _ q.ratchetBytes ha4 hrel
  -- the decoded message, read back
  obtain ⟨d, hd, -, -, -, -, -, hdid, -⟩ := Tacenta.UnitLifecycleResponderFirstFrame.decode_first_frame hpub codec
    hct hbound q pending hpend _ msg hmsg
  have hpd : p.decoded = d := by
    have := p.hDecode
    rw [hd] at this
    simp only [ok.injEq, core.result.Result.Ok.injEq] at this
    exact this.symm
  -- the session after the first receipt keeps the prepared session's wrapper fields
  have hwrites := Tacenta.UnitLifecycleAtomicity.decrypt_ratchet_ok_writes rcB crcB p.session p.message rngB ptB
    sB' rngB' hinner
  have hestablished : sB'.established_ephemeral = some p.ephemeralCopy := by
    rw [hwrites]; rfl
  have hpeer : sB'.peer_identity_public = q.ourPublic := by
    rw [hwrites]; exact h5
  -- the second source and its oracle
  let oracleB2 : Model.Lifecycle.Oracle := { oracleB with draws := dB2 :: restB2 }
  let oracleB3 : Model.Lifecycle.Oracle := { oracleB with draws := restB2 }
  have oracleOfB2 : DecryptOracleOf rcB crcB dh traceB oracleB2 :=
    ⟨oracleOfB.dhPublic, oracleOfB.dhAgree, oracleOfB.aeadOpen, oracleOfB.random32⟩
  let mB := firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)
    (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
    (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB
  let aview := attributedView view (modelCodewordOf c).index (modelCodewordOf c).data (modelChunkOf src c)
  -- the model step on the frame again
  have hA := established_triple_first dh q.toInitiatorOutputParts
  obtain ⟨a, ha, hcan, -⟩ :=
    Tacenta.UnitLifecycleResponderFirstFrame.view_of_public hpub codec q.hRatchetPublic
  rw [q.hRatchetBytes] at ha
  cases ha
  have hkey : Model.Messages.checkKey (arrayOf q.ratchetBytes) = some () := by
    simp [Model.Messages.checkKey, Tacenta.UnitLifecycleResponderFirstFrame.canonicalKey_arrayOf _ hcan]
  have hlen : (arrayOf q.ratchetBytes).length = 32 := by simp [arrayOf]
  obtain ⟨dR, hdR⟩ := key_agreement_ratchet hcon codec oracleOfB2 q sB'.ratchet_private
  rw [hrel.ratchetPrivate] at hdR
  obtain ⟨dS, hdS⟩ := responder_candidate_agreement hcon codec oracleOfB2 q rngB2 dB2 restB2 hdrawB2
  have hM : ∀ viewB, Model.Lifecycle.decryptRatchet viewB oracleB2 mB (sliceOf p.message) =
      ⟨mB, .error (.triple (.classical .outOfOrder)), oracleB3⟩ := by
    intro viewB
    rw [h8]
    exact repeat_frame_model_refused view viewB oracleA oracleB2 (establishedModelOf dh q.session) mB
      (arrayOf q.ratchetBytes) (arrayOf q.peerRatchetBytes) (arrayOf q.rootKey) (arrayOf q.sendChain)
      (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) (arrayOf ec) (arrayOf q.dhOut)
      dSend (oracleB.dhPublic dB) (sliceOf plaintext) _ (modelChunkOf src c) hA rfl
      (by simp [mB, firstReceiptSession, Model.Lifecycle.agreementFailed]) hlen hkey
      (by rw [hsend]; simp [modelCodewordOf, arrayOf]) dR hdR dB2 restB2 rfl dS hdS
  -- the run inputs of the inner receive at the session after the first receipt
  have hdec : Model.CompositeHeader.decodeDetailed (sliceOf (ResponderPreparedParts.message p)) =
      .ok (Tacenta.UnitLifecycleEstablishedEncrypt.firstComposite view (establishedModelOf dh q.session)
          (modelChunkOf src c),
        oracleA.aeadSeal
          (Model.State.messageKeys (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) .tacenta).1
          (Model.State.messageKeys (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) .tacenta).2.1
          (Model.State.messageKeys (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) .tacenta).2.2
          (sliceOf plaintext)
          (Tacenta.UnitLifecycleResponderFirstReceipt.firstAd view (establishedModelOf dh q.session)
            (modelChunkOf src c))) := by
    rw [h8, Model.CompositeHeader.decodeDetailed_ok_iff]
    exact Tacenta.UnitLifecycleResponderFirstReceipt.decode_encodeMessage _ _
      (by simpa [Tacenta.UnitLifecycleEstablishedEncrypt.firstComposite, hA, firstSenderTriple] using hlen)
      (by simpa [Tacenta.UnitLifecycleEstablishedEncrypt.firstComposite, hA, firstSenderTriple] using hkey)
      (fun w hw => by
        simp only [Tacenta.UnitLifecycleEstablishedEncrypt.firstComposite, hsend, Option.some.injEq] at hw
        subst hw
        simp [modelCodewordOf, arrayOf])
  have inputs : DecryptRatchetRunInputs aview oracleB2 traceB sB' mB p.message rngB2 := by
    refine ⟨?_, ?_, ⟨dB2, restB2, hdrawB2⟩⟩
    · intro rc' mc ct hd' hrel'
      rw [hdec] at hd'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hd'
      obtain ⟨rfl, -⟩ := hd'
      have hag := hrel'.agChunk
      unfold Tacenta.UnitLifecycleT3.IncomingChunkRefines
      simp only [Tacenta.UnitLifecycleEstablishedEncrypt.firstComposite, hsend] at hag ⊢
      rcases hrc : rc'.ag_chunk with _ | rch
      · rw [hrc] at hag
        exact hag.elim
      · rw [hrc] at hag
        simp only
        obtain ⟨hi, hdat⟩ := hag
        have hidx : rch.index = c.index := by
          apply UScalar.eq_of_val_eq
          rw [hi]
          simp [modelCodewordOf]
        have hdata : rch.data = c.data := by
          apply Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes
          exact hdat
        refine ⟨src, ?_, ?_⟩
        · rw [hidx, hdata]
          exact hcw
        · simp [aview, attributedView, hidx, modelChunkOf]
    · intro mc ct hd'
      rw [hdec] at hd'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hd'
      obtain ⟨rfl, -⟩ := hd'
      intro m hm _
      simp only [Model.Lifecycle.braidMessageOf, Tacenta.UnitLifecycleEstablishedEncrypt.firstComposite, hsend,
        Option.map_some, Option.some.injEq, aview, attributedView, and_self, if_true] at hm
      subst hm
      simp [mB, firstReceiptSession, Tacenta.SessionUnitBraidT3.ChunkFits, Model.Braid.Decoder.addChunk,
        Model.Braid.Decoder.new, modelChunkOf, hsrc, Model.Lifecycle.braidMessageOf,
        Tacenta.UnitLifecycleEstablishedEncrypt.firstComposite, Model.Lifecycle.braidTypeOf]
  -- the inner receive refines the model's at the session after the first receipt
  obtain ⟨inner, hinner2, hstep⟩ := Tacenta.UnitLifecycleDecryptRunBounds.decrypt_ratchet_refines_of_invariant
    rcB crcB traceB dh aview oracleB2 oracleOfB2 codec contracts.decrypt agreements sB' mB p.message rngB2 hinv
    hrel hhead hdrawB2 inputs
  have hres := hstep.result
  have hdr := hstep.draws
  rw [hM] at hres hdr
  obtain ⟨res, sB2, rngB3⟩ := inner
  have he : res = core.result.Result.Err (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical
      tacenta_ratchet.RatchetError.OutOfOrder)) := by
    cases res with
    | Ok v => simp [ResultRefines] at hres
    | Err e =>
      simp only [ResultRefines] at hres
      have h' : Tacenta.UnitLifecycleT3.refusalOf e = Tacenta.UnitLifecycleT3.refusalOf
          (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.OutOfOrder)) :=
        hres
      rw [Tacenta.UnitLifecycleT3.refusalOf_injective h']
  subst he
  have hs2 := Tacenta.UnitLifecycleAtomicity.decrypt_ratchet_err_leaves_state rcB crcB sB' p.message rngB2 _ sB2
    rngB3 hinner2
  subst hs2
  -- the wrapper: the message is an initial message, and the repeat recognition passes
  have htype : serialization.message_type msg = ok (some serialization.MessageType.Initial) := by
    obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT3.message_type_refines msg)
    have hmt : Model.Lifecycle.messageType (sliceOf msg) = some .initial := by
      rw [hmsg]
      simp [initialWire, Model.Messages.encodeInitial, Model.Lifecycle.messageType, Model.Messages.typeInitial,
        Model.Messages.typeRatchet]
    rw [hmt] at hpost
    rw [hr]
    rcases r with _ | ⟨_ | _⟩ <;> simp [Tacenta.UnitLifecycleT3.messageTypeOf] at hpost ⊢
  have hidentity' : vecOf p.decoded.identity =
      Model.PersistedState.SessionState.encodeEc (dh.publicKey sB2.peer_identity_public) := by
    rw [hpeer, hpd]; exact hdid
  have hsame := same_ephemeral_repeat hcon p q h6 sB2.ratchet_private
  have hmodelSame := (Tacenta.UnitLifecycleInitialAgreementT3.repeated_initial_agreement_true_iff oracleOfB2 codec
    hrel p.ephemeralCopy p.decoded).mp hsame
  have hmsgInner : (Tacenta.SessionUnitWireInitialT3.initialOf p.decoded).ratchetMessage = sliceOf p.message := rfl
  obtain ⟨out, hout, hstepOut⟩ := Tacenta.UnitLifecycleT3.decrypt_initial_repeat_agreement_refusal_exact rcB crcB
    traceB dh codec oracleB.braidKem aview oracleB2 { oracleB with draws := restB2 } sB2 mB msg rngB2 rngB3
    p.ephemeralCopy p.decoded _ _ mB hrel hdr htype p.hDecode hestablished hidentity' hsame hmodelSame hinner2
    (by rw [hmsgInner]; exact hM aview) (by rw [hmsgInner]; exact hstep)
  -- the model's public step, at every view
  obtain ⟨-, -, -, hrepeat⟩ := Tacenta.UnitLifecycleT3.repeated_initial_agreement_checks_refine oracleB2 dh codec
    oracleB.braidKem sB2 mB p.ephemeralCopy p.decoded hrel hestablished hidentity' hmodelSame
  have hdecodeRel := Tacenta.UnitLifecycleT3.decode_initial_refines_lifecycle msg
  rw [p.hDecode] at hdecodeRel
  have hdispatch := Model.Lifecycle.dispatchDecrypt_repeat oracleB2 mB (sliceOf msg)
    (Tacenta.SessionUnitWireInitialT3.initialOf p.decoded)
    (Tacenta.UnitLifecycleT3.message_type_refines_initial msg htype) hdecodeRel hrepeat
  have hD : ∀ viewB, Model.Lifecycle.decrypt viewB oracleB2 mB (sliceOf msg) =
      ⟨mB, .error (.triple (.classical .outOfOrder)), oracleB3⟩ := by
    intro viewB
    simp only [Model.Lifecycle.decrypt, hdispatch, hmsgInner, hM viewB]
  -- the code's public step
  have hres' := hstepOut.result
  have hdr' := hstepOut.draws
  rw [hD aview] at hres' hdr'
  obtain ⟨res', sB3, rngB4⟩ := out
  have he' : res' = core.result.Result.Err (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical
      tacenta_ratchet.RatchetError.OutOfOrder)) := by
    cases res' with
    | Ok v => simp [ResultRefines] at hres'
    | Err e =>
      simp only [ResultRefines] at hres'
      have h' : Tacenta.UnitLifecycleT3.refusalOf e = Tacenta.UnitLifecycleT3.refusalOf
          (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.OutOfOrder)) :=
        hres'
      rw [Tacenta.UnitLifecycleT3.refusalOf_injective h']
  rw [he'] at hout
  have hs3 := Tacenta.UnitLifecycleAtomicity.decrypt_err_leaves_state rcB crcB sB2 msg rngB2 _ sB3 rngB4 hout
  rw [hs3] at hout
  exact ⟨p, ec, dSend, rngB4, hrel, hD, hout, hdr'⟩

end Inner

section Comp
open Tacenta.UnitLifecycleT3 (DhView DhCodecOf vecOf sliceOf arrayOf SessionRefines modelChunkOf CodewordViewSendOf)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid establishedModelOf InitiatorOutputParts)
open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts responderModelOf)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstKey firstReceiptSession DhAgreeContributory AeadRoundTrip
  headerSource established_triple_first first_send_key)
open Tacenta.UnitLifecycleT3 (OracleOf BraidSendRefinementContracts TripleSendRefinementContracts KemView) in
/-- **The initiator's first send, delivered twice: the responder's `decrypt` of the second copy is refused with no
durable effect.**  Under the hypotheses of `initiator_first_send_responder_successor_hypotheses` (those of
`initiator_first_send_responder_receives` without the store bound, and the success equation of `establish_responder`
on the bytes the initiator's first `encrypt` emitted) and a responder source `rngB2` whose trace holds a draw `dB2`:
`sB'` refines `mB`, the model's step after the first receipt at the header source of the initiator's key generation;
the model's public `decrypt` of the same bytes at `mB`, at every codeword view, with the oracle holding `dB2` first,
consumes `dB2`, refuses `triple (classical outOfOrder)` and leaves `mB`; and the translated `decrypt` of the same bytes
at `sB'` from `rngB2` returns `Triple(Classical(OutOfOrder))`, `sB'` itself and a source whose trace is the rest after
`dB2`.  `rngB2` is any source with a draw; the reach takes the one the first call left. -/
theorem initiator_first_send_responder_repeat_refused [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E) (ourA : lifecycle.Identity)
    (bundleA : lifecycle.PublishedBundle) (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
    (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE ourA bundleA expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (q : InitiatorSecretParts rcE crcE ourA bundleA) (hq : s = q.session)
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws) (d1 d2 : Model.Lifecycle.Key)
    (rest : List Model.Lifecycle.Key) (hdraws : trace rng = d1 :: d2 :: rest)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng = ok (core.result.Result.Ok bytes, s', rng'))
    (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (traceB : F → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundleA)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundleA.kem_prekey_id q.kemCiphertext q.kemSecret)
    (rngB : F) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (storeB' : lifecycle.PrekeyStore) (rngB' : F)
    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB'))
    (rngB2 : F) (dB2 : Model.Lifecycle.Key) (restB2 : List Model.Lifecycle.Key)
    (hdrawB2 : traceB rngB2 = dB2 :: restB2) :
    ∃ (p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes)) (ec : Array U8 32#usize)
      (dSend : Model.Lifecycle.Key) (dk ekSeed ekVector : Model.Braid.Bytes) (mB : Model.Lifecycle.Session)
      (rngB3 : F),
      oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector) ∧
      mB = firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret)
          ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
          (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
          (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB ∧
      SessionRefines dh oracleB.braidKem sB' mB ∧
      (∀ viewB : Model.Lifecycle.CodewordView,
        Model.Lifecycle.decrypt viewB { oracleB with draws := dB2 :: restB2 } mB
            (sliceOf (alloc.vec.Vec.deref bytes)) =
          { session := mB, result := .error (.triple (.classical .outOfOrder)),
            oracle := { oracleB with draws := restB2 } }) ∧
      lifecycle.Session.decrypt rcB crcB sB' (alloc.vec.Vec.deref bytes) rngB2 =
        ok (core.result.Result.Err (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical
          tacenta_ratchet.RatchetError.OutOfOrder)), sB', rngB3) ∧
      traceB rngB3 = restB2 := by
  obtain ⟨output, hcall', hdr, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes rc
    crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen
    hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h plaintext hroom rng htrace d1 d2 rest hdraws
  rw [hcall] at hcall'
  cases hcall'
  rcases hcases with ⟨-, hres, -⟩ | ⟨dk, ekSeed, ekVector, hkg, bytes', hres, -, -, tripleNext, messageKey,
    chunk, encoder, pending, a, ⟨header, hsendM⟩, hbraidA, hnc, hpend, hwire, -⟩
  · cases hres
  simp only [core.result.Result.Ok.injEq] at hres
  subst hres
  subst hq
  have hmk : messageKey = firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend) := by
    rw [established_triple_first dh q.toInitiatorOutputParts, first_send_key] at hsendM
    simp only [Except.ok.injEq, Prod.mk.injEq] at hsendM
    exact hsendM.2.2.symm
  have ha : a = Tacenta.SessionUnitBraidT3.AuthOf q.auth := by
    simp only [establishedModelOf, InitiatorOutputParts.session,
      Tacenta.UnitLifecycleEstablishInitiatorShape.unsampledModelOf, Model.Braid.BraidState.keysUnsampled.injEq]
      at hbraidA
    exact hbraidA.2.symm
  subst ha
  have hchunk : chunk = ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed
      ekVector, 0⟩ := by
    simp only [Model.Braid.encode, Model.Braid.Encoder.nextChunk, Prod.mk.injEq] at hnc
    rw [← hnc.1]
    rfl
  obtain ⟨hs32, -, hhl⟩ := hsizes _ _ _ _ hkg
  have hsrc : (headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector).length =
      Model.Braid.headerSize + Model.Braid.macSize := by
    simp [headerSource, Model.Braid.Auth.macHdr, Model.Kdf.hmac_length, Model.Kdf.hashLen, hs32, hhl,
      Model.Braid.headerSize, Model.Braid.macSize]
  obtain ⟨-, -, c, -, -, hc0, hcw, -⟩ := Tacenta.UnitHeldKemWitness.held_encoder contracts.divCeilValue
    agreements.erasure _ (by rw [hsrc]; rfl)
  have hmc : modelChunkOf (headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed
      ekVector) c = ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩ := by
    simp [modelChunkOf, hc0]
  have hsend := codewordView.send (establishedModelOf dh q.session).braid _ c hcw
  rw [hmk, hchunk, ← hmc] at hwire
  obtain ⟨p, ec, dSend, rngB3, hrel, hD, hdec, hdr3⟩ := responder_first_frame_repeat_refused rcB crcB contracts
    hpub hsym hcon haead hrt hct hbound hoeq codec view oracle oracleOf.aeadSeal traceB oracleB oracleOfB agreements
    q pending hpend plaintext (by omega) _ hsrc c hcw hsend (alloc.vec.Vec.deref bytes) hwire ourB storeB hpublish
    hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB rngB2 dB2 restB2 hdrawB2
  rw [hmc] at hrel hD
  exact ⟨p, ec, dSend, dk, ekSeed, ekVector, _, rngB3, hkg, rfl, hrel, hD, hdec, hdr3⟩

end Comp

section Reach
open Tacenta.UnitLifecycleT3 (DhView)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptRatchetAgreements)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitLifecycleResponderFirstFrame (FirstFrameSuccessShape InitiatorSecretParts DhAgreeSymmetric)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory AeadRoundTrip first_send_receive_reachable
  initiator_first_send_responder_receives)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)

open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleEstablishedEncrypt (EncryptExtraLaws emptyPlaintext) in
/-- **The reach of the refused repeat**: at the real constants, under the laws of `first_send_receive_reachable`
(all assumed), for every initiator identity and every 64-byte source at whose bytes the model's key generation
answers, one run from `publish` through the establishment, the first send of the empty plaintext and the responder's
successful `establish_responder`, after which the responder's `decrypt` of the same bytes at the session that call
returned, from the source it left (which still holds the second 32-byte draw of the responder's 64 bytes), returns
`Triple(Classical(OutOfOrder))` and that session.  It applies `initiator_first_send_responder_repeat_refused` to the run
of `first_send_receive_reachable`, with the draw from `initiator_first_send_responder_receives`.  Last-resort path only. -/
theorem first_send_repeat_refused_reachable (K : Model.Braid.Kem) (dh : DhView)
    (kem : Tacenta.UnitLifecycleT3.KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (X : EncryptExtraLaws K dh kem) (RA : Nonempty (ResponderAxiom Interp.real byteRng))
    (hsym : DhAgreeSymmetric) (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (FS : FirstFrameSuccessShape Interp.real tacenta_boundary.kem.KeyPair.public_key
      @alloc.vec.Vec.is_empty)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K)
    (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (ourA : lifecycle.Identity) (seed : List Std.U8) (hseed : seed.length = 64)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle)
      (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (bytes : alloc.vec.Vec Std.U8)
      (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity)
      (storeB : lifecycle.PrekeyStore) (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8)
      (storeB' : lifecycle.PrekeyStore) (rngB' rngB3 : List Std.U8),
      oracle.braidKem = K ∧
      lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext seed =
        ok (core.result.Result.Ok bytes, s', rng') ∧
      lifecycle.PrekeyStore.publish storeB = ok bundle ∧
      lifecycle.establish_responder byteRng byteCrc ourB storeB (alloc.vec.Vec.deref bytes) seed =
        ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
      lifecycle.Session.decrypt byteRng byteCrc sB' (alloc.vec.Vec.deref bytes) rngB' =
        ok (core.result.Result.Err (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical
          tacenta_ratchet.RatchetError.OutOfOrder)), sB', rngB3) := by
  obtain ⟨oracle, bundle, rng0, rng1, q, bytes, s', rng', ourB, storeB, sB', ptB, storeB', rngB', hK, H, hcall,
    hpublish, hidentity, hdistinct, hkem, hhead, oracleOfB, htraceB, -, -, hcallB, -⟩ :=
    first_send_receive_reachable K dh kem L A S hpub hct X RA hsym hrt FS hsizes hcon haead ourA seed hseed hkg
  obtain ⟨contracts⟩ := Tacenta.UnitSatisfiabilityRecords.responder_contracts_of_axiom_base byteRng RA L.laws
  obtain ⟨inst⟩ := H.derivedKeys
  subst hK
  obtain ⟨oracle0, bundle1, s1, rng11, hK0, H1⟩ :=
    Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable
      oracle.braidKem dh L A S hpub hct ourA
  have ag : DecryptRatchetAgreements oracle.braidKem :=
    hK0 ▸ (H1 Tacenta.UnitLifecycleRepair.witnessView).agreements
  obtain ⟨d1, d2, rest2, hdrB⟩ : ∃ d1 d2 rest2, byteTrace seed = d1 :: d2 :: rest2 := by
    have := Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega)
    exact ⟨_, _, _, this⟩
  -- the source the first receipt left holds the second draw
  obtain ⟨-, hdisj⟩ := initiator_first_send_responder_receives byteRng byteCrc byteTrace dh kem
    Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec
    H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes H.kemCiphertextLen
    H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session H.established q rfl emptyPlaintext H.room seed
    H.trace_eq _ _ _ (Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega)) bytes s' rng'
    hcall byteRng byteCrc contracts hpub hsym hcon haead hrt L.optionEq byteTrace oracle oracleOfB ag ourB
    storeB hpublish hidentity hdistinct hkem hhead seed htraceB d1 (d2 :: rest2) hdrB
  have hdr2 : byteTrace rngB' = d2 :: rest2 := by
    rcases hdisj with ⟨-, e, -, hrefuse⟩ |
      ⟨-, -, -, -, -, -, ptB0, sB0, storeB0, rngB0, -, -, -, -, -, -, -, -, -, -, hcall0, -, hdr0, -⟩
    · rw [hrefuse] at hcallB
      cases hcallB
    · rw [hcallB] at hcall0
      simp only [ok.injEq, Prod.mk.injEq] at hcall0
      rw [hcall0.2.2]
      exact hdr0
  obtain ⟨-, -, -, -, -, -, -, rngB3, -, -, -, -, hdec, -⟩ := initiator_first_send_responder_repeat_refused byteRng
    byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec
    H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes
    H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session H.established q rfl
    emptyPlaintext H.room seed H.trace_eq _ _ _ (Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega))
    bytes s' rng' hcall byteRng byteCrc contracts hpub hsym hcon haead hrt L.optionEq byteTrace oracle oracleOfB ag
    ourB storeB hpublish hidentity hdistinct hkem seed htraceB d1 (d2 :: rest2) hdrB ptB sB' storeB' rngB' hcallB
    rngB' d2 rest2 hdr2
  exact ⟨oracle, bundle, q, bytes, s', rng', ourB, storeB, sB', ptB, storeB', rngB', rngB3, rfl, hcall, hpublish,
    hcallB, hdec⟩

end Reach
end Tacenta.UnitLifecycleResponderRepeatedFrame

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleResponderRepeatedFrame.repeat_receive_outOfOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderRepeatedFrame.repeat_receive_outOfOrder

/--
info: 'Tacenta.UnitLifecycleResponderRepeatedFrame.repeat_receive_with_eviction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderRepeatedFrame.repeat_receive_with_eviction

/--
info: 'Tacenta.UnitLifecycleResponderRepeatedFrame.repeat_frame_model_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderRepeatedFrame.repeat_frame_model_refused

/--
info: 'Tacenta.UnitLifecycleResponderRepeatedFrame.key_agreement_ratchet' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderRepeatedFrame.key_agreement_ratchet

/--
info: 'Tacenta.UnitLifecycleResponderRepeatedFrame.same_ephemeral_repeat' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderRepeatedFrame.same_ephemeral_repeat

/--
info: 'Tacenta.UnitLifecycleResponderRepeatedFrame.responder_first_frame_repeat_refused' depends on axioms: [propext,
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
 tacenta_session_unit.alloc.vec.Vec.is_empty,
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
 tacenta_session_unit.tacenta_boundary.kem.KeyPair.public_key,
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
#print axioms Tacenta.UnitLifecycleResponderRepeatedFrame.responder_first_frame_repeat_refused

/--
info: 'Tacenta.UnitLifecycleResponderRepeatedFrame.initiator_first_send_responder_repeat_refused' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.xeddsa.sign,
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
 tacenta_session_unit.alloc.vec.Vec.is_empty,
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
 tacenta_session_unit.tacenta_boundary.kem.KeyPair.public_key,
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
#print axioms Tacenta.UnitLifecycleResponderRepeatedFrame.initiator_first_send_responder_repeat_refused

/--
info: 'Tacenta.UnitLifecycleResponderRepeatedFrame.first_send_repeat_refused_reachable' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.xeddsa.sign,
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
 tacenta_session_unit.alloc.vec.Vec.is_empty,
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
 tacenta_session_unit.tacenta_boundary.kem.KeyPair.public_key,
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
#print axioms Tacenta.UnitLifecycleResponderRepeatedFrame.first_send_repeat_refused_reachable

set_option pp.deepTerms true
set_option pp.proofs.withType true

/--
info: Tacenta.UnitLifecycleResponderRepeatedFrame.repeat_receive_outOfOrder : ∀
  (a4 ec prk k1 k2 d dSend newPub dR dS np : Model.State.Key) (out : Option Model.SparseRatchet.Output),
  Model.Triple.receiveDetailed
      (Tacenta.UnitLifecycleResponderFirstReceipt.receiverAfterFirst ec prk k1 k2 a4 d dSend newPub)
      (Tacenta.UnitLifecycleResponderFirstReceipt.firstHeader a4) dR dS np out =
    Except.error (Model.Triple.ReceiveRefusal.classical Model.Ratchet.ReceiveRefusal.outOfOrder)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderRepeatedFrame.repeat_receive_outOfOrder

/--
info: Tacenta.UnitLifecycleResponderRepeatedFrame.repeat_receive_with_eviction : ∀
  (a4 ec prk k1 k2 d dSend newPub dR dS np : Model.State.Key) (composite : Model.CompositeHeader.Composite)
  (out : Option Model.SparseRatchet.Output),
  Model.Lifecycle.receiveWithEviction
      (Tacenta.UnitLifecycleResponderFirstReceipt.receiverAfterFirst ec prk k1 k2 a4 d dSend newPub) composite
      (Tacenta.UnitLifecycleResponderFirstReceipt.firstHeader a4) dR dS np out =
    Except.error (Model.Triple.ReceiveRefusal.classical Model.Ratchet.ReceiveRefusal.outOfOrder)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderRepeatedFrame.repeat_receive_with_eviction

/--
info: Tacenta.UnitLifecycleResponderRepeatedFrame.repeat_frame_model_refused : ∀ (viewA viewB : Model.Lifecycle.CodewordView)
  (oracleA oracleB : Model.Lifecycle.Oracle) (mA mB : Model.Lifecycle.Session)
  (a4 peer rkA cksA prk k1 k2 ec d dSend newPub : Model.State.Key) (pt : Model.Lifecycle.Bytes) (mk : Model.State.Key)
  (chunk : Model.Braid.Chunk),
  mA.triple = Tacenta.UnitLifecycleResponderFirstReceipt.firstSenderTriple a4 peer rkA cksA prk k1 k2 →
    mB.triple = Tacenta.UnitLifecycleResponderFirstReceipt.receiverAfterFirst ec prk k1 k2 a4 d dSend newPub →
      Model.Lifecycle.agreementFailed mB = false →
        List.length a4 = 32 →
          Model.Messages.checkKey a4 = some () →
            (viewA.send mA.braid chunk).data.length = 32 →
              ∀ (dR : Model.State.Key),
                oracleB.dhAgree mB.ratchetPrivate a4 = some dR →
                  ∀ (c : Model.State.Key) (rest : List Model.State.Key),
                    oracleB.draws = c :: rest →
                      ∀ (dS : Model.State.Key),
                        oracleB.dhAgree c a4 = some dS →
                          Model.Lifecycle.decryptRatchet viewB oracleB mB
                              (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame viewA oracleA mA pt mk chunk) =
                            { session := mB,
                              result :=
                                Except.error
                                  (Model.Lifecycle.Refusal.triple
                                    (Model.Lifecycle.TripleRefusal.classical
                                      Model.Lifecycle.RatchetRefusal.outOfOrder)),
                              oracle :=
                                { draws := rest, braidKem := oracleB.braidKem, dhPublic := oracleB.dhPublic,
                                  dhAgree := oracleB.dhAgree, identityValid := oracleB.identityValid,
                                  aeadSeal := oracleB.aeadSeal, aeadOpen := oracleB.aeadOpen,
                                  kemValid := oracleB.kemValid, kemEncaps := oracleB.kemEncaps,
                                  kemDecaps := oracleB.kemDecaps, sigVerify := oracleB.sigVerify,
                                  sigSign := oracleB.sigSign } }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderRepeatedFrame.repeat_frame_model_refused

/--
info: @Tacenta.UnitLifecycleResponderRepeatedFrame.key_agreement_ratchet : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle},
  Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
    ∀ {E : Type} {rcB : tacenta_session_unit.rand_core_1.RngCore E}
      {crcB : tacenta_session_unit.rand_core_1.CryptoRng E} {dh : Tacenta.UnitLifecycleT3.DhView},
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        ∀ {traceB : E → List Model.Lifecycle.Key} {oracleB : Model.Lifecycle.Oracle},
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
            ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle)
              (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
              ∃ x, oracleB.dhAgree (dh.privateKey k) (Tacenta.UnitLifecycleT3.arrayOf q.ratchetBytes) = some x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderRepeatedFrame.key_agreement_ratchet

/--
info: @Tacenta.UnitLifecycleResponderRepeatedFrame.same_ephemeral_repeat : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle},
  Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
    ∀ {ourB : tacenta_session_unit.lifecycle.Identity} {storeB : tacenta_session_unit.lifecycle.PrekeyStore}
      {msg : Aeneas.Std.Slice Aeneas.Std.U8}
      (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg)
      (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle),
      p.peerEphemeral = q.ephemeralPublic →
        ∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
          tacenta_session_unit.lifecycle.same_ephemeral_agreement k p.ephemeralCopy.deref p.decoded.ephemeral.deref =
            Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderRepeatedFrame.same_ephemeral_repeat

/--
info: @Tacenta.UnitLifecycleResponderRepeatedFrame.responder_first_frame_repeat_refused : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type} (rcB : tacenta_session_unit.rand_core_1.RngCore E)
  (crcB : tacenta_session_unit.rand_core_1.CryptoRng E)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
      Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
        Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
          Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
            Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
              Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                    @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                  ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
                    Tacenta.UnitLifecycleT3.DhCodecOf dh →
                      ∀ (view : Model.Lifecycle.CodewordView) (oracleA : Model.Lifecycle.Oracle),
                        Tacenta.UnitOracleShape.AeadSealClause Tacenta.UnitSatisfiabilityJoint.Interp.real oracleA →
                          ∀ (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle),
                            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
                              Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracleB.braidKem →
                                ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle)
                                  (pending : Model.Lifecycle.PendingInitial),
                                  (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh
                                          q.session).pendingInitial =
                                      some pending →
                                    ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
                                      (↑plaintext).length + 48 ≤ Aeneas.Std.Usize.max →
                                        ∀ (src : Model.Lifecycle.Bytes),
                                          List.length src = Model.Braid.headerSize + Model.Braid.macSize →
                                            ∀ (c : tacenta_session_unit.tacenta_erasure.Chunk),
                                              Tacenta.SessionUnitBraidT3.CodewordOf src c →
                                                view.send
                                                      (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                          dh q.session).braid
                                                      (Tacenta.UnitLifecycleT3.modelChunkOf src c) =
                                                    Tacenta.UnitLifecycleT3.modelCodewordOf c →
                                                  ∀ (msg : Aeneas.Std.Slice Aeneas.Std.U8),
                                                    Tacenta.UnitLifecycleT3.sliceOf msg =
                                                        Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
                                                          (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                            dh q.session)
                                                          pending
                                                          (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame view
                                                            oracleA
                                                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                              dh q.session)
                                                            (Tacenta.UnitLifecycleT3.sliceOf plaintext)
                                                            (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                              (Tacenta.UnitLifecycleT3.arrayOf q.sendChain)
                                                              (Tacenta.UnitLifecycleT3.arrayOf q.sparseSend))
                                                            (Tacenta.UnitLifecycleT3.modelChunkOf src c)) →
                                                      ∀ (ourB : tacenta_session_unit.lifecycle.Identity)
                                                        (storeB : tacenta_session_unit.lifecycle.PrekeyStore),
                                                        storeB.publish = Aeneas.Std.Result.ok bundle →
                                                          ourB.public = Aeneas.Std.Result.ok storeB.identity_public →
                                                            Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                storeB →
                                                              Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                  storeB bundle.kem_prekey_id q.kemCiphertext
                                                                  q.kemSecret →
                                                                ∀ (rngB : E),
                                                                  traceB rngB = oracleB.draws →
                                                                    ∀ (dB : Model.Lifecycle.Key)
                                                                      (restB : List Model.Lifecycle.Key),
                                                                      traceB rngB = dB :: restB →
                                                                        ∀ (ptB : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
                                                                          (sB' : tacenta_session_unit.lifecycle.Session)
                                                                          (storeB' :
                                                                            tacenta_session_unit.lifecycle.PrekeyStore)
                                                                          (rngB' : E),
                                                                          tacenta_session_unit.lifecycle.establish_responder
                                                                                rcB crcB ourB storeB msg rngB =
                                                                              Aeneas.Std.Result.ok
                                                                                (Aeneas.Std.core.result.Result.Ok
                                                                                    (sB', ptB),
                                                                                  storeB', rngB') →
                                                                            ∀ (rngB2 : E) (dB2 : Model.Lifecycle.Key)
                                                                              (restB2 : List Model.Lifecycle.Key),
                                                                              traceB rngB2 = dB2 :: restB2 →
                                                                                ∃ p ec dSend rngB3,
                                                                                  Tacenta.UnitLifecycleT3.SessionRefines
                                                                                      dh oracleB.braidKem sB'
                                                                                      (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                                        (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                          dh p)
                                                                                        (Tacenta.UnitLifecycleT3.sliceOf
                                                                                          p.braidSecret)
                                                                                        (Tacenta.UnitLifecycleT3.modelChunkOf
                                                                                          src c)
                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                          ec)
                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                          q.sparseRoot)
                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                          q.sparseSend)
                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                          q.sparseReceive)
                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                          q.ratchetBytes)
                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                          q.dhOut)
                                                                                        dSend (oracleB.dhPublic dB)
                                                                                        dB) ∧
                                                                                    (∀
                                                                                        (viewB :
                                                                                          Model.Lifecycle.CodewordView),
                                                                                        Model.Lifecycle.decrypt viewB
                                                                                            { draws := dB2 :: restB2,
                                                                                              braidKem :=
                                                                                                oracleB.braidKem,
                                                                                              dhPublic :=
                                                                                                oracleB.dhPublic,
                                                                                              dhAgree :=
                                                                                                oracleB.dhAgree,
                                                                                              identityValid :=
                                                                                                oracleB.identityValid,
                                                                                              aeadSeal :=
                                                                                                oracleB.aeadSeal,
                                                                                              aeadOpen :=
                                                                                                oracleB.aeadOpen,
                                                                                              kemValid :=
                                                                                                oracleB.kemValid,
                                                                                              kemEncaps :=
                                                                                                oracleB.kemEncaps,
                                                                                              kemDecaps :=
                                                                                                oracleB.kemDecaps,
                                                                                              sigVerify :=
                                                                                                oracleB.sigVerify,
                                                                                              sigSign :=
                                                                                                oracleB.sigSign }
                                                                                            (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                                              (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                                dh p)
                                                                                              (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                p.braidSecret)
                                                                                              (Tacenta.UnitLifecycleT3.modelChunkOf
                                                                                                src c)
                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                ec)
                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                q.sparseRoot)
                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                q.sparseSend)
                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                q.sparseReceive)
                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                q.ratchetBytes)
                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                q.dhOut)
                                                                                              dSend
                                                                                              (oracleB.dhPublic dB) dB)
                                                                                            (Tacenta.UnitLifecycleT3.sliceOf
                                                                                              msg) =
                                                                                          {
                                                                                            session :=
                                                                                              Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                                                (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                                  dh p)
                                                                                                (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                  p.braidSecret)
                                                                                                (Tacenta.UnitLifecycleT3.modelChunkOf
                                                                                                  src c)
                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                  ec)
                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                  q.sparseRoot)
                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                  q.sparseSend)
                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                  q.sparseReceive)
                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                  q.ratchetBytes)
                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                  q.dhOut)
                                                                                                dSend
                                                                                                (oracleB.dhPublic dB)
                                                                                                dB,
                                                                                            result :=
                                                                                              Except.error
                                                                                                (Model.Lifecycle.Refusal.triple
                                                                                                  (Model.Lifecycle.TripleRefusal.classical
                                                                                                    Model.Lifecycle.RatchetRefusal.outOfOrder)),
                                                                                            oracle :=
                                                                                              { draws := restB2,
                                                                                                braidKem :=
                                                                                                  oracleB.braidKem,
                                                                                                dhPublic :=
                                                                                                  oracleB.dhPublic,
                                                                                                dhAgree :=
                                                                                                  oracleB.dhAgree,
                                                                                                identityValid :=
                                                                                                  oracleB.identityValid,
                                                                                                aeadSeal :=
                                                                                                  oracleB.aeadSeal,
                                                                                                aeadOpen :=
                                                                                                  oracleB.aeadOpen,
                                                                                                kemValid :=
                                                                                                  oracleB.kemValid,
                                                                                                kemEncaps :=
                                                                                                  oracleB.kemEncaps,
                                                                                                kemDecaps :=
                                                                                                  oracleB.kemDecaps,
                                                                                                sigVerify :=
                                                                                                  oracleB.sigVerify,
                                                                                                sigSign :=
                                                                                                  oracleB.sigSign } }) ∧
                                                                                      tacenta_session_unit.lifecycle.Session.decrypt
                                                                                            rcB crcB sB' msg rngB2 =
                                                                                          Aeneas.Std.Result.ok
                                                                                            (Aeneas.Std.core.result.Result.Err
                                                                                                (tacenta_session_unit.lifecycle.Error.Triple
                                                                                                  (tacenta_session_unit.tacenta_triple.TripleError.Classical
                                                                                                    tacenta_session_unit.tacenta_ratchet.RatchetError.OutOfOrder)),
                                                                                              sB', rngB3) ∧
                                                                                        traceB rngB3 = restB2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderRepeatedFrame.responder_first_frame_repeat_refused

/--
info: @Tacenta.UnitLifecycleResponderRepeatedFrame.initiator_first_send_responder_repeat_refused : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
  (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc oracle.braidKem →
    Tacenta.UnitLifecycleT3.TripleSendRefinementContracts →
      Tacenta.UnitLifecycleT1.AeadSealBounded →
        Tacenta.UnitLifecycleT1.DhCodecTotal →
          Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle →
            Tacenta.UnitLifecycleT3.DhCodecOf dh →
              Tacenta.UnitLifecycleT3.CodewordViewSendOf view →
                Tacenta.SessionUnitT3.ZeroizingRoundTrips80 →
                  Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Aeneas.Std.Array Aeneas.Std.U8 32#usize) →
                    Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
                        (Aeneas.Std.Array Aeneas.Std.U8 32#usize ×
                          Aeneas.Std.Array Aeneas.Std.U8 32#usize × Aeneas.Std.Array Aeneas.Std.U8 16#usize) →
                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
                        Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem →
                          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                            Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                              ∀ (rcE : tacenta_session_unit.rand_core_1.RngCore E)
                                (crcE : tacenta_session_unit.rand_core_1.CryptoRng E)
                                (ourA : tacenta_session_unit.lifecycle.Identity)
                                (bundleA : tacenta_session_unit.lifecycle.PublishedBundle)
                                (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                                (s : tacenta_session_unit.lifecycle.Session),
                                tacenta_session_unit.lifecycle.establish_initiator_for rcE crcE ourA bundleA expected
                                      rng0 =
                                    Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                                  ∀
                                    (q :
                                      Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcE crcE ourA
                                        bundleA),
                                    s = q.session →
                                      ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
                                        (↑plaintext).length + 65770 ≤ Aeneas.Std.Usize.max →
                                          ∀ (rng : R),
                                            trace rng = oracle.draws →
                                              ∀ (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
                                                trace rng = d1 :: d2 :: rest →
                                                  ∀ (bytes : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
                                                    (s' : tacenta_session_unit.lifecycle.Session) (rng' : R),
                                                    tacenta_session_unit.lifecycle.Session.encrypt rc crc s plaintext
                                                          rng =
                                                        Aeneas.Std.Result.ok
                                                          (Aeneas.Std.core.result.Result.Ok bytes, s', rng') →
                                                      ∀ (rcB : tacenta_session_unit.rand_core_1.RngCore F)
                                                        (crcB : tacenta_session_unit.rand_core_1.CryptoRng F)
                                                        (contracts :
                                                          Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
                                                        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                                                          Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                                                            Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                                                              Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                                                                Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                                                                  Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                                                                      @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                                                                    ∀ (traceB : F → List Model.Lifecycle.Key)
                                                                      (oracleB : Model.Lifecycle.Oracle),
                                                                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf
                                                                          rcB crcB dh traceB oracleB →
                                                                        Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                            oracleB.braidKem →
                                                                          ∀
                                                                            (ourB :
                                                                              tacenta_session_unit.lifecycle.Identity)
                                                                            (storeB :
                                                                              tacenta_session_unit.lifecycle.PrekeyStore),
                                                                            storeB.publish =
                                                                                Aeneas.Std.Result.ok bundleA →
                                                                              ourB.public =
                                                                                  Aeneas.Std.Result.ok
                                                                                    storeB.identity_public →
                                                                                Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                                    storeB →
                                                                                  Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                                      storeB bundleA.kem_prekey_id
                                                                                      q.kemCiphertext q.kemSecret →
                                                                                    ∀ (rngB : F),
                                                                                      traceB rngB = oracleB.draws →
                                                                                        ∀ (dB : Model.Lifecycle.Key)
                                                                                          (restB :
                                                                                            List Model.Lifecycle.Key),
                                                                                          traceB rngB = dB :: restB →
                                                                                            ∀
                                                                                              (ptB :
                                                                                                Aeneas.Std.alloc.vec.Vec
                                                                                                  Aeneas.Std.U8)
                                                                                              (sB' :
                                                                                                tacenta_session_unit.lifecycle.Session)
                                                                                              (storeB' :
                                                                                                tacenta_session_unit.lifecycle.PrekeyStore)
                                                                                              (rngB' : F),
                                                                                              tacenta_session_unit.lifecycle.establish_responder
                                                                                                    rcB crcB ourB storeB
                                                                                                    bytes.deref rngB =
                                                                                                  Aeneas.Std.Result.ok
                                                                                                    (Aeneas.Std.core.result.Result.Ok
                                                                                                        (sB', ptB),
                                                                                                      storeB', rngB') →
                                                                                                ∀ (rngB2 : F)
                                                                                                  (dB2 :
                                                                                                    Model.Lifecycle.Key)
                                                                                                  (restB2 :
                                                                                                    List
                                                                                                      Model.Lifecycle.Key),
                                                                                                  traceB rngB2 =
                                                                                                      dB2 :: restB2 →
                                                                                                    ∃ p ec dSend dk
                                                                                                      ekSeed ekVector mB
                                                                                                      rngB3,
                                                                                                      oracle.braidKem.keyGen
                                                                                                            (Model.Lifecycle.braidRandomness
                                                                                                              (d1 ++
                                                                                                                d2)) =
                                                                                                          some
                                                                                                            (dk, ekSeed,
                                                                                                              ekVector) ∧
                                                                                                        mB =
                                                                                                            Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                                                              (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                                                dh p)
                                                                                                              (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                p.braidSecret)
                                                                                                              {
                                                                                                                source :=
                                                                                                                  Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                    oracle.braidKem
                                                                                                                    (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                      q.auth)
                                                                                                                    ekSeed
                                                                                                                    ekVector,
                                                                                                                index :=
                                                                                                                  0 }
                                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                ec)
                                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                q.sparseRoot)
                                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                q.sparseSend)
                                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                q.sparseReceive)
                                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                q.ratchetBytes)
                                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                q.dhOut)
                                                                                                              dSend
                                                                                                              (oracleB.dhPublic
                                                                                                                dB)
                                                                                                              dB ∧
                                                                                                          Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                              dh
                                                                                                              oracleB.braidKem
                                                                                                              sB' mB ∧
                                                                                                            (∀
                                                                                                                (viewB :
                                                                                                                  Model.Lifecycle.CodewordView),
                                                                                                                Model.Lifecycle.decrypt
                                                                                                                    viewB
                                                                                                                    {
                                                                                                                      draws :=
                                                                                                                        dB2 ::
                                                                                                                          restB2,
                                                                                                                      braidKem :=
                                                                                                                        oracleB.braidKem,
                                                                                                                      dhPublic :=
                                                                                                                        oracleB.dhPublic,
                                                                                                                      dhAgree :=
                                                                                                                        oracleB.dhAgree,
                                                                                                                      identityValid :=
                                                                                                                        oracleB.identityValid,
                                                                                                                      aeadSeal :=
                                                                                                                        oracleB.aeadSeal,
                                                                                                                      aeadOpen :=
                                                                                                                        oracleB.aeadOpen,
                                                                                                                      kemValid :=
                                                                                                                        oracleB.kemValid,
                                                                                                                      kemEncaps :=
                                                                                                                        oracleB.kemEncaps,
                                                                                                                      kemDecaps :=
                                                                                                                        oracleB.kemDecaps,
                                                                                                                      sigVerify :=
                                                                                                                        oracleB.sigVerify,
                                                                                                                      sigSign :=
                                                                                                                        oracleB.sigSign }
                                                                                                                    mB
                                                                                                                    (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                      bytes.deref) =
                                                                                                                  {
                                                                                                                    session :=
                                                                                                                      mB,
                                                                                                                    result :=
                                                                                                                      Except.error
                                                                                                                        (Model.Lifecycle.Refusal.triple
                                                                                                                          (Model.Lifecycle.TripleRefusal.classical
                                                                                                                            Model.Lifecycle.RatchetRefusal.outOfOrder)),
                                                                                                                    oracle :=
                                                                                                                      {
                                                                                                                        draws :=
                                                                                                                          restB2,
                                                                                                                        braidKem :=
                                                                                                                          oracleB.braidKem,
                                                                                                                        dhPublic :=
                                                                                                                          oracleB.dhPublic,
                                                                                                                        dhAgree :=
                                                                                                                          oracleB.dhAgree,
                                                                                                                        identityValid :=
                                                                                                                          oracleB.identityValid,
                                                                                                                        aeadSeal :=
                                                                                                                          oracleB.aeadSeal,
                                                                                                                        aeadOpen :=
                                                                                                                          oracleB.aeadOpen,
                                                                                                                        kemValid :=
                                                                                                                          oracleB.kemValid,
                                                                                                                        kemEncaps :=
                                                                                                                          oracleB.kemEncaps,
                                                                                                                        kemDecaps :=
                                                                                                                          oracleB.kemDecaps,
                                                                                                                        sigVerify :=
                                                                                                                          oracleB.sigVerify,
                                                                                                                        sigSign :=
                                                                                                                          oracleB.sigSign } }) ∧
                                                                                                              tacenta_session_unit.lifecycle.Session.decrypt
                                                                                                                    rcB
                                                                                                                    crcB
                                                                                                                    sB'
                                                                                                                    bytes.deref
                                                                                                                    rngB2 =
                                                                                                                  Aeneas.Std.Result.ok
                                                                                                                    (Aeneas.Std.core.result.Result.Err
                                                                                                                        (tacenta_session_unit.lifecycle.Error.Triple
                                                                                                                          (tacenta_session_unit.tacenta_triple.TripleError.Classical
                                                                                                                            tacenta_session_unit.tacenta_ratchet.RatchetError.OutOfOrder)),
                                                                                                                      sB',
                                                                                                                      rngB3) ∧
                                                                                                                traceB
                                                                                                                    rngB3 =
                                                                                                                  restB2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderRepeatedFrame.initiator_first_send_responder_repeat_refused

/--
info: Tacenta.UnitLifecycleResponderRepeatedFrame.first_send_repeat_refused_reachable : ∀ (K : Model.Braid.Kem)
  (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    Nonempty
        (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
      Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc →
        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
            Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLaws K dh kem →
              Nonempty
                  (Tacenta.UnitSatisfiabilityJoint.ResponderAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
                    Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
                Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                  Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                    Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape
                        Tacenta.UnitSatisfiabilityJoint.Interp.real
                        tacenta_session_unit.tacenta_boundary.kem.KeyPair.public_key
                        @tacenta_session_unit.alloc.vec.Vec.is_empty →
                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K →
                        Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                          Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                            ∀ (ourA : tacenta_session_unit.lifecycle.Identity) (seed : List Aeneas.Std.U8),
                              seed.length = 64 →
                                K.keyGen
                                      (Model.Lifecycle.braidRandomness (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠
                                    none →
                                  ∃ oracle bundle q bytes s' rng' ourB storeB sB' ptB storeB' rngB' rngB3,
                                    oracle.braidKem = K ∧
                                      tacenta_session_unit.lifecycle.Session.encrypt
                                            Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc q.session
                                            Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed =
                                          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok bytes, s', rng') ∧
                                        storeB.publish = Aeneas.Std.Result.ok bundle ∧
                                          tacenta_session_unit.lifecycle.establish_responder
                                                Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourB storeB bytes.deref
                                                seed =
                                              Aeneas.Std.Result.ok
                                                (Aeneas.Std.core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
                                            tacenta_session_unit.lifecycle.Session.decrypt
                                                Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                Tacenta.UnitLifecycleIntegrationScreen.byteCrc sB' bytes.deref rngB' =
                                              Aeneas.Std.Result.ok
                                                (Aeneas.Std.core.result.Result.Err
                                                    (tacenta_session_unit.lifecycle.Error.Triple
                                                      (tacenta_session_unit.tacenta_triple.TripleError.Classical
                                                        tacenta_session_unit.tacenta_ratchet.RatchetError.OutOfOrder)),
                                                  sB', rngB3)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderRepeatedFrame.first_send_repeat_refused_reachable
