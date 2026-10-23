import Translation.UnitLifecycleInitiatorSecondSend
import Translation.UnitLifecycleReceivePreserve

/-!
# The initiator's second message: its second send on the run of the reply's receipt, under no condition at `s''`

`UnitLifecycleInitiatorSecondSend` states the initiator's second `Session::encrypt`, at the session `s''` its receipt of
the responder's reply returns and from the source `rngA'` that receipt left, on the run from the initiator's
establishment: the model's step there has one outcome, and the code-level part (the call returns that frame, takes no
draw and refines the step) is stated under the premises that `s''` passes `Session::invariant` and meets the four counter
ceilings `CounterHeadroom`, which that module does not derive.  `UnitLifecycleReceivePreserve` derives exactly those two
facts at `s''` on the same run (`initiator_receives_reply_successor`).  This module joins the two on one run, so the
code-level part holds with no condition at `s''`, and carries `Session::invariant` and the ceilings through the second
send to the session `s'''` it leaves.

## How

* `initiator_sends_second_message`: `initiator_second_send_after_reply` gives the second send on the run, its code-level
  part as an implication from the invariant and the ceilings at its `s''`; `initiator_receives_reply_successor`, under the
  same hypotheses, gives the invariant, `CounterHeadroom` and room for every `j` with `j + 2 < u32::MAX` further operations
  (`CounterRoom`) at its `s''`.  The two theorems name their sessions separately; they are one session because the
  responder's `encrypt` of the reply and the initiator's `decrypt` of it are functions of their inputs, and both theorems
  state the same two calls on the same inputs (the reply's bytes are equal, so the session and the source the receipt
  returns are).  The implication's premises are then discharged.  `encrypt_keeps_invariant_no_draw`
  (`UnitLifecycleSendPreserve`) applies at `s''`: its agreement is at `KeysSampled`, whose send takes no draw; its
  relation after the call is the second send's relation to the model's step, read through that step's one outcome; and
  its budget is the receipt's room for `j + 1`, so `s'''` passes `Session::invariant`, meets `CounterHeadroom` and has room
  for every `j` with `j + 3 < u32::MAX`.
* `SecondMessageRun`, `first_send_second_message_reachable`: at the real constants, under the laws of
  `first_send_reply_receipt_reachable` (all assumed), one run from `publish` through the first send, the responder's
  receipt and reply and the initiator's receipt of the reply to the initiator's second send, on which every hypothesis of
  the headline holds: the run of `reply_receipt_reach_run`, rebuilt here with the responder's source chosen by
  `DhPublicNotConstant` (as `first_send_reply_receipt_reachable` chooses it), for every reply plaintext and every second
  plaintext of at most 4096 bytes.  On that run `s''` passes `Session::invariant` and meets the ceilings, the second
  `encrypt` returns `Ok` and leaves the source as it was, and `s'''` passes `Session::invariant` and meets the ceilings.

## The statements

* `initiator_sends_second_message`: under the hypotheses of `initiator_receives_reply` and the bound on the second
  plaintext `ptS` (`102 + (ptS.length + 48) ≤ Usize.max`) and no other, the conjuncts of
  `initiator_second_send_after_reply` hold (the two agreements, the reply's `encrypt`, the initiator's `decrypt` of it
  returning `Ok ptA` with the bytes of `ptR`, `s''` and `rngA'`, the trace after the draw, no pending initial message at
  `s''`, the relation of `s''` and the model's one outcome for the second send) except that the model agreement's no-draw
  conjunct is not restated, and in place of that theorem's implication: `s''` passes `Session::invariant` and meets
  `CounterHeadroom`; the public `encrypt` of `ptS` at `s''` from `rngA'` returns `Ok bytes2` and `s'''` and leaves `rngA'`
  as it was (no draw); `s'''` is `s''` with only the Triple Ratchet and the agreement written and no pending initial
  message; `bytes2` is `secondFrame` (agreement type `hdr`, the header chunk at index 1, no initial wrapper) sealed under
  `secondKey` with the initiator's associated data; `s'''` refines the model session after that step (the Triple
  `initiatorAfterSecond`, the header encoder at position 2); and `s'''` passes `Session::invariant`, meets
  `CounterHeadroom` and has room for every `j` with `j + 3 < u32::MAX` further operations.
* `first_send_second_message_reachable`: under the laws of `first_send_reply_receipt_reachable` and no other, for every
  initiator identity, every 64-byte seed at whose bytes the model's key generation answers, every 32 further bytes, and
  every reply plaintext `ptR` and second plaintext `ptS` of at most 4096 bytes, `SecondMessageRun` holds: there is a run
  (an oracle whose KEM is the given one, a bundle a prekey store publishes, a successful establishment, the first send of
  the empty plaintext from the seed followed by the 32 bytes, `establish_responder` on its bytes, the responder's `encrypt`
  of `ptR`, the initiator's `decrypt` of the reply returning `ptR`) on which `s''` passes `Session::invariant` and meets
  `CounterHeadroom`, the initiator's `encrypt` of `ptS` at `s''` from `rngA'` returns `Ok bytes2` and `s'''` and leaves
  `rngA'`, and `s'''` passes `Session::invariant` and meets `CounterHeadroom`.

## Laws and premises

No new law and no new per-run premise.  The headline takes exactly the hypotheses of `initiator_second_send_after_reply`:
those of `initiator_receives_reply` (which `initiator_receives_reply_successor` also takes) and the bound on `ptS`, which
holds of every plaintext of at most `2^32 - 151` bytes on a 32-bit target.  The record the preservation step adds,
`KemCloneAgrees`, is a field of the initiator's Braid send record `BraidSendRefinementContracts`, already a hypothesis.
`CounterRoom` is internal: the headline concludes `CounterHeadroom` at `s''` and `s'''` and states the budget it computes.
No premise names a width, so each result holds on 32- and 64-bit targets.  The reach takes the laws of
`first_send_reply_receipt_reachable`, `DhPublicNotConstant` included, and no other.

## Trust

Every result here rests on the kernel and opaque constants only, with no compiler-trust axiom (pins below); the headline
applies the encrypt and decrypt refinements through `initiator_second_send_after_reply` and
`initiator_receives_reply_successor`, whose nine `native_decide` constants are kernel proofs since 2026-10-21.  The
headline's statement pin prints the whole statement: the module sets `pp.deepTerms true` and `pp.proofs.withType true`
before its pins, without which Lean cut the pin off with `⋯` after the binder `trace rng' = dA :: restA`.  The reach's
statement pin and the `#print` pin of `SecondMessageRun`, the conclusion it names, are printed in full too.  A printed
pin is still not the whole elaborated statement (instance arguments, coercion functions, implicit arguments and the
binder types of `∃` and `fun` are not printed), so that the pinned statement is the right one is decided by reading.

## Non-vacuity

No law is added, so `reply_receipt_laws_model` still puts every law the reach takes in one toy interpretation,
`InterpO.modelReply`.  `first_send_second_message_reachable` exhibits, at the real constants under those laws, a run at
which every hypothesis of the headline holds and its conclusion's code-level part applies: `Session::invariant` and the
ceilings at `s''`, the second send returning `Ok`, and `Session::invariant` and the ceilings at `s'''`.  The laws are
assumed at the real constants, not shown of them.

## What it does not show

* The responder's receipt of this second message (shown, on the same run, in `UnitLifecycleResponderSecondReceipt`), a
  second reply and its receipt, the header's third chunk, the responder's first sampling send and every later step: one
  further send by the initiator, not a second exchange.
* That the budget is exact at `s'''`: room for every `j` with `j + 3 < u32::MAX` is what the composition derives (the
  preservation step charges a unit for the send although the clock does not move); more room is not claimed.
* A refusal `encrypt` can reach: none occurs at this state; the refusals reachable elsewhere in a session (the terminal
  guard, `AgreementFailed`, `ChainExhausted`, `NoSendingChain`) are not covered.
* That the code's key pair after the call equals the one before: the send clones it and the relation holds through
  `KemCloneAgrees`; code-level equality is not checked.
* The reply's bytes as `replyFrame` and the frame equation of `s''` against `s'`: conjuncts of `initiator_receives_reply`
  that the statement does not carry (they follow by applying it again).
* A restored copy of `s''` or `s'''`; the one-time path in a run (the reach takes the last-resort path only); that the
  related model sessions hold only bytes the parties received; that `hfreshB` holds under an honest random source.
* That the real primitives meet the boundary records or the laws the run rests on (`KemCloneAgrees`, `AeadRoundTrip`,
  `DhAgreeContributory`, `DhAgreeSymmetric`, `DhPublicValid`, `DhPublicNotConstant`), that ML-KEM decapsulation agrees on a
  run (`FirstKemAgrees`), or `PrekeyIdsDistinct` from `PrekeyStore::invariant`; the model's own `establishResponder`
  equality.
* That `Session::invariant` says a session is reachable: it is a predicate on fields.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit

namespace Tacenta.UnitLifecycleInitiatorSecondMessage

open Tacenta.UnitLifecycleT3 (DhView DhCodecOf KemView arrayOf vecOf sliceOf SessionRefines OracleOf
  BraidSendRefinementContracts TripleSendRefinementContracts CodewordViewSendOf ZeroizingRoundTrips)
open Tacenta.UnitLifecycleDecryptRunBounds (CounterHeadroom)
open Tacenta.UnitLifecycleSendPreserve (CounterRoom counterRoom_zero encrypt_keeps_invariant_no_draw)
open Tacenta.UnitLifecycleInitiatorSecondSend (initiatorAfterSecond secondFrame secondKey
  initiator_second_send_after_reply)
open Tacenta.UnitLifecycleReceivePreserve (initiator_receives_reply_successor)
open Tacenta.UnitLifecycleResponderReplyReceipt (replyReceiptSession)
open Tacenta.UnitLifecycleResponderFirstReceipt (headerSource DhAgreeContributory AeadRoundTrip)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid establishedModelOf)

/-- **The initiator's second message, on the run of the reply's receipt, with no condition at `s''`.**  Under the
hypotheses of `initiator_receives_reply` (the run from the initiator's establishment through its first send, the
responder's receipt and reply, and the initiator's receipt of the reply, with the per-run premises that the initiator's
source after its first send holds a draw `dA` and that the responder's fresh ratchet key is not the peer key the
initiator holds) and the bound on the second plaintext `ptS`, and no other: the conjuncts of
`initiator_second_send_after_reply` other than its no-draw conjunct and its implication (the first send's key
generation, the two agreements, the reply's `encrypt`, the initiator's `decrypt` of it returning `Ok ptA` (the bytes of
`ptR`), `s''` and `rngA'`, the trace after the draw, no pending initial message at `s''`, the relation of `s''`, and the
model's one outcome for the second send), and

* `s''` passes `Session::invariant` and meets `CounterHeadroom` (from `initiator_receives_reply_successor`, on the same
  calls);
* the public `Session::encrypt` of `ptS` at `s''` from `rngA'` returns `Ok bytes2` and `s'''` and leaves `rngA'` as it was;
  `s'''` is `s''` with only the Triple Ratchet and the agreement written, no pending initial message; `bytes2` is
  `secondFrame` (the header chunk at index 1, sealed under `secondKey`); and `s'''` refines the model session after that
  step;
* `s'''` passes `Session::invariant`, meets `CounterHeadroom` and has room for every `j` with `j + 3 < u32::MAX` further
  operations (`encrypt_keeps_invariant_no_draw` at `KeysSampled`, whose send takes no draw).

The two sessions named `s''` by the two theorems it composes are one: both state the responder's `encrypt` of the reply
and the initiator's `decrypt` of its bytes on the same inputs, and those are functions.  No compiler-trust axiom (the
pin): the nine `native_decide` constants of the refinements it applies are kernel proofs since 2026-10-21. -/
theorem initiator_sends_second_message [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (ptS : Slice Std.U8) (hroomS : 102 + (ptS.val.length + 48) ≤ Usize.max)
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
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
    (contractsA : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (agreementsA : DecryptRatchetAgreements oracle.braidKem)
    (dA : Model.Lifecycle.Key) (restA : List Model.Lifecycle.Key) (hdrawA : trace rng' = dA :: restA)
    (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (traceB : F → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : OracleOf rcB crcB dh kem traceB oracleB)
    (braidB : BraidSendRefinementContracts rcB oracleB.braidKem)
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
    (ptR : Slice Std.U8) (hroomR : 102 + (ptR.val.length + 48) ≤ Usize.max) (rngR : F)
    (hfreshB : oracleB.dhPublic dB ≠ arrayOf q.peerRatchetBytes) :
    ∃ (dSend x : Model.Lifecycle.Key) (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session)
      (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' : R) (dk ekSeed ekVector : Model.Braid.Bytes)
      (bytes2 : alloc.vec.Vec Std.U8) (s''' : lifecycle.Session),
      oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector) ∧
      oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
      oracle.dhAgree dA (oracleB.dhPublic dB) = some x ∧
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' =
        ok (core.result.Result.Ok ptA, s'', rngA') ∧
      ptA.val = ptR.val ∧ trace rngA' = restA ∧ s''.pending_initial = none ∧
      lifecycle.Session.invariant s'' = ok true ∧ CounterHeadroom s'' ∧
      SessionRefines dh oracle.braidKem s''
        (replyReceiptSession
          (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
          (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
          (oracleB.dhPublic dB) (oracle.dhPublic dA) dA) ∧
      Model.Lifecycle.encrypt view { oracle with draws := restA }
        (replyReceiptSession
          (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
          (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
          (oracleB.dhPublic dB) (oracle.dhPublic dA) dA) (sliceOf ptS) =
        { session :=
            { replyReceiptSession
                (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
                (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
                (oracleB.dhPublic dB) (oracle.dhPublic dA) dA with
              triple := initiatorAfterSecond (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend)
                (arrayOf q.sparseReceive) dSend x (oracleB.dhPublic dB) (oracle.dhPublic dA)
              braid := .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
                ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 2⟩ }
          result := .ok (secondFrame view oracle (vecOf q.identityAd)
            (.keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
              ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩)
            (oracle.dhPublic dA) (secondKey (arrayOf q.rootKey) (arrayOf q.sparseSend) dSend x)
            ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩
            (sliceOf ptS))
          oracle := { oracle with draws := restA } } ∧
      lifecycle.Session.encrypt rc crc s'' ptS rngA' = ok (core.result.Result.Ok bytes2, s''', rngA') ∧
      s''' = { s'' with triple := s'''.triple, braid := s'''.braid } ∧ s'''.pending_initial = none ∧
      vecOf bytes2 = secondFrame view oracle (vecOf q.identityAd)
        (.keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
          ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩)
        (oracle.dhPublic dA) (secondKey (arrayOf q.rootKey) (arrayOf q.sparseSend) dSend x)
        ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩
        (sliceOf ptS) ∧
      SessionRefines dh oracle.braidKem s'''
        { replyReceiptSession
            (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
            (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
            (oracleB.dhPublic dB) (oracle.dhPublic dA) dA with
          triple := initiatorAfterSecond (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend)
            (arrayOf q.sparseReceive) dSend x (oracleB.dhPublic dB) (oracle.dhPublic dA)
          braid := .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
            ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 2⟩ } ∧
      lifecycle.Session.invariant s''' = ok true ∧ CounterHeadroom s''' ∧
      (∀ j, j + 3 < Std.U32.max → CounterRoom s''' j) := by
  -- the second send on the run of the reply's receipt, its code-level part under the invariant and the ceilings
  obtain ⟨dSend, x, bytesR, sB'', ptA, s'', rngA', dk, ekSeed, ekVector, hkg, hagreeB, hx, hcallR, hcallA, hpt,
    hdr, hpend, hsess, hdraw, hM, himp⟩ :=
    initiator_second_send_after_reply rc crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec
      codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h q hq
      plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall contractsA agreementsA dA restA hdrawA rcB
      crcB contracts hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish
      hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR rngR hfreshB
      ptS hroomS
  -- the invariant, the ceilings and the budget at the session the same receipt returns, on the same run
  obtain ⟨-, -, bytesR₁, sB''₁, ptA₁, s''₁, rngA'₁, hcallR₁, hcallA₁, -, hinv₁, -, hroom₁, -⟩ :=
    initiator_receives_reply_successor rc crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec
      codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h q hq
      plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall contractsA agreementsA dA restA hdrawA rcB
      crcB contracts hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish
      hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR rngR hfreshB
  -- one session: the responder's `encrypt` and the initiator's `decrypt` are functions of their inputs
  rw [hcallR] at hcallR₁
  simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hcallR₁
  obtain ⟨rfl, -⟩ := hcallR₁
  rw [hcallA] at hcallA₁
  simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hcallA₁
  obtain ⟨-, rfl, rfl⟩ := hcallA₁
  -- the second send, its code-level part now unconditional
  have hc : CounterHeadroom s'' := (counterRoom_zero s'').mp (hroom₁ 0 (by simp [Std.U32.max_eq]))
  obtain ⟨bytes2, s''', hcallS, hframe, hpend3, hbytes, hrel3⟩ := himp hinv₁ hc
  -- the send keeps the invariant and spends one unit of the budget: the agreement at `KeysSampled` draws nothing
  have key : ∀ j, j + 3 < Std.U32.max → lifecycle.Session.invariant s''' = ok true ∧ CounterRoom s''' j :=
    fun j hj => encrypt_keeps_invariant_no_draw braid.kemClone rc crc dh oracle.braidKem view
      { oracle with draws := restA } s'' _ j hinv₁ (hroom₁ (j + 1) (by omega)) hsess hdraw ptS (sliceOf ptS)
      rngA' bytes2 s''' rngA' hcallS (by rw [hM]; exact hrel3)
  have h0 : (0 : Nat) + 3 < Std.U32.max := by simp [Std.U32.max_eq]
  exact ⟨dSend, x, bytesR, sB'', ptA, s'', rngA', dk, ekSeed, ekVector, bytes2, s''', hkg, hagreeB, hx, hcallR,
    hcallA, hpt, hdr, hpend, hinv₁, hc, hsess, hM, hcallS, hframe, hpend3, hbytes, hrel3, (key 0 h0).1,
    (counterRoom_zero s''').mp (key 0 h0).2, fun j hj => (key j hj).2⟩

/-! ## The reach: one run, from `publish` to the initiator's second send -/

section Reach

open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real InitiatorAxiom ResponderAxiom)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace chunks32)
open Tacenta.UnitLifecycleResponderFirstFrame (FirstFrameSuccessShape PoolEntry reachStore reachBundle
  publish_reachStore reachStore_distinct reach_establishment heldKemPair zPool)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf)
open Tacenta.UnitLifecycleResponderReply (oracleOf_with_draws)
open Tacenta.UnitLifecycleResponderReplyReceipt (DhPublicNotConstant dhPublicNotConstant_is byteTrace_one
  byteTrace_seed_extra two_draws_of_seed_extra)
open Tacenta.UnitLifecycleEstablishedEncrypt (EstablishedEncryptHypotheses EncryptExtraLaws emptyPlaintext)

/-- The run the reach exhibits, named so that its pin prints it whole: at an oracle whose KEM is `K`, a bundle a prekey
store publishes and the initiator's secret parts of an establishment against it, the first send of the empty plaintext
from `seed ++ extra`, `establish_responder` on its bytes from a responder source `seedB`, the responder's `encrypt` of
`ptR`, the initiator's `decrypt` of the reply returning `ptR`, the session `s''` it returns passing `Session::invariant`
and meeting `CounterHeadroom`, the initiator's `encrypt` of `ptS` at `s''` from the source the receipt left returning
`Ok` and leaving that source, and the session `s'''` it returns passing `Session::invariant` and meeting
`CounterHeadroom`. -/
def SecondMessageRun (K : Model.Braid.Kem) (ourA : lifecycle.Identity) (seed extra : List Std.U8)
    (ptR ptS : Slice Std.U8) : Prop :=
  ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle)
    (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (bytes : alloc.vec.Vec Std.U8)
    (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity)
    (storeB : lifecycle.PrekeyStore) (seedB : List Std.U8) (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8)
    (storeB' : lifecycle.PrekeyStore) (rngB' : List Std.U8) (bytesR : alloc.vec.Vec Std.U8)
    (sB'' : lifecycle.Session) (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' : List Std.U8)
    (bytes2 : alloc.vec.Vec Std.U8) (s''' : lifecycle.Session),
    oracle.braidKem = K ∧
    lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext (seed ++ extra) =
      ok (core.result.Result.Ok bytes, s', rng') ∧
    lifecycle.PrekeyStore.publish storeB = ok bundle ∧
    lifecycle.establish_responder byteRng byteCrc ourB storeB (alloc.vec.Vec.deref bytes) seedB =
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
    lifecycle.Session.encrypt byteRng byteCrc sB' ptR rngB' =
      ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
    lifecycle.Session.decrypt byteRng byteCrc s' (alloc.vec.Vec.deref bytesR) rng' =
      ok (core.result.Result.Ok ptA, s'', rngA') ∧
    ptA.val = ptR.val ∧
    lifecycle.Session.invariant s'' = ok true ∧ CounterHeadroom s'' ∧
    lifecycle.Session.encrypt byteRng byteCrc s'' ptS rngA' = ok (core.result.Result.Ok bytes2, s''', rngA') ∧
    lifecycle.Session.invariant s''' = ok true ∧ CounterHeadroom s'''

/-- **The reach of the initiator's second message**: at the real constants, under the laws of
`first_send_reply_receipt_reachable` (all assumed, `DhPublicNotConstant` included) and no other, for every initiator
identity, every 64-byte seed at whose bytes the model's key generation answers, every 32 further bytes, every reply
plaintext `ptR` and every second plaintext `ptS` of at most 4096 bytes, `SecondMessageRun` holds.  The run is
`reply_receipt_reach_run`'s, rebuilt here with the responder's source chosen by `DhPublicNotConstant` so that its fresh
public key is not the signed prekey's, and `initiator_sends_second_message` is applied to it: every hypothesis of the
headline holds on it.  Last-resort path only.  No compiler-trust axiom (the pin). -/
theorem first_send_second_message_reachable (K : Model.Braid.Kem) (dh : DhView)
    (kem : Tacenta.UnitLifecycleT3.KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (X : EncryptExtraLaws K dh kem) (RA : Nonempty (ResponderAxiom Interp.real byteRng))
    (hsym : DhAgreeSymmetric) (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (FS : FirstFrameSuccessShape Interp.real tacenta_boundary.kem.KeyPair.public_key
      @alloc.vec.Vec.is_empty)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K)
    (hcon : DhAgreeContributory) (haead : AeadRoundTrip) (hnc : DhPublicNotConstant)
    (ourA : lifecycle.Identity) (seed : List Std.U8) (hseed : seed.length = 64)
    (extra : List Std.U8) (hextra : extra.length = 32)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none)
    (ptR : Slice Std.U8) (hptR : ptR.val.length ≤ 4096) (ptS : Slice Std.U8) (hptS : ptS.val.length ≤ 4096) :
    SecondMessageRun K ourA seed extra ptR ptS := by
  unfold SecondMessageRun
  -- the run's keys and KEM pair
  obtain ⟨sb, kB, pkb, a, hkB, hpkb, ha, hcan, hprime, heq, hsig, hag⟩ := FS.key
  obtain ⟨kp, kemPk, stream, ct, ss, rest, hkp, hlen, henc, hdec⟩ := FS.kem
  obtain ⟨z, hz⟩ := FS.pool
  have hkB' : tacenta_boundary.dh.PrivateKey.from_bytes sb = ok kB := hkB
  have hpkb' : tacenta_boundary.dh.PrivateKey.public_key kB = ok pkb := hpkb
  have ha' : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a := ha
  have hprime' : tacenta_boundary.dh.is_prime_order_public pkb = ok true := hprime
  have heq' : tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq pkb pkb =
      ok true := heq
  have hsig' : ∀ m, ∃ sig, tacenta_boundary.xeddsa.verify pkb m sig = ok (core.result.Result.Ok ()) := hsig
  have hag' : ∀ k, ∃ x, tacenta_boundary.dh.PrivateKey.agree k pkb = ok (some x) := hag
  have henc' : tacenta_boundary.kem.encapsulate byteRng byteCrc (alloc.vec.Vec.deref kemPk) stream =
      ok (core.result.Result.Ok (ct, ss), rest) := henc
  have hdec' : tacenta_boundary.kem.decapsulate kp (alloc.vec.Vec.deref ct) = ok (core.result.Result.Ok ss) :=
    hdec
  have hz' : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref zPool z = ok (alloc.vec.Vec.new PoolEntry) := hz
  -- the contracts
  obtain ⟨c⟩ := Tacenta.UnitSatisfiabilityRecords.initiator_contracts_of_axiom_base byteRng A
  obtain ⟨contracts⟩ := Tacenta.UnitSatisfiabilityRecords.responder_contracts_of_axiom_base byteRng RA L.laws
  have hdh := c.dhCodec
  -- the bundle's signatures
  obtain ⟨v, hv, -⟩ := Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.encode_ec_spec hdh pkb)
  obtain ⟨sig1, hs1⟩ := hsig' (alloc.vec.Vec.deref v)
  obtain ⟨v1, hv1, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.encode_kem_no_panic (alloc.vec.Vec.deref kemPk) hlen)
  obtain ⟨sig2, hs2⟩ := hsig' (alloc.vec.Vec.deref v1)
  have hverify : verify_bundle (reachBundle pkb sig1 sig2 kemPk).bundle = ok (core.result.Result.Ok ()) :=
    Tacenta.UnitLifecycleEstablishInitiatorShape.verify_successBundle pkb a ha' hcan hprime' sig1 sig2 kemPk
      v v1 hv hs1 hv1 hs2
  -- the establishment
  obtain ⟨q, rng1, hqct, hqss, h⟩ := reach_establishment c ourA pkb a ha' hcan heq' sig1 sig2 kemPk hverify
    hag' stream rest ct ss henc'
  -- the encrypt record at that establishment, from the seed followed by the 32 bytes
  have hlen96 : 64 ≤ (seed ++ extra).length := by simp [hseed]
  obtain ⟨oracle, bundle0, s0, rng10, hK, hdraws0, H0⟩ :=
    Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_hypotheses_jointly_satisfiable K dh kem L A S
      hpub hct X ourA (seed ++ extra) hlen96
  have H : EstablishedEncryptHypotheses byteRng byteCrc byteTrace dh kem
      Tacenta.UnitLifecycleRepair.witnessView oracle byteRng byteCrc ourA (reachBundle pkb sig1 sig2 kemPk)
      (reachBundle pkb sig1 sig2 kemPk).bundle.identity_key (List.replicate 32 0#u8 ++ stream) rng1 q.session
      emptyPlaintext (seed ++ extra) :=
    { braid := H0.braid, triple := H0.triple, derivedKeys := H0.derivedKeys, aead := H0.aead,
      dhCodec := H0.dhCodec, oracleOf := H0.oracleOf, codec := H0.codec, codewordView := H0.codewordView,
      zeroizing80 := H0.zeroizing80, zeroizing32 := H0.zeroizing32, zeroizingKeys := H0.zeroizingKeys,
      keyGen := H0.keyGen, kemCiphertextLen := H0.kemCiphertextLen,
      kemCiphertextBound := H0.kemCiphertextBound, established := h, room := H0.room,
      trace_eq := H0.trace_eq, draws := H0.draws }
  obtain ⟨inst⟩ := H.derivedKeys
  subst hK
  have htr := byteTrace_seed_extra seed extra hseed hextra
  -- the first send's success, and the source it leaves
  obtain ⟨output, hcall, hrest, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes
    byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead
    H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen
    H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session H.established
    emptyPlaintext H.room (seed ++ extra) H.trace_eq _ _ _ htr
  rw [two_draws_of_seed_extra seed extra hseed] at hcases
  obtain ⟨res, s', rng'⟩ := output
  rcases hcases with ⟨hnone, -⟩ | ⟨dk, ekSeed, ekVector, -, bytes, hres, -⟩
  · exact absurd hnone hkg
  simp only at hres hrest
  subst hres
  -- the responder's side
  let ourB : lifecycle.Identity := { secret := sb }
  have hidentity : lifecycle.Identity.public ourB = ok pkb := by
    show (do let pk ← tacenta_boundary.dh.PrivateKey.from_bytes sb; tacenta_boundary.dh.PrivateKey.public_key pk)
      = ok pkb
    rw [hkB']; exact hpkb'
  let storeB := reachStore pkb sb sig1 sig2 z kp
  have hpublish := publish_reachStore pkb sb kB hkB' hpkb' sig1 sig2 z hz' FS.empty kp kemPk hkp
  have hdistinct := reachStore_distinct pkb sb sig1 sig2 z hz' kp
  have hkem : FirstKemAgrees storeB (reachBundle pkb sig1 sig2 kemPk).kem_prekey_id q.kemCiphertext
      q.kemSecret := by
    refine ⟨kp, by simp [heldKemPair, storeB, reachStore, reachBundle], ?_⟩
    rw [hqct, hqss]; exact hdec'
  have hhead : Tacenta.UnitLifecycleT1.EstablishResponderHeadroom storeB :=
    ⟨by simp [storeB, reachStore]; exact Tacenta.UnitSatisfiabilityBraidAgreements.usize_max_ge 1 (by norm_num)⟩
  obtain ⟨oracle0, bundle1, s1, rng11, hK0, H1⟩ :=
    Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable
      oracle.braidKem dh L A S hpub hct ourA
  have ag : DecryptRatchetAgreements oracle.braidKem :=
    hK0 ▸ (H1 Tacenta.UnitLifecycleRepair.witnessView).agreements
  have hpeer : q.peerRatchetBytes = a := by
    have hp := q.hPeerRatchetBytes
    simp only [reachBundle] at hp
    rw [ha'] at hp
    cases hp
    rfl
  -- the oracle's public key of 32 bytes is the bytes of the boundary's public key of them
  have hpubOf : ∀ (sb' : Array U8 32#usize) (k : tacenta_boundary.dh.PrivateKey)
      (pk : tacenta_boundary.dh.PublicKeyBytes) (b : Array U8 32#usize),
      tacenta_boundary.dh.PrivateKey.from_bytes sb' = ok k →
      tacenta_boundary.dh.PrivateKey.public_key k = ok pk → tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok b →
      oracle.dhPublic (arrayOf sb') = arrayOf b := by
    intro sb' k pk b hk hpk hb
    obtain ⟨k', hk', hkv⟩ := H.codec.privateFromBytes sb'
    rw [hk] at hk'; cases hk'
    obtain ⟨pk', hpk', hpkv⟩ := H.oracleOf.dhPublic k
    rw [hpk] at hpk'; cases hpk'
    obtain ⟨b', hb', hbv⟩ := H.codec.asBytes pk
    rw [hb] at hb'; cases hb'
    rw [← hkv, ← hpkv, hbv]
  -- the initiator's draw after its first send: the 32 bytes after the seed
  have hdrawA : byteTrace rng' = extra.map Tacenta.SessionUnitBraidT3.u8 :: [] := hrest
  have hu : 4294967295 ≤ Usize.max :=
    Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  -- the responder's 32-byte source: a key whose public key is not the peer key the initiator holds
  obtain ⟨sbB, kF, pkF, bF, hkF, hpkF, hbF, hne⟩ := (dhPublicNotConstant_is.mp hnc) q.peerRatchetBytes
  have hseedB : sbB.val.length = 32 := by simp
  set seedB := sbB.val with hseedBdef
  -- the responder's oracle: the shared oracle with the responder source's draw
  let oracleB : Model.Lifecycle.Oracle := { oracle with draws := byteTrace seedB }
  have oracleOfB : Tacenta.UnitLifecycleT3.OracleOf byteRng byteCrc dh kem byteTrace oracleB :=
    oracleOf_with_draws H.oracleOf _
  have hdrB : byteTrace seedB = seedB.map Tacenta.SessionUnitBraidT3.u8 :: [] := byteTrace_one seedB hseedB
  obtain ⟨-, hdisj⟩ := Tacenta.UnitLifecycleResponderFirstReceipt.initiator_first_send_responder_receives byteRng
    byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec
    H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes
    H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session h q rfl emptyPlaintext H.room
    (seed ++ extra) H.trace_eq _ _ _ htr bytes s' rng' hcall byteRng byteCrc contracts hpub hsym hcon haead hrt
    L.optionEq byteTrace oracleB (DecryptOracleOf.of_oracleOf oracleOfB) ag ourB storeB hpublish hidentity
    hdistinct hkem hhead seedB rfl _ [] hdrB
  rcases hdisj with ⟨-, e, hrefuse, -⟩ |
    ⟨p, ec, dSend, dk', ekSeed', ekVector', ptB, sB', storeB', rngB', -, -, -, -, -, -, -, -, -, -, hcallB, -⟩
  · exfalso
    rcases hrefuse with ⟨-, hleg⟩ | ⟨-, fp, -, x, hx, -⟩ | ⟨-, -, hne', -⟩
    · simp [storeB, reachStore] at hleg
    · simp [storeB, reachStore] at hx
    · exact hne' (by simp [storeB, reachStore])
  -- the fresh-key premise, on this run
  have hfresh : oracleB.dhPublic (seedB.map Tacenta.SessionUnitBraidT3.u8) ≠ arrayOf q.peerRatchetBytes := by
    show oracle.dhPublic (seedB.map Tacenta.SessionUnitBraidT3.u8) ≠ arrayOf q.peerRatchetBytes
    rw [show seedB.map Tacenta.SessionUnitBraidT3.u8 = arrayOf sbB from rfl, hpubOf sbB kF pkF bF hkF hpkF hbF]
    intro hab
    exact hne (Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes hab)
  -- the headline on this run
  obtain ⟨-, -, bytesR, sB'', ptA, s'', rngA', -, -, -, bytes2, s''', -, -, -, hcallR, hcallA, hpt, -, -, hinv2, hc2,
    -, -, hcallS, -, -, -, -, hinv3, hc3, -⟩ :=
    initiator_sends_second_message ptS (by omega) byteRng byteCrc byteTrace dh kem
      Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec
      H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes H.kemCiphertextLen
      H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session H.established q rfl emptyPlaintext H.room
      (seed ++ extra) H.trace_eq _ _ _ htr bytes s' rng' hcall contracts.decrypt ag _ [] hdrawA byteRng byteCrc
      contracts hpub hsym hcon haead hrt L.optionEq byteTrace oracleB oracleOfB H.braid ag ourB storeB hpublish
      hidentity hdistinct hkem seedB rfl _ [] hdrB ptB sB' storeB' rngB' hcallB ptR (by omega) rngB' hfresh
  exact ⟨oracle, _, q, bytes, s', rng', ourB, storeB, seedB, sB', ptB, storeB', rngB', bytesR, sB'', ptA, s'',
    rngA', bytes2, s''', rfl, hcall, hpublish, hcallB, hcallR, hcallA, hpt, hinv2, hc2, hcallS, hinv3, hc3⟩

end Reach

end Tacenta.UnitLifecycleInitiatorSecondMessage

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleInitiatorSecondMessage.initiator_sends_second_message' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.is_empty,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_boundary.kem.KeyPair.public_key,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitiatorSecondMessage.initiator_sends_second_message

/--
info: 'Tacenta.UnitLifecycleInitiatorSecondMessage.first_send_second_message_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.is_empty,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_boundary.kem.KeyPair.public_key,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitiatorSecondMessage.first_send_second_message_reachable

set_option pp.deepTerms true
set_option pp.proofs.withType true

/--
info: @Tacenta.UnitLifecycleInitiatorSecondMessage.initiator_sends_second_message : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {R E F : Type} (ptS : Slice U8),
  102 + ((↑ptS).length + 48) ≤ Usize.max →
    ∀ (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
      (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
      (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
      Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc oracle.braidKem →
        Tacenta.UnitLifecycleT3.TripleSendRefinementContracts →
          Tacenta.UnitLifecycleT1.AeadSealBounded →
            Tacenta.UnitLifecycleT1.DhCodecTotal →
              Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle →
                Tacenta.UnitLifecycleT3.DhCodecOf dh →
                  Tacenta.UnitLifecycleT3.CodewordViewSendOf view →
                    Tacenta.SessionUnitT3.ZeroizingRoundTrips80 →
                      Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Std.Array U8 32#usize) →
                        Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
                            (Std.Array U8 32#usize × Std.Array U8 32#usize × Std.Array U8 16#usize) →
                          Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
                            Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem →
                              Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                                Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                                  ∀ (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
                                    (ourA : lifecycle.Identity) (bundleA : lifecycle.PublishedBundle)
                                    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                                    (s : lifecycle.Session),
                                    lifecycle.establish_initiator_for rcE crcE ourA bundleA expected rng0 =
                                        ok (core.result.Result.Ok s, rng1) →
                                      ∀
                                        (q :
                                          Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcE crcE ourA
                                            bundleA),
                                        s = q.session →
                                          ∀ (plaintext : Slice U8),
                                            (↑plaintext).length + 65770 ≤ Usize.max →
                                              ∀ (rng : R),
                                                trace rng = oracle.draws →
                                                  ∀ (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
                                                    trace rng = d1 :: d2 :: rest →
                                                      ∀ (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                                                        lifecycle.Session.encrypt rc crc s plaintext rng =
                                                            ok (core.result.Result.Ok bytes, s', rng') →
                                                          Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc →
                                                            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                oracle.braidKem →
                                                              ∀ (dA : Model.Lifecycle.Key)
                                                                (restA : List Model.Lifecycle.Key),
                                                                trace rng' = dA :: restA →
                                                                  ∀ (rcB : rand_core_1.RngCore F)
                                                                    (crcB : rand_core_1.CryptoRng F)
                                                                    (contracts :
                                                                      Tacenta.UnitLifecycleT1.EstablishResponderContracts
                                                                        rcB),
                                                                    Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                                                                      Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                                                                        Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                                                                          Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                                                                            Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                                                                              Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                                                                                  @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                                                                                ∀
                                                                                  (traceB :
                                                                                    F → List Model.Lifecycle.Key)
                                                                                  (oracleB : Model.Lifecycle.Oracle),
                                                                                  Tacenta.UnitLifecycleT3.OracleOf rcB
                                                                                      crcB dh kem traceB oracleB →
                                                                                    Tacenta.UnitLifecycleT3.BraidSendRefinementContracts
                                                                                        rcB oracleB.braidKem →
                                                                                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                                          oracleB.braidKem →
                                                                                        ∀ (ourB : lifecycle.Identity)
                                                                                          (storeB :
                                                                                            lifecycle.PrekeyStore),
                                                                                          storeB.publish = ok bundleA →
                                                                                            ourB.public =
                                                                                                ok
                                                                                                  storeB.identity_public →
                                                                                              Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                                                  storeB →
                                                                                                Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                                                    storeB
                                                                                                    bundleA.kem_prekey_id
                                                                                                    q.kemCiphertext
                                                                                                    q.kemSecret →
                                                                                                  ∀ (rngB : F),
                                                                                                    traceB rngB =
                                                                                                        oracleB.draws →
                                                                                                      ∀
                                                                                                        (dB :
                                                                                                          Model.Lifecycle.Key)
                                                                                                        (restB :
                                                                                                          List
                                                                                                            Model.Lifecycle.Key),
                                                                                                        traceB rngB =
                                                                                                            dB ::
                                                                                                              restB →
                                                                                                          ∀
                                                                                                            (ptB :
                                                                                                              alloc.vec.Vec
                                                                                                                U8)
                                                                                                            (sB' :
                                                                                                              lifecycle.Session)
                                                                                                            (storeB' :
                                                                                                              lifecycle.PrekeyStore)
                                                                                                            (rngB' : F),
                                                                                                            lifecycle.establish_responder
                                                                                                                  rcB
                                                                                                                  crcB
                                                                                                                  ourB
                                                                                                                  storeB
                                                                                                                  bytes.deref
                                                                                                                  rngB =
                                                                                                                ok
                                                                                                                  (core.result.Result.Ok
                                                                                                                      (sB',
                                                                                                                        ptB),
                                                                                                                    storeB',
                                                                                                                    rngB') →
                                                                                                              ∀
                                                                                                                (ptR :
                                                                                                                  Slice
                                                                                                                    U8),
                                                                                                                102 +
                                                                                                                      ((↑ptR).length +
                                                                                                                        48) ≤
                                                                                                                    Usize.max →
                                                                                                                  ∀
                                                                                                                    (rngR :
                                                                                                                      F),
                                                                                                                    oracleB.dhPublic
                                                                                                                          dB ≠
                                                                                                                        Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                          q.peerRatchetBytes →
                                                                                                                      ∃
                                                                                                                        dSend
                                                                                                                        x
                                                                                                                        bytesR
                                                                                                                        sB''
                                                                                                                        ptA
                                                                                                                        s''
                                                                                                                        rngA'
                                                                                                                        dk
                                                                                                                        ekSeed
                                                                                                                        ekVector
                                                                                                                        bytes2
                                                                                                                        s''',
                                                                                                                        oracle.braidKem.keyGen
                                                                                                                              (Model.Lifecycle.braidRandomness
                                                                                                                                (d1 ++
                                                                                                                                  d2)) =
                                                                                                                            some
                                                                                                                              (dk,
                                                                                                                                ekSeed,
                                                                                                                                ekVector) ∧
                                                                                                                          oracleB.dhAgree
                                                                                                                                dB
                                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                  q.ratchetBytes) =
                                                                                                                              some
                                                                                                                                dSend ∧
                                                                                                                            oracle.dhAgree
                                                                                                                                  dA
                                                                                                                                  (oracleB.dhPublic
                                                                                                                                    dB) =
                                                                                                                                some
                                                                                                                                  x ∧
                                                                                                                              lifecycle.Session.encrypt
                                                                                                                                    rcB
                                                                                                                                    crcB
                                                                                                                                    sB'
                                                                                                                                    ptR
                                                                                                                                    rngR =
                                                                                                                                  ok
                                                                                                                                    (core.result.Result.Ok
                                                                                                                                        bytesR,
                                                                                                                                      sB'',
                                                                                                                                      rngR) ∧
                                                                                                                                lifecycle.Session.decrypt
                                                                                                                                      rc
                                                                                                                                      crc
                                                                                                                                      s'
                                                                                                                                      bytesR.deref
                                                                                                                                      rng' =
                                                                                                                                    ok
                                                                                                                                      (core.result.Result.Ok
                                                                                                                                          ptA,
                                                                                                                                        s'',
                                                                                                                                        rngA') ∧
                                                                                                                                  ↑ptA =
                                                                                                                                      ↑ptR ∧
                                                                                                                                    trace
                                                                                                                                          rngA' =
                                                                                                                                        restA ∧
                                                                                                                                      s''.pending_initial =
                                                                                                                                          none ∧
                                                                                                                                        s''.invariant =
                                                                                                                                            ok
                                                                                                                                              true ∧
                                                                                                                                          Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                                                                              s'' ∧
                                                                                                                                            Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                                                                dh
                                                                                                                                                oracle.braidKem
                                                                                                                                                s''
                                                                                                                                                (Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession
                                                                                                                                                  (Model.Lifecycle.encrypt
                                                                                                                                                      view
                                                                                                                                                      oracle
                                                                                                                                                      (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                                                                                        dh
                                                                                                                                                        s)
                                                                                                                                                      (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                                        plaintext)).session
                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                    q.rootKey)
                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                    q.sparseRoot)
                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                    q.sparseSend)
                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                    q.sparseReceive)
                                                                                                                                                  dSend
                                                                                                                                                  x
                                                                                                                                                  (oracleB.dhPublic
                                                                                                                                                    dB)
                                                                                                                                                  (oracle.dhPublic
                                                                                                                                                    dA)
                                                                                                                                                  dA) ∧
                                                                                                                                              Model.Lifecycle.encrypt
                                                                                                                                                    view
                                                                                                                                                    {
                                                                                                                                                      draws :=
                                                                                                                                                        restA,
                                                                                                                                                      braidKem :=
                                                                                                                                                        oracle.braidKem,
                                                                                                                                                      dhPublic :=
                                                                                                                                                        oracle.dhPublic,
                                                                                                                                                      dhAgree :=
                                                                                                                                                        oracle.dhAgree,
                                                                                                                                                      identityValid :=
                                                                                                                                                        oracle.identityValid,
                                                                                                                                                      aeadSeal :=
                                                                                                                                                        oracle.aeadSeal,
                                                                                                                                                      aeadOpen :=
                                                                                                                                                        oracle.aeadOpen,
                                                                                                                                                      kemValid :=
                                                                                                                                                        oracle.kemValid,
                                                                                                                                                      kemEncaps :=
                                                                                                                                                        oracle.kemEncaps,
                                                                                                                                                      kemDecaps :=
                                                                                                                                                        oracle.kemDecaps,
                                                                                                                                                      sigVerify :=
                                                                                                                                                        oracle.sigVerify,
                                                                                                                                                      sigSign :=
                                                                                                                                                        oracle.sigSign }
                                                                                                                                                    (Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession
                                                                                                                                                      (Model.Lifecycle.encrypt
                                                                                                                                                          view
                                                                                                                                                          oracle
                                                                                                                                                          (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                                                                                            dh
                                                                                                                                                            s)
                                                                                                                                                          (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                                            plaintext)).session
                                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                        q.rootKey)
                                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                        q.sparseRoot)
                                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                        q.sparseSend)
                                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                        q.sparseReceive)
                                                                                                                                                      dSend
                                                                                                                                                      x
                                                                                                                                                      (oracleB.dhPublic
                                                                                                                                                        dB)
                                                                                                                                                      (oracle.dhPublic
                                                                                                                                                        dA)
                                                                                                                                                      dA)
                                                                                                                                                    (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                                      ptS) =
                                                                                                                                                  {
                                                                                                                                                    session :=
                                                                                                                                                      have
                                                                                                                                                        __src :=
                                                                                                                                                        Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession
                                                                                                                                                          (Model.Lifecycle.encrypt
                                                                                                                                                              view
                                                                                                                                                              oracle
                                                                                                                                                              (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                                                                                                dh
                                                                                                                                                                s)
                                                                                                                                                              (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                                                plaintext)).session
                                                                                                                                                          (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                            q.rootKey)
                                                                                                                                                          (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                            q.sparseRoot)
                                                                                                                                                          (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                            q.sparseSend)
                                                                                                                                                          (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                            q.sparseReceive)
                                                                                                                                                          dSend
                                                                                                                                                          x
                                                                                                                                                          (oracleB.dhPublic
                                                                                                                                                            dB)
                                                                                                                                                          (oracle.dhPublic
                                                                                                                                                            dA)
                                                                                                                                                          dA;
                                                                                                                                                      {
                                                                                                                                                        triple :=
                                                                                                                                                          Tacenta.UnitLifecycleInitiatorSecondSend.initiatorAfterSecond
                                                                                                                                                            (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                              q.rootKey)
                                                                                                                                                            (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                              q.sparseRoot)
                                                                                                                                                            (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                              q.sparseSend)
                                                                                                                                                            (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                              q.sparseReceive)
                                                                                                                                                            dSend
                                                                                                                                                            x
                                                                                                                                                            (oracleB.dhPublic
                                                                                                                                                              dB)
                                                                                                                                                            (oracle.dhPublic
                                                                                                                                                              dA),
                                                                                                                                                        braid :=
                                                                                                                                                          Model.Braid.BraidState.keysSampled
                                                                                                                                                            1
                                                                                                                                                            (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                                              q.auth)
                                                                                                                                                            dk
                                                                                                                                                            ekVector
                                                                                                                                                            {
                                                                                                                                                              source :=
                                                                                                                                                                Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                                                                  oracle.braidKem
                                                                                                                                                                  (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                                                    q.auth)
                                                                                                                                                                  ekSeed
                                                                                                                                                                  ekVector,
                                                                                                                                                              next :=
                                                                                                                                                                2 },
                                                                                                                                                        ratchetPrivate :=
                                                                                                                                                          __src.ratchetPrivate,
                                                                                                                                                        identityAd :=
                                                                                                                                                          __src.identityAd,
                                                                                                                                                        ourIdentityPublic :=
                                                                                                                                                          __src.ourIdentityPublic,
                                                                                                                                                        peerIdentityPublic :=
                                                                                                                                                          __src.peerIdentityPublic,
                                                                                                                                                        pendingInitial :=
                                                                                                                                                          __src.pendingInitial,
                                                                                                                                                        establishedEphemeral :=
                                                                                                                                                          __src.establishedEphemeral },
                                                                                                                                                    result :=
                                                                                                                                                      Except.ok
                                                                                                                                                        (Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame
                                                                                                                                                          view
                                                                                                                                                          oracle
                                                                                                                                                          (Tacenta.UnitLifecycleT3.vecOf
                                                                                                                                                            q.identityAd)
                                                                                                                                                          (Model.Braid.BraidState.keysSampled
                                                                                                                                                            1
                                                                                                                                                            (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                                              q.auth)
                                                                                                                                                            dk
                                                                                                                                                            ekVector
                                                                                                                                                            {
                                                                                                                                                              source :=
                                                                                                                                                                Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                                                                  oracle.braidKem
                                                                                                                                                                  (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                                                    q.auth)
                                                                                                                                                                  ekSeed
                                                                                                                                                                  ekVector,
                                                                                                                                                              next :=
                                                                                                                                                                1 })
                                                                                                                                                          (oracle.dhPublic
                                                                                                                                                            dA)
                                                                                                                                                          (Tacenta.UnitLifecycleInitiatorSecondSend.secondKey
                                                                                                                                                            (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                              q.rootKey)
                                                                                                                                                            (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                              q.sparseSend)
                                                                                                                                                            dSend
                                                                                                                                                            x)
                                                                                                                                                          {
                                                                                                                                                            source :=
                                                                                                                                                              Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                                                                oracle.braidKem
                                                                                                                                                                (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                                                  q.auth)
                                                                                                                                                                ekSeed
                                                                                                                                                                ekVector,
                                                                                                                                                            index :=
                                                                                                                                                              1 }
                                                                                                                                                          (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                                            ptS)),
                                                                                                                                                    oracle :=
                                                                                                                                                      {
                                                                                                                                                        draws :=
                                                                                                                                                          restA,
                                                                                                                                                        braidKem :=
                                                                                                                                                          oracle.braidKem,
                                                                                                                                                        dhPublic :=
                                                                                                                                                          oracle.dhPublic,
                                                                                                                                                        dhAgree :=
                                                                                                                                                          oracle.dhAgree,
                                                                                                                                                        identityValid :=
                                                                                                                                                          oracle.identityValid,
                                                                                                                                                        aeadSeal :=
                                                                                                                                                          oracle.aeadSeal,
                                                                                                                                                        aeadOpen :=
                                                                                                                                                          oracle.aeadOpen,
                                                                                                                                                        kemValid :=
                                                                                                                                                          oracle.kemValid,
                                                                                                                                                        kemEncaps :=
                                                                                                                                                          oracle.kemEncaps,
                                                                                                                                                        kemDecaps :=
                                                                                                                                                          oracle.kemDecaps,
                                                                                                                                                        sigVerify :=
                                                                                                                                                          oracle.sigVerify,
                                                                                                                                                        sigSign :=
                                                                                                                                                          oracle.sigSign } } ∧
                                                                                                                                                lifecycle.Session.encrypt
                                                                                                                                                      rc
                                                                                                                                                      crc
                                                                                                                                                      s''
                                                                                                                                                      ptS
                                                                                                                                                      rngA' =
                                                                                                                                                    ok
                                                                                                                                                      (core.result.Result.Ok
                                                                                                                                                          bytes2,
                                                                                                                                                        s''',
                                                                                                                                                        rngA') ∧
                                                                                                                                                  s''' =
                                                                                                                                                      {
                                                                                                                                                        triple :=
                                                                                                                                                          s'''.triple,
                                                                                                                                                        braid :=
                                                                                                                                                          s'''.braid,
                                                                                                                                                        ratchet_private :=
                                                                                                                                                          s''.ratchet_private,
                                                                                                                                                        identity_ad :=
                                                                                                                                                          s''.identity_ad,
                                                                                                                                                        our_identity_public :=
                                                                                                                                                          s''.our_identity_public,
                                                                                                                                                        peer_identity_public :=
                                                                                                                                                          s''.peer_identity_public,
                                                                                                                                                        pending_initial :=
                                                                                                                                                          s''.pending_initial,
                                                                                                                                                        established_ephemeral :=
                                                                                                                                                          s''.established_ephemeral } ∧
                                                                                                                                                    s'''.pending_initial =
                                                                                                                                                        none ∧
                                                                                                                                                      Tacenta.UnitLifecycleT3.vecOf
                                                                                                                                                            bytes2 =
                                                                                                                                                          Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame
                                                                                                                                                            view
                                                                                                                                                            oracle
                                                                                                                                                            (Tacenta.UnitLifecycleT3.vecOf
                                                                                                                                                              q.identityAd)
                                                                                                                                                            (Model.Braid.BraidState.keysSampled
                                                                                                                                                              1
                                                                                                                                                              (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                                                q.auth)
                                                                                                                                                              dk
                                                                                                                                                              ekVector
                                                                                                                                                              {
                                                                                                                                                                source :=
                                                                                                                                                                  Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                                                                    oracle.braidKem
                                                                                                                                                                    (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                                                      q.auth)
                                                                                                                                                                    ekSeed
                                                                                                                                                                    ekVector,
                                                                                                                                                                next :=
                                                                                                                                                                  1 })
                                                                                                                                                            (oracle.dhPublic
                                                                                                                                                              dA)
                                                                                                                                                            (Tacenta.UnitLifecycleInitiatorSecondSend.secondKey
                                                                                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                q.rootKey)
                                                                                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                q.sparseSend)
                                                                                                                                                              dSend
                                                                                                                                                              x)
                                                                                                                                                            {
                                                                                                                                                              source :=
                                                                                                                                                                Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                                                                  oracle.braidKem
                                                                                                                                                                  (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                                                    q.auth)
                                                                                                                                                                  ekSeed
                                                                                                                                                                  ekVector,
                                                                                                                                                              index :=
                                                                                                                                                                1 }
                                                                                                                                                            (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                                              ptS) ∧
                                                                                                                                                        Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                                                                            dh
                                                                                                                                                            oracle.braidKem
                                                                                                                                                            s'''
                                                                                                                                                            (have
                                                                                                                                                              __src :=
                                                                                                                                                              Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession
                                                                                                                                                                (Model.Lifecycle.encrypt
                                                                                                                                                                    view
                                                                                                                                                                    oracle
                                                                                                                                                                    (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                                                                                                      dh
                                                                                                                                                                      s)
                                                                                                                                                                    (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                                                      plaintext)).session
                                                                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                  q.rootKey)
                                                                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                  q.sparseRoot)
                                                                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                  q.sparseSend)
                                                                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                  q.sparseReceive)
                                                                                                                                                                dSend
                                                                                                                                                                x
                                                                                                                                                                (oracleB.dhPublic
                                                                                                                                                                  dB)
                                                                                                                                                                (oracle.dhPublic
                                                                                                                                                                  dA)
                                                                                                                                                                dA;
                                                                                                                                                            {
                                                                                                                                                              triple :=
                                                                                                                                                                Tacenta.UnitLifecycleInitiatorSecondSend.initiatorAfterSecond
                                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                    q.rootKey)
                                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                    q.sparseRoot)
                                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                    q.sparseSend)
                                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                    q.sparseReceive)
                                                                                                                                                                  dSend
                                                                                                                                                                  x
                                                                                                                                                                  (oracleB.dhPublic
                                                                                                                                                                    dB)
                                                                                                                                                                  (oracle.dhPublic
                                                                                                                                                                    dA),
                                                                                                                                                              braid :=
                                                                                                                                                                Model.Braid.BraidState.keysSampled
                                                                                                                                                                  1
                                                                                                                                                                  (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                                                    q.auth)
                                                                                                                                                                  dk
                                                                                                                                                                  ekVector
                                                                                                                                                                  {
                                                                                                                                                                    source :=
                                                                                                                                                                      Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                                                                        oracle.braidKem
                                                                                                                                                                        (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                                                          q.auth)
                                                                                                                                                                        ekSeed
                                                                                                                                                                        ekVector,
                                                                                                                                                                    next :=
                                                                                                                                                                      2 },
                                                                                                                                                              ratchetPrivate :=
                                                                                                                                                                __src.ratchetPrivate,
                                                                                                                                                              identityAd :=
                                                                                                                                                                __src.identityAd,
                                                                                                                                                              ourIdentityPublic :=
                                                                                                                                                                __src.ourIdentityPublic,
                                                                                                                                                              peerIdentityPublic :=
                                                                                                                                                                __src.peerIdentityPublic,
                                                                                                                                                              pendingInitial :=
                                                                                                                                                                __src.pendingInitial,
                                                                                                                                                              establishedEphemeral :=
                                                                                                                                                                __src.establishedEphemeral }) ∧
                                                                                                                                                          s'''.invariant =
                                                                                                                                                              ok
                                                                                                                                                                true ∧
                                                                                                                                                            Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                                                                                                s''' ∧
                                                                                                                                                              ∀
                                                                                                                                                                (j :
                                                                                                                                                                  ℕ),
                                                                                                                                                                j +
                                                                                                                                                                      3 <
                                                                                                                                                                    U32.max →
                                                                                                                                                                  Tacenta.UnitLifecycleSendPreserve.CounterRoom
                                                                                                                                                                    s'''
                                                                                                                                                                    j
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorSecondMessage.initiator_sends_second_message

/--
info: Tacenta.UnitLifecycleInitiatorSecondMessage.first_send_second_message_reachable : ∀ (K : Model.Braid.Kem)
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
                        Tacenta.UnitSatisfiabilityJoint.Interp.real tacenta_boundary.kem.KeyPair.public_key
                        @alloc.vec.Vec.is_empty →
                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K →
                        Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                          Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                            Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstant →
                              ∀ (ourA : lifecycle.Identity) (seed : List U8),
                                seed.length = 64 →
                                  ∀ (extra : List U8),
                                    extra.length = 32 →
                                      K.keyGen
                                            (Model.Lifecycle.braidRandomness
                                              (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠
                                          none →
                                        ∀ (ptR : Slice U8),
                                          (↑ptR).length ≤ 4096 →
                                            ∀ (ptS : Slice U8),
                                              (↑ptS).length ≤ 4096 →
                                                Tacenta.UnitLifecycleInitiatorSecondMessage.SecondMessageRun K ourA seed
                                                  extra ptR ptS
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitiatorSecondMessage.first_send_second_message_reachable

/--
info: def Tacenta.UnitLifecycleInitiatorSecondMessage.SecondMessageRun : Model.Braid.Kem →
  lifecycle.Identity → List U8 → List U8 → Slice U8 → Slice U8 → Prop :=
fun K ourA seed extra ptR ptS =>
  ∃ oracle bundle q bytes s' rng' ourB storeB seedB sB' ptB storeB' rngB' bytesR sB'' ptA s'' rngA' bytes2 s''',
    oracle.braidKem = K ∧
      lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
            Tacenta.UnitLifecycleIntegrationScreen.byteCrc q.session
            Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext (seed ++ extra) =
          ok (core.result.Result.Ok bytes, s', rng') ∧
        storeB.publish = ok bundle ∧
          lifecycle.establish_responder Tacenta.UnitLifecycleIntegrationScreen.byteRng
                Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourB storeB bytes.deref seedB =
              ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
            lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                  Tacenta.UnitLifecycleIntegrationScreen.byteCrc sB' ptR rngB' =
                ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
              lifecycle.Session.decrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                    Tacenta.UnitLifecycleIntegrationScreen.byteCrc s' bytesR.deref rng' =
                  ok (core.result.Result.Ok ptA, s'', rngA') ∧
                ↑ptA = ↑ptR ∧
                  s''.invariant = ok true ∧
                    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s'' ∧
                      lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc s'' ptS rngA' =
                          ok (core.result.Result.Ok bytes2, s''', rngA') ∧
                        s'''.invariant = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s'''
-/
#guard_msgs in
#print Tacenta.UnitLifecycleInitiatorSecondMessage.SecondMessageRun
