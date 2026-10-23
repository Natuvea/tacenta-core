import Translation.UnitLifecycleResponderSecondReceipt

/-!
# The responder's second reply: `Session::encrypt` at the session its receipt of the second message returned

`UnitLifecycleResponderSecondReceipt` shows that the responder's public `Session::decrypt` of the initiator's second
message, at the session `sB''` its reply left, returns the initiator's second plaintext and a session `sB'''` that
passes `Session::invariant`, meets the four ceilings and refines the model's step (`secondReceiptSession`), on one run
from the initiator's establishment, under the per-run premises that the responder's source after its reply holds a draw
and that the initiator's new ratchet key is not its first.  This module takes the responder's next operation on that
same session: its `Session::encrypt` of a further plaintext `ptR2` at `sB'''`, from the source `rngR2` the receipt left,
on the same run (the same `sB'''`, from the same call on the same bytes).

## How

At `sB'''` the responder's agreement waits for the header at epoch 1 (`NoHeaderReceived`, two of the header's three
32-byte chunks held), and the receipt cleared the pending initial message.  So:
* `noHeader_of_refines`: a session related to a model session whose agreement is at `noHeaderReceived` holds its
  agreement at `NoHeaderReceived`.  The translated `Braid::send` there (`braid_send_noHeader`, at any decoder) returns
  the source it was given, the agreement as given, an empty message (type `None`, no chunk) and no output; the walk
  names every call on that path, and none is an encapsulation, a decapsulation, a key generation or a draw.
* `second_reply_send_key`, `second_reply_model_step`, `modelCounterRoom_secondReplier` (model only): the model Triple's
  send from `responderAfterSecond` at epoch 0 succeeds with header `secondHeader newPub2` (the ratchet key the receipt
  installed, previous chain length 1 for the reply, message number 0, sparse epoch 0 and number 2), key
  `secondReplyKey` (the classical chain the receipt's Diffie-Hellman step derived, the sparse chain `k2` at number 2)
  and successor `responderAfterSecondSend`; the model's `encrypt` there has one outcome, the bare `secondReplyFrame`
  (agreement type `none`, no chunk, no initial wrapper), with no draw and the agreement unchanged; and the model session
  after it has room for every `k` with `k + 3 < u32::MAX` further operations.
* `responder_second_send_refines`: the generic dispatch-layer route `public_session_encrypt_of_send_contracts` at every
  session related to `secondReceiptSession` of an agreement at `noHeaderReceived` epoch 1 that passes the invariant and
  meets the ceilings, with the providers from `encryptProviders_of_invariant`, the counted draw record from
  `braidSendTraceCounted_of_noHeader` and the headroom from `encryptHeadroom_reply`.
* `responder_sends_second_reply` composes them on the run: `sB'''`, its relation, invariant, ceilings and budget
  and `rngR2` from `responder_receives_second_message`; the associated data the responder's model session carries from
  `initiator_first_send_responder_replies` on the same reply call; the refinement at the responder's oracle with the
  draws `rngR2` holds; the bytes and the session from `second_reply_model_step`; the source and the agreement after the
  call from the walk (`encrypt_ok_parts`, `braid_send_noHeader`); `Session::invariant` and the ceilings after the call
  from send preservation (`encrypt_keeps_invariant_no_draw` at `NoHeaderReceived`, one unit of the budget at `sB'''`);
  and the budget after the call read off the model session after the step (`counterRoom_iff_model`,
  `modelCounterRoom_secondReplier`).

## The statements

* `responder_sends_second_reply`: under the hypotheses of `responder_receives_second_message` (the run from the
  initiator's establishment through its second send and the responder's receipt of it, with its per-run premises: the
  responder's source after its reply holds a draw `dB2`, and the initiator's new ratchet key is not its first,
  `hfreshA`) and for every plaintext `ptR2` of at most `Usize.max - 150` bytes (placed first): the receipt's calls and
  plaintext equations, its draw equation and the agreements `x` and `z` hold, `sB'''` passes `Session::invariant` and
  meets `CounterHeadroom`, and the public `Session::encrypt` of `ptR2` at `sB'''` from `rngR2` returns `Ok bytesR2` and
  a session `sB4` and leaves `rngR2` as it was (no draw); `sB4` is `sB'''` with only the Triple Ratchet written (the
  agreement, the ratchet key and the pending initial message, none, unchanged); `bytesR2` is `secondReplyFrame` at the
  responder's oracle, the initiator's associated data and the responder's new ratchet key `oracleB.dhPublic dB2`, sealed
  under `secondReplyKey`; `sB4` refines the model session after that step (the Triple `responderAfterSecondSend`, the
  agreement as after the receipt); and `sB4` passes `Session::invariant`, meets `CounterHeadroom` and has room for every
  `j` with `j + 3 < u32::MAX` further operations (`CounterRoom`).
* `first_send_second_reply_reachable`: at the real constants under the laws of `first_send_second_receipt_reachable`,
  for every initiator identity, every 64-byte seed at whose bytes the model's key generation answers, every 32 further
  bytes of the responder's source and every reply, second and second reply plaintext of at most 4096 bytes, a run on
  which the responder's `encrypt` after the receipt returns bytes, leaves its source, writes only the Triple Ratchet and
  leaves a session passing `Session::invariant` and meeting `CounterHeadroom` (`SecondReplyRun`).

## Laws and premises

No new law and no new per-run premise.  Beyond the hypotheses of `responder_receives_second_message` (including its two
per-run premises, the responder's draw `dB2` and `hfreshA`), the headline takes only the plaintext bound
`102 + (ptR2.length + 48) ≤ Usize.max`, which holds of every plaintext of at most `2^32 - 151` bytes on a 32-bit
target.  The encrypt records the second reply uses are the ones the responder's reply already takes
(`BraidSendRefinementContracts` and `OracleOf` at the responder's source, and the source-free records
`TripleSendRefinementContracts`, `AeadSealBounded`, `DhCodecTotal`, `DhCodecOf`, `CodewordViewSendOf` and the three
`zeroize` round trips), at the source the receipt left (the oracle record holds of the oracle with any draws,
`oracleOf_with_draws`); `Ct1LenTotal` comes from the responder's contracts and `KemCloneAgrees` (send preservation)
from its `DecryptRatchetAgreements`.  At `NoHeaderReceived` the agreement's send reads neither randomness nor a KEM
operation (`braid_send_noHeader`), so no fact relating the two parties' Braid KEMs is used by this step; the Braid send
record still carries `KemAgreesFor` at the responder oracle's KEM, as the generic route takes it for every state, and
whether it could be dropped here is not checked.  No premise names a platform width, so each result holds on 32- and
64-bit targets.  The reach takes the laws of `first_send_second_receipt_reachable` and no other.

## Trust

Every result here rests on the kernel and opaque constants only, with no compiler-trust axiom (pins below); the
headline and the reach apply the encrypt and decrypt refinements through the theorems they compose, whose nine
`native_decide` constants are kernel proofs since 2026-10-21.  The module sets `pp.deepTerms true` and
`pp.proofs.withType true` before its pins, so the statement pins print each statement whole; the reach's conclusion is
the definition `SecondReplyRun`, whose `#print` pin holds the whole run.  A printed pin is still not the whole
elaborated statement (instance arguments, coercion functions, implicit arguments and the binder types of `∃` and `fun`
are not printed), so that the pinned statement is the right one is decided by reading.  Of the headline's conclusion,
the reach consumes its five calls (the reply, its receipt, the second send, its receipt and the second reply), the
plaintext equations, the frame equation of `sB4`, and
`Session::invariant` and `CounterHeadroom` at `sB4`; its other conjuncts (the draw equation, the agreements `x` and `z`,
the invariant and the ceilings at `sB'''`, the bytes as `secondReplyFrame`, the relation of `sB4` and the budget) are
pinned and used by no later proof.

## Non-vacuity

No law is added, so `reply_receipt_laws_model` still puts every law the reach takes in one toy interpretation,
`InterpO.modelReply`.  `first_send_second_reply_reachable` exhibits, at the real constants under those laws (assumed,
not shown of the real primitives), a run at which every hypothesis of `responder_sends_second_reply` holds (the
initiator's further bytes chosen by `DhPublicNotConstant`, the responder's further bytes its draw for the receipt) and
the responder's `encrypt` returns bytes.  The encrypt at this state has one outcome, so there is no second arm to reach;
the stale arm of the receipt leaves `sB''` unchanged and is not followed here.

## What it does not show

* The initiator's `decrypt` of the second reply at its session after its second send, and every later step: the
  header's third chunk, the responder's first sampling send, and the responder's check of the completed encapsulation
  key, the first step at which both parties' KEMs act on one key pair.
* A refusal `encrypt` can reach: at this state none occurs (the terminal guard is false, the agreement's send at
  `NoHeaderReceived` does not refuse, the model's Triple send succeeds from message number 0 on the chain the receipt
  derived, the composite header is defined); the refusals reachable elsewhere in a session (the terminal guard,
  `AgreementFailed`, `ChainExhausted`, `NoSendingChain`) are not covered.
* That a tampered, foreign or replayed frame is refused by either party on this route, or delivery out of order, a
  skipped or stored key, or the decoder holding more than one chunk before a receive.
* That the budget is exact at `sB4`: room for every `j` with `j + 3 < u32::MAX` is what the model session after the
  step gives (the send does not advance the clock, which is 2 there); more room is not claimed.
* That `hfreshA` or the draw holds of a run with an honest random source (they are premises; no probability is
  claimed); a restored copy of `sB'''` or `sB4`; the one-time path in a run (the reach takes the last-resort path only);
  that the related model sessions hold only bytes the parties received (the responder's relations are at views that
  attribute the received codewords).
* That the real primitives meet the boundary records or the laws (`KemCloneAgrees`, `AeadRoundTrip`,
  `DhAgreeContributory`, `DhAgreeSymmetric`, `DhPublicValid`, `DhPublicNotConstant`), that ML-KEM decapsulation agrees
  on a run (`FirstKemAgrees`), or `PrekeyIdsDistinct` from `PrekeyStore::invariant`; the model's own
  `establishResponder` equality.
* That `Session::invariant` says a session is reachable: it is a predicate on fields.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit

namespace Tacenta.UnitLifecycleResponderSecondSend

open Tacenta.UnitLifecycleT3 (DhView DhCodecOf KemView arrayOf vecOf sliceOf SessionRefines OracleOf
  BraidSendRefinementContracts TripleSendRefinementContracts CodewordViewSendOf PublicEncryptWitness
  ZeroizingRoundTrips)
open Tacenta.UnitLifecycleDecryptRunBounds (CounterHeadroom)

/-! ## The model's second reply -/

section Model
open Model.State (Key)
open Tacenta.UnitLifecycleResponderSecondReceipt (responderAfterSecond secondReceiptSession)
open Tacenta.UnitLifecycleInitiatorSecondSend (secondHeader)

/-- The responder's Triple after its second send: the classical sending chain its receipt of the second message
derived (from the agreement `z` of its new ratchet key `newPub2` with the initiator's new key) stepped once, the
sparse sending chain of epoch 0 stepped from number 1 to 2; everything else as after the receipt. -/
def responderAfterSecondSend (ec prk k1 k2 d dSend candA xB z newPub2 : Key) : Model.Triple.State :=
  { classical :=
      { dhsPub := newPub2, dhrPub := some candA,
        rk := (Model.State.kdfRk (Model.State.kdfRk
          (Model.State.kdfRk (Model.State.kdfRk ec d .tacenta).1 dSend .tacenta).1 xB .tacenta).1 z .tacenta).1,
        cks := some (Model.State.kdfCk (Model.State.kdfRk (Model.State.kdfRk
          (Model.State.kdfRk (Model.State.kdfRk ec d .tacenta).1 dSend .tacenta).1 xB .tacenta).1 z .tacenta).2).1,
        ckr := some (Model.State.kdfCk (Model.State.kdfRk
          (Model.State.kdfRk (Model.State.kdfRk ec d .tacenta).1 dSend .tacenta).1 xB .tacenta).2).1,
        ns := 1, nr := 1, pn := 1, skipped := [], events := 2, labels := .tacenta }
    postQuantum :=
      { rk := prk, epoch := 0,
        chains :=
          [(0, { send := some ⟨(Model.SparseRatchet.kdfCk (Model.SparseRatchet.kdfCk k2 1).1 2).1, 2⟩
                 receive := some ⟨(Model.SparseRatchet.kdfCk (Model.SparseRatchet.kdfCk k1 1).1 2).1, 2⟩ })],
        skipped := [], direction := .b2a } }

/-- The second reply's message key: the combination of the classical message key of the sending chain the receipt
of the second message derived (root after `d`, `dSend`, `xB`, then `z`) and the sparse message key of `k2`'s chain
at number 2. -/
def secondReplyKey (ec k2 d dSend xB z : Key) : Key :=
  Model.TripleRatchet.combine
    (Model.State.kdfCk (Model.State.kdfRk (Model.State.kdfRk
      (Model.State.kdfRk (Model.State.kdfRk ec d .tacenta).1 dSend .tacenta).1 xB .tacenta).1 z .tacenta).2).2
    (Model.SparseRatchet.kdfCk (Model.SparseRatchet.kdfCk k2 1).1 2).2

/-- **The model's second reply send from the responder after its receipt of the second message**: header
`secondHeader newPub2` (the ratchet key the receipt installed, previous chain length 1, message number 0, sparse epoch
0 and number 2), key `secondReplyKey`, successor `responderAfterSecondSend`.  Hypothesis-free. -/
theorem second_reply_send_key (ec prk k1 k2 d dSend candA xB z newPub2 : Key) :
    Model.Triple.sendDetailed (responderAfterSecond ec prk k1 k2 d dSend candA xB z newPub2) 0 none =
      .ok (responderAfterSecondSend ec prk k1 k2 d dSend candA xB z newPub2, secondHeader newPub2,
        secondReplyKey ec k2 d dSend xB z) := by
  simp [Model.Triple.sendDetailed, Model.Ratchet.sendDetailed, Model.SparseRatchet.sendDetailed,
    Model.SparseRatchet.maybeAdvanceDetailed, Model.SparseRatchet.findChains, responderAfterSecond,
    responderAfterSecondSend, secondHeader, secondReplyKey, Model.State.u32Max, Model.SparseRatchet.u64Max,
    Model.SparseRatchet.setChains]

/-- The second reply's composite header: the ratchet key `newPub2`, classical numbers 1 (previous chain) and 0,
sparse epoch 0 and number 2, agreement epoch 1, agreement type `none`, no chunk. -/
def secondReplyComposite (newPub2 : Key) : Model.CompositeHeader.Composite :=
  { dh := newPub2
    pn := UInt32.ofNat 1
    n := UInt32.ofNat 0
    pqEpoch := UInt64.ofNat 0
    pqN := UInt64.ofNat 2
    agEpoch := UInt64.ofNat 1
    agType := .none
    agChunk := none }

/-- The second reply frame: the composite header and the plaintext sealed under the message key, with the
associated data `ad` followed by the encoded header.  No initial wrapper. -/
def secondReplyFrame (oracle : Model.Lifecycle.Oracle) (ad : Model.Lifecycle.Bytes) (newPub2 messageKey : Key)
    (plaintext : Model.Lifecycle.Bytes) : Model.Lifecycle.Bytes :=
  Model.CompositeHeader.encodeMessage (secondReplyComposite newPub2)
    (oracle.aeadSeal (Model.State.messageKeys messageKey .tacenta).1
      (Model.State.messageKeys messageKey .tacenta).2.1
      (Model.State.messageKeys messageKey .tacenta).2.2 plaintext
      (Model.Messages.concatAd ad (Model.CompositeHeader.encode (secondReplyComposite newPub2))))

/-- The second reply frame reads only the oracle's seal: it is the same at the oracle with any draws. -/
theorem secondReplyFrame_with_draws (oracle : Model.Lifecycle.Oracle) (draws : List Key)
    (ad : Model.Lifecycle.Bytes) (newPub2 messageKey : Key) (plaintext : Model.Lifecycle.Bytes) :
    secondReplyFrame { oracle with draws := draws } ad newPub2 messageKey plaintext =
      secondReplyFrame oracle ad newPub2 messageKey plaintext :=
  rfl

/-- **The model's `encrypt` at the responder after its receipt of the second message has one outcome**, for every
codeword view, oracle and plaintext, when the agreement there waits for the header at epoch 1: it reads no draw,
returns the bare second reply frame (`secondReplyFrame`, agreement type `none`, no chunk, no initial wrapper since the
receipt cleared the pending initial message), and leaves the session with the Triple `responderAfterSecondSend` and
everything else, the agreement included, unchanged.  Model only. -/
theorem second_reply_model_step (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (mB : Model.Lifecycle.Session) (auth : Model.Braid.Auth) (dec : Model.Braid.Decoder)
    (ec prk k1 k2 d dSend candA xB z newPub2 c : Key) (pt : Model.Lifecycle.Bytes) :
    Model.Lifecycle.encrypt view oracle
        (secondReceiptSession mB (.noHeaderReceived 1 auth dec) ec prk k1 k2 d dSend candA xB z newPub2 c) pt =
      { session := { secondReceiptSession mB (.noHeaderReceived 1 auth dec) ec prk k1 k2 d dSend candA xB z
            newPub2 c with
          triple := responderAfterSecondSend ec prk k1 k2 d dSend candA xB z newPub2 }
        result := .ok (secondReplyFrame oracle mB.identityAd newPub2 (secondReplyKey ec k2 d dSend xB z) pt)
        oracle := oracle } := by
  simp [Model.Lifecycle.encrypt, Model.Lifecycle.agreementFailed, Model.Lifecycle.sendAgreement,
    Model.Lifecycle.braidSendNeedsDraw, Model.Braid.send, Model.Lifecycle.braidFailed,
    Model.Lifecycle.sparseOutputOf, Model.Braid.BraidState.epoch, secondReceiptSession, second_reply_send_key,
    Model.Lifecycle.compositeOf, Model.Lifecycle.compositeTypeOf, secondReplyFrame, secondReplyComposite,
    secondHeader]

/-- **The budget at the responder's model session after its second reply**: clock 2, sparse epoch 0, chain counters
2 and 2, agreement epoch 1, so room for every `k` with `k + 3 < u32::MAX`.  Model only. -/
theorem modelCounterRoom_secondReplier (mB : Model.Lifecycle.Session) (auth : Model.Braid.Auth)
    (dec : Model.Braid.Decoder) (ec prk k1 k2 d dSend candA xB z newPub2 c : Key) (k : Nat)
    (hk : k + 3 < Std.U32.max) :
    Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom
      { secondReceiptSession mB (.noHeaderReceived 1 auth dec) ec prk k1 k2 d dSend candA xB z newPub2 c with
        triple := responderAfterSecondSend ec prk k1 k2 d dSend candA xB z newPub2 } k := by
  have h32 : Std.U32.max = 4294967295 := by simp [Std.U32.max_eq]
  have h64 : Std.U64.max = 18446744073709551615 := by simp [Std.U64.max_eq]
  rw [h32] at hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [responderAfterSecondSend]; omega
  · simp only [responderAfterSecondSend]; omega
  · simp only [responderAfterSecondSend, List.mem_singleton]
    rintro q rfl ch (h | h) <;> (simp at h; subst h; simp only; omega)
  · simp only [secondReceiptSession, Model.Braid.BraidState.epoch]; omega

end Model

/-! ## The encrypt refinement at the session after the receipt of the second message -/

section Refines
open Tacenta.UnitLifecycleResponderSecondReceipt (secondReceiptSession)

/-- A session related to a model session whose agreement waits for the header holds an agreement waiting for the
header.  Hypothesis-free. -/
theorem noHeader_of_refines {dh : DhView} {K : Model.Braid.Kem} {s : lifecycle.Session}
    {m : Model.Lifecycle.Session} {e : Nat} {a : Model.Braid.Auth} {dec : Model.Braid.Decoder}
    (hrel : SessionRefines dh K s m) (hb : m.braid = .noHeaderReceived e a dec) :
    ∃ e' auth d, s.braid.state = tacenta_braid.State.NoHeaderReceived e' auth d := by
  have h := hrel.braid
  rw [hb] at h
  rcases hst : s.braid.state with _ | _ | _ | _ | _ | ⟨e', auth, d⟩ | _ | _ | _ | _ | _ | _
  all_goals (rw [hst] at h; try (simp [Tacenta.SessionUnitBraidT3.StateRefines] at h; done))
  exact ⟨e', auth, d, rfl⟩

/-- **The public `Session::encrypt` at a session related to the model session after the receipt of the second
message refines the model's step**: for a session that refines `secondReceiptSession mB …` with the agreement waiting
for the header at epoch 1 (any decoder), passes `Session::invariant` and meets `CounterHeadroom`, every plaintext of at
most `Usize.max - 150` bytes and every source state, the call returns, and its result, its post-state and the draws it
leaves refine `Model.Lifecycle.encrypt` there.  Under the encrypt boundary records on that source, the oracle record,
`DhCodecOf`, `CodewordViewSendOf`, three `zeroize` round trips, `Ct1LenTotal` and the trace equation.  The generic
dispatch-layer route (`public_session_encrypt_of_send_contracts`) with its session-specific inputs discharged here: the
providers from the invariant and the ceilings (`encryptProviders_of_invariant`), the counted draw record at
`NoHeaderReceived` (`braidSendTraceCounted_of_noHeader`), and the headroom from the invariant with no pending initial
message (`encryptHeadroom_reply`). -/
theorem responder_second_send_refines [Tacenta.SessionUnitT1.DerivedKeysModel] {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem) (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (mB : Model.Lifecycle.Session) (auth : Model.Braid.Auth) (dec : Model.Braid.Decoder)
    (ec prk k1 k2 d dSend candA xB z newPub2 c : Model.State.Key)
    (sB : lifecycle.Session)
    (hrel : SessionRefines dh oracle.braidKem sB
      (secondReceiptSession mB (.noHeaderReceived 1 auth dec) ec prk k1 k2 d dSend candA xB z newPub2 c))
    (hinv : lifecycle.Session.invariant sB = ok true) (hc : CounterHeadroom sB)
    (plaintext : Slice Std.U8) (hroom : 102 + (plaintext.val.length + 48) ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws) :
    PublicEncryptWitness rc crc trace dh oracle.braidKem view oracle sB
      (secondReceiptSession mB (.noHeaderReceived 1 auth dec) ec prk k1 k2 d dSend candA xB z newPub2 c)
      plaintext rng := by
  have hpendR : sB.pending_initial = none := by
    have h := hrel.pendingInitial
    simp only [secondReceiptSession, Option.map_eq_none_iff] at h
    exact h
  obtain ⟨e, a, d0, hst⟩ := noHeader_of_refines hrel rfl
  have hdraw : Model.Lifecycle.braidSendNeedsDraw
      (secondReceiptSession mB (.noHeaderReceived 1 auth dec) ec prk k1 k2 d dSend candA xB z newPub2 c).braid =
        false := rfl
  obtain ⟨providers⟩ := Tacenta.UnitLifecycleInitiatorSecondSend.encryptProviders_of_invariant dh kem
    oracle.braidKem view oracle sB _ hinv hrel hc hdraw plaintext rng
  exact Tacenta.UnitLifecycleT3.public_session_encrypt_of_send_contracts braid
    (Tacenta.UnitLifecycleResponderReply.braidSendTraceCounted_of_noHeader rfl e a d0 hst 1 auth dec rfl)
    triple aead dhCodec
    (Tacenta.UnitLifecycleResponderReply.encryptHeadroom_reply dhCodec hct1 sB hinv hpendR plaintext hroom)
    oracleOf codec codewordView braid.hkdf hz80 hz32 hzKeys hrel htrace providers

end Refines

/-! ## The responder's second reply, on the run -/

section Comp

open Tacenta.UnitLifecycleResponderFirstReceipt (headerSource DhAgreeContributory AeadRoundTrip)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid)
open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts responderModelOf)
open Tacenta.UnitLifecycleResponderReply (oracleOf_with_draws)
open Tacenta.UnitLifecycleResponderSecondReceipt (secondReceiptSession replierSession)
open Tacenta.UnitLifecycleSendPreserve (CounterRoom)

/-- **The responder's second reply, on the run of the initiator's first send.**  Under the hypotheses of
`responder_receives_second_message`, with its two per-run premises (the responder's source after its reply holds a
draw `dB2`; `hfreshA`, the initiator's new ratchet key is not its first), and for every plaintext `ptR2` of at most
`Usize.max - 150` bytes (the only binder added, placed first): the receipt's conjuncts named in the statement hold (the
reply, the initiator's receipt of it, the second send, the responder's receipt of it returning the second plaintext and
leaving `rngR2` with the rest after `dB2`, the agreements `x` and `z`, `Session::invariant` and `CounterHeadroom` at
`sB'''`); the public `Session::encrypt` of `ptR2` at `sB'''` from `rngR2` returns `Ok bytesR2` and `sB4` and leaves
`rngR2` as it was (no draw); `sB4` is `sB'''` with only the Triple Ratchet written; `bytesR2` is the bare
`secondReplyFrame` (the responder's new ratchet key, previous chain length 1, message number 0, sparse epoch 0 and
number 2, agreement epoch 1 and type `none`, no chunk) sealed under `secondReplyKey` with the initiator's associated
data; `sB4` refines the model session after that step (the Triple `responderAfterSecondSend`); and `sB4` passes
`Session::invariant` (send preservation at `NoHeaderReceived`), meets `CounterHeadroom` and has room for every `j` with
`j + 3 < u32::MAX` further operations (read off the model session after the step).  No compiler-trust axiom (the
pin). -/
theorem responder_sends_second_reply [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (ptR2 : Slice Std.U8) (hroomR2 : 102 + (ptR2.val.length + 48) ≤ Usize.max)
    (traceB : F → List Model.Lifecycle.Key) (rngR : F) (dB2 : Model.Lifecycle.Key) (restB2 : List Model.Lifecycle.Key)
    (hdrawB2 : traceB rngR = dB2 :: restB2) (oracle : Model.Lifecycle.Oracle) (dA : Model.Lifecycle.Key)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E) (ourA : lifecycle.Identity)
    (bundleA : lifecycle.PublishedBundle) (q : InitiatorSecretParts rcE crcE ourA bundleA)
    (hfreshA : oracle.dhPublic dA ≠ arrayOf q.ratchetBytes)
    (ptS : Slice Std.U8) (hroomS : 102 + (ptS.val.length + 48) ≤ Usize.max)
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView)
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
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
    (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE ourA bundleA expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (hq : s = q.session)
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws) (d1 d2 : Model.Lifecycle.Key)
    (rest : List Model.Lifecycle.Key) (hdraws : trace rng = d1 :: d2 :: rest)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng = ok (core.result.Result.Ok bytes, s', rng'))
    (contractsA : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (agreementsA : DecryptRatchetAgreements oracle.braidKem)
    (restA : List Model.Lifecycle.Key) (hdrawA : trace rng' = dA :: restA)
    (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (oracleB : Model.Lifecycle.Oracle)
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
    (ptR : Slice Std.U8) (hroomR : 102 + (ptR.val.length + 48) ≤ Usize.max)
    (hfreshB : oracleB.dhPublic dB ≠ arrayOf q.peerRatchetBytes) :
    ∃ (p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes)) (ec : Array U8 32#usize)
      (dSend x : Model.Lifecycle.Key) (ekSeed ekVector : Model.Braid.Bytes) (bytesR : alloc.vec.Vec Std.U8)
      (sB'' : lifecycle.Session) (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' : R)
      (bytes2 : alloc.vec.Vec Std.U8) (s''' : lifecycle.Session) (z : Model.Lifecycle.Key)
      (ptB2 : alloc.vec.Vec Std.U8) (sB''' : lifecycle.Session) (rngR2 : F) (bytesR2 : alloc.vec.Vec Std.U8)
      (sB4 : lifecycle.Session),
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' =
        ok (core.result.Result.Ok ptA, s'', rngA') ∧ ptA.val = ptR.val ∧
      lifecycle.Session.encrypt rc crc s'' ptS rngA' = ok (core.result.Result.Ok bytes2, s''', rngA') ∧
      lifecycle.Session.decrypt rcB crcB sB'' (alloc.vec.Vec.deref bytes2) rngR =
        ok (core.result.Result.Ok ptB2, sB''', rngR2) ∧
      ptB2.val = ptS.val ∧ traceB rngR2 = restB2 ∧
      oracle.dhAgree dA (oracleB.dhPublic dB) = some x ∧
      oracleB.dhAgree dB2 (oracle.dhPublic dA) = some z ∧
      lifecycle.Session.invariant sB''' = ok true ∧ CounterHeadroom sB''' ∧
      lifecycle.Session.encrypt rcB crcB sB''' ptR2 rngR2 = ok (core.result.Result.Ok bytesR2, sB4, rngR2) ∧
      sB4 = { sB''' with triple := sB4.triple } ∧
      vecOf bytesR2 = secondReplyFrame oracleB (vecOf q.identityAd) (oracleB.dhPublic dB2)
        (secondReplyKey (arrayOf ec) (arrayOf q.sparseReceive) (arrayOf q.dhOut) dSend x z) (sliceOf ptR2) ∧
      SessionRefines dh oracleB.braidKem sB4
        { secondReceiptSession
            (replierSession (responderModelOf dh p) (sliceOf p.braidSecret)
              ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
              (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
              (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB)
            (.noHeaderReceived 1 (Model.Braid.Auth.init 1 (sliceOf p.braidSecret))
              (((Model.Braid.Decoder.new (Model.Braid.headerSize + Model.Braid.macSize)).addChunk
                ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector,
                  0⟩).addChunk
                ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩))
            (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
            (arrayOf q.dhOut) dSend (oracle.dhPublic dA) x z (oracleB.dhPublic dB2) dB2 with
          triple := responderAfterSecondSend (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend)
            (arrayOf q.sparseReceive) (arrayOf q.dhOut) dSend (oracle.dhPublic dA) x z (oracleB.dhPublic dB2) } ∧
      lifecycle.Session.invariant sB4 = ok true ∧ CounterHeadroom sB4 ∧
      (∀ j, j + 3 < Std.U32.max → CounterRoom sB4 j) := by
  -- the responder's receipt of the second message, on the run
  obtain ⟨p, ec, dSend, x, dk, ekSeed, ekVector, bytesR, sB'', ptA, s'', rngA', bytes2, s''', z, ptB2, sB''', rngR2,
    hcallR, hcallA, hptA, hcallS, -, hx, hz, -, -, hcallB2, hpt, hdr, -, hs3, hsess, hinv3, hc3, hroom3⟩ :=
    Tacenta.UnitLifecycleResponderSecondReceipt.responder_receives_second_message traceB rngR dB2 restB2 hdrawB2
      oracle dA rcE crcE ourA bundleA q hfreshA ptS hroomS rc crc trace dh kem view braid triple aead dhCodec oracleOf
      codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound expected rng0 rng1 s h hq plaintext hroom rng htrace
      d1 d2 rest hdraws bytes s' rng' hcall contractsA agreementsA restA hdrawA rcB crcB contracts hpub hsym hcon
      haead hrt hoeq oracleB oracleOfB braidB agreements ourB storeB hpublish hidentity hdistinct hkem rngB htraceB
      dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR hfreshB
  -- the reply on the same run, for the associated data the responder's model session carries
  obtain ⟨p', ec', dSend', dk', ekSeed', ekVector', bytesR', sB''₁, -, -, -, hidad, -, hcallR', -, -, -, -,
    hrelB'⟩ :=
    Tacenta.UnitLifecycleResponderReply.initiator_first_send_responder_replies rc crc trace dh kem view oracle braid
      triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA
      expected rng0 rng1 s h q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall rcB crcB contracts
      hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish hidentity
      hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR rngR
  rw [hcallR] at hcallR'
  simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hcallR'
  obtain ⟨-, rfl, -⟩ := hcallR'
  set mB := replierSession (responderModelOf dh p) (sliceOf p.braidSecret)
    ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
    (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
    (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB with hmBdef
  have hadB : mB.identityAd = vecOf q.identityAd := by
    have h3 := hsess.identityAd
    have h2 := hrelB'.identityAd
    have hid : sB'''.identity_ad = sB''.identity_ad := by rw [hs3]
    simp only [secondReceiptSession] at h3
    simp only [Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession, responderModelOf, hidad] at h2
    rw [← h3, hid, h2]
  -- the encrypt refinement at `sB'''`, at the responder's oracle with the draws the source holds after the receipt
  obtain ⟨output, hcallR2, hstep⟩ := responder_second_send_refines rcB crcB traceB dh kem view
    { oracleB with draws := traceB rngR2 } braidB triple aead dhCodec (oracleOf_with_draws oracleOfB _) codec
    codewordView hz80 hz32 hzKeys contracts.decrypt.braid.ct1Len mB _ _ (arrayOf ec) (arrayOf q.sparseRoot)
    (arrayOf q.sparseSend) (arrayOf q.sparseReceive) (arrayOf q.dhOut) dSend (oracle.dhPublic dA) x z
    (oracleB.dhPublic dB2) dB2 sB''' hsess hinv3 hc3 ptR2 hroomR2 rngR2 rfl
  -- the model's step: one outcome, the bare second reply frame
  have hstepM := second_reply_model_step view { oracleB with draws := traceB rngR2 } mB
    (Model.Braid.Auth.init 1 (sliceOf p.braidSecret))
    (((Model.Braid.Decoder.new (Model.Braid.headerSize + Model.Braid.macSize)).addChunk
      ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩).addChunk
      ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩)
    (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) (arrayOf q.dhOut) dSend
    (oracle.dhPublic dA) x z (oracleB.dhPublic dB2) dB2 (sliceOf ptR2)
  rw [hstepM] at hstep
  obtain ⟨res, sB4, rngR3⟩ := output
  have hres := hstep.result
  have hsess4 := hstep.session
  simp only at hres hsess4 hcallR2
  cases res with
  | Err err => exact hres.elim
  | Ok bytesR2 =>
    -- the walk of the call: the agreement's send took no draw and returned the agreement as given
    obtain ⟨m, ep, o, b, hsendB, _sparse, _cand, _hdr, _mk, -, hs4⟩ :=
      Tacenta.UnitLifecycleEstablishedEncrypt.encrypt_ok_parts rcB crcB sB''' ptR2 rngR2 bytesR2 sB4 rngR3 hcallR2
    obtain ⟨e, auth, dec, hst⟩ := noHeader_of_refines hsess rfl
    obtain ⟨hr, hb, -, -⟩ := Tacenta.UnitLifecycleResponderReply.braid_send_noHeader rcB crcB sB'''.braid e auth dec
      hst rngR2 _ rngR3 hsendB
    simp only at hb
    subst hb
    rw [hr] at hcallR2
    -- `Session::invariant` after the call, by send preservation at `NoHeaderReceived`
    have hroom1 : CounterRoom sB''' (0 + 1) := hroom3 1 (by simp [Std.U32.max_eq])
    obtain ⟨hinv4, hroom4⟩ := Tacenta.UnitLifecycleSendPreserve.encrypt_keeps_invariant_no_draw agreements.kemClone
      rcB crcB dh oracleB.braidKem view { oracleB with draws := traceB rngR2 } sB''' _ 0 hinv3 hroom1 hsess rfl ptR2
      (sliceOf ptR2) rngR2 bytesR2 sB4 rngR2 hcallR2 (by rw [hstepM]; exact hsess4)
    refine ⟨p, ec, dSend, x, ekSeed, ekVector, bytesR, sB'', ptA, s'', rngA', bytes2, s''', z, ptB2, sB''',
      rngR2, bytesR2, sB4, hcallR, hcallA, hptA, hcallS, hcallB2, hpt, hdr, hx, hz, hinv3, hc3, hcallR2, ?_, ?_,
      hsess4, hinv4, (Tacenta.UnitLifecycleSendPreserve.counterRoom_zero sB4).mp hroom4, ?_⟩
    · rw [hs4]
    · -- the bytes: the model's frame, closed by rewriting so that a wrong key or key name fails fast
      simp only [Tacenta.UnitLifecycleT3.ResultRefines] at hres
      rw [hres, secondReplyFrame_with_draws, hadB]
    · -- the budget, read off the model session after the send
      intro j hj
      exact (Tacenta.UnitLifecycleSendPreserve.counterRoom_iff_model hsess4 j).mpr
        (modelCounterRoom_secondReplier _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj)

end Comp

/-! ## The reach: one run, from `publish` to the responder's second reply -/

section Reach

open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real InitiatorAxiom ResponderAxiom)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitLifecycleResponderFirstFrame (FirstFrameSuccessShape PoolEntry reachStore reachBundle
  publish_reachStore reachStore_distinct heldKemPair zPool InitiatorSecretParts DhAgreeSymmetric FirstKemAgrees)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory AeadRoundTrip)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid)
open Tacenta.UnitLifecycleResponderReply (oracleOf_with_draws)
open Tacenta.UnitLifecycleResponderReplyReceipt (DhPublicNotConstant dhPublicNotConstant_is byteTrace_seed_extra
  two_draws_of_seed_extra)
open Tacenta.UnitLifecycleResponderSecondReceipt (reach_establishment_secret byteTrace_pair)
open Tacenta.UnitLifecycleEstablishedEncrypt (EstablishedEncryptHypotheses EncryptExtraLaws emptyPlaintext)

/-- The run the reach of the second reply exhibits, named so that its pin prints it whole: at an oracle whose KEM is
`K`, the first send of the empty plaintext from `seed ++ extra`, `establish_responder` on its bytes from
`seedB ++ extraB`, the reply, the initiator's receipt of it returning `ptR`, the initiator's second `encrypt` of `ptS`,
the responder's `decrypt` of its bytes returning `ptS`, and the responder's `encrypt` of `ptR2` at the session that
receipt left, from the source it left, returning bytes, leaving that source, writing only the Triple Ratchet and
leaving a session that passes `Session::invariant` and meets `CounterHeadroom`. -/
def SecondReplyRun (K : Model.Braid.Kem) (ourA : lifecycle.Identity) (seed extraB : List Std.U8)
    (ptR ptS ptR2 : Slice Std.U8) : Prop :=
  ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle)
    (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (extra : List Std.U8) (bytes : alloc.vec.Vec Std.U8)
    (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (seedB : List Std.U8) (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8) (storeB' : lifecycle.PrekeyStore)
    (rngB' : List Std.U8) (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session) (ptA : alloc.vec.Vec Std.U8)
    (s'' : lifecycle.Session) (rngA' : List Std.U8) (bytes2 : alloc.vec.Vec Std.U8) (s''' : lifecycle.Session)
    (ptB2 : alloc.vec.Vec Std.U8) (sB''' : lifecycle.Session) (rngR2 : List Std.U8)
    (bytesR2 : alloc.vec.Vec Std.U8) (sB4 : lifecycle.Session),
    oracle.braidKem = K ∧ extra.length = 32 ∧
    lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext (seed ++ extra) =
      ok (core.result.Result.Ok bytes, s', rng') ∧
    lifecycle.PrekeyStore.publish storeB = ok bundle ∧
    lifecycle.establish_responder byteRng byteCrc ourB storeB (alloc.vec.Vec.deref bytes) (seedB ++ extraB) =
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
    lifecycle.Session.encrypt byteRng byteCrc sB' ptR rngB' = ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
    lifecycle.Session.decrypt byteRng byteCrc s' (alloc.vec.Vec.deref bytesR) rng' =
      ok (core.result.Result.Ok ptA, s'', rngA') ∧
    ptA.val = ptR.val ∧
    lifecycle.Session.encrypt byteRng byteCrc s'' ptS rngA' = ok (core.result.Result.Ok bytes2, s''', rngA') ∧
    lifecycle.Session.decrypt byteRng byteCrc sB'' (alloc.vec.Vec.deref bytes2) rngB' =
      ok (core.result.Result.Ok ptB2, sB''', rngR2) ∧
    ptB2.val = ptS.val ∧
    lifecycle.Session.encrypt byteRng byteCrc sB''' ptR2 rngR2 = ok (core.result.Result.Ok bytesR2, sB4, rngR2) ∧
    sB4 = { sB''' with triple := sB4.triple } ∧
    lifecycle.Session.invariant sB4 = ok true ∧ CounterHeadroom sB4

/-- **The reach of the responder's second reply**: at the real constants, under the laws of
`first_send_second_receipt_reachable` (all assumed, `DhPublicNotConstant` included) and no other, for every initiator
identity, every 64-byte seed at whose bytes the model's key generation answers, every 32 further bytes of the
responder's source, and every reply plaintext `ptR`, second plaintext `ptS` and second reply plaintext `ptR2` of at
most 4096 bytes, `SecondReplyRun` holds: the initiator's 32 further bytes are chosen by `DhPublicNotConstant` so that
its new ratchet key is not its first, the responder's 32 further bytes are its draw for the receipt of the second
message, and every hypothesis of `responder_sends_second_reply` holds on the run, which it applies.  Last-resort path
only.  No compiler-trust axiom (the pin). -/
theorem first_send_second_reply_reachable (K : Model.Braid.Kem) (dh : DhView)
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
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none)
    (extraB : List Std.U8) (hextraB : extraB.length = 32)
    (ptR : Slice Std.U8) (hptR : ptR.val.length ≤ 4096) (ptS : Slice Std.U8) (hptS : ptS.val.length ≤ 4096)
    (ptR2 : Slice Std.U8) (hptR2 : ptR2.val.length ≤ 4096) :
    SecondReplyRun K ourA seed extraB ptR ptS ptR2 := by
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
  have hverify : verify_bundle (reachBundle pkb sig1 sig2 kemPk).bundle =
      ok (core.result.Result.Ok ()) :=
    Tacenta.UnitLifecycleEstablishInitiatorShape.verify_successBundle pkb a ha' hcan hprime' sig1 sig2 kemPk
      v v1 hv hs1 hv1 hs2
  -- the establishment, with the bytes of the initiator's ratchet key
  obtain ⟨q, rng1, -, hqct, hqss, -, h⟩ := reach_establishment_secret c ourA pkb a ha' hcan heq' sig1 sig2
    kemPk hverify hag' stream rest ct ss henc'
  -- the initiator's 32 further bytes: a key whose public key is not its first ratchet key
  obtain ⟨sbA, kF, pkF, bF, hkF, hpkF, hbF, hneA⟩ := (dhPublicNotConstant_is.mp hnc) q.ratchetBytes
  set extra := sbA.val with hextradef
  have hextra : extra.length = 32 := by simp [extra]
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
  -- the initiator's draw after its first send: the 32 bytes after the seed, a key that is not its first
  have hdrawA : byteTrace rng' = extra.map Tacenta.SessionUnitBraidT3.u8 :: [] := hrest
  have hfreshA : oracle.dhPublic (extra.map Tacenta.SessionUnitBraidT3.u8) ≠ arrayOf q.ratchetBytes := by
    rw [show extra.map Tacenta.SessionUnitBraidT3.u8 = arrayOf sbA from rfl, hpubOf sbA kF pkF bF hkF hpkF hbF]
    intro hab
    exact hneA (Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes hab)
  have hu : 4294967295 ≤ Usize.max :=
    Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  -- the responder's source: 32 bytes of a key whose public key is not the peer key the initiator holds, then
  -- the 32 bytes its receipt of the second message draws
  obtain ⟨sbB, kFB, pkFB, bFB, hkFB, hpkFB, hbFB, hneB⟩ := (dhPublicNotConstant_is.mp hnc) q.peerRatchetBytes
  have hseedB : sbB.val.length = 32 := by simp
  set seedB := sbB.val with hseedBdef
  let oracleB : Model.Lifecycle.Oracle := { oracle with draws := byteTrace (seedB ++ extraB) }
  have oracleOfB : Tacenta.UnitLifecycleT3.OracleOf byteRng byteCrc dh kem byteTrace oracleB :=
    oracleOf_with_draws H.oracleOf _
  have hdrB : byteTrace (seedB ++ extraB) =
      seedB.map Tacenta.SessionUnitBraidT3.u8 :: [extraB.map Tacenta.SessionUnitBraidT3.u8] :=
    byteTrace_pair seedB extraB hseedB hextraB
  obtain ⟨-, hdisj⟩ := Tacenta.UnitLifecycleResponderFirstReceipt.initiator_first_send_responder_receives byteRng
    byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec
    H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes
    H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session h q rfl emptyPlaintext H.room
    (seed ++ extra) H.trace_eq _ _ _ htr bytes s' rng' hcall byteRng byteCrc contracts hpub hsym hcon haead hrt
    L.optionEq byteTrace oracleB (DecryptOracleOf.of_oracleOf oracleOfB) ag ourB storeB hpublish hidentity
    hdistinct hkem hhead (seedB ++ extraB) rfl _ _ hdrB
  rcases hdisj with ⟨-, e, hrefuse, -⟩ |
    ⟨p, ec, dSend, dk', ekSeed', ekVector', ptB, sB', storeB', rngB', -, -, -, -, -, -, -, -, -, -, hcallB, -,
      hrestB, -⟩
  · exfalso
    rcases hrefuse with ⟨-, hleg⟩ | ⟨-, fp, -, x, hx, -⟩ | ⟨-, -, hne', -⟩
    · simp [storeB, reachStore] at hleg
    · simp [storeB, reachStore] at hx
    · exact hne' (by simp [storeB, reachStore])
  -- the fresh-key premise of the reply's receipt, on this run
  have hfreshB : oracleB.dhPublic (seedB.map Tacenta.SessionUnitBraidT3.u8) ≠ arrayOf q.peerRatchetBytes := by
    show oracle.dhPublic (seedB.map Tacenta.SessionUnitBraidT3.u8) ≠ arrayOf q.peerRatchetBytes
    rw [show seedB.map Tacenta.SessionUnitBraidT3.u8 = arrayOf sbB from rfl, hpubOf sbB kFB pkFB bFB hkFB hpkFB hbFB]
    intro hab
    exact hneB (Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes hab)
  -- the responder's second reply, on this run
  obtain ⟨_p, _ec, _dSend, _x, _ekSeed, _ekVector, bytesR, sB'', ptA, s'', rngA', bytes2, s''', _z, ptB2, sB''',
    rngR2, bytesR2, sB4, hcallR, hcallA, hpt, hcallS, hcallB2, hpt2, -, -, -, -, -, hcallR2, hs4, -, -, hinv4, hc4,
    -⟩ :=
    responder_sends_second_reply ptR2 (by omega) byteTrace rngB' _ [] hrestB oracle _ byteRng byteCrc ourA _ q
      hfreshA ptS (by omega) byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView H.braid H.triple
      H.aead H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes
      H.kemCiphertextLen H.kemCiphertextBound _ _ rng1 q.session H.established rfl emptyPlaintext H.room
      (seed ++ extra) H.trace_eq _ _ _ htr bytes s' rng' hcall contracts.decrypt ag [] hdrawA byteRng byteCrc
      contracts hpub hsym hcon haead hrt L.optionEq oracleB oracleOfB H.braid ag ourB storeB hpublish
      hidentity hdistinct hkem (seedB ++ extraB) rfl _ _ hdrB ptB sB' storeB' rngB' hcallB ptR (by omega) hfreshB
  exact ⟨oracle, _, q, extra, bytes, s', rng', ourB, storeB, seedB, sB', ptB, storeB', rngB', bytesR, sB'', ptA,
    s'', rngA', bytes2, s''', ptB2, sB''', rngR2, bytesR2, sB4, rfl, hextra, hcall, hpublish, hcallB, hcallR,
    hcallA, hpt, hcallS, hcallB2, hpt2, hcallR2, hs4, hinv4, hc4⟩

end Reach

end Tacenta.UnitLifecycleResponderSecondSend

-- The pins `genpins.py` writes after this line print each statement whole: with no cut at depth 50
-- (`pp.deepTerms`) and each omitted proof with its proposition, `(⋯ : P)` (`pp.proofs.withType`). `attest.py`
-- refuses a statement pin that prints a bare `⋯`, and every other `pp` option.
set_option pp.deepTerms true
set_option pp.proofs.withType true

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleResponderSecondSend.second_reply_send_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondSend.second_reply_send_key

/--
info: 'Tacenta.UnitLifecycleResponderSecondSend.secondReplyFrame_with_draws' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondSend.secondReplyFrame_with_draws

/--
info: 'Tacenta.UnitLifecycleResponderSecondSend.second_reply_model_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondSend.second_reply_model_step

/--
info: 'Tacenta.UnitLifecycleResponderSecondSend.modelCounterRoom_secondReplier' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondSend.modelCounterRoom_secondReplier

/--
info: 'Tacenta.UnitLifecycleResponderSecondSend.noHeader_of_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondSend.noHeader_of_refines

/--
info: 'Tacenta.UnitLifecycleResponderSecondSend.responder_second_send_refines' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSecondSend.responder_second_send_refines

/--
info: 'Tacenta.UnitLifecycleResponderSecondSend.responder_sends_second_reply' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSecondSend.responder_sends_second_reply

/--
info: 'Tacenta.UnitLifecycleResponderSecondSend.first_send_second_reply_reachable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSecondSend.first_send_second_reply_reachable

/--
info: Tacenta.UnitLifecycleResponderSecondSend.second_reply_send_key : ∀
  (ec prk k1 k2 d dSend candA xB z newPub2 : Model.State.Key),
  Model.Triple.sendDetailed
      (Tacenta.UnitLifecycleResponderSecondReceipt.responderAfterSecond ec prk k1 k2 d dSend candA xB z newPub2) 0
      none =
    Except.ok
      (Tacenta.UnitLifecycleResponderSecondSend.responderAfterSecondSend ec prk k1 k2 d dSend candA xB z newPub2,
        Tacenta.UnitLifecycleInitiatorSecondSend.secondHeader newPub2,
        Tacenta.UnitLifecycleResponderSecondSend.secondReplyKey ec k2 d dSend xB z)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondSend.second_reply_send_key

/--
info: Tacenta.UnitLifecycleResponderSecondSend.secondReplyFrame_with_draws : ∀ (oracle : Model.Lifecycle.Oracle)
  (draws : List Model.State.Key) (ad : Model.Lifecycle.Bytes) (newPub2 messageKey : Model.State.Key)
  (plaintext : Model.Lifecycle.Bytes),
  Tacenta.UnitLifecycleResponderSecondSend.secondReplyFrame
      { draws := draws, braidKem := oracle.braidKem, dhPublic := oracle.dhPublic, dhAgree := oracle.dhAgree,
        identityValid := oracle.identityValid, aeadSeal := oracle.aeadSeal, aeadOpen := oracle.aeadOpen,
        kemValid := oracle.kemValid, kemEncaps := oracle.kemEncaps, kemDecaps := oracle.kemDecaps,
        sigVerify := oracle.sigVerify, sigSign := oracle.sigSign }
      ad newPub2 messageKey plaintext =
    Tacenta.UnitLifecycleResponderSecondSend.secondReplyFrame oracle ad newPub2 messageKey plaintext
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondSend.secondReplyFrame_with_draws

/--
info: Tacenta.UnitLifecycleResponderSecondSend.second_reply_model_step : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (mB : Model.Lifecycle.Session) (auth : Model.Braid.Auth) (dec : Model.Braid.Decoder)
  (ec prk k1 k2 d dSend candA xB z newPub2 c : Model.State.Key) (pt : Model.Lifecycle.Bytes),
  Model.Lifecycle.encrypt view oracle
      (Tacenta.UnitLifecycleResponderSecondReceipt.secondReceiptSession mB
        (Model.Braid.BraidState.noHeaderReceived 1 auth dec) ec prk k1 k2 d dSend candA xB z newPub2 c)
      pt =
    {
      session :=
        have __src :=
          Tacenta.UnitLifecycleResponderSecondReceipt.secondReceiptSession mB
            (Model.Braid.BraidState.noHeaderReceived 1 auth dec) ec prk k1 k2 d dSend candA xB z newPub2 c;
        {
          triple :=
            Tacenta.UnitLifecycleResponderSecondSend.responderAfterSecondSend ec prk k1 k2 d dSend candA xB z newPub2,
          braid := __src.braid, ratchetPrivate := __src.ratchetPrivate, identityAd := __src.identityAd,
          ourIdentityPublic := __src.ourIdentityPublic, peerIdentityPublic := __src.peerIdentityPublic,
          pendingInitial := __src.pendingInitial, establishedEphemeral := __src.establishedEphemeral },
      result :=
        Except.ok
          (Tacenta.UnitLifecycleResponderSecondSend.secondReplyFrame oracle mB.identityAd newPub2
            (Tacenta.UnitLifecycleResponderSecondSend.secondReplyKey ec k2 d dSend xB z) pt),
      oracle := oracle }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondSend.second_reply_model_step

/--
info: Tacenta.UnitLifecycleResponderSecondSend.modelCounterRoom_secondReplier : ∀ (mB : Model.Lifecycle.Session)
  (auth : Model.Braid.Auth) (dec : Model.Braid.Decoder) (ec prk k1 k2 d dSend candA xB z newPub2 c : Model.State.Key)
  (k : ℕ),
  k + 3 < U32.max →
    Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom
      (have __src :=
        Tacenta.UnitLifecycleResponderSecondReceipt.secondReceiptSession mB
          (Model.Braid.BraidState.noHeaderReceived 1 auth dec) ec prk k1 k2 d dSend candA xB z newPub2 c;
      {
        triple :=
          Tacenta.UnitLifecycleResponderSecondSend.responderAfterSecondSend ec prk k1 k2 d dSend candA xB z newPub2,
        braid := __src.braid, ratchetPrivate := __src.ratchetPrivate, identityAd := __src.identityAd,
        ourIdentityPublic := __src.ourIdentityPublic, peerIdentityPublic := __src.peerIdentityPublic,
        pendingInitial := __src.pendingInitial, establishedEphemeral := __src.establishedEphemeral })
      k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondSend.modelCounterRoom_secondReplier

/--
info: @Tacenta.UnitLifecycleResponderSecondSend.noHeader_of_refines : ∀ {dh : Tacenta.UnitLifecycleT3.DhView}
  {K : Model.Braid.Kem} {s : lifecycle.Session} {m : Model.Lifecycle.Session} {e : ℕ} {a : Model.Braid.Auth}
  {dec : Model.Braid.Decoder},
  Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
    m.braid = Model.Braid.BraidState.noHeaderReceived e a dec →
      ∃ e' auth d, s.braid.state = tacenta_braid.State.NoHeaderReceived e' auth d
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondSend.noHeader_of_refines

/--
info: @Tacenta.UnitLifecycleResponderSecondSend.responder_second_send_refines : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
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
                  Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Std.Array U8 32#usize) →
                    Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
                        (Std.Array U8 32#usize × Std.Array U8 32#usize × Std.Array U8 16#usize) →
                      Tacenta.SessionUnitBraidT1.Ct1LenTotal →
                        ∀ (mB : Model.Lifecycle.Session) (auth : Model.Braid.Auth) (dec : Model.Braid.Decoder)
                          (ec prk k1 k2 d dSend candA xB z newPub2 c : Model.State.Key) (sB : lifecycle.Session),
                          Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem sB
                              (Tacenta.UnitLifecycleResponderSecondReceipt.secondReceiptSession mB
                                (Model.Braid.BraidState.noHeaderReceived 1 auth dec) ec prk k1 k2 d dSend candA xB z
                                newPub2 c) →
                            sB.invariant = ok true →
                              Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB →
                                ∀ (plaintext : Slice U8),
                                  102 + ((↑plaintext).length + 48) ≤ Usize.max →
                                    ∀ (rng : R),
                                      trace rng = oracle.draws →
                                        Tacenta.UnitLifecycleT3.PublicEncryptWitness rc crc trace dh oracle.braidKem
                                          view oracle sB
                                          (Tacenta.UnitLifecycleResponderSecondReceipt.secondReceiptSession mB
                                            (Model.Braid.BraidState.noHeaderReceived 1 auth dec) ec prk k1 k2 d dSend
                                            candA xB z newPub2 c)
                                          plaintext rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondSend.responder_second_send_refines

/--
info: @Tacenta.UnitLifecycleResponderSecondSend.responder_sends_second_reply : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {R E F : Type} (ptR2 : Slice U8),
  102 + ((↑ptR2).length + 48) ≤ Usize.max →
    ∀ (traceB : F → List Model.Lifecycle.Key) (rngR : F) (dB2 : Model.Lifecycle.Key)
      (restB2 : List Model.Lifecycle.Key),
      traceB rngR = dB2 :: restB2 →
        ∀ (oracle : Model.Lifecycle.Oracle) (dA : Model.Lifecycle.Key) (rcE : rand_core_1.RngCore E)
          (crcE : rand_core_1.CryptoRng E) (ourA : lifecycle.Identity) (bundleA : lifecycle.PublishedBundle)
          (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcE crcE ourA bundleA),
          oracle.dhPublic dA ≠ Tacenta.UnitLifecycleT3.arrayOf q.ratchetBytes →
            ∀ (ptS : Slice U8),
              102 + ((↑ptS).length + 48) ≤ Usize.max →
                ∀ (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
                  (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
                  (view : Model.Lifecycle.CodewordView),
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
                                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc
                                          trace →
                                        Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem →
                                          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                                            Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                                              ∀ (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                                                (s : lifecycle.Session),
                                                lifecycle.establish_initiator_for rcE crcE ourA bundleA expected rng0 =
                                                    ok (core.result.Result.Ok s, rng1) →
                                                  s = q.session →
                                                    ∀ (plaintext : Slice U8),
                                                      (↑plaintext).length + 65770 ≤ Usize.max →
                                                        ∀ (rng : R),
                                                          trace rng = oracle.draws →
                                                            ∀ (d1 d2 : Model.Lifecycle.Key)
                                                              (rest : List Model.Lifecycle.Key),
                                                              trace rng = d1 :: d2 :: rest →
                                                                ∀ (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session)
                                                                  (rng' : R),
                                                                  lifecycle.Session.encrypt rc crc s plaintext rng =
                                                                      ok (core.result.Result.Ok bytes, s', rng') →
                                                                    Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc →
                                                                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                          oracle.braidKem →
                                                                        ∀ (restA : List Model.Lifecycle.Key),
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
                                                                                            (oracleB :
                                                                                              Model.Lifecycle.Oracle),
                                                                                            Tacenta.UnitLifecycleT3.OracleOf
                                                                                                rcB crcB dh kem traceB
                                                                                                oracleB →
                                                                                              Tacenta.UnitLifecycleT3.BraidSendRefinementContracts
                                                                                                  rcB oracleB.braidKem →
                                                                                                Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                                                    oracleB.braidKem →
                                                                                                  ∀
                                                                                                    (ourB :
                                                                                                      lifecycle.Identity)
                                                                                                    (storeB :
                                                                                                      lifecycle.PrekeyStore),
                                                                                                    storeB.publish =
                                                                                                        ok bundleA →
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
                                                                                                            ∀
                                                                                                              (rngB :
                                                                                                                F),
                                                                                                              traceB
                                                                                                                    rngB =
                                                                                                                  oracleB.draws →
                                                                                                                ∀
                                                                                                                  (dB :
                                                                                                                    Model.Lifecycle.Key)
                                                                                                                  (restB :
                                                                                                                    List
                                                                                                                      Model.Lifecycle.Key),
                                                                                                                  traceB
                                                                                                                        rngB =
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
                                                                                                                      (rngB' :
                                                                                                                        F),
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
                                                                                                                            oracleB.dhPublic
                                                                                                                                  dB ≠
                                                                                                                                Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                  q.peerRatchetBytes →
                                                                                                                              ∃
                                                                                                                                p
                                                                                                                                ec
                                                                                                                                dSend
                                                                                                                                x
                                                                                                                                ekSeed
                                                                                                                                ekVector
                                                                                                                                bytesR
                                                                                                                                sB''
                                                                                                                                ptA
                                                                                                                                s''
                                                                                                                                rngA'
                                                                                                                                bytes2
                                                                                                                                s'''
                                                                                                                                z
                                                                                                                                ptB2
                                                                                                                                sB'''
                                                                                                                                rngR2
                                                                                                                                bytesR2
                                                                                                                                sB4,
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
                                                                                                                                        lifecycle.Session.decrypt
                                                                                                                                              rcB
                                                                                                                                              crcB
                                                                                                                                              sB''
                                                                                                                                              bytes2.deref
                                                                                                                                              rngR =
                                                                                                                                            ok
                                                                                                                                              (core.result.Result.Ok
                                                                                                                                                  ptB2,
                                                                                                                                                sB''',
                                                                                                                                                rngR2) ∧
                                                                                                                                          ↑ptB2 =
                                                                                                                                              ↑ptS ∧
                                                                                                                                            traceB
                                                                                                                                                  rngR2 =
                                                                                                                                                restB2 ∧
                                                                                                                                              oracle.dhAgree
                                                                                                                                                    dA
                                                                                                                                                    (oracleB.dhPublic
                                                                                                                                                      dB) =
                                                                                                                                                  some
                                                                                                                                                    x ∧
                                                                                                                                                oracleB.dhAgree
                                                                                                                                                      dB2
                                                                                                                                                      (oracle.dhPublic
                                                                                                                                                        dA) =
                                                                                                                                                    some
                                                                                                                                                      z ∧
                                                                                                                                                  sB'''.invariant =
                                                                                                                                                      ok
                                                                                                                                                        true ∧
                                                                                                                                                    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                                                                                        sB''' ∧
                                                                                                                                                      lifecycle.Session.encrypt
                                                                                                                                                            rcB
                                                                                                                                                            crcB
                                                                                                                                                            sB'''
                                                                                                                                                            ptR2
                                                                                                                                                            rngR2 =
                                                                                                                                                          ok
                                                                                                                                                            (core.result.Result.Ok
                                                                                                                                                                bytesR2,
                                                                                                                                                              sB4,
                                                                                                                                                              rngR2) ∧
                                                                                                                                                        sB4 =
                                                                                                                                                            {
                                                                                                                                                              triple :=
                                                                                                                                                                sB4.triple,
                                                                                                                                                              braid :=
                                                                                                                                                                sB'''.braid,
                                                                                                                                                              ratchet_private :=
                                                                                                                                                                sB'''.ratchet_private,
                                                                                                                                                              identity_ad :=
                                                                                                                                                                sB'''.identity_ad,
                                                                                                                                                              our_identity_public :=
                                                                                                                                                                sB'''.our_identity_public,
                                                                                                                                                              peer_identity_public :=
                                                                                                                                                                sB'''.peer_identity_public,
                                                                                                                                                              pending_initial :=
                                                                                                                                                                sB'''.pending_initial,
                                                                                                                                                              established_ephemeral :=
                                                                                                                                                                sB'''.established_ephemeral } ∧
                                                                                                                                                          Tacenta.UnitLifecycleT3.vecOf
                                                                                                                                                                bytesR2 =
                                                                                                                                                              Tacenta.UnitLifecycleResponderSecondSend.secondReplyFrame
                                                                                                                                                                oracleB
                                                                                                                                                                (Tacenta.UnitLifecycleT3.vecOf
                                                                                                                                                                  q.identityAd)
                                                                                                                                                                (oracleB.dhPublic
                                                                                                                                                                  dB2)
                                                                                                                                                                (Tacenta.UnitLifecycleResponderSecondSend.secondReplyKey
                                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                    ec)
                                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                    q.sparseReceive)
                                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                    q.dhOut)
                                                                                                                                                                  dSend
                                                                                                                                                                  x
                                                                                                                                                                  z)
                                                                                                                                                                (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                                                  ptR2) ∧
                                                                                                                                                            Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                                                                                dh
                                                                                                                                                                oracleB.braidKem
                                                                                                                                                                sB4
                                                                                                                                                                (have
                                                                                                                                                                  __src :=
                                                                                                                                                                  Tacenta.UnitLifecycleResponderSecondReceipt.secondReceiptSession
                                                                                                                                                                    (Tacenta.UnitLifecycleResponderSecondReceipt.replierSession
                                                                                                                                                                      (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                                                                                                        dh
                                                                                                                                                                        p)
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
                                                                                                                                                                      dB)
                                                                                                                                                                    (Model.Braid.BraidState.noHeaderReceived
                                                                                                                                                                      1
                                                                                                                                                                      (Model.Braid.Auth.init
                                                                                                                                                                        1
                                                                                                                                                                        (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                                                          p.braidSecret))
                                                                                                                                                                      (((Model.Braid.Decoder.new
                                                                                                                                                                                (Model.Braid.headerSize +
                                                                                                                                                                                  Model.Braid.macSize)).addChunk
                                                                                                                                                                            {
                                                                                                                                                                              source :=
                                                                                                                                                                                Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                                                                                  oracle.braidKem
                                                                                                                                                                                  (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                                                                    q.auth)
                                                                                                                                                                                  ekSeed
                                                                                                                                                                                  ekVector,
                                                                                                                                                                              index :=
                                                                                                                                                                                0 }).addChunk
                                                                                                                                                                        {
                                                                                                                                                                          source :=
                                                                                                                                                                            Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                                                                              oracle.braidKem
                                                                                                                                                                              (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                                                                q.auth)
                                                                                                                                                                              ekSeed
                                                                                                                                                                              ekVector,
                                                                                                                                                                          index :=
                                                                                                                                                                            1 }))
                                                                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                      ec)
                                                                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                      q.sparseRoot)
                                                                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                      q.sparseSend)
                                                                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                      q.sparseReceive)
                                                                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                      q.dhOut)
                                                                                                                                                                    dSend
                                                                                                                                                                    (oracle.dhPublic
                                                                                                                                                                      dA)
                                                                                                                                                                    x
                                                                                                                                                                    z
                                                                                                                                                                    (oracleB.dhPublic
                                                                                                                                                                      dB2)
                                                                                                                                                                    dB2;
                                                                                                                                                                {
                                                                                                                                                                  triple :=
                                                                                                                                                                    Tacenta.UnitLifecycleResponderSecondSend.responderAfterSecondSend
                                                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                        ec)
                                                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                        q.sparseRoot)
                                                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                        q.sparseSend)
                                                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                        q.sparseReceive)
                                                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                                        q.dhOut)
                                                                                                                                                                      dSend
                                                                                                                                                                      (oracle.dhPublic
                                                                                                                                                                        dA)
                                                                                                                                                                      x
                                                                                                                                                                      z
                                                                                                                                                                      (oracleB.dhPublic
                                                                                                                                                                        dB2),
                                                                                                                                                                  braid :=
                                                                                                                                                                    __src.braid,
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
                                                                                                                                                              sB4.invariant =
                                                                                                                                                                  ok
                                                                                                                                                                    true ∧
                                                                                                                                                                Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                                                                                                    sB4 ∧
                                                                                                                                                                  ∀
                                                                                                                                                                    (j :
                                                                                                                                                                      ℕ),
                                                                                                                                                                    j +
                                                                                                                                                                          3 <
                                                                                                                                                                        U32.max →
                                                                                                                                                                      Tacenta.UnitLifecycleSendPreserve.CounterRoom
                                                                                                                                                                        sB4
                                                                                                                                                                        j
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondSend.responder_sends_second_reply

/--
info: Tacenta.UnitLifecycleResponderSecondSend.first_send_second_reply_reachable : ∀ (K : Model.Braid.Kem)
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
                                  K.keyGen
                                        (Model.Lifecycle.braidRandomness
                                          (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠
                                      none →
                                    ∀ (extraB : List U8),
                                      extraB.length = 32 →
                                        ∀ (ptR : Slice U8),
                                          (↑ptR).length ≤ 4096 →
                                            ∀ (ptS : Slice U8),
                                              (↑ptS).length ≤ 4096 →
                                                ∀ (ptR2 : Slice U8),
                                                  (↑ptR2).length ≤ 4096 →
                                                    Tacenta.UnitLifecycleResponderSecondSend.SecondReplyRun K ourA seed
                                                      extraB ptR ptS ptR2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondSend.first_send_second_reply_reachable

/--
info: def Tacenta.UnitLifecycleResponderSecondSend.responderAfterSecondSend : Model.State.Key →
  Model.State.Key →
    Model.State.Key →
      Model.State.Key →
        Model.State.Key →
          Model.State.Key →
            Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.Triple.State :=
fun ec prk k1 k2 d dSend candA xB z newPub2 =>
  {
    classical :=
      { dhsPub := newPub2, dhrPub := some candA,
        rk :=
          (Model.State.kdfRk
              (Model.State.kdfRk
                  (Model.State.kdfRk (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 dSend
                      Model.State.LabelSet.tacenta).1
                  xB Model.State.LabelSet.tacenta).1
              z Model.State.LabelSet.tacenta).1,
        cks :=
          some
            (Model.State.kdfCk
                (Model.State.kdfRk
                    (Model.State.kdfRk
                        (Model.State.kdfRk (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 dSend
                            Model.State.LabelSet.tacenta).1
                        xB Model.State.LabelSet.tacenta).1
                    z Model.State.LabelSet.tacenta).2).1,
        ckr :=
          some
            (Model.State.kdfCk
                (Model.State.kdfRk
                    (Model.State.kdfRk (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 dSend
                        Model.State.LabelSet.tacenta).1
                    xB Model.State.LabelSet.tacenta).2).1,
        ns := 1, nr := 1, pn := 1, skipped := [], events := 2, labels := Model.State.LabelSet.tacenta },
    postQuantum :=
      { rk := prk, epoch := 0,
        chains :=
          [(0,
              { send := some { ck := (Model.SparseRatchet.kdfCk (Model.SparseRatchet.kdfCk k2 1).1 2).1, n := 2 },
                receive :=
                  some { ck := (Model.SparseRatchet.kdfCk (Model.SparseRatchet.kdfCk k1 1).1 2).1, n := 2 } })],
        skipped := [], direction := Model.SparseRatchet.Direction.b2a } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderSecondSend.responderAfterSecondSend

/--
info: def Tacenta.UnitLifecycleResponderSecondSend.secondReplyKey : Model.State.Key →
  Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key :=
fun ec k2 d dSend xB z =>
  Model.TripleRatchet.combine
    (Model.State.kdfCk
        (Model.State.kdfRk
            (Model.State.kdfRk
                (Model.State.kdfRk (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 dSend
                    Model.State.LabelSet.tacenta).1
                xB Model.State.LabelSet.tacenta).1
            z Model.State.LabelSet.tacenta).2).2
    (Model.SparseRatchet.kdfCk (Model.SparseRatchet.kdfCk k2 1).1 2).2
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderSecondSend.secondReplyKey

/--
info: def Tacenta.UnitLifecycleResponderSecondSend.secondReplyComposite : Model.State.Key → Model.CompositeHeader.Composite :=
fun newPub2 =>
  { dh := newPub2, pn := UInt32.ofNat 1, n := UInt32.ofNat 0, pqEpoch := UInt64.ofNat 0, pqN := UInt64.ofNat 2,
    agEpoch := UInt64.ofNat 1, agType := Model.CompositeHeader.AgreementType.none, agChunk := none }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderSecondSend.secondReplyComposite

/--
info: def Tacenta.UnitLifecycleResponderSecondSend.secondReplyFrame : Model.Lifecycle.Oracle →
  Model.Lifecycle.Bytes → Model.State.Key → Model.State.Key → Model.Lifecycle.Bytes → Model.Lifecycle.Bytes :=
fun oracle ad newPub2 messageKey plaintext =>
  Model.CompositeHeader.encodeMessage (Tacenta.UnitLifecycleResponderSecondSend.secondReplyComposite newPub2)
    (oracle.aeadSeal (Model.State.messageKeys messageKey Model.State.LabelSet.tacenta).1
      (Model.State.messageKeys messageKey Model.State.LabelSet.tacenta).2.1
      (Model.State.messageKeys messageKey Model.State.LabelSet.tacenta).2.2 plaintext
      (Model.Messages.concatAd ad
        (Model.CompositeHeader.encode (Tacenta.UnitLifecycleResponderSecondSend.secondReplyComposite newPub2))))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderSecondSend.secondReplyFrame

/--
info: def Tacenta.UnitLifecycleResponderSecondSend.SecondReplyRun : Model.Braid.Kem →
  lifecycle.Identity → List U8 → List U8 → Slice U8 → Slice U8 → Slice U8 → Prop :=
fun K ourA seed extraB ptR ptS ptR2 =>
  ∃ oracle bundle q extra bytes s' rng' ourB storeB seedB sB' ptB storeB' rngB' bytesR sB'' ptA s'' rngA' bytes2 s'''
    ptB2 sB''' rngR2 bytesR2 sB4,
    oracle.braidKem = K ∧
      extra.length = 32 ∧
        lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
              Tacenta.UnitLifecycleIntegrationScreen.byteCrc q.session
              Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext (seed ++ extra) =
            ok (core.result.Result.Ok bytes, s', rng') ∧
          storeB.publish = ok bundle ∧
            lifecycle.establish_responder Tacenta.UnitLifecycleIntegrationScreen.byteRng
                  Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourB storeB bytes.deref (seedB ++ extraB) =
                ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
              lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                    Tacenta.UnitLifecycleIntegrationScreen.byteCrc sB' ptR rngB' =
                  ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
                lifecycle.Session.decrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                      Tacenta.UnitLifecycleIntegrationScreen.byteCrc s' bytesR.deref rng' =
                    ok (core.result.Result.Ok ptA, s'', rngA') ∧
                  ↑ptA = ↑ptR ∧
                    lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                          Tacenta.UnitLifecycleIntegrationScreen.byteCrc s'' ptS rngA' =
                        ok (core.result.Result.Ok bytes2, s''', rngA') ∧
                      lifecycle.Session.decrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc sB'' bytes2.deref rngB' =
                          ok (core.result.Result.Ok ptB2, sB''', rngR2) ∧
                        ↑ptB2 = ↑ptS ∧
                          lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                Tacenta.UnitLifecycleIntegrationScreen.byteCrc sB''' ptR2 rngR2 =
                              ok (core.result.Result.Ok bytesR2, sB4, rngR2) ∧
                            sB4 =
                                { triple := sB4.triple, braid := sB'''.braid, ratchet_private := sB'''.ratchet_private,
                                  identity_ad := sB'''.identity_ad, our_identity_public := sB'''.our_identity_public,
                                  peer_identity_public := sB'''.peer_identity_public,
                                  pending_initial := sB'''.pending_initial,
                                  established_ephemeral := sB'''.established_ephemeral } ∧
                              sB4.invariant = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB4
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderSecondSend.SecondReplyRun
