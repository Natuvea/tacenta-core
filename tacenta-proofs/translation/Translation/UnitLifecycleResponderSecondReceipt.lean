import Translation.UnitLifecycleInitiatorSecondMessage

/-!
# The responder receives the initiator's second message: `Session::decrypt` at the session after its reply

`UnitLifecycleInitiatorSecondMessage` shows the initiator's second `Session::encrypt`, at the session `s''` its receipt
of the responder's reply returned, on one run from the initiator's establishment: it returns `bytes2`, the bare second
frame carrying the header's chunk at index 1.  `UnitLifecycleSendPreserve` shows that the responder's session `sB''`,
the one its reply's `encrypt` left on the same run, passes `Session::invariant` and meets the four ceilings.  This module
takes `bytes2` to the responder on that run: its public `Session::decrypt` at `sB''`, from the source `rngR` the reply
left (the reply takes no draw).  The chain is one run: the initiator's first send, the responder's receipt of it
(`sB'`), the responder's reply (`sB''`), the initiator's receipt of the reply (`s''`), the initiator's second send
(`bytes2`), the responder's receipt of `bytes2` (`sB'''`).

## How

* `responderAfterSecond`, `second_receive_key`, `second_receive_stale`, `second_receipt_model_outcomes` (model only):
  the model Triple's receive of the second message's header (`secondHeader candA`: ratchet key `candA`, previous chain
  length 1, message number 0, sparse epoch 0 and number 2) at the responder after its reply (`replierAfterSend`) takes
  one Diffie-Hellman step on `candA` when it is not the initiator's first ratchet key `a4` the responder holds as its
  peer key, with nothing to skip (the responder's receiving chain is at 1, the header's previous chain length), and
  derives the key the initiator's second send used (`secondKey`); when `candA` is `a4` no step is taken and the message
  number 0 is below the responder's counter 1, so the receive refuses `outOfOrder`.  The model's public `decrypt` of the
  second frame there has exactly the outcomes listed in `second_receipt_model_outcomes`.  The model agreement at
  `noHeaderReceived`, holding the first header chunk, takes the second and still waits (two of three chunks).
* `agreement_swap`, `second_codeword` (bridges): the responder's first agreement on the second message is the initiator's
  agreement `x` with the reply's key, by `DhAgreeSymmetric` (the responder's ratchet key is the one whose public key the
  reply carried: clause (a) of `Session::invariant` at `sB''`); the header's chunk at index 1 is a codeword of the header
  source (the real encoder's second `next_chunk`, through `EncoderRefines`).
* `established_responder_decoder_small` (code walk): the decoder the agreement holds at the session `establish_responder`
  returns holds at most one chunk; the reply keeps the agreement, so the same holds at `sB''`.  This is the scope
  `decrypt_keeps_invariant_in_order` takes (at most one chunk held before the receive).
* `second_receipt_run_inputs`: the inputs of the decrypt refinement at `sB''`, at the view that attributes the frame's
  codeword at index 1 to the header source (`attributedView`, a second attribution on the same base view as the first
  receipt's): the chunk relation, `HonestChunk` (the chunk fits the decoder, which holds the same source's chunk at index
  0) and the responder's draw.
* `responder_receives_second_message_two_outcomes` composes them on the run: the second message from
  `initiator_sends_second_message`; the reply's keys, the identity data and the relation at `sB''` from
  `initiator_first_send_responder_replies` on the same call (the two theorems name one `sB''`: the reply's `encrypt` is a
  function of its inputs); the invariant and the ceilings at `sB''` from `initiator_first_send_responder_reply_admissible`;
  the refinement of the public `decrypt` from `decrypt_refines_ratchet_frame_of_counter_headroom` at the responder's
  oracle with the draws its source holds; the model's step from `second_receipt_model_outcomes`, whose `Handshake` and
  `Aead` arms `DhAgreeContributory` and `AeadRoundTrip` exclude.
* `responder_receives_second_message` adds the per-run premise `hfreshA` and applies `decrypt_keeps_invariant_in_order`
  (`UnitLifecycleReceivePreserve`) at `sB''`: the model step is an in-order receive step (`secondReceipt_inOrderStep`),
  the decoder holds one chunk before the call, and the budget at `sB''` is read off its model session
  (`modelCounterRoom_replier`).

## The statements

* `responder_receives_second_message_two_outcomes`: under the hypotheses of `initiator_sends_second_message` and the
  per-run premise that the responder's source after its reply holds a draw `dB2`, the run's conjuncts hold (the reply's
  `encrypt` at `sB'` returning `bytesR` and `sB''`, the initiator's `decrypt` of it returning `Ok ptA` with the bytes of
  `ptR`, the initiator's second `encrypt` at `s''` returning `bytes2` and leaving its source, `bytes2` as `secondFrame`, the
  initiator's agreement `x`), `sB''` refines the model session after the reply (`replierSession`), keeps the agreement
  `establish_responder` left, passes `Session::invariant` and meets `CounterHeadroom`, and the responder's public
  `decrypt` of `bytes2` at `sB''` from `rngR` returns, takes exactly the draw `dB2`, and either
  * refuses `Triple(Classical(OutOfOrder))` with the session unchanged, exactly when the initiator's new ratchet key is
    its first ratchet key (`oracle.dhPublic dA = arrayOf q.ratchetBytes`), or
  * returns `Ok ptB2` with `ptB2` the bytes of `ptS`, clears the pending initial message, writes only the Triple
    Ratchet, the agreement and the ratchet key, and its session refines `secondReceiptSession` (the Triple
    `responderAfterSecond`, the header decoder holding the chunks at index 0 and 1 of the header source).
* `responder_receives_second_message`: adding only the per-run premise `hfreshA` (the initiator's new ratchet key is not
  its first), the second arm, with `Session::invariant` and `CounterHeadroom` at `sB'''` and room for every `j` with
  `j + 3 < u32::MAX` further operations (`CounterRoom`).
* `first_send_second_receipt_reachable`, `first_send_second_receipt_stale_reachable` (through
  `second_receipt_reach_run`): at the real constants under the laws of `first_send_second_message_reachable`, for every
  initiator identity, every 64-byte seed at whose bytes the model's key generation answers, every 32 further bytes of the
  responder's source and every reply and second plaintext of at most 4096 bytes, there is a run on which the responder's
  `decrypt` of the second message returns `ptS` and leaves a session passing `Session::invariant` and the ceilings
  (`SecondReceiptRun`, the initiator's 32 further bytes chosen by `DhPublicNotConstant`), and a run on which it refuses
  `Triple(Classical(OutOfOrder))` with the session unchanged (`SecondReceiptStaleRun`, the initiator's 32 further bytes
  those of its own first ratchet key).

## Laws and premises

No new law.  The two headlines use the laws `initiator_sends_second_message` already takes, with the roles swapped:
`DhAgreeSymmetric` (the responder's first agreement), `DhAgreeContributory` (the responder's draw), `AeadRoundTrip` (the
initiator seals, the responder opens) and `DhPublicValid`.  New per-run premises: the responder's source after its reply
holds a draw `dB2` (both headlines) and `hfreshA` (success only): the public key of the initiator's draw `dA` (its new
ratchet key) is not its first ratchet key.  `hfreshA` is a condition on the run, not a law: it fails when the initiator's
draw gives its first ratchet key back, and then the responder refuses the second message
(`first_send_second_receipt_stale_reachable` reaches that refusal).  The decoder scope of the receive preservation (at
most one chunk held before the call) and its in-order scope are computed on the run, not assumed.  No premise names a
platform width, so each result holds on 32- and 64-bit targets.  The reaches take the laws of
`first_send_second_message_reachable` and no other.

At `sB''` the responder's agreement is at `NoHeaderReceived`; the second chunk does not complete the 96-byte header (two
of three chunks), so the model's step runs no encapsulation, decapsulation, key generation or header check (the code's
`Braid::receive` likewise, by reading the generated code; no theorem here states it), and no fact relating the two
parties' Braid KEMs is used by this step (the run's premises still include `FirstKemAgrees`, about the prekey
encapsulation of the first message). The records the decrypt refinement takes for every state
(`DecryptRatchetAgreements` at the responder oracle's KEM) are the ones the first receipt already takes.

## Trust

Every result here rests on the kernel and opaque constants only, with no compiler-trust axiom (pins below); the
headlines apply the encrypt and decrypt refinements through the theorems they compose, whose nine `native_decide`
constants are kernel proofs since 2026-10-21. The statement pins of the two headlines and of `second_receipt_reach_run`
print the whole statement: the module sets `pp.deepTerms true` and `pp.proofs.withType true` before its pins, without
which Lean cut them off with `⋯` (the new per-run premises are placed first).  The two reaches print in full too: their
conclusions are the definitions `SecondReceiptRun` and `SecondReceiptStaleRun`, whose `#print` pins hold the whole runs.
A printed pin is still not the whole elaborated statement (instance arguments, coercion functions, implicit arguments
and the binder types of `∃` and `fun` are not printed), so that the pinned statement is the right one is decided by
reading.  Of the success headline's conclusion, the run consumes its four calls, the plaintext equation and
`Session::invariant` and `CounterHeadroom` at `sB'''`; its other conjuncts (the reply receipt's plaintext, the frame
equation of `bytes2`, the agreements `x` and `z`, the invariant and the ceilings at `sB''`, the draw equation, the
cleared pending initial message, the frame equation of `sB'''`, its relation to the model and the budget) are pinned
and used by no later proof.

## Non-vacuity

No law is added, so `reply_receipt_laws_model` still puts every law the reaches take in one toy interpretation,
`InterpO.modelReply`.  `first_send_second_receipt_reachable` exhibits, at the real constants under those laws, a run at
which every hypothesis of `responder_receives_second_message` holds and the responder's `decrypt` returns the second
plaintext; `first_send_second_receipt_stale_reachable` exhibits one at which the stale arm of the two-outcome theorem is
taken.  The laws are assumed at the real constants, not shown of them.

## What it does not show

* A second reply (the responder's next `encrypt` at `sB'''`; shown, on the same run, in
  `UnitLifecycleResponderSecondSend`) and its receipt, the header's third chunk, the responder's
  first sampling send and every later step; the responder's check of the completed encapsulation key, the first step
  at which both parties' KEMs act on one key pair.
* That a tampered, foreign or replayed second frame is refused: no AEAD authenticity law is assumed, and the `Aead` arm
  is the open of the initiator's own seal, excluded by `AeadRoundTrip`.
* Delivery out of order, a skipped or stored key, or the decoder holding more than one chunk before a receive.
* That the budget is exact at `sB'''`: room for every `j` with `j + 3 < u32::MAX` is what the composition derives (the
  clock at `sB'''` is 2, by reading; exactness also follows from the success headline's relation conjunct through
  `counterRoom_iff_model`, which no theorem here states); more room is not claimed.
* That the code's agreement or key pair after the call equals the one before: they refine the same model values.
* That `hfreshA` or the draw holds of a run with an honest random source: they are premises, and no probability is
  claimed.
* A restored copy of `sB''` or `sB'''`; the one-time path in a run (the reaches take the last-resort path only).
* That the related model sessions hold only bytes the parties received (the responder's relations are at views that
  attribute the received codewords).
* That the real primitives meet the boundary records or the laws (`KemCloneAgrees`, `AeadRoundTrip`,
  `DhAgreeContributory`, `DhAgreeSymmetric`, `DhPublicValid`, `DhPublicNotConstant`), that ML-KEM decapsulation agrees on
  a run (`FirstKemAgrees`), or `PrekeyIdsDistinct` from `PrekeyStore::invariant`; the model's own `establishResponder`
  equality.
* That `Session::invariant` says a session is reachable: it is a predicate on fields.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit

namespace Tacenta.UnitLifecycleResponderSecondReceipt

open Tacenta.UnitLifecycleT3 (DhView DhCodecOf KemView arrayOf vecOf sliceOf SessionRefines OracleOf)

/-! ## The model's receipt of the second message -/

section Model
open Model.State (Key)
open Tacenta.UnitLifecycleResponderReply (replierAfterSend)
open Tacenta.UnitLifecycleInitiatorSecondSend (secondHeader secondKey)

/-- The responder's Triple after it receives the initiator's second message: one Diffie-Hellman step on the initiator's
new ratchet key `candA` from the root its reply left (agreement `xB` for the receiving chain, then `z` with the fresh key
`newPub2` for the sending chain), the previous chain length 1 (the reply), the receiving chain stepped once, clock 2; the
sparse receiving chain of `k1` stepped from number 1 to 2. -/
def responderAfterSecond (ec prk k1 k2 d dSend candA xB z newPub2 : Key) : Model.Triple.State :=
  { classical :=
      { dhsPub := newPub2, dhrPub := some candA,
        rk := (Model.State.kdfRk (Model.State.kdfRk
          (Model.State.kdfRk (Model.State.kdfRk ec d .tacenta).1 dSend .tacenta).1 xB .tacenta).1 z .tacenta).1,
        cks := some (Model.State.kdfRk (Model.State.kdfRk
          (Model.State.kdfRk (Model.State.kdfRk ec d .tacenta).1 dSend .tacenta).1 xB .tacenta).1 z .tacenta).2,
        ckr := some (Model.State.kdfCk (Model.State.kdfRk
          (Model.State.kdfRk (Model.State.kdfRk ec d .tacenta).1 dSend .tacenta).1 xB .tacenta).2).1,
        ns := 0, nr := 1, pn := 1, skipped := [], events := 2, labels := .tacenta }
    postQuantum :=
      { rk := prk, epoch := 0,
        chains :=
          [(0, { send := some ⟨(Model.SparseRatchet.kdfCk k2 1).1, 1⟩
                 receive := some ⟨(Model.SparseRatchet.kdfCk (Model.SparseRatchet.kdfCk k1 1).1 2).1, 2⟩ })],
        skipped := [], direction := .b2a } }

/-- **The model's receive of the second message at the responder after its reply, on a new ratchet key**: when the
second message's ratchet key `candA` is not the peer key `a4` the responder holds, the receive of `secondHeader candA`
skips nothing (the header's previous chain length is the responder's counter, 1), takes one Diffie-Hellman step and
succeeds with the key the initiator's second send used, `secondKey` of the root `(kdfRk ec d).1`, and successor
`responderAfterSecond`.  Hypothesis-free beyond `candA ≠ a4`. -/
theorem second_receive_key (ec prk k1 k2 a4 d dSend newPub candA xB z newPub2 : Key) (hne : candA ≠ a4) :
    Model.Triple.receiveDetailed (replierAfterSend ec prk k1 k2 a4 d dSend newPub) (secondHeader candA) xB z
        newPub2 none =
      .ok (responderAfterSecond ec prk k1 k2 d dSend candA xB z newPub2,
        secondKey (Model.State.kdfRk ec d .tacenta).1 k1 dSend xB) := by
  simp [Model.Triple.receiveDetailed, Model.Ratchet.receiveDetailed, Model.Ratchet.trySkipped,
    Model.Ratchet.skipMessageKeysDetailed, Model.State.skipMessageKeys, Model.Ratchet.dhRatchet,
    Model.SparseRatchet.receiveDetailed, Model.SparseRatchet.maybeAdvanceReceiveDetailed,
    Model.SparseRatchet.maybeAdvanceDetailed, Model.SparseRatchet.trySkipped,
    Model.SparseRatchet.skipMessageKeysDetailed, Model.SparseRatchet.skipMessageKeys,
    Model.SparseRatchet.findChains, Model.SparseRatchet.setChains, replierAfterSend, secondHeader,
    responderAfterSecond, secondKey, Model.State.ageStore, Model.State.u32Max, Model.SparseRatchet.u64Max,
    Model.State.maxEvents, Ne.symm hne]

/-- **The model's receive of the second message on the key the responder already holds is refused**: when the second
message's ratchet key is the peer key `a4` the responder holds, no Diffie-Hellman step is taken and the message number 0
is below the receiving counter 1, so the receive refuses `outOfOrder`.  Hypothesis-free. -/
theorem second_receive_stale (ec prk k1 k2 a4 d dSend newPub xB z newPub2 : Key) :
    Model.Triple.receiveDetailed (replierAfterSend ec prk k1 k2 a4 d dSend newPub) (secondHeader a4) xB z
        newPub2 none = .error (.classical .outOfOrder) := by
  simp [Model.Triple.receiveDetailed, Model.Ratchet.receiveDetailed, Model.Ratchet.trySkipped,
    Model.Ratchet.skipMessageKeysDetailed, Model.State.skipMessageKeys, replierAfterSend, secondHeader]

open Tacenta.UnitLifecycleInitiatorSecondSend (secondComposite secondFrame)
open Tacenta.UnitLifecycleResponderFirstReceipt (firstOpen decode_encodeMessage)

/-- The associated data the second message is sealed under: `ad`, then the encoded composite header. -/
def secondAd (view : Model.Lifecycle.CodewordView) (ad : Model.Lifecycle.Bytes) (braid : Model.Braid.BraidState)
    (candA : Key) (chunk : Model.Braid.Chunk) : Model.Lifecycle.Bytes :=
  Model.Messages.concatAd ad (Model.CompositeHeader.encode (secondComposite view braid candA chunk))

/-- The responder's model session after its reply: the model session after its receipt of the first message
(`firstReceiptSession`) with the Triple after the reply's send (`replierAfterSend`). -/
def replierSession (mB : Model.Lifecycle.Session) (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk)
    (ec prk k1 k2 a4 d dSend newPub c : Key) : Model.Lifecycle.Session :=
  { Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c with
    triple := replierAfterSend ec prk k1 k2 a4 d dSend newPub }

/-- The responder's model session after it accepts the second message: the Triple `responderAfterSecond`, the agreement
`braid'`, the ratchet key replaced by the draw `c` unless the fresh public key equals the old, and no pending initial
message. -/
def secondReceiptSession (mB : Model.Lifecycle.Session) (braid' : Model.Braid.BraidState)
    (ec prk k1 k2 d dSend candA xB z newPub2 c : Key) : Model.Lifecycle.Session :=
  { mB with
    triple := responderAfterSecond ec prk k1 k2 d dSend candA xB z newPub2
    braid := braid'
    ratchetPrivate := if newPub2 == mB.triple.classical.dhsPub then mB.ratchetPrivate else c
    pendingInitial := none }

/-- The second frame is a ratchet message: its first two bytes are the version and the ratchet type. -/
theorem secondFrame_messageType (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (ad : Model.Lifecycle.Bytes) (braid : Model.Braid.BraidState) (candA mk : Key) (chunk : Model.Braid.Chunk)
    (pt : Model.Lifecycle.Bytes) :
    Model.Lifecycle.messageType (secondFrame view oracle ad braid candA mk chunk pt) = some .ratchet := by
  simp [secondFrame, Model.CompositeHeader.encodeMessage, Model.CompositeHeader.encode,
    Model.Lifecycle.messageType]

/-- The model's decoder reads the second frame back: its composite header and the sealed ciphertext, when the ratchet
key is 32 canonical bytes and the codeword the view sends carries 32 bytes. -/
theorem secondFrame_decodeDetailed (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (ad : Model.Lifecycle.Bytes) (braid : Model.Braid.BraidState) (candA mk : Key) (chunk : Model.Braid.Chunk)
    (pt : Model.Lifecycle.Bytes) (hlen : candA.length = 32) (hkey : Model.Messages.checkKey candA = some ())
    (hdata : (view.send braid chunk).data.length = 32) :
    Model.CompositeHeader.decodeDetailed (secondFrame view oracle ad braid candA mk chunk pt) =
      .ok (secondComposite view braid candA chunk,
        oracle.aeadSeal (Model.State.messageKeys mk .tacenta).1 (Model.State.messageKeys mk .tacenta).2.1
          (Model.State.messageKeys mk .tacenta).2.2 pt (secondAd view ad braid candA chunk)) := by
  rw [Model.CompositeHeader.decodeDetailed_ok_iff]
  exact decode_encodeMessage _ _ hlen hkey (fun c hc => by
    simp only [secondComposite, Option.some.injEq] at hc
    subst hc; exact hdata)

/-- **Every outcome of the model's public `decrypt` of the second frame at the responder after its reply**, model only.
For a model session whose Triple is the responder after its reply (`replierAfterSend`), whose agreement has not failed
and receives the frame's composite into `braid'` with no output, a second frame of `oracleA` (ratchet key `candA`, 32
canonical bytes, a 32-byte codeword, sealed under the key the receive derives on a new key with the session's associated
data) whose first agreement with the session's ratchet key returns `xB`: the step is exactly one of
* the oracle holds no draw: `ceiling`, session and oracle unchanged;
* the draw `c`'s agreement with `candA` is refused: `handshake nonContributoryAgreement`, the draw consumed;
* that agreement returns `z` and `candA` is the peer key the session holds: the Triple refuses `outOfOrder`, the draw
  consumed;
* `candA` is not the peer key and the session oracle's open of `oracleA`'s seal is refused: `aead`, the draw consumed;
* the open returns `y`: the step returns `y`, consumes the draw, and leaves `secondReceiptSession` (agreement
  `braid'`, no pending initial message).
No other refusal occurs. -/
theorem second_receipt_model_outcomes (view viewA : Model.Lifecycle.CodewordView)
    (oracleB oracleA : Model.Lifecycle.Oracle) (mB : Model.Lifecycle.Session)
    (ec prk k1 k2 a4 d dSend newPub : Key)
    (hB : mB.triple = replierAfterSend ec prk k1 k2 a4 d dSend newPub)
    (braidA : Model.Braid.BraidState) (chunk : Model.Braid.Chunk) (candA xB : Key) (pt : Model.Lifecycle.Bytes)
    (e : Nat) (braid' : Model.Braid.BraidState)
    (hfail : Model.Lifecycle.agreementFailed mB = false)
    (hlen : candA.length = 32) (hkey : Model.Messages.checkKey candA = some ())
    (hdata : (viewA.send braidA chunk).data.length = 32)
    (hbr : Model.Braid.receive oracleB.braidKem mB.braid
      (Model.Lifecycle.braidMessageOf view mB.braid (secondComposite viewA braidA candA chunk)) = (e, none, braid'))
    (hagree : oracleB.dhAgree mB.ratchetPrivate candA = some xB) :
    (oracleB.draws = [] ∧
      Model.Lifecycle.decrypt view oracleB mB (secondFrame viewA oracleA mB.identityAd braidA candA
          (secondKey (Model.State.kdfRk ec d .tacenta).1 k1 dSend xB) chunk pt) =
        { session := mB, result := .error .ceiling, oracle := oracleB }) ∨
    (∃ c rest, oracleB.draws = c :: rest ∧ oracleB.dhAgree c candA = none ∧
      Model.Lifecycle.decrypt view oracleB mB (secondFrame viewA oracleA mB.identityAd braidA candA
          (secondKey (Model.State.kdfRk ec d .tacenta).1 k1 dSend xB) chunk pt) =
        { session := mB, result := .error (.handshake .nonContributoryAgreement),
          oracle := { oracleB with draws := rest } }) ∨
    (∃ c rest z, oracleB.draws = c :: rest ∧ oracleB.dhAgree c candA = some z ∧ candA = a4 ∧
      Model.Lifecycle.decrypt view oracleB mB (secondFrame viewA oracleA mB.identityAd braidA candA
          (secondKey (Model.State.kdfRk ec d .tacenta).1 k1 dSend xB) chunk pt) =
        { session := mB, result := .error (Model.Lifecycle.tripleReceiveRefusalOf (.classical .outOfOrder)),
          oracle := { oracleB with draws := rest } }) ∨
    (∃ c rest z, oracleB.draws = c :: rest ∧ oracleB.dhAgree c candA = some z ∧ candA ≠ a4 ∧
      firstOpen oracleA oracleB (secondKey (Model.State.kdfRk ec d .tacenta).1 k1 dSend xB) pt
        (secondAd viewA mB.identityAd braidA candA chunk) = none ∧
      Model.Lifecycle.decrypt view oracleB mB (secondFrame viewA oracleA mB.identityAd braidA candA
          (secondKey (Model.State.kdfRk ec d .tacenta).1 k1 dSend xB) chunk pt) =
        { session := mB, result := .error .aead, oracle := { oracleB with draws := rest } }) ∨
    (∃ c rest z y, oracleB.draws = c :: rest ∧ oracleB.dhAgree c candA = some z ∧ candA ≠ a4 ∧
      firstOpen oracleA oracleB (secondKey (Model.State.kdfRk ec d .tacenta).1 k1 dSend xB) pt
        (secondAd viewA mB.identityAd braidA candA chunk) = some y ∧
      Model.Lifecycle.decrypt view oracleB mB (secondFrame viewA oracleA mB.identityAd braidA candA
          (secondKey (Model.State.kdfRk ec d .tacenta).1 k1 dSend xB) chunk pt) =
        { session := secondReceiptSession mB braid' ec prk k1 k2 d dSend candA xB z (oracleB.dhPublic c) c
          result := .ok y
          oracle := { oracleB with draws := rest } }) := by
  have hdisp := Model.Lifecycle.dispatchDecrypt_passthrough oracleB mB
    (secondFrame viewA oracleA mB.identityAd braidA candA
      (secondKey (Model.State.kdfRk ec d .tacenta).1 k1 dSend xB) chunk pt)
    (by rw [secondFrame_messageType]; simp)
  have hdec := secondFrame_decodeDetailed viewA oracleA mB.identityAd braidA candA
    (secondKey (Model.State.kdfRk ec d .tacenta).1 k1 dSend xB) chunk pt hlen hkey hdata
  have hhdr : Model.Lifecycle.tripleHeaderOf (secondComposite viewA braidA candA chunk) = secondHeader candA := by
    simp [Model.Lifecycle.tripleHeaderOf, secondComposite, secondHeader]
  have hdh : (secondComposite viewA braidA candA chunk).dh = candA := rfl
  have hout : Model.Lifecycle.sparseOutputOf none = none := rfl
  rcases hdr : oracleB.draws with _ | ⟨c, rest⟩
  · left
    refine ⟨rfl, ?_⟩
    have hrand : Model.Lifecycle.random32 oracleB = none := by
      simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hdr]
    unfold Model.Lifecycle.decrypt Model.Lifecycle.decryptRatchet
    rw [hdisp]
    dsimp only
    rw [hfail, if_neg (by simp), hdec]
    dsimp only
    rw [hbr, hdh, hagree]
    dsimp only
    rw [hrand]
  have hrand : Model.Lifecycle.random32 oracleB = some (c, { oracleB with draws := rest }) := by
    simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hdr]
  rcases hcand : oracleB.dhAgree c candA with _ | z
  · right; left
    refine ⟨c, rest, rfl, hcand, ?_⟩
    unfold Model.Lifecycle.decrypt Model.Lifecycle.decryptRatchet
    rw [hdisp]
    dsimp only
    rw [hfail, if_neg (by simp), hdec]
    dsimp only
    rw [hbr, hdh, hagree]
    dsimp only
    rw [hrand]
    dsimp only
    rw [hcand]
  by_cases hpeer : candA = a4
  · right; right; left
    refine ⟨c, rest, z, rfl, hcand, hpeer, ?_⟩
    have hrecv : Model.Lifecycle.receiveWithEviction mB.triple (secondComposite viewA braidA candA chunk)
        (secondHeader candA) xB z (oracleB.dhPublic c) none = .error (.classical .outOfOrder) := by
      unfold Model.Lifecycle.receiveWithEviction
      rw [hB, hpeer, second_receive_stale]
      rfl
    unfold Model.Lifecycle.decrypt Model.Lifecycle.decryptRatchet
    rw [hdisp]
    dsimp only
    rw [hfail, if_neg (by simp), hdec]
    dsimp only
    rw [hbr, hdh, hagree]
    dsimp only
    rw [hrand]
    dsimp only
    rw [hcand]
    dsimp only
    rw [hhdr, hout, hrecv]
  have hrecv : Model.Lifecycle.receiveWithEviction mB.triple (secondComposite viewA braidA candA chunk)
      (secondHeader candA) xB z (oracleB.dhPublic c) none =
      .ok (responderAfterSecond ec prk k1 k2 d dSend candA xB z (oracleB.dhPublic c),
        secondKey (Model.State.kdfRk ec d .tacenta).1 k1 dSend xB) := by
    unfold Model.Lifecycle.receiveWithEviction
    rw [hB, second_receive_key ec prk k1 k2 a4 d dSend newPub candA xB z _ hpeer]
  rcases hopen : firstOpen oracleA oracleB (secondKey (Model.State.kdfRk ec d .tacenta).1 k1 dSend xB) pt
      (secondAd viewA mB.identityAd braidA candA chunk) with _ | y
  · right; right; right; left
    refine ⟨c, rest, z, rfl, hcand, hpeer, rfl, ?_⟩
    unfold Model.Lifecycle.decrypt Model.Lifecycle.decryptRatchet
    rw [hdisp]
    dsimp only
    rw [hfail, if_neg (by simp), hdec]
    dsimp only
    rw [hbr, hdh, hagree]
    dsimp only
    rw [hrand]
    dsimp only
    rw [hcand]
    dsimp only
    rw [hhdr, hout, hrecv]
    dsimp only
    simp only [firstOpen] at hopen
    rw [show Model.Messages.concatAd mB.identityAd
        (Model.CompositeHeader.encode (secondComposite viewA braidA candA chunk)) =
      secondAd viewA mB.identityAd braidA candA chunk from rfl, hopen]
  · right; right; right; right
    refine ⟨c, rest, z, y, rfl, hcand, hpeer, rfl, ?_⟩
    unfold Model.Lifecycle.decrypt Model.Lifecycle.decryptRatchet
    rw [hdisp]
    dsimp only
    rw [hfail, if_neg (by simp), hdec]
    dsimp only
    rw [hbr, hdh, hagree]
    dsimp only
    rw [hrand]
    dsimp only
    rw [hcand]
    dsimp only
    rw [hhdr, hout, hrecv]
    dsimp only
    simp only [firstOpen] at hopen
    rw [show Model.Messages.concatAd mB.identityAd
        (Model.CompositeHeader.encode (secondComposite viewA braidA candA chunk)) =
      secondAd viewA mB.identityAd braidA candA chunk from rfl, hopen]
    dsimp only
    simp [secondReceiptSession, responderAfterSecond]

/-- **The budget at the responder's model session after its reply**: clock 1, sparse epoch 0, chain counters 1 and 1,
agreement epoch 1, so room for every `k` with `k + 2 < u32::MAX`.  Model only. -/
theorem modelCounterRoom_replier (mB : Model.Lifecycle.Session) (secret : Model.Lifecycle.Bytes)
    (rcv : Model.Braid.Chunk) (ec prk k1 k2 a4 d dSend newPub c : Model.State.Key) (k : Nat)
    (hk : k + 2 < Std.U32.max) :
    Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom
      (replierSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c) k := by
  have h32 : Std.U32.max = 4294967295 := by simp [Std.U32.max_eq]
  have h64 : Std.U64.max = 18446744073709551615 := by simp [Std.U64.max_eq]
  rw [h32] at hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [replierSession, replierAfterSend]; omega
  · simp only [replierSession, replierAfterSend]; omega
  · simp only [replierSession, replierAfterSend, List.mem_singleton]
    rintro q rfl ch (h | h) <;> (simp at h; subst h; simp only; omega)
  · simp only [replierSession, Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession,
      Model.Braid.BraidState.epoch]; omega

/-- **The responder's model step on the second message is an in-order receive step**: from a model session whose Triple
is the responder after its reply and whose agreement waits for the header at epoch 1, the session `secondReceiptSession`
of the receipt on a ratchet key `candA` that is canonical and not the peer key the responder holds is an
`InOrderReceiveStep`: one Diffie-Hellman step, nothing skipped, the sparse chain stepped once, the agreement still waiting
for the header at epoch 1.  Model only. -/
theorem secondReceipt_inOrderStep (oracle : Model.Lifecycle.Oracle) (mB : Model.Lifecycle.Session)
    (ec prk k1 k2 a4 d dSend newPub candA xB z c : Key) (auth : Model.Braid.Auth)
    (dec dec' : Model.Braid.Decoder)
    (hB : mB.triple = replierAfterSend ec prk k1 k2 a4 d dSend newPub)
    (hbraid : mB.braid = .noHeaderReceived 1 auth dec)
    (hne : candA ≠ a4) (hcan : Model.Messages.canonicalKey candA = true) :
    Tacenta.UnitLifecycleReceivePreserve.InOrderReceiveStep oracle mB
      (secondReceiptSession mB (.noHeaderReceived 1 auth dec') ec prk k1 k2 d dSend candA xB z
        (oracle.dhPublic c) c) := by
  refine ⟨?_, Or.inr ⟨secondHeader candA, xB, z, c, secondKey (Model.State.kdfRk ec d .tacenta).1 k1 dSend xB,
    ?_, hcan, ?_, ?_⟩⟩
  · simp [secondReceiptSession, hbraid, Tacenta.UnitLifecycleReceivePreserve.KeepsAgreementState]
  · rw [hB]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Model.Ratchet.trySkipped, replierAfterSend]
    · intro _; simp [replierAfterSend, secondHeader]
    · intro _; simp [replierAfterSend, secondHeader]
    · simp [Model.SparseRatchet.trySkipped, replierAfterSend]
    · intro cs ch hf hr
      simp [Model.SparseRatchet.findChains, replierAfterSend, secondHeader] at hf
      subst hf
      simp at hr
      subst hr
      simp [secondHeader]
  · simp only [secondReceiptSession]
    rw [hB]
    exact second_receive_key ec prk k1 k2 a4 d dSend newPub candA xB z _ hne
  · simp [secondReceiptSession, responderAfterSecond]

end Model

/-! ## From the two runs to the responder's receive -/

section Bridges

open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf)
open Tacenta.UnitLifecycleResponderFirstFrame (DhAgreeSymmetric dhAgreeSymmetric_is)
open Tacenta.UnitLifecycleT3 (modelChunkOf modelCodewordOf CodewordViewSendOf)

/-- **Two oracles' agreements of two keys with each other's public keys agree**: for private keys `a`, `b` with public
keys `pa`, `pb`, one oracle's agreement of `a` with `pb` is the other's of `b` with `pa`.  Under `DhAgreeSymmetric` and
the two oracle records; the oracles need not be equal. -/
theorem agreement_swap (hsym : DhAgreeSymmetric) {dh : DhView} {R E : Type}
    {rcX : rand_core_1.RngCore R} {crcX : rand_core_1.CryptoRng R} {traceX : R → List Model.Lifecycle.Key}
    {oX : Model.Lifecycle.Oracle} (oracleOfX : DecryptOracleOf rcX crcX dh traceX oX)
    {rcY : rand_core_1.RngCore E} {crcY : rand_core_1.CryptoRng E} {traceY : E → List Model.Lifecycle.Key}
    {oY : Model.Lifecycle.Oracle} (oracleOfY : DecryptOracleOf rcY crcY dh traceY oY)
    (a b : tacenta_boundary.dh.PrivateKey) (pa pb : tacenta_boundary.dh.PublicKeyBytes)
    (ha : tacenta_boundary.dh.PrivateKey.public_key a = ok pa)
    (hb : tacenta_boundary.dh.PrivateKey.public_key b = ok pb) :
    oX.dhAgree (dh.privateKey a) (dh.publicKey pb) = oY.dhAgree (dh.privateKey b) (dh.publicKey pa) := by
  obtain ⟨ra, hra, hmapA⟩ := oracleOfX.dhAgree a pb
  obtain ⟨rb, hrb, hmapB⟩ := oracleOfY.dhAgree b pa
  have hs := (dhAgreeSymmetric_is.mp hsym) a b pa pb ha hb
  rw [hs, hrb] at hra
  cases hra
  rw [← hmapA, ← hmapB]

/-- **The header's chunk at index 1 is a codeword of the header**: for a 96-byte message there is a real chunk at index 1
that the real encoder of a slice reading it emits (`CodewordOf`), the encoder's second `next_chunk`.  Under `DivCeilValue`
and `ErasureAgrees`. -/
theorem second_codeword (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees) (m : Model.Lifecycle.Bytes) (hm : m.length = 96) :
    ∃ c : tacenta_erasure.Chunk, Tacenta.SessionUnitBraidT3.CodewordOf m c ∧ c.index.val = 1 := by
  obtain ⟨-, enc1, -, -, -, -, -, href1, -, -⟩ := Tacenta.UnitHeldKemWitness.held_encoder hdiv hea m hm
  obtain ⟨c1, enc2, hnc, hidx, -⟩ := href1.2 1 (by simp)
  obtain ⟨-, hcw, -⟩ := Tacenta.SessionUnitBraidT3.EncoderRefines.step href1 (by simp) hnc
  exact ⟨c1, hcw, by simpa [Model.Braid.Encoder.nextChunk] using hidx⟩

end Bridges

/-! ## The decoder the responder's agreement holds -/

section Decoder

open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts)

/-- **The decoder at the session `establish_responder` returns holds at most one chunk**: for every successful return
`Ok (sB', pt)` of `establish_responder`, if `sB'`'s agreement is at `NoHeaderReceived`, its decoder holds at most one
chunk (the prepared agreement holds a fresh decoder, and the inner receive adds at most one chunk).  Hypothesis-free. -/
theorem established_responder_decoder_small {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (our : lifecycle.Identity) (store : lifecycle.PrekeyStore) (msg : Slice U8)
    (rng : R) (sB' : lifecycle.Session) (pt : alloc.vec.Vec U8) (store' : lifecycle.PrekeyStore) (rng' : R)
    (h : lifecycle.establish_responder rc crc our store msg rng =
      ok (core.result.Result.Ok (sB', pt), store', rng')) :
    ∀ e a d, sB'.braid.state = tacenta_braid.State.NoHeaderReceived e a d → d.«have».val.length ≤ 1 := by
  intro e a d hst
  rcases Tacenta.UnitLifecycleEstablishResponder.establish_responder_cases rc crc our store msg rng _ h with
    ⟨e0, -, hout⟩ | ⟨p, inner, hinner, ⟨e1, -, hout⟩ | ⟨pt', store'', hok, -, hout⟩⟩
  · simp at hout
  · simp at hout
  obtain ⟨r, s1, rng1⟩ := inner
  simp only at hok hout
  subst hok
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at hout
  obtain ⟨⟨rfl, -⟩, -, -⟩ := hout
  obtain ⟨m, x, y, bc, _a, _ck, _pkb, _new, hrecv, -, -, -, -, hcases⟩ :=
    Tacenta.UnitLifecycleResponderSuccessor.decrypt_ratchet_ok_parts rc crc p.session p.message rng pt' sB' rng1
      hinner
  have hbc : sB'.braid = bc := by
    rcases hcases with ⟨-, hs⟩ | ⟨-, hs⟩ <;> (rw [hs])
  obtain ⟨auth, d0, hd0, hbraid⟩ := Tacenta.UnitLifecycleEstablishResponder.braid_responder_ok _ _ p.hBraid
  obtain ⟨_hv, _n, _needed, -, -, -, -, hd⟩ := Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_ok d0 hd0
  have hps : p.session.braid = p.braid := rfl
  rw [hps, hbraid] at hrecv
  rw [hbc] at hst
  rcases Tacenta.UnitLifecycleResponderSuccessor.braid_receive_noHeader 1#u64 auth d0 m x y bc hrecv e a d hst with
    rfl | ⟨c, r, hadd⟩
  · rw [hd]; simp
  · have hv : d0.«have».val = [] := by rw [hd]
    exact (Tacenta.UnitLifecycleResponderSuccessor.add_chunk_fresh_have d0 d c r hv hadd).2.2.1

end Decoder

/-! ## The run inputs of the receive at the second frame -/

section RunInputs

open Tacenta.UnitLifecycleT3 (modelChunkOf modelCodewordOf)
open Tacenta.UnitLifecycleResponderFirstReceipt (attributedView)
open Tacenta.UnitLifecycleInitiatorSecondSend (secondFrame secondComposite)

/-- **The run inputs of the receive at the second frame**, at the view that attributes the frame's codeword to the
header source: when the message is the second frame sent with the chunk `modelChunkOf src c` of a real codeword `c` of
`src` (as `CodewordViewSendOf` sends it), the session's agreement waits for the header with a decoder that `src` fits,
and the responder's source holds a draw, then the chunk relation, `HonestChunk` and the draw hold.  The codeword half is
derived; the attribution half is the view's construction. -/
theorem second_receipt_run_inputs {E : Type} (view : Model.Lifecycle.CodewordView)
    (oracleA oracleB : Model.Lifecycle.Oracle) (traceB : E → List Model.Lifecycle.Key)
    (real : lifecycle.Session) (mB : Model.Lifecycle.Session) (msg : Slice U8) (braidA : Model.Braid.BraidState)
    (candA mk : Model.Lifecycle.Key) (pt : Model.Lifecycle.Bytes) (src : Model.Lifecycle.Bytes)
    (c : tacenta_erasure.Chunk) (hcw : Tacenta.SessionUnitBraidT3.CodewordOf src c)
    (hsend : view.send braidA (modelChunkOf src c) = modelCodewordOf c)
    (hlen : candA.length = 32) (hkey : Model.Messages.checkKey candA = some ())
    (hframe : sliceOf msg = secondFrame view oracleA mB.identityAd braidA candA mk (modelChunkOf src c) pt)
    (e : Nat) (auth : Model.Braid.Auth) (dec : Model.Braid.Decoder)
    (hbraid : mB.braid = .noHeaderReceived e auth dec)
    (hfits : src.length = dec.size ∧ ∀ x ∈ dec.chunks, x.source = src)
    (rngB : E) (dB : Model.Lifecycle.Key) (restB : List Model.Lifecycle.Key)
    (hdraw : traceB rngB = dB :: restB) :
    Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs
      (attributedView view (modelCodewordOf c).index (modelCodewordOf c).data (modelChunkOf src c))
      oracleB traceB real mB msg rngB := by
  have hdata : (view.send braidA (modelChunkOf src c)).data.length = 32 := by
    rw [hsend]; simp [modelCodewordOf, arrayOf]
  have hdec := secondFrame_decodeDetailed view oracleA mB.identityAd braidA candA mk (modelChunkOf src c) pt
    hlen hkey hdata
  rw [← hframe] at hdec
  refine ⟨?_, ?_, ⟨dB, restB, hdraw⟩⟩
  · intro rc mc ct hd hrel
    rw [hdec] at hd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    have hag := hrel.agChunk
    unfold Tacenta.UnitLifecycleT3.IncomingChunkRefines
    simp only [secondComposite, hsend] at hag ⊢
    rcases hrc : rc.ag_chunk with _ | rch
    · rw [hrc] at hag
      exact hag.elim
    · rw [hrc] at hag
      simp only
      obtain ⟨hi, hdat⟩ := hag
      have hidx : rch.index = c.index := by
        apply UScalar.eq_of_val_eq
        rw [hi]
        simp [modelCodewordOf]
      have hdata' : rch.data = c.data := by
        apply Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes
        exact hdat
      refine ⟨src, ?_, ?_⟩
      · rw [hidx, hdata']
        exact hcw
      · simp [attributedView, hidx, modelChunkOf]
  · intro mc ct hd
    rw [hdec] at hd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    unfold Tacenta.SessionUnitBraidT3.HonestChunk
    intro m hm _
    rw [hbraid]
    simp only [Model.Lifecycle.braidMessageOf, secondComposite, hsend, Option.map_some,
      Option.some.injEq, attributedView, and_self, if_true] at hm
    subst hm
    simp only [Model.Lifecycle.braidMessageOf, secondComposite, Model.Lifecycle.braidTypeOf,
      Tacenta.SessionUnitBraidT3.ChunkFits, modelChunkOf]
    exact ⟨hfits.1, hfits.2⟩

end RunInputs


/-! ## The responder's receive of the second message, on the run -/

section Comp

open Tacenta.UnitLifecycleT3 (BraidSendRefinementContracts TripleSendRefinementContracts CodewordViewSendOf
  ZeroizingRoundTrips modelChunkOf modelCodewordOf)
open Tacenta.UnitLifecycleResponderFirstReceipt (headerSource DhAgreeContributory AeadRoundTrip aead_open_sealed
  firstOpen attributedView)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid establishedModelOf)
open Tacenta.UnitLifecycleEstablishResponder (ResponderPreparedParts responderModelOf)
open Tacenta.UnitLifecycleResponderReply (oracleOf_with_draws replierAfterSend)
open Tacenta.UnitLifecycleInitiatorSecondSend (secondFrame secondComposite secondKey)
open Tacenta.UnitLifecycleResponderReplyReceipt (fresh_public_of_draw initiator_candidate_agreement)

/-- The second message's associated data fits a slice: four length bytes, the 66 bytes of `identity_ad` and the 102
bytes of the composite header. -/
theorem secondAd_length_le (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal) {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity}
    {bundle : lifecycle.PublishedBundle}
    (q : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle)
    (view : Model.Lifecycle.CodewordView) (braid : Model.Braid.BraidState) (candA : Model.Lifecycle.Key)
    (chunk : Model.Braid.Chunk) (hlen : candA.length = 32) (hdata : (view.send braid chunk).data.length = 32) :
    (secondAd view (vecOf q.identityAd) braid candA chunk).length ≤ Usize.max := by
  have h66 := Tacenta.UnitLifecycleEstablishedEncrypt.identityAd_length_parts hdh q
  apply Tacenta.UnitSatisfiabilityBraidAgreements.usize_max_ge
  simp [secondAd, Model.Messages.concatAd, Model.CompositeHeader.encode, secondComposite, vecOf, h66, hlen,
    Model.Messages.be32, Model.CompositeHeader.be64, Model.CompositeHeader.encodeChunk,
    Model.CompositeHeader.be16, hdata]

/-- **The responder's `decrypt` of the initiator's second message has two outcomes, told apart by the second message's
ratchet key**, on the run of the initiator's first send.  Under the hypotheses of `initiator_sends_second_message` and the
per-run premise that the responder's source after its reply holds a draw `dB2` (placed first, with the source): the
reply's `encrypt` at `sB'` returns `bytesR` and `sB''`, the initiator's `decrypt` of it returns `Ok ptA` with the bytes of
`ptR`, the initiator's second `encrypt` at `s''` returns `bytes2` (`secondFrame`, the header chunk at index 1) and leaves
its source; `sB''` refines `replierSession`, keeps the agreement `sB'` held, passes `Session::invariant` and meets
`CounterHeadroom`; and the responder's public `decrypt` of `bytes2` at `sB''` from `rngR` returns, takes exactly the draw
`dB2`, and
* refuses `Triple(Classical(OutOfOrder))` with the session unchanged exactly when the initiator's new ratchet key is its
  first ratchet key, and
* otherwise returns `Ok ptB2` with `ptB2` the bytes of `ptS`, clears the pending initial message, writes only the Triple
  Ratchet, the agreement and the ratchet key, and its session refines `secondReceiptSession` (the Triple
  `responderAfterSecond`, the header decoder holding the chunks at index 0 and 1).
`DhAgreeContributory` and `AeadRoundTrip`, hypotheses already, exclude the model step's `Handshake` and `Aead` arms; the
draw premise excludes its `ceiling` arm.  No compiler-trust axiom (the pin). -/
theorem responder_receives_second_message_two_outcomes [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (traceB : F → List Model.Lifecycle.Key) (rngR : F) (dB2 : Model.Lifecycle.Key) (restB2 : List Model.Lifecycle.Key)
    (hdrawB2 : traceB rngR = dB2 :: restB2)
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
      (dSend x : Model.Lifecycle.Key) (dk ekSeed ekVector : Model.Braid.Bytes) (bytesR : alloc.vec.Vec Std.U8)
      (sB'' : lifecycle.Session) (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' : R)
      (bytes2 : alloc.vec.Vec Std.U8) (s''' : lifecycle.Session)
      (res : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error) (sB''' : lifecycle.Session) (rngR2 : F),
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' =
        ok (core.result.Result.Ok ptA, s'', rngA') ∧ ptA.val = ptR.val ∧
      lifecycle.Session.encrypt rc crc s'' ptS rngA' = ok (core.result.Result.Ok bytes2, s''', rngA') ∧
      vecOf bytes2 = secondFrame view oracle (vecOf q.identityAd)
        (.keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
          ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩)
        (oracle.dhPublic dA) (secondKey (arrayOf q.rootKey) (arrayOf q.sparseSend) dSend x)
        ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩
        (sliceOf ptS) ∧
      oracle.dhAgree dA (oracleB.dhPublic dB) = some x ∧
      SessionRefines dh oracleB.braidKem sB''
        (replierSession (responderModelOf dh p) (sliceOf p.braidSecret)
          ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
          (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
          (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) ∧
      sB''.braid = sB'.braid ∧ lifecycle.Session.invariant sB'' = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB'' ∧
      lifecycle.Session.decrypt rcB crcB sB'' (alloc.vec.Vec.deref bytes2) rngR = ok (res, sB''', rngR2) ∧
      traceB rngR2 = restB2 ∧
      ((oracle.dhPublic dA = arrayOf q.ratchetBytes ∧
          res = core.result.Result.Err (lifecycle.Error.Triple
            (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.OutOfOrder)) ∧ sB''' = sB'') ∨
        (oracle.dhPublic dA ≠ arrayOf q.ratchetBytes ∧
          ∃ (z : Model.Lifecycle.Key) (ptB2 : alloc.vec.Vec Std.U8),
          oracleB.dhAgree dB2 (oracle.dhPublic dA) = some z ∧
          res = core.result.Result.Ok ptB2 ∧ ptB2.val = ptS.val ∧ sB'''.pending_initial = none ∧
          sB''' = { sB'' with
            triple := sB'''.triple, braid := sB'''.braid, ratchet_private := sB'''.ratchet_private,
            pending_initial := none } ∧
          SessionRefines dh oracleB.braidKem sB'''
            (secondReceiptSession
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
              (arrayOf q.dhOut) dSend (oracle.dhPublic dA) x z (oracleB.dhPublic dB2) dB2))) := by
  -- the initiator's second message, on the run
  obtain ⟨dSend, x, bytesR, sB'', ptA, s'', rngA', dk, ekSeed, ekVector, bytes2, s''', hkg, hagreeB, hx, hcallR,
    hcallA, hpt, -, -, -, -, -, -, hcallS, -, -, hbytes2, -, -, -, -⟩ :=
    Tacenta.UnitLifecycleInitiatorSecondMessage.initiator_sends_second_message ptS hroomS rc crc trace dh kem view
      oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE
      ourA bundleA expected rng0 rng1 s h q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall
      contractsA agreementsA dA restA hdrawA rcB crcB contracts hpub hsym hcon haead hrt hoeq traceB oracleB
      oracleOfB braidB agreements ourB storeB hpublish hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB'
      storeB' rngB' hcallB ptR hroomR rngR hfreshB
  -- the responder's reply on the same run: its keys and the relation at the session it leaves
  obtain ⟨p, ec, dSend', dk', ekSeed', ekVector', bytesR', sB''₁, hkg', hkdf, hagreeB', hidad, -, hcallR', hbraidEq,
    -, -, -, hrelB⟩ :=
    Tacenta.UnitLifecycleResponderReply.initiator_first_send_responder_replies rc crc trace dh kem view oracle braid
      triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA
      expected rng0 rng1 s h q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall rcB crcB contracts
      hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish hidentity
      hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR rngR
  rw [hcallR] at hcallR'
  simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hcallR'
  obtain ⟨rfl, rfl, -⟩ := hcallR'
  rw [hagreeB] at hagreeB'
  cases hagreeB'
  rw [hkg] at hkg'
  simp only [Option.some.injEq, Prod.mk.injEq] at hkg'
  obtain ⟨rfl, rfl, rfl⟩ := hkg'
  -- the invariant and the ceilings at the session the reply left
  obtain ⟨hinvB, hcB⟩ := Tacenta.UnitLifecycleSendPreserve.initiator_first_send_responder_reply_admissible rc crc
    trace dh kem view oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct
    hbound rcE crcE ourA bundleA expected rng0 rng1 s h q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s'
    rng' hcall rcB crcB contracts hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB
    storeB hpublish hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR
    rngR bytesR sB'' rngR hcallR
  subst hq
  -- the header source and the codeword of its chunk at index 1
  set src := headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector with hsrcdef
  obtain ⟨hs32, -, hhl⟩ := hsizes _ _ _ _ hkg
  have hsrc : src.length = Model.Braid.headerSize + Model.Braid.macSize := by
    simp [src, headerSource, Model.Braid.Auth.macHdr, Model.Kdf.hmac_length, Model.Kdf.hashLen, hs32, hhl,
      Model.Braid.headerSize, Model.Braid.macSize]
  obtain ⟨c1, hcw1, hidx1⟩ := second_codeword contracts.divCeilValue agreements.erasure src
    (by rw [hsrc]; rfl)
  have hmc1 : modelChunkOf src c1 = ⟨src, 1⟩ := by simp [modelChunkOf, hidx1]
  set braidA : Model.Braid.BraidState := .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
    ⟨src, 1⟩ with hbraidAdef
  have hsend1 := codewordView.send braidA src c1 hcw1
  -- the initiator's new ratchet key, from its draw: 32 canonical bytes
  have oracleOfA : DecryptOracleOf rc crc dh trace { oracle with draws := trace rng' } :=
    DecryptOracleOf.of_oracleOf (oracleOf_with_draws oracleOf _)
  obtain ⟨-, kA, pkA, bA, -, -, hkdA, hpkA, -, hcanA, hpkbA, hnewA⟩ :=
    fresh_public_of_draw hpub codec oracleOfA rng' dA restA hdrawA
  have hnewA' : oracle.dhPublic dA = arrayOf bA := hnewA
  have hlenA : (oracle.dhPublic dA).length = 32 := by rw [hnewA']; simp [arrayOf]
  have hkeyA : Model.Messages.checkKey (oracle.dhPublic dA) = some () := by
    rw [hnewA']
    simp [Model.Messages.checkKey, Tacenta.UnitLifecycleResponderFirstFrame.canonicalKey_arrayOf _ hcanA]
  -- the responder's model session after its reply, and the second frame in its terms
  set mB := replierSession (responderModelOf dh p) (sliceOf p.braidSecret) ⟨src, 0⟩ (arrayOf ec)
    (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) (arrayOf q.ratchetBytes)
    (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB with hmBdef
  replace hrelB : SessionRefines dh oracleB.braidKem sB'' mB := hrelB
  have hadB : mB.identityAd = vecOf q.identityAd := by
    simp only [mB, replierSession, Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession,
      responderModelOf, hidad]
  have hroot : (Model.State.kdfRk (arrayOf ec) (arrayOf q.dhOut) .tacenta).1 = arrayOf q.rootKey := by
    rw [hkdf]
  have hframe2 : sliceOf (alloc.vec.Vec.deref bytes2) = secondFrame view oracle mB.identityAd braidA
      (oracle.dhPublic dA) (secondKey (Model.State.kdfRk (arrayOf ec) (arrayOf q.dhOut) .tacenta).1
        (arrayOf q.sparseSend) dSend x) (modelChunkOf src c1) (sliceOf ptS) := by
    rw [hadB, hroot, hmc1]
    exact hbytes2
  -- the responder's oracle, with the draws its source holds after the reply
  let oracleB2 : Model.Lifecycle.Oracle := { oracleB with draws := traceB rngR }
  have oracleOfB2 : DecryptOracleOf rcB crcB dh traceB oracleB2 :=
    DecryptOracleOf.of_oracleOf (oracleOf_with_draws oracleOfB _)
  -- the run's inputs of the decrypt refinement, at the view that attributes the chunk at index 1
  let aview := attributedView view (modelCodewordOf c1).index (modelCodewordOf c1).data (modelChunkOf src c1)
  have hdec0 : (Model.Braid.Decoder.new (Model.Braid.headerSize + Model.Braid.macSize)).addChunk ⟨src, 0⟩ =
      ⟨Model.Braid.headerSize + Model.Braid.macSize, [⟨src, 0⟩]⟩ := by
    simp [Model.Braid.Decoder.addChunk, Model.Braid.Decoder.new]
  have inputs := second_receipt_run_inputs view oracle oracleB2 traceB sB'' mB (alloc.vec.Vec.deref bytes2) braidA
    (oracle.dhPublic dA) _ (sliceOf ptS) src c1 hcw1 hsend1 hlenA hkeyA hframe2 1 _ _ rfl
    (by rw [hdec0]; exact ⟨hsrc, by simp⟩) rngR dB2 restB2 hdrawB2
  have hft : Model.Lifecycle.messageType (sliceOf (alloc.vec.Vec.deref bytes2)) ≠ some .initial := by
    rw [hframe2, secondFrame_messageType]; simp
  obtain ⟨output, hcallB2, hstep⟩ :=
    Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_of_counter_headroom rcB crcB traceB dh aview
      oracleB2 oracleOfB2 codec contracts.decrypt agreements sB'' mB (alloc.vec.Vec.deref bytes2) rngR hft hinvB
      hrelB hcB rfl inputs
  -- the model's step: the agreement holds two chunks of three, so it stays waiting for the header
  have hfail : Model.Lifecycle.agreementFailed mB = false := by
    simp [mB, replierSession, Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession,
      Model.Lifecycle.agreementFailed]
  have hbr : Model.Braid.receive oracleB2.braidKem mB.braid
      (Model.Lifecycle.braidMessageOf aview mB.braid
        (secondComposite view braidA (oracle.dhPublic dA) (modelChunkOf src c1))) =
      (0, none, .noHeaderReceived 1 (Model.Braid.Auth.init 1 (sliceOf p.braidSecret))
        (((Model.Braid.Decoder.new (Model.Braid.headerSize + Model.Braid.macSize)).addChunk ⟨src, 0⟩).addChunk
          ⟨src, 1⟩)) := by
    have hsend1' : view.send braidA ⟨src, 1⟩ = modelCodewordOf c1 := by rw [← hmc1]; exact hsend1
    simp only [Model.Lifecycle.braidMessageOf, secondComposite, hmc1, hsend1', Option.map_some, aview,
      attributedView, and_self, if_true]
    simp [mB, replierSession, Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession, Model.Braid.receive,
      Model.Braid.Decoder.addChunk, Model.Braid.Decoder.new, Model.Braid.Decoder.message,
      Model.Braid.Decoder.hasMessage, Model.Braid.chunkBytes, Model.Braid.headerSize, Model.Braid.macSize,
      Model.Lifecycle.braidTypeOf, Model.Braid.BraidState.epoch]
  -- the responder's first agreement on the second message is the initiator's agreement `x`, by symmetry: the
  -- responder's ratchet key is the one whose public key the reply carried (clause (a) of the invariant at `sB''`)
  obtain ⟨hstrB, -, -⟩ := (Tacenta.UnitLifecycleSendPreserve.session_invariant_iff sB'').mp hinvB
  obtain ⟨pkR, hpkR, hbR⟩ := Tacenta.UnitLifecycleReceivePreserve.clause_a_of_structural sB'' hstrB
  have hdhsB : Tacenta.SessionUnitT3.keyOf sB''.triple.classical.dhs_pub = oracleB.dhPublic dB :=
    Tacenta.UnitLifecycleReceivePreserve.keyOf_dhs hrelB.triple
  obtain ⟨bR, hbR', hpkRv⟩ := codec.asBytes pkR
  rw [hbR] at hbR'
  cases hbR'
  have hpubR : dh.publicKey pkR = oracleB.dhPublic dB := by rw [← hpkRv, ← hdhsB]; rfl
  have hagree : oracleB2.dhAgree mB.ratchetPrivate (oracle.dhPublic dA) = some x := by
    rw [← hrelB.ratchetPrivate, hnewA', ← hpkbA,
      agreement_swap hsym oracleOfB2 (DecryptOracleOf.of_oracleOf oracleOf) sB''.ratchet_private kA pkR pkA hpkR
        hpkA, hkdA, hpubR]
    exact hx
  have hdata : (view.send braidA (modelChunkOf src c1)).data.length = 32 := by
    rw [hsend1]; simp [modelCodewordOf, arrayOf]
  have O := second_receipt_model_outcomes aview view oracleB2 oracle mB (arrayOf ec) (arrayOf q.sparseRoot)
    (arrayOf q.sparseSend) (arrayOf q.sparseReceive) (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend
    (oracleB.dhPublic dB) rfl braidA (modelChunkOf src c1) (oracle.dhPublic dA) x (sliceOf ptS) 0 _ hfail hlenA
    hkeyA hdata hbr hagree
  rw [← hframe2] at O
  -- the responder's draw agrees with the initiator's new key (contributory), and the initiator's seal opens
  have hdrB2 : oracleB2.draws = dB2 :: restB2 := hdrawB2
  obtain ⟨z0, hz0⟩ := initiator_candidate_agreement hcon codec oracleOfB2 rngR dB2 restB2 hdrawB2 kA pkA hpkA
  rw [hpkbA, ← hnewA'] at hz0
  have hadlen : (secondAd view mB.identityAd braidA (oracle.dhPublic dA) (modelChunkOf src c1)).length ≤
      Usize.max := by
    rw [hadB]
    exact secondAd_length_le dhCodec q.toInitiatorOutputParts view braidA _ _ hlenA hdata
  have hopen := aead_open_sealed haead oracleOf.aeadSeal oracleOfB2
    (Model.State.messageKeys (secondKey (Model.State.kdfRk (arrayOf ec) (arrayOf q.dhOut) .tacenta).1
      (arrayOf q.sparseSend) dSend x) .tacenta).1
    (Model.State.messageKeys (secondKey (Model.State.kdfRk (arrayOf ec) (arrayOf q.dhOut) .tacenta).1
      (arrayOf q.sparseSend) dSend x) .tacenta).2.1
    (Model.State.messageKeys (secondKey (Model.State.kdfRk (arrayOf ec) (arrayOf q.dhOut) .tacenta).1
      (arrayOf q.sparseSend) dSend x) .tacenta).2.2
    (by simp [Model.State.messageKeys, Model.Kdf.hkdf_length])
    (by simp [Model.State.messageKeys, Model.Kdf.hkdf_length])
    (by simp [Model.State.messageKeys, Model.Kdf.hkdf_length]) ptS (by omega)
    (secondAd view mB.identityAd braidA (oracle.dhPublic dA) (modelChunkOf src c1)) hadlen
  obtain ⟨res, sB''', rngR2⟩ := output
  have hres := hstep.result
  have hdr := hstep.draws
  have hsess := hstep.session
  rcases O with ⟨hnil, -⟩ | ⟨c, rest', hdr', hnone, -⟩ | ⟨c, rest', z, hdr', -, hpeer, hM⟩ |
    ⟨c, rest', z, hdr', -, -, hopen', -⟩ | ⟨c, rest', z, y, hdr', hsome, hpeer, hopen', hM⟩
  · rw [hdrB2] at hnil; cases hnil
  · rw [hdrB2] at hdr'
    obtain ⟨rfl, rfl⟩ := List.cons.inj hdr'
    rw [hz0] at hnone
    cases hnone
  · rw [hdrB2] at hdr'
    obtain ⟨rfl, rfl⟩ := List.cons.inj hdr'
    rw [hM] at hres hdr
    refine ⟨p, ec, dSend, x, dk, ekSeed, ekVector, bytesR, sB'', ptA, s'', rngA', bytes2, s''', res, sB''', rngR2,
      hcallR, hcallA, hpt, hcallS, hbytes2, hx, hrelB, hbraidEq, hinvB, hcB, hcallB2, hdr, Or.inl ⟨hpeer, ?_, ?_⟩⟩
    · cases res with
      | Ok v => simp [Tacenta.UnitLifecycleT3.ResultRefines] at hres
      | Err e =>
        simp only [Tacenta.UnitLifecycleT3.ResultRefines] at hres
        have he : e = lifecycle.Error.Triple
            (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.OutOfOrder) :=
          Tacenta.UnitLifecycleT3.refusalOf_injective (hres.trans rfl)
        rw [he]
    · cases res with
      | Ok v => simp [Tacenta.UnitLifecycleT3.ResultRefines] at hres
      | Err e => exact Tacenta.UnitLifecycleAtomicity.decrypt_err_leaves_state rcB crcB _ _ _ e sB''' rngR2 hcallB2
  · simp only [firstOpen] at hopen'
    rw [hopen] at hopen'
    cases hopen'
  · rw [hdrB2] at hdr'
    obtain ⟨rfl, rfl⟩ := List.cons.inj hdr'
    simp only [firstOpen] at hopen'
    rw [hopen] at hopen'
    cases hopen'
    rw [hM] at hres hdr hsess
    cases res with
    | Err e => simp [Tacenta.UnitLifecycleT3.ResultRefines] at hres
    | Ok ptB2 =>
      have hs3 := Tacenta.UnitLifecycleAtomicity.decrypt_ok_writes rcB crcB _ _ _ ptB2 sB''' rngR2 hcallB2
      exact ⟨p, ec, dSend, x, dk, ekSeed, ekVector, bytesR, sB'', ptA, s'', rngA', bytes2, s''', _, sB''', rngR2,
        hcallR, hcallA, hpt, hcallS, hbytes2, hx, hrelB, hbraidEq, hinvB, hcB, hcallB2, hdr, Or.inr ⟨hpeer, z, ptB2, hsome, rfl,
          Tacenta.UnitLifecycleEstablishResponder.map_u8_inj hres, by rw [hs3], hs3, hsess⟩⟩

/-- **The responder receives the initiator's second message, on the run of the initiator's first send, and keeps
`Session::invariant` and the four ceilings.**  Under the hypotheses of `responder_receives_second_message_two_outcomes`
and the per-run premise `hfreshA` that the initiator's new ratchet key (`oracle.dhPublic dA`, from its draw) is not its
first ratchet key, the only premise added (placed first, with the draw premise): the run's conjuncts as there, the
responder's agreement `z` of its draw with the new key, and the responder's public `decrypt` of `bytes2` at `sB''` from
`rngR` returns `Ok ptB2` with `ptB2` the bytes of `ptS`, takes exactly the draw `dB2`, clears the pending initial message,
writes only the Triple Ratchet, the agreement and the ratchet key, and its session `sB'''` refines `secondReceiptSession`,
passes `Session::invariant`, meets `CounterHeadroom` and has room for every `j` with `j + 3 < u32::MAX` further operations
(`CounterRoom`).  The invariant and the budget come from `decrypt_keeps_invariant_in_order` at `sB''`: the model step is an
in-order step (`secondReceipt_inOrderStep`), the decoder there holds one chunk (`established_responder_decoder_small`,
through the reply keeping the agreement), and the budget is read off the model session (`modelCounterRoom_replier`).  No
compiler-trust axiom (the pin). -/
theorem responder_receives_second_message [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
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
      (dSend x : Model.Lifecycle.Key) (dk ekSeed ekVector : Model.Braid.Bytes) (bytesR : alloc.vec.Vec Std.U8)
      (sB'' : lifecycle.Session) (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' : R)
      (bytes2 : alloc.vec.Vec Std.U8) (s''' : lifecycle.Session) (z : Model.Lifecycle.Key)
      (ptB2 : alloc.vec.Vec Std.U8) (sB''' : lifecycle.Session) (rngR2 : F),
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' =
        ok (core.result.Result.Ok ptA, s'', rngA') ∧ ptA.val = ptR.val ∧
      lifecycle.Session.encrypt rc crc s'' ptS rngA' = ok (core.result.Result.Ok bytes2, s''', rngA') ∧
      vecOf bytes2 = secondFrame view oracle (vecOf q.identityAd)
        (.keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
          ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩)
        (oracle.dhPublic dA) (secondKey (arrayOf q.rootKey) (arrayOf q.sparseSend) dSend x)
        ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩
        (sliceOf ptS) ∧
      oracle.dhAgree dA (oracleB.dhPublic dB) = some x ∧
      oracleB.dhAgree dB2 (oracle.dhPublic dA) = some z ∧
      lifecycle.Session.invariant sB'' = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB'' ∧
      lifecycle.Session.decrypt rcB crcB sB'' (alloc.vec.Vec.deref bytes2) rngR =
        ok (core.result.Result.Ok ptB2, sB''', rngR2) ∧
      ptB2.val = ptS.val ∧ traceB rngR2 = restB2 ∧ sB'''.pending_initial = none ∧
      sB''' = { sB'' with
        triple := sB'''.triple, braid := sB'''.braid, ratchet_private := sB'''.ratchet_private,
        pending_initial := none } ∧
      SessionRefines dh oracleB.braidKem sB'''
        (secondReceiptSession
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
          (arrayOf q.dhOut) dSend (oracle.dhPublic dA) x z (oracleB.dhPublic dB2) dB2) ∧
      lifecycle.Session.invariant sB''' = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB''' ∧
      (∀ j, j + 3 < Std.U32.max → Tacenta.UnitLifecycleSendPreserve.CounterRoom sB''' j) := by
  obtain ⟨p, ec, dSend, x, dk, ekSeed, ekVector, bytesR, sB'', ptA, s'', rngA', bytes2, s''', res, sB''', rngR2,
    hcallR, hcallA, hptA, hcallS, hbytes2, hx, hrelB, hbraidEq, hinvB, hcB, hcallB2, hdr, hcases⟩ :=
    responder_receives_second_message_two_outcomes traceB rngR dB2 restB2 hdrawB2 ptS hroomS rc crc trace dh kem
      view oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE
      crcE ourA bundleA expected rng0 rng1 s h q hq plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall
      contractsA agreementsA dA restA hdrawA rcB crcB contracts hpub hsym hcon haead hrt hoeq oracleB oracleOfB braidB
      agreements ourB storeB hpublish hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB'
      hcallB ptR hroomR hfreshB
  -- the fresh-key premise excludes the stale arm
  rcases hcases with ⟨hstale, -, -⟩ | ⟨-, z, ptB2, hz, hres, hpt, hpend, hs3, hsess⟩
  · exact absurd hstale hfreshA
  subst hres
  -- the model step is an in-order receive: one Diffie-Hellman step on the initiator's new key, nothing skipped
  obtain ⟨-, -, -, bA, -, -, -, -, -, hcanA, -, hnewA⟩ :=
    fresh_public_of_draw hpub codec (DecryptOracleOf.of_oracleOf (oracleOf_with_draws oracleOf (trace rng'))) rng' dA
      restA hdrawA
  have hcanM : Model.Messages.canonicalKey (oracle.dhPublic dA) = true := by
    rw [show oracle.dhPublic dA = arrayOf bA from hnewA]
    exact Tacenta.UnitLifecycleResponderFirstFrame.canonicalKey_arrayOf bA hcanA
  have hstep := secondReceipt_inOrderStep { oracleB with draws := traceB rngR }
    (replierSession (responderModelOf dh p) (sliceOf p.braidSecret)
      ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
      (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
      (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB)
    (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) (arrayOf q.ratchetBytes)
    (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) (oracle.dhPublic dA) x z dB2 _ _
    (((Model.Braid.Decoder.new (Model.Braid.headerSize + Model.Braid.macSize)).addChunk
      ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩).addChunk
      ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩)
    rfl rfl hfreshA hcanM
  -- the decoder at `sB''` holds at most one chunk: the reply kept the agreement `establish_responder` returned
  have hsmall : ∀ e a d, sB''.braid.state = tacenta_braid.State.NoHeaderReceived e a d →
      d.«have».val.length ≤ 1 := by
    rw [hbraidEq]
    exact established_responder_decoder_small rcB crcB ourB storeB _ rngB sB' ptB storeB' rngB' hcallB
  -- the budget at `sB''`
  have hroomB : ∀ j, j + 3 < Std.U32.max → Tacenta.UnitLifecycleSendPreserve.CounterRoom sB'' (j + 1) :=
    fun j hj => (Tacenta.UnitLifecycleSendPreserve.counterRoom_iff_model hrelB (j + 1)).mpr
      (modelCounterRoom_replier _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega))
  -- the general receive preservation, at `NoHeaderReceived` with one chunk held
  have key : ∀ j, j + 3 < Std.U32.max →
      lifecycle.Session.invariant sB''' = ok true ∧ Tacenta.UnitLifecycleSendPreserve.CounterRoom sB''' j :=
    fun j hj => Tacenta.UnitLifecycleReceivePreserve.decrypt_keeps_invariant_in_order agreements.kemClone hpub rcB
      crcB dh codec oracleB.braidKem { oracleB with draws := traceB rngR } oracleOfB.dhPublic sB'' _ _ j hinvB
      (hroomB j hj) hrelB hsmall _ rngR ptB2 sB''' rngR2 hcallB2 hsess hstep
  have h0 : (0 : Nat) + 3 < Std.U32.max := by simp [Std.U32.max_eq]
  exact ⟨p, ec, dSend, x, dk, ekSeed, ekVector, bytesR, sB'', ptA, s'', rngA', bytes2, s''', z, ptB2, sB''', rngR2,
    hcallR, hcallA, hptA, hcallS, hbytes2, hx, hz, hinvB, hcB, hcallB2, hpt, hdr, hpend, hs3, hsess, (key 0 h0).1,
    (Tacenta.UnitLifecycleSendPreserve.counterRoom_zero sB''').mp (key 0 h0).2, fun j hj => (key j hj).2⟩

end Comp

/-! ## The reaches: one run, from `publish` to the responder's receipt of the second message -/

section Reach

open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real InitiatorAxiom ResponderAxiom)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace chunks32)
open Tacenta.UnitLifecycleResponderFirstFrame (FirstFrameSuccessShape PoolEntry reachStore reachBundle
  publish_reachStore reachStore_distinct heldKemPair zPool InitiatorSecretParts DhAgreeSymmetric FirstKemAgrees
  random_secret_byte)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory AeadRoundTrip)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid InitiatorOutputParts initiatorTriple init_sender_ok
  braid_initiator_ok)
open Tacenta.UnitLifecycleEstablishResponder (z32 fullSlice)
open Tacenta.UnitLifecycleResponderReply (oracleOf_with_draws)
open Tacenta.UnitLifecycleResponderReplyReceipt (DhPublicNotConstant dhPublicNotConstant_is byteTrace_one
  byteTrace_seed_extra two_draws_of_seed_extra)
open Tacenta.UnitLifecycleEstablishedEncrypt (EstablishedEncryptHypotheses EncryptExtraLaws emptyPlaintext)

open Tacenta.UnitLifecycleT1 in
/-- **The initiator's establishment against `reachBundle`, with the bytes of its ratchet key**: as
`reach_establishment` (whose proof this repeats), and the run's record carries 32 bytes whose `from_bytes` is the
initiator's ratchet private key. -/
theorem reach_establishment_secret (c : EstablishInitiatorContracts byteRng) (ourA : lifecycle.Identity)
    (pkb : tacenta_boundary.dh.PublicKeyBytes) (a : Array U8 32#usize)
    (ha : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (heq : tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq pkb pkb = ok true)
    (sig1 sig2 : Array U8 64#usize) (kemPk : alloc.vec.Vec U8)
    (hverify : verify_bundle (reachBundle pkb sig1 sig2 kemPk).bundle = ok (core.result.Result.Ok ()))
    (hag : ∀ k, ∃ x, tacenta_boundary.dh.PrivateKey.agree k pkb = ok (some x))
    (stream rest : List U8) (ct : alloc.vec.Vec U8) (ss : Array U8 32#usize)
    (henc : tacenta_boundary.kem.encapsulate byteRng byteCrc (alloc.vec.Vec.deref kemPk) stream =
      ok (core.result.Result.Ok (ct, ss), rest)) :
    ∃ (q : InitiatorSecretParts byteRng byteCrc ourA (reachBundle pkb sig1 sig2 kemPk)) (rng1 : List U8)
      (sec : Array U8 32#usize),
      q.kemCiphertext = ct ∧ q.kemSecret = ss ∧ tacenta_boundary.dh.PrivateKey.from_bytes sec = ok q.ratchetPrivate ∧
      lifecycle.establish_initiator_for byteRng byteCrc ourA (reachBundle pkb sig1 sig2 kemPk) pkb
        (List.replicate 32 0#u8 ++ stream) = ok (core.result.Result.Ok q.session, rng1) := by
  rcases c with ⟨hdh, hid, hagree, hkem, hx, hrngTotal, hrng, hkdf, hzero, htripleZero, hkdfInit,
    hspqrZero, hbraidKdf, hzeroArray, hindex⟩
  let _ : Tacenta.SessionUnitSessionT1.ZeroizingModel := hzero
  obtain ⟨a1, hr1⟩ := random_secret_byte byteCrc (List.replicate 32 0#u8) stream (by simp)
  obtain ⟨eph, heph, -⟩ := Std.WP.spec_imp_exists (private_key_from_bytes_no_panic hdh a1)
  obtain ⟨z1, hz1, hz1d⟩ := hzeroArray 32#usize z32 ss
  obtain ⟨ik, hik, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_dh_key_no_panic hdh ourA)
  have hsec := Tacenta.UnitLifecycleEstablishInitiatorShape.shared_secret_successBundle hzeroArray hkdf pkb
    sig1 sig2 kemPk hverify hag ik eph ss
  obtain ⟨sec, hsec⟩ := hsec
  obtain ⟨z2, hz2, hz2d⟩ := hzeroArray 32#usize z32 sec
  obtain ⟨⟨a2, r3⟩, hr3, -⟩ := Std.WP.spec_imp_exists (random_secret_no_panic byteRng byteCrc hrng rest)
  obtain ⟨rp, hrp, -⟩ := Std.WP.spec_imp_exists (private_key_from_bytes_no_panic hdh a2)
  obtain ⟨d, hd⟩ := hag rp
  obtain ⟨z3, hz3, hz3d⟩ := hzeroArray 32#usize z32 d
  obtain ⟨s1, hs1i, -⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.index_full_spec hindex sec)
  obtain ⟨rpub, hrpub, -⟩ := Std.WP.spec_imp_exists (private_key_public_no_panic hdh rp)
  obtain ⟨a4, ha4, -⟩ := Std.WP.spec_imp_exists (public_key_as_bytes_no_panic hdh rpub)
  obtain ⟨triple, htriple, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitTripleT1.State.init_sender_no_panic hkdf htripleZero hkdfInit hspqrZero s1 a4
      a d tacenta_ratchet.LabelSet.Tacenta)
  obtain ⟨rk, cks, prk, c1, c2, rfl⟩ := init_sender_ok _ _ _ _ _ htriple
  obtain ⟨braid, hbraid, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.Braid.initiator_no_panic hbraidKdf hzeroArray s1)
  obtain ⟨auth, rfl⟩ := braid_initiator_ok _ _ hbraid
  obtain ⟨opub, hopub, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_public_no_panic hdh ourA)
  obtain ⟨ad, had, -⟩ := Std.WP.spec_imp_exists (identity_ad_no_panic hdh opub pkb)
  obtain ⟨epub, hepub, -⟩ := Std.WP.spec_imp_exists (private_key_public_no_panic hdh eph)
  have hne : core.cmp.PartialEq.ne.trait_default
      tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes pkb pkb = ok false := by
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, heq]
  have hcanon : is_canonical_key pkb = ok true := by
    rw [Tacenta.UnitHeadroomInvariant.is_canonical_key_eq pkb a ha, hcan]
  have hvalid : is_valid_identity_key pkb = ok true := Tacenta.UnitLifecycleEstablishInitiatorShape.verify_bundle_ok _ _ hverify
  refine ⟨
    { ratchetPrivate := rp, ratchetPublic := rpub, ratchetBytes := a4, peerRatchetBytes := a, rootKey := rk,
      sendChain := cks, sparseRoot := prk, sparseSend := c1, sparseReceive := c2, auth := auth,
      identityAd := ad, ourPublic := opub, ephemeral := eph, ephemeralPublic := epub, kemCiphertext := ct,
      kemSecret := ss, rngBefore := stream, rngAfter := rest,
      hRatchetPublic := hrpub, hRatchetBytes := ha4, hPeerRatchetBytes := ha, hPeerRatchetCanonical := hcanon,
      hOurPublic := hopub, hIdentityAd := had, hPeerValid := hvalid, hEphemeralPublic := hepub,
      hEncapsulate := henc,
      identityKey := ik, kemSecretZ := z1, encapsulated := ss, shared := sec, sharedZ := z2,
      sharedBytes := sec, sharedSlice := s1, dhOut := d, dhOutZ := z3, dhOutBytes := d, braidSlice := s1,
      hDhKey := hik, hKemSecretZ := hz1, hEncapsulated := hz1d, hShared := hsec, hSharedZ := hz2,
      hSharedBytes := hz2d, hTriple := htriple, hSharedSlice := hs1i, hDhOutBytes := hz3d, hDhOutZ := hz3,
      hDhOut := hd, hBraid := hbraid, hBraidSlice := hs1i, hVerify := hverify }, r3, a2, rfl, rfl, hrp, ?_⟩
  simp only [reachBundle, Tacenta.UnitLifecycleEstablishInitiatorShape.successBundle] at hverify hsec
  generalize List.replicate 32 0#u8 ++ stream = rng0 at hr1 ⊢
  simp [lifecycle.establish_initiator_for, reachBundle, hne, hcanon, hverify, hr1, heph, henc, hz1, hz1d,
    hik, hsec, hz2, hz2d, hr3, hrp, hd, hz3, hz3d, hs1i, hrpub, ha4, ha, htriple, hbraid, hopub, had, hepub,
    InitiatorOutputParts.session]
/-- A byte-stream state of two 32-byte blocks holds two draws, the blocks. -/
theorem byteTrace_pair (a b : List Std.U8) (ha : a.length = 32) (hb : b.length = 32) :
    byteTrace (a ++ b) = [a.map Tacenta.SessionUnitBraidT3.u8, b.map Tacenta.SessionUnitBraidT3.u8] := by
  unfold byteTrace
  rw [chunks32, if_pos (by simp [ha, hb]), chunks32, if_pos (by simp [ha, hb]), chunks32, if_neg (by simp [ha, hb])]
  simp [ha, hb]


/-- **One run from `publish` to the responder's receipt of the second message, for every 32 further bytes of the
initiator's source**: at the real constants, under the laws of `first_send_second_message_reachable` (all assumed), for
every initiator identity, every 64-byte seed at whose bytes the model's key generation answers, every 32 further bytes
`extraB` of the responder's source and every reply and second plaintext of at most 4096 bytes, there are a bundle, a
record `q` of an establishment against it and 32 bytes whose `from_bytes` is `q`'s ratchet private key, such that for
every 32 bytes `extra` there is a run (the first send of the empty plaintext from the seed followed by `extra`,
`establish_responder` on its bytes from a source of 32 bytes chosen by `DhPublicNotConstant` followed by `extraB`, the
responder's `encrypt` of `ptR`, the initiator's `decrypt` of it returning `ptR`, the initiator's `encrypt` of `ptS`) on
which the responder's `decrypt` of the second message from the source its reply left returns `ptS` and leaves a session
passing `Session::invariant` and the ceilings when the oracle's public key of `extra` is not `q`'s ratchet key, and
refuses `Triple(Classical(OutOfOrder))` with the session unchanged when it is.  It applies the two headlines to that run.
Last-resort path only.  No compiler-trust axiom (the pin). -/
theorem second_receipt_reach_run (K : Model.Braid.Kem) (dh : DhView)
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
    (ptR : Slice Std.U8) (hptR : ptR.val.length ≤ 4096) (ptS : Slice Std.U8) (hptS : ptS.val.length ≤ 4096) :
    ∃ (bundle : lifecycle.PublishedBundle) (q : InitiatorSecretParts byteRng byteCrc ourA bundle)
      (sec : Array U8 32#usize),
      tacenta_boundary.dh.PrivateKey.from_bytes sec = ok q.ratchetPrivate ∧
      ∀ extra : List Std.U8, extra.length = 32 →
        ∃ (oracle : Model.Lifecycle.Oracle) (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session)
          (rng' : List Std.U8) (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore) (seedB : List Std.U8)
          (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8) (storeB' : lifecycle.PrekeyStore)
          (rngB' : List Std.U8) (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session)
          (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' : List Std.U8)
          (bytes2 : alloc.vec.Vec Std.U8) (s''' : lifecycle.Session),
          oracle.braidKem = K ∧
          lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext (seed ++ extra) =
            ok (core.result.Result.Ok bytes, s', rng') ∧
          lifecycle.PrekeyStore.publish storeB = ok bundle ∧
          lifecycle.establish_responder byteRng byteCrc ourB storeB (alloc.vec.Vec.deref bytes) (seedB ++ extraB) =
            ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
          lifecycle.Session.encrypt byteRng byteCrc sB' ptR rngB' =
            ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
          lifecycle.Session.decrypt byteRng byteCrc s' (alloc.vec.Vec.deref bytesR) rng' =
            ok (core.result.Result.Ok ptA, s'', rngA') ∧
          ptA.val = ptR.val ∧
          lifecycle.Session.encrypt byteRng byteCrc s'' ptS rngA' = ok (core.result.Result.Ok bytes2, s''', rngA') ∧
          (∀ (sb : Array U8 32#usize) (k : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes)
            (b : Array U8 32#usize), tacenta_boundary.dh.PrivateKey.from_bytes sb = ok k →
            tacenta_boundary.dh.PrivateKey.public_key k = ok pk → tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok b →
            oracle.dhPublic (arrayOf sb) = arrayOf b) ∧
          (oracle.dhPublic (extra.map Tacenta.SessionUnitBraidT3.u8) ≠ arrayOf q.ratchetBytes →
            ∃ (ptB2 : alloc.vec.Vec Std.U8) (sB''' : lifecycle.Session) (rngR2 : List Std.U8),
              lifecycle.Session.decrypt byteRng byteCrc sB'' (alloc.vec.Vec.deref bytes2) rngB' =
                ok (core.result.Result.Ok ptB2, sB''', rngR2) ∧
              ptB2.val = ptS.val ∧ lifecycle.Session.invariant sB''' = ok true ∧
              Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB''') ∧
          (oracle.dhPublic (extra.map Tacenta.SessionUnitBraidT3.u8) = arrayOf q.ratchetBytes →
            ∃ rngR2 : List Std.U8,
              lifecycle.Session.decrypt byteRng byteCrc sB'' (alloc.vec.Vec.deref bytes2) rngB' =
                ok (core.result.Result.Err (lifecycle.Error.Triple
                  (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.OutOfOrder)), sB'', rngR2)) := by
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
  -- the establishment, with the bytes of the initiator's ratchet key
  obtain ⟨q, rng1, sec, hqct, hqss, hsec, h⟩ := reach_establishment_secret c ourA pkb a ha' hcan heq' sig1 sig2
    kemPk hverify hag' stream rest ct ss henc'
  refine ⟨_, q, sec, hsec, ?_⟩
  intro extra hextra
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
  -- the initiator's draw after its first send: the 32 bytes after the seed
  have hdrawA : byteTrace rng' = extra.map Tacenta.SessionUnitBraidT3.u8 :: [] := hrest
  have hu : 4294967295 ≤ Usize.max :=
    Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  -- the responder's source: 32 bytes of a key whose public key is not the peer key the initiator holds, then
  -- the 32 bytes its second receipt draws
  obtain ⟨sbB, kF, pkF, bF, hkF, hpkF, hbF, hne⟩ := (dhPublicNotConstant_is.mp hnc) q.peerRatchetBytes
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
  have hfresh : oracleB.dhPublic (seedB.map Tacenta.SessionUnitBraidT3.u8) ≠ arrayOf q.peerRatchetBytes := by
    show oracle.dhPublic (seedB.map Tacenta.SessionUnitBraidT3.u8) ≠ arrayOf q.peerRatchetBytes
    rw [show seedB.map Tacenta.SessionUnitBraidT3.u8 = arrayOf sbB from rfl, hpubOf sbB kF pkF bF hkF hpkF hbF]
    intro hab
    exact hne (Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes hab)
  -- the two outcomes of the responder's receipt of the second message, on this run
  obtain ⟨_p, _ec, _dSend, _x, _dk, _ekSeed, _ekVector, bytesR, sB'', ptA, s'', rngA', bytes2, s''', res, sB''',
    rngR2, hcallR, hcallA, hpt, hcallS, -, -, -, -, -, -, hcallB2, -, hcases2⟩ :=
    responder_receives_second_message_two_outcomes byteTrace rngB' _ [] hrestB ptS (by omega) byteRng byteCrc
      byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec H.oracleOf
      H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes H.kemCiphertextLen
      H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session H.established q rfl emptyPlaintext H.room
      (seed ++ extra) H.trace_eq _ _ _ htr bytes s' rng' hcall contracts.decrypt ag _ [] hdrawA byteRng byteCrc
      contracts hpub hsym hcon haead hrt L.optionEq oracleB oracleOfB H.braid ag ourB storeB hpublish
      hidentity hdistinct hkem (seedB ++ extraB) rfl _ _ hdrB ptB sB' storeB' rngB' hcallB ptR (by omega) hfresh
  refine ⟨oracle, bytes, s', rng', ourB, storeB, seedB, sB', ptB, storeB', rngB', bytesR, sB'', ptA, s'', rngA',
    bytes2, s''', rfl, hcall, hpublish, hcallB, hcallR, hcallA, hpt, hcallS, hpubOf, ?_, ?_⟩
  · intro hfreshA
    obtain ⟨_p₁, _ec₁, _dSend₁, _x₁, _dk₁, _ekSeed₁, _ekVector₁, bytesR₁, sB''₁, ptA₁, s''₁, rngA'₁, bytes2₁, s'''₁,
      _z₁, ptB2, sB'''₁, rngR2₁,
      hcallR₁, hcallA₁, -, hcallS₁, -, -, -, -, -, hcallB2₁, hpt2, -, -, -, -, hinv3, hc3, -⟩ :=
      responder_receives_second_message byteTrace rngB' _ [] hrestB oracle _ byteRng byteCrc ourA _ q hfreshA ptS
        (by omega) byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView H.braid H.triple H.aead
        H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes
        H.kemCiphertextLen H.kemCiphertextBound _ _ rng1 q.session H.established rfl emptyPlaintext H.room
        (seed ++ extra) H.trace_eq _ _ _ htr bytes s' rng' hcall contracts.decrypt ag [] hdrawA byteRng byteCrc
        contracts hpub hsym hcon haead hrt L.optionEq oracleB oracleOfB H.braid ag ourB storeB hpublish
        hidentity hdistinct hkem (seedB ++ extraB) rfl _ _ hdrB ptB sB' storeB' rngB' hcallB ptR (by omega) hfresh
    rw [hcallR] at hcallR₁
    simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hcallR₁
    obtain ⟨rfl, rfl, -⟩ := hcallR₁
    rw [hcallA] at hcallA₁
    simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hcallA₁
    obtain ⟨rfl, rfl, rfl⟩ := hcallA₁
    rw [hcallS] at hcallS₁
    simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hcallS₁
    obtain ⟨rfl, rfl, -⟩ := hcallS₁
    exact ⟨ptB2, sB'''₁, rngR2₁, hcallB2₁, hpt2, hinv3, hc3⟩
  · intro hstale
    rcases hcases2 with ⟨-, hres, hs⟩ | ⟨hne2, -⟩
    · subst hres hs
      exact ⟨rngR2, hcallB2⟩
    · exact absurd hstale hne2

/-- The run the reach of the receipt exhibits, named so that its pin prints it whole: at an oracle whose KEM is `K`, the
first send of the empty plaintext from `seed ++ extra`, `establish_responder` on its bytes from `seedB ++ extraB`, the
reply, the initiator's receipt of it returning `ptR`, the initiator's second `encrypt` of `ptS`, and the responder's
`decrypt` of its bytes at the session after the reply, from the source the reply left, returning `ptS` and a session that
passes `Session::invariant` and meets `CounterHeadroom`. -/
def SecondReceiptRun (K : Model.Braid.Kem) (ourA : lifecycle.Identity) (seed extraB : List Std.U8)
    (ptR ptS : Slice Std.U8) : Prop :=
  ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle)
    (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (extra : List Std.U8) (bytes : alloc.vec.Vec Std.U8)
    (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (seedB : List Std.U8) (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8) (storeB' : lifecycle.PrekeyStore)
    (rngB' : List Std.U8) (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session) (ptA : alloc.vec.Vec Std.U8)
    (s'' : lifecycle.Session) (rngA' : List Std.U8) (bytes2 : alloc.vec.Vec Std.U8) (s''' : lifecycle.Session)
    (ptB2 : alloc.vec.Vec Std.U8) (sB''' : lifecycle.Session) (rngR2 : List Std.U8),
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
    lifecycle.Session.invariant sB''' = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB'''

/-- The run the stale reach exhibits, named so that its pin prints it whole: as `SecondReceiptRun` up to the second
`encrypt`, with the oracle's public key of the initiator's 32 further bytes its first ratchet key, and the responder's
`decrypt` of the second message refusing `Triple(Classical(OutOfOrder))` with the session after the reply unchanged. -/
def SecondReceiptStaleRun (K : Model.Braid.Kem) (ourA : lifecycle.Identity) (seed extraB : List Std.U8)
    (ptR ptS : Slice Std.U8) : Prop :=
  ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle)
    (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (extra : List Std.U8) (bytes : alloc.vec.Vec Std.U8)
    (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (seedB : List Std.U8) (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8) (storeB' : lifecycle.PrekeyStore)
    (rngB' : List Std.U8) (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session) (ptA : alloc.vec.Vec Std.U8)
    (s'' : lifecycle.Session) (rngA' : List Std.U8) (bytes2 : alloc.vec.Vec Std.U8) (s''' : lifecycle.Session)
    (rngR2 : List Std.U8),
    oracle.braidKem = K ∧ extra.length = 32 ∧
    oracle.dhPublic (extra.map Tacenta.SessionUnitBraidT3.u8) = arrayOf q.ratchetBytes ∧
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
      ok (core.result.Result.Err (lifecycle.Error.Triple
        (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.OutOfOrder)), sB'', rngR2)

/-- **The reach of the responder's receipt of the second message**: at the real constants, under the laws of
`first_send_second_message_reachable` (all assumed, `DhPublicNotConstant` included) and no other, for every initiator
identity, every 64-byte seed at whose bytes the model's key generation answers, every 32 further bytes of the responder's
source, and every reply plaintext `ptR` and second plaintext `ptS` of at most 4096 bytes, `SecondReceiptRun` holds: the
initiator's 32 further bytes are chosen by `DhPublicNotConstant` so that its new ratchet key is not its first, and every
hypothesis of `responder_receives_second_message` holds on the run (`second_receipt_reach_run`).  Last-resort path only.
No compiler-trust axiom (the pin). -/
theorem first_send_second_receipt_reachable (K : Model.Braid.Kem) (dh : DhView)
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
    (ptR : Slice Std.U8) (hptR : ptR.val.length ≤ 4096) (ptS : Slice Std.U8) (hptS : ptS.val.length ≤ 4096) :
    SecondReceiptRun K ourA seed extraB ptR ptS := by
  obtain ⟨bundle, q, -, -, hrun⟩ := second_receipt_reach_run K dh kem L A S hpub hct X RA hsym hrt FS hsizes hcon
    haead hnc ourA seed hseed hkg extraB hextraB ptR hptR ptS hptS
  -- the initiator's 32 further bytes: a key whose public key is not its first ratchet key
  obtain ⟨sbA, kF, pkF, bF, hkF, hpkF, hbF, hne⟩ := (dhPublicNotConstant_is.mp hnc) q.ratchetBytes
  obtain ⟨oracle, bytes, s', rng', ourB, storeB, seedB, sB', ptB, storeB', rngB', bytesR, sB'', ptA, s'', rngA',
    bytes2, s''', hK, hcall, hpublish, hcallB, hcallR, hcallA, hpt, hcallS, hpubOf, hfresh, -⟩ :=
    hrun sbA.val (by simp)
  have hfreshA : oracle.dhPublic (sbA.val.map Tacenta.SessionUnitBraidT3.u8) ≠ arrayOf q.ratchetBytes := by
    rw [show sbA.val.map Tacenta.SessionUnitBraidT3.u8 = arrayOf sbA from rfl, hpubOf sbA kF pkF bF hkF hpkF hbF]
    intro hab
    exact hne (Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes hab)
  obtain ⟨ptB2, sB''', rngR2, hcallB2, hpt2, hinv3, hc3⟩ := hfresh hfreshA
  exact ⟨oracle, bundle, q, sbA.val, bytes, s', rng', ourB, storeB, seedB, sB', ptB, storeB', rngB', bytesR, sB'',
    ptA, s'', rngA', bytes2, s''', ptB2, sB''', rngR2, hK, by simp, hcall, hpublish, hcallB, hcallR, hcallA, hpt,
    hcallS, hcallB2, hpt2, hinv3, hc3⟩

/-- **The refusing arm is reached**: under the same laws, with the initiator's 32 further bytes those of its own first
ratchet key, its new ratchet key is its first, and the responder's `decrypt` of the second message refuses
`Triple(Classical(OutOfOrder))` with its session unchanged (`SecondReceiptStaleRun`), although every earlier call of the
run succeeded.  So the premise `hfreshA` is needed by the success theorem, and its failure is reached.  No compiler-trust
axiom (the pin). -/
theorem first_send_second_receipt_stale_reachable (K : Model.Braid.Kem) (dh : DhView)
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
    (ptR : Slice Std.U8) (hptR : ptR.val.length ≤ 4096) (ptS : Slice Std.U8) (hptS : ptS.val.length ≤ 4096) :
    SecondReceiptStaleRun K ourA seed extraB ptR ptS := by
  obtain ⟨bundle, q, sec, hsec, hrun⟩ := second_receipt_reach_run K dh kem L A S hpub hct X RA hsym hrt FS hsizes
    hcon haead hnc ourA seed hseed hkg extraB hextraB ptR hptR ptS hptS
  -- the initiator's 32 further bytes: the bytes of its own first ratchet key
  obtain ⟨oracle, bytes, s', rng', ourB, storeB, seedB, sB', ptB, storeB', rngB', bytesR, sB'', ptA, s'', rngA',
    bytes2, s''', hK, hcall, hpublish, hcallB, hcallR, hcallA, hpt, hcallS, hpubOf, -, hstale⟩ :=
    hrun sec.val (by simp)
  have hsame : oracle.dhPublic (sec.val.map Tacenta.SessionUnitBraidT3.u8) = arrayOf q.ratchetBytes := by
    rw [show sec.val.map Tacenta.SessionUnitBraidT3.u8 = arrayOf sec from rfl]
    exact hpubOf sec q.ratchetPrivate q.ratchetPublic q.ratchetBytes hsec q.hRatchetPublic q.hRatchetBytes
  obtain ⟨rngR2, hcallB2⟩ := hstale hsame
  exact ⟨oracle, bundle, q, sec.val, bytes, s', rng', ourB, storeB, seedB, sB', ptB, storeB', rngB', bytesR, sB'',
    ptA, s'', rngA', bytes2, s''', rngR2, hK, by simp, hsame, hcall, hpublish, hcallB, hcallR, hcallA, hpt,
    hcallS, hcallB2⟩

end Reach

end Tacenta.UnitLifecycleResponderSecondReceipt

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.second_receive_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.second_receive_key

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.second_receive_stale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.second_receive_stale

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.secondFrame_messageType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.secondFrame_messageType

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.secondFrame_decodeDetailed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.secondFrame_decodeDetailed

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.second_receipt_model_outcomes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.second_receipt_model_outcomes

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.modelCounterRoom_replier' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.modelCounterRoom_replier

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.secondReceipt_inOrderStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.secondReceipt_inOrderStep

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.agreement_swap' depends on axioms: [propext,
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
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
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
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.agreement_swap

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.second_codeword' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.second_codeword

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.established_responder_decoder_small' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
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
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.established_responder_decoder_small

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.second_receipt_run_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.second_receipt_run_inputs

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.secondAd_length_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.secondAd_length_le

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.responder_receives_second_message_two_outcomes' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.responder_receives_second_message_two_outcomes

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.responder_receives_second_message' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.responder_receives_second_message

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.reach_establishment_secret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.reach_establishment_secret

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.byteTrace_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.byteTrace_pair

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.second_receipt_reach_run' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.second_receipt_reach_run

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.first_send_second_receipt_reachable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.first_send_second_receipt_reachable

/--
info: 'Tacenta.UnitLifecycleResponderSecondReceipt.first_send_second_receipt_stale_reachable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderSecondReceipt.first_send_second_receipt_stale_reachable

set_option pp.deepTerms true
set_option pp.proofs.withType true

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.second_receive_key : ∀
  (ec prk k1 k2 a4 d dSend newPub candA xB z newPub2 : Model.State.Key),
  candA ≠ a4 →
    Model.Triple.receiveDetailed (Tacenta.UnitLifecycleResponderReply.replierAfterSend ec prk k1 k2 a4 d dSend newPub)
        (Tacenta.UnitLifecycleInitiatorSecondSend.secondHeader candA) xB z newPub2 none =
      Except.ok
        (Tacenta.UnitLifecycleResponderSecondReceipt.responderAfterSecond ec prk k1 k2 d dSend candA xB z newPub2,
          Tacenta.UnitLifecycleInitiatorSecondSend.secondKey (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 k1
            dSend xB)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.second_receive_key

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.second_receive_stale : ∀
  (ec prk k1 k2 a4 d dSend newPub xB z newPub2 : Model.State.Key),
  Model.Triple.receiveDetailed (Tacenta.UnitLifecycleResponderReply.replierAfterSend ec prk k1 k2 a4 d dSend newPub)
      (Tacenta.UnitLifecycleInitiatorSecondSend.secondHeader a4) xB z newPub2 none =
    Except.error (Model.Triple.ReceiveRefusal.classical Model.Ratchet.ReceiveRefusal.outOfOrder)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.second_receive_stale

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.secondFrame_messageType : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (ad : Model.Lifecycle.Bytes) (braid : Model.Braid.BraidState)
  (candA mk : Model.State.Key) (chunk : Model.Braid.Chunk) (pt : Model.Lifecycle.Bytes),
  Model.Lifecycle.messageType
      (Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame view oracle ad braid candA mk chunk pt) =
    some Model.Lifecycle.MessageType.ratchet
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.secondFrame_messageType

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.secondFrame_decodeDetailed : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (ad : Model.Lifecycle.Bytes) (braid : Model.Braid.BraidState)
  (candA mk : Model.State.Key) (chunk : Model.Braid.Chunk) (pt : Model.Lifecycle.Bytes),
  List.length candA = 32 →
    Model.Messages.checkKey candA = some () →
      (view.send braid chunk).data.length = 32 →
        Model.CompositeHeader.decodeDetailed
            (Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame view oracle ad braid candA mk chunk pt) =
          Except.ok
            (Tacenta.UnitLifecycleInitiatorSecondSend.secondComposite view braid candA chunk,
              oracle.aeadSeal (Model.State.messageKeys mk Model.State.LabelSet.tacenta).1
                (Model.State.messageKeys mk Model.State.LabelSet.tacenta).2.1
                (Model.State.messageKeys mk Model.State.LabelSet.tacenta).2.2 pt
                (Tacenta.UnitLifecycleResponderSecondReceipt.secondAd view ad braid candA chunk))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.secondFrame_decodeDetailed

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.second_receipt_model_outcomes : ∀
  (view viewA : Model.Lifecycle.CodewordView) (oracleB oracleA : Model.Lifecycle.Oracle) (mB : Model.Lifecycle.Session)
  (ec prk k1 k2 a4 d dSend newPub : Model.State.Key),
  mB.triple = Tacenta.UnitLifecycleResponderReply.replierAfterSend ec prk k1 k2 a4 d dSend newPub →
    ∀ (braidA : Model.Braid.BraidState) (chunk : Model.Braid.Chunk) (candA xB : Model.State.Key)
      (pt : Model.Lifecycle.Bytes) (e : ℕ) (braid' : Model.Braid.BraidState),
      Model.Lifecycle.agreementFailed mB = false →
        List.length candA = 32 →
          Model.Messages.checkKey candA = some () →
            (viewA.send braidA chunk).data.length = 32 →
              Model.Braid.receive oracleB.braidKem mB.braid
                    (Model.Lifecycle.braidMessageOf view mB.braid
                      (Tacenta.UnitLifecycleInitiatorSecondSend.secondComposite viewA braidA candA chunk)) =
                  (e, none, braid') →
                oracleB.dhAgree mB.ratchetPrivate candA = some xB →
                  oracleB.draws = [] ∧
                      Model.Lifecycle.decrypt view oracleB mB
                          (Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame viewA oracleA mB.identityAd braidA candA
                            (Tacenta.UnitLifecycleInitiatorSecondSend.secondKey
                              (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 k1 dSend xB)
                            chunk pt) =
                        { session := mB, result := Except.error Model.Lifecycle.Refusal.ceiling, oracle := oracleB } ∨
                    (∃ c rest,
                        oracleB.draws = c :: rest ∧
                          oracleB.dhAgree c candA = none ∧
                            Model.Lifecycle.decrypt view oracleB mB
                                (Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame viewA oracleA mB.identityAd braidA
                                  candA
                                  (Tacenta.UnitLifecycleInitiatorSecondSend.secondKey
                                    (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 k1 dSend xB)
                                  chunk pt) =
                              { session := mB,
                                result :=
                                  Except.error
                                    (Model.Lifecycle.Refusal.handshake
                                      Model.Lifecycle.HandshakeRefusal.nonContributoryAgreement),
                                oracle :=
                                  { draws := rest, braidKem := oracleB.braidKem, dhPublic := oracleB.dhPublic,
                                    dhAgree := oracleB.dhAgree, identityValid := oracleB.identityValid,
                                    aeadSeal := oracleB.aeadSeal, aeadOpen := oracleB.aeadOpen,
                                    kemValid := oracleB.kemValid, kemEncaps := oracleB.kemEncaps,
                                    kemDecaps := oracleB.kemDecaps, sigVerify := oracleB.sigVerify,
                                    sigSign := oracleB.sigSign } }) ∨
                      (∃ c rest z,
                          oracleB.draws = c :: rest ∧
                            oracleB.dhAgree c candA = some z ∧
                              candA = a4 ∧
                                Model.Lifecycle.decrypt view oracleB mB
                                    (Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame viewA oracleA mB.identityAd
                                      braidA candA
                                      (Tacenta.UnitLifecycleInitiatorSecondSend.secondKey
                                        (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 k1 dSend xB)
                                      chunk pt) =
                                  { session := mB,
                                    result :=
                                      Except.error
                                        (Model.Lifecycle.tripleReceiveRefusalOf
                                          (Model.Triple.ReceiveRefusal.classical
                                            Model.Ratchet.ReceiveRefusal.outOfOrder)),
                                    oracle :=
                                      { draws := rest, braidKem := oracleB.braidKem, dhPublic := oracleB.dhPublic,
                                        dhAgree := oracleB.dhAgree, identityValid := oracleB.identityValid,
                                        aeadSeal := oracleB.aeadSeal, aeadOpen := oracleB.aeadOpen,
                                        kemValid := oracleB.kemValid, kemEncaps := oracleB.kemEncaps,
                                        kemDecaps := oracleB.kemDecaps, sigVerify := oracleB.sigVerify,
                                        sigSign := oracleB.sigSign } }) ∨
                        (∃ c rest z,
                            oracleB.draws = c :: rest ∧
                              oracleB.dhAgree c candA = some z ∧
                                candA ≠ a4 ∧
                                  Tacenta.UnitLifecycleResponderFirstReceipt.firstOpen oracleA oracleB
                                        (Tacenta.UnitLifecycleInitiatorSecondSend.secondKey
                                          (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 k1 dSend xB)
                                        pt
                                        (Tacenta.UnitLifecycleResponderSecondReceipt.secondAd viewA mB.identityAd braidA
                                          candA chunk) =
                                      none ∧
                                    Model.Lifecycle.decrypt view oracleB mB
                                        (Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame viewA oracleA
                                          mB.identityAd braidA candA
                                          (Tacenta.UnitLifecycleInitiatorSecondSend.secondKey
                                            (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 k1 dSend xB)
                                          chunk pt) =
                                      { session := mB, result := Except.error Model.Lifecycle.Refusal.aead,
                                        oracle :=
                                          { draws := rest, braidKem := oracleB.braidKem, dhPublic := oracleB.dhPublic,
                                            dhAgree := oracleB.dhAgree, identityValid := oracleB.identityValid,
                                            aeadSeal := oracleB.aeadSeal, aeadOpen := oracleB.aeadOpen,
                                            kemValid := oracleB.kemValid, kemEncaps := oracleB.kemEncaps,
                                            kemDecaps := oracleB.kemDecaps, sigVerify := oracleB.sigVerify,
                                            sigSign := oracleB.sigSign } }) ∨
                          ∃ c rest z y,
                            oracleB.draws = c :: rest ∧
                              oracleB.dhAgree c candA = some z ∧
                                candA ≠ a4 ∧
                                  Tacenta.UnitLifecycleResponderFirstReceipt.firstOpen oracleA oracleB
                                        (Tacenta.UnitLifecycleInitiatorSecondSend.secondKey
                                          (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 k1 dSend xB)
                                        pt
                                        (Tacenta.UnitLifecycleResponderSecondReceipt.secondAd viewA mB.identityAd braidA
                                          candA chunk) =
                                      some y ∧
                                    Model.Lifecycle.decrypt view oracleB mB
                                        (Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame viewA oracleA
                                          mB.identityAd braidA candA
                                          (Tacenta.UnitLifecycleInitiatorSecondSend.secondKey
                                            (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 k1 dSend xB)
                                          chunk pt) =
                                      {
                                        session :=
                                          Tacenta.UnitLifecycleResponderSecondReceipt.secondReceiptSession mB braid' ec
                                            prk k1 k2 d dSend candA xB z (oracleB.dhPublic c) c,
                                        result := Except.ok y,
                                        oracle :=
                                          { draws := rest, braidKem := oracleB.braidKem, dhPublic := oracleB.dhPublic,
                                            dhAgree := oracleB.dhAgree, identityValid := oracleB.identityValid,
                                            aeadSeal := oracleB.aeadSeal, aeadOpen := oracleB.aeadOpen,
                                            kemValid := oracleB.kemValid, kemEncaps := oracleB.kemEncaps,
                                            kemDecaps := oracleB.kemDecaps, sigVerify := oracleB.sigVerify,
                                            sigSign := oracleB.sigSign } }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.second_receipt_model_outcomes

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.modelCounterRoom_replier : ∀ (mB : Model.Lifecycle.Session)
  (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk) (ec prk k1 k2 a4 d dSend newPub c : Model.State.Key)
  (k : ℕ),
  k + 2 < U32.max →
    Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom
      (Tacenta.UnitLifecycleResponderSecondReceipt.replierSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c) k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.modelCounterRoom_replier

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.secondReceipt_inOrderStep : ∀ (oracle : Model.Lifecycle.Oracle)
  (mB : Model.Lifecycle.Session) (ec prk k1 k2 a4 d dSend newPub candA xB z c : Model.State.Key)
  (auth : Model.Braid.Auth) (dec dec' : Model.Braid.Decoder),
  mB.triple = Tacenta.UnitLifecycleResponderReply.replierAfterSend ec prk k1 k2 a4 d dSend newPub →
    mB.braid = Model.Braid.BraidState.noHeaderReceived 1 auth dec →
      candA ≠ a4 →
        Model.Messages.canonicalKey candA = true →
          Tacenta.UnitLifecycleReceivePreserve.InOrderReceiveStep oracle mB
            (Tacenta.UnitLifecycleResponderSecondReceipt.secondReceiptSession mB
              (Model.Braid.BraidState.noHeaderReceived 1 auth dec') ec prk k1 k2 d dSend candA xB z (oracle.dhPublic c)
              c)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.secondReceipt_inOrderStep

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.agreement_swap : Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
  ∀ {dh : Tacenta.UnitLifecycleT3.DhView} {R E : Type} {rcX : rand_core_1.RngCore R} {crcX : rand_core_1.CryptoRng R}
    {traceX : R → List Model.Lifecycle.Key} {oX : Model.Lifecycle.Oracle},
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcX crcX dh traceX oX →
      ∀ {rcY : rand_core_1.RngCore E} {crcY : rand_core_1.CryptoRng E} {traceY : E → List Model.Lifecycle.Key}
        {oY : Model.Lifecycle.Oracle},
        Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcY crcY dh traceY oY →
          ∀ (a b : tacenta_boundary.dh.PrivateKey) (pa pb : tacenta_boundary.dh.PublicKeyBytes),
            a.public_key = ok pa →
              b.public_key = ok pb →
                oX.dhAgree (dh.privateKey a) (dh.publicKey pb) = oY.dhAgree (dh.privateKey b) (dh.publicKey pa)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.agreement_swap

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.second_codeword : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  Tacenta.SessionUnitBraidT3.ErasureAgrees →
    ∀ (m : Model.Lifecycle.Bytes), List.length m = 96 → ∃ c, Tacenta.SessionUnitBraidT3.CodewordOf m c ∧ ↑c.index = 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.second_codeword

/--
info: @Tacenta.UnitLifecycleResponderSecondReceipt.established_responder_decoder_small : ∀ {R : Type}
  (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (our : lifecycle.Identity)
  (store : lifecycle.PrekeyStore) (msg : Slice U8) (rng : R) (sB' : lifecycle.Session) (pt : alloc.vec.Vec U8)
  (store' : lifecycle.PrekeyStore) (rng' : R),
  lifecycle.establish_responder rc crc our store msg rng = ok (core.result.Result.Ok (sB', pt), store', rng') →
    ∀ (e : U64) (a : tacenta_braid.Auth) (d : tacenta_erasure.Decoder),
      sB'.braid.state = tacenta_braid.State.NoHeaderReceived e a d → (↑d.have).length ≤ 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.established_responder_decoder_small

/--
info: @Tacenta.UnitLifecycleResponderSecondReceipt.second_receipt_run_inputs : ∀ {E : Type}
  (view : Model.Lifecycle.CodewordView) (oracleA oracleB : Model.Lifecycle.Oracle)
  (traceB : E → List Model.Lifecycle.Key) (real : lifecycle.Session) (mB : Model.Lifecycle.Session) (msg : Slice U8)
  (braidA : Model.Braid.BraidState) (candA mk : Model.Lifecycle.Key) (pt src : Model.Lifecycle.Bytes)
  (c : tacenta_erasure.Chunk),
  Tacenta.SessionUnitBraidT3.CodewordOf src c →
    view.send braidA (Tacenta.UnitLifecycleT3.modelChunkOf src c) = Tacenta.UnitLifecycleT3.modelCodewordOf c →
      List.length candA = 32 →
        Model.Messages.checkKey candA = some () →
          Tacenta.UnitLifecycleT3.sliceOf msg =
              Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame view oracleA mB.identityAd braidA candA mk
                (Tacenta.UnitLifecycleT3.modelChunkOf src c) pt →
            ∀ (e : ℕ) (auth : Model.Braid.Auth) (dec : Model.Braid.Decoder),
              mB.braid = Model.Braid.BraidState.noHeaderReceived e auth dec →
                (List.length src = dec.size ∧ ∀ x ∈ dec.chunks, x.source = src) →
                  ∀ (rngB : E) (dB : Model.Lifecycle.Key) (restB : List Model.Lifecycle.Key),
                    traceB rngB = dB :: restB →
                      Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs
                        (Tacenta.UnitLifecycleResponderFirstReceipt.attributedView view
                          (Tacenta.UnitLifecycleT3.modelCodewordOf c).index
                          (Tacenta.UnitLifecycleT3.modelCodewordOf c).data (Tacenta.UnitLifecycleT3.modelChunkOf src c))
                        oracleB traceB real mB msg rngB
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.second_receipt_run_inputs

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.secondAd_length_le : Tacenta.UnitLifecycleT1.DhCodecTotal →
  ∀ {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity}
    {bundle : lifecycle.PublishedBundle}
    (q : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle)
    (view : Model.Lifecycle.CodewordView) (braid : Model.Braid.BraidState) (candA : Model.Lifecycle.Key)
    (chunk : Model.Braid.Chunk),
    List.length candA = 32 →
      (view.send braid chunk).data.length = 32 →
        List.length
            (Tacenta.UnitLifecycleResponderSecondReceipt.secondAd view (Tacenta.UnitLifecycleT3.vecOf q.identityAd)
              braid candA chunk) ≤
          Usize.max
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.secondAd_length_le

/--
info: @Tacenta.UnitLifecycleResponderSecondReceipt.responder_receives_second_message_two_outcomes : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type} (traceB : F → List Model.Lifecycle.Key) (rngR : F)
  (dB2 : Model.Lifecycle.Key) (restB2 : List Model.Lifecycle.Key),
  traceB rngR = dB2 :: restB2 →
    ∀ (ptS : Slice U8),
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
                                              Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcE crcE
                                                ourA bundleA),
                                            s = q.session →
                                              ∀ (plaintext : Slice U8),
                                                (↑plaintext).length + 65770 ≤ Usize.max →
                                                  ∀ (rng : R),
                                                    trace rng = oracle.draws →
                                                      ∀ (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
                                                        trace rng = d1 :: d2 :: rest →
                                                          ∀ (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session)
                                                            (rng' : R),
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
                                                                                                      ∀ (rngB : F),
                                                                                                        traceB rngB =
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
                                                                                                                          dk
                                                                                                                          ekSeed
                                                                                                                          ekVector
                                                                                                                          bytesR
                                                                                                                          sB''
                                                                                                                          ptA
                                                                                                                          s''
                                                                                                                          rngA'
                                                                                                                          bytes2
                                                                                                                          s'''
                                                                                                                          res
                                                                                                                          sB'''
                                                                                                                          rngR2,
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
                                                                                                                                    oracle.dhAgree
                                                                                                                                          dA
                                                                                                                                          (oracleB.dhPublic
                                                                                                                                            dB) =
                                                                                                                                        some
                                                                                                                                          x ∧
                                                                                                                                      Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                                                          dh
                                                                                                                                          oracleB.braidKem
                                                                                                                                          sB''
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
                                                                                                                                            dB) ∧
                                                                                                                                        sB''.braid =
                                                                                                                                            sB'.braid ∧
                                                                                                                                          sB''.invariant =
                                                                                                                                              ok
                                                                                                                                                true ∧
                                                                                                                                            Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                                                                                sB'' ∧
                                                                                                                                              lifecycle.Session.decrypt
                                                                                                                                                    rcB
                                                                                                                                                    crcB
                                                                                                                                                    sB''
                                                                                                                                                    bytes2.deref
                                                                                                                                                    rngR =
                                                                                                                                                  ok
                                                                                                                                                    (res,
                                                                                                                                                      sB''',
                                                                                                                                                      rngR2) ∧
                                                                                                                                                traceB
                                                                                                                                                      rngR2 =
                                                                                                                                                    restB2 ∧
                                                                                                                                                  (oracle.dhPublic
                                                                                                                                                          dA =
                                                                                                                                                        Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                          q.ratchetBytes ∧
                                                                                                                                                      res =
                                                                                                                                                          core.result.Result.Err
                                                                                                                                                            (lifecycle.Error.Triple
                                                                                                                                                              (tacenta_triple.TripleError.Classical
                                                                                                                                                                tacenta_ratchet.RatchetError.OutOfOrder)) ∧
                                                                                                                                                        sB''' =
                                                                                                                                                          sB'' ∨
                                                                                                                                                    oracle.dhPublic
                                                                                                                                                          dA ≠
                                                                                                                                                        Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                          q.ratchetBytes ∧
                                                                                                                                                      ∃
                                                                                                                                                        z
                                                                                                                                                        ptB2,
                                                                                                                                                        oracleB.dhAgree
                                                                                                                                                              dB2
                                                                                                                                                              (oracle.dhPublic
                                                                                                                                                                dA) =
                                                                                                                                                            some
                                                                                                                                                              z ∧
                                                                                                                                                          res =
                                                                                                                                                              core.result.Result.Ok
                                                                                                                                                                ptB2 ∧
                                                                                                                                                            ↑ptB2 =
                                                                                                                                                                ↑ptS ∧
                                                                                                                                                              sB'''.pending_initial =
                                                                                                                                                                  none ∧
                                                                                                                                                                sB''' =
                                                                                                                                                                    {
                                                                                                                                                                      triple :=
                                                                                                                                                                        sB'''.triple,
                                                                                                                                                                      braid :=
                                                                                                                                                                        sB'''.braid,
                                                                                                                                                                      ratchet_private :=
                                                                                                                                                                        sB'''.ratchet_private,
                                                                                                                                                                      identity_ad :=
                                                                                                                                                                        sB''.identity_ad,
                                                                                                                                                                      our_identity_public :=
                                                                                                                                                                        sB''.our_identity_public,
                                                                                                                                                                      peer_identity_public :=
                                                                                                                                                                        sB''.peer_identity_public,
                                                                                                                                                                      pending_initial :=
                                                                                                                                                                        none,
                                                                                                                                                                      established_ephemeral :=
                                                                                                                                                                        sB''.established_ephemeral } ∧
                                                                                                                                                                  Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                                                                                    dh
                                                                                                                                                                    oracleB.braidKem
                                                                                                                                                                    sB'''
                                                                                                                                                                    (Tacenta.UnitLifecycleResponderSecondReceipt.secondReceiptSession
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
                                                                                                                                                                      dB2))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.responder_receives_second_message_two_outcomes

/--
info: @Tacenta.UnitLifecycleResponderSecondReceipt.responder_receives_second_message : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type} (traceB : F → List Model.Lifecycle.Key) (rngR : F)
  (dB2 : Model.Lifecycle.Key) (restB2 : List Model.Lifecycle.Key),
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
                                  Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
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
                                                                                                        ∀ (rngB : F),
                                                                                                          traceB rngB =
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
                                                                                                                            dk
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
                                                                                                                            rngR2,
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
                                                                                                                                          sB''.invariant =
                                                                                                                                              ok
                                                                                                                                                true ∧
                                                                                                                                            Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                                                                                sB'' ∧
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
                                                                                                                                                    sB'''.pending_initial =
                                                                                                                                                        none ∧
                                                                                                                                                      sB''' =
                                                                                                                                                          {
                                                                                                                                                            triple :=
                                                                                                                                                              sB'''.triple,
                                                                                                                                                            braid :=
                                                                                                                                                              sB'''.braid,
                                                                                                                                                            ratchet_private :=
                                                                                                                                                              sB'''.ratchet_private,
                                                                                                                                                            identity_ad :=
                                                                                                                                                              sB''.identity_ad,
                                                                                                                                                            our_identity_public :=
                                                                                                                                                              sB''.our_identity_public,
                                                                                                                                                            peer_identity_public :=
                                                                                                                                                              sB''.peer_identity_public,
                                                                                                                                                            pending_initial :=
                                                                                                                                                              none,
                                                                                                                                                            established_ephemeral :=
                                                                                                                                                              sB''.established_ephemeral } ∧
                                                                                                                                                        Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                                                                            dh
                                                                                                                                                            oracleB.braidKem
                                                                                                                                                            sB'''
                                                                                                                                                            (Tacenta.UnitLifecycleResponderSecondReceipt.secondReceiptSession
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
                                                                                                                                                              dB2) ∧
                                                                                                                                                          sB'''.invariant =
                                                                                                                                                              ok
                                                                                                                                                                true ∧
                                                                                                                                                            Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                                                                                                sB''' ∧
                                                                                                                                                              ∀
                                                                                                                                                                (j :
                                                                                                                                                                  ℕ),
                                                                                                                                                                j +
                                                                                                                                                                      3 <
                                                                                                                                                                    U32.max →
                                                                                                                                                                  Tacenta.UnitLifecycleSendPreserve.CounterRoom
                                                                                                                                                                    sB'''
                                                                                                                                                                    j
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.responder_receives_second_message

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.reach_establishment_secret : ∀
  (c : Tacenta.UnitLifecycleT1.EstablishInitiatorContracts Tacenta.UnitLifecycleIntegrationScreen.byteRng)
  (ourA : lifecycle.Identity) (pkb : tacenta_boundary.dh.PublicKeyBytes) (a : Std.Array U8 32#usize),
  pkb.as_bytes = ok a →
    Tacenta.SessionUnitT1.canonicalX25519 a = true →
      tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq pkb pkb = ok true →
        ∀ (sig1 sig2 : Std.Array U8 64#usize) (kemPk : alloc.vec.Vec U8),
          verify_bundle (Tacenta.UnitLifecycleResponderFirstFrame.reachBundle pkb sig1 sig2 kemPk).bundle =
              ok (core.result.Result.Ok ()) →
            (∀ (k : tacenta_boundary.dh.PrivateKey), ∃ x, k.agree pkb = ok (some x)) →
              ∀ (stream rest : List U8) (ct : alloc.vec.Vec U8) (ss : Std.Array U8 32#usize),
                tacenta_boundary.kem.encapsulate Tacenta.UnitLifecycleIntegrationScreen.byteRng
                      Tacenta.UnitLifecycleIntegrationScreen.byteCrc kemPk.deref stream =
                    ok (core.result.Result.Ok (ct, ss), rest) →
                  ∃ q rng1 sec,
                    q.kemCiphertext = ct ∧
                      q.kemSecret = ss ∧
                        tacenta_boundary.dh.PrivateKey.from_bytes sec = ok q.ratchetPrivate ∧
                          lifecycle.establish_initiator_for Tacenta.UnitLifecycleIntegrationScreen.byteRng
                              Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourA
                              (Tacenta.UnitLifecycleResponderFirstFrame.reachBundle pkb sig1 sig2 kemPk) pkb
                              (List.replicate 32 0#u8 ++ stream) =
                            ok (core.result.Result.Ok q.session, rng1)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.reach_establishment_secret

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.byteTrace_pair : ∀ (a b : List U8),
  a.length = 32 →
    b.length = 32 →
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace (a ++ b) =
        [List.map Tacenta.SessionUnitBraidT3.u8 a, List.map Tacenta.SessionUnitBraidT3.u8 b]
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.byteTrace_pair

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.second_receipt_reach_run : ∀ (K : Model.Braid.Kem)
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
                                                ∃ bundle q sec,
                                                  tacenta_boundary.dh.PrivateKey.from_bytes sec = ok q.ratchetPrivate ∧
                                                    ∀ (extra : List U8),
                                                      extra.length = 32 →
                                                        ∃ oracle bytes s' rng' ourB storeB seedB sB' ptB storeB' rngB'
                                                          bytesR sB'' ptA s'' rngA' bytes2 s''',
                                                          oracle.braidKem = K ∧
                                                            lifecycle.Session.encrypt
                                                                  Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                  Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                                                  q.session
                                                                  Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext
                                                                  (seed ++ extra) =
                                                                ok (core.result.Result.Ok bytes, s', rng') ∧
                                                              storeB.publish = ok bundle ∧
                                                                lifecycle.establish_responder
                                                                      Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                      Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                                                      ourB storeB bytes.deref (seedB ++ extraB) =
                                                                    ok
                                                                      (core.result.Result.Ok (sB', ptB), storeB',
                                                                        rngB') ∧
                                                                  lifecycle.Session.encrypt
                                                                        Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                        Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                                                        sB' ptR rngB' =
                                                                      ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
                                                                    lifecycle.Session.decrypt
                                                                          Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                          Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                                                          s' bytesR.deref rng' =
                                                                        ok (core.result.Result.Ok ptA, s'', rngA') ∧
                                                                      ↑ptA = ↑ptR ∧
                                                                        lifecycle.Session.encrypt
                                                                              Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                              Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                                                              s'' ptS rngA' =
                                                                            ok
                                                                              (core.result.Result.Ok bytes2, s''',
                                                                                rngA') ∧
                                                                          (∀ (sb : Std.Array U8 32#usize)
                                                                              (k : tacenta_boundary.dh.PrivateKey)
                                                                              (pk : tacenta_boundary.dh.PublicKeyBytes)
                                                                              (b : Std.Array U8 32#usize),
                                                                              tacenta_boundary.dh.PrivateKey.from_bytes
                                                                                    sb =
                                                                                  ok k →
                                                                                k.public_key = ok pk →
                                                                                  pk.as_bytes = ok b →
                                                                                    oracle.dhPublic
                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                          sb) =
                                                                                      Tacenta.UnitLifecycleT3.arrayOf
                                                                                        b) ∧
                                                                            (oracle.dhPublic
                                                                                    (List.map
                                                                                      Tacenta.SessionUnitBraidT3.u8
                                                                                      extra) ≠
                                                                                  Tacenta.UnitLifecycleT3.arrayOf
                                                                                    q.ratchetBytes →
                                                                                ∃ ptB2 sB''' rngR2,
                                                                                  lifecycle.Session.decrypt
                                                                                        Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                                        Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                                                                        sB'' bytes2.deref rngB' =
                                                                                      ok
                                                                                        (core.result.Result.Ok ptB2,
                                                                                          sB''', rngR2) ∧
                                                                                    ↑ptB2 = ↑ptS ∧
                                                                                      sB'''.invariant = ok true ∧
                                                                                        Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                          sB''') ∧
                                                                              (oracle.dhPublic
                                                                                    (List.map
                                                                                      Tacenta.SessionUnitBraidT3.u8
                                                                                      extra) =
                                                                                  Tacenta.UnitLifecycleT3.arrayOf
                                                                                    q.ratchetBytes →
                                                                                ∃ rngR2,
                                                                                  lifecycle.Session.decrypt
                                                                                      Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                                      Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                                                                      sB'' bytes2.deref rngB' =
                                                                                    ok
                                                                                      (core.result.Result.Err
                                                                                          (lifecycle.Error.Triple
                                                                                            (tacenta_triple.TripleError.Classical
                                                                                              tacenta_ratchet.RatchetError.OutOfOrder)),
                                                                                        sB'', rngR2))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.second_receipt_reach_run

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.first_send_second_receipt_reachable : ∀ (K : Model.Braid.Kem)
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
                                                Tacenta.UnitLifecycleResponderSecondReceipt.SecondReceiptRun K ourA seed
                                                  extraB ptR ptS
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.first_send_second_receipt_reachable

/--
info: Tacenta.UnitLifecycleResponderSecondReceipt.first_send_second_receipt_stale_reachable : ∀ (K : Model.Braid.Kem)
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
                                                Tacenta.UnitLifecycleResponderSecondReceipt.SecondReceiptStaleRun K ourA
                                                  seed extraB ptR ptS
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderSecondReceipt.first_send_second_receipt_stale_reachable

/--
info: def Tacenta.UnitLifecycleResponderSecondReceipt.responderAfterSecond : Model.State.Key →
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
            (Model.State.kdfRk
                (Model.State.kdfRk
                    (Model.State.kdfRk (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 dSend
                        Model.State.LabelSet.tacenta).1
                    xB Model.State.LabelSet.tacenta).1
                z Model.State.LabelSet.tacenta).2,
        ckr :=
          some
            (Model.State.kdfCk
                (Model.State.kdfRk
                    (Model.State.kdfRk (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 dSend
                        Model.State.LabelSet.tacenta).1
                    xB Model.State.LabelSet.tacenta).2).1,
        ns := 0, nr := 1, pn := 1, skipped := [], events := 2, labels := Model.State.LabelSet.tacenta },
    postQuantum :=
      { rk := prk, epoch := 0,
        chains :=
          [(0,
              { send := some { ck := (Model.SparseRatchet.kdfCk k2 1).1, n := 1 },
                receive :=
                  some { ck := (Model.SparseRatchet.kdfCk (Model.SparseRatchet.kdfCk k1 1).1 2).1, n := 2 } })],
        skipped := [], direction := Model.SparseRatchet.Direction.b2a } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderSecondReceipt.responderAfterSecond

/--
info: def Tacenta.UnitLifecycleResponderSecondReceipt.secondAd : Model.Lifecycle.CodewordView →
  Model.Lifecycle.Bytes → Model.Braid.BraidState → Model.State.Key → Model.Braid.Chunk → Model.Lifecycle.Bytes :=
fun view ad braid candA chunk =>
  Model.Messages.concatAd ad
    (Model.CompositeHeader.encode (Tacenta.UnitLifecycleInitiatorSecondSend.secondComposite view braid candA chunk))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderSecondReceipt.secondAd

/--
info: def Tacenta.UnitLifecycleResponderSecondReceipt.replierSession : Model.Lifecycle.Session →
  Model.Lifecycle.Bytes →
    Model.Braid.Chunk →
      Model.State.Key →
        Model.State.Key →
          Model.State.Key →
            Model.State.Key →
              Model.State.Key →
                Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.Lifecycle.Session :=
fun mB secret rcv ec prk k1 k2 a4 d dSend newPub c =>
  have __src :=
    Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession mB secret rcv ec prk k1 k2 a4 d dSend newPub c;
  { triple := Tacenta.UnitLifecycleResponderReply.replierAfterSend ec prk k1 k2 a4 d dSend newPub, braid := __src.braid,
    ratchetPrivate := __src.ratchetPrivate, identityAd := __src.identityAd,
    ourIdentityPublic := __src.ourIdentityPublic, peerIdentityPublic := __src.peerIdentityPublic,
    pendingInitial := __src.pendingInitial, establishedEphemeral := __src.establishedEphemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderSecondReceipt.replierSession

/--
info: def Tacenta.UnitLifecycleResponderSecondReceipt.secondReceiptSession : Model.Lifecycle.Session →
  Model.Braid.BraidState →
    Model.State.Key →
      Model.State.Key →
        Model.State.Key →
          Model.State.Key →
            Model.State.Key →
              Model.State.Key →
                Model.State.Key →
                  Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.Lifecycle.Session :=
fun mB braid' ec prk k1 k2 d dSend candA xB z newPub2 c =>
  { triple := Tacenta.UnitLifecycleResponderSecondReceipt.responderAfterSecond ec prk k1 k2 d dSend candA xB z newPub2,
    braid := braid', ratchetPrivate := if (newPub2 == mB.triple.classical.dhsPub) = true then mB.ratchetPrivate else c,
    identityAd := mB.identityAd, ourIdentityPublic := mB.ourIdentityPublic, peerIdentityPublic := mB.peerIdentityPublic,
    pendingInitial := none, establishedEphemeral := mB.establishedEphemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderSecondReceipt.secondReceiptSession

/--
info: def Tacenta.UnitLifecycleResponderSecondReceipt.SecondReceiptRun : Model.Braid.Kem →
  lifecycle.Identity → List U8 → List U8 → Slice U8 → Slice U8 → Prop :=
fun K ourA seed extraB ptR ptS =>
  ∃ oracle bundle q extra bytes s' rng' ourB storeB seedB sB' ptB storeB' rngB' bytesR sB'' ptA s'' rngA' bytes2 s'''
    ptB2 sB''' rngR2,
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
                          sB'''.invariant = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB'''
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderSecondReceipt.SecondReceiptRun

/--
info: def Tacenta.UnitLifecycleResponderSecondReceipt.SecondReceiptStaleRun : Model.Braid.Kem →
  lifecycle.Identity → List U8 → List U8 → Slice U8 → Slice U8 → Prop :=
fun K ourA seed extraB ptR ptS =>
  ∃ oracle bundle q extra bytes s' rng' ourB storeB seedB sB' ptB storeB' rngB' bytesR sB'' ptA s'' rngA' bytes2 s'''
    rngR2,
    oracle.braidKem = K ∧
      extra.length = 32 ∧
        oracle.dhPublic (List.map Tacenta.SessionUnitBraidT3.u8 extra) =
            Tacenta.UnitLifecycleT3.arrayOf q.ratchetBytes ∧
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
                          ok
                            (core.result.Result.Err
                                (lifecycle.Error.Triple
                                  (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.OutOfOrder)),
                              sB'', rngR2)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderSecondReceipt.SecondReceiptStaleRun
