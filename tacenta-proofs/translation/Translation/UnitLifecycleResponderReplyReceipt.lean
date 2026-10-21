import Translation.UnitLifecycleResponderReply
import Translation.UnitLifecycleDecryptT3

/-!
# The initiator receives the reply: `Session::decrypt` of the responder's reply

`UnitLifecycleResponderReply` shows that the responder's `Session::encrypt` at the session `sB'` that
`establish_responder` returned on the initiator's first frame returns the bare reply frame.  This module takes those
bytes, on the same run, to the initiator: its public `Session::decrypt` at the session `s'` its own first `encrypt`
left, from the source that `encrypt` left.  The chain is one run: the initiator's first send (`s'`, `bytes`, `rng'`),
the responder's receipt of `bytes` (`sB'`), the responder's reply (`bytesR`), the initiator's receipt of `bytesR`.

## How

* `reply_receive_key`, `reply_receive_stale`, `reply_receipt_model_outcomes` (model only): the model Triple's
  receive of the reply's header at the sender after its first message (`senderAfterFirst`) takes one
  Diffie-Hellman step and derives `firstKey (kdfRk rkA dSend).2 k2` when the reply's ratchet key is not the peer key
  the sender holds, and refuses `noReceivingChain` when it is (no step is taken and the sender has no receiving
  chain); the model's public `decrypt` of the reply frame there has exactly the outcomes listed below.  The
  model agreement's receive at `keysSampled` of a message of type `none` leaves the agreement as it was.
* `fresh_public_of_draw`, `initiator_reply_agreement`, `initiator_candidate_agreement` (bridges): the responder's
  fresh ratchet key from its draw, the initiator oracle's agreement of the initiator's ratchet key with it (equal to
  the responder oracle's agreement `dSend`, by `DhAgreeSymmetric`), and the initiator's draw's agreement with it
  (returns, by `DhAgreeContributory`).  The AEAD open is `aead_open_sealed` with the roles of the two oracles
  swapped: the responder's oracle seals, the initiator's opens.
* `first_send_model_session`: the model session the first send leaves is the established one with the Triple
  `senderAfterFirst` and the agreement at `keysSampled`.
* `initiator_receives_reply_outcomes` composes them on the run: the reply's bytes and the receipt's key equations
  from `initiator_first_send_responder_replies`, the invariant, relation, counter ceilings and honest chunks at `s'`
  from `established_encrypt_successor_hypotheses` on the same first send, the refinement of the public `decrypt`
  from `decrypt_refines_ratchet_frame_of_counter_headroom` at the initiator's oracle with the source's draws, and the
  model's step from `reply_receipt_model_outcomes`.  `initiator_receives_reply_two_outcomes` excludes two of its four
  arms under its own premises (`DhAgreeContributory`, `AeadRoundTrip`), and `initiator_receives_reply` takes the success
  arm.

## The statements

* `initiator_receives_reply_outcomes`: under the hypotheses of `initiator_first_send_responder_replies`, the decrypt
  records `DecryptRatchetContracts` and `DecryptRatchetAgreements` at the initiator's source and oracle, and the
  per-run premise that the initiator's source after its first send holds a draw `dA`: the responder's `encrypt`
  returns `bytesR` (the reply frame under the key the initiator's receiving chain derives) and the initiator's
  `decrypt` of `bytesR` at `s'` from `rng'` returns, takes exactly `dA`, and is one of four arms:
  `Handshake(NonContributoryAgreement)` (the initiator's draw's agreement with the reply's key refused),
  `Triple(Classical(NoReceivingChain))` (the reply's ratchet key is the peer key the initiator holds), `Aead` (the
  initiator's open of the responder's own seal refused) with the session unchanged, or `Ok` of what the open returned
  with the session related to `replyReceiptSession`.  This is the general outcomes analysis: the `Handshake` and `Aead`
  arms are those the model step lists, and under the theorem's own premises they do not occur (next item).  The `Aead`
  arm is not the refusal of a bad frame: the frame here is the responder's own.
* `initiator_receives_reply_two_outcomes`: under exactly the same hypotheses, `DhAgreeContributory` and `AeadRoundTrip`
  exclude the `Handshake` and `Aead` arms, so the `decrypt` either refuses `Triple(Classical(NoReceivingChain))` with
  the session unchanged, exactly when the reply's ratchet key is the peer key the initiator holds, or returns `Ok ptA`
  with `ptA` the bytes of the responder's plaintext, the pending initial message cleared and the session related to
  `replyReceiptSession`.
* `initiator_receives_reply`: adding only the per-run premise `hfreshB` to those hypotheses (that the responder's fresh
  ratchet public key is not the peer key the initiator holds), the `decrypt` returns `Ok ptA` with
  `ptA` the bytes of the responder's plaintext, takes exactly `dA`, clears the pending initial message, writes only
  the Triple Ratchet, the agreement and the ratchet key, and the session refines `replyReceiptSession` of the model
  session the first send left (Triple `initiatorAfterReply`, agreement unchanged, no pending initial message).
* `reply_receipt_laws_model`: every law of the first receipt's joint model and the new law `DhPublicNotConstantShape`
  hold together in `InterpO.modelReply`, a toy interpretation whose public key varies.
  `modelFirstReceipt_not_notConstant`: the first receipt's joint model fails the new law (there every public key is
  the base point, so the responder's fresh key always equals its signed prekey's and the receipt refuses).
* `reply_receipt_reach_run`, `first_send_reply_receipt_reachable`, `first_send_reply_stale_reachable`: at the real
  constants under the reach's laws, one run from `publish` through the first send, the responder's receipt and reply,
  for every 32-byte responder source and every reply plaintext of at most 4096 bytes; with a source chosen by
  `DhPublicNotConstant` the initiator's `decrypt` returns that plaintext, and with the responder's own signed prekey secret as its source it refuses
  `Triple(Classical(NoReceivingChain))`.

## Laws and premises

No new law is used by the two headline theorems.  They use the receipt's laws with the roles swapped:
`AeadRoundTrip` (the responder seals, the initiator opens), `DhAgreeSymmetric` (the initiator's first agreement),
`DhAgreeContributory` (the initiator's draw), and `DhPublicValid` (the reply's ratchet key is 32 canonical bytes).
New boundary records, of existing kinds, at the initiator's source: `DecryptRatchetContracts` and
`DecryptRatchetAgreements` at the initiator oracle's KEM; the second also gives the `KemLenAgrees` and
`ValidateEkAgrees` that `established_encrypt_successor_hypotheses` takes at `s'`.  New per-run premises: the
initiator's source after its first send holds a draw (both headlines), and `hfreshB`, the responder's fresh ratchet
public key is not the peer key the initiator holds (success only).  `hfreshB` is a condition on the run, not a law: it
fails when the responder's draw gives the signed prekey's public key, and then the initiator refuses the reply
(`first_send_reply_stale_reachable` reaches that refusal).  The law `DhPublicNotConstant` (for every 32 bytes there is
a private key from 32 bytes whose public key's bytes differ from them) is used only by
`first_send_reply_receipt_reachable`, to choose the responder's source.

At the session `s'` the agreement is at `KeysSampled`.  The translated `Braid::step_receive` there returns the state
it was given unless the message is a `Ct1` chunk (by reading the generated code; no theorem here states it), and the
model's receive likewise, so the reply's receipt runs no
encapsulation, decapsulation or key generation and no fact relating the two parties' KEMs is used.  The call does clone
the agreement state, key pair included (`Braid::receive` clones `self.state`), which the route covers through
`KemCloneAgrees`.  `DecryptRatchetAgreements` also carries the KEM agreements `KemAgreesFor`, `KemLenAgrees` and
`ValidateEkAgrees` at the initiator oracle's KEM, as the generic route takes them for every state; whether
`KemAgreesFor` could be dropped here is not checked.

## Trust

`initiator_receives_reply_outcomes`, `initiator_receives_reply_two_outcomes`, `initiator_receives_reply`,
`reply_receipt_reach_run` and the two reaches are compiler-trusted through the nine `native_decide` constants of the encrypt and decrypt refinements.  Every other
result rests on the kernel and opaque constants only (pins below).

## Non-vacuity

`reply_receipt_laws_model` puts every law the statements and the reaches take in one interpretation,
`InterpO.modelReply`: the first receipt's joint model with a public key that is the private key when that key is
canonical and not all zero and the base point otherwise, and an agreement that refuses the all-zero key and otherwise
returns the base point.  It is a toy: nothing about X25519 is modelled beyond these shapes.  Every conjunct of
`first_receipt_laws_model` is proved again there.  `first_send_reply_receipt_reachable` exhibits, at the real constants
under the reach's laws, one run for every reply plaintext of at most 4096 bytes (last-resort path, the initiator's
first plaintext empty, the initiator's source the 64-byte seed and 32 further bytes, the responder's source chosen by
`DhPublicNotConstant`) at which every premise of `initiator_receives_reply` holds, `hfreshB` included, and the
initiator's `decrypt` returns the responder's plaintext.  The toy's agreement ignores the private key: it returns the
base point for every key that is not all zero, so symmetry and contributoriness hold degenerately and every agreement
value (`dSend`, `x`) is the same constant; the toy cannot tell which key sealed the reply, and that a non-degenerate
symmetric agreement is consistent with the other laws rests on reading X25519, not on this model.

## What it does not show

* That a tampered or foreign reply frame is refused: no AEAD authenticity law is assumed, and the `Aead` arm above is
  the open of the responder's own seal, excluded by `AeadRoundTrip`.
* A second message in either direction: a second reply, the initiator's next send and the header's later chunks
  (which do need a per-run premise relating the two parties' Braid KEMs), the responder's first sampling send.
* `Session::invariant` or the ceilings at the session the receipt of the reply returns, or at the responder's session
  after its reply.
* That the code's agreement after the call equals the one before: it refines the same model agreement
  (`keysSampled`), and code-level equality is not checked.
* That `hfreshB` holds of a run with an honest random source: it is a premise, and no probability is claimed.
* The receipt of a reply on a restored copy of either session; the one-time path in a run (the reaches take the
  last-resort path).
* That the related model sessions hold only bytes the parties received (the responder's relation is at the view that
  attributes the received codeword); that `rngR` is the source `establish_responder` left (the headlines hold for every
  source state; the reaches take that one).
* That the real primitives meet the boundary records or the laws (`AeadRoundTrip`, `DhAgreeContributory`,
  `DhAgreeSymmetric`, `DhPublicValid`, `DhPublicNotConstant`), that ML-KEM decapsulation agrees on a run
  (`FirstKemAgrees`), or `PrekeyIdsDistinct` from `PrekeyStore::invariant`; the model's own `establishResponder`
  equality.  The results are compiler-trusted through the nine `native_decide` constants.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit

namespace Tacenta.UnitLifecycleResponderReplyReceipt

open Tacenta.UnitLifecycleT3 (DhView DhCodecOf KemView arrayOf vecOf sliceOf SessionRefines OracleOf StepRefines
  ResultRefines)
open Tacenta.UnitLifecycleResponderFirstReceipt (senderAfterFirst firstHeader firstKey firstOpen
  decode_encodeMessage)
open Tacenta.UnitLifecycleResponderReply (replyComposite replyFrame)

/-! ## The model's receipt of the reply -/

section Model
open Model.State (Key)

/-- The initiator's Triple after it receives the reply: one Diffie-Hellman step on the reply's ratchet key `newPub`
from the root `rkA` (agreement `dSend` for the receiving chain, then `x` with the fresh key `candPub` for the
sending chain), the previous chain length 1 (the first message), the receiving chain stepped once, clock 1; the
sparse receiving chain `k2` stepped once to number 1. -/
def initiatorAfterReply (rkA prk k1 k2 dSend x newPub candPub : Key) : Model.Triple.State :=
  { classical :=
      { dhsPub := candPub, dhrPub := some newPub,
        rk := (Model.State.kdfRk (Model.State.kdfRk rkA dSend .tacenta).1 x .tacenta).1,
        cks := some (Model.State.kdfRk (Model.State.kdfRk rkA dSend .tacenta).1 x .tacenta).2,
        ckr := some (Model.State.kdfCk (Model.State.kdfRk rkA dSend .tacenta).2).1,
        ns := 0, nr := 1, pn := 1, skipped := [], events := 1, labels := .tacenta }
    postQuantum :=
      { rk := prk, epoch := 0,
        chains :=
          [(0, { send := some ⟨(Model.SparseRatchet.kdfCk k1 1).1, 1⟩
                 receive := some ⟨(Model.SparseRatchet.kdfCk k2 1).1, 1⟩ })],
        skipped := [], direction := .a2b } }

/-- **The model's receive of the reply at the sender after its first message, on a fresh ratchet key**: when the
reply's ratchet key `newPub` is not the peer key the sender holds, the receive of `firstHeader newPub` takes one
Diffie-Hellman step and succeeds with key `firstKey (kdfRk rkA dSend).2 k2` and successor `initiatorAfterReply`.
Hypothesis-free beyond `newPub ≠ peer`. -/
theorem reply_receive_key (a4 peer rkA cksA prk k1 k2 dSend x newPub candPub : Key) (hne : newPub ≠ peer) :
    Model.Triple.receiveDetailed (senderAfterFirst a4 peer rkA cksA prk k1 k2) (firstHeader newPub) dSend x
        candPub none =
      .ok (initiatorAfterReply rkA prk k1 k2 dSend x newPub candPub,
        firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) := by
  simp [Model.Triple.receiveDetailed, Model.Ratchet.receiveDetailed, Model.Ratchet.trySkipped,
    Model.Ratchet.skipMessageKeysDetailed, Model.State.skipMessageKeys, Model.Ratchet.dhRatchet,
    Model.SparseRatchet.receiveDetailed, Model.SparseRatchet.maybeAdvanceReceiveDetailed,
    Model.SparseRatchet.maybeAdvanceDetailed, Model.SparseRatchet.trySkipped,
    Model.SparseRatchet.skipMessageKeysDetailed, Model.SparseRatchet.skipMessageKeys,
    Model.SparseRatchet.findChains, Model.SparseRatchet.setChains, senderAfterFirst, firstHeader,
    initiatorAfterReply, firstKey, Model.State.ageStore, Model.State.u32Max, Model.SparseRatchet.u64Max,
    Model.State.maxEvents, Ne.symm hne]

/-- **The model's receive of the reply on the key the sender already holds is refused**: when the reply's ratchet
key is the peer key the sender holds, no Diffie-Hellman step is taken, the sender has no receiving chain, and the
receive refuses `noReceivingChain`.  Hypothesis-free. -/
theorem reply_receive_stale (a4 peer rkA cksA prk k1 k2 dSend x candPub : Key) :
    Model.Triple.receiveDetailed (senderAfterFirst a4 peer rkA cksA prk k1 k2) (firstHeader peer) dSend x
        candPub none = .error (.classical .noReceivingChain) := by
  simp [Model.Triple.receiveDetailed, Model.Ratchet.receiveDetailed, Model.Ratchet.trySkipped,
    Model.Ratchet.skipMessageKeysDetailed, Model.State.skipMessageKeys, senderAfterFirst, firstHeader]

/-- The associated data the reply is sealed under: `ad`, then the encoded reply header. -/
def replyAd (ad : Model.Lifecycle.Bytes) (newPub : Key) : Model.Lifecycle.Bytes :=
  Model.Messages.concatAd ad (Model.CompositeHeader.encode (replyComposite newPub))

/-- The initiator's model session after it accepts the reply: the Triple `initiatorAfterReply`, the agreement as it
was, the ratchet key replaced by the draw `c` unless the fresh public key equals the old, and no pending initial
message. -/
def replyReceiptSession (mA : Model.Lifecycle.Session) (rkA prk k1 k2 dSend x newPub candPub c : Key) :
    Model.Lifecycle.Session :=
  { mA with
    triple := initiatorAfterReply rkA prk k1 k2 dSend x newPub candPub
    ratchetPrivate := if candPub == mA.triple.classical.dhsPub then mA.ratchetPrivate else c
    pendingInitial := none }

/-- The reply frame is a ratchet message: its first two bytes are the version and the ratchet type. -/
theorem replyFrame_messageType (oracle : Model.Lifecycle.Oracle) (ad : Model.Lifecycle.Bytes)
    (newPub mk : Key) (pt : Model.Lifecycle.Bytes) :
    Model.Lifecycle.messageType (replyFrame oracle ad newPub mk pt) = some .ratchet := by
  simp [replyFrame, Model.CompositeHeader.encodeMessage, Model.CompositeHeader.encode,
    Model.Lifecycle.messageType]

/-- The model's decoder reads the reply frame back: its composite header and the sealed ciphertext, when the
ratchet key is 32 canonical bytes. -/
theorem replyFrame_decodeDetailed (oracle : Model.Lifecycle.Oracle) (ad : Model.Lifecycle.Bytes) (newPub mk : Key)
    (pt : Model.Lifecycle.Bytes) (hlen : newPub.length = 32) (hkey : Model.Messages.checkKey newPub = some ()) :
    Model.CompositeHeader.decodeDetailed (replyFrame oracle ad newPub mk pt) =
      .ok (replyComposite newPub,
        oracle.aeadSeal (Model.State.messageKeys mk .tacenta).1 (Model.State.messageKeys mk .tacenta).2.1
          (Model.State.messageKeys mk .tacenta).2.2 pt (replyAd ad newPub)) := by
  rw [Model.CompositeHeader.decodeDetailed_ok_iff]
  exact decode_encodeMessage _ _ hlen hkey (fun c hc => by simp [replyComposite] at hc)

/-- **Every outcome of the model's public `decrypt` of the reply frame at the sender after its first message**,
model only.  For a model session whose Triple is the sender pair form after the first message
(`senderAfterFirst`) and whose agreement is at `keysSampled`, a reply frame of `oracleB` (ratchet key `newPub`,
32 canonical bytes, sealed under `mk` with the session's associated data) whose first agreement with the session's
ratchet key returns `dSend`, and `mk` the key the receive derives on a fresh key: the step is exactly one of
* the oracle holds no draw: `ceiling`, session and oracle unchanged;
* the draw `c`'s agreement with `newPub` is refused: `handshake nonContributoryAgreement`, the draw consumed;
* that agreement returns `x` and `newPub` is the peer key the session holds: the Triple refuses
  `noReceivingChain` (no Diffie-Hellman step, no receiving chain), the draw consumed;
* `newPub` is not the peer key and the session oracle's open of `oracleB`'s seal is refused: `aead`, the draw
  consumed;
* the open returns `y`: the step returns `y`, consumes the draw, and leaves `replyReceiptSession` (the agreement
  unchanged, no pending initial message).
No other refusal (`agreementFailed`, the dispatch, `decode`, the first agreement, another Triple refusal) occurs. -/
theorem reply_receipt_model_outcomes (view : Model.Lifecycle.CodewordView)
    (oracleA oracleB : Model.Lifecycle.Oracle) (mA : Model.Lifecycle.Session)
    (a4 peer rkA cksA prk k1 k2 : Key) (e : Nat) (auth : Model.Braid.Auth) (dk ekVector : Model.Braid.Bytes)
    (enc : Model.Braid.Encoder)
    (hA : mA.triple = senderAfterFirst a4 peer rkA cksA prk k1 k2)
    (hbraid : mA.braid = .keysSampled e auth dk ekVector enc)
    (newPub dSend : Key) (pt : Model.Lifecycle.Bytes)
    (hlen : newPub.length = 32) (hkey : Model.Messages.checkKey newPub = some ())
    (hagree : oracleA.dhAgree mA.ratchetPrivate newPub = some dSend) :
    (oracleA.draws = [] ∧
      Model.Lifecycle.decrypt view oracleA mA
          (replyFrame oracleB mA.identityAd newPub (firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) pt) =
        { session := mA, result := .error .ceiling, oracle := oracleA }) ∨
    (∃ c rest, oracleA.draws = c :: rest ∧ oracleA.dhAgree c newPub = none ∧
      Model.Lifecycle.decrypt view oracleA mA
          (replyFrame oracleB mA.identityAd newPub (firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) pt) =
        { session := mA, result := .error (.handshake .nonContributoryAgreement),
          oracle := { oracleA with draws := rest } }) ∨
    (∃ c rest x, oracleA.draws = c :: rest ∧ oracleA.dhAgree c newPub = some x ∧ newPub = peer ∧
      Model.Lifecycle.decrypt view oracleA mA
          (replyFrame oracleB mA.identityAd newPub (firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) pt) =
        { session := mA, result := .error (Model.Lifecycle.tripleReceiveRefusalOf (.classical .noReceivingChain)),
          oracle := { oracleA with draws := rest } }) ∨
    (∃ c rest x, oracleA.draws = c :: rest ∧ oracleA.dhAgree c newPub = some x ∧ newPub ≠ peer ∧
      firstOpen oracleB oracleA (firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) pt
        (replyAd mA.identityAd newPub) = none ∧
      Model.Lifecycle.decrypt view oracleA mA
          (replyFrame oracleB mA.identityAd newPub (firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) pt) =
        { session := mA, result := .error .aead, oracle := { oracleA with draws := rest } }) ∨
    (∃ c rest x y, oracleA.draws = c :: rest ∧ oracleA.dhAgree c newPub = some x ∧ newPub ≠ peer ∧
      firstOpen oracleB oracleA (firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) pt
        (replyAd mA.identityAd newPub) = some y ∧
      Model.Lifecycle.decrypt view oracleA mA
          (replyFrame oracleB mA.identityAd newPub (firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) pt) =
        { session := replyReceiptSession mA rkA prk k1 k2 dSend x newPub (oracleA.dhPublic c) c
          result := .ok y
          oracle := { oracleA with draws := rest } }) := by
  -- the frame is a ratchet message, so the dispatch passes it through
  have hdisp := Model.Lifecycle.dispatchDecrypt_passthrough oracleA mA
    (replyFrame oracleB mA.identityAd newPub (firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) pt)
    (by rw [replyFrame_messageType]; simp)
  have hdec := replyFrame_decodeDetailed oracleB mA.identityAd newPub
    (firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) pt hlen hkey
  have hhdr : Model.Lifecycle.tripleHeaderOf (replyComposite newPub) = firstHeader newPub := by
    simp [Model.Lifecycle.tripleHeaderOf, replyComposite, firstHeader]
  have hbr : Model.Braid.receive oracleA.braidKem mA.braid
      (Model.Lifecycle.braidMessageOf view mA.braid (replyComposite newPub)) = (e - 1, none, mA.braid) := by
    rw [hbraid]
    simp [Model.Braid.receive, Model.Lifecycle.braidMessageOf, replyComposite, Model.Lifecycle.braidTypeOf,
      Model.Braid.BraidState.epoch]
  have hfail : Model.Lifecycle.agreementFailed mA = false := by
    simp [Model.Lifecycle.agreementFailed, hbraid]
  have hdh : (replyComposite newPub).dh = newPub := rfl
  have hout : Model.Lifecycle.sparseOutputOf none = none := rfl
  rcases hdr : oracleA.draws with _ | ⟨c, rest⟩
  · left
    refine ⟨rfl, ?_⟩
    have hrand : Model.Lifecycle.random32 oracleA = none := by
      simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hdr]
    unfold Model.Lifecycle.decrypt Model.Lifecycle.decryptRatchet
    rw [hdisp]
    dsimp only
    rw [hfail, if_neg (by simp), hdec]
    dsimp only
    rw [hbr, hdh, hagree]
    dsimp only
    rw [hrand]
  have hrand : Model.Lifecycle.random32 oracleA = some (c, { oracleA with draws := rest }) := by
    simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hdr]
  rcases hcand : oracleA.dhAgree c newPub with _ | x
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
  by_cases hpeer : newPub = peer
  · right; right; left
    refine ⟨c, rest, x, rfl, hcand, hpeer, ?_⟩
    have hrecv : Model.Lifecycle.receiveWithEviction mA.triple (replyComposite newPub) (firstHeader newPub) dSend x
        (oracleA.dhPublic c) none = .error (.classical .noReceivingChain) := by
      unfold Model.Lifecycle.receiveWithEviction
      rw [hA, hpeer, reply_receive_stale]
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
  have hrecv : Model.Lifecycle.receiveWithEviction mA.triple (replyComposite newPub) (firstHeader newPub) dSend x
      (oracleA.dhPublic c) none =
      .ok (initiatorAfterReply rkA prk k1 k2 dSend x newPub (oracleA.dhPublic c),
        firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) := by
    unfold Model.Lifecycle.receiveWithEviction
    rw [hA, reply_receive_key a4 peer rkA cksA prk k1 k2 dSend x newPub _ hpeer]
  rcases hopen : firstOpen oracleB oracleA (firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) pt
      (replyAd mA.identityAd newPub) with _ | y
  · right; right; right; left
    refine ⟨c, rest, x, rfl, hcand, hpeer, rfl, ?_⟩
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
    rw [show Model.Messages.concatAd mA.identityAd (Model.CompositeHeader.encode (replyComposite newPub)) =
      replyAd mA.identityAd newPub from rfl, hopen]
  · right; right; right; right
    refine ⟨c, rest, x, y, rfl, hcand, hpeer, rfl, ?_⟩
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
    rw [show Model.Messages.concatAd mA.identityAd (Model.CompositeHeader.encode (replyComposite newPub)) =
      replyAd mA.identityAd newPub from rfl, hopen]
    dsimp only
    simp [replyReceiptSession, hA, senderAfterFirst, initiatorAfterReply]

end Model

/-! ## From the two runs to the initiator's receive -/

section Bridges

variable {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
  {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}

open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid establishedModelOf)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric dhAgreeSymmetric_is)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory dhAgreeContributory_is view_ratchet_public)

/-- **The responder's fresh ratchet key, from its draw**: for a draw of the responder's source, there are the private
key `from_bytes` makes of the drawn bytes (the view reads it as the draw), its public key, and that key's bytes,
which are canonical; the responder oracle's public key of the draw is those bytes.  Under `DhPublicValid`, the
responder's oracle record and the view's codec relation. -/
theorem fresh_public_of_draw (hpub : DhPublicValid) {E : Type} {rcB : rand_core_1.RngCore E}
    {crcB : rand_core_1.CryptoRng E} {dh : DhView} (codec : DhCodecOf dh) {traceB : E → List Model.Lifecycle.Key}
    {oracleB : Model.Lifecycle.Oracle} (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB) (rngB : E)
    (dB : Model.Lifecycle.Key) (restB : List Model.Lifecycle.Key) (hdraw : traceB rngB = dB :: restB) :
    ∃ (value : Array U8 32#usize) (k : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes)
      (b : Array U8 32#usize),
      arrayOf value = dB ∧ tacenta_boundary.dh.PrivateKey.from_bytes value = ok k ∧ dh.privateKey k = dB ∧
      tacenta_boundary.dh.PrivateKey.public_key k = ok pk ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok b ∧ Tacenta.SessionUnitT1.canonicalX25519 b = true ∧
      dh.publicKey pk = arrayOf b ∧ oracleB.dhPublic dB = arrayOf b := by
  obtain ⟨value, -, -, hval, -⟩ := oracleOfB.random32 rngB dB restB hdraw
  obtain ⟨k, hk, hkv⟩ := codec.privateFromBytes value
  obtain ⟨pk, hpk, hpkv⟩ := oracleOfB.dhPublic k
  obtain ⟨b, hb, hcan, hbv⟩ := Tacenta.UnitLifecycleResponderFirstFrame.view_of_public hpub codec hpk
  refine ⟨value, k, pk, b, hval, hk, hkv.trans hval, hpk, hb, hcan, hbv, ?_⟩
  rw [← hval, ← hkv, ← hpkv, hbv]

/-- **The initiator's first agreement on the reply is the responder's agreement of its draw**: for a responder key
`k` with public key `pk`, the initiator oracle's agreement of the initiator's ratchet key with `pk` is the responder
oracle's agreement of `k` with the initiator's ratchet key.  Under the agreement law `DhAgreeSymmetric` and the two
oracle records; the two oracles need not be equal. -/
theorem initiator_reply_agreement (hsym : DhAgreeSymmetric) {dh : DhView} (codec : DhCodecOf dh)
    {traceA : R → List Model.Lifecycle.Key} {oracleA : Model.Lifecycle.Oracle}
    (oracleOfA : DecryptOracleOf rc crc dh traceA oracleA) {E F : Type} {rcE : rand_core_1.RngCore E}
    {crcE : rand_core_1.CryptoRng E} {rcB : rand_core_1.RngCore F} {crcB : rand_core_1.CryptoRng F}
    {traceB : F → List Model.Lifecycle.Key} {oracleB : Model.Lifecycle.Oracle}
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB) (q : InitiatorSecretParts rcE crcE our bundle)
    (k : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes)
    (hk : tacenta_boundary.dh.PrivateKey.public_key k = ok pk) :
    oracleA.dhAgree (dh.privateKey q.ratchetPrivate) (dh.publicKey pk) =
      oracleB.dhAgree (dh.privateKey k) (arrayOf q.ratchetBytes) := by
  obtain ⟨ra, hra, hmapA⟩ := oracleOfA.dhAgree q.ratchetPrivate pk
  obtain ⟨rb, hrb, hmapB⟩ := oracleOfB.dhAgree k q.ratchetPublic
  have hs := (dhAgreeSymmetric_is.mp hsym) q.ratchetPrivate k _ _ q.hRatchetPublic hk
  rw [hs, hrb] at hra
  cases hra
  rw [← hmapA, ← view_ratchet_public codec q, ← hmapB]

/-- **Every draw of the initiator's source agrees contributorily with the reply's ratchet key**, in the initiator's
oracle, under `DhAgreeContributory`, the initiator's oracle record and the view's codec relation, for every key the
boundary's `public_key` returned. -/
theorem initiator_candidate_agreement (hcon : DhAgreeContributory) {dh : DhView} (codec : DhCodecOf dh)
    {traceA : R → List Model.Lifecycle.Key} {oracleA : Model.Lifecycle.Oracle}
    (oracleOfA : DecryptOracleOf rc crc dh traceA oracleA) (rng : R) (dA : Model.Lifecycle.Key)
    (restA : List Model.Lifecycle.Key) (hdraw : traceA rng = dA :: restA)
    (k : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes)
    (hk : tacenta_boundary.dh.PrivateKey.public_key k = ok pk) :
    ∃ x, oracleA.dhAgree dA (dh.publicKey pk) = some x := by
  obtain ⟨value, -, -, hval, -⟩ := oracleOfA.random32 rng dA restA hdraw
  obtain ⟨c, -, hcv⟩ := codec.privateFromBytes value
  obtain ⟨res, hres, hmap⟩ := oracleOfA.dhAgree c pk
  obtain ⟨x, hx⟩ := (dhAgreeContributory_is.mp hcon) c k pk hk
  rw [hx] at hres
  cases hres
  refine ⟨arrayOf x, ?_⟩
  rw [← hval, ← hcv, ← hmap]
  rfl

open Tacenta.UnitLifecycleResponderFirstReceipt (established_triple_first first_send_key) in
/-- **The model session the initiator's first send leaves**, when the model's key generation answers at the two
draws: the established model session with the Triple after the first message (`senderAfterFirst` of the
establishment's keys) and the agreement at `keysSampled` epoch 1 holding the key generation's decapsulation key and
vector and some encoder.  Model only (through the establishment's parts). -/
theorem first_send_model_session {E : Type} {rcE : rand_core_1.RngCore E} {crcE : rand_core_1.CryptoRng E}
    (dh : DhView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (q : InitiatorSecretParts rcE crcE our bundle) (plaintext : Model.Lifecycle.Bytes)
    (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key) (hdraws : oracle.draws = d1 :: d2 :: rest)
    (dk ekSeed ekVector : Model.Braid.Bytes)
    (hkg : oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector)) :
    ∃ encoder,
      (Model.Lifecycle.encrypt view oracle (establishedModelOf dh q.session) plaintext).session =
        { establishedModelOf dh q.session with
          triple := senderAfterFirst (arrayOf q.ratchetBytes) (arrayOf q.peerRatchetBytes) (arrayOf q.rootKey)
            (arrayOf q.sendChain) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
          braid := .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector encoder } := by
  obtain ⟨-, hc⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_model_cases dh view oracle
    q.toInitiatorOutputParts plaintext d1 d2 rest hdraws
  rcases hc with ⟨hnone, -⟩ | ⟨dk', ekSeed', ekVector', hkg', tripleNext, header, mk, chunk, encoder, pending,
    htriple, -, -, -, hsess⟩
  · rw [hkg] at hnone; cases hnone
  rw [hkg] at hkg'
  simp only [Option.some.injEq, Prod.mk.injEq] at hkg'
  obtain ⟨rfl, rfl, rfl⟩ := hkg'
  rw [established_triple_first dh q.toInitiatorOutputParts, first_send_key] at htriple
  simp only [Except.ok.injEq, Prod.mk.injEq] at htriple
  obtain ⟨rfl, -, -⟩ := htriple
  exact ⟨encoder, hsess⟩

/-- The reply's associated data fits a slice: four length bytes, the 66 bytes of `identity_ad` and the 102 bytes of
the composite header. -/
theorem replyAd_length_le (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle)
    (newPub : Model.Lifecycle.Key) (hlen : newPub.length = 32) :
    (replyAd (vecOf p.identityAd) newPub).length ≤ Usize.max := by
  have h66 := Tacenta.UnitLifecycleEstablishedEncrypt.identityAd_length_parts hdh p
  apply Tacenta.UnitSatisfiabilityBraidAgreements.usize_max_ge
  simp [replyAd, Model.Messages.concatAd, Model.CompositeHeader.encode, replyComposite, vecOf, h66, hlen,
    Model.Messages.be32, Model.CompositeHeader.be64, Model.CompositeHeader.encodeChunk,
    Model.CompositeHeader.be16, Model.CompositeHeader.chunkBytes]

end Bridges

/-! ## The initiator's receive of the reply, on the run -/

section Comp

open Tacenta.UnitLifecycleT3 (BraidSendRefinementContracts TripleSendRefinementContracts CodewordViewSendOf
  ZeroizingRoundTrips)
open Tacenta.UnitLifecycleResponderFirstReceipt (headerSource DhAgreeContributory AeadRoundTrip aead_open_sealed)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid establishedModelOf)
open Tacenta.UnitLifecycleResponderReply (replyKey oracleOf_with_draws initiator_first_send_responder_replies)

/-- **Every outcome of the initiator's `decrypt` of the responder's reply, on the run of the initiator's first
send.**  Under the hypotheses of `initiator_first_send_responder_replies`, the decrypt boundary records at the
initiator's source (`DecryptRatchetContracts`, `DecryptRatchetAgreements` at the initiator oracle's KEM) and the
per-run premise that the initiator's source after its first send holds a draw `dA`: at every successful return of
`establish_responder` on the bytes the initiator's first `encrypt` emitted, for every plaintext `ptR` of at most
`Usize.max - 150` bytes and every source state `rngR` of the responder, the responder's `encrypt` at `sB'` returns
bytes `bytesR` (the bare reply frame under the key the initiator's receiving chain will derive: the root `rootKey`
after the agreement `dSend`), and the initiator's public `decrypt` of those bytes at the session `s'` its first
send left, from the source `rng'` that send left, returns, takes exactly the draw `dA`, and its result is one of the
four arms the model's step lists:
* `Handshake(NonContributoryAgreement)`, exactly when the initiator oracle's agreement of `dA` with the reply's
  ratchet key is refused; the session unchanged;
* `Triple(Classical(NoReceivingChain))`, when that agreement returns and the reply's ratchet key is the peer key
  the initiator holds (the responder's fresh public key is its signed prekey's): no Diffie-Hellman step; the
  session unchanged;
* `Aead`, when the reply's ratchet key is fresh and the initiator oracle's open of the responder oracle's own seal is
  refused (not the refusal of a bad frame); the session unchanged;
* `Ok` of bytes that are what that open returned, the session with only the Triple Ratchet, the agreement and the
  ratchet key written and the pending initial message cleared, related to the model session
  `replyReceiptSession`.
No other outcome of the call occurs on these bytes.  This is the general analysis: the theorem's own premises
`DhAgreeContributory` and `AeadRoundTrip` exclude the `Handshake` and `Aead` arms
(`initiator_receives_reply_two_outcomes`).  Compiler-trusted through the nine `native_decide` constants of the
encrypt and decrypt refinements. -/
theorem initiator_receives_reply_outcomes [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
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
    (ptR : Slice Std.U8) (hroomR : 102 + (ptR.val.length + 48) ≤ Usize.max) (rngR : F) :
    ∃ (dSend : Model.Lifecycle.Key) (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session)
      (res : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error) (s'' : lifecycle.Session) (rngA' : R),
      oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      vecOf bytesR = replyFrame oracleB (vecOf q.identityAd) (oracleB.dhPublic dB)
        (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2 (arrayOf q.sparseReceive)) (sliceOf ptR) ∧
      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' = ok (res, s'', rngA') ∧
      trace rngA' = restA ∧
      ((res = core.result.Result.Err (lifecycle.Error.Handshake SessionError.NonContributoryAgreement) ∧
          oracle.dhAgree dA (oracleB.dhPublic dB) = none ∧ s'' = s') ∨
        (res = core.result.Result.Err (lifecycle.Error.Triple
            (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.NoReceivingChain)) ∧
          (∃ x, oracle.dhAgree dA (oracleB.dhPublic dB) = some x) ∧
          oracleB.dhPublic dB = arrayOf q.peerRatchetBytes ∧ s'' = s') ∨
        (res = core.result.Result.Err lifecycle.Error.Aead ∧
          (∃ x, oracle.dhAgree dA (oracleB.dhPublic dB) = some x) ∧
          oracleB.dhPublic dB ≠ arrayOf q.peerRatchetBytes ∧
          firstOpen oracleB oracle
            (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2 (arrayOf q.sparseReceive))
            (sliceOf ptR) (replyAd (vecOf q.identityAd) (oracleB.dhPublic dB)) = none ∧
          s'' = s') ∨
        (∃ ptA x y, res = core.result.Result.Ok ptA ∧
          oracle.dhAgree dA (oracleB.dhPublic dB) = some x ∧
          oracleB.dhPublic dB ≠ arrayOf q.peerRatchetBytes ∧
          firstOpen oracleB oracle
            (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2 (arrayOf q.sparseReceive))
            (sliceOf ptR) (replyAd (vecOf q.identityAd) (oracleB.dhPublic dB)) = some y ∧
          vecOf ptA = y ∧
          s'' = { s' with
            triple := s''.triple, braid := s''.braid, ratchet_private := s''.ratchet_private,
            pending_initial := none } ∧
          SessionRefines dh oracle.braidKem s''
            (replyReceiptSession
              (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
              (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
              (oracleB.dhPublic dB) (oracle.dhPublic dA) dA))) := by
  -- the responder's reply, on the run
  obtain ⟨p, ec, dSend, dk, ekSeed, ekVector, bytesR, sB'', hkg, hkdf, hagreeB, -, -, hcallR, -, -, -, hbytes,
    -⟩ := initiator_first_send_responder_replies rc crc trace dh kem view oracle braid triple aead dhCodec oracleOf
      codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h q hq
      plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall rcB crcB contracts hpub hsym hcon haead hrt
      hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish hidentity hdistinct hkem rngB htraceB dB
      restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR rngR
  -- the session the initiator's first send left: invariant, relation, ceilings, honest chunks
  obtain ⟨hinv, hrel, hc, hhonest⟩ :=
    Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_hypotheses rc crc trace dh kem view
      oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct hbound hpub hoeq
      agreementsA.kemLen agreementsA.validateEk hsizes contracts.divCeilValue rcE crcE ourA bundleA expected rng0
      rng1 s h plaintext hroom rng htrace ⟨d1, d2, rest, hdraws⟩ bytes s' rng' hcall
  subst hq
  obtain ⟨encoder, hmA⟩ := first_send_model_session dh view oracle q (sliceOf plaintext) d1 d2 rest
    (htrace.symm.trans hdraws) dk ekSeed ekVector hkg
  -- the responder's fresh ratchet key and the initiator's first agreement with it
  obtain ⟨-, k, pk, b, -, -, hkd, hpk, -, hcan, hpkb, hnew⟩ :=
    fresh_public_of_draw hpub codec (DecryptOracleOf.of_oracleOf oracleOfB) rngB dB restB hdrawB
  let oracleA : Model.Lifecycle.Oracle := { oracle with draws := trace rng' }
  have oracleOfA : DecryptOracleOf rc crc dh trace oracleA :=
    DecryptOracleOf.of_oracleOf (oracleOf_with_draws oracleOf _)
  have hagreeA : oracleA.dhAgree (dh.privateKey q.ratchetPrivate) (oracleB.dhPublic dB) = some dSend := by
    rw [← hagreeB, hnew, ← hpkb, ← hkd]
    exact initiator_reply_agreement hsym codec oracleOfA (DecryptOracleOf.of_oracleOf oracleOfB) q k pk hpk
  have hlen : (oracleB.dhPublic dB).length = 32 := by rw [hnew]; simp [arrayOf]
  have hkey : Model.Messages.checkKey (oracleB.dhPublic dB) = some () := by
    rw [hnew]
    simp [Model.Messages.checkKey, Tacenta.UnitLifecycleResponderFirstFrame.canonicalKey_arrayOf _ hcan]
  -- the reply bytes, in the key the initiator's receive derives
  have hrk : replyKey (arrayOf ec) (arrayOf q.sparseReceive) (arrayOf q.dhOut) dSend =
      firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2 (arrayOf q.sparseReceive) := by
    simp only [replyKey, hkdf]
  rw [hrk] at hbytes
  have hmsg : sliceOf (alloc.vec.Vec.deref bytesR) = vecOf bytesR := rfl
  rw [← hmsg] at hbytes
  -- the decrypt refinement at that session, with the run's inputs
  let mA := (Model.Lifecycle.encrypt view oracle (establishedModelOf dh q.session) (sliceOf plaintext)).session
  have hadA : mA.identityAd = vecOf q.identityAd := by simp only [mA, hmA]; rfl
  have inputs : Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracleA trace s' mA
      (alloc.vec.Vec.deref bytesR) rng' := by
    refine ⟨?_, fun mc ct _ => hhonest _, ⟨dA, restA, hdrawA⟩⟩
    intro rcomp mcomp ct hd hcr
    rw [hbytes, replyFrame_decodeDetailed _ _ _ _ _ hlen hkey] at hd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    have hag := hcr.agChunk
    unfold Tacenta.UnitLifecycleT3.IncomingChunkRefines
    simp only [replyComposite] at hag ⊢
    rcases hrc : rcomp.ag_chunk with _ | rch
    · trivial
    · rw [hrc] at hag; exact hag.elim
  have hframe : Model.Lifecycle.messageType (sliceOf (alloc.vec.Vec.deref bytesR)) ≠ some .initial := by
    rw [hbytes, replyFrame_messageType]; simp
  obtain ⟨output, hcallA, hstep⟩ :=
    Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_of_counter_headroom rc crc trace dh view oracleA
      oracleOfA codec contractsA agreementsA s' mA (alloc.vec.Vec.deref bytesR) rng' hframe hinv hrel hc rfl inputs
  -- the model's step: the outcomes at the sender after its first message
  have O := reply_receipt_model_outcomes view oracleA oracleB mA (arrayOf q.ratchetBytes)
    (arrayOf q.peerRatchetBytes) (arrayOf q.rootKey) (arrayOf q.sendChain) (arrayOf q.sparseRoot)
    (arrayOf q.sparseSend) (arrayOf q.sparseReceive) 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
    encoder (by simp only [mA, hmA]) (by simp only [mA, hmA]) (oracleB.dhPublic dB) dSend (sliceOf ptR) hlen hkey
    (by simp only [mA, hmA]; exact hagreeA)
  rw [hadA] at O
  rw [hbytes] at hstep
  have hdrA : oracleA.draws = dA :: restA := hdrawA
  obtain ⟨res, s'', rngA'⟩ := output
  refine ⟨dSend, bytesR, sB'', res, s'', rngA', hagreeB, hcallR, by rw [← hmsg, hbytes], hcallA, ?_⟩
  have hres := hstep.result
  have hdr := hstep.draws
  have hsess := hstep.session
  rcases O with ⟨hnil, -⟩ | ⟨c, rest', hdr', hnone, hM⟩ | ⟨c, rest', x, hdr', hsome, hpeer, hM⟩ |
    ⟨c, rest', x, hdr', hsome, hpeer, hopen, hM⟩ | ⟨c, rest', x, y, hdr', hsome, hpeer, hopen, hM⟩
  · rw [hdrA] at hnil; cases hnil
  · rw [hdrA] at hdr'
    obtain ⟨rfl, rfl⟩ := List.cons.inj hdr'
    rw [hM] at hres hdr
    refine ⟨hdr, Or.inl ⟨?_, hnone, ?_⟩⟩
    · cases res with
      | Ok v => simp [ResultRefines] at hres
      | Err e =>
        simp only [ResultRefines] at hres
        have he : e = lifecycle.Error.Handshake SessionError.NonContributoryAgreement :=
          Tacenta.UnitLifecycleT3.refusalOf_injective (hres.trans rfl)
        rw [he]
    · cases res with
      | Ok v => simp [ResultRefines] at hres
      | Err e => exact Tacenta.UnitLifecycleAtomicity.decrypt_err_leaves_state rc crc _ _ _ e s'' rngA' hcallA
  · rw [hdrA] at hdr'
    obtain ⟨rfl, rfl⟩ := List.cons.inj hdr'
    rw [hM] at hres hdr
    refine ⟨hdr, Or.inr (Or.inl ⟨?_, ⟨x, hsome⟩, hpeer, ?_⟩)⟩
    · cases res with
      | Ok v => simp [ResultRefines] at hres
      | Err e =>
        simp only [ResultRefines] at hres
        have he : e = lifecycle.Error.Triple
            (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.NoReceivingChain) :=
          Tacenta.UnitLifecycleT3.refusalOf_injective (hres.trans rfl)
        rw [he]
    · cases res with
      | Ok v => simp [ResultRefines] at hres
      | Err e => exact Tacenta.UnitLifecycleAtomicity.decrypt_err_leaves_state rc crc _ _ _ e s'' rngA' hcallA
  · rw [hdrA] at hdr'
    obtain ⟨rfl, rfl⟩ := List.cons.inj hdr'
    rw [hM] at hres hdr
    refine ⟨hdr, Or.inr (Or.inr (Or.inl ⟨?_, ⟨x, hsome⟩, hpeer, hopen, ?_⟩))⟩
    · cases res with
      | Ok v => simp [ResultRefines] at hres
      | Err e =>
        simp only [ResultRefines] at hres
        have he : e = lifecycle.Error.Aead := Tacenta.UnitLifecycleT3.refusalOf_injective (hres.trans rfl)
        rw [he]
    · cases res with
      | Ok v => simp [ResultRefines] at hres
      | Err e => exact Tacenta.UnitLifecycleAtomicity.decrypt_err_leaves_state rc crc _ _ _ e s'' rngA' hcallA
  · rw [hdrA] at hdr'
    obtain ⟨rfl, rfl⟩ := List.cons.inj hdr'
    rw [hM] at hres hdr hsess
    refine ⟨hdr, Or.inr (Or.inr (Or.inr ?_))⟩
    cases res with
    | Err e => simp [ResultRefines] at hres
    | Ok ptA =>
      exact ⟨ptA, x, y, rfl, hsome, hpeer, hopen, hres,
        Tacenta.UnitLifecycleAtomicity.decrypt_ok_writes rc crc _ _ _ ptA s'' rngA' hcallA, hsess⟩

/-- **The initiator's `decrypt` of the reply has two outcomes, told apart by the reply's ratchet key**, on the run of
the initiator's first send.  Under exactly the hypotheses of `initiator_receives_reply_outcomes`, whose
`DhAgreeContributory` and `AeadRoundTrip` exclude its `Handshake(NonContributoryAgreement)` and `Aead` arms (the
initiator's draw agrees with the reply's ratchet key; the initiator oracle opens the responder oracle's own seal): the
responder's `encrypt` at `sB'` returns `bytesR`, and the initiator's `decrypt` of `bytesR` at `s'` from `rng'` returns,
takes exactly the draw `dA`, and
* refuses `Triple(Classical(NoReceivingChain))` with the session unchanged exactly when the reply's ratchet key is the
  peer key the initiator holds, and
* otherwise returns `Ok ptA` with `ptA` the bytes of `ptR`, clears the pending initial message, writes only the Triple
  Ratchet, the agreement and the ratchet key, and its session refines `replyReceiptSession`.
The two agreements `dSend` and `x` the relation names are in the conclusion.  No premise is added to those of
`initiator_receives_reply_outcomes`.  Compiler-trusted through the nine `native_decide` constants of the encrypt and
decrypt refinements. -/
theorem initiator_receives_reply_two_outcomes [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
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
    (ptR : Slice Std.U8) (hroomR : 102 + (ptR.val.length + 48) ≤ Usize.max) (rngR : F) :
    ∃ (dSend x : Model.Lifecycle.Key) (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session)
      (res : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error) (s'' : lifecycle.Session) (rngA' : R),
      oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
      oracle.dhAgree dA (oracleB.dhPublic dB) = some x ∧
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      vecOf bytesR = replyFrame oracleB (vecOf q.identityAd) (oracleB.dhPublic dB)
        (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2 (arrayOf q.sparseReceive)) (sliceOf ptR) ∧
      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' = ok (res, s'', rngA') ∧
      trace rngA' = restA ∧
      ((oracleB.dhPublic dB = arrayOf q.peerRatchetBytes ∧
          res = core.result.Result.Err (lifecycle.Error.Triple
            (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.NoReceivingChain)) ∧ s'' = s') ∨
        (oracleB.dhPublic dB ≠ arrayOf q.peerRatchetBytes ∧
          ∃ ptA : alloc.vec.Vec Std.U8, res = core.result.Result.Ok ptA ∧ ptA.val = ptR.val ∧
          s''.pending_initial = none ∧
          s'' = { s' with
            triple := s''.triple, braid := s''.braid, ratchet_private := s''.ratchet_private,
            pending_initial := none } ∧
          SessionRefines dh oracle.braidKem s''
            (replyReceiptSession
              (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
              (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
              (oracleB.dhPublic dB) (oracle.dhPublic dA) dA))) := by
  obtain ⟨dSend, bytesR, sB'', res, s'', rngA', hagreeB, hcallR, hbytes, hcallA, hdr, hcases⟩ :=
    initiator_receives_reply_outcomes rc crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec
      codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h q hq
      plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall contractsA agreementsA dA restA hdrawA rcB
      crcB contracts hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish
      hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR rngR
  -- the candidate agreement returns (contributory), and the responder's seal opens (round trip)
  obtain ⟨-, k, pk, b, -, -, -, hpk, -, -, hpkb, hnew⟩ :=
    fresh_public_of_draw hpub codec (DecryptOracleOf.of_oracleOf oracleOfB) rngB dB restB hdrawB
  have oracleOfA : DecryptOracleOf rc crc dh trace oracle := DecryptOracleOf.of_oracleOf oracleOf
  obtain ⟨x0, hx0⟩ := initiator_candidate_agreement hcon codec
    (DecryptOracleOf.of_oracleOf (oracleOf_with_draws oracleOf (trace rng'))) rng' dA restA hdrawA k pk hpk
  rw [hpkb, ← hnew] at hx0
  have hlen : (oracleB.dhPublic dB).length = 32 := by rw [hnew]; simp [arrayOf]
  subst hq
  have hopen := aead_open_sealed haead oracleOfB.aeadSeal oracleOfA
    (Model.State.messageKeys (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2
      (arrayOf q.sparseReceive)) .tacenta).1
    (Model.State.messageKeys (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2
      (arrayOf q.sparseReceive)) .tacenta).2.1
    (Model.State.messageKeys (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2
      (arrayOf q.sparseReceive)) .tacenta).2.2
    (by simp [Model.State.messageKeys, Model.Kdf.hkdf_length])
    (by simp [Model.State.messageKeys, Model.Kdf.hkdf_length])
    (by simp [Model.State.messageKeys, Model.Kdf.hkdf_length]) ptR (by omega)
    (replyAd (vecOf q.identityAd) (oracleB.dhPublic dB))
    (replyAd_length_le dhCodec q.toInitiatorOutputParts _ hlen)
  rcases hcases with ⟨-, hnone, -⟩ | ⟨hres, -, hpeer, hs⟩ | ⟨-, -, -, hopen', -⟩ |
    ⟨ptA, x, y, hres, hsome, hne, hopen', hvec, hs'', hsess⟩
  · rw [hx0] at hnone; cases hnone
  · exact ⟨dSend, x0, bytesR, sB'', res, s'', rngA', hagreeB, hx0, hcallR, hbytes, hcallA, hdr,
      Or.inl ⟨hpeer, hres, hs⟩⟩
  · simp only [firstOpen] at hopen'
    rw [hopen] at hopen'
    cases hopen'
  · simp only [firstOpen] at hopen'
    rw [hopen] at hopen'
    cases hopen'
    exact ⟨dSend, x, bytesR, sB'', res, s'', rngA', hagreeB, hsome, hcallR, hbytes, hcallA, hdr,
      Or.inr ⟨hne, ptA, hres, Tacenta.UnitLifecycleEstablishResponder.map_u8_inj hvec, by rw [hs''], hs'', hsess⟩⟩

/-- **The initiator receives the responder's reply, on the run of the initiator's first send.**  Under the
hypotheses of `initiator_receives_reply_outcomes` and the per-run premise that the responder's fresh ratchet public
key (`oracleB.dhPublic dB`, from its draw) is not the peer key the initiator holds (its signed prekey's bytes), the
only premise added (`initiator_receives_reply_two_outcomes` with its stale-key arm excluded): at
every successful return of `establish_responder` on the bytes the initiator's first `encrypt` emitted, for every
plaintext `ptR` of at most `Usize.max - 150` bytes and every source state `rngR` of the responder, the responder's
`encrypt` at `sB'` returns bytes `bytesR`, and the initiator's public `decrypt` of those bytes at the session `s'`
its first send left, from the source `rng'` that send left, returns `Ok ptA` with `ptA` the bytes of `ptR`, takes
exactly the draw `dA`, clears the pending initial message, writes only the Triple Ratchet, the agreement and the
ratchet key, and the session it returns refines `replyReceiptSession` of the model session the first send left
(the Triple after one Diffie-Hellman step on the reply's ratchet key, the agreement unchanged).  The responder
oracle's agreement `dSend` of its draw with the initiator's ratchet key and the initiator oracle's agreement `x` of
its draw with the reply's ratchet key are the ones the relation names.  Compiler-trusted through the nine
`native_decide` constants of the encrypt and decrypt refinements. -/
theorem initiator_receives_reply [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
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
      (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' : R),
      oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
      oracle.dhAgree dA (oracleB.dhPublic dB) = some x ∧
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      vecOf bytesR = replyFrame oracleB (vecOf q.identityAd) (oracleB.dhPublic dB)
        (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2 (arrayOf q.sparseReceive)) (sliceOf ptR) ∧
      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' =
        ok (core.result.Result.Ok ptA, s'', rngA') ∧
      ptA.val = ptR.val ∧ trace rngA' = restA ∧ s''.pending_initial = none ∧
      s'' = { s' with
        triple := s''.triple, braid := s''.braid, ratchet_private := s''.ratchet_private,
        pending_initial := none } ∧
      SessionRefines dh oracle.braidKem s''
        (replyReceiptSession
          (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
          (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
          (oracleB.dhPublic dB) (oracle.dhPublic dA) dA) := by
  obtain ⟨dSend, x, bytesR, sB'', res, s'', rngA', hagreeB, hx, hcallR, hbytes, hcallA, hdr, hcases⟩ :=
    initiator_receives_reply_two_outcomes rc crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec
      codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h q hq
      plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall contractsA agreementsA dA restA hdrawA rcB
      crcB contracts hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish
      hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR rngR
  -- the fresh-key premise excludes the stale-key refusal
  rcases hcases with ⟨hpeer, -, -⟩ | ⟨-, ptA, hres, hpt, hpend, hs'', hsess⟩
  · exact absurd hpeer hfreshB
  · subst hres
    exact ⟨dSend, x, bytesR, sB'', ptA, s'', rngA', hagreeB, hx, hcallR, hbytes, hcallA, hpt, hdr, hpend, hs'',
      hsess⟩

end Comp

/-! ## One interpretation of every law, with a public key that varies -/

section JointModel

open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitLifecycleResponderFirstFrame (DhAgreeSymmetricShape FirstFrameSuccessShape PoolEntry
  basePoint_ne_zero)
open Tacenta.UnitLifecycleResponderFirstReceipt (AeadRoundTripShape DhAgreeContributoryShape
  Interp.modelFirstReceipt modelFirstReceipt_aeadOpen modelFirstReceipt_aeadSeal modelFirstReceipt_aeadRoundTrip)
open Tacenta.UnitLifecycleEstablishedEncrypt (toyKemR zeroSeed oneSeed EncryptExtraLawsShape
  established_encrypt_laws_model encapResult encapFill)
open Tacenta.UnitLifecycleDecryptRatchetScreen (DhViewShape)
open Tacenta.UnitOracleShape (InterpO DhViewOf KemViewOf)

/-- The toy public key of a 32-byte private key: the key itself when it is canonical and not all zero, the base
point otherwise.  Canonical and not all zero for every key, and not constant (`replyPub_basePoint`,
`replyPub_oneKey`). -/
def replyPub (k : Array U8 32#usize) : Array U8 32#usize :=
  if Tacenta.SessionUnitT1.canonicalX25519 k = true ∧
      k.val ≠ Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then k
  else Tacenta.UnitLifecycleEstablishResponder.basePoint

/-- Every toy public key is canonical. -/
theorem replyPub_canonical (k : Array U8 32#usize) :
    Tacenta.SessionUnitT1.canonicalX25519 (replyPub k) = true := by
  unfold replyPub
  split
  · rename_i h; exact h.1
  · exact Tacenta.UnitLifecycleEstablishResponder.basePoint_canonical

/-- No toy public key is all zero. -/
theorem replyPub_ne_zero (k : Array U8 32#usize) :
    (replyPub k).val ≠ Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val := by
  unfold replyPub
  split
  · rename_i h; exact h.2
  · exact basePoint_ne_zero

/-- The base point is its own toy public key. -/
theorem replyPub_basePoint :
    replyPub Tacenta.UnitLifecycleEstablishResponder.basePoint =
      Tacenta.UnitLifecycleEstablishResponder.basePoint := by
  unfold replyPub; split <;> rfl

/-- The key `1` is its own toy public key. -/
theorem replyPub_oneKey :
    replyPub Tacenta.UnitLifecycleEstablishedDecrypt.oneKey = Tacenta.UnitLifecycleEstablishedDecrypt.oneKey := by
  unfold replyPub
  rw [if_pos ⟨Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_canonical,
    Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_ne_zero⟩]

/-- The all-zero key's toy public key is the base point. -/
theorem replyPub_zeros :
    replyPub Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32 =
      Tacenta.UnitLifecycleEstablishResponder.basePoint := by
  unfold replyPub
  rw [if_neg (by decide)]

/-- `Interp.modelFirstReceipt` (the first receipt's joint model) with a public key that varies with the private
key (`replyPub`) and an agreement that refuses the all-zero key and otherwise returns the base point: symmetric,
and contributory with every key `public_key` returns.  Every other field is `Interp.modelFirstReceipt`'s.  A toy:
nothing about X25519 is modelled beyond these shapes. -/
noncomputable def Interp.modelReply : Interp :=
  { Interp.modelFirstReceipt with
    dhPrivPublicKey := fun k => ok (replyPub k)
    dhPrivAgree := fun _ p => ok (if p.val = Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
      else some Tacenta.UnitLifecycleEstablishResponder.basePoint) }

/-- The joint interpretation with its signing function. -/
noncomputable def InterpO.modelReply : InterpO :=
  { Interp.modelReply with xeddsaSign := Tacenta.UnitOracleModel.signModelO }

/-- The view of the joint interpretation: both key types are their bytes. -/
def viewReply : DhViewShape Interp.modelReply := ⟨arrayOf, arrayOf⟩
/-- The DH view of the joint interpretation with its signing function. -/
def dhViewReply : DhViewOf InterpO.modelReply.toInterp := ⟨viewReply.privateKey, viewReply.publicKey⟩
/-- The KEM view of the joint interpretation with its signing function. -/
def kemViewReply : KemViewOf InterpO.modelReply.toInterp := ⟨fun _ => []⟩

/-- A private key from 32 bytes whose public key's bytes differ from a given 32 bytes, over an interpretation
`I`. -/
def DhPublicNotConstantShape (I : Interp) : Prop :=
  ∀ pa : Array U8 32#usize, ∃ (sb : Array U8 32#usize) (k : I.PrivateKey) (pk : I.PublicKeyBytes)
    (b : Array U8 32#usize),
    I.dhPrivFromBytes sb = ok k ∧ I.dhPrivPublicKey k = ok pk ∧ I.dhPubAsBytes pk = ok b ∧ b ≠ pa

/-- **Assumed law**: `DhPublicNotConstantShape` at the real constants. -/
def DhPublicNotConstant : Prop := DhPublicNotConstantShape Interp.real

/-- At the real constants, `DhPublicNotConstant` is the statement about the real functions. -/
theorem dhPublicNotConstant_is : DhPublicNotConstant ↔
    ∀ pa : Array U8 32#usize, ∃ (sb : Array U8 32#usize) (k : tacenta_boundary.dh.PrivateKey)
      (pk : tacenta_boundary.dh.PublicKeyBytes) (b : Array U8 32#usize),
      tacenta_boundary.dh.PrivateKey.from_bytes sb = ok k ∧
      tacenta_boundary.dh.PrivateKey.public_key k = ok pk ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok b ∧ b ≠ pa := Iff.rfl

/-- The joint interpretation's DH codec functions return. -/
theorem modelReply_dhCodec : Tacenta.UnitSatisfiabilityJoint.DhCodecShape Interp.modelReply :=
  ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩,
    fun _ _ => ⟨_, rfl⟩⟩

/-- The joint interpretation's agreement returns. -/
theorem modelReply_dhAgree : Tacenta.UnitSatisfiabilityJoint.DhAgreeShape Interp.modelReply :=
  fun _ _ => ⟨_, rfl⟩

/-- The agreement law holds in the joint interpretation: both sides return the base point, since no public key is
all zero. -/
theorem modelReply_symmetric : DhAgreeSymmetricShape Interp.modelReply := by
  intro a b pa pb ha hb
  simp only [Interp.modelReply, ok.injEq] at ha hb
  subst ha hb
  show ok (if (replyPub b).val = Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
      else some Tacenta.UnitLifecycleEstablishResponder.basePoint) =
    ok (if (replyPub a).val = Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
      else some Tacenta.UnitLifecycleEstablishResponder.basePoint)
  rw [if_neg (replyPub_ne_zero b), if_neg (replyPub_ne_zero a)]

/-- **`DhAgreeContributoryShape` holds in the joint interpretation**: no public key is all zero. -/
theorem modelReply_contributory : DhAgreeContributoryShape Interp.modelReply := by
  intro a b pb hb
  simp only [Interp.modelReply, ok.injEq] at hb
  subst hb
  refine ⟨Tacenta.UnitLifecycleEstablishResponder.basePoint, ?_⟩
  show ok (if (replyPub b).val = Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
      else some Tacenta.UnitLifecycleEstablishResponder.basePoint) = _
  rw [if_neg (replyPub_ne_zero b)]

/-- **The first receipt's joint model does not satisfy `DhPublicNotConstantShape`**: there every private key has the
base point as public key, so no key's public key differs from the base point.  This is why the reply's receipt
needs a new joint model: in `InterpO.modelFirstReceipt` the responder's fresh ratchet key is always its signed
prekey's, and the initiator's receive of the reply takes the refusing arm. -/
theorem modelFirstReceipt_not_notConstant : ¬ DhPublicNotConstantShape Interp.modelFirstReceipt := by
  intro h
  obtain ⟨_sb, _k, pk, b, _hk, hpk, hb, hne⟩ := h Tacenta.UnitLifecycleEstablishResponder.basePoint
  have hpk' : ok Tacenta.UnitLifecycleEstablishResponder.basePoint = ok pk := hpk
  injection hpk' with hpk''
  subst hpk''
  have hb' : ok Tacenta.UnitLifecycleEstablishResponder.basePoint = ok b := hb
  injection hb' with hb''
  exact hne hb''.symm

/-- **`DhPublicNotConstantShape` holds in the joint interpretation**: the base point and the key `1` are their
own public keys, and they differ, so one of them differs from any given bytes. -/
theorem modelReply_notConstant : DhPublicNotConstantShape Interp.modelReply := by
  intro pa
  by_cases h : pa = Tacenta.UnitLifecycleEstablishResponder.basePoint
  · refine ⟨Tacenta.UnitLifecycleEstablishedDecrypt.oneKey, Tacenta.UnitLifecycleEstablishedDecrypt.oneKey,
      Tacenta.UnitLifecycleEstablishedDecrypt.oneKey, Tacenta.UnitLifecycleEstablishedDecrypt.oneKey, rfl, ?_, rfl, ?_⟩
    · exact congrArg ok replyPub_oneKey
    · subst h; decide
  · refine ⟨Tacenta.UnitLifecycleEstablishResponder.basePoint, Tacenta.UnitLifecycleEstablishResponder.basePoint,
      Tacenta.UnitLifecycleEstablishResponder.basePoint, Tacenta.UnitLifecycleEstablishResponder.basePoint, rfl, ?_,
      rfl, fun he => h he.symm⟩
    exact congrArg ok replyPub_basePoint

open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleSessionCodec (ZeroizingVecRoundTripShape DhPrivateBytesRoundTripShape
  DhPublicBytesRoundTripShape OptionBranchSomeShape VecAsSliceShape optionBranchImpl vecAsSliceImpl) in
open Tacenta.UnitLifecycleRestoredSession (KemCiphertextLenBoundShape) in
open Tacenta.UnitLifecycleEstablishInitiatorShape (InitiatorSuccessShape DhPublicValidShape
  KemCiphertextLenLawShape) in
/-- **Every law of the first receipt's joint model holds again in `InterpO.modelReply`, together with
`DhPublicNotConstantShape`**: the same conjuncts as `first_receipt_laws_model`, in the same order, at the
interpretation whose public key varies, then the new law.  In the substitution sense of
`UnitSatisfiabilityRecords`; not a statement that the real primitives meet them. -/
theorem reply_receipt_laws_model :
    Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape Interp.modelReply viewReply toyKemR
        @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
      Nonempty (InitiatorAxiom Interp.modelReply byteRng) ∧
      InitiatorSuccessShape Interp.modelReply byteRng byteCrc ∧
      DhPublicValidShape Interp.modelReply ∧
      KemCiphertextLenLawShape (ok 0#usize) Interp.modelReply ∧
      EncryptExtraLawsShape InterpO.modelReply dhViewReply kemViewReply toyKemR (ok 0#usize) ∧
      (ZeroizingVecRoundTripShape Interp.modelReply ∧
        DhPrivateBytesRoundTripShape Interp.modelReply ∧
        DhPublicBytesRoundTripShape Interp.modelReply ∧ OptionBranchSomeShape @optionBranchImpl ∧
        VecAsSliceShape @vecAsSliceImpl ∧ KemCiphertextLenBoundShape (ok 0#usize)) ∧
      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf toyKemR ∧
      toyKemR.keyGen (Model.Lifecycle.braidRandomness
          (zeroSeed.map Tacenta.SessionUnitBraidT3.u8)) = none ∧
      toyKemR.keyGen (Model.Lifecycle.braidRandomness
          (oneSeed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none ∧
      Nonempty (ResponderAxiom Interp.modelReply byteRng) ∧
      Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape Interp.modelReply ∧
      Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape Interp.modelReply ∧
      DhAgreeSymmetricShape Interp.modelReply ∧
      FirstFrameSuccessShape Interp.modelReply (fun _ => ok (alloc.vec.Vec.new U8))
        (fun _ v => ok (decide (v.val = []))) ∧
      AeadRoundTripShape Interp.modelReply ∧ DhAgreeContributoryShape Interp.modelReply ∧
      DhPublicNotConstantShape Interp.modelReply := by
  obtain ⟨M, ⟨A⟩, -, -, C, X, ⟨r1, r2, r3, r4, r5, r6⟩, ks, s0, s1⟩ := established_encrypt_laws_model
  obtain ⟨-, ⟨RA⟩, -, -, -⟩ := Tacenta.UnitLifecycleEstablishResponder.responder_route_laws_model
  have hcodec := modelReply_dhCodec
  have hagree := modelReply_dhAgree
  have hb := basePoint_ne_zero
  refine ⟨?_, ⟨?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, r4, r5, r6⟩, ks, s0, s1, ⟨?_⟩, ?_, ?_,
    modelReply_symmetric, ?_, modelFirstReceipt_aeadRoundTrip, modelReply_contributory, modelReply_notConstant⟩
  · exact
      { dhCodec := hcodec
        dhAgree := hagree
        aeadOpen := modelFirstReceipt_aeadOpen
        viewInjective := M.viewInjective
        codec := by have h := M.codec; cases h; constructor <;> assumption
        braid := by have h := M.braid; cases h; constructor <;> assumption
        triple := by have h := M.triple; cases h; constructor <;> assumption
        messageKeyMaterial := M.messageKeyMaterial
        laws := by have h := M.laws; cases h; constructor <;> assumption
        truncatePrefix := M.truncatePrefix
        derivedKeys := by
          obtain ⟨h⟩ := M.derivedKeys; cases h; exact ⟨by constructor <;> assumption⟩
        agreements := by have h := M.agreements; cases h; constructor <;> assumption
        roundTrips := by have h := M.roundTrips; cases h; constructor <;> assumption
        validKey := ⟨Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32,
          Tacenta.UnitLifecycleEstablishResponder.basePoint, Tacenta.UnitLifecycleEstablishResponder.basePoint,
          congrArg ok replyPub_zeros, rfl,
          Tacenta.UnitLifecycleEstablishResponder.basePoint_canonical, rfl⟩
        optionEq := M.optionEq }
  · exact
      { dhCodec := hcodec
        dhIdentity := A.dhIdentity
        dhAgree := hagree
        kemEncapsulate := A.kemEncapsulate
        xeddsaVerify := A.xeddsaVerify
        rngTotal := A.rngTotal
        random32 := A.random32
        sessionHkdf := A.sessionHkdf
        sessionZeroizing := by have h := A.sessionZeroizing; cases h; constructor <;> assumption
        tripleZeroizing := A.tripleZeroizing
        spqrZeroize := A.spqrZeroize
        braidHkdf := A.braidHkdf
        zeroizingArray := A.zeroizingArray
        rangeFullIndex := A.rangeFullIndex }
  · refine ⟨⟨Tacenta.UnitLifecycleEstablishedDecrypt.oneKey, Tacenta.UnitLifecycleEstablishedDecrypt.oneKey,
      rfl, Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_canonical, rfl, ?_,
      fun _ => ⟨Array.repeat 64#usize 0#u8, rfl⟩, fun k => ⟨Tacenta.UnitLifecycleEstablishResponder.basePoint, ?_⟩⟩,
      ⟨alloc.vec.Vec.new U8, by simp; scalar_tac, fun rng => ?_⟩⟩
    · show ok (decide (Tacenta.UnitLifecycleEstablishedDecrypt.oneKey.val =
        Tacenta.UnitLifecycleEstablishedDecrypt.oneKey.val)) = ok true
      simp
    · show ok (if Tacenta.UnitLifecycleEstablishedDecrypt.oneKey.val =
          Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
        else some Tacenta.UnitLifecycleEstablishResponder.basePoint) =
        ok (some Tacenta.UnitLifecycleEstablishResponder.basePoint)
      simp [Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_ne_zero]
    · show ∃ ct ss rng', encapFill byteRng byteCrc _ rng = ok (core.result.Result.Ok (ct, ss), rng')
      simp only [encapFill, if_true]
      exact ⟨_, _, _, rfl⟩
  · intro k pkb h
    have hp : pkb = replyPub k := by
      simpa [Interp.modelReply] using h.symm
    subst hp
    exact ⟨replyPub k, rfl, replyPub_canonical k, rfl⟩
  · exact C
  · exact
      { oracle :=
          { dhCodec := hcodec
            dhAgree := hagree
            dhIdentity := X.oracle.dhIdentity
            aeadSeal := modelFirstReceipt_aeadSeal
            aeadOpen := modelFirstReceipt_aeadOpen
            kemDecapsulate := X.oracle.kemDecapsulate
            xeddsaVerify := X.oracle.xeddsaVerify
            signLaw := X.oracle.signLaw
            kemLaw := X.oracle.kemLaw
            dhView := X.oracle.dhView
            kemView := X.oracle.kemView }
        encrypt :=
          { braid := by have h := X.encrypt.braid; cases h; constructor <;> assumption
            triple := by have h := X.encrypt.triple; cases h; constructor <;> assumption
            aeadSeal := modelFirstReceipt_aeadSeal
            messageKeyMaterial := X.encrypt.messageKeyMaterial
            dhCodec := hcodec }
        keyGen := X.keyGen
        zeroizingKeys := X.zeroizingKeys
        ciphertextBound := X.ciphertextBound }
  · exact r1
  · exact r2
  · exact r3
  · exact
      { decrypt := ⟨hcodec, hagree, modelFirstReceipt_aeadOpen, RA.decrypt.random32,
          by have h := RA.decrypt.braid; cases h; constructor <;> assumption,
          by have h := RA.decrypt.triple; cases h; constructor <;> assumption,
          RA.decrypt.messageKeyMaterial⟩
        dhIdentity := RA.dhIdentity
        kemDecapsulate := RA.kemDecapsulate
        sessionHkdf := RA.sessionHkdf
        sessionZeroizing := by have h := RA.sessionZeroizing; cases h; constructor <;> assumption
        vecPop := RA.vecPop
        divCeilValue := RA.divCeilValue }
  · refine ⟨⟨Tacenta.UnitLifecycleEstablishResponder.basePoint, rfl, rfl, rfl,
      fun k => ⟨Tacenta.UnitLifecycleEstablishResponder.basePoint, ?_⟩⟩,
      ⟨(), alloc.vec.Vec.new U8, Tacenta.UnitSatisfiabilityBraidStates.zeros32, by simp, rfl⟩,
      ⟨alloc.vec.Vec.new _⟩⟩
    show ok (if Tacenta.UnitLifecycleEstablishResponder.basePoint.val =
        Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
      else some Tacenta.UnitLifecycleEstablishResponder.basePoint) =
      ok (some Tacenta.UnitLifecycleEstablishResponder.basePoint)
    simp [hb]
  · refine ⟨Tacenta.UnitSatisfiabilityBraidStates.zeros32, rfl, fun k => ?_⟩
    show (ok (if Tacenta.UnitSatisfiabilityBraidStates.zeros32.val =
        Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
      else some Tacenta.UnitLifecycleEstablishResponder.basePoint)) = ok none
    simp [Tacenta.UnitSatisfiabilityBraidStates.zeros32, Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32]
  · refine ⟨⟨Tacenta.UnitSatisfiabilityBraidStates.zeros32, Tacenta.UnitSatisfiabilityBraidStates.zeros32,
      Tacenta.UnitLifecycleEstablishResponder.basePoint, Tacenta.UnitLifecycleEstablishResponder.basePoint,
      rfl, ?_, rfl, Tacenta.UnitLifecycleEstablishResponder.basePoint_canonical, rfl, ?_,
      fun _ => ⟨Array.repeat 64#usize 0#u8, rfl⟩, fun k => ⟨Tacenta.UnitLifecycleEstablishResponder.basePoint, ?_⟩⟩,
      ⟨(), alloc.vec.Vec.new U8, List.replicate 32 0#u8, alloc.vec.Vec.new U8,
        Tacenta.UnitSatisfiabilityBraidStates.zeros32, [], rfl, by simp; scalar_tac, ?_, ?_⟩,
      ⟨alloc.vec.Vec.new PoolEntry, rfl⟩, fun _ _ => rfl⟩
    · exact congrArg ok replyPub_zeros
    · show ok (decide (Tacenta.UnitLifecycleEstablishResponder.basePoint.val =
        Tacenta.UnitLifecycleEstablishResponder.basePoint.val)) = ok true
      simp
    · show ok (if Tacenta.UnitLifecycleEstablishResponder.basePoint.val =
          Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
        else some Tacenta.UnitLifecycleEstablishResponder.basePoint) =
        ok (some Tacenta.UnitLifecycleEstablishResponder.basePoint)
      simp [hb]
    · show encapFill byteRng byteCrc _ (List.replicate 32 0#u8) = _
      simp [encapFill, encapResult, byteRng, Tacenta.UnitLifecycleIntegrationScreen.zeros32,
        Tacenta.UnitLifecycleIntegrationScreen.zeroSlice]
      decide
    · rfl

end JointModel

/-! ## The reach: one run, from `publish` to the initiator's receipt of the reply -/

section Reach

open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace chunks32)
open Tacenta.UnitLifecycleResponderFirstFrame (FirstFrameSuccessShape PoolEntry reachStore reachBundle
  publish_reachStore reachStore_distinct reach_establishment heldKemPair zPool InitiatorSecretParts
  DhAgreeSymmetric FirstKemAgrees)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory AeadRoundTrip)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid)
open Tacenta.UnitLifecycleResponderReply (oracleOf_with_draws)

/-- A byte-stream state of exactly 32 bytes holds one draw, its bytes. -/
theorem byteTrace_one (l : List Std.U8) (h : l.length = 32) :
    byteTrace l = [l.map Tacenta.SessionUnitBraidT3.u8] := by
  unfold byteTrace
  rw [chunks32, if_pos (by simp [h]), chunks32, if_neg (by simp [h])]
  simp [h]

/-- A byte-stream state of a 64-byte seed followed by 32 more bytes holds three draws: the seed's two halves, then
the 32 bytes. -/
theorem byteTrace_seed_extra (seed extra : List Std.U8) (hseed : seed.length = 64) (hextra : extra.length = 32) :
    byteTrace (seed ++ extra) =
      ((seed ++ extra).map Tacenta.SessionUnitBraidT3.u8).take 32 ::
        (((seed ++ extra).map Tacenta.SessionUnitBraidT3.u8).drop 32).take 32 ::
          [extra.map Tacenta.SessionUnitBraidT3.u8] := by
  rw [Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two _ (by simp [hseed])]
  have hd : (((seed ++ extra).map Tacenta.SessionUnitBraidT3.u8).drop 32).drop 32 =
      extra.map Tacenta.SessionUnitBraidT3.u8 := by
    rw [List.drop_drop, List.map_append, List.drop_append_of_le_length (by simp [hseed])]
    simp [hseed]
  rw [hd, chunks32, if_pos (by simp [hextra]), chunks32, if_neg (by simp [hextra])]
  simp [hextra]

/-- The first two draws of that state are the seed's bytes. -/
theorem two_draws_of_seed_extra (seed extra : List Std.U8) (hseed : seed.length = 64) :
    ((seed ++ extra).map Tacenta.SessionUnitBraidT3.u8).take 32 ++
        (((seed ++ extra).map Tacenta.SessionUnitBraidT3.u8).drop 32).take 32 =
      seed.map Tacenta.SessionUnitBraidT3.u8 := by
  rw [← List.take_add, List.map_append, List.take_append_of_le_length (by simp [hseed])]
  exact List.take_of_length_le (by simp [hseed])

open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleEstablishedEncrypt (EstablishedEncryptHypotheses EncryptExtraLaws emptyPlaintext) in
/-- **One run from `publish` to the responder's reply, for every 32-byte responder source, with the initiator's
receipt of the reply**: at the real constants, under the laws of `first_send_receive_reachable` (all assumed), for
every initiator identity, every 64-byte seed at whose bytes the model's key generation answers and every 32 further
bytes, and every reply plaintext `ptR` of at most 4096 bytes, there are a prekey store, its owner and the bundle it
publishes (the store's signed prekey secret gives, through `from_bytes`, `public_key` and `as_bytes`, the peer key
bytes the initiator holds), a successful establishment against that bundle and a first send of the empty plaintext
from the seed followed by the 32 bytes, such that the oracle's public key of any 32 bytes is the bytes of the
boundary's public key of them, and for every 32-byte responder source `establish_responder` on the first send's bytes
succeeds, the responder's `encrypt` of `ptR` from the source it left returns bytes, and the initiator's `decrypt` of
those bytes from the source its first send left
* returns `ptR` and clears the pending initial message when the oracle's public key of the responder's
  draw is not the peer key the initiator holds, and
* refuses `Triple(Classical(NoReceivingChain))` with the session unchanged when it is.
It applies `initiator_receives_reply_two_outcomes` to that run; the two parties share
the oracle up to its draws and the byte-stream source type.  Last-resort path only.  Compiler-trusted. -/
theorem reply_receipt_reach_run (K : Model.Braid.Kem) (dh : DhView)
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
    (extra : List Std.U8) (hextra : extra.length = 32)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none)
    (ptR : Slice Std.U8) (hptR : ptR.val.length ≤ 4096) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle)
      (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (bytes : alloc.vec.Vec Std.U8)
      (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
      (kB : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes),
      oracle.braidKem = K ∧
      lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext (seed ++ extra) =
        ok (core.result.Result.Ok bytes, s', rng') ∧
      lifecycle.PrekeyStore.publish storeB = ok bundle ∧
      tacenta_boundary.dh.PrivateKey.from_bytes storeB.signed_prekey_secret = ok kB ∧
      tacenta_boundary.dh.PrivateKey.public_key kB = ok pkb ∧
      tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok q.peerRatchetBytes ∧
      (∀ (sb : Array U8 32#usize) (k : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes)
        (b : Array U8 32#usize), tacenta_boundary.dh.PrivateKey.from_bytes sb = ok k →
        tacenta_boundary.dh.PrivateKey.public_key k = ok pk → tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok b →
        oracle.dhPublic (arrayOf sb) = arrayOf b) ∧
      ∀ seedB : List Std.U8, seedB.length = 32 →
        ∃ (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8) (storeB' : lifecycle.PrekeyStore)
          (rngB' : List Std.U8) (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session),
          lifecycle.establish_responder byteRng byteCrc ourB storeB (alloc.vec.Vec.deref bytes) seedB =
            ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
          lifecycle.Session.encrypt byteRng byteCrc sB' ptR rngB' =
            ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
          (oracle.dhPublic (seedB.map Tacenta.SessionUnitBraidT3.u8) ≠ arrayOf q.peerRatchetBytes →
            ∃ (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' : List Std.U8),
              lifecycle.Session.decrypt byteRng byteCrc s' (alloc.vec.Vec.deref bytesR) rng' =
                ok (core.result.Result.Ok ptA, s'', rngA') ∧
              ptA.val = ptR.val ∧ s''.pending_initial = none) ∧
          (oracle.dhPublic (seedB.map Tacenta.SessionUnitBraidT3.u8) = arrayOf q.peerRatchetBytes →
            ∃ rngA' : List Std.U8,
              lifecycle.Session.decrypt byteRng byteCrc s' (alloc.vec.Vec.deref bytesR) rng' =
                ok (core.result.Result.Err (lifecycle.Error.Triple
                  (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.NoReceivingChain)), s',
                  rngA')) := by
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
  refine ⟨oracle, _, q, bytes, s', rng', ourB, storeB, kB, pkb, rfl, hcall, hpublish, hkB', hpkb',
    by rw [hpeer]; exact ha', hpubOf, ?_⟩
  intro seedB hseedB
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
  -- the two outcomes of the initiator's receipt of the reply on this run
  obtain ⟨_dSend, _x, bytesR, sB'', res, s'', rngA', -, -, hcallR, -, hcallA, -, hcases⟩ :=
    initiator_receives_reply_two_outcomes byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView
      oracle H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32
      H.zeroizingKeys H.keyGen hsizes H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1
      q.session H.established q rfl emptyPlaintext H.room (seed ++ extra) H.trace_eq _ _ _ htr bytes s' rng' hcall
      contracts.decrypt ag _ [] hdrawA byteRng byteCrc contracts hpub hsym hcon haead hrt L.optionEq byteTrace
      oracleB oracleOfB H.braid ag ourB storeB hpublish hidentity hdistinct hkem seedB rfl _ [] hdrB ptB sB'
      storeB' rngB' hcallB ptR (by omega) rngB'
  refine ⟨sB', ptB, storeB', rngB', bytesR, sB'', hcallB, hcallR, ?_, ?_⟩
  · intro hfresh
    rcases hcases with ⟨hpeer, -, -⟩ | ⟨-, ptA, hres, hpt, hpend, -, -⟩
    · exact absurd hpeer hfresh
    · subst hres
      exact ⟨ptA, s'', rngA', hcallA, hpt, hpend⟩
  · intro hstale
    rcases hcases with ⟨-, hres, hs⟩ | ⟨hne, -⟩
    · subst hres hs
      exact ⟨rngA', hcallA⟩
    · exact absurd hstale hne

open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleEstablishedEncrypt (EncryptExtraLaws emptyPlaintext) in
/-- **The reach of the reply's receipt**: at the real constants, under the laws of `first_send_receive_reachable`
(all assumed) and the law `DhPublicNotConstant`, for every initiator identity, every 64-byte seed at whose bytes the
model's key generation answers, every 32 further bytes and every reply plaintext `ptR` of at most 4096 bytes: there
is a run (`reply_receipt_reach_run`) whose responder source is chosen by `DhPublicNotConstant` so that the responder's
fresh public key is not the signed prekey's, in which `establish_responder` on the initiator's first-send bytes
succeeds, the responder's `encrypt` of `ptR` returns bytes, and the initiator's `decrypt` of those bytes from the
source its first send left returns `ptR` and clears the pending initial message.  Last-resort path only.  Compiler-trusted. -/
theorem first_send_reply_receipt_reachable (K : Model.Braid.Kem) (dh : DhView)
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
    (ptR : Slice Std.U8) (hptR : ptR.val.length ≤ 4096) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle)
      (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (bytes : alloc.vec.Vec Std.U8)
      (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity)
      (storeB : lifecycle.PrekeyStore) (seedB : List Std.U8) (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8)
      (storeB' : lifecycle.PrekeyStore) (rngB' : List Std.U8) (bytesR : alloc.vec.Vec Std.U8)
      (sB'' : lifecycle.Session) (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' : List Std.U8),
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
      ptA.val = ptR.val ∧ s''.pending_initial = none := by
  obtain ⟨oracle, bundle, q, bytes, s', rng', ourB, storeB, -, -, hK, hcall, hpublish, -, -, -, hpubOf, hrun⟩ :=
    reply_receipt_reach_run K dh kem L A S hpub hct X RA hsym hrt FS hsizes hcon haead ourA seed hseed extra hextra
      hkg ptR hptR
  -- the responder's 32-byte source: a key whose public key is not the peer key the initiator holds
  obtain ⟨sbB, kF, pkF, bF, hkF, hpkF, hbF, hne⟩ := (dhPublicNotConstant_is.mp hnc) q.peerRatchetBytes
  obtain ⟨sB', ptB, storeB', rngB', bytesR, sB'', hcallB, hcallR, hok, -⟩ := hrun sbB.val (by simp)
  have hfresh : oracle.dhPublic (sbB.val.map Tacenta.SessionUnitBraidT3.u8) ≠ arrayOf q.peerRatchetBytes := by
    rw [show sbB.val.map Tacenta.SessionUnitBraidT3.u8 = arrayOf sbB from rfl, hpubOf sbB kF pkF bF hkF hpkF hbF]
    intro hab
    exact hne (Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes hab)
  obtain ⟨ptA, s'', rngA', hcallA, hpt, hpend⟩ := hok hfresh
  exact ⟨oracle, bundle, q, bytes, s', rng', ourB, storeB, sbB.val, sB', ptB, storeB', rngB', bytesR, sB'', ptA, s'',
    rngA', hK, hcall, hpublish, hcallB, hcallR, hcallA, hpt, hpend⟩

open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleEstablishedEncrypt (EncryptExtraLaws emptyPlaintext) in
/-- **The refusing arm is reached**: at the real constants, under the laws of `first_send_receive_reachable` (all
assumed; `DhPublicNotConstant` is not used), on the run of `reply_receipt_reach_run` with the responder's source the
32 bytes of its own signed prekey secret, the responder's fresh ratchet key is its signed prekey's, and the
initiator's `decrypt` of the reply refuses `Triple(Classical(NoReceivingChain))` with its session unchanged, although
`establish_responder` accepted the first send and the responder's `encrypt` returned bytes.  So the premise that the
fresh key is not the peer key is needed by the success theorem, and its failure is reached.  Compiler-trusted. -/
theorem first_send_reply_stale_reachable (K : Model.Braid.Kem) (dh : DhView)
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
    (extra : List Std.U8) (hextra : extra.length = 32)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none)
    (ptR : Slice Std.U8) (hptR : ptR.val.length ≤ 4096) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle)
      (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (bytes : alloc.vec.Vec Std.U8)
      (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity)
      (storeB : lifecycle.PrekeyStore) (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8)
      (storeB' : lifecycle.PrekeyStore) (rngB' : List Std.U8) (bytesR : alloc.vec.Vec Std.U8)
      (sB'' : lifecycle.Session) (rngA' : List Std.U8),
      oracle.braidKem = K ∧
      lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext (seed ++ extra) =
        ok (core.result.Result.Ok bytes, s', rng') ∧
      lifecycle.PrekeyStore.publish storeB = ok bundle ∧
      lifecycle.establish_responder byteRng byteCrc ourB storeB (alloc.vec.Vec.deref bytes)
          storeB.signed_prekey_secret.val =
        ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
      lifecycle.Session.encrypt byteRng byteCrc sB' ptR rngB' =
        ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
      lifecycle.Session.decrypt byteRng byteCrc s' (alloc.vec.Vec.deref bytesR) rng' =
        ok (core.result.Result.Err (lifecycle.Error.Triple
          (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.NoReceivingChain)), s', rngA') := by
  obtain ⟨oracle, bundle, q, bytes, s', rng', ourB, storeB, kB, pkb, hK, hcall, hpublish, hkB, hpkb, hpeer, hpubOf,
    hrun⟩ := reply_receipt_reach_run K dh kem L A S hpub hct X RA hsym hrt FS hsizes hcon haead ourA seed hseed extra
      hextra hkg ptR hptR
  obtain ⟨sB', ptB, storeB', rngB', bytesR, sB'', hcallB, hcallR, -, hstale⟩ :=
    hrun storeB.signed_prekey_secret.val (by simp)
  have hsame : oracle.dhPublic (storeB.signed_prekey_secret.val.map Tacenta.SessionUnitBraidT3.u8) =
      arrayOf q.peerRatchetBytes := by
    rw [show storeB.signed_prekey_secret.val.map Tacenta.SessionUnitBraidT3.u8 = arrayOf storeB.signed_prekey_secret
      from rfl]
    exact hpubOf _ kB pkb _ hkB hpkb hpeer
  obtain ⟨rngA', hcallA⟩ := hstale hsame
  exact ⟨oracle, bundle, q, bytes, s', rng', ourB, storeB, sB', ptB, storeB', rngB', bytesR, sB'', rngA', hK, hcall,
    hpublish, hcallB, hcallR, hcallA⟩

end Reach

end Tacenta.UnitLifecycleResponderReplyReceipt

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.reply_receive_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.reply_receive_key

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.reply_receive_stale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.reply_receive_stale

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.replyFrame_messageType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.replyFrame_messageType

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.replyFrame_decodeDetailed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.replyFrame_decodeDetailed

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.reply_receipt_model_outcomes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.reply_receipt_model_outcomes

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.fresh_public_of_draw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
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
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.fresh_public_of_draw

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.initiator_reply_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
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
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.initiator_reply_agreement

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.initiator_candidate_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
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
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.initiator_candidate_agreement

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.first_send_model_session' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
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
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.first_send_model_session

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.replyAd_length_le' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.replyAd_length_le

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply_outcomes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
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
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
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
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply_outcomes

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply_two_outcomes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
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
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
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
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply_two_outcomes

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
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
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
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
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_canonical

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_ne_zero

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_basePoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_basePoint

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_oneKey' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_oneKey

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_zeros' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_zeros

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.dhPublicNotConstant_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
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
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.dhPublicNotConstant_is

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_dhCodec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_dhCodec

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_dhAgree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_dhAgree

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_symmetric

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_contributory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_contributory

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.modelFirstReceipt_not_notConstant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.modelFirstReceipt_not_notConstant

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_notConstant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_notConstant

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.reply_receipt_laws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.reply_receipt_laws_model

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.byteTrace_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.byteTrace_one

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.byteTrace_seed_extra' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.byteTrace_seed_extra

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.two_draws_of_seed_extra' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.two_draws_of_seed_extra

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.reply_receipt_reach_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
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
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
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
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.reply_receipt_reach_run

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.first_send_reply_receipt_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
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
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
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
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.first_send_reply_receipt_reachable

/--
info: 'Tacenta.UnitLifecycleResponderReplyReceipt.first_send_reply_stale_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
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
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
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
#print axioms Tacenta.UnitLifecycleResponderReplyReceipt.first_send_reply_stale_reachable

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.reply_receive_key : ∀
  (a4 peer rkA cksA prk k1 k2 dSend x newPub candPub : Model.State.Key),
  newPub ≠ peer →
    Model.Triple.receiveDetailed
        (Tacenta.UnitLifecycleResponderFirstReceipt.senderAfterFirst a4 peer rkA cksA prk k1 k2)
        (Tacenta.UnitLifecycleResponderFirstReceipt.firstHeader newPub) dSend x candPub none =
      Except.ok
        (Tacenta.UnitLifecycleResponderReplyReceipt.initiatorAfterReply rkA prk k1 k2 dSend x newPub candPub,
          Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
            (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).2 k2)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.reply_receive_key

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.reply_receive_stale : ∀
  (a4 peer rkA cksA prk k1 k2 dSend x candPub : Model.State.Key),
  Model.Triple.receiveDetailed (Tacenta.UnitLifecycleResponderFirstReceipt.senderAfterFirst a4 peer rkA cksA prk k1 k2)
      (Tacenta.UnitLifecycleResponderFirstReceipt.firstHeader peer) dSend x candPub none =
    Except.error (Model.Triple.ReceiveRefusal.classical Model.Ratchet.ReceiveRefusal.noReceivingChain)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.reply_receive_stale

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.replyFrame_messageType : ∀ (oracle : Model.Lifecycle.Oracle)
  (ad : Model.Lifecycle.Bytes) (newPub mk : Model.State.Key) (pt : Model.Lifecycle.Bytes),
  Model.Lifecycle.messageType (Tacenta.UnitLifecycleResponderReply.replyFrame oracle ad newPub mk pt) =
    some Model.Lifecycle.MessageType.ratchet
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.replyFrame_messageType

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.replyFrame_decodeDetailed : ∀ (oracle : Model.Lifecycle.Oracle)
  (ad : Model.Lifecycle.Bytes) (newPub mk : Model.State.Key) (pt : Model.Lifecycle.Bytes),
  List.length newPub = 32 →
    Model.Messages.checkKey newPub = some () →
      Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleResponderReply.replyFrame oracle ad newPub mk pt) =
        Except.ok
          (Tacenta.UnitLifecycleResponderReply.replyComposite newPub,
            oracle.aeadSeal (Model.State.messageKeys mk Model.State.LabelSet.tacenta).1
              (Model.State.messageKeys mk Model.State.LabelSet.tacenta).2.1
              (Model.State.messageKeys mk Model.State.LabelSet.tacenta).2.2 pt
              (Tacenta.UnitLifecycleResponderReplyReceipt.replyAd ad newPub))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.replyFrame_decodeDetailed

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.reply_receipt_model_outcomes : ∀ (view : Model.Lifecycle.CodewordView)
  (oracleA oracleB : Model.Lifecycle.Oracle) (mA : Model.Lifecycle.Session)
  (a4 peer rkA cksA prk k1 k2 : Model.State.Key) (e : ℕ) (auth : Model.Braid.Auth) (dk ekVector : Model.Braid.Bytes)
  (enc : Model.Braid.Encoder),
  mA.triple = Tacenta.UnitLifecycleResponderFirstReceipt.senderAfterFirst a4 peer rkA cksA prk k1 k2 →
    mA.braid = Model.Braid.BraidState.keysSampled e auth dk ekVector enc →
      ∀ (newPub dSend : Model.State.Key) (pt : Model.Lifecycle.Bytes),
        List.length newPub = 32 →
          Model.Messages.checkKey newPub = some () →
            oracleA.dhAgree mA.ratchetPrivate newPub = some dSend →
              oracleA.draws = [] ∧
                  Model.Lifecycle.decrypt view oracleA mA
                      (Tacenta.UnitLifecycleResponderReply.replyFrame oracleB mA.identityAd newPub
                        (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                          (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).2 k2)
                        pt) =
                    { session := mA, result := Except.error Model.Lifecycle.Refusal.ceiling, oracle := oracleA } ∨
                (∃ c rest,
                    oracleA.draws = c :: rest ∧
                      oracleA.dhAgree c newPub = none ∧
                        Model.Lifecycle.decrypt view oracleA mA
                            (Tacenta.UnitLifecycleResponderReply.replyFrame oracleB mA.identityAd newPub
                              (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).2 k2)
                              pt) =
                          { session := mA,
                            result :=
                              Except.error
                                (Model.Lifecycle.Refusal.handshake
                                  Model.Lifecycle.HandshakeRefusal.nonContributoryAgreement),
                            oracle :=
                              { draws := rest, braidKem := oracleA.braidKem, dhPublic := oracleA.dhPublic,
                                dhAgree := oracleA.dhAgree, identityValid := oracleA.identityValid,
                                aeadSeal := oracleA.aeadSeal, aeadOpen := oracleA.aeadOpen,
                                kemValid := oracleA.kemValid, kemEncaps := oracleA.kemEncaps,
                                kemDecaps := oracleA.kemDecaps, sigVerify := oracleA.sigVerify,
                                sigSign := oracleA.sigSign } }) ∨
                  (∃ c rest x,
                      oracleA.draws = c :: rest ∧
                        oracleA.dhAgree c newPub = some x ∧
                          newPub = peer ∧
                            Model.Lifecycle.decrypt view oracleA mA
                                (Tacenta.UnitLifecycleResponderReply.replyFrame oracleB mA.identityAd newPub
                                  (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                    (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).2 k2)
                                  pt) =
                              { session := mA,
                                result :=
                                  Except.error
                                    (Model.Lifecycle.tripleReceiveRefusalOf
                                      (Model.Triple.ReceiveRefusal.classical
                                        Model.Ratchet.ReceiveRefusal.noReceivingChain)),
                                oracle :=
                                  { draws := rest, braidKem := oracleA.braidKem, dhPublic := oracleA.dhPublic,
                                    dhAgree := oracleA.dhAgree, identityValid := oracleA.identityValid,
                                    aeadSeal := oracleA.aeadSeal, aeadOpen := oracleA.aeadOpen,
                                    kemValid := oracleA.kemValid, kemEncaps := oracleA.kemEncaps,
                                    kemDecaps := oracleA.kemDecaps, sigVerify := oracleA.sigVerify,
                                    sigSign := oracleA.sigSign } }) ∨
                    (∃ c rest x,
                        oracleA.draws = c :: rest ∧
                          oracleA.dhAgree c newPub = some x ∧
                            newPub ≠ peer ∧
                              Tacenta.UnitLifecycleResponderFirstReceipt.firstOpen oracleB oracleA
                                    (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                      (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).2 k2)
                                    pt (Tacenta.UnitLifecycleResponderReplyReceipt.replyAd mA.identityAd newPub) =
                                  none ∧
                                Model.Lifecycle.decrypt view oracleA mA
                                    (Tacenta.UnitLifecycleResponderReply.replyFrame oracleB mA.identityAd newPub
                                      (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                        (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).2 k2)
                                      pt) =
                                  { session := mA, result := Except.error Model.Lifecycle.Refusal.aead,
                                    oracle :=
                                      { draws := rest, braidKem := oracleA.braidKem, dhPublic := oracleA.dhPublic,
                                        dhAgree := oracleA.dhAgree, identityValid := oracleA.identityValid,
                                        aeadSeal := oracleA.aeadSeal, aeadOpen := oracleA.aeadOpen,
                                        kemValid := oracleA.kemValid, kemEncaps := oracleA.kemEncaps,
                                        kemDecaps := oracleA.kemDecaps, sigVerify := oracleA.sigVerify,
                                        sigSign := oracleA.sigSign } }) ∨
                      ∃ c rest x y,
                        oracleA.draws = c :: rest ∧
                          oracleA.dhAgree c newPub = some x ∧
                            newPub ≠ peer ∧
                              Tacenta.UnitLifecycleResponderFirstReceipt.firstOpen oracleB oracleA
                                    (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                      (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).2 k2)
                                    pt (Tacenta.UnitLifecycleResponderReplyReceipt.replyAd mA.identityAd newPub) =
                                  some y ∧
                                Model.Lifecycle.decrypt view oracleA mA
                                    (Tacenta.UnitLifecycleResponderReply.replyFrame oracleB mA.identityAd newPub
                                      (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                        (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).2 k2)
                                      pt) =
                                  {
                                    session :=
                                      Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession mA rkA prk k1 k2
                                        dSend x newPub (oracleA.dhPublic c) c,
                                    result := Except.ok y,
                                    oracle :=
                                      { draws := rest, braidKem := oracleA.braidKem, dhPublic := oracleA.dhPublic,
                                        dhAgree := oracleA.dhAgree, identityValid := oracleA.identityValid,
                                        aeadSeal := oracleA.aeadSeal, aeadOpen := oracleA.aeadOpen,
                                        kemValid := oracleA.kemValid, kemEncaps := oracleA.kemEncaps,
                                        kemDecaps := oracleA.kemDecaps, sigVerify := oracleA.sigVerify,
                                        sigSign := oracleA.sigSign } }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.reply_receipt_model_outcomes

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.fresh_public_of_draw : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
  ∀ {E : Type} {rcB : rand_core_1.RngCore E} {crcB : rand_core_1.CryptoRng E} {dh : Tacenta.UnitLifecycleT3.DhView},
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      ∀ {traceB : E → List Model.Lifecycle.Key} {oracleB : Model.Lifecycle.Oracle},
        Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
          ∀ (rngB : E) (dB : Model.Lifecycle.Key) (restB : List Model.Lifecycle.Key),
            traceB rngB = dB :: restB →
              ∃ value k pk b,
                Tacenta.UnitLifecycleT3.arrayOf value = dB ∧
                  tacenta_boundary.dh.PrivateKey.from_bytes value = ok k ∧
                    dh.privateKey k = dB ∧
                      k.public_key = ok pk ∧
                        pk.as_bytes = ok b ∧
                          Tacenta.SessionUnitT1.canonicalX25519 b = true ∧
                            dh.publicKey pk = Tacenta.UnitLifecycleT3.arrayOf b ∧
                              oracleB.dhPublic dB = Tacenta.UnitLifecycleT3.arrayOf b
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.fresh_public_of_draw

/--
info: @Tacenta.UnitLifecycleResponderReplyReceipt.initiator_reply_agreement : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle},
  Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
    ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        ∀ {traceA : R → List Model.Lifecycle.Key} {oracleA : Model.Lifecycle.Oracle},
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rc crc dh traceA oracleA →
            ∀ {E F : Type} {rcE : rand_core_1.RngCore E} {crcE : rand_core_1.CryptoRng E} {rcB : rand_core_1.RngCore F}
              {crcB : rand_core_1.CryptoRng F} {traceB : F → List Model.Lifecycle.Key}
              {oracleB : Model.Lifecycle.Oracle},
              Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
                ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcE crcE our bundle)
                  (k : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
                  k.public_key = ok pk →
                    oracleA.dhAgree (dh.privateKey q.ratchetPrivate) (dh.publicKey pk) =
                      oracleB.dhAgree (dh.privateKey k) (Tacenta.UnitLifecycleT3.arrayOf q.ratchetBytes)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.initiator_reply_agreement

/--
info: @Tacenta.UnitLifecycleResponderReplyReceipt.initiator_candidate_agreement : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R},
  Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
    ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        ∀ {traceA : R → List Model.Lifecycle.Key} {oracleA : Model.Lifecycle.Oracle},
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rc crc dh traceA oracleA →
            ∀ (rng : R) (dA : Model.Lifecycle.Key) (restA : List Model.Lifecycle.Key),
              traceA rng = dA :: restA →
                ∀ (k : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes),
                  k.public_key = ok pk → ∃ x, oracleA.dhAgree dA (dh.publicKey pk) = some x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.initiator_candidate_agreement

/--
info: @Tacenta.UnitLifecycleResponderReplyReceipt.first_send_model_session : ∀ {our : lifecycle.Identity}
  {bundle : lifecycle.PublishedBundle} {E : Type} {rcE : rand_core_1.RngCore E} {crcE : rand_core_1.CryptoRng E}
  (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
  (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcE crcE our bundle)
  (plaintext : Model.Lifecycle.Bytes) (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
  oracle.draws = d1 :: d2 :: rest →
    ∀ (dk ekSeed ekVector : Model.Braid.Bytes),
      oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector) →
        ∃ encoder,
          (Model.Lifecycle.encrypt view oracle
                (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh q.session) plaintext).session =
            have __src := Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh q.session;
            {
              triple :=
                Tacenta.UnitLifecycleResponderFirstReceipt.senderAfterFirst
                  (Tacenta.UnitLifecycleT3.arrayOf q.ratchetBytes) (Tacenta.UnitLifecycleT3.arrayOf q.peerRatchetBytes)
                  (Tacenta.UnitLifecycleT3.arrayOf q.rootKey) (Tacenta.UnitLifecycleT3.arrayOf q.sendChain)
                  (Tacenta.UnitLifecycleT3.arrayOf q.sparseRoot) (Tacenta.UnitLifecycleT3.arrayOf q.sparseSend)
                  (Tacenta.UnitLifecycleT3.arrayOf q.sparseReceive),
              braid :=
                Model.Braid.BraidState.keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector encoder,
              ratchetPrivate := __src.ratchetPrivate, identityAd := __src.identityAd,
              ourIdentityPublic := __src.ourIdentityPublic, peerIdentityPublic := __src.peerIdentityPublic,
              pendingInitial := __src.pendingInitial, establishedEphemeral := __src.establishedEphemeral }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.first_send_model_session

/--
info: @Tacenta.UnitLifecycleResponderReplyReceipt.replyAd_length_le : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle},
  Tacenta.UnitLifecycleT1.DhCodecTotal →
    ∀ (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle)
      (newPub : Model.Lifecycle.Key),
      List.length newPub = 32 →
        List.length
            (Tacenta.UnitLifecycleResponderReplyReceipt.replyAd (Tacenta.UnitLifecycleT3.vecOf p.identityAd) newPub) ≤
          Usize.max
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.replyAd_length_le

/--
info: @Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply_outcomes : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
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
                                (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session),
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
                                                                (crcB : rand_core_1.CryptoRng F), ⋯
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply_outcomes

/--
info: @Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply_two_outcomes : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
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
                                (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session),
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
                                                                (crcB : rand_core_1.CryptoRng F), ⋯
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply_two_outcomes

/--
info: @Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {R E F : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
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
                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
                        Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem →
                          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                            Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                              ∀ (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
                                (ourA : lifecycle.Identity) (bundleA : lifecycle.PublishedBundle)
                                (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session),
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
                                                                (crcB : rand_core_1.CryptoRng F), ⋯
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.initiator_receives_reply

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_canonical : ∀ (k : Std.Array U8 32#usize),
  Tacenta.SessionUnitT1.canonicalX25519 (Tacenta.UnitLifecycleResponderReplyReceipt.replyPub k) = true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_canonical

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_ne_zero : ∀ (k : Std.Array U8 32#usize),
  ↑(Tacenta.UnitLifecycleResponderReplyReceipt.replyPub k) ≠ ↑Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_ne_zero

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_basePoint : Tacenta.UnitLifecycleResponderReplyReceipt.replyPub
    Tacenta.UnitLifecycleEstablishResponder.basePoint =
  Tacenta.UnitLifecycleEstablishResponder.basePoint
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_basePoint

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_oneKey : Tacenta.UnitLifecycleResponderReplyReceipt.replyPub
    Tacenta.UnitLifecycleEstablishedDecrypt.oneKey =
  Tacenta.UnitLifecycleEstablishedDecrypt.oneKey
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_oneKey

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_zeros : Tacenta.UnitLifecycleResponderReplyReceipt.replyPub
    Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32 =
  Tacenta.UnitLifecycleEstablishResponder.basePoint
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.replyPub_zeros

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.dhPublicNotConstant_is : Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstant ↔
  ∀ (pa : Std.Array U8 32#usize),
    ∃ sb k pk b,
      tacenta_boundary.dh.PrivateKey.from_bytes sb = ok k ∧ k.public_key = ok pk ∧ pk.as_bytes = ok b ∧ b ≠ pa
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.dhPublicNotConstant_is

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_dhCodec : Tacenta.UnitSatisfiabilityJoint.DhCodecShape
  Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_dhCodec

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_dhAgree : Tacenta.UnitSatisfiabilityJoint.DhAgreeShape
  Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_dhAgree

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_symmetric : Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetricShape
  Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_symmetric

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_contributory : Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributoryShape
  Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_contributory

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.modelFirstReceipt_not_notConstant : ¬Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstantShape
    Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.modelFirstReceipt_not_notConstant

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_notConstant : Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstantShape
  Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_notConstant

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.reply_receipt_laws_model : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape
    Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply Tacenta.UnitLifecycleResponderReplyReceipt.viewReply
    Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
  Nonempty
      (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply
        Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
    Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape
        Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc ∧
      Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape
          Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply ∧
        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenLawShape (ok 0#usize)
            Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply ∧
          Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape
              Tacenta.UnitLifecycleResponderReplyReceipt.InterpO.modelReply
              Tacenta.UnitLifecycleResponderReplyReceipt.dhViewReply
              Tacenta.UnitLifecycleResponderReplyReceipt.kemViewReply Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR
              (ok 0#usize) ∧
            (Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTripShape
                  Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply ∧
                Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTripShape
                    Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply ∧
                  Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTripShape
                      Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply ∧
                    Tacenta.UnitLifecycleSessionCodec.OptionBranchSomeShape
                        @Tacenta.UnitLifecycleSessionCodec.optionBranchImpl ∧
                      Tacenta.UnitLifecycleSessionCodec.VecAsSliceShape
                          @Tacenta.UnitLifecycleSessionCodec.vecAsSliceImpl ∧
                        Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape (ok 0#usize)) ∧
              Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR ∧
                Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR.keyGen
                      (Model.Lifecycle.braidRandomness
                        (List.map Tacenta.SessionUnitBraidT3.u8 Tacenta.UnitLifecycleEstablishedEncrypt.zeroSeed)) =
                    none ∧
                  Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR.keyGen
                        (Model.Lifecycle.braidRandomness
                          (List.map Tacenta.SessionUnitBraidT3.u8 Tacenta.UnitLifecycleEstablishedEncrypt.oneSeed)) ≠
                      none ∧
                    Nonempty
                        (Tacenta.UnitSatisfiabilityJoint.ResponderAxiom
                          Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply
                          Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
                      Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape
                          Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply ∧
                        Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape
                            Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply ∧
                          Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetricShape
                              Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply ∧
                            (Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape
                                Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply
                                (fun x => ok (alloc.vec.Vec.new U8)) fun {T} x v => ok (decide (↑v = []))) ∧
                              Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape
                                  Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply ∧
                                Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributoryShape
                                    Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply ∧
                                  Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstantShape
                                    Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.reply_receipt_laws_model

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.byteTrace_one : ∀ (l : List U8),
  l.length = 32 → Tacenta.UnitLifecycleIntegrationScreen.byteTrace l = [List.map Tacenta.SessionUnitBraidT3.u8 l]
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.byteTrace_one

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.byteTrace_seed_extra : ∀ (seed extra : List U8),
  seed.length = 64 →
    extra.length = 32 →
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace (seed ++ extra) =
        [List.take 32 (List.map Tacenta.SessionUnitBraidT3.u8 (seed ++ extra)),
          List.take 32 (List.drop 32 (List.map Tacenta.SessionUnitBraidT3.u8 (seed ++ extra))),
          List.map Tacenta.SessionUnitBraidT3.u8 extra]
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.byteTrace_seed_extra

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.two_draws_of_seed_extra : ∀ (seed extra : List U8),
  seed.length = 64 →
    List.take 32 (List.map Tacenta.SessionUnitBraidT3.u8 (seed ++ extra)) ++
        List.take 32 (List.drop 32 (List.map Tacenta.SessionUnitBraidT3.u8 (seed ++ extra))) =
      List.map Tacenta.SessionUnitBraidT3.u8 seed
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.two_draws_of_seed_extra

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.reply_receipt_reach_run : ∀ (K : Model.Braid.Kem)
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
                                          ∃ oracle bundle q bytes s' rng' ourB storeB kB pkb,
                                            oracle.braidKem = K ∧
                                              lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                    Tacenta.UnitLifecycleIntegrationScreen.byteCrc q.session
                                                    Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext
                                                    (seed ++ extra) =
                                                  ok (core.result.Result.Ok bytes, s', rng') ∧
                                                storeB.publish = ok bundle ∧
                                                  tacenta_boundary.dh.PrivateKey.from_bytes
                                                        storeB.signed_prekey_secret =
                                                      ok kB ∧
                                                    kB.public_key = ok pkb ∧
                                                      pkb.as_bytes = ok q.peerRatchetBytes ∧
                                                        (∀ (sb : Std.Array U8 32#usize)
                                                            (k : tacenta_boundary.dh.PrivateKey)
                                                            (pk : tacenta_boundary.dh.PublicKeyBytes)
                                                            (b : Std.Array U8 32#usize),
                                                            tacenta_boundary.dh.PrivateKey.from_bytes sb = ok k →
                                                              k.public_key = ok pk →
                                                                pk.as_bytes = ok b →
                                                                  oracle.dhPublic (Tacenta.UnitLifecycleT3.arrayOf sb) =
                                                                    Tacenta.UnitLifecycleT3.arrayOf b) ∧
                                                          ∀ (seedB : List U8),
                                                            seedB.length = 32 →
                                                              ∃ sB' ptB storeB' rngB' bytesR sB'',
                                                                lifecycle.establish_responder
                                                                      Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                      Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                                                      ourB storeB bytes.deref seedB =
                                                                    ok
                                                                      (core.result.Result.Ok (sB', ptB), storeB',
                                                                        rngB') ∧
                                                                  lifecycle.Session.encrypt
                                                                        Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                        Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                                                        sB' ptR rngB' =
                                                                      ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
                                                                    ⋯
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.reply_receipt_reach_run

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.first_send_reply_receipt_reachable : ∀ (K : Model.Braid.Kem)
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
                                            ∃ oracle bundle q bytes s' rng' ourB storeB seedB sB' ptB storeB' rngB'
                                              bytesR sB'' ptA s'' rngA',
                                              oracle.braidKem = K ∧
                                                lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                      Tacenta.UnitLifecycleIntegrationScreen.byteCrc q.session
                                                      Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext
                                                      (seed ++ extra) =
                                                    ok (core.result.Result.Ok bytes, s', rng') ∧
                                                  storeB.publish = ok bundle ∧
                                                    lifecycle.establish_responder
                                                          Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                          Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourB storeB
                                                          bytes.deref seedB =
                                                        ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
                                                      lifecycle.Session.encrypt
                                                            Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc sB' ptR
                                                            rngB' =
                                                          ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
                                                        lifecycle.Session.decrypt
                                                              Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                              Tacenta.UnitLifecycleIntegrationScreen.byteCrc s'
                                                              bytesR.deref rng' =
                                                            ok (core.result.Result.Ok ptA, s'', rngA') ∧
                                                          ↑ptA = ↑ptR ∧ s''.pending_initial = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.first_send_reply_receipt_reachable

/--
info: Tacenta.UnitLifecycleResponderReplyReceipt.first_send_reply_stale_reachable : ∀ (K : Model.Braid.Kem)
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
                                          ∃ oracle bundle q bytes s' rng' ourB storeB sB' ptB storeB' rngB' bytesR sB''
                                            rngA',
                                            oracle.braidKem = K ∧
                                              lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                    Tacenta.UnitLifecycleIntegrationScreen.byteCrc q.session
                                                    Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext
                                                    (seed ++ extra) =
                                                  ok (core.result.Result.Ok bytes, s', rng') ∧
                                                storeB.publish = ok bundle ∧
                                                  lifecycle.establish_responder
                                                        Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                        Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourB storeB
                                                        bytes.deref ↑storeB.signed_prekey_secret =
                                                      ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
                                                    lifecycle.Session.encrypt
                                                          Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                          Tacenta.UnitLifecycleIntegrationScreen.byteCrc sB' ptR rngB' =
                                                        ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
                                                      lifecycle.Session.decrypt
                                                          Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                          Tacenta.UnitLifecycleIntegrationScreen.byteCrc s' bytesR.deref
                                                          rng' =
                                                        ok
                                                          (core.result.Result.Err
                                                              (lifecycle.Error.Triple
                                                                (tacenta_triple.TripleError.Classical
                                                                  tacenta_ratchet.RatchetError.NoReceivingChain)),
                                                            s', rngA')
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderReplyReceipt.first_send_reply_stale_reachable

/--
info: def Tacenta.UnitLifecycleResponderReplyReceipt.initiatorAfterReply : Model.State.Key →
  Model.State.Key →
    Model.State.Key →
      Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.Triple.State :=
fun rkA prk k1 k2 dSend x newPub candPub =>
  {
    classical :=
      { dhsPub := candPub, dhrPub := some newPub,
        rk :=
          (Model.State.kdfRk (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).1 x
              Model.State.LabelSet.tacenta).1,
        cks :=
          some
            (Model.State.kdfRk (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).1 x
                Model.State.LabelSet.tacenta).2,
        ckr := some (Model.State.kdfCk (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).2).1, ns := 0,
        nr := 1, pn := 1, skipped := [], events := 1, labels := Model.State.LabelSet.tacenta },
    postQuantum :=
      { rk := prk, epoch := 0,
        chains :=
          [(0,
              { send := some { ck := (Model.SparseRatchet.kdfCk k1 1).1, n := 1 },
                receive := some { ck := (Model.SparseRatchet.kdfCk k2 1).1, n := 1 } })],
        skipped := [], direction := Model.SparseRatchet.Direction.a2b } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReplyReceipt.initiatorAfterReply

/--
info: def Tacenta.UnitLifecycleResponderReplyReceipt.replyAd : Model.Lifecycle.Bytes →
  Model.State.Key → Model.Lifecycle.Bytes :=
fun ad newPub =>
  Model.Messages.concatAd ad (Model.CompositeHeader.encode (Tacenta.UnitLifecycleResponderReply.replyComposite newPub))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReplyReceipt.replyAd

/--
info: def Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession : Model.Lifecycle.Session →
  Model.State.Key →
    Model.State.Key →
      Model.State.Key →
        Model.State.Key →
          Model.State.Key →
            Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.Lifecycle.Session :=
fun mA rkA prk k1 k2 dSend x newPub candPub c =>
  { triple := Tacenta.UnitLifecycleResponderReplyReceipt.initiatorAfterReply rkA prk k1 k2 dSend x newPub candPub,
    braid := mA.braid,
    ratchetPrivate := if (candPub == mA.triple.classical.dhsPub) = true then mA.ratchetPrivate else c,
    identityAd := mA.identityAd, ourIdentityPublic := mA.ourIdentityPublic, peerIdentityPublic := mA.peerIdentityPublic,
    pendingInitial := none, establishedEphemeral := mA.establishedEphemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession

/--
info: def Tacenta.UnitLifecycleResponderReplyReceipt.replyPub : Std.Array U8 32#usize → Std.Array U8 32#usize :=
fun k =>
  if Tacenta.SessionUnitT1.canonicalX25519 k = true ∧ ↑k ≠ ↑Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32 then k
  else Tacenta.UnitLifecycleEstablishResponder.basePoint
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReplyReceipt.replyPub

/--
info: def Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply : Tacenta.UnitSatisfiabilityJoint.Interp :=
let __src := Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt;
{ PrivateKey := __src.PrivateKey, PublicKeyBytes := __src.PublicKeyBytes, KemKeyPair := __src.KemKeyPair,
  IncrementalKeyPair := __src.IncrementalKeyPair, EncapsState := __src.EncapsState, Zeroizing := __src.Zeroizing,
  dhPrivFromBytes := __src.dhPrivFromBytes,
  dhPrivPublicKey := fun k => ok (Tacenta.UnitLifecycleResponderReplyReceipt.replyPub k),
  dhPrivAgree := fun x p =>
    ok
      (if ↑p = ↑Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32 then none
      else some Tacenta.UnitLifecycleEstablishResponder.basePoint),
  dhPrivToBytes := __src.dhPrivToBytes, dhPubFromBytes := __src.dhPubFromBytes, dhPubAsBytes := __src.dhPubAsBytes,
  dhPubEq := __src.dhPubEq, dhIsPrimeOrderPublic := __src.dhIsPrimeOrderPublic, aeadEncrypt := __src.aeadEncrypt,
  aeadDecrypt := __src.aeadDecrypt, kemEncapsulate := @Tacenta.UnitSatisfiabilityJoint.Interp.kemEncapsulate __src,
  kemDecapsulate := __src.kemDecapsulate, xeddsaVerify := __src.xeddsaVerify, hkdfSha256 := __src.hkdfSha256,
  hmacSha256 := __src.hmacSha256, HEADER_LEN := __src.HEADER_LEN, EK_VECTOR_LEN := __src.EK_VECTOR_LEN,
  CT1_LEN := __src.CT1_LEN, CT2_LEN := __src.CT2_LEN, ikpClone := __src.ikpClone,
  ikpGenerate := @Tacenta.UnitSatisfiabilityJoint.Interp.ikpGenerate __src, ikpHeader := __src.ikpHeader,
  ikpEkVector := __src.ikpEkVector, ikpDecapsulate := __src.ikpDecapsulate, esClone := __src.esClone,
  encapsulate1 := @Tacenta.UnitSatisfiabilityJoint.Interp.encapsulate1 __src, encapsulate2 := __src.encapsulate2,
  validateEk := __src.validateEk, blanketZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.blanketZeroize __src,
  arrayZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.arrayZeroize __src,
  tupleZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.tupleZeroize __src,
  pairZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.pairZeroize __src,
  vecZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.vecZeroize __src,
  zNew := @Tacenta.UnitSatisfiabilityJoint.Interp.zNew __src,
  zDeref := @Tacenta.UnitSatisfiabilityJoint.Interp.zDeref __src,
  zDerefMut := @Tacenta.UnitSatisfiabilityJoint.Interp.zDerefMut __src,
  vecPop := @Tacenta.UnitSatisfiabilityJoint.Interp.vecPop __src,
  vecCapacity := @Tacenta.UnitSatisfiabilityJoint.Interp.vecCapacity __src,
  vecTruncate := @Tacenta.UnitSatisfiabilityJoint.Interp.vecTruncate __src,
  optionClone := @Tacenta.UnitSatisfiabilityJoint.Interp.optionClone __src,
  optionAsMut := @Tacenta.UnitSatisfiabilityJoint.Interp.optionAsMut __src,
  rangeFullIndex := @Tacenta.UnitSatisfiabilityJoint.Interp.rangeFullIndex __src, divCeil := __src.divCeil }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply

/--
info: def Tacenta.UnitLifecycleResponderReplyReceipt.InterpO.modelReply : Tacenta.UnitOracleShape.InterpO :=
have __src := Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply;
{ toInterp := __src, xeddsaSign := fun {R} => Tacenta.UnitOracleModel.signModelO }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReplyReceipt.InterpO.modelReply

/--
info: def Tacenta.UnitLifecycleResponderReplyReceipt.viewReply : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape
  Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply :=
{ privateKey := Tacenta.UnitLifecycleT3.arrayOf, publicKey := Tacenta.UnitLifecycleT3.arrayOf }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReplyReceipt.viewReply

/--
info: def Tacenta.UnitLifecycleResponderReplyReceipt.dhViewReply : Tacenta.UnitOracleShape.DhViewOf
  Tacenta.UnitLifecycleResponderReplyReceipt.InterpO.modelReply.toInterp :=
{ privateKey := Tacenta.UnitLifecycleResponderReplyReceipt.viewReply.privateKey,
  publicKey := Tacenta.UnitLifecycleResponderReplyReceipt.viewReply.publicKey }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReplyReceipt.dhViewReply

/--
info: def Tacenta.UnitLifecycleResponderReplyReceipt.kemViewReply : Tacenta.UnitOracleShape.KemViewOf
  Tacenta.UnitLifecycleResponderReplyReceipt.InterpO.modelReply.toInterp :=
{ keyPair := fun x => [] }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReplyReceipt.kemViewReply

/--
info: def Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstantShape : Tacenta.UnitSatisfiabilityJoint.Interp →
  Prop :=
fun I =>
  ∀ (pa : Std.Array U8 32#usize),
    ∃ sb k pk b, I.dhPrivFromBytes sb = ok k ∧ I.dhPrivPublicKey k = ok pk ∧ I.dhPubAsBytes pk = ok b ∧ b ≠ pa
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstantShape

/--
info: def Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstant : Prop :=
Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstantShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstant
