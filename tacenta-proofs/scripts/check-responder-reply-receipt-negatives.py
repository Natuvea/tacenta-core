#!/usr/bin/env python3
"""Hold the initiator's receipt of the responder's reply against a planted fault.

`Translation/UnitLifecycleResponderReplyReceipt.lean` shows that, on the run in which the responder's `encrypt` at the
session `establish_responder` returned emits the bare reply frame, the initiator's public `Session::decrypt` of those
bytes, at the session its own first `encrypt` left and from the source that `encrypt` left, has the four arms the model
step lists, that under that theorem's own premises it has two (a stale-key refusal exactly when the reply's ratchet key
is the peer key the initiator holds, otherwise the responder's plaintext), and that it returns the responder's
plaintext when the responder's fresh ratchet key is not that peer key.  A proof that Lean accepts after the fact it
rests on is removed would hold nothing, so this script makes one change to a copy of the module and requires Lean to
refuse it, at a named place, with an error that names what the change removed.

Seven controls are labelled inside the proofs that compose the run and four are projections.  A control refused in a
composing theorem is a projection when it is refused where that proof places a conjunct of a called theorem's
conclusion unchanged, and a composition step, labelled inside, otherwise.  The script holds each of the two labels to
a syntactic form of that standard read off the module (`passed_through`: the refusal names a hypothesis the proof
binds by destructuring a called theorem's conclusion, never rewrites, simplifies or substitutes, and places with a
constructor), and requires every control refused in a composing theorem to carry one of them.  For each inside
control it also runs the changed copy with that theorem's proof replaced by `sorry`, requiring Lean to accept the
change there, so the refusal is attributable to that proof.  That probe verifies attribution only: it cannot tell a
composing step from a projection (a corollary's statement-shape check passes it too).  That the syntactic form is the
right standard, and that the three theorems named in `COMPOSING` compose rather than project, is decided by reading.
The labels are also held consistent (an inside control must be labelled with the declaration it is refused in and
with a composing theorem; no control carries two labels; every place a projection may be refused must be a composing
theorem; a statement-shape check may not be refused in a composing theorem, and the theorem it projects must be in
`PROJECTED`), at start-up (at run time the script checks only that each change is refused at its labelled place):

  * inside `initiator_receives_reply_outcomes`: the reply's bytes claimed to carry the peer key the initiator holds
    instead of the fresh ratchet key (refused at the step that closes the bytes equation from the reply's run); the
    refusal on a stale ratchet key claimed to be `Aead` instead of `Triple(Classical(NoReceivingChain))` (refused
    where the model's refusal fixes the code's error); the session after a success claimed to keep the pending
    initial message (refused where the walk of the public `decrypt` fixes what the call writes); the call claimed to
    take no draw (refused where the model step's oracle fixes the draws the call leaves);
  * inside `initiator_receives_reply_two_outcomes`: the plaintext claimed to be the initiator's first plaintext
    instead of the responder's (refused where the open's plaintext is placed); the agreement the relation names
    claimed of the responder's draw instead of the initiator's (refused where the contributory agreement, rewritten
    to the reply's key, is placed);
  * inside `initiator_receives_reply`: the freshness premise claimed against the initiator's own ratchet key instead
    of the peer key it holds (refused where the stale-key arm is excluded);
  * projections: the decrypt claimed from the source before the first send (whose draws that send took) instead of
    the source it left (refused in `initiator_receives_reply_outcomes` where the call conjunct of
    `decrypt_refines_ratchet_frame_of_counter_headroom` is placed unchanged); the stale-key arm claimed on a fresh key
    (refused in `initiator_receives_reply_outcomes` where the key conjunct of the stale arm of
    `reply_receipt_model_outcomes` is placed unchanged); the stale-key arm claimed on a fresh key in the two-outcome
    theorem (refused in `initiator_receives_reply_two_outcomes` where the stale arm of
    `initiator_receives_reply_outcomes` is placed unchanged); the success claimed to take no draw (refused in
    `initiator_receives_reply`, where the draw conjunct of `initiator_receives_reply_two_outcomes` is placed
    unchanged).

Eight are on the leaf lemmas:

  * the model's receive on a fresh key claimed under a premise about the sender's own ratchet key instead of the
    peer key (refused in `reply_receive_key`, which then cannot decide whether to take the Diffie-Hellman step);
  * the stale-key receive claimed to refuse `outOfOrder` (refused in `reply_receive_stale`);
  * the Triple after the reply's receipt claimed with previous chain length 0 instead of 1 (refused in
    `reply_receive_key`, which computes the step from a sender that has sent one message);
  * the joint model's public key made constant again, as in the first receipt's model (refused in
    `modelReply_notConstant`, whose witness key `1` then has the base point as its public key);
  * the responder's fresh private key claimed read by the view as its public key's bytes instead of the draw (refused
    in `fresh_public_of_draw`);
  * the initiator's first agreement claimed equal to the responder's agreement with the peer key instead of the
    initiator's ratchet key (refused in `initiator_reply_agreement`);
  * the model's stale-key outcome claimed to refuse `aead` (refused in `reply_receipt_model_outcomes`);
  * the model session the first send leaves claimed with the agreement at epoch 0 (refused in
    `first_send_model_session`).

One is a statement-shape check: the reach's decrypt claimed at the responder's session instead of the initiator's
(refused in `first_send_reply_receipt_reachable` because its statement no longer matches `reply_receipt_reach_run`;
the script runs it again with that theorem's proof replaced by `sorry` and requires the same refusal, so it is refused
whatever that proof does).  One holds a definition: the model session after the reply's receipt keeping the pending
initial message, the module's pins kept (refused at the pin of `replyReceiptSession`).

Every change is to a statement or a definition; none replaces a proof step.  Each refusal is a proof-breakage check at
a named place: it shows that the proof there depends on what the change removed (or, for the last, that the pin holds
the definition), not that the changed statement is false.

The changes are checked on a copy without the module's pins, so that the refusal comes from a proof and not from a
pin, except the one kept with its pins.  The unmodified copies must be accepted first.  A compiler that does not
start, a syntax error, an unrelated failure and a refusal elsewhere than the named place never count: the named
refusal must be an error at the named place that matches the expected message.  An error whose first line names a
kind of failure that is not a refusal (an unresolved name, a syntax error) voids the run anywhere in the copy,
compared without regard to case.  A timeout (heartbeat or deterministic) never counts as the named refusal; one
elsewhere in the copy is logged in the result and does not void a separate matching error at the named place.  The
script checks at start that the guard fires on the toolchain's own `Unknown identifier`, on the kernel's `unknown
constant`, on a parser's `unexpected token` and `expected '...'`, on `unknown namespace` and on `does not contain`,
each from a sample holding that spelling alone, and not on an ordinary refusal, and that a heartbeat timeout is told
apart from a refusal.  These are controls on copies of the Lean; no source, olean or git state changes.

Dependencies must be built (`lake build Translation.UnitLifecycleResponderReply Translation.UnitLifecycleDecryptT3`).
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / 'translation/Translation/UnitLifecycleResponderReplyReceipt.lean'

OUTCOMES_CALL = ("      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' = ok (res, s'', rngA') ∧\n"
                 "      trace rngA' = restA ∧\n"
                 "      ((res = core.result.Result.Err (lifecycle.Error.Handshake SessionError.NonContributoryAgreement) ∧\n")

OUTCOMES_BYTES = ("      vecOf bytesR = replyFrame oracleB (vecOf q.identityAd) (oracleB.dhPublic dB)\n"
                  "        (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2 (arrayOf q.sparseReceive)) (sliceOf ptR) ∧\n"
                  + OUTCOMES_CALL)

STALE_ERROR = ("        (res = core.result.Result.Err (lifecycle.Error.Triple\n"
               "            (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.NoReceivingChain)) ∧\n")

STALE_KEY = "          oracleB.dhPublic dB = arrayOf q.peerRatchetBytes ∧ s'' = s') ∨\n"

OUTCOMES_WRITES = ("          vecOf ptA = y ∧\n"
                   "          s'' = { s' with\n"
                   "            triple := s''.triple, braid := s''.braid, ratchet_private := s''.ratchet_private,\n"
                   "            pending_initial := none } ∧\n")

TWO_STALE = ("      ((oracleB.dhPublic dB = arrayOf q.peerRatchetBytes ∧\n"
             "          res = core.result.Result.Err (lifecycle.Error.Triple\n")

TWO_OK = "          ∃ ptA : alloc.vec.Vec Std.U8, res = core.result.Result.Ok ptA ∧ ptA.val = ptR.val ∧\n"

TWO_AGREE = ("      (res : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error) (s'' : lifecycle.Session) (rngA' : R),\n"
             "      oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧\n"
             "      oracle.dhAgree dA (oracleB.dhPublic dB) = some x ∧\n")

SUCCESS_TAIL = "      ptA.val = ptR.val ∧ trace rngA' = restA ∧ s''.pending_initial = none ∧\n"

FRESH = "    (hfreshB : oracleB.dhPublic dB ≠ arrayOf q.peerRatchetBytes) :\n"

REACH_CALL = ("      lifecycle.Session.decrypt byteRng byteCrc s' (alloc.vec.Vec.deref bytesR) rng' =\n"
              "        ok (core.result.Result.Ok ptA, s'', rngA') ∧\n")

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
    # in the composing proofs: inside, except the projections in `PROJECTION`
    ('module', 'decrypt-claimed-from-the-source-before-the-first-send',
     [(OUTCOMES_CALL, OUTCOMES_CALL.replace("bytesR) rng' = ok (res", "bytesR) rng = ok (res"))],
     r"hcallA\nhas type\n  lifecycle\.Session\.decrypt rc crc s' bytesR\.deref rng' = ok \(res, s'', rngA'\)\nbut is expected to have type\n  lifecycle\.Session\.decrypt rc crc s' bytesR\.deref rng = ok \(res, s'', rngA'\)", ['initiator_receives_reply_outcomes']),
    ('module', 'reply-claimed-under-the-peer-ratchet-key',
     [(OUTCOMES_BYTES, OUTCOMES_BYTES.replace("(vecOf q.identityAd) (oracleB.dhPublic dB)", "(vecOf q.identityAd) (arrayOf q.peerRatchetBytes)"))],
     r"⊢ replyFrame oracleB \(vecOf q\.identityAd\) \(oracleB\.dhPublic dB\)\n[\s\S]*?=\n    replyFrame oracleB \(vecOf q\.identityAd\) \(arrayOf q\.peerRatchetBytes\)", ['initiator_receives_reply_outcomes']),
    ('module', 'stale-key-refusal-claimed-as-aead',
     [(STALE_ERROR, "        (res = core.result.Result.Err lifecycle.Error.Aead ∧\n")],
     r"⊢ core\.result\.Result\.Err\n      \(lifecycle\.Error\.Triple \(tacenta_triple\.TripleError\.Classical tacenta_ratchet\.RatchetError\.NoReceivingChain\)\) =\n    core\.result\.Result\.Err lifecycle\.Error\.Aead", ['initiator_receives_reply_outcomes']),
    ('module', 'stale-key-arm-claimed-on-a-fresh-key',
     [(STALE_KEY, STALE_KEY.replace("dB = arrayOf q.peerRatchetBytes", "dB ≠ arrayOf q.peerRatchetBytes"))],
     r"hpeer\nhas type\n  oracleB\.dhPublic dB = arrayOf q\.peerRatchetBytes\nbut is expected to have type\n  oracleB\.dhPublic dB ≠ arrayOf q\.peerRatchetBytes", ['initiator_receives_reply_outcomes']),
    ('module', 'success-claimed-to-keep-the-pending-initial-message',
     [(OUTCOMES_WRITES, OUTCOMES_WRITES.replace("pending_initial := none }", "pending_initial := s'.pending_initial }"))],
     r"decrypt_ok_writes rc crc s' bytesR\.deref rng' ptA s'' rngA' hcallA\nhas type\n[\s\S]*?pending_initial := none, [\s\S]*?but is expected to have type\n[\s\S]*?pending_initial := s'\.pending_initial, ", ['initiator_receives_reply_outcomes']),
    ('module', 'decrypt-claimed-to-take-no-draw',
     [(OUTCOMES_CALL, OUTCOMES_CALL.replace("trace rngA' = restA", "trace rngA' = dA :: restA"))],
     r"hdr\nhas type\n  trace \(res, s'', rngA'\)\.2\.2 =\n[\s\S]*?draws := restA,[\s\S]*?but is expected to have type\n  trace rngA' = dA :: restA", ['initiator_receives_reply_outcomes']),
    ('module', 'two-outcome-stale-arm-claimed-on-a-fresh-key',
     [(TWO_STALE, TWO_STALE.replace("dB = arrayOf q.peerRatchetBytes", "dB ≠ arrayOf q.peerRatchetBytes"))],
     r"hpeer\nhas type\n  oracleB\.dhPublic dB = arrayOf q\.peerRatchetBytes\nbut is expected to have type\n  oracleB\.dhPublic dB ≠ arrayOf q\.peerRatchetBytes\nin the application\n  And\.intro hpeer", ['initiator_receives_reply_two_outcomes']),
    ('module', 'plaintext-claimed-to-be-the-first-message',
     [(TWO_OK, TWO_OK.replace("ptA.val = ptR.val", "ptA.val = plaintext.val"))],
     r"hvec\nhas type\n  vecOf ptA = sliceOf ptR\nbut is expected to have type\n  List\.map SessionUnitBraidT3\.u8 ↑ptA = List\.map SessionUnitBraidT3\.u8 ↑plaintext\nin the application\n  UnitLifecycleEstablishResponder\.map_u8_inj hvec", ['initiator_receives_reply_two_outcomes']),
    ('module', 'candidate-agreement-claimed-with-the-responder-draw',
     [(TWO_AGREE, TWO_AGREE.replace("oracle.dhAgree dA (oracleB.dhPublic dB)", "oracle.dhAgree dB (oracleB.dhPublic dB)"))],
     r"hx0\nhas type\n[\s\S]*?\.dhAgree\n      dA \(oracleB\.dhPublic dB\) =\n    some x0\nbut is expected to have type\n  oracle\.dhAgree dB \(oracleB\.dhPublic dB\) = some x0", ['initiator_receives_reply_two_outcomes']),
    ('module', 'fresh-premise-claimed-against-the-initiator-own-key',
     [(FRESH, FRESH.replace("arrayOf q.peerRatchetBytes", "arrayOf q.ratchetBytes"))],
     r"hfreshB\nhas type\n  oracleB\.dhPublic dB ≠ arrayOf q\.ratchetBytes\nbut is expected to have type\n  ¬oracleB\.dhPublic dB = arrayOf q\.peerRatchetBytes\nin the application\n  absurd hpeer hfreshB", ['initiator_receives_reply']),
    # a projection of the two-outcome theorem's draw conjunct, refused in a composing theorem
    ('module', 'success-claimed-without-a-draw',
     [(SUCCESS_TAIL, SUCCESS_TAIL.replace("trace rngA' = restA", "trace rngA' = dA :: restA"))],
     r"hdr\nhas type\n  trace rngA' = restA\nbut is expected to have type\n  trace rngA' = dA :: restA", ['initiator_receives_reply']),
    # leaf lemmas
    ('module', 'fresh-key-receive-claimed-under-the-own-key-premise',
     [("theorem reply_receive_key (a4 peer rkA cksA prk k1 k2 dSend x newPub candPub : Key) (hne : newPub ≠ peer) :\n",
       "theorem reply_receive_key (a4 peer rkA cksA prk k1 k2 dSend x newPub candPub : Key) (hne : newPub ≠ a4) :\n")],
     r"hne : newPub ≠ a4\n⊢ \(match\n      match\n        if peer = newPub then", ['reply_receive_key']),
    ('module', 'stale-key-receive-claimed-to-refuse-out-of-order',
     [("        candPub none = .error (.classical .noReceivingChain) := by\n",
       "        candPub none = .error (.classical .outOfOrder) := by\n")],
     r"error: unsolved goals\na4 peer rkA cksA prk k1 k2 dSend x candPub : Key\n⊢ False", ['reply_receive_stale']),
    ('module', 'reply-receipt-triple-claimed-with-previous-chain-length-zero',
     [("        ns := 0, nr := 1, pn := 1, skipped := [], events := 1, labels := .tacenta }\n",
       "        ns := 0, nr := 1, pn := 0, skipped := [], events := 1, labels := .tacenta }\n")],
     r"error: unsolved goals\na4 peer rkA cksA prk k1 k2 dSend x newPub candPub : Key\nhne : newPub ≠ peer\n⊢ False", ['reply_receive_key']),
    ('module', 'joint-model-public-key-made-constant',
     [("    dhPrivPublicKey := fun k => ok (replyPub k)\n",
       "    dhPrivPublicKey := fun _ => ok Tacenta.UnitLifecycleEstablishResponder.basePoint\n")],
     r"replyPub_oneKey\nhas type\n  replyPub UnitLifecycleEstablishedDecrypt\.oneKey = UnitLifecycleEstablishedDecrypt\.oneKey\nbut is expected to have type\n  UnitLifecycleEstablishResponder\.basePoint = UnitLifecycleEstablishedDecrypt\.oneKey", ['modelReply_notConstant']),
    ('module', 'fresh-private-key-claimed-read-as-its-public-bytes',
     [("      arrayOf value = dB ∧ tacenta_boundary.dh.PrivateKey.from_bytes value = ok k ∧ dh.privateKey k = dB ∧\n",
       "      arrayOf value = dB ∧ tacenta_boundary.dh.PrivateKey.from_bytes value = ok k ∧ dh.privateKey k = arrayOf b ∧\n")],
     r"hval\nhas type\n  arrayOf value = dB\nbut is expected to have type\n  arrayOf value = arrayOf b\nin the application\n  Eq\.trans hkv hval", ['fresh_public_of_draw']),
    ('module', 'first-agreement-claimed-with-the-peer-key',
     [("      oracleB.dhAgree (dh.privateKey k) (arrayOf q.ratchetBytes) := by\n",
       "      oracleB.dhAgree (dh.privateKey k) (arrayOf q.peerRatchetBytes) := by\n")],
     r"Did not find an occurrence of the pattern\n  arrayOf q\.ratchetBytes\nin the target expression\n  Option\.map arrayOf ra = oracleB\.dhAgree \(dh\.privateKey k\) \(arrayOf q\.peerRatchetBytes\)", ['initiator_reply_agreement']),
    ('module', 'model-stale-key-outcome-claimed-as-aead',
     [("        { session := mA, result := .error (Model.Lifecycle.tripleReceiveRefusalOf (.classical .noReceivingChain)),\n",
       "        { session := mA, result := .error .aead,\n")],
     r"match Except\.error \(Model\.Triple\.ReceiveRefusal\.classical Model\.Ratchet\.ReceiveRefusal\.noReceivingChain\) with[\s\S]*?\{ session := mA, result := Except\.error Model\.Lifecycle\.Refusal\.aead", ['reply_receipt_model_outcomes']),
    ('module', 'first-send-model-session-claimed-at-epoch-zero',
     [("          braid := .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector encoder } := by\n",
       "          braid := .keysSampled 0 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector encoder } := by\n")],
     r"hsess\nhas type\n[\s\S]*?braid := Model\.Braid\.BraidState\.keysSampled 1 \(SessionUnitBraidT3\.AuthOf q\.auth\) dk ekVector encoder,[\s\S]*?but is expected to have type\n[\s\S]*?braid := Model\.Braid\.BraidState\.keysSampled 0 \(SessionUnitBraidT3\.AuthOf q\.auth\) dk ekVector encoder,", ['first_send_model_session']),
    # statement-shape check (projects `reply_receipt_reach_run`)
    ('module', 'reach-decrypt-claimed-at-the-responder-session',
     [(REACH_CALL, REACH_CALL.replace("byteCrc s' (alloc", "byteCrc sB' (alloc"))],
     r"hcallA\nhas type\n  lifecycle\.Session\.decrypt byteRng byteCrc s' bytesR\.deref rng' = ok \(core\.result\.Result\.Ok ptA, s'', rngA'\)\nbut is expected to have type\n  lifecycle\.Session\.decrypt byteRng byteCrc sB' bytesR\.deref rng' = ok \(core\.result\.Result\.Ok ptA, s'', rngA'\)", ['first_send_reply_receipt_reachable']),
    # the definition, with the pins kept
    ('pinned', 'reply-receipt-session-keeping-the-pending-initial-message-pinned',
     [("    pendingInitial := none }\n", "    pendingInitial := mA.pendingInitial }\n")],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession')),
]

COMPOSING = {
    'initiator_receives_reply_outcomes',
    'initiator_receives_reply_two_outcomes',
    'initiator_receives_reply',
}

# The controls labelled inside a composing proof, with the declaration each is refused in.  For each, the script also
# runs the changed copy with that theorem's proof replaced by `sorry` and requires Lean to accept the change there:
# the refusal is attributable to that proof.
INSIDE = {
    'reply-claimed-under-the-peer-ratchet-key': 'initiator_receives_reply_outcomes',
    'stale-key-refusal-claimed-as-aead': 'initiator_receives_reply_outcomes',
    'success-claimed-to-keep-the-pending-initial-message': 'initiator_receives_reply_outcomes',
    'decrypt-claimed-to-take-no-draw': 'initiator_receives_reply_outcomes',
    'plaintext-claimed-to-be-the-first-message': 'initiator_receives_reply_two_outcomes',
    'candidate-agreement-claimed-with-the-responder-draw': 'initiator_receives_reply_two_outcomes',
    'fresh-premise-claimed-against-the-initiator-own-key': 'initiator_receives_reply',
}

# The controls refused in a composing proof where it places a conjunct of a called theorem's conclusion unchanged,
# with that called theorem: projections, labelled neither inside nor statement-shape and not probed.  Every other
# control refused in a composing proof must be labelled inside; `check_labels` holds both labels to the syntactic
# form of that standard (`passed_through`).
PROJECTION = {
    'decrypt-claimed-from-the-source-before-the-first-send': 'decrypt_refines_ratchet_frame_of_counter_headroom',
    'stale-key-arm-claimed-on-a-fresh-key': 'reply_receipt_model_outcomes',
    'two-outcome-stale-arm-claimed-on-a-fresh-key': 'initiator_receives_reply_outcomes',
    'success-claimed-without-a-draw': 'initiator_receives_reply_two_outcomes',
}

# The theorems a statement-shape check may project: the composing theorems and the reach run the two reaches apply.
PROJECTED = COMPOSING | {'reply_receipt_reach_run'}

# The statement-shape checks, with the theorem each projects.  For each, the script also runs the changed copy with
# that theorem's proof replaced by `sorry` and requires Lean still to refuse the change at its named place: the
# refusal does not depend on the projected theorem's proof.
STATEMENT_SHAPE = {
    'reach-decrypt-claimed-at-the-responder-session': 'reply_receipt_reach_run',
}


BINDER = re.compile(r'\s*(?:· )?(obtain|rcases|have)\b')
PLACING = frozenset({'And.intro', 'Or.inl', 'Or.inr', 'Exists.intro'})


def mentions(name):
    return re.compile(r'(?<![\w.\'])' + re.escape(name) + r'(?![\w\'])')


def binding(lines, name):
    """The tactic of `lines` that binds `name` at its first mention, as (source, end), where `source` is the term the
    tactic destructures (`obtain pattern := source`, `rcases source with pattern`, `have name := source`) and `end` the
    index of the line after the tactic; None when the first mention is not in such a tactic's pattern."""
    word = mentions(name)
    first = next((k for k, line in enumerate(lines) if word.search(line)), None)
    if first is None:
        return None
    j = first
    while j >= 0 and not BINDER.match(lines[j]):
        j -= 1
    if j < 0:
        return None
    indent = len(lines[j]) - len(lines[j].lstrip())
    end = j + 1
    while end < len(lines) and (not lines[end].strip() or len(lines[end]) - len(lines[end].lstrip()) > indent):
        end += 1
    if first >= end:
        return None
    tactic = ' '.join(line.strip() for line in lines[j:end])
    if BINDER.match(lines[j]).group(1) == 'rcases':
        m = re.match(r'(?:· )?rcases (.*?) with (.*)$', tactic)
        if not m:
            return None
        source, pattern = m.group(1), m.group(2)
    else:
        pattern, sep, source = tactic.partition(':=')
        if not sep:
            return None
    if not word.search(pattern):
        return None
    return source.strip(), end


def called_theorem(lines, premises, name):
    """The called theorem whose conclusion the proof `lines` destructures to bind `name`, directly or through local
    hypotheses bound the same way, with the index of the line after the binding tactic; None when `name` is a premise
    or is bound otherwise (a tactic block, a field of a premise)."""
    found = binding(lines, name)
    if found is None:
        return None
    source, end = found
    m = re.match(r'@?([\w.\']+)', source)
    if not m or m.group(1) == 'by':
        return None
    head = m.group(1)
    local = head.split('.')[0]
    if local in premises:
        return None
    start = next(k for k, line in enumerate(lines) if mentions(name).search(line))
    if binding(lines[:start], local) is not None:
        inner = called_theorem(lines[:start], premises, local)
        return None if inner is None else (inner[0], end)
    return head.split('.')[-1], end


def passed_through(text, decl, marker):
    """The called theorem a conjunct of whose conclusion the composing proof `decl` places unchanged where the refusal
    `marker` is, or None.  A syntactic form of the projection standard: the refusal names a hypothesis (`h\\nhas type`)
    that the proof binds by destructuring a called theorem's conclusion, that no later tactic rewrites, simplifies or
    substitutes (`at ... h`, `subst h`), and that the message places with a constructor or in no named application.
    Any other refusal in a composing proof is read as a composition step."""
    m = re.match(r'([\w\']+)\\nhas type', marker)
    if not m:
        return None
    app = re.search(r'in the application\\n  ([\w\\.\']+)', marker)
    if app and app.group(1).replace('\\', '') not in PLACING:
        return None
    span = declaration_lines(text, decl)
    if span is None:
        return None
    lines = text.split('\n')[span[0] - 1:span[1]]
    start = next((k for k, line in enumerate(lines) if line.rstrip().endswith(':= by')), None)
    if start is None:
        return None
    signature, proof = '\n'.join(lines[:start + 1]), lines[start + 1:]
    premises = {n for group in re.findall(r'[({\[]([^(){}\[\]:]*?) :', signature) for n in group.split()}
    found = called_theorem(proof, premises, m.group(1))
    if found is None:
        return None
    called, end = found
    word = re.escape(m.group(1)) + r'(?![\w\'])'
    for line in proof[end:]:
        if re.search(r'\b(?:at|subst)\b[^\n]*(?<![\w.\'])' + word, line):
            return None
    return called


def check_labels(text):
    """The inside, projection and statement-shape labels are consistent with each other, with where each control is
    refused, and, for the controls refused in a composing proof, with the syntactic form of the projection standard
    (`passed_through`) read off `text`, the module without its pins."""
    wheres = {name: where for _, name, _, _, where in MUTANTS}
    markers = {name: marker for _, name, _, marker, _ in MUTANTS}
    for name, _ in list(INSIDE.items()) + list(PROJECTION.items()) + list(STATEMENT_SHAPE.items()):
        if name not in wheres:
            raise SystemExit(f'LABELS BROKEN: {name} is labelled but is not a control')
    for first, second, kinds in ((INSIDE, STATEMENT_SHAPE, 'inside and statement-shape'),
                                 (INSIDE, PROJECTION, 'inside and projection'),
                                 (PROJECTION, STATEMENT_SHAPE, 'projection and statement-shape')):
        both = set(first) & set(second)
        if both:
            raise SystemExit(f'LABELS BROKEN: {", ".join(sorted(both))} labelled both {kinds}')
    for name, decl in INSIDE.items():
        if isinstance(wheres[name], tuple) or decl not in wheres[name]:
            raise SystemExit(f'LABELS BROKEN: {name} is labelled inside {decl}, which is not where it is refused')
        if decl not in COMPOSING:
            raise SystemExit(f'LABELS BROKEN: {name} is labelled inside {decl}, which is not a composing proof')
        called = passed_through(text, decl, markers[name])
        if called is not None:
            raise SystemExit(f'LABELS BROKEN: {name} is labelled inside {decl}, but is refused where {decl} places a '
                             f'conjunct of {called} unchanged, a projection')
    # Every place a projection is refused must be a composing proof that places the conjunct unchanged: a refusal
    # list that also names a leaf or another declaration would let the control be refused there instead.
    for name, called in PROJECTION.items():
        places = [] if isinstance(wheres[name], tuple) else list(wheres[name])
        if not places:
            raise SystemExit(f'LABELS BROKEN: {name} is labelled a projection but is not refused in a composing proof')
        others = [d for d in places if d not in COMPOSING]
        if others:
            raise SystemExit(f'LABELS BROKEN: {name} is labelled a projection, but it may be refused in '
                             f'{", ".join(others)}, which is not a composing proof')
        for place in places:
            if passed_through(text, place, markers[name]) != called:
                raise SystemExit(f'LABELS BROKEN: {name} is labelled a projection of {called}, but is not refused '
                                 f'where {place} places a conjunct of {called} unchanged')
    for name, decl in STATEMENT_SHAPE.items():
        if isinstance(wheres[name], tuple) or any(d in COMPOSING for d in wheres[name]):
            raise SystemExit(f'LABELS BROKEN: the statement-shape check {name} is refused in a composing proof')
        if decl not in PROJECTED:
            raise SystemExit(f'LABELS BROKEN: the statement-shape check {name} projects {decl}, which is not in '
                             f'PROJECTED')
    for name, where in wheres.items():
        if not isinstance(where, tuple) and any(d in COMPOSING for d in where) and name not in INSIDE \
                and name not in PROJECTION:
            raise SystemExit(f'LABELS BROKEN: {name} is refused in a composing proof but labelled neither inside nor '
                             f'a projection')

NOT_A_REFUSAL = ('unknown identifier', 'unknown constant', 'unexpected token', "expected '",
                 'unknown namespace', 'does not contain')

# A timeout (a heartbeat or deterministic timeout) is never a refusal: it never counts as the named refusal, and one
# elsewhere in the copy is logged.  It does not void a run whose named refusal is a separate error at the named place
# that matches the expected message.
TIMEOUT = ('timeout', 'maxheartbeats', 'heartbeats', 'deterministic')


# Lean capitalises its error messages (`Unknown identifier`, `Unknown constant`, `Function expected`), so the
# guard is matched case-insensitively, on the first line of each error, where Lean names the kind of failure.
ERROR_HEAD = re.compile(r'^\S+\.lean:\d+:\d+: error(?:\([^)]*\))?: (.*)$', re.M)
MESSAGE = re.compile(r'^\S+\.lean:(\d+):\d+: (error|warning|info|information)(?:\([^)]*\))?: (.*)$', re.M)


def not_a_refusal(output, guards):
    """Whether an error of `output` is of a kind that is not a refusal (a name that does not resolve, a syntax
    error, ...), compared without regard to case."""
    heads = [head.lower() for head in ERROR_HEAD.findall(output)]
    return any(bad in head for head in heads for bad in guards)


def error_blocks(output):
    """Each error of `output` as (line, first line, whole text)."""
    found = list(MESSAGE.finditer(output))
    blocks = []
    for k, m in enumerate(found):
        end = found[k + 1].start() if k + 1 < len(found) else len(output)
        if m.group(2) == 'error':
            blocks.append((int(m.group(1)), m.group(3), output[m.start():end]))
    return blocks


def is_timeout(head):
    return any(t in head.lower() for t in TIMEOUT)


def guard_self_test(guards):
    """The guard must fire on the toolchain's own spelling of an unresolved name, on each parser and namespace
    spelling it lists, each from a sample holding that spelling alone, and a timeout must be told apart from a
    refusal."""
    sample = ("/tmp/x.lean:3:8: error(lean.unknownIdentifier): Unknown identifier `fooBar`\n"
              "/tmp/x.lean:4:2: error: unsolved goals\n")
    if not not_a_refusal(sample, guards):
        raise SystemExit('GUARD BROKEN: the not-a-refusal guard does not fire on `Unknown identifier`')
    kernel = ("/tmp/x.lean:5:8: error: (kernel) unknown constant 'Foo.bar'\n"
              "/tmp/x.lean:6:2: error: unsolved goals\n")
    if not not_a_refusal(kernel, guards):
        raise SystemExit('GUARD BROKEN: the not-a-refusal guard does not fire on the kernel\'s `unknown constant`')
    # every spelling the guard is meant to list, fixed here so that a spelling dropped from the guard is caught
    spellings = ('unknown identifier', 'unknown constant', 'unexpected token', "expected '", 'unknown namespace',
                 'does not contain')
    for spelling, line in (
            ('unexpected token', "/tmp/x.lean:8:4: error: unexpected token 'at'; expected term\n"),
            ("expected '", "/tmp/x.lean:9:0: error: unexpected end of input; expected ':='\n"),
            ('unknown namespace', "/tmp/x.lean:2:5: error: unknown namespace 'Foo.Bar'\n"),
            ('does not contain', "/tmp/x.lean:3:6: error: invalid field 'baz', the environment does not contain "
                                 "'Foo.baz'\n")):
        sample_one = line + "/tmp/x.lean:10:2: error: unsolved goals\n"
        if spelling not in line.lower() or sum(other in line.lower() for other in spellings) != 1:
            raise SystemExit(f'GUARD BROKEN: the self-test sample for `{spelling}` does not hold that spelling alone')
        if not not_a_refusal(sample_one, guards):
            raise SystemExit(f'GUARD BROKEN: the not-a-refusal guard does not fire on `{spelling}`')
    if not_a_refusal("/tmp/x.lean:4:2: error: unsolved goals\n", guards):
        raise SystemExit('GUARD BROKEN: the not-a-refusal guard fires on an ordinary refusal')
    timeout = ("/tmp/x.lean:7:2: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) "
               "has been reached\nUse `set_option maxHeartbeats <num>` to set the limit.\n")
    blocks = error_blocks(timeout)
    if len(blocks) != 1 or not is_timeout(blocks[0][1]):
        raise SystemExit('GUARD BROKEN: a heartbeat timeout is not recognised as a timeout')
    if any(is_timeout(h) for _, h, _ in error_blocks("/tmp/x.lean:4:2: error: unsolved goals\nx : T\n")):
        raise SystemExit('GUARD BROKEN: an ordinary refusal is taken for a timeout')


# Every Lean run this script made, as (file name, exit status), appended by `run_lean` alone; `check_complete`
# counts the runs from here, not from what `main` reports.
RUNS = []


def run_lean(path, log, timeout):
    with log.open('w') as output:
        try:
            process = subprocess.Popen(
                ['lake', 'env', 'lean', str(path)], cwd=ROOT / 'translation',
                stdout=output, stderr=subprocess.STDOUT, start_new_session=True,
            )
        except OSError as error:
            raise SystemExit(f'COMPILER LAUNCH FAILED (not a passing control): {error}')
        try:
            status = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            process.wait()
            raise SystemExit(f'TIMEOUT (not a passing control): {path.name}; see {log}')
    RUNS.append((path.name, status))
    return status, log.read_text()


def without_pins(text, path):
    cut = text.find('\n/-! ## Pins')
    if cut < 0:
        raise SystemExit(f'no pin section found in {path.name}')
    return text[:cut] + '\n'


DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*'
                  r'(theorem|lemma|def|abbrev|structure|instance|inductive)\s+(\S+)')
COMMAND = re.compile(r'^(?:@\[|/--|/-!|#|theorem |lemma |def |abbrev |structure |instance |'
                     r'inductive |private |protected |noncomputable |set_option |attribute |open |'
                     r'namespace |section |end |variable )')


def declaration_lines(text, name):
    """The 1-based line range of the declaration `name` in `text` (its leading `set_option ... in`
    and doc comment excluded), or None."""
    lines = text.split('\n')
    for k, line in enumerate(lines):
        m = DECL.match(line)
        if m and (m.group(2) == name or m.group(2).endswith('.' + name)):
            end = k + 1
            while end < len(lines) and not COMMAND.match(lines[end]):
                end += 1
            return k + 1, end
    return None


def pin_line(text, name):
    """The 1-based line of the `#guard_msgs in` that precedes `#print name`, or None."""
    lines = text.split('\n')
    for k in range(1, len(lines)):
        if lines[k] == f'#print {name}' and lines[k - 1].startswith('#guard_msgs'):
            return k
    return None


ERROR_AT = re.compile(r'^\S+\.lean:(\d+):\d+: error', re.M)


def gutted(text, name):
    """`text` with the proof of the theorem `name` (from the line after its `:= by` to the next command)
    replaced by `sorry`."""
    span = declaration_lines(text, name)
    if span is None:
        raise SystemExit(f'no declaration {name} to empty')
    lines = text.split('\n')
    start = next((k for k in range(span[0] - 1, span[1]) if lines[k].rstrip().endswith(':= by')), None)
    if start is None:
        raise SystemExit(f'no tactic proof found in {name}')
    end = start + 1
    while end < len(lines) and not COMMAND.match(lines[end]):
        end += 1
    return '\n'.join(lines[:start + 1] + ['  sorry'] + lines[end:])


def check_inside(name, decl, status, output, log, emptied):
    """With the composing proof emptied, the change must not be refused there."""
    if 'declaration uses `sorry`' not in output:
        raise SystemExit(f'FAILED inside check {name}: the emptied copy did not elaborate to `sorry`; {log}')
    span = declaration_lines(emptied, decl)
    errors = {int(n) for n in ERROR_AT.findall(output)}
    if any(span[0] <= e <= span[1] for e in errors):
        raise SystemExit(f'FAILED inside check {name}: still refused in {decl} with its proof emptied, so the '
                         f'refusal is not the proof\'s; {log}')


def check_refused(name, status, output, marker, log, mutated, where):
    """Refused at the named place, by an error there that is not a timeout and that matches the expected message;
    an error that is not a refusal voids the run anywhere in the copy; a timeout elsewhere is returned for the log."""
    if status == 0 or not_a_refusal(output, NOT_A_REFUSAL):
        raise SystemExit(f'FAILED control {name}: expected Lean to refuse it with `{marker}`, '
                         f'exit={status}; {log}')
    blocks = error_blocks(output)
    if isinstance(where, tuple):
        line = pin_line(mutated, where[1])
        if line is None:
            raise SystemExit(f'FAILED control {name}: the copy has no `#print {where[1]}` pin, so '
                             f'its refusal cannot be the pin\'s; {log}')
        spans = [(where[1], (line, line))]
    else:
        spans = []
        for decl in where:
            span = declaration_lines(mutated, decl)
            if span is None:
                raise SystemExit(f'Target changed for {name}: no declaration {decl} in the copy')
            spans.append((decl, span))
    for decl, (lo, hi) in spans:
        if any(lo <= ln <= hi and not is_timeout(head) and re.search(marker, text) for ln, head, text in blocks):
            place = decl if not isinstance(where, tuple) else f'the pin of {where[1]}'
            timeouts = sorted(ln for ln, head, _ in blocks if is_timeout(head))
            return place, timeouts
    raise SystemExit(f'FAILED control {name}: no error at the named place ({", ".join(d for d, _ in spans)}) that is '
                     f'not a timeout matches `{marker}`; {log}')


def check_complete(results, sources):
    """The run ran what the script holds: every unmodified copy accepted, in order; every control in `MUTANTS` refused
    once; the emptied-proof run of every inside control and of every statement-shape check, and the place of every
    projection, recorded; and Lean run, by `run_lean`, once for each of those runs, at least once accepting per
    baseline and once refusing per control and statement-shape check (`RUNS`, which `main` does not write; an
    inside control's emptied run may exit either way, since only its own declaration must be accepted).  A control skipped by a slice of
    `MUTANTS` or a `continue`, a baseline left out, or results written without running Lean fails the script here
    instead of leaving a smaller run that passes.  It does not see Lean run on files other than the controls.
    `check-negatives-control-counts.py` requires `main` to call this, and the number of controls to match its
    record."""
    rejected = {key.split('/', 1)[1]: r for key, r in results['rejected'].items()}
    problems = []
    if results['accepted'] != list(sources):
        problems.append(f'unmodified copies accepted {results["accepted"]}, expected {list(sources)}')
    if len(results['rejected']) != len(MUTANTS) or sorted(rejected) != sorted(m[1] for m in MUTANTS):
        problems.append(f'{len(results["rejected"])} controls refused, expected the {len(MUTANTS)} in MUTANTS; not run: '
                        f'{sorted(set(m[1] for m in MUTANTS) - set(rejected))}')
    if sorted(n for n, r in rejected.items() if 'inside' in r) != sorted(INSIDE):
        problems.append('the emptied-proof run of an inside control is missing')
    if sorted(n for n, r in rejected.items() if 'projects' in r) != sorted(STATEMENT_SHAPE):
        problems.append('the emptied-proof run of a statement-shape check is missing')
    if sorted(n for n, r in rejected.items() if 'projection_of' in r) != sorted(PROJECTION):
        problems.append('the place of a projection is not recorded')
    accepting = sum(1 for _, status in RUNS if status == 0)
    refusing = len(RUNS) - accepting
    runs = len(sources) + len(MUTANTS) + len(INSIDE) + len(STATEMENT_SHAPE)
    if len(RUNS) != runs or accepting < len(sources) or refusing < len(MUTANTS) + len(STATEMENT_SHAPE):
        problems.append(f'Lean ran {accepting} accepting and {refusing} refusing times, expected {runs} runs, at least '
                        f'{len(sources)} accepting and {len(MUTANTS) + len(STATEMENT_SHAPE)} refusing')
    if problems:
        raise SystemExit('INCOMPLETE RUN (not a passing control): ' + '; '.join(problems))

def main():
    guard_self_test(NOT_A_REFUSAL)
    check_labels(without_pins(MODULE.read_text(), MODULE))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=900)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='responder-reply-receipt-logs-'))
    logs.mkdir(parents=True, exist_ok=True)
    module = MODULE.read_text()
    sources = {
        'module': without_pins(module, MODULE),
        'pinned': module,
    }
    results = {
        'module_sha256': hashlib.sha256(module.encode()).hexdigest(),
        'accepted': [], 'rejected': {},
    }
    with tempfile.TemporaryDirectory(prefix='responder-reply-receipt-controls-') as tmp:
        tmp = Path(tmp)
        for label, text in sources.items():
            path = tmp / f'baseline_{label}.lean'
            path.write_text(text)
            status, output = run_lean(path, logs / f'baseline_{label}.log', args.timeout)
            if status or 'sorry' in output or 'error' in output:
                raise SystemExit(f'BASELINE FAILED for the {label} copy; no mutation evidence: '
                                 f'{logs / f"baseline_{label}.log"}')
            results['accepted'].append(label)
            print(f'PASS: the unmodified {label} copy is accepted', flush=True)
        for label, name, edits, marker, where in MUTANTS:
            source = sources[label]
            mutated = source
            for old, new in edits:
                found = mutated.count(old)
                if found != 1:
                    raise SystemExit(f'Target changed for {name}: expected 1 occurrence of the '
                                     f'text in the {label} copy, found {found}')
                mutated = mutated.replace(old, new, 1)
            assert mutated != source
            path = tmp / f'{label}_{name}.lean'
            path.write_text(mutated)
            log = logs / f'{label}_{name}.log'
            status, output = run_lean(path, log, args.timeout)
            place, timeouts = check_refused(name, status, output, marker, log, mutated, where)
            results['rejected'][f'{label}/{name}'] = {'exit': status, 'marker': marker, 'at': place}
            if timeouts:
                results['rejected'][f'{label}/{name}']['timeouts_elsewhere'] = timeouts
                print(f'NOTE: {label}/{name} also has a timeout at line(s) {timeouts}, not counted', flush=True)
            print(f'PASS: {label}/{name} refused by Lean in {place}', flush=True)
            if name in INSIDE:
                decl = INSIDE[name]
                if place != decl:
                    raise SystemExit(f'FAILED inside check {name}: refused in {place}, labelled inside {decl}; {log}')
                emptied = gutted(mutated, decl)
                epath = tmp / f'{label}_{name}_emptied.lean'
                epath.write_text(emptied)
                elog = logs / f'{label}_{name}_emptied.log'
                status, output = run_lean(epath, elog, args.timeout)
                check_inside(name, decl, status, output, elog, emptied)
                results['rejected'][f'{label}/{name}']['inside'] = decl
                print(f'PASS: {label}/{name} accepted in {decl} with its proof emptied', flush=True)
            if name in PROJECTION:
                places = [d for d in where if d in COMPOSING]
                if place != places[0]:
                    raise SystemExit(f'FAILED projection check {name}: refused in {place}, labelled a projection in '
                                     f'{places[0]}; {log}')
                results['rejected'][f'{label}/{name}']['projection_of'] = PROJECTION[name]
            if name in STATEMENT_SHAPE:
                decl = STATEMENT_SHAPE[name]
                emptied = gutted(mutated, decl)
                epath = tmp / f'{label}_{name}_projected_emptied.lean'
                epath.write_text(emptied)
                elog = logs / f'{label}_{name}_projected_emptied.log'
                status, output = run_lean(epath, elog, args.timeout)
                check_refused(name, status, output, marker, elog, emptied, where)
                results['rejected'][f'{label}/{name}']['projects'] = decl
                print(f'PASS: {label}/{name} still refused with the proof of {decl} emptied', flush=True)
    check_complete(results, sources)
    (logs / 'result.json').write_text(json.dumps(results, indent=2) + '\n')
    inside = sum(1 for r in results['rejected'].values() if 'inside' in r)
    shape = sum(1 for r in results['rejected'].values() if 'projects' in r)
    projection = sum(1 for r in results['rejected'].values() if 'projection_of' in r)
    print(f'{len(results["accepted"])} unmodified copies accepted, {len(results["rejected"])} changes '
          f'refused at their named places, {inside} of them labelled inside a composing proof (accepted there with '
          f'that proof emptied), {projection} labelled projections and {shape} labelled statement-shape (still refused with the projected proof '
          f'emptied); logs: {logs}', flush=True)


if __name__ == '__main__':
    sys.exit(main())
