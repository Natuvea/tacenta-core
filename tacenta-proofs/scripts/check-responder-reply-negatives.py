#!/usr/bin/env python3
"""Hold the responder's reply against a planted fault.

`Translation/UnitLifecycleResponderReply.lean` shows that, on the run in which `establish_responder` accepts the bytes
the initiator's first `encrypt` emitted and returns the session `sB'`, the responder's `Session::encrypt` at that same
`sB'` returns the bare reply frame, takes no draw, keeps the agreement and relates to the model's step.  A proof that
Lean accepts after the fact it rests on is removed would hold nothing, so this script makes one change to a copy of the
module and requires Lean to refuse it, at a named place, with an error that names what the change removed.

Seven controls are labelled inside the proofs that compose the run, and none is a projection.  A control refused in a
composing theorem is a projection when it is refused where that proof places a conjunct of a called theorem's
conclusion unchanged, and a composition step, labelled inside, otherwise.  The script holds each label to a syntactic
form of that standard read off the module (`passed_through`: the refusal names a hypothesis the proof binds by
destructuring a called theorem's conclusion, never rewrites, simplifies or substitutes, and places with a
constructor), and requires every control refused in a composing theorem to carry the inside or the projection label;
each of the seven is refused at a goal the proof closes, at an argument it passes, or at a hypothesis it has
rewritten.  For each inside control it also runs the changed copy with that theorem's proof replaced by `sorry`,
requiring Lean to accept the change there, so the refusal is attributable to that proof.  That probe verifies
attribution only: it cannot tell a composing step from a projection (a corollary's statement-shape check passes it
too).  That the syntactic form is the right standard, and that the three theorems named in `COMPOSING` compose rather
than project, is decided by reading.  The labels are also held consistent (an inside control must be labelled with
the declaration it is refused in and with a composing theorem; no control carries two labels; a statement-shape check
may not be refused in a composing theorem, and the theorem it projects must be in `PROJECTED`), at start-up
(at run time the script checks only that each change is refused at its labelled place):

  * in `initiator_first_send_responder_replies`: the call claimed to return the source `establish_responder` left
    (`rngB'`, the receipt's draw taken) instead of the source it was given (refused where the walk has fixed the
    returned source); the reply claimed to be wrapped as an initial message, the reply claimed sealed under the key
    of the sparse chain `k1` the responder receives on instead of `k2`, and the reply claimed to carry the responder's
    prepared ratchet key (its signed prekey's) instead of the fresh one (all three refused at the step that closes the
    bytes equation from the model's computed step); the session after the call claimed related to the model session
    after the receipt with its Triple unchanged (refused where the model's step fixes the Triple after the send);
  * in `responder_first_frame_successor_keys`: the root-key equation claimed with the initiator's sparse root instead
    of its classical root (refused where the receipt's derived equation is placed);
  * in `initiator_first_send_responder_successor_keys`: the receipt's call taken on the plaintext instead of the bytes
    the first send returned (refused at the step where the encrypt's output fixes the message).

Seven are on the leaf lemmas:

  * the agreement's send claimed to emit a header message at `NoHeaderReceived` (refused in `braid_send_noHeader`);
  * the counted draw record claimed at a model state that draws (`headerReceived`; refused in
    `braidSendTraceCounted_of_noHeader`, whose draw clauses are then not vacuous);
  * the reply's Triple header claimed with sparse number 0 (refused in `reply_send_key`);
  * the agreement's send at `noHeaderReceived` claimed to output an epoch key (refused in
    `sendAgreement_noHeader_output`, which computes the model's send there; the providers' `newBound` rests on it);
  * the headroom record claimed from a plaintext bound without the 102 bytes of header room (refused in
    `encryptHeadroom_reply`);
  * the reply's composite header claimed with agreement type `hdr` (refused in `reply_model_step`);
  * the model step claimed without the premise that the model session has no pending initial message (refused in
    `reply_model_step`, which then cannot decide whether the frame is wrapped).

One is a statement-shape check: the reach's call claimed to leave the byte-stream source `seed` (refused in
`first_send_reply_reachable` because its statement no longer matches `initiator_first_send_responder_replies`; the
script runs it again with that theorem's proof replaced by `sorry` and requires the same refusal, so it is refused
whatever that proof does).  One holds a definition: the reply frame without the session's
associated data, the module's pins kept (refused at the pin of `replyFrame`).

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

Dependencies must be built (`lake build Translation.UnitLifecycleResponderSuccessor`).
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
MODULE = ROOT / 'translation/Translation/UnitLifecycleResponderReply.lean'

REPLY_CALL = ("      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧\n")

REPLY_BYTES = ("      vecOf bytesR = replyFrame oracleB (vecOf q.identityAd) (oracleB.dhPublic dB)\n"
               "        (replyKey (arrayOf ec) (arrayOf q.sparseReceive) (arrayOf q.dhOut) dSend) (sliceOf ptR) ∧\n")

REPLY_RELATION = ("      SessionRefines dh oracleB.braidKem sB''\n"
                  "        { firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret)\n"
                  "            ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩\n"
                  "            (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)\n"
                  "            (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB with\n"
                  "          triple := replierAfterSend (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend)\n"
                  "            (arrayOf q.sparseReceive) (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) } := by\n")

REPLY_RELATION_UNCHANGED = ("      SessionRefines dh oracleB.braidKem sB''\n"
                            "        (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret)\n"
                            "            ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩\n"
                            "            (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)\n"
                            "            (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) := by\n")

KEYS_ROOT = ("      Model.State.kdfRk (arrayOf ec) (arrayOf q.dhOut) .tacenta = (arrayOf q.rootKey, arrayOf q.sendChain) ∧\n"
             "      oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧\n"
             "      p.identityAd = q.identityAd ∧\n"
             "      SessionRefines dh oracleB.braidKem sB'\n"
             "        (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)\n")

KEYS_CALL = ("    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =\n"
             "      ok (core.result.Result.Ok (sB', ptB), storeB', rngB')) :\n"
             "    ∃ (p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes)) (ec : Array U8 32#usize)\n"
             "      (dSend : Model.Lifecycle.Key) (dk ekSeed ekVector : Model.Braid.Bytes),\n")

REACH_CALL = ("      lifecycle.Session.encrypt byteRng byteCrc sB' emptyPlaintext rngB' =\n"
              "        ok (core.result.Result.Ok bytesR, sB'', rngB') ∧\n")

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
    # inside the composing proofs
    ('module', 'reply-claimed-to-return-the-receipt-source',
     [(REPLY_CALL, REPLY_CALL.replace("sB'', rngR) ∧", "sB'', rngB') ∧"))],
     r"hcallR\nhas type\n  lifecycle\.Session\.encrypt rcB crcB sB' ptR rngR' = ok \(core\.result\.Result\.Ok bytesR, sB'', rngR'\)\nbut is expected to have type\n  lifecycle\.Session\.encrypt rcB crcB sB' ptR rngR' = ok \(core\.result\.Result\.Ok bytesR, sB'', rngB'\)", ['initiator_first_send_responder_replies']),
    ('module', 'reply-claimed-wrapped-as-an-initial-message',
     [(REPLY_BYTES, REPLY_BYTES.replace(
         "vecOf bytesR = replyFrame oracleB",
         "vecOf bytesR = Model.Messages.encodeInitial (vecOf q.identityAd) [] [] 0 0 0 (replyFrame oracleB").replace(
         "(sliceOf ptR) ∧", "(sliceOf ptR)) ∧"))],
     r"⊢ replyFrame oracleB \(vecOf q\.identityAd\) \(oracleB\.dhPublic dB\)\n      \(replyKey \(arrayOf ec\) \(arrayOf q\.sparseReceive\) \(arrayOf q\.dhOut\) dSend\) \(sliceOf ptR\) =\n    Model\.Messages\.encodeInitial ", ['initiator_first_send_responder_replies']),
    ('module', 'reply-claimed-on-the-sparse-chain-k1',
     [(REPLY_BYTES, REPLY_BYTES.replace("(arrayOf q.sparseReceive)", "(arrayOf q.sparseSend)"))],
     r"⊢ replyFrame oracleB \(vecOf q\.identityAd\) \(oracleB\.dhPublic dB\)\n      \(replyKey \(arrayOf ec\) \(arrayOf q\.sparseReceive\) \(arrayOf q\.dhOut\) dSend\) \(sliceOf ptR\) =\n    replyFrame oracleB \(vecOf q\.identityAd\) \(oracleB\.dhPublic dB\)\n      \(replyKey \(arrayOf ec\) \(arrayOf q\.sparseSend\) ", ['initiator_first_send_responder_replies']),
    ('module', 'reply-claimed-under-the-prepared-ratchet-key',
     [(REPLY_BYTES, REPLY_BYTES.replace("(vecOf q.identityAd) (oracleB.dhPublic dB)", "(vecOf q.identityAd) (arrayOf p.ratchetBytes)"))],
     r"⊢ replyFrame oracleB \(vecOf q\.identityAd\) \(oracleB\.dhPublic dB\)\n      \(replyKey \(arrayOf ec\) \(arrayOf q\.sparseReceive\) \(arrayOf q\.dhOut\) dSend\) \(sliceOf ptR\) =\n    replyFrame oracleB \(vecOf q\.identityAd\) \(arrayOf p\.ratchetBytes\)", ['initiator_first_send_responder_replies']),
    ('module', 'reply-relation-claimed-with-the-triple-unchanged',
     [(REPLY_RELATION, REPLY_RELATION_UNCHANGED)],
     r"hsess\nhas type\n  SessionRefines dh oracleB\.braidKem sB''\n    \{\n      triple :=\n        replierAfterSend [\s\S]*?but is expected to have type\n  SessionRefines dh oracleB\.braidKem sB''\n    \(firstReceiptSession ", ['initiator_first_send_responder_replies']),
    ('module', 'root-key-equation-claimed-with-the-sparse-root',
     [(KEYS_ROOT, KEYS_ROOT.replace("(arrayOf q.rootKey, arrayOf q.sendChain)", "(arrayOf q.sparseRoot, arrayOf q.sendChain)"))],
     r"hkdf\nhas type\n  Model\.State\.kdfRk \(arrayOf ec\) \(arrayOf q\.dhOut\) Model\.State\.LabelSet\.tacenta =\n    \(arrayOf q\.rootKey, arrayOf q\.sendChain\)\nbut is expected to have type\n  Model\.State\.kdfRk \(arrayOf ec\) \(arrayOf q\.dhOut\) Model\.State\.LabelSet\.tacenta =\n    \(arrayOf q\.sparseRoot, arrayOf q\.sendChain\)", ['responder_first_frame_successor_keys']),
    ('module', 'receipt-call-on-the-plaintext-not-the-sent-bytes',
     [(KEYS_CALL, KEYS_CALL.replace('storeB (alloc.vec.Vec.deref bytes) rngB =', 'storeB plaintext rngB =', 1))],
     r"hcallB\nhas type\n  lifecycle\.establish_responder rcB crcB ourB storeB plaintext rngB =[\s\S]*?but is expected to have type\n  lifecycle\.establish_responder rcB crcB ourB storeB bytes\.deref rngB =[\s\S]*?in the application\n  responder_first_frame_successor_keys ", ['initiator_first_send_responder_successor_keys']),
    # leaf lemmas
    ('module', 'agreement-send-claimed-to-emit-a-header-message',
     [("      x.1 = { epoch := epoch, ty := tacenta_braid.MsgType.None, data := none } ∧ x.2.2.1 = none := by\n",
       "      x.1 = { epoch := epoch, ty := tacenta_braid.MsgType.Hdr, data := none } ∧ x.2.2.1 = none := by\n")],
     r"but is expected to have type\n  \(\{ epoch := epoch, ty := tacenta_braid\.MsgType\.None, data := none \}, r, none,\n        \{ state := tacenta_braid\.State\.NoHeaderReceived epoch auth dd \}\)\.1 =\n    \{ epoch := epoch, ty := tacenta_braid\.MsgType\.Hdr, data := none \}", ['braid_send_noHeader']),
    ('module', 'draw-record-claimed-at-a-drawing-state',
     [("    (decM : Model.Braid.Decoder) (hmodel : model.braid = .noHeaderReceived e a decM) :\n"
       "    BraidSendTraceAgreementCounted rc crc trace K oracle real model rng where\n",
       "    (decM : Model.Braid.Decoder) (hmodel : model.braid = .headerReceived e a [] [] decM) :\n"
       "    BraidSendTraceAgreementCounted rc crc trace K oracle real model rng where\n")],
     r"hmodel : model\.braid = Model\.Braid\.BraidState\.headerReceived e a \[\] \[\] decM[\s\S]*?⊢ ∃ draws rest,\n    draws\.length = Model\.Lifecycle\.braidSendDrawCount model\.braid", ['braidSendTraceCounted_of_noHeader']),
    ('module', 'reply-header-claimed-with-sparse-number-zero',
     [("      .ok (replierAfterSend ec prk k1 k2 a4 d dSend newPub, firstHeader newPub, replyKey ec k2 d dSend) := by\n",
       "      .ok (replierAfterSend ec prk k1 k2 a4 d dSend newPub, ⟨⟨newPub, 0, 0⟩, 0, 0⟩, replyKey ec k2 d dSend) := by\n")],
     r"error: unsolved goals\nec prk k1 k2 a4 d dSend newPub : Key\n⊢ False", ['reply_send_key']),
    ('module', 'agreement-send-claimed-to-output-an-epoch-key',
     [("      some ((message, epoch, output, next), oracleNext)) :\n"
       "    output = none := by\n",
       "      some ((message, epoch, output, next), oracleNext)) :\n"
       "    output = some { keyEpoch := e, key := [] } := by\n")],
     r"is not definitionally equal to the right-hand side\n  some \{ keyEpoch := e, key := \[\] \}[\s\S]*?⊢ none = some \{ keyEpoch := e, key := \[\] \}", ['sendAgreement_noHeader_output']),
    ('module', 'headroom-claimed-without-the-header-room',
     [("    (plaintext : Slice U8) (hroom : 102 + (plaintext.val.length + 48) ≤ Usize.max) :\n"
       "    Tacenta.UnitLifecycleT1.EncryptHeadroom s plaintext :=\n",
       "    (plaintext : Slice U8) (hroom : plaintext.val.length + 48 ≤ Usize.max) :\n"
       "    Tacenta.UnitLifecycleT1.EncryptHeadroom s plaintext :=\n")],
     r"hroom\nhas type\n  \(↑plaintext\)\.length \+ 48 ≤ Usize\.max\nbut is expected to have type\n  102 \+ \(\(↑plaintext\)\.length \+ 48\) ≤ Usize\.max", ['encryptHeadroom_reply']),
    ('module', 'reply-composite-claimed-with-agreement-type-hdr',
     [("    agType := .none\n    agChunk := none }\n", "    agType := .hdr\n    agChunk := none }\n")],
     r"agType := Model\.CompositeHeader\.AgreementType\.none, agChunk := none \}\)\)\) =\n    Model\.CompositeHeader\.encodeMessage\n      \{ dh := newPub, pn := 0, n := 0, pqEpoch := 0, pqN := 1, agEpoch := 1,\n        agType := Model\.CompositeHeader\.AgreementType\.hdr, agChunk := none \}", ['reply_model_step']),
    ('module', 'model-step-claimed-without-the-pending-premise',
     [("    (ec prk k1 k2 a4 d dSend newPub c : Key) (hpend : mB.pendingInitial = none) (pt : Model.Lifecycle.Bytes) :\n",
       "    (ec prk k1 k2 a4 d dSend newPub c : Key) (hpend : True) (pt : Model.Lifecycle.Bytes) :\n")],
     r"hpend : True\npt : Model\.Lifecycle\.Bytes\n⊢ \(match mB\.pendingInitial with\n    \| none =>", ['reply_model_step']),
    # statement-shape check
    ('module', 'reach-call-claimed-to-leave-the-seed',
     [(REACH_CALL, REACH_CALL.replace("sB'', rngB') ∧", "sB'', seed) ∧"))],
     r"hcallR\nhas type\n  lifecycle\.Session\.encrypt byteRng byteCrc sB' emptyPlaintext rngB' = ok \(core\.result\.Result\.Ok bytesR, sB'', rngB'\)\nbut is expected to have type\n  lifecycle\.Session\.encrypt byteRng byteCrc sB' emptyPlaintext rngB' = ok \(core\.result\.Result\.Ok bytesR, sB'', seed\)", ['first_send_reply_reachable']),
    # the definition, with the pins kept
    ('pinned', 'reply-frame-without-the-associated-data-pinned',
     [("      (Model.Messages.concatAd ad (Model.CompositeHeader.encode (replyComposite newPub))))\n",
       "      (Model.CompositeHeader.encode (replyComposite newPub)))\n")],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleResponderReply.replyFrame')),
]

# The theorems whose proofs compose the run.  Which theorem is a composing step and which only projects another's
# statement is decided by reading; the script holds the labels to each other, to where each control is refused and to
# a syntactic form of the projection standard (below).
COMPOSING = {
    'initiator_first_send_responder_replies',
    'responder_first_frame_successor_keys',
    'initiator_first_send_responder_successor_keys',
}

# The controls that sit inside a composing proof, with the declaration where each is refused.  For each, the script
# also runs the changed copy with that theorem's proof replaced by `sorry` and requires Lean to accept the change
# there: the refusal must be attributable to that proof.  That is all the emptied-proof check shows; it cannot tell a
# composing step from a projection (a corollary's statement-shape check passes it too), which is why the entries must
# name a declaration in `COMPOSING`.
INSIDE = {
    'reply-claimed-to-return-the-receipt-source': 'initiator_first_send_responder_replies',
    'reply-claimed-wrapped-as-an-initial-message': 'initiator_first_send_responder_replies',
    'reply-claimed-on-the-sparse-chain-k1': 'initiator_first_send_responder_replies',
    'reply-claimed-under-the-prepared-ratchet-key': 'initiator_first_send_responder_replies',
    'reply-relation-claimed-with-the-triple-unchanged': 'initiator_first_send_responder_replies',
    'root-key-equation-claimed-with-the-sparse-root': 'responder_first_frame_successor_keys',
    'receipt-call-on-the-plaintext-not-the-sent-bytes': 'initiator_first_send_responder_successor_keys',
}

# The controls refused in a composing proof where it places a conjunct of a called theorem's conclusion unchanged,
# with that called theorem: projections, labelled neither inside nor statement-shape and not probed.  Every other
# control refused in a composing proof must be labelled inside; `check_labels` holds both labels to the syntactic
# form of that standard (`passed_through`).
PROJECTION = {
}

# The theorems a statement-shape check may project: the composing theorems.  The reach `first_send_reply_reachable`
# applies `initiator_first_send_responder_replies` directly to the run `first_send_receive_reachable` gives; there is
# no separate reach run in this module for it to project, as there is in the reply receipt's.
PROJECTED = set(COMPOSING)

# The statement-shape checks, with the theorem each projects.  For each, the script also runs the changed copy with
# that theorem's proof replaced by `sorry` and requires Lean still to refuse the change at its named place: the
# refusal does not depend on the projected theorem's proof.
STATEMENT_SHAPE = {
    'reach-call-claimed-to-leave-the-seed': 'initiator_first_send_responder_replies',
}


BINDER = re.compile(r'\s*(?:· )?(obtain|rcases|have)\b')
PLACING = {'And.intro', 'Or.inl', 'Or.inr', 'Exists.intro'}


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
    for name, called in PROJECTION.items():
        places = [] if isinstance(wheres[name], tuple) else [d for d in wheres[name] if d in COMPOSING]
        if not places:
            raise SystemExit(f'LABELS BROKEN: {name} is labelled a projection but is not refused in a composing proof')
        if passed_through(text, places[0], markers[name]) != called:
            raise SystemExit(f'LABELS BROKEN: {name} is labelled a projection of {called}, but is not refused where '
                             f'{places[0]} places a conjunct of {called} unchanged')
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


def main():
    guard_self_test(NOT_A_REFUSAL)
    check_labels(without_pins(MODULE.read_text(), MODULE))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=900)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='responder-reply-logs-'))
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
    with tempfile.TemporaryDirectory(prefix='responder-reply-controls-') as tmp:
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
