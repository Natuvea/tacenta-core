#!/usr/bin/env python3
"""Hold the initiator's refusal of a tampered reply against a planted fault.

`Translation/UnitLifecycleTamperedReply.lean` shows that, on the run in which the initiator's public `Session::decrypt`
at the session `s'` its first `encrypt` left accepts the responder's reply `bytesR`, the same call, from the same
source, refuses with `Aead` every frame that keeps the reply's first 102 bytes and carries bytes that no call of the
boundary's `encrypt` returns under the reply's message keys and associated data (the per-run premise `NotASealing`),
leaves the session as it was and takes exactly one draw; under the assumed law `AeadOpenSealUnique` (an opened
ciphertext is the sealing of what it opened to), which the module also shows holds in a toy model and is not implied
by the round trip.  A proof that Lean accepts after the fact it rests on is removed would hold nothing, so this script
makes one change to a copy of the module and requires Lean to refuse it, at a named place, with an error that names
what the change removed.

Seven controls are labelled inside the proof that composes the run, `initiator_refuses_tampered_reply`, and none is a
projection.  A control refused in a composing theorem is a projection when it is refused where that proof places a
conjunct of a called theorem's conclusion unchanged, and a composition step, labelled inside, otherwise.  The script
holds each of the two labels to a syntactic form of that standard read off the module (`passed_through`: the refusal
names a hypothesis the proof binds by destructuring a called theorem's conclusion, never rewrites, simplifies or
substitutes, and places with a constructor), and requires every control refused in a composing theorem to carry one of
them.  For each inside control it also runs the changed copy with that theorem's proof replaced by `sorry`, requiring
Lean to accept the change there, so the refusal is attributable to that proof.  That probe verifies attribution only:
it cannot tell a composing step from a projection.  That the syntactic form is the right standard, and that the theorem
named in `COMPOSING` composes rather than projects, is decided by reading.  The labels are also held consistent (an
inside control must be labelled with the declaration it is refused in and with a composing theorem; no control carries
two labels; every place a projection may be refused must be a composing theorem; a statement-shape check may not be
refused in a composing theorem, and the theorem it projects must be in `PROJECTED`), at start-up (at run time the
script checks only that each change is refused at its labelled place):

  * inside: the tampered frame claimed to keep only the reply's first 101 bytes (refused where the frame layout lemma
    is rewritten into the frame premise, which then does not match the reply's 102-byte header);
  * inside: the reply's own ciphertext claimed to start after 101 bytes (refused where the layout lemma for the bytes
    after the header is rewritten into the conjunct that the reply's ciphertext is a sealing);
  * inside: the frame's premise claimed under the associated data of the peer key the initiator holds instead of the
    reply's ratchet key (refused where the premise is given to the open's bridge at the run's associated data);
  * inside: the freshness premise claimed against the initiator's own ratchet key instead of the peer key (refused
    where it is given to `initiator_receives_reply`);
  * inside: the uniqueness law replaced by the round trip `AeadRoundTrip` (refused where the law is given to the open's
    bridge);
  * inside: the refused call claimed to take no draw (refused where the draw conjunct of the decrypt refinement,
    rewritten by the model's refusal, is placed);
  * inside: the refusal claimed to be the stale-key refusal `Triple(Classical(NoReceivingChain))` instead of `Aead`
    (refused where the call, rewritten by the error the model's refusal fixes and by the refusal frame, is placed).

Six are on the leaf lemmas:

  * the law weakened to equal ciphertext lengths (refused in `open_none_of_not_sealing`, which then cannot read the
    tampered bytes back as a sealing);
  * the model's refusal claimed to leave the oracle's draws untouched (refused in `tampered_reply_model_refusal`);
  * the model's refusal claimed when the reply's ratchet key is the peer key (refused there, where the fresh-key
    receive is used);
  * the reply's header claimed to be 103 bytes (refused in `replyFrame_take`);
  * the toy's seal of the empty plaintext claimed to be no sealing (refused in `modelReply_notASealing_nil`);
  * the lenient open made to check the leading byte as the toy does (refused in `lenient_roundTrip_not_unique`, whose
    counterexample it then refuses to open).

Two hold definitions with the module's pins kept: the per-run premise reversed (a sealing claimed instead of excluded;
refused at the pin of `NotASealingShape`) and the law weakened to equal lengths (refused at the pin of
`AeadOpenSealUniqueShape`).  No statement-shape check: the module has no reach.

Every change is to a statement or a definition; none replaces a proof step.  Each refusal is a proof-breakage check at
a named place: it shows that the proof there depends on what the change removed (or, for the last two, that the pin
holds the definition), not that the changed statement is false.

The changes are checked on a copy without the module's pins, so that the refusal comes from a proof and not from a
pin, except the two kept with their pins.  The unmodified copies must be accepted first.  A compiler that does not
start, a syntax error, an unrelated failure and a refusal elsewhere than the named place never count: the named
refusal must be an error at the named place that matches the expected message.  An error whose first line names a
kind of failure that is not a refusal (an unresolved name, a syntax error) voids the run anywhere in the copy,
compared without regard to case.  A timeout (heartbeat or deterministic) never counts as the named refusal; one
elsewhere in the copy is logged in the result and does not void a separate matching error at the named place.  The
script checks at start that the guard fires on the toolchain's own `Unknown identifier`, on the kernel's `unknown
constant`, on a parser's `unexpected token` and `expected '...'`, on `unknown namespace` and on `does not contain`,
each from a sample holding that spelling alone, and not on an ordinary refusal, and that a heartbeat timeout is told
apart from a refusal.  These are
controls on copies of the Lean; no source, olean or git state changes.

Dependencies must be built (`lake build Translation.UnitLifecycleResponderReplyReceipt`).
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
MODULE = ROOT / 'translation/Translation/UnitLifecycleTamperedReply.lean'

FRAME = "        sliceOf frame = (vecOf bytesR).take 102 ++ cT →\n"

HONEST = "        (replyAd (vecOf q.identityAd) (oracleB.dhPublic dB)) ((vecOf bytesR).drop 102) ∧\n"

NOT_SEALED = "          (replyAd (vecOf q.identityAd) (oracleB.dhPublic dB)) cT →\n"

FRESH = "    (hfreshB : oracleB.dhPublic dB ≠ arrayOf q.peerRatchetBytes) :\n"

LAW = "    (hu : AeadOpenSealUnique) (rc : rand_core_1.RngCore R)"

REFUSED = "            ok (core.result.Result.Err lifecycle.Error.Aead, s', rngT) ∧ trace rngT = restA := by\n"

LAW_BODY = "    ∃ ct, I.aeadEncrypt k1 k2 iv (alloc.vec.Vec.deref v) ad = ok ct ∧ ct.val = c.val\n"

MODEL_OUT = "      { session := mA, result := .error .aead, oracle := { oracleA with draws := rest } } := by\n"

MODEL_PEER = "    (hcand : oracleA.dhAgree c newPub = some x) (hpeer : newPub ≠ peer)\n"

TAKE = ("    (replyFrame oracle ad newPub mk pt).take 102 = Model.CompositeHeader.encode (replyComposite newPub) "
        ":= by\n")

NIL = "    NotASealingShape Interp.modelReply k1 k2 iv ad [] := by\n"

LENIENT = "  if c.val = [] then .Err () else .Ok ⟨c.val.tail, by have := c.property; simp; omega⟩\n"

NOT_SEALED_BODY = "    I.aeadEncrypt K1 K2 IV pt A = ok ct → vecOf ct ≠ c\n"

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`, or ('pin', name, 'check') for that of
#  its statement pin `#check @name`)
MUTANTS = [
    # in the composing proof: inside
    ('module', 'tampered-frame-claimed-with-a-101-byte-header',
     [(FRAME, FRAME.replace("take 102", "take 101"))],
     r"Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  List\.take 102 \(replyFrame [\s\S]*?"
     r"in the target expression\n  sliceOf frame =\n    List\.take 101", ['initiator_refuses_tampered_reply']),
    ('module', 'honest-ciphertext-claimed-after-101-bytes',
     [(HONEST, HONEST.replace("drop 102", "drop 101"))],
     r"Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  List\.drop 102 \(replyFrame [\s\S]*?"
     r"in the target expression\n  ¬NotASealing[\s\S]*?\(List\.drop 101", ['initiator_refuses_tampered_reply']),
    ('module', 'no-sealing-claimed-under-the-peer-key-associated-data',
     [(NOT_SEALED, NOT_SEALED.replace("(oracleB.dhPublic dB)) cT", "(arrayOf q.peerRatchetBytes)) cT"))],
     r"Application type mismatch: The argument\n  hns\nhas type\n  NotASealing[\s\S]*?"
     r"\(replyAd \(vecOf q\.identityAd\) \(arrayOf q\.peerRatchetBytes\)\) cT\nbut is expected to have type",
     ['initiator_refuses_tampered_reply']),
    ('module', 'freshness-claimed-against-the-initiator-own-key',
     [(FRESH, FRESH.replace("q.peerRatchetBytes", "q.ratchetBytes"))],
     r"The argument\n  hfreshB\nhas type\n  oracleB\.dhPublic dB ≠ arrayOf q\.ratchetBytes\nbut is expected to have "
     r"type\n  oracleB\.dhPublic dB ≠ arrayOf q\.peerRatchetBytes\nin the application\n  initiator_receives_reply ",
     ['initiator_refuses_tampered_reply']),
    ('module', 'uniqueness-law-replaced-by-the-round-trip',
     [(LAW, LAW.replace("AeadOpenSealUnique", "AeadRoundTrip"))],
     r"The argument\n  hu\nhas type\n  AeadRoundTrip\nbut is expected to have type\n  AeadOpenSealUnique\nin the "
     r"application\n  @open_none_of_not_sealing hu", ['initiator_refuses_tampered_reply']),
    ('module', 'tampered-refusal-claimed-to-take-no-draw',
     [(REFUSED, REFUSED.replace("trace rngT = restA", "trace rngT = dA :: restA"))],
     r"hdrT\nhas type\n[\s\S]*?\{ draws := restA, [\s\S]*?\.oracle\.draws\nbut is expected to have type\n  "
     r"trace rngT = dA :: restA", ['initiator_refuses_tampered_reply']),
    ('module', 'tampered-refusal-claimed-as-the-stale-key-refusal',
     [(REFUSED, REFUSED.replace(
         "Err lifecycle.Error.Aead",
         "Err (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical "
         "tacenta_ratchet.RatchetError.NoReceivingChain))"))],
     r"hcallT\nhas type\n  lifecycle\.Session\.decrypt rc crc s' frame rng' = ok \(core\.result\.Result\.Err "
     r"lifecycle\.Error\.Aead, s', rngT\)\nbut is expected to have type[\s\S]*?NoReceivingChain",
     ['initiator_refuses_tampered_reply']),
    # leaf lemmas
    ('module', 'uniqueness-law-weakened-to-equal-lengths',
     [(LAW_BODY, LAW_BODY.replace("ct.val = c.val", "ct.val.length = c.val.length"))],
     r"Type mismatch\n  hC\nhas type\n  sliceOf C = c\nbut is expected to have type\n  "
     r"List\.map SessionUnitBraidT3\.u8 ↑ct = c", ['open_none_of_not_sealing']),
    ('module', 'model-refusal-claimed-to-keep-the-draw',
     [(MODEL_OUT, MODEL_OUT.replace("oracle := { oracleA with draws := rest } }", "oracle := oracleA }"))],
     r"error: unsolved goals[\s\S]*?\{ draws := rest, braidKem := oracleA\.braidKem[\s\S]*?=\n    "
     r"\{ session := mA, result := Except\.error Model\.Lifecycle\.Refusal\.aead, oracle := oracleA \}",
     ['tampered_reply_model_refusal']),
    ('module', 'model-refusal-claimed-on-the-peer-key',
     [(MODEL_PEER, MODEL_PEER.replace("newPub ≠ peer", "newPub = peer"))],
     r"The argument\n  hpeer\nhas type\n  newPub = peer\nbut is expected to have type\n  newPub ≠ peer\nin the "
     r"application\n  reply_receive_key ", ['tampered_reply_model_refusal']),
    ('module', 'reply-header-claimed-103-bytes',
     [(TAKE, TAKE.replace("take 102", "take 103"))],
     r"Did not find an occurrence of the pattern\n  102\nin the target expression\n  List\.take 103",
     ['replyFrame_take']),
    ('module', 'toy-seal-of-empty-claimed-no-sealing',
     [(NIL, NIL.replace("ad [] := by", "ad [0] := by"))],
     r"error: unsolved goals\ncase isTrue[\s\S]*?⊢ SessionUnitBraidT3\.u8 0#u8 = 0 → ¬↑pt = \[\]",
     ['modelReply_notASealing_nil']),
    ('module', 'lenient-open-made-to-check-the-leading-byte',
     [(LENIENT, LENIENT.replace("if c.val = [] then", "if c.val.head? ≠ some 0#u8 then"))],
     r"Tactic `rfl` failed: The left-hand side\n  ok \(if \(↑c\)\.head\? ≠ some 0#u8 then",
     ['lenient_roundTrip_not_unique']),
    # the definitions, with the pins kept
    ('pinned', 'no-sealing-premise-reversed-pinned',
     [(NOT_SEALED_BODY, NOT_SEALED_BODY.replace("vecOf ct ≠ c", "vecOf ct = c"))],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleTamperedReply.NotASealingShape')),
    ('pinned', 'uniqueness-law-weakened-pinned',
     [(LAW_BODY, LAW_BODY.replace("ct.val = c.val", "ct.val.length = c.val.length"))],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleTamperedReply.AeadOpenSealUniqueShape')),
]

COMPOSING = {
    'initiator_refuses_tampered_reply',
}

# The controls labelled inside a composing proof, with the declaration each is refused in.  For each, the script also
# runs the changed copy with that theorem's proof replaced by `sorry` and requires Lean to accept the change there:
# the refusal is attributable to that proof.
INSIDE = {
    'tampered-frame-claimed-with-a-101-byte-header': 'initiator_refuses_tampered_reply',
    'honest-ciphertext-claimed-after-101-bytes': 'initiator_refuses_tampered_reply',
    'no-sealing-claimed-under-the-peer-key-associated-data': 'initiator_refuses_tampered_reply',
    'freshness-claimed-against-the-initiator-own-key': 'initiator_refuses_tampered_reply',
    'uniqueness-law-replaced-by-the-round-trip': 'initiator_refuses_tampered_reply',
    'tampered-refusal-claimed-to-take-no-draw': 'initiator_refuses_tampered_reply',
    'tampered-refusal-claimed-as-the-stale-key-refusal': 'initiator_refuses_tampered_reply',
}

# The controls refused in a composing proof where it places a conjunct of a called theorem's conclusion unchanged,
# with that called theorem: projections, labelled neither inside nor statement-shape and not probed (none here).
# Every other control refused in a composing proof must be labelled inside; `check_labels` holds both labels to the
# syntactic form of that standard (`passed_through`).
PROJECTION = {}

# The theorems a statement-shape check may project.
PROJECTED = set(COMPOSING)

# The statement-shape checks, with the theorem each projects (none: the module has no reach).  For each, the script
# would also run the changed copy with that theorem's proof replaced by `sorry` and require Lean still to refuse the
# change at its named place.
STATEMENT_SHAPE = {}


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
    for name, where in wheres.items():
        if isinstance(where, tuple) and not (where[:1] == ('pin',) and (len(where) == 2 or (len(where) == 3 and
                                                                                           where[2] == 'check'))):
            raise SystemExit(f'LABELS BROKEN: {name} is refused at {where}, which is neither (\'pin\', name), a '
                             f'`#print` pin, nor (\'pin\', name, \'check\'), a `#check @` pin')
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


def pin_line(text, name, form='print'):
    """The 1-based line of the `#guard_msgs in` that precedes the pin of `name` in the one form its control names:
    `#print name` (a definition's pin, `form` 'print') or `#check @name` (a statement pin, `form` 'check'), or None.
    Only that form is matched, so a name pinned both ways cannot resolve to the other pin."""
    command = {'print': f'#print {name}', 'check': f'#check @{name}'}[form]
    lines = text.split('\n')
    for k in range(1, len(lines)):
        if lines[k] == command and lines[k - 1].startswith('#guard_msgs'):
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
        form = where[2] if len(where) == 3 else 'print'
        line = pin_line(mutated, where[1], form)
        if line is None:
            shown = f'#print {where[1]}' if form == 'print' else f'#check @{where[1]}'
            raise SystemExit(f'FAILED control {name}: the copy has no `{shown}` pin, so its refusal cannot be the '
                             f'pin\'s; {log}')
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
    # Kept from this script's own start-up checks (the shared check_labels no longer holds them): a control list that
    # is empty, or two controls with one name, stop the run before Lean does.
    if not MUTANTS:
        raise SystemExit('NO CONTROLS: MUTANTS is empty; a control with no planted change holds nothing')
    if len({name for _, name, _, _, _ in MUTANTS}) != len(MUTANTS):
        raise SystemExit('LABELS BROKEN: two controls have one name')
    check_labels(without_pins(MODULE.read_text(), MODULE))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=900)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='tampered-reply-logs-'))
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
    with tempfile.TemporaryDirectory(prefix='tampered-reply-controls-') as tmp:
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
