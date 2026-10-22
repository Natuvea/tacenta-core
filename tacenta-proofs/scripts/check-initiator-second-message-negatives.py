#!/usr/bin/env python3
"""Hold the initiator's second message against a planted fault.

`Translation/UnitLifecycleInitiatorSecondMessage.lean` joins two results on one run: the initiator's second
`Session::encrypt` at the session `s''` its receipt of the reply returns, whose code-level part
`initiator_second_send_after_reply` states under `Session::invariant` and `CounterHeadroom` at `s''`, and
`initiator_receives_reply_successor`, which derives those two facts at `s''` under the same hypotheses.  The headline
`initiator_sends_second_message` identifies the two theorems' sessions through the two calls they both state, discharges
the premises, and applies `encrypt_keeps_invariant_no_draw` at `KeysSampled` to carry the invariant, the ceilings and the
budget to the session `s'''` the send leaves.  The reach `first_send_second_message_reachable` rebuilds the reply's
reach run and applies the headline to it.  A proof that Lean accepts after the fact it rests on is removed would hold
nothing, so this script makes one change to a copy of the module and requires Lean to refuse it, at a named place, with
an error that names what the change removed.

The two theorems named in `COMPOSING` compose (decided by reading).  A control refused in a composing theorem is a
projection when it is refused where that proof places a conjunct of a called theorem's conclusion unchanged, and a
composition step, labelled inside, otherwise.  The script holds each of the two labels to a syntactic form of that
standard read off the module (`passed_through`: the refusal names a hypothesis the proof binds by destructuring a called
theorem's conclusion, never rewrites, simplifies or substitutes, and places with a constructor), and requires every
control refused in a composing theorem to carry one of them.  For each inside control it also runs the changed copy with
that theorem's proof replaced by `sorry`, requiring Lean to accept the change there, so the refusal is attributable to
that proof.  That probe verifies attribution only: it cannot tell a composing step from a projection.  That the syntactic
form is the right standard, and that the two theorems compose rather than project, is decided by reading.  The labels
are also held consistent (an inside control must be labelled with the declaration it is refused in and with a composing
theorem; no control carries two labels; a statement-shape check may not be refused in a composing theorem, and the
theorem it projects must be in `PROJECTED`), at start-up (at run time the script checks only that each change is refused
at its labelled place):

  * in `initiator_sends_second_message`: the budget after the send claimed for `j + 1` further operations (refused where
    the preservation step's budget is placed); the budget claimed for every `j` with `j + 2 < u32::MAX`, more than the
    composition derives (refused where the preservation step is applied to it; the clock at `s'''` is 1, so this claim
    is true of the code by reading, and the control shows only that the proof derives no more); the fresh-key premise
    claimed against the initiator's own ratchet key instead of the peer key it holds (refused where the second send's
    theorem is applied); the bound on the second plaintext weakened to `ptS.length + 48 ≤ Usize.max` (refused there
    too); and `s''` claimed to have room for one more operation instead of meeting the ceilings (refused where the
    ceilings derived from the receipt's budget are placed; a true statement, so this shows only that the proof places
    the ceilings, not that it derives no more);
  * in `first_send_second_message_reachable`: the bound on the second plaintext widened to `2 ^ 64` bytes (refused at
    the `omega` that gives the headline its plaintext bound) and the law `DhPublicNotConstant` swapped for
    `DhAgreeSymmetric` (refused where the responder's source is chosen by it).

Three are projections, labelled neither inside nor statement-shape: the initiator's `decrypt` of the reply claimed from
the source before its first send, and the session after the second send claimed to refine the model session before it,
both refused in `initiator_sends_second_message` at the final term where it places the conjuncts of
`initiator_second_send_after_reply` unchanged; and the second `encrypt` claimed at the session before the receipt in
`SecondMessageRun`, refused in the reach at the final term where it places the conjunct of
`initiator_sends_second_message` unchanged.  They show that the composing theorems forward those conjuncts, not that
they compose them, and no emptied-proof run is made for them.

One holds a definition: `SecondMessageRun` with `CounterHeadroom s'''` replaced by `True`, the module's pins kept
(refused at the pin of `SecondMessageRun`).  There is no leaf lemma in the module and no statement-shape check.

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

Dependencies must be built (`lake build Translation.UnitLifecycleInitiatorSecondSend
Translation.UnitLifecycleReceivePreserve`).
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
MODULE = ROOT / 'translation/Translation/UnitLifecycleInitiatorSecondMessage.lean'

BUDGET = "      (∀ j, j + 3 < Std.U32.max → CounterRoom s''' j) := by\n"

FRESH = "    (hfreshB : oracleB.dhPublic dB ≠ arrayOf q.peerRatchetBytes) :\n"

ROOM_S = "    (ptS : Slice Std.U8) (hroomS : 102 + (ptS.val.length + 48) ≤ Usize.max)\n"

CEILINGS = "      lifecycle.Session.invariant s'' = ok true ∧ CounterHeadroom s'' ∧\n"

RECEIPT_CALL = "      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' =\n"

SENT_REL = """      SessionRefines dh oracle.braidKem s'''
        { replyReceiptSession
            (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
            (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
            (oracleB.dhPublic dB) (oracle.dhPublic dA) dA with
          triple := initiatorAfterSecond (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend)
            (arrayOf q.sparseReceive) dSend x (oracleB.dhPublic dB) (oracle.dhPublic dA)
          braid := .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
            ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 2⟩ } ∧
"""

SENT_REL_BEFORE = """      SessionRefines dh oracle.braidKem s'''
        (replyReceiptSession
            (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session
            (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) dSend x
            (oracleB.dhPublic dB) (oracle.dhPublic dA) dA) ∧
"""

REACH_PTS = "(ptS : Slice Std.U8) (hptS : ptS.val.length ≤ 4096) :\n"

REACH_LAW = "(haead : AeadRoundTrip) (hnc : DhPublicNotConstant)\n"

RUN_SEND = ("    lifecycle.Session.encrypt byteRng byteCrc s'' ptS rngA' = "
            "ok (core.result.Result.Ok bytes2, s''', rngA') ∧\n")

RUN_LAST = "    lifecycle.Session.invariant s''' = ok true ∧ CounterHeadroom s'''\n\n"

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
    # inside the composing proofs
    ('module', 'budget-after-the-send-claimed-one-operation-longer',
     [(BUDGET, BUDGET.replace("CounterRoom s''' j)", "CounterRoom s''' (j + 1))"))],
     r"\(key j hj\)\.right\nhas type\n  CounterRoom s''' j\nbut is expected to have type\n  CounterRoom s''' \(j \+ 1\)",
     ['initiator_sends_second_message']),
    ('module', 'budget-after-the-send-claimed-beyond-the-composed-bound',
     [(BUDGET, BUDGET.replace("j + 3 <", "j + 2 <"))],
     r"hj\nhas type\n  j \+ 2 < U32\.max\nbut is expected to have type\n  j \+ 3 < U32\.max\nin the application\n  key j hj",
     ['initiator_sends_second_message']),
    ('module', 'fresh-key-premise-claimed-against-the-initiator-key',
     [(FRESH, FRESH.replace("q.peerRatchetBytes", "q.ratchetBytes"))],
     r"hfreshB\nhas type\n  oracleB\.dhPublic dB ≠ arrayOf q\.ratchetBytes\nbut is expected to have type\n  oracleB\.dhPublic dB ≠ arrayOf q\.peerRatchetBytes\nin the application\n  initiator_second_send_after_reply",
     ['initiator_sends_second_message']),
    ('module', 'second-plaintext-bound-weakened',
     [(ROOM_S, ROOM_S.replace("102 + (ptS.val.length + 48)", "ptS.val.length + 48"))],
     r"hroomS\nhas type\n  \(↑ptS\)\.length \+ 48 ≤ Usize\.max\nbut is expected to have type\n  102 \+ \(\(↑ptS\)\.length \+ 48\) ≤ Usize\.max\nin the application\n  initiator_second_send_after_reply",
     ['initiator_sends_second_message']),
    ('module', 'receipt-session-claimed-to-have-room-for-one-more-operation',
     [(CEILINGS, CEILINGS.replace("CounterHeadroom s''", "CounterRoom s'' 1"))],
     r"hc\nhas type\n  CounterHeadroom s''\nbut is expected to have type\n  CounterRoom s'' 1\nin the application\n  And\.intro hc",
     ['initiator_sends_second_message']),
    ('module', 'reach-second-plaintext-bound-widened',
     [(REACH_PTS, REACH_PTS.replace("≤ 4096", "≤ 2 ^ 64"))],
     r"omega could not prove the goal:", ['first_send_second_message_reachable']),
    ('module', 'reach-fresh-key-law-swapped',
     [(REACH_LAW, REACH_LAW.replace("(hnc : DhPublicNotConstant)", "(hnc : DhAgreeSymmetric)"))],
     r"hnc\nhas type\n  DhAgreeSymmetric\nbut is expected to have type\n  DhPublicNotConstant\nin the application\n  dhPublicNotConstant_is\.mp hnc",
     ['first_send_second_message_reachable']),
    # projections
    ('module', 'receipt-claimed-from-the-source-before-the-first-send',
     [(RECEIPT_CALL, RECEIPT_CALL.replace("bytesR) rng' =", "bytesR) rng ="))],
     r"hcallA\nhas type\n  lifecycle\.Session\.decrypt rc crc s' bytesR\.deref rng' = ok \(core\.result\.Result\.Ok ptA, s'', rngA'\)\nbut is expected to have type\n  lifecycle\.Session\.decrypt rc crc s' bytesR\.deref rng = ok \(core\.result\.Result\.Ok ptA, s'', rngA'\)\nin the application\n  And\.intro hcallA",
     ['initiator_sends_second_message']),
    ('module', 'session-after-the-send-claimed-to-refine-the-model-before-it',
     [(SENT_REL, SENT_REL_BEFORE)],
     r"hrel3\nhas type\n  SessionRefines dh oracle\.braidKem s'''\n[\s\S]*?but is expected to have type\n  SessionRefines dh oracle\.braidKem s'''\n    \(replyReceiptSession[\s\S]*?in the application\n  And\.intro hrel3",
     ['initiator_sends_second_message']),
    ('module', 'reach-second-send-claimed-at-the-session-before-the-receipt',
     [(RUN_SEND, RUN_SEND.replace("s'' ptS rngA' =", "s' ptS rngA' ="))],
     r"hcallS\nhas type\n  lifecycle\.Session\.encrypt byteRng byteCrc s'' ptS rngA' = [\s\S]*?but is expected to have type\n  lifecycle\.Session\.encrypt byteRng byteCrc s' ptS rngA' = [\s\S]*?in the application\n  And\.intro hcallS",
     ['first_send_second_message_reachable']),
    # the definition, with the pins kept
    ('pinned', 'run-without-the-ceilings-after-the-send-pinned',
     [(RUN_LAST, RUN_LAST.replace("∧ CounterHeadroom s'''\n", "∧ True\n"))],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleInitiatorSecondMessage.SecondMessageRun')),
]

COMPOSING = {
    'initiator_sends_second_message',
    'first_send_second_message_reachable',
}

# The controls labelled inside a composing proof, with the declaration each is refused in.  For each, the script also
# runs the changed copy with that theorem's proof replaced by `sorry` and requires Lean to accept the change there:
# the refusal is attributable to that proof.
INSIDE = {
    'budget-after-the-send-claimed-one-operation-longer': 'initiator_sends_second_message',
    'budget-after-the-send-claimed-beyond-the-composed-bound': 'initiator_sends_second_message',
    'fresh-key-premise-claimed-against-the-initiator-key': 'initiator_sends_second_message',
    'second-plaintext-bound-weakened': 'initiator_sends_second_message',
    'receipt-session-claimed-to-have-room-for-one-more-operation': 'initiator_sends_second_message',
    'reach-second-plaintext-bound-widened': 'first_send_second_message_reachable',
    'reach-fresh-key-law-swapped': 'first_send_second_message_reachable',
}

# The controls refused in a composing proof where it places a conjunct of a called theorem's conclusion unchanged,
# with that called theorem: projections, labelled neither inside nor statement-shape and not probed.  Every other
# control refused in a composing proof must be labelled inside; `check_labels` holds both labels to the syntactic form
# of that standard (`passed_through`).
PROJECTION = {
    'receipt-claimed-from-the-source-before-the-first-send': 'initiator_second_send_after_reply',
    'session-after-the-send-claimed-to-refine-the-model-before-it': 'initiator_second_send_after_reply',
    'reach-second-send-claimed-at-the-session-before-the-receipt': 'initiator_sends_second_message',
}

# The theorems a statement-shape check may project: the composing theorems.
PROJECTED = set(COMPOSING)

# The statement-shape checks, with the theorem each projects (none: the module has no leaf lemma).
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
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='initiator-second-message-logs-'))
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
    with tempfile.TemporaryDirectory(prefix='initiator-second-message-controls-') as tmp:
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
