#!/usr/bin/env python3
"""Hold the responder successor's invariant and ceilings against a planted fault.

`Translation/UnitLifecycleResponderSuccessor.lean` shows that the session `establish_responder` returns on the bytes
the initiator's first `encrypt` emits passes `Session::invariant` and meets the four counter ceilings, from a walk of
the successful `decrypt_ratchet`, the relation the first receipt proves (which fixes the Triple and the agreement's
state), and a walk of `Braid::receive` for the agreement's decoder.  A proof that Lean accepts after the fact it rests
on is removed would hold nothing, so this script makes one change to a copy of the module and requires Lean to refuse
it, at a named place, with an error that names what the change removed.

One control is labelled inside the proofs that compose the run, two are projections and three are statement-shape
checks.  A control refused in a composing theorem is a projection when it is refused where that proof places a
conjunct of a called theorem's conclusion unchanged, and a composition step, labelled inside, otherwise.  The script
holds each of the two labels to a syntactic form of that standard read off the module (`passed_through`: the refusal
names a hypothesis the proof binds by destructuring a called theorem's conclusion, never rewrites, simplifies or
substitutes, and places with a constructor), and requires every control refused in a composing theorem to carry one
of them.  For the inside control it also runs the changed copy with that theorem's proof replaced by `sorry`,
requiring Lean to accept the change there, so the refusal is attributable to that proof.  That probe verifies
attribution only: it cannot tell a composing step from a projection (a corollary's statement-shape check passes it
too).  That the syntactic form is the right standard, and that the two theorems named in `COMPOSING` compose rather
than project, is decided by reading.  The labels are also held consistent (an inside control must be labelled with
the declaration it is refused in and with a composing theorem; no control carries two labels; every place a projection
may be refused must be a composing theorem; a statement-shape check may not be refused in a composing theorem, and the
theorem it projects must be in `PROJECTED`), at start-up (at run time the script checks only that each change is refused
at its labelled place):

  * inside `initiator_first_send_responder_successor_hypotheses`: the composed call taken on the plaintext instead of
    the bytes the first send returned (refused at the step where the encrypt's output fixes the message, the argument
    the proof passes to `responder_first_frame_successor`);
  * projections: the composed invariant claimed of the initiator's session after its send (refused in
    `initiator_first_send_responder_successor_hypotheses` where the invariant conjunct of
    `responder_first_frame_successor` is placed unchanged), and the returned session's relation claimed to the
    prepared session's model instead of the step's (refused in `responder_first_frame_successor` where the relation
    conjunct of `responder_first_frame_inner_succeeds` is placed unchanged).

Ten are on the leaf lemmas:

  * the Triple's shape: one message received claimed as none (refused in `triple_eq_received`: the relation fixes
    the receive counter at 1), the sparse receiving chain's counter claimed 0 (same place);
  * the ceilings: the clock claimed parked at `u32::MAX - 1` (refused in `received_counterHeadroom`, whose first
    field, the classical-clock ceiling, is then left as `False`);
  * the invariant's premises: the Triple's invariant without the sending key's canonicity (refused in
    `receivedTriple_invariant`), the structural invariant without the ratchet key's public bytes being the sending
    key (refused in `structural_received`), the agreement claimed at epoch 2 (refused in `structural_received`,
    where the sparse epoch 0 must be one below the agreement's);
  * the decoder: the decoder lemma for two chunks instead of one (refused in `decoder_invariant_small`, whose loop
    computation covers at most one chunk) and without its chunk-count premise (same place);
  * the walks: `Braid::receive` claimed to keep the decoder or return nothing else (`d' = d ∨ False`; refused in
    `braid_receive_noHeader` only at the branch where the chunk is added) and `decrypt_ratchet` claimed never to
    replace the ratchet key (refused in `decrypt_ratchet_ok_parts`).

Three are statement-shape checks on the headline's own corollaries, each projecting
`initiator_first_send_responder_successor_hypotheses`: the invariant claimed of the initiator's session and the call
taken on the plaintext (refused in `initiator_first_send_responder_successor_admissible`), and the reach's invariant
claimed of the initiator's session (refused in `first_send_receive_successor_reachable`).  Each is refused because its
statement no longer matches that theorem's; the script runs each again with that theorem's proof replaced by `sorry`
and requires the same refusal, so it is refused whatever that proof does.  One holds a definition: the session after
the receive without its ratchet key, the module's pins kept (refused at the pin of `receivedSession`).

Every change is to a statement or a definition; none replaces a proof step.  Each refusal is a proof-breakage check at
a named place: it shows that the proof there depends on what the change removed (or, for the last, that the pin holds
the definition), not that the changed statement is false.  Only the control inside the composing proof shows that
the composed proof uses what it names (the bytes the first send returned); the two projections show only that the
composed conclusions place the called theorems' invariant and relation unchanged, and the three statement-shape checks
only that the corollaries and the reach project the headline's statement.  None is a proof that any other session
fails the invariant.

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

Dependencies must be built (`lake build Translation.UnitLifecycleResponderFirstReceipt`).
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
MODULE = ROOT / 'translation/Translation/UnitLifecycleResponderSuccessor.lean'

ADMISSIBLE_CALL = ("    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =\n"
                   "      ok (core.result.Result.Ok (sB', ptB), storeB', rngB')) :\n"
                   "    lifecycle.Session.invariant sB' = ok true := by\n")

HYPOTHESES_CALL = ("    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =\n"
                   "      ok (core.result.Result.Ok (sB', ptB), storeB', rngB')) :\n"
                   "    ∃ (p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes)) (ec : Array U8 32#usize)\n")

STEP_RELATION = ("      SessionRefines dh oracleB.braidKem sB'\n"
                 "        (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)\n"
                 "          (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)\n"
                 "          (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) ∧\n")

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`, or ('pin', name, 'check') for that of
#  its statement pin `#check @name`)
MUTANTS = [
    # leaf lemmas
    ('module', 'triple-claimed-to-have-received-nothing',
     [('        ns := 0#u32, nr := 1#u32, pn := 0#u32, skipped := alloc.vec.Vec.new tacenta_ratchet.SkippedKey,\n',
       '        ns := 0#u32, nr := 0#u32, pn := 0#u32, skipped := alloc.vec.Vec.new tacenta_ratchet.SkippedKey,\n')],
     r'but is expected to have type\n  \{\n      classical :=\n[^\n]*nr := 1#u32,[\s\S]*?=\n    receivedTriple dhs a rk',
     ['triple_eq_received']),
    ('module', 'sparse-receive-counter-claimed-zero',
     [('    [(0#u64, { send := some { ck := c2, n := 0#u64 }, receive := some { ck := cr, n := 1#u64 } })]\n',
       '    [(0#u64, { send := some { ck := c2, n := 0#u64 }, receive := some { ck := cr, n := 0#u64 } })]\n')],
     r'hch\nhas type\n  ↑ch = \[\(0#u64, \{ send := some \{ ck := sck, n := 0#u64 \}, receive := some \{ ck := rck, n := 1#u64 \} \}\)\]\nbut is expected to have type\n  ↑ch = ↑\(receivedChains sck rck\)',
     ['triple_eq_received']),
    ('module', 'clock-claimed-parked',
     [('        events := 1#u32, labels := tacenta_ratchet.LabelSet.Tacenta },\n',
       '        events := 4294967294#u32, labels := tacenta_ratchet.LabelSet.Tacenta },\n')],
     r'error: unsolved goals\ncase refine_1\nour : lifecycle\.Identity[\s\S]*?rp : tacenta_boundary\.dh\.PrivateKey\n⊢ False',
     ['received_counterHeadroom']),
    ('module', 'triple-invariant-without-the-sending-key-canonical',
     [('    (hs : Tacenta.SessionUnitT1.canonicalX25519 dhs = true)\n',
       '    (hs : True)\n')],
     r'term\n  hs\n has type\n  True\nbut is expected to have type\n  SessionUnitT1\.canonicalX25519 dhs = true',
     ['receivedTriple_invariant']),
    ('module', 'structural-invariant-without-the-ratchet-key-bytes',
     [('    (hpk : tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok dhs) :\n'
       '    lifecycle.Session.structural_invariant\n',
       '    (hpk : True) :\n'
       '    lifecycle.Session.structural_invariant\n')],
     r'hpk : True[\s\S]*?⊢ \(do\n      let a ← pk\.as_bytes\n      let b ← core\.array\.equality\.PartialEqArray\.ne core\.cmp\.PartialEqU8 a dhs',
     ['structural_received']),
    ('module', 'agreement-claimed-at-epoch-two',
     [('    braid := ⟨tacenta_braid.State.NoHeaderReceived 1#u64 auth dec⟩\n',
       '    braid := ⟨tacenta_braid.State.NoHeaderReceived 2#u64 auth dec⟩\n')],
     r'h01 : U64\.checked_add 0#u64 1#u64 = some 1#u64\nhmod : 1#u64 % 2#u64 = ok 1#u64\n⊢ False',
     ['structural_received']),
    ('module', 'decoder-lemma-for-two-chunks',
     [('    (hlen : d.«have».val.length ≤ 1) (hn : d.«have».val.length ≤ d.needed.val) :\n',
       '    (hlen : d.«have».val.length ≤ 2) (hn : d.«have».val.length ≤ d.needed.val) :\n')],
     r'case cons\.cons\n[\s\S]*?hv : ↑d\.have = c :: c\' :: rest\nhlen : rest = \[\]\n⊢ d\.invariant_loop \(Array\.repeat 8192#usize 0#u8\) true 0#usize = ok \(d\.size, d\.needed, d\.have, true\)', ['decoder_invariant_small']),
    ('module', 'decoder-lemma-without-the-chunk-count',
     [('    (hcc : tacenta_erasure.chunk_count d.size = ok d.needed) (hle : d.needed.val ≤ 65536)\n',
       '    (hcc : True) (hle : d.needed.val ≤ 65536)\n')],
     r'⊢ \(do\n      let i2 ← tacenta_erasure\.chunk_count d\.size\n      if d\.needed = i2 then ok true else ok false\) =\n    ok true', ['decoder_invariant_small']),
    ('module', 'braid-receive-claimed-to-keep-the-decoder',
     [("    d' = d ∨ ∃ c r, tacenta_erasure.Decoder.add_chunk d c = ok (r, d') := by\n",
       "    d' = d ∨ False := by\n")],
     r'Invalid `⟨\.\.\.⟩` notation: The expected type `False` has no constructors', ['braid_receive_noHeader']),
    ('module', 'receive-claimed-never-to-replace-the-ratchet-key',
     [("          s' = { s with triple := s'.triple, braid := bc, ratchet_private := ck }) ∨\n",
       "          s' = { s with triple := s'.triple, braid := bc }) ∨\n")],
     r'ratchet_private := ck, identity_ad := s\.identity_ad,[\s\S]*?=\n    \{\n      triple :=[\s\S]*?braid := bc, ratchet_private := s\.ratchet_private', ['decrypt_ratchet_ok_parts']),
    # in the composing proofs: one inside, two projections
    ('module', 'composed-call-on-the-plaintext-not-the-sent-bytes',
     [(HYPOTHESES_CALL, HYPOTHESES_CALL.replace('storeB (alloc.vec.Vec.deref bytes) rngB =', 'storeB plaintext rngB =', 1))],
     r'hcallB\nhas type\n  lifecycle\.establish_responder rcB crcB ourB storeB plaintext rngB =[\s\S]*?but is expected to have type\n  lifecycle\.establish_responder rcB crcB ourB storeB bytes\.deref rngB =[\s\S]*?in the application\n  responder_first_frame_successor ',
     ['initiator_first_send_responder_successor_hypotheses']),
    ('module', 'composed-invariant-claimed-of-the-initiator-session',
     [("      lifecycle.Session.invariant sB' = ok true ∧\n"
       "      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' := by\n"
       "  obtain ⟨output, hcall', hdr, hcases⟩",
       "      lifecycle.Session.invariant s' = ok true ∧\n"
       "      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' := by\n"
       "  obtain ⟨output, hcall', hdr, hcases⟩")],
     r"hinv\nhas type\n  sB'\.invariant = ok true\nbut is expected to have type\n  s'\.invariant = ok true\nin the application\n  And\.intro hinv",
     ['initiator_first_send_responder_successor_hypotheses']),
    ('module', 'relation-claimed-to-the-prepared-model',
     [(STEP_RELATION, "      SessionRefines dh oracleB.braidKem sB' (responderModelOf dh p) ∧\n")],
     r"hrel\nhas type\n  SessionRefines dh oracleB\.braidKem sB'\n    \(firstReceiptSession \(responderModelOf dh p\)[\s\S]*?but is expected to have type\n  SessionRefines dh oracleB\.braidKem sB' \(responderModelOf dh p\)", ['responder_first_frame_successor']),
    # statement-shape checks (each projects `initiator_first_send_responder_successor_hypotheses`)
    ('module', 'invariant-claimed-of-the-initiator-session',
     [(ADMISSIBLE_CALL, ADMISSIBLE_CALL.replace("invariant sB'", "invariant s'"))],
     r"has type\n  sB'\.invariant = ok true\nbut is expected to have type\n  s'\.invariant = ok true", ['initiator_first_send_responder_successor_admissible']),
    ('module', 'responder-call-on-the-plaintext-not-the-sent-bytes',
     [(ADMISSIBLE_CALL, ADMISSIBLE_CALL.replace('(alloc.vec.Vec.deref bytes)', 'plaintext'))],
     r'has type\n  lifecycle\.establish_responder rcB crcB ourB storeB plaintext rngB =[\s\S]*?but is expected to have type\n  lifecycle\.establish_responder rcB crcB ourB storeB bytes\.deref rngB =', ['initiator_first_send_responder_successor_admissible']),
    ('module', 'reach-invariant-claimed-of-the-initiator-session',
     [("      lifecycle.Session.invariant sB' = ok true ∧\n"
       "      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' := by\n"
       "  obtain ⟨oracle, bundle, rng0",
       "      lifecycle.Session.invariant s' = ok true ∧\n"
       "      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' := by\n"
       "  obtain ⟨oracle, bundle, rng0")],
     r"has type\n  sB'\.invariant = ok true\nbut is expected to have type\n  s'\.invariant = ok true\nin the application\n  And\.intro hinv", ['first_send_receive_successor_reachable']),
    # the definition, with the pins kept
    ('pinned', 'session-without-its-ratchet-key-pinned',
     [('    braid := ⟨tacenta_braid.State.NoHeaderReceived 1#u64 auth dec⟩\n'
       '    ratchet_private := rp }\n',
       '    braid := ⟨tacenta_braid.State.NoHeaderReceived 1#u64 auth dec⟩ }\n')],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleResponderSuccessor.receivedSession')),
]


# The theorems whose proofs compose the run.  Which theorem is a composing step and which only projects another's
# statement is decided by reading; the script holds the labels to each other, to where each control is refused and to
# a syntactic form of the projection standard (below).
COMPOSING = {
    'responder_first_frame_successor',
    'initiator_first_send_responder_successor_hypotheses',
}

# The controls labelled inside a composing proof, with the declaration each is refused in.  For each, the script also
# runs the changed copy with that theorem's proof replaced by `sorry` and requires Lean to accept the change there:
# the refusal is attributable to that proof.
INSIDE = {
    'composed-call-on-the-plaintext-not-the-sent-bytes': 'initiator_first_send_responder_successor_hypotheses',
}

# The controls refused in a composing proof where it places a conjunct of a called theorem's conclusion unchanged,
# with that called theorem: projections, labelled neither inside nor statement-shape and not probed.  Every other
# control refused in a composing proof must be labelled inside; `check_labels` holds both labels to the syntactic
# form of that standard (`passed_through`).
PROJECTION = {
    'composed-invariant-claimed-of-the-initiator-session': 'responder_first_frame_successor',
    'relation-claimed-to-the-prepared-model': 'responder_first_frame_inner_succeeds',
}

# The theorems a statement-shape check may project: the composing theorems.  The corollaries and the reach
# `first_send_receive_successor_reachable` apply `initiator_first_send_responder_successor_hypotheses` directly; there
# is no separate reach run in this module for them to project.
PROJECTED = set(COMPOSING)

# The statement-shape checks, with the theorem each projects.  For each, the script also runs the changed copy with
# that theorem's proof replaced by `sorry` and requires Lean still to refuse the change at its named place: the
# refusal does not depend on the projected theorem's proof.
STATEMENT_SHAPE = {
    'invariant-claimed-of-the-initiator-session': 'initiator_first_send_responder_successor_hypotheses',
    'responder-call-on-the-plaintext-not-the-sent-bytes': 'initiator_first_send_responder_successor_hypotheses',
    'reach-invariant-claimed-of-the-initiator-session': 'initiator_first_send_responder_successor_hypotheses',
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
    check_labels(without_pins(MODULE.read_text(), MODULE))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=900)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='responder-successor-logs-'))
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
    with tempfile.TemporaryDirectory(prefix='responder-successor-controls-') as tmp:
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
