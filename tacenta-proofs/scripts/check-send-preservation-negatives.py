#!/usr/bin/env python3
"""Hold the bridge between `Triple::invariant` and the model, and send preservation, against a planted fault.

`Translation/UnitTripleInvModel.lean` shows that at every code Triple that refines a model Triple, `Triple::invariant`
returns `true` exactly when `ModelTripleInv` holds of the model Triple.  `Translation/UnitLifecycleSendPreserve.lean`
shows that a successful `Session::encrypt` at an agreement state whose send takes no draw keeps `Session::invariant`
and spends one unit of a counter budget whose zero is `CounterHeadroom`, given the relation after the call, and on the
run of the initiator's first send gives the invariant and the four ceilings at the session the responder's reply
leaves.  A proof that Lean accepts after the fact it rests on is removed would hold nothing, so this script makes one
change to a copy of one of the two modules and requires Lean to refuse it, at a named place, with an error that names
what the change removed.

Seven controls are labelled inside the proofs that compose: the general step `encrypt_keeps_invariant_no_draw` (which
composes the bridge, the model's send, the agreement walk, the structural congruence and the budget) and the two
theorems on the run, and two are projections.  Each is a change to a composing theorem's statement.  A control refused
in a composing theorem is a projection when it is refused where that proof places a conjunct of a called theorem's
conclusion unchanged, and a composition step, labelled inside, otherwise.  The script holds each of the two labels to a
syntactic form of that standard read off the module (`passed_through`: the refusal names a hypothesis the proof binds
by destructuring a called theorem's conclusion, never rewrites, simplifies or substitutes, and places with a
constructor), and requires every control refused in a composing theorem to carry one of them.  For each inside control
it also runs the changed copy with that theorem's proof replaced by `sorry`, requiring Lean to accept the change there,
so the refusal is attributable to that proof.  That probe verifies attribution only: it cannot tell a composing step
from a projection.  That the syntactic form is the right standard, and that the three theorems named in `COMPOSING`
compose rather than project, is decided by reading.  The labels are also held consistent (an inside control must be
labelled with the declaration it is refused in and with a composing theorem; no control carries two labels; every place
a projection may be refused must be a composing theorem; a statement-shape check may not be refused in a composing
theorem, and the theorem it projects must be in `PROJECTED`), at start-up (at run time the script checks only that each
change is refused at its labelled place):

  * in `encrypt_keeps_invariant_no_draw`: the no-draw premise weakened to "takes no draw, or has not failed" (refused
    at the agreement walk, where the state is read as one whose send takes no draw); the key-pair clone record
    `KemCloneAgrees` swapped for the erasure clone record (refused where the agreement walk is applied); the budget
    claimed unspent, `CounterRoom s' (k + 1)` (refused where the model's budget step is carried back); the relation
    after the call claimed to the model session before the call instead of the model's step (refused where the bridge
    carries the model's send back: the step's Triple is the one the model's preservation is about).  The last is a
    true statement refused by the proof's dependence on the step's relation, not a false one;
  * in `initiator_first_send_responder_reply_successor`: the budget after the reply claimed for every `j` with
    `j + 1 < u32::MAX` (false: the clock after the reply is 1, so `j = u32::MAX - 2` has no room), and for `j + 2`
    further operations under the headline's bound (false at `j = u32::MAX - 4`); both are refused where the general
    step's result on the run (`key`) is applied;
  * in `established_encrypt_triple_invariant_via_preservation`: the establishment's law `DhPublicValid` swapped for
    `KemCiphertextLenOf` (refused where the establishment's invariant is taken, the first step of the re-derivation).

Two are projections, labelled neither inside nor statement-shape: the reply's call claimed from the source before the
receipt, and the session after the reply claimed to refine the model session before the send.  Both are refused in
`initiator_first_send_responder_reply_successor`, at the final term, where that theorem passes the call and the
relation of `initiator_first_send_responder_replies` through unchanged; they show that the headline forwards them, not
that it composes them, and no emptied-proof run is made for them.

Seven are on the leaf lemmas: the sparse send's frame claimed with an agreement output (refused in `spqr_send_frame`,
whose table is then the advanced one); the budget claimed kept with no unit to spend, `ModelCounterRoom m k` to
`ModelCounterRoom m' k`, which at `k = 0` is the claim that a send keeps the ceilings (refused at `omega` in
`modelCounterRoom_encrypt`, on the chain the send steps: a chain counter at `u64::MAX - 1` passes the ceilings and
steps to `u64::MAX`); `next_chunk` claimed to change the codewords (refused in `next_chunk_keeps`); the key-generation
state claimed to send without a draw (refused in `braid_send_no_draw`); the structural clauses claimed blind to the
sparse epoch (refused in `structural_congr`); and, in the bridge, `ModelTripleInv` without its roles clause (refused in
`triple_invariant_iff_model` at its final `rfl`: this shows the definition is used literally, not that the roles
clause carries content) and the sparse epoch window claimed as a plain sum instead of the code's saturating sum
(refused in `spqr_inv_iff_model`, where the window is carried across).

One is a statement-shape check: the corollary `initiator_first_send_responder_reply_admissible` claimed at the
initiator's session instead of the responder's (refused there because its statement no longer matches the
headline's; the script runs it again with the headline's proof replaced by `sorry` and requires the same refusal, so
it is refused whatever that proof does).  One holds a definition: `ModelTripleInv` regrouped, with the bridge's pins
kept (refused at the pin of `ModelTripleInv`).

Every change is to a statement or a definition; none replaces a proof step.  Each refusal is a proof-breakage check at
a named place: it shows that the proof there depends on what the change removed (or, for the last, that the pin holds
the definition), not that the changed statement is false.

The changes are checked on copies without the modules' pins, so that the refusal comes from a proof and not from a pin,
except the one kept with the bridge's pins.  The three unmodified copies (the bridge without its pins, the bridge with
them, the preservation module without its pins) must be accepted first.  A compiler that does not start, a syntax
error, an unrelated failure and a refusal elsewhere than the named place never count: the named refusal must be an
error at the named place that matches the expected message.  An error whose first line names a kind of failure that is
not a refusal (an unresolved name, a syntax error) voids the run anywhere in the copy, compared without regard to case.
A timeout (heartbeat or deterministic) never counts as the named refusal; one elsewhere in the copy is logged in the
result and does not void a separate matching error at the named place.  The script checks at start that the guard
fires on the toolchain's own `Unknown identifier`, on the kernel's `unknown constant`, on a parser's `unexpected token`
and `expected '...'`, on `unknown namespace` and on `does not contain`, each from a sample holding that spelling alone,
and not on an ordinary refusal, and that a heartbeat timeout is told apart from a refusal.  These are controls on copies
of the Lean; no source, olean or git state changes.  A copy of the preservation module imports the built bridge, not
the copy.

Dependencies must be built (`lake build Translation.UnitLifecycleResponderReply Translation.UnitTripleInvModel`).
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
BRIDGE = ROOT / 'translation/Translation/UnitTripleInvModel.lean'
MODULE = ROOT / 'translation/Translation/UnitLifecycleSendPreserve.lean'

NO_DRAW = ("    (hdraw : Model.Lifecycle.braidSendNeedsDraw m.braid = false)\n"
           "    (pt : Slice U8) (ptM : Model.Lifecycle.Bytes) (rng : R)\n")

KEEPS_HEAD = "theorem encrypt_keeps_invariant_no_draw (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees) {R : Type}\n"

KEEPS_TAIL = "    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by\n"

REPLY_CALL = ("      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧\n"
              "      lifecycle.Session.invariant sB'' = ok true ∧\n")

REPLY_MODEL = "          triple := replierAfterSend (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend)\n"

REL_AFTER = "    (hrel' : SessionRefines dh K s' (Model.Lifecycle.encrypt view oracle m ptM).session) :\n"

REPLY_BUDGET = "      (∀ j, j + 3 < Std.U32.max → CounterRoom sB'' j) ∧\n"

ADMISSIBLE_CALL = ("    (hcallR : lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', "
                   "rngR')) :\n")

SPQR_FRAME = ("theorem spqr_send_frame {st st' : Model.SparseRatchet.State} {e n : Nat} {key : Model.State.Key}\n"
              "    (hs : Model.SparseRatchet.sendDetailed st e none = .ok (st', n, key)) :\n")

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
    # inside the composing proofs
    ('module', 'no-draw-premise-weakened',
     [(NO_DRAW, NO_DRAW.replace("m.braid = false)", "m.braid = false ∨ m.braid ≠ .failed)"))],
     r"hdraw\nhas type\n  Model\.Lifecycle\.braidSendNeedsDraw m\.braid = false ∨ m\.braid ≠ Model\.Braid\.BraidState\.failed\nbut is expected to have type\n  Model\.Lifecycle\.braidSendNeedsDraw m\.braid = false\nin the application\n  sendsWithoutDraw_of_refines hrel\.braid hdraw", ['encrypt_keeps_invariant_no_draw']),
    ('module', 'key-pair-clone-record-swapped-for-the-erasure-one',
     [(KEEPS_HEAD, KEEPS_HEAD.replace("KemCloneAgrees)", "ErasureCloneAgrees)"))],
     r"hkcl\nhas type\n  SessionUnitBraidT3\.ErasureCloneAgrees\nbut is expected to have type\n  SessionUnitBraidT3\.KemCloneAgrees\nin the application\n  @braid_send_no_draw hkcl", ['encrypt_keeps_invariant_no_draw']),
    ('module', 'budget-claimed-unspent',
     [(KEEPS_TAIL, KEEPS_TAIL.replace("CounterRoom s' k", "CounterRoom s' (k + 1)"))],
     r"has type\n  CounterRoom s' k\nbut is expected to have type\n  CounterRoom s' \(k \+ 1\)", ['encrypt_keeps_invariant_no_draw']),
    ('module', 'reply-call-claimed-from-the-source-before-the-receipt',
     [(REPLY_CALL, REPLY_CALL.replace("sB' ptR rngR = ok", "sB' ptR rngB = ok"))],
     r"hcallR\nhas type\n  lifecycle\.Session\.encrypt rcB crcB sB' ptR rngR = ok \(core\.result\.Result\.Ok bytesR, sB'', rngR\)\nbut is expected to have type\n  lifecycle\.Session\.encrypt rcB crcB sB' ptR rngB = ok \(core\.result\.Result\.Ok bytesR, sB'', rngR\)", ['initiator_first_send_responder_reply_successor']),
    ('module', 'reply-session-claimed-to-refine-the-model-before-the-send',
     [(REPLY_MODEL, REPLY_MODEL.replace("replierAfterSend", "receiverAfterFirst"))],
     r"hrel''\nhas type\n  SessionRefines dh oracleB\.braidKem sB''[\s\S]*?replierAfterSend[\s\S]*?but is expected to have type[\s\S]*?receiverAfterFirst", ['initiator_first_send_responder_reply_successor']),
    ('module', 'first-send-establishment-law-swapped',
     [("    (hpub : DhPublicValid)\n    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape",
       "    (hpub : KemCiphertextLenOf)\n    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape")],
     r"hpub\nhas type\n[\s\S]*?but is expected to have type\n  DhPublicValid\nin the application\n  UnitLifecycleEstablishInitiatorShape\.establish_initiator_for_admissible rcE crcE hpub", ['established_encrypt_triple_invariant_via_preservation']),
    ('module', 'relation-after-the-call-claimed-to-the-model-before-it',
     [(REL_AFTER, REL_AFTER.replace("(Model.Lifecycle.encrypt view oracle m ptM).session", "m"))],
     r"hmodel'\nhas type\n  ModelTripleInv m'\.triple\nbut is expected to have type\n  ModelTripleInv m\.triple\nin the application\n  \(triple_invariant_iff_model hrel'\.triple\)\.mpr hmodel'", ['encrypt_keeps_invariant_no_draw']),
    ('module', 'reply-budget-claimed-beyond-the-clock',
     [(REPLY_BUDGET, REPLY_BUDGET.replace("j + 3 <", "j + 1 <"))],
     r"hj\nhas type\n  j \+ 1 < U32\.max\nbut is expected to have type\n  j \+ 3 < U32\.max\nin the application\n  key j hj", ['initiator_first_send_responder_reply_successor']),
    ('module', 'reply-budget-claimed-two-operations-longer',
     [(REPLY_BUDGET, REPLY_BUDGET.replace("CounterRoom sB'' j)", "CounterRoom sB'' (j + 2))"))],
     r"\(key j hj\)\.right\nhas type\n  CounterRoom sB'' j\nbut is expected to have type\n  CounterRoom sB'' \(j \+ 2\)", ['initiator_first_send_responder_reply_successor']),
    # leaf lemmas
    ('module', 'sparse-send-frame-claimed-with-an-agreement-output',
     [(SPQR_FRAME, SPQR_FRAME.replace("{key : Model.State.Key}\n", "{key : Model.State.Key}\n    (o : Model.SparseRatchet.Output)\n")
                             .replace("st e none", "st e (some o)"))],
     r"Did not find an occurrence of the pattern\n  Model\.SparseRatchet\.findChains st e\nin the target expression\n  \(match Model\.SparseRatchet\.advanceDetailed st o with", ['spqr_send_frame']),
    ('module', 'budget-claimed-kept-without-a-unit-to-spend',
     [("(k : Nat) (h : ModelCounterRoom m (k + 1)) :\n", "(k : Nat) (h : ModelCounterRoom m k) :\n")],
     r"omega could not prove the goal:[\s\S]*?:= ↑ch0\.n", ['modelCounterRoom_encrypt']),
    ('module', 'next-chunk-claimed-to-change-the-codewords',
     [("    enc'.chunks = enc.chunks ∧ tacenta_erasure.Encoder.invariant enc' = tacenta_erasure.Encoder.invariant enc := by\n",
       "    enc'.chunks ≠ enc.chunks ∧ tacenta_erasure.Encoder.invariant enc' = tacenta_erasure.Encoder.invariant enc := by\n")],
     r"rfl\nhas type\n  \?m\.\d+ = \?m\.\d+\nbut is expected to have type\n  enc\.chunks ≠ enc\.chunks", ['next_chunk_keeps']),
    ('module', 'key-generation-state-claimed-to-send-without-a-draw',
     [("  | .KeysUnsampled _ _ => False\n", "  | .KeysUnsampled _ _ => True\n")],
     r"hnd\nhas type\n  SendsWithoutDraw \{ state := tacenta_braid\.State\.KeysUnsampled e a \}\.state\nbut is expected to have type\n  False", ['braid_send_no_draw']),
    ('module', 'structural-clauses-claimed-blind-to-the-sparse-epoch',
     [("    (hep : t.post_quantum.epoch = s.triple.post_quantum.epoch)\n",
       "    (hep : t.post_quantum.epoch = s.triple.post_quantum.epoch ∨ True)\n")],
     r"unsolved goals\n[\s\S]*?hep : t\.post_quantum\.epoch = s\.triple\.post_quantum\.epoch ∨ True", ['structural_congr']),
    ('bridge', 'bridge-without-its-roles-clause',
     [("  ModelRatchetInv m.classical ∧ ModelSpqrInv m.postQuantum ∧ ModelRolesAgree m\n",
       "  ModelRatchetInv m.classical ∧ ModelSpqrInv m.postQuantum\n")],
     r"Tactic `rfl` failed: The left-hand side\n  ModelRatchetInv m\.classical ∧ ModelSpqrInv m\.postQuantum ∧ ModelRolesAgree m\nis not definitionally equal to the right-hand side\n  ModelTripleInv m", ['triple_invariant_iff_model']),
    ('bridge', 'sparse-window-claimed-without-the-saturation',
     [("    m.epoch < min Model.SparseRatchet.u64Max (q.1 + Model.SparseRatchet.epochsKept)\n",
       "    m.epoch < q.1 + Model.SparseRatchet.epochsKept\n")],
     r"Did not find an occurrence of the pattern\n  min Model\.SparseRatchet\.u64Max \(↑\?e \+ Model\.SparseRatchet\.epochsKept\)\nin the target expression\n  ↑q\.1 ≤ ↑s\.epoch ∧ ↑s\.epoch < ↑q\.1 \+ Model\.SparseRatchet\.epochsKept", ['spqr_inv_iff_model']),
    # statement-shape check (projects `initiator_first_send_responder_reply_successor`)
    ('module', 'reply-admissible-claimed-of-the-initiator-session',
     [(ADMISSIBLE_CALL, ADMISSIBLE_CALL.replace("crcB sB' ptR", "crcB s' ptR"))],
     r"Did not find an occurrence of the pattern\n  lifecycle\.Session\.encrypt rcB crcB s' ptR rngR\nin the target expression\n  lifecycle\.Session\.encrypt rcB crcB sB' ptR rngR", ['initiator_first_send_responder_reply_admissible']),
    # the definition, with the pins kept
    ('pinned', 'model-triple-invariant-regrouped-pinned',
     [("  ModelRatchetInv m.classical ∧ ModelSpqrInv m.postQuantum ∧ ModelRolesAgree m\n",
       "  (ModelRatchetInv m.classical ∧ ModelSpqrInv m.postQuantum) ∧ ModelRolesAgree m\n")],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitTripleInvModel.ModelTripleInv')),
]

COMPOSING = {
    'encrypt_keeps_invariant_no_draw',
    'initiator_first_send_responder_reply_successor',
    'established_encrypt_triple_invariant_via_preservation',
}

# The controls labelled inside a composing proof, with the declaration each is refused in.  For each, the script also
# runs the changed copy with that theorem's proof replaced by `sorry` and requires Lean to accept the change there:
# the refusal is attributable to that proof.
INSIDE = {
    'no-draw-premise-weakened': 'encrypt_keeps_invariant_no_draw',
    'key-pair-clone-record-swapped-for-the-erasure-one': 'encrypt_keeps_invariant_no_draw',
    'budget-claimed-unspent': 'encrypt_keeps_invariant_no_draw',
    'relation-after-the-call-claimed-to-the-model-before-it': 'encrypt_keeps_invariant_no_draw',
    'reply-budget-claimed-beyond-the-clock': 'initiator_first_send_responder_reply_successor',
    'reply-budget-claimed-two-operations-longer': 'initiator_first_send_responder_reply_successor',
    'first-send-establishment-law-swapped': 'established_encrypt_triple_invariant_via_preservation',
}

# The controls refused in a composing proof where it places a conjunct of a called theorem's conclusion unchanged,
# with that called theorem: projections, labelled neither inside nor statement-shape and not probed (the called
# theorem lives in another module).  Every other control refused in a composing proof must be labelled inside;
# `check_labels` holds both labels to the syntactic form of that standard (`passed_through`).
PROJECTION = {
    'reply-call-claimed-from-the-source-before-the-receipt': 'initiator_first_send_responder_replies',
    'reply-session-claimed-to-refine-the-model-before-the-send': 'initiator_first_send_responder_replies',
}

# The theorems a statement-shape check may project: the composing theorems.
PROJECTED = set(COMPOSING)

# The statement-shape checks, with the theorem each projects.  For each, the script also runs the changed copy with
# that theorem's proof replaced by `sorry` and requires Lean still to refuse the change at its named place: the
# refusal does not depend on the projected theorem's proof.
STATEMENT_SHAPE = {
    'reply-admissible-claimed-of-the-initiator-session': 'initiator_first_send_responder_reply_successor',
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
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='send-preservation-logs-'))
    logs.mkdir(parents=True, exist_ok=True)
    bridge = BRIDGE.read_text()
    module = MODULE.read_text()
    sources = {
        'bridge': without_pins(bridge, BRIDGE),
        'pinned': bridge,
        'module': without_pins(module, MODULE),
    }
    results = {
        'bridge_sha256': hashlib.sha256(bridge.encode()).hexdigest(),
        'module_sha256': hashlib.sha256(module.encode()).hexdigest(),
        'accepted': [], 'rejected': {},
    }
    with tempfile.TemporaryDirectory(prefix='send-preservation-controls-') as tmp:
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
                results['rejected'][f'{label}/{name}']['forwards'] = PROJECTION[name]
                print(f'PASS: {label}/{name} is a projection of {PROJECTION[name]}, refused where {place} forwards it',
                      flush=True)
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
    shape = sum(1 for k, r in results['rejected'].items() if k.split('/', 1)[1] in STATEMENT_SHAPE)
    projections = sum(1 for k, r in results['rejected'].items() if k.split('/', 1)[1] in PROJECTION)
    print(f'{len(results["accepted"])} unmodified copies accepted, {len(results["rejected"])} changes '
          f'refused at their named places, {inside} of them labelled inside a composing proof (accepted there with '
          f'that proof emptied) and {shape} labelled statement-shape (still refused with the projected proof '
          f'emptied) and {projections} labelled projections; logs: {logs}', flush=True)


if __name__ == '__main__':
    sys.exit(main())
