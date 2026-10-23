#!/usr/bin/env python3
"""Hold the responder's second reply against a planted fault.

`Translation/UnitLifecycleResponderSecondSend.lean` takes the responder's next operation after its receipt of the
initiator's second message (`responder_receives_second_message`), on the same run: its public `Session::encrypt` at the
session `sB'''` that receipt returned, from the source the receipt left.  `responder_sends_second_reply` composes the
receipt, the associated data its model session carries (from `initiator_first_send_responder_replies` on the same reply
call), the encrypt refinement at `sB'''` (`responder_second_send_refines`), the model's one outcome there
(`second_reply_model_step`), the walk of the agreement's send at `NoHeaderReceived`, send preservation for the invariant
and the ceilings after the call, and the budget read off the model session after the step;
`first_send_second_reply_reachable` builds one run at the real constants and applies it.  A proof that Lean accepts
after the fact it rests on is removed would hold nothing, so this script makes one change to a copy of the module and
requires Lean to refuse it, at a named place, with an error that names what the change removed.

The script labels each control by where it is refused: inside a composing proof (the theorems named in `COMPOSING`,
decided by reading), a projection (refused where a composing proof places a conjunct of a called theorem's conclusion
unchanged), on a leaf lemma, or at a pin.  It holds the inside and projection labels, once at start-up, to a syntactic
form of that standard read off the module (`passed_through`), requires every control refused in a composing theorem to
carry one of them, and holds the labels consistent with each other and with where each control is refused (at run time
it checks only that each change is refused at its labelled place).  What a run establishes is that each control is
refused at its named place, and that each control it runs against a composing proof is accepted there when that proof is
replaced by `sorry` (attribution to that proof, nothing more).  The labels and the per-class counts in
`negatives-control-counts.json` are the script's own labelling and are guidance, not a claim: the helper that tells
inside from projection reads Lean's error text and can read some projections as composition steps
(`ASSURANCE-OBLIGATIONS.md` records the decision, not built).  The controls, by where they are refused:

  * in `responder_sends_second_reply`: the second reply's call claimed to return the source the reply left instead of
    the one the receipt left, and claimed at the session before the receipt (both refused where the call, its source
    rewritten by the walk of the agreement's send, is placed); the session after the call claimed equal to the one
    before, the Triple unwritten (refused where the walk's frame equation is placed); the frame claimed to carry the
    initiator's new ratchet key instead of the responder's, and claimed sealed on the sparse chain the responder
    receives on (both refused where the model step's frame is rewritten into the code's bytes); the relation after the
    call claimed with the Triple the receipt left (refused where the relation, rewritten through the model step's
    outcome, is placed); the budget after the call claimed for every `j` with `j + 2 < u32::MAX` (refused where the
    model session's budget is read off at `j`; false of the code by reading, the clock after the call being 2); the
    ceilings after the call claimed as one unit of room (`CounterRoom sB4 1`, true by the budget conjunct; refused where
    the send-preservation step's budget at `k = 0` is placed, so it shows that the ceilings conjunct is that step's
    output); and `Session::invariant` claimed of the session before the call (true too; refused where the headline places
    the send-preservation step's invariant conjunct unchanged, so it shows only that the invariant conjunct is that
    step's, by forwarding); the initiator's receipt of the reply claimed to return the second plaintext (refused where
    the headline places that conjunct of `responder_receives_second_message` unchanged);
  * in `first_send_second_reply_reachable`: the responder's 32 further bytes claimed to be 31 (refused where the
    responder's source is read as two draws), the law `DhPublicNotConstant` swapped for `DhAgreeSymmetric` (refused where
    the initiator's further bytes are chosen by it, so that its new ratchet key is not its first), the second reply's
    plaintext bound claimed as `2^32` bytes (refused where the headline's plaintext bound is discharged from it), and the
    run's definition, in the copy without pins, claimed with the second reply returning the source the reply left
    (refused where the reach places that conjunct of `responder_sends_second_reply` unchanged);
  * in the leaf lemmas: the responder's Triple after the second reply claimed with message number 0
    (`second_reply_send_key`), the model's step claimed to take a draw and the composite header claimed with agreement
    type `hdr` (`second_reply_model_step`), the model budget after the second reply claimed for every `k` with
    `k + 2 < u32::MAX` (`modelCounterRoom_secondReplier`), and the encrypt refinement claimed from the Triple's invariant
    alone instead of `Session::invariant` (`responder_second_send_refines`);
  * at a pin, with the module's pins kept: `SecondReplyRun` with `Session::invariant` after the second reply replaced by
    `True`, and `secondReplyFrame` with the encoded header dropped from its associated data.  Both definitions are also
    held without the pins: the first change is refused in the reach (a structural refusal: the reach places the
    invariant where `True` is expected), the second in `second_reply_model_step` (the model's `encrypt` binds the encoded
    header into the associated data).  So these two controls show that the pins hold the definitions, not that the pins
    are needed for it.  There is no statement-shape check.

Every change is to a statement or a definition; none replaces a proof step.  Each refusal is a proof-breakage check at
a named place: it shows that the proof there depends on what the change removed (or, for the pin controls, that the pin
holds the definition), not that the changed statement is false.  None shows anything about the initiator's receipt of
the second reply, a refused `encrypt`, a tampered frame or a later step.

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
apart from a refusal.  At the end, `check_complete` refuses a run that did not run every control, baseline and
emptied-proof run once, counted from `RUNS`, which `run_lean` alone writes.  These are controls on copies of the
Lean; no source, olean or git state changes.

The helpers from `BINDER` to `check_complete` are shared, character for character, with the other lifecycle
negatives scripts and with this template; `check-negatives-control-counts.py` holds them to one text, compares the
number of controls in each class with `negatives-control-counts.json` (edit the script's entry there in the change
that adds, removes or relabels a control), and reads `main`.

Dependencies must be built (`lake build Translation.UnitLifecycleResponderSecondReceipt`).
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
MODULE = ROOT / 'translation/Translation/UnitLifecycleResponderSecondSend.lean'

CALL = "      lifecycle.Session.encrypt rcB crcB sB''' ptR2 rngR2 = ok (core.result.Result.Ok bytesR2, sB4, rngR2) ∧\n"

WRITES = "      sB4 = { sB''' with triple := sB4.triple } ∧\n"

FRAME = """      vecOf bytesR2 = secondReplyFrame oracleB (vecOf q.identityAd) (oracleB.dhPublic dB2)
        (secondReplyKey (arrayOf ec) (arrayOf q.sparseReceive) (arrayOf q.dhOut) dSend x z) (sliceOf ptR2) ∧
"""

RELATION = "          triple := responderAfterSecondSend (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend)\n"

BUDGET = "      (∀ j, j + 3 < Std.U32.max → CounterRoom sB4 j) := by\n"

AFTER = "      lifecycle.Session.invariant sB4 = ok true ∧ CounterHeadroom sB4 ∧\n"

RECEIPT_PT = "        ok (core.result.Result.Ok ptA, s'', rngA') ∧ ptA.val = ptR.val ∧\n"

EXTRA = "    (extraB : List Std.U8) (hextraB : extraB.length = 32)\n"

LAWS = "    (hcon : DhAgreeContributory) (haead : AeadRoundTrip) (hnc : DhPublicNotConstant)\n"

BOUND = "    (ptR2 : Slice Std.U8) (hptR2 : ptR2.val.length ≤ 4096) :\n"

RUN_CALL = ("    lifecycle.Session.encrypt byteRng byteCrc sB''' ptR2 rngR2 = ok (core.result.Result.Ok bytesR2, sB4, "
            "rngR2) ∧\n")

RUN_INVARIANT = "    lifecycle.Session.invariant sB4 = ok true ∧ CounterHeadroom sB4\n"

MODEL_TRIPLE = "        ns := 1, nr := 1, pn := 1, skipped := [], events := 2, labels := .tacenta }\n"

MODEL_STEP = "        oracle := oracle } := by\n"

COMPOSITE = "    agType := .none\n"

MODEL_BUDGET = "    (hk : k + 3 < Std.U32.max) :\n"

REFINES_INV = "    (hinv : lifecycle.Session.invariant sB = ok true) (hc : CounterHeadroom sB)\n"

FRAME_AD = "      (Model.Messages.concatAd ad (Model.CompositeHeader.encode (secondReplyComposite newPub2))))\n"

HEAD = 'responder_sends_second_reply'
REACH = 'first_send_second_reply_reachable'

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`, or ('pin', name, 'check') for that of
#  its statement pin `#check @name`)
MUTANTS = [
    # inside the composing proofs
    ('module', 'second-reply-claimed-to-return-the-source-the-reply-left',
     [(CALL, CALL.replace("sB4, rngR2) ∧", "sB4, rngR) ∧"))],
     r"hcallR2\nhas type\n  lifecycle\.Session\.encrypt rcB crcB sB''' ptR2 rngR2 = ok \(core\.result\.Result\.Ok bytesR2, sB4, rngR2\)\nbut is expected to have type\n  lifecycle\.Session\.encrypt rcB crcB sB''' ptR2 rngR2 = ok \(core\.result\.Result\.Ok bytesR2, sB4, rngR\)\nin the application\n  And\.intro hcallR2",
     [HEAD]),
    ('module', 'second-reply-claimed-at-the-session-before-the-receipt',
     [(CALL, CALL.replace("crcB sB''' ptR2", "crcB sB'' ptR2"))],
     r"hcallR2\nhas type\n  lifecycle\.Session\.encrypt rcB crcB sB''' ptR2 rngR2 = ok \(core\.result\.Result\.Ok bytesR2, sB4, rngR2\)\nbut is expected to have type\n  lifecycle\.Session\.encrypt rcB crcB sB'' ptR2 rngR2 = ok \(core\.result\.Result\.Ok bytesR2, sB4, rngR2\)\nin the application\n  And\.intro hcallR2",
     [HEAD]),
    ('module', 'second-reply-claimed-to-write-nothing',
     [(WRITES, "      sB4 = sB''' ∧\n")],
     r"unsolved goals\ncase Ok\.refine_1\n[\s\S]*?⊢ \{ triple := _cand, braid := sB'''\.braid, [\s\S]*?\} =\n    sB'''\n",
     [HEAD]),
    ('module', 'second-reply-frame-claimed-with-the-initiator-key',
     [(FRAME, FRAME.replace("(vecOf q.identityAd) (oracleB.dhPublic dB2)", "(vecOf q.identityAd) (oracle.dhPublic dA)"))],
     r"unsolved goals\ncase Ok\.refine_2\n[\s\S]*?⊢ secondReplyFrame oracleB \(vecOf q\.identityAd\) \(oracleB\.dhPublic dB2\)\n[\s\S]*? =\n    secondReplyFrame oracleB \(vecOf q\.identityAd\) \(oracle\.dhPublic dA\)\n",
     [HEAD]),
    ('module', 'second-reply-frame-claimed-on-the-receiving-sparse-chain',
     [(FRAME, FRAME.replace("(arrayOf q.sparseReceive)", "(arrayOf q.sparseSend)"))],
     r"unsolved goals\ncase Ok\.refine_2\n[\s\S]*?⊢ secondReplyFrame oracleB \(vecOf q\.identityAd\) \(oracleB\.dhPublic dB2\)\n[\s\S]*? =\n    secondReplyFrame oracleB \(vecOf q\.identityAd\) \(oracleB\.dhPublic dB2\)\n      \(secondReplyKey \(arrayOf ec\) \(arrayOf q\.sparseSend\)",
     [HEAD]),
    ('module', 'second-reply-relation-claimed-with-the-receipt-triple',
     [(RELATION, RELATION.replace("triple := responderAfterSecondSend",
                                  "triple := Tacenta.UnitLifecycleResponderSecondReceipt.responderAfterSecond"))],
     r"hsess4\nhas type\n  SessionRefines dh oracleB\.braidKem sB4\n[\s\S]*?responderAfterSecondSend \(arrayOf ec\)[\s\S]*?but is expected to have type\n[\s\S]*?UnitLifecycleResponderSecondReceipt\.responderAfterSecond \(arrayOf ec\)[\s\S]*?in the application\n  And\.intro hsess4",
     [HEAD]),
    ('module', 'budget-after-the-second-reply-claimed-beyond-the-clock',
     [(BUDGET, BUDGET.replace("j + 3 <", "j + 2 <"))],
     r"hj\nhas type\n  j \+ 2 < U32\.max\nbut is expected to have type\n  j \+ 3 < U32\.max\nin the application\n  modelCounterRoom_secondReplier",
     [HEAD]),
    ('module', 'ceilings-after-the-second-reply-claimed-with-a-unit-of-room',
     [(AFTER, AFTER.replace("CounterHeadroom sB4 ∧", "Tacenta.UnitLifecycleSendPreserve.CounterRoom sB4 1 ∧"))],
     r"\(UnitLifecycleSendPreserve\.counterRoom_zero sB4\)\.mp hroom4\nhas type\n  CounterHeadroom sB4\nbut is expected to have type\n  CounterRoom sB4 1\nin the application\n  And\.intro",
     [HEAD]),
    ('module', 'reach-responder-extra-bytes-claimed-shorter',
     [(EXTRA, EXTRA.replace("extraB.length = 32", "extraB.length = 31"))],
     r"hextraB\nhas type\n  extraB\.length = 31\nbut is expected to have type\n  extraB\.length = 32\nin the application\n  byteTrace_pair seedB extraB hseedB hextraB",
     [REACH]),
    ('module', 'reach-fresh-key-law-swapped',
     [(LAWS, LAWS.replace("(hnc : DhPublicNotConstant)", "(hnc : DhAgreeSymmetric)"))],
     r"hnc\nhas type\n  DhAgreeSymmetric\nbut is expected to have type\n  DhPublicNotConstant\nin the application\n  dhPublicNotConstant_is\.mp hnc",
     [REACH]),
    ('module', 'reach-second-reply-plaintext-bound-claimed-wider',
     [(BOUND, BOUND.replace("ptR2.val.length ≤ 4096", "ptR2.val.length ≤ 4294967296"))],
     r"omega could not prove the goal:\na possible counterexample may satisfy the constraints\n[\s\S]*?\n  0 ≤ \w+ ≤ 4294967296\n",
     [REACH]),
    # projections
    ('module', 'reply-receipt-claimed-to-return-the-second-plaintext',
     [(RECEIPT_PT, RECEIPT_PT.replace("ptA.val = ptR.val", "ptA.val = ptS.val"))],
     r"hptA\nhas type\n  ↑ptA = ↑ptR\nbut is expected to have type\n  ↑ptA = ↑ptS\nin the application\n  And\.intro hptA",
     [HEAD]),
    ('module', 'run-claimed-with-the-second-reply-returning-the-source-the-reply-left',
     [(RUN_CALL, RUN_CALL.replace("sB4, rngR2) ∧", "sB4, rngB') ∧"))],
     r"hcallR2\nhas type\n  lifecycle\.Session\.encrypt byteRng byteCrc sB''' ptR2 rngR2 = ok \(core\.result\.Result\.Ok bytesR2, sB4, rngR2\)\nbut is expected to have type\n  lifecycle\.Session\.encrypt byteRng byteCrc sB''' ptR2 rngR2 = ok \(core\.result\.Result\.Ok bytesR2, sB4, rngB'\)\nin the application\n  And\.intro hcallR2",
     [REACH]),
    ('module', 'invariant-after-the-second-reply-claimed-of-the-session-before-it',
     [(AFTER, AFTER.replace("invariant sB4 = ok true", "invariant sB''' = ok true"))],
     r"hinv4\nhas type\n  sB4\.invariant = ok true\nbut is expected to have type\n  sB'''\.invariant = ok true\nin the application\n  And\.intro hinv4",
     [HEAD]),
    # leaf lemmas
    ('module', 'model-triple-after-the-second-reply-claimed-with-message-number-zero',
     [(MODEL_TRIPLE, MODEL_TRIPLE.replace("ns := 1,", "ns := 0,"))],
     r"unsolved goals\nec prk k1 k2 d dSend candA xB z newPub2 : Key\n⊢ False",
     ['second_reply_send_key']),
    ('module', 'model-second-reply-claimed-to-take-a-draw',
     [(MODEL_STEP, "        oracle := { oracle with draws := oracle.draws.drop 1 } } := by\n")],
     r"unsolved goals\n[\s\S]*?⊢ oracle =\n    \{ draws := oracle\.draws\.tail, ",
     ['second_reply_model_step']),
    ('module', 'second-reply-composite-claimed-with-agreement-type-hdr',
     [(COMPOSITE, "    agType := .hdr\n")],
     r"unsolved goals\n[\s\S]*?agType := Model\.CompositeHeader\.AgreementType\.none, agChunk := none \}\)\)\) =\n    Model\.CompositeHeader\.encodeMessage\n      \{ dh := newPub2, pn := 1, n := 0, pqEpoch := 0, pqN := 2, agEpoch := 1,\n        agType := Model\.CompositeHeader\.AgreementType\.hdr, ",
     ['second_reply_model_step']),
    ('module', 'model-budget-after-the-second-reply-claimed-beyond-the-clock',
     [(MODEL_BUDGET, MODEL_BUDGET.replace("k + 3 <", "k + 2 <"))],
     r"omega could not prove the goal:\na possible counterexample may satisfy the constraints\n  0 ≤ a ≤ 4294967292\n  a ≥ 4294967292\nwhere\n a := ↑k",
     ['modelCounterRoom_secondReplier']),
    ('module', 'refinement-claimed-from-the-triple-invariant-alone',
     [(REFINES_INV, REFINES_INV.replace("(hinv : lifecycle.Session.invariant sB = ok true)",
                                        "(hinv : tacenta_triple.State.invariant sB.triple = ok true)"))],
     r"hinv\nhas type\n  sB\.triple\.invariant = ok true\nbut is expected to have type\n  sB\.invariant = ok true\nin the application\n  UnitLifecycleInitiatorSecondSend\.encryptProviders_of_invariant",
     ['responder_second_send_refines']),
    # the definitions, with the pins kept
    ('pinned', 'second-reply-run-without-the-invariant-pinned',
     [(RUN_INVARIANT, RUN_INVARIANT.replace("lifecycle.Session.invariant sB4 = ok true ∧", "True ∧"))],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleResponderSecondSend.SecondReplyRun')),
    ('pinned', 'second-reply-frame-without-the-header-in-its-associated-data-pinned',
     [(FRAME_AD, "      (Model.Messages.concatAd ad []))\n")],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleResponderSecondSend.secondReplyFrame')),
]

COMPOSING = {
    HEAD,
    REACH,
}

# The controls labelled inside a composing proof, with the declaration each is refused in.  For each, the script also
# runs the changed copy with that theorem's proof replaced by `sorry` and requires Lean to accept the change there:
# the refusal is attributable to that proof.
INSIDE = {
    'second-reply-claimed-to-return-the-source-the-reply-left': HEAD,
    'second-reply-claimed-at-the-session-before-the-receipt': HEAD,
    'second-reply-claimed-to-write-nothing': HEAD,
    'second-reply-frame-claimed-with-the-initiator-key': HEAD,
    'second-reply-frame-claimed-on-the-receiving-sparse-chain': HEAD,
    'second-reply-relation-claimed-with-the-receipt-triple': HEAD,
    'budget-after-the-second-reply-claimed-beyond-the-clock': HEAD,
    'ceilings-after-the-second-reply-claimed-with-a-unit-of-room': HEAD,
    'reach-responder-extra-bytes-claimed-shorter': REACH,
    'reach-fresh-key-law-swapped': REACH,
    'reach-second-reply-plaintext-bound-claimed-wider': REACH,
}

# The controls refused in a composing proof where it places a conjunct of a called theorem's conclusion unchanged,
# with that called theorem: projections, labelled neither inside nor statement-shape and not probed.  Every other
# control refused in a composing proof must be labelled inside; `check_labels` holds both labels to the syntactic form
# of that standard (`passed_through`).
PROJECTION = {
    'reply-receipt-claimed-to-return-the-second-plaintext': 'responder_receives_second_message',
    'run-claimed-with-the-second-reply-returning-the-source-the-reply-left': HEAD,
    'invariant-after-the-second-reply-claimed-of-the-session-before-it': 'encrypt_keeps_invariant_no_draw',
}

# The theorems a statement-shape check may project: the composing theorems.
PROJECTED = set(COMPOSING)

# The statement-shape checks, with the theorem each projects (none).
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
    if not MUTANTS:
        raise SystemExit('NO CONTROLS: MUTANTS is empty; a control with no planted change holds nothing')
    check_labels(without_pins(MODULE.read_text(), MODULE))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=900)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='responder-second-send-logs-'))
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
    with tempfile.TemporaryDirectory(prefix='responder-second-send-controls-') as tmp:
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
    check_complete(results, sources)
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
