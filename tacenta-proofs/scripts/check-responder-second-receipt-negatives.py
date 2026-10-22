#!/usr/bin/env python3
"""Hold the responder's receipt of the initiator's second message against a planted fault.

`Translation/UnitLifecycleResponderSecondReceipt.lean` takes the initiator's second message, on the run that ends in the
initiator's second `Session::encrypt` (`initiator_sends_second_message`), to the responder: its public `Session::decrypt`
at the session `sB''` its reply left.  `responder_receives_second_message_two_outcomes` composes the second message, the
reply's keys and relation at `sB''` (`initiator_first_send_responder_replies`, identified on the reply's call), the
invariant and the ceilings at `sB''`, the decrypt refinement at the responder's oracle and the model's outcomes there,
and excludes the outcomes its premises rule out; `responder_receives_second_message` adds the fresh-key premise and
applies the receive preservation at `sB''`; `second_receipt_reach_run` builds one run at the real constants and applies
both, and the two reaches take its fresh and its stale arm.  A proof that Lean accepts after the fact it rests on is
removed would hold nothing, so this script makes one change to a copy of the module and requires Lean to refuse it, at a
named place, with an error that names what the change removed.

The five theorems named in `COMPOSING` compose (decided by reading).  A control refused in a composing theorem is a
projection when it is refused where that proof places a conjunct of a called theorem's conclusion unchanged, and a
composition step, labelled inside, otherwise.  The script holds each of the two labels to a syntactic form of that
standard read off the module (`passed_through`: the refusal names a hypothesis the proof binds by destructuring a called
theorem's conclusion, never rewrites, simplifies or substitutes, and places with a constructor), and requires every
control refused in a composing theorem to carry one of them.  For each inside control it also runs the changed copy with
that theorem's proof replaced by `sorry`, requiring Lean to accept the change there, so the refusal is attributable to
that proof.  That probe verifies attribution only: it cannot tell a composing step from a projection.  That the syntactic
form is the right standard, and that the five theorems compose rather than project, is decided by reading.  The labels
are also held consistent (an inside control must be labelled with the declaration it is refused in and with a composing
theorem; no control carries two labels; every place a projection may be refused must be a composing theorem; a
statement-shape check may not be refused in a composing theorem, and the theorem it projects must be in `PROJECTED`), at
start-up (at run time the script checks only that each change is refused at its labelled place):

  * in `responder_receives_second_message_two_outcomes`: the responder's source after its reply claimed empty, so that no
    draw is there (refused where the run inputs of the decrypt refinement take the draw); the success arm's plaintext
    claimed to be the reply's (refused where the open's result is read back as the plaintext's bytes); the stale arm
    claimed to refuse `NoReceivingChain` instead of `OutOfOrder` (refused where the refusal the model step names is read
    back as the code's error); and the decoder after the receipt claimed to hold only the first header chunk (refused
    where the relation after the call, rewritten through the model step's outcome, is placed);
  * in `responder_receives_second_message`: the fresh-key premise claimed against the peer key the initiator holds
    instead of its own first ratchet key (refused where it excludes the stale arm); the budget after the receipt claimed
    for every `j` with `j + 2 < u32::MAX` (refused where the preservation step is applied to it; false of the code by
    reading, since the clock at `sB'''` is 2); and the budget claimed for `j + 1` further operations (refused where the
    preservation step's budget is placed);
  * in `second_receipt_reach_run`: the responder's 32 further bytes claimed to be 31 (refused where the responder's
    source is read as two draws) and the law `DhPublicNotConstant` swapped for `DhAgreeSymmetric` (refused where the
    responder's source is chosen by it);
  * in `first_send_second_receipt_reachable`: the same law swapped (refused where the reach chooses the initiator's
    further bytes by it, so that its new ratchet key is not its first);
  * in `first_send_second_receipt_stale_reachable`: the stale run's definition, in the copy without pins, claimed with the
    initiator's new ratchet key not its first (refused where the reach places the equation it derives from its first
    ratchet key's bytes and the oracle's public-key record).

Two are projections, labelled neither inside nor statement-shape: the initiator's second `encrypt` claimed at the session
before its receipt of the reply, refused in `responder_receives_second_message_two_outcomes` where it places the
conjunct of `initiator_sends_second_message` unchanged, and the initiator's receipt of the reply claimed to return the
second plaintext, refused in `responder_receives_second_message` where it places the conjunct of
`responder_receives_second_message_two_outcomes` unchanged.  They show that the composing theorems forward those
conjuncts, not that they compose them, and no emptied-proof run is made for them.

Four are on leaf lemmas: the model's receive of the second message on the peer key claimed to refuse `noReceivingChain`
(refused in `second_receive_stale`), the responder's Triple after the receipt claimed with previous chain length 0
(refused in `second_receive_key`), the decoder at the session `establish_responder` returns claimed empty (refused in
`established_responder_decoder_small`), and the in-order step claimed on a key that is not the reply's instead of one
that is not the peer key (refused in `secondReceipt_inOrderStep`).  Two hold definitions: `SecondReceiptStaleRun` with
`OutOfOrder` replaced by `NoReceivingChain`, and `SecondReceiptRun` with `Session::invariant` at `sB'''` replaced by
`True`, each with the module's pins kept (refused at that definition's pin).  There is no statement-shape check.

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
apart from a refusal.  These are controls on copies of the Lean; no source, olean or git state changes.

Dependencies must be built (`lake build Translation.UnitLifecycleInitiatorSecondMessage`).
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
MODULE = ROOT / 'translation/Translation/UnitLifecycleResponderSecondReceipt.lean'

DRAW = "    (hdrawB2 : traceB rngR = dB2 :: restB2)\n    (ptS : Slice Std.U8)"

PLAINTEXT = "          res = core.result.Result.Ok ptB2 ∧ ptB2.val = ptS.val ∧ sB'''.pending_initial = none ∧\n"

STALE = ("            (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.OutOfOrder)) ∧ "
         "sB''' = sB'') ∨\n")

DECODER = """              (.noHeaderReceived 1 (Model.Braid.Auth.init 1 (sliceOf p.braidSecret))
                (((Model.Braid.Decoder.new (Model.Braid.headerSize + Model.Braid.macSize)).addChunk
                  ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector,
                    0⟩).addChunk
                  ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩))
              (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
              (arrayOf q.dhOut) dSend (oracle.dhPublic dA) x z (oracleB.dhPublic dB2) dB2))) := by
"""

DECODER_ONE = """              (.noHeaderReceived 1 (Model.Braid.Auth.init 1 (sliceOf p.braidSecret))
                ((Model.Braid.Decoder.new (Model.Braid.headerSize + Model.Braid.macSize)).addChunk
                  ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector,
                    0⟩))
              (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
              (arrayOf q.dhOut) dSend (oracle.dhPublic dA) x z (oracleB.dhPublic dB2) dB2))) := by
"""

FRESH = "    (hfreshA : oracle.dhPublic dA ≠ arrayOf q.ratchetBytes)\n"

BUDGET = "      (∀ j, j + 3 < Std.U32.max → Tacenta.UnitLifecycleSendPreserve.CounterRoom sB''' j) := by\n"

SECOND_SEND = """      oracle.dhAgree dA (oracleB.dhPublic dB) = some x ∧
      SessionRefines dh oracleB.braidKem sB''
"""

SECOND_SEND_CALL = "      lifecycle.Session.encrypt rc crc s'' ptS rngA' = ok (core.result.Result.Ok bytes2, s''', rngA') ∧\n"

RECEIPT_PT = """        ok (core.result.Result.Ok ptA, s'', rngA') ∧ ptA.val = ptR.val ∧
      lifecycle.Session.encrypt rc crc s'' ptS rngA' = ok (core.result.Result.Ok bytes2, s''', rngA') ∧
      vecOf bytes2 = secondFrame view oracle (vecOf q.identityAd)
        (.keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
          ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩)
        (oracle.dhPublic dA) (secondKey (arrayOf q.rootKey) (arrayOf q.sparseSend) dSend x)
        ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩
        (sliceOf ptS) ∧
      oracle.dhAgree dA (oracleB.dhPublic dB) = some x ∧
      oracleB.dhAgree dB2"""

LAWS = """    (hcon : DhAgreeContributory) (haead : AeadRoundTrip) (hnc : DhPublicNotConstant)
    (ourA : lifecycle.Identity) (seed : List Std.U8) (hseed : seed.length = 64)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none)
    (extraB : List Std.U8) (hextraB : extraB.length = 32)
    (ptR : Slice Std.U8) (hptR : ptR.val.length ≤ 4096) (ptS : Slice Std.U8) (hptS : ptS.val.length ≤ 4096) :
"""

EXTRA = """    (extraB : List Std.U8) (hextraB : extraB.length = 32)
    (ptR : Slice Std.U8) (hptR : ptR.val.length ≤ 4096) (ptS : Slice Std.U8) (hptS : ptS.val.length ≤ 4096) :
"""

STALE_KEY = "    oracle.dhPublic (extra.map Tacenta.SessionUnitBraidT3.u8) = arrayOf q.ratchetBytes ∧\n"

MODEL_STALE = "        newPub2 none = .error (.classical .outOfOrder) := by\n"

MODEL_TRIPLE = "        ns := 0, nr := 1, pn := 1, skipped := [], events := 2, labels := .tacenta }\n"

DECODER_SMALL = ("    ∀ e a d, sB'.braid.state = tacenta_braid.State.NoHeaderReceived e a d → "
                 "d.«have».val.length ≤ 1 := by\n")

IN_ORDER = "    (hne : candA ≠ a4) (hcan : Model.Messages.canonicalKey candA = true) :\n"

STALE_RUN = """      ok (core.result.Result.Err (lifecycle.Error.Triple
        (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.OutOfOrder)), sB'', rngR2)

"""

RUN_INVARIANT = """    ptB2.val = ptS.val ∧
    lifecycle.Session.invariant sB''' = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB'''
"""

TWO = 'responder_receives_second_message_two_outcomes'
HEAD = 'responder_receives_second_message'
RUN = 'second_receipt_reach_run'
REACH = 'first_send_second_receipt_reachable'
STALE_REACH = 'first_send_second_receipt_stale_reachable'

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
    # inside the composing proofs
    ('module', 'responder-source-claimed-empty-after-the-reply',
     [(DRAW, DRAW.replace("traceB rngR = dB2 :: restB2", "traceB rngR = []"))],
     r"hdrawB2\nhas type\n  traceB rngR = \[\]\nbut is expected to have type\n  traceB rngR = dB2 :: restB2\nin the application\n  second_receipt_run_inputs",
     [TWO]),
    ('module', 'second-plaintext-claimed-to-be-the-reply',
     [(PLAINTEXT, PLAINTEXT.replace("ptB2.val = ptS.val", "ptB2.val = ptR.val"))],
     r"hres\nhas type\n[\s\S]*?but is expected to have type\n  List\.map SessionUnitBraidT3\.u8 ↑ptB2 = List\.map SessionUnitBraidT3\.u8 ↑ptR\nin the application\n  UnitLifecycleEstablishResponder\.map_u8_inj hres",
     [TWO]),
    ('module', 'stale-arm-claimed-to-refuse-no-receiving-chain',
     [(STALE, STALE.replace("RatchetError.OutOfOrder", "RatchetError.NoReceivingChain"))],
     r"unsolved goals[\s\S]*⊢ core\.result\.Result\.Err\n      \(lifecycle\.Error\.Triple \(tacenta_triple\.TripleError\.Classical tacenta_ratchet\.RatchetError\.OutOfOrder\)\) =\n    core\.result\.Result\.Err\n      \(lifecycle\.Error\.Triple \(tacenta_triple\.TripleError\.Classical tacenta_ratchet\.RatchetError\.NoReceivingChain\)\)",
     [TWO]),
    ('module', 'decoder-after-the-receipt-claimed-to-hold-only-the-first-chunk',
     [(DECODER, DECODER_ONE)],
     r"hsess\nhas type\n  SessionRefines dh oracleB2\.braidKem \(core\.result\.Result\.Ok ptB2, sB''', rngR2\)\.2\.1[\s\S]*?but is expected to have type\n[\s\S]*?\(\(Model\.Braid\.Decoder\.new \(Model\.Braid\.headerSize \+ Model\.Braid\.macSize\)\)\.addChunk\n          \{ source := headerSource oracle\.braidKem \(SessionUnitBraidT3\.AuthOf q\.auth\) ekSeed ekVector, index := 0 \}\)\)\n[\s\S]*?in the application\n  ⟨hs3, hsess⟩",
     [TWO]),
    ('module', 'fresh-key-premise-claimed-against-the-peer-key',
     [(FRESH, FRESH.replace("q.ratchetBytes", "q.peerRatchetBytes"))],
     r"hfreshA\nhas type\n  oracle\.dhPublic dA ≠ arrayOf q\.peerRatchetBytes\nbut is expected to have type\n  ¬oracle\.dhPublic dA = arrayOf q\.ratchetBytes\nin the application\n  absurd hstale hfreshA",
     [HEAD]),
    ('module', 'budget-after-the-receipt-claimed-beyond-the-clock',
     [(BUDGET, BUDGET.replace("j + 3 <", "j + 2 <"))],
     r"hj\nhas type\n  j \+ 2 < U32\.max\nbut is expected to have type\n  j \+ 3 < U32\.max\nin the application\n  key j hj",
     [HEAD]),
    ('module', 'budget-after-the-receipt-claimed-one-operation-longer',
     [(BUDGET, BUDGET.replace("CounterRoom sB''' j)", "CounterRoom sB''' (j + 1))"))],
     r"\(key j hj\)\.right\nhas type\n  UnitLifecycleSendPreserve\.CounterRoom sB''' j\nbut is expected to have type\n  UnitLifecycleSendPreserve\.CounterRoom sB''' \(j \+ 1\)",
     [HEAD]),
    ('module', 'run-responder-extra-bytes-claimed-shorter',
     [(EXTRA + "    ∃ (bundle", (EXTRA + "    ∃ (bundle").replace("extraB.length = 32", "extraB.length = 31"))],
     r"hextraB\nhas type\n  extraB\.length = 31\nbut is expected to have type\n  extraB\.length = 32\nin the application\n  byteTrace_pair seedB extraB hseedB hextraB",
     [RUN]),
    ('module', 'run-fresh-key-law-swapped',
     [(LAWS + "    ∃ (bundle", (LAWS + "    ∃ (bundle").replace("(hnc : DhPublicNotConstant)", "(hnc : DhAgreeSymmetric)"))],
     r"hnc\nhas type\n  DhAgreeSymmetric\nbut is expected to have type\n  DhPublicNotConstant\nin the application\n  dhPublicNotConstant_is\.mp hnc",
     [RUN]),
    ('module', 'reach-fresh-key-law-swapped',
     [(LAWS + "    SecondReceiptRun K", (LAWS + "    SecondReceiptRun K").replace("(hnc : DhPublicNotConstant)",
                                                                             "(hnc : DhAgreeSymmetric)"))],
     r"hnc\nhas type\n  DhAgreeSymmetric\nbut is expected to have type\n  DhPublicNotConstant\nin the application\n  dhPublicNotConstant_is\.mp hnc",
     [REACH]),
    ('module', 'stale-run-claimed-on-a-fresh-key',
     [(STALE_KEY, STALE_KEY.replace("= arrayOf q.ratchetBytes ∧", "≠ arrayOf q.ratchetBytes ∧"))],
     r"hsame\nhas type\n  oracle\.dhPublic \(List\.map SessionUnitBraidT3\.u8 ↑sec\) = arrayOf q\.ratchetBytes\nbut is expected to have type\n  oracle\.dhPublic \(List\.map SessionUnitBraidT3\.u8 ↑sec\) ≠ arrayOf q\.ratchetBytes\nin the application\n  And\.intro hsame",
     [STALE_REACH]),
    # projections
    ('module', 'second-send-claimed-at-the-session-before-the-receipt',
     [(SECOND_SEND_CALL + "      vecOf bytes2 = secondFrame view oracle (vecOf q.identityAd)\n"
       "        (.keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector\n"
       "          ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩)\n"
       "        (oracle.dhPublic dA) (secondKey (arrayOf q.rootKey) (arrayOf q.sparseSend) dSend x)\n"
       "        ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩\n"
       "        (sliceOf ptS) ∧\n" + SECOND_SEND,
       (SECOND_SEND_CALL + "      vecOf bytes2 = secondFrame view oracle (vecOf q.identityAd)\n"
        "        (.keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector\n"
        "          ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩)\n"
        "        (oracle.dhPublic dA) (secondKey (arrayOf q.rootKey) (arrayOf q.sparseSend) dSend x)\n"
        "        ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 1⟩\n"
        "        (sliceOf ptS) ∧\n" + SECOND_SEND).replace("crc s'' ptS rngA' =", "crc s' ptS rngA' =", 1))],
     r"hcallS\nhas type\n  lifecycle\.Session\.encrypt rc crc s'' ptS rngA' = ok \(core\.result\.Result\.Ok bytes2, s''', rngA'\)\nbut is expected to have type\n  lifecycle\.Session\.encrypt rc crc s' ptS rngA' = ok \(core\.result\.Result\.Ok bytes2, s''', rngA'\)\nin the application\n  And\.intro hcallS",
     [TWO]),
    ('module', 'reply-receipt-claimed-to-return-the-second-plaintext',
     [(RECEIPT_PT, RECEIPT_PT.replace("ptA.val = ptR.val", "ptA.val = ptS.val", 1))],
     r"hptA\nhas type\n  ↑ptA = ↑ptR\nbut is expected to have type\n  ↑ptA = ↑ptS\nin the application\n  And\.intro hptA",
     [HEAD]),
    # leaf lemmas
    ('module', 'model-stale-receive-claimed-to-refuse-no-receiving-chain',
     [(MODEL_STALE, MODEL_STALE.replace(".outOfOrder", ".noReceivingChain"))],
     r"unsolved goals\nec prk k1 k2 a4 d dSend newPub xB z newPub2 : Key\n⊢ False",
     ['second_receive_stale']),
    ('module', 'model-triple-after-the-receipt-claimed-with-previous-chain-zero',
     [(MODEL_TRIPLE, MODEL_TRIPLE.replace("pn := 1", "pn := 0"))],
     r"unsolved goals\nec prk k1 k2 a4 d dSend newPub candA xB z newPub2 : Key\nhne : candA ≠ a4\n⊢ False",
     ['second_receive_key']),
    ('module', 'decoder-at-the-responder-session-claimed-empty',
     [(DECODER_SMALL, DECODER_SMALL.replace("length ≤ 1 := by", "length ≤ 0 := by"))],
     r"\(UnitLifecycleResponderSuccessor\.add_chunk_fresh_have d0 d c r hv hadd\)\.right\.right\.left\nhas type\n  \(↑d\.have\)\.length ≤ 1\nbut is expected to have type\n  \(↑d\.have\)\.length ≤ 0",
     ['established_responder_decoder_small']),
    ('module', 'in-order-step-claimed-on-a-key-other-than-the-reply-key',
     [(IN_ORDER, IN_ORDER.replace("candA ≠ a4", "candA ≠ newPub"))],
     r"hne\nhas type\n  candA ≠ newPub\nbut is expected to have type\n  candA ≠ a4\nin the application\n  second_receive_key",
     ['secondReceipt_inOrderStep']),
    # the definitions, with the pins kept
    ('pinned', 'stale-run-claimed-to-refuse-no-receiving-chain-pinned',
     [(STALE_RUN, STALE_RUN.replace("RatchetError.OutOfOrder", "RatchetError.NoReceivingChain"))],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleResponderSecondReceipt.SecondReceiptStaleRun')),
    ('pinned', 'run-without-the-invariant-after-the-receipt-pinned',
     [(RUN_INVARIANT, RUN_INVARIANT.replace("lifecycle.Session.invariant sB''' = ok true ∧", "True ∧"))],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleResponderSecondReceipt.SecondReceiptRun')),
]

COMPOSING = {
    TWO,
    HEAD,
    RUN,
    REACH,
    STALE_REACH,
}

# The controls labelled inside a composing proof, with the declaration each is refused in.  For each, the script also
# runs the changed copy with that theorem's proof replaced by `sorry` and requires Lean to accept the change there:
# the refusal is attributable to that proof.
INSIDE = {
    'responder-source-claimed-empty-after-the-reply': TWO,
    'second-plaintext-claimed-to-be-the-reply': TWO,
    'stale-arm-claimed-to-refuse-no-receiving-chain': TWO,
    'decoder-after-the-receipt-claimed-to-hold-only-the-first-chunk': TWO,
    'fresh-key-premise-claimed-against-the-peer-key': HEAD,
    'budget-after-the-receipt-claimed-beyond-the-clock': HEAD,
    'budget-after-the-receipt-claimed-one-operation-longer': HEAD,
    'run-responder-extra-bytes-claimed-shorter': RUN,
    'run-fresh-key-law-swapped': RUN,
    'reach-fresh-key-law-swapped': REACH,
    'stale-run-claimed-on-a-fresh-key': STALE_REACH,
}

# The controls refused in a composing proof where it places a conjunct of a called theorem's conclusion unchanged,
# with that called theorem: projections, labelled neither inside nor statement-shape and not probed.  Every other
# control refused in a composing proof must be labelled inside; `check_labels` holds both labels to the syntactic form
# of that standard (`passed_through`).
PROJECTION = {
    'second-send-claimed-at-the-session-before-the-receipt': 'initiator_sends_second_message',
    'reply-receipt-claimed-to-return-the-second-plaintext': TWO,
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
    """The 1-based line of the `#guard_msgs in` that precedes `#print name` (a definition's pin) or `#check @name` (a
    statement pin), or None."""
    lines = text.split('\n')
    for k in range(1, len(lines)):
        if lines[k] in (f'#print {name}', f'#check @{name}') and lines[k - 1].startswith('#guard_msgs'):
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
            raise SystemExit(f'FAILED control {name}: the copy has no `#print {where[1]}` or `#check @{where[1]}` '
                             f'pin, so its refusal cannot be the pin\'s; {log}')
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
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='responder-second-receipt-logs-'))
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
    with tempfile.TemporaryDirectory(prefix='responder-second-receipt-controls-') as tmp:
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
