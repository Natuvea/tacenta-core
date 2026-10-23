#!/usr/bin/env python3
"""Hold receive preservation against a planted fault.

`Translation/UnitLifecycleReceivePreserve.lean` shows that a successful `Session::decrypt_ratchet` (and the public
`Session::decrypt`) keeps `Session::invariant` and spends one unit of the counter budget `CounterRoom`, for every
invariant session whose model step is an in-order receive that leaves the agreement at `NoHeaderReceived` (holding at
most one chunk before the call) or at `KeysSampled`, given the relation after the call; and, on the runs, that the
session the initiator's `decrypt` of the reply returns passes the invariant and meets the four ceilings, and that the
session `establish_responder` returns on the first frame does, by the same step.  A proof that Lean accepts after the
fact it rests on is removed would hold nothing, so this script makes one change to a copy of the module and requires
Lean to refuse it, at a named place, with an error that names what the change removed.

The proofs that compose are the general step `decrypt_ratchet_keeps_invariant_in_order` (which composes the bridge, the
model's in-order receive, the agreement walk, clause (a) from the call's walk, the structural clauses and the budget),
the public step `decrypt_keeps_invariant_in_order`, and the two theorems on the runs.  What a run establishes is that
each control is refused at its named place, and that each control it labels inside a composing proof is also accepted
there when that proof is replaced by `sorry` (attribution to that proof, nothing more); controls it labels projections
are not probed.  The labels and the per-class counts in `negatives-control-counts.json` are the script's own labelling
and are guidance, not a claim: the helper that tells inside from projection reads Lean's error text and can read some
projections as composition steps (`ASSURANCE-OBLIGATIONS.md` records the decision, not built).  Each control labelled
inside is a change to a composing theorem's statement.  A control refused in a composing theorem is a projection when it
is refused where that proof places a conjunct of a called theorem's conclusion unchanged, and a composition step,
labelled inside, otherwise.  The script holds each of the two labels to a syntactic form of that standard read off the
module (`passed_through`: the refusal names a hypothesis the proof binds by destructuring a called theorem's conclusion,
never rewrites, simplifies or substitutes, and places with a constructor), and requires every control refused in a
composing theorem to carry one of them.  For each inside control it also runs the changed copy with that theorem's proof
replaced by `sorry`, requiring Lean to accept the change there, so the refusal is attributable to that proof.  That
probe verifies attribution only: it cannot tell a composing step from a projection.  That the syntactic form is the
right standard, and that the four theorems named in `COMPOSING` compose rather than project, is decided by reading.  The
labels are also held consistent (an inside control must be labelled with the declaration it is refused in and with a
composing theorem; no control carries two labels; every place a projection may be refused must be a composing theorem; a
statement-shape check may not be refused in a composing theorem, and the theorem it projects must be in `PROJECTED`), at
start-up (at run time the script checks only that each change is refused at its labelled place):

  * in `decrypt_ratchet_keeps_invariant_in_order`: the decoder scope widened to two chunks held (refused where the
    agreement walk is applied); the key-pair clone record `KemCloneAgrees` swapped for the erasure clone record
    (refused where the walk is applied); the budget claimed unspent, `CounterRoom s' (k + 1)` (refused where the model's
    budget step is carried back); the relation after the call claimed to the model session before the call (refused
    where the agreement's kind is read through the two relations and the step); the law `DhPublicValid` swapped for
    `KemCiphertextLenOf` (refused where the new sending key is read as canonical); the oracle's public-key clause
    claimed at one key only (refused where it is applied to the drawn candidate);
  * in `decrypt_keeps_invariant_in_order`: the decoder scope widened (refused where the general step is applied) and the
    budget claimed unspent (refused where the inner step's budget is placed at the cleared session);
  * in `initiator_receives_reply_successor`: the budget after the receipt claimed for every `j` with `j + 1 < u32::MAX`
    (false: the clock there is 1, so `j = u32::MAX - 2` has no room) and for `j + 1` further operations under the
    headline's bound (false at `j = u32::MAX - 3`), both refused where the general step's result on the run (`key`) is
    applied; the fresh-key premise claimed against the initiator's own ratchet key instead of the peer key it holds
    (refused where the receipt is taken);
  * in `responder_successor_via_preservation`: the session after the first frame claimed to have room for one more
    operation instead of meeting the ceilings (refused where the general step's budget is placed; a true statement,
    so this shows only that the proof derives no more room than the prepared session's one unit less one).

Labelled projections, neither inside nor statement-shape: the initiator's `decrypt` claimed from the source before its
first send, and the session after the receipt claimed to refine the model session before it.  Both are refused in
`initiator_receives_reply_successor`, at the final term, where that theorem passes the call and the relation of
`initiator_receives_reply` through unchanged; they show that the headline forwards them, not that it composes them, and
no emptied-proof run is made for them.

On the leaf lemmas: the sparse receive claimed with an agreement output (refused in `spqr_receive_inOrder`, whose state
is then the advanced one); the budget claimed kept with no unit to spend (refused at `omega` in
`modelCounterRoom_receive`); the two-chunk loop claimed for chunks of equal index (refused in `two_chunk_loop`); the
decoder step claimed for a decoder holding two chunks (refused in `decoder_step_keeps`, whose three-chunk case is then
open); `KeepsAgreementState` widened to the completion of `ct2`, which moves `ekSentCt1Received` to `noHeaderReceived`
with an output (refused in `keeps_output_none` and `keeps_epoch`); clearing the established ephemeral claimed in place
of the pending initial message (refused in `structural_clear_pending`, at the step that reads a cleared `none` field as
the session itself); and the in-order scope without its first-message condition on a new ratchet key (refused in
`modelTripleInv_receive_inOrder`, where the scope is handed to the classical receive).

Labelled statement-shape: the corollary `decrypt_keeps_invariant_model_step` claimed with the relation at the model's
`decryptRatchet` instead of its public `decrypt` (refused there because the model step it builds is the public call's;
the script runs it again with the proof of `decrypt_keeps_invariant_in_order` replaced by `sorry` and requires the same
refusal).  At a pin: `KeepsAgreementState` with its epoch equation reversed, the module's pins kept (refused at the pin
of `KeepsAgreementState`).

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

Dependencies must be built (`lake build Translation.UnitLifecycleSendPreserve
Translation.UnitLifecycleResponderReplyReceipt`).
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
MODULE = ROOT / 'translation/Translation/UnitLifecycleReceivePreserve.lean'

GEN_HEAD = ("theorem decrypt_ratchet_keeps_invariant_in_order (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees)\n"
            "    (hpub : DhPublicValid) {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)\n"
            "    (dh : DhView) (codec : DhCodecOf dh) (K : Model.Braid.Kem) (oracle : Model.Lifecycle.Oracle)\n"
            "    (hdhPublic : ∀ secret, ∃ publicKey,")

GEN_SMALL = ("    (hsmall : ∀ e a d, s.braid.state = tacenta_braid.State.NoHeaderReceived e a d → "
             "d.«have».val.length ≤ 1)\n"
             "    (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)\n"
             "    (hcall : lifecycle.Session.decrypt_ratchet rc crc")

GEN_TAIL = ("    (hrel' : SessionRefines dh K s' m') (hstep : InOrderReceiveStep oracle m m') :\n"
            "    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by\n"
            "  obtain ⟨hstr, htri, hbr⟩")

PUB_SMALL = ("    (hsmall : ∀ e a d, s.braid.state = tacenta_braid.State.NoHeaderReceived e a d → "
             "d.«have».val.length ≤ 1)\n"
             "    (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)\n"
             "    (hcall : lifecycle.Session.decrypt rc crc")

PUB_TAIL = ("    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by\n"
            "  obtain ⟨inner, s1, hin, rfl⟩")

REPLY_BUDGET = "      (∀ j, j + 2 < Std.U32.max → CounterRoom s'' j) ∧\n"

REPLY_CALL = "      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' =\n"

REPLY_REL = ("        (replyReceiptSession\n"
             "          (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session\n"
             "          (arrayOf q.rootKey) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive) "
             "dSend x\n"
             "          (oracleB.dhPublic dB) (oracle.dhPublic dA) dA) := by\n")

REPLY_FRESH = "    (hfreshB : oracleB.dhPublic dB ≠ arrayOf q.peerRatchetBytes) :\n"

REG_TAIL = ("      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' := by\n"
            "  rcases responder_first_frame_prepares")

SPQR_HEAD = "theorem spqr_receive_inOrder {st : Model.SparseRatchet.State} {e n : Nat}\n"

SPQR = "    Model.SparseRatchet.receiveDetailed st e none n = sparseTail st e n := by\n"

MODEL_STEP_REL = "    (hrel' : SessionRefines dh K s' (Model.Lifecycle.decrypt view oracle m msgM).session) :\n"

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`, or ('pin', name, 'check') for that of
#  its statement pin `#check @name`)
MUTANTS = [
    # inside the composing proofs
    ('module', 'decoder-scope-widened-to-two-chunks',
     [(GEN_SMALL, GEN_SMALL.replace("length ≤ 1)", "length ≤ 2)"))],
     r"hsmall\nhas type\n[\s\S]*?length ≤ 2\nbut is expected to have type\n[\s\S]*?length ≤ 1\nin the application\n  braid_receive_keeps hkcl s\.braid msgB x y bc hrecv hbr hsmall", ['decrypt_ratchet_keeps_invariant_in_order']),
    ('module', 'key-pair-clone-record-swapped-for-the-erasure-one',
     [(GEN_HEAD, GEN_HEAD.replace("KemCloneAgrees)", "ErasureCloneAgrees)"))],
     r"hkcl\nhas type\n  SessionUnitBraidT3\.ErasureCloneAgrees\nbut is expected to have type\n  SessionUnitBraidT3\.KemCloneAgrees\nin the application\n  braid_receive_keeps hkcl", ['decrypt_ratchet_keeps_invariant_in_order']),
    ('module', 'budget-claimed-unspent',
     [(GEN_TAIL, GEN_TAIL.replace("CounterRoom s' k", "CounterRoom s' (k + 1)"))],
     r"\(modelCounterRoom_receive oracle k hstep [\s\S]*?has type\n  CounterRoom s' k\nbut is expected to have type\n  CounterRoom s' \(k \+ 1\)", ['decrypt_ratchet_keeps_invariant_in_order']),
    ('module', 'relation-after-the-call-claimed-to-the-model-before-it',
     [(GEN_TAIL, GEN_TAIL.replace("SessionRefines dh K s' m')", "SessionRefines dh K s' m)"))],
     r"hrel'\.braid\nhas type\n  SessionUnitBraidT3\.StateRefines K s'\.braid\.state m\.braid\nbut is expected to have type\n  SessionUnitBraidT3\.StateRefines K s'\.braid\.state m'\.braid", ['decrypt_ratchet_keeps_invariant_in_order']),
    ('module', 'canonical-key-law-swapped',
     [(GEN_HEAD, GEN_HEAD.replace("(hpub : DhPublicValid)",
                                  "(hpub : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)"))],
     r"hpub\nhas type\n[\s\S]*?but is expected to have type\n  DhPublicValid\nin the application\n  @dhPublicValid_canonical hpub", ['decrypt_ratchet_keeps_invariant_in_order']),
    ('module', 'public-key-clause-claimed-at-one-key',
     [(GEN_HEAD, GEN_HEAD.replace("(hdhPublic : ∀ secret,", "(hdhPublic : ∃ secret,"))],
     r"Function expected at\n  hdhPublic\nbut this term has type\n  ∃ secret publicKey,[\s\S]*?applied to the argument\n  ck", ['decrypt_ratchet_keeps_invariant_in_order']),
    ('module', 'public-decoder-scope-widened-to-two-chunks',
     [(PUB_SMALL, PUB_SMALL.replace("length ≤ 1)", "length ≤ 2)"))],
     r"hsmall\nhas type\n[\s\S]*?length ≤ 2\nbut is expected to have type\n[\s\S]*?length ≤ 1\nin the application\n  decrypt_ratchet_keeps_invariant_in_order hkcl", ['decrypt_keeps_invariant_in_order']),
    ('module', 'public-budget-claimed-unspent',
     [(PUB_TAIL, PUB_TAIL.replace("CounterRoom s' k", "CounterRoom s' (k + 1)"))],
     r"r1\nhas type\n  ↑s1\.triple\.classical\.events \+ k \+ 1 < U32\.max\nbut is expected to have type\n[\s\S]*?\(k \+ 1\) \+\n\s*1 <[\s\S]*?in the application\n  CounterRoom\.mk r1", ['decrypt_keeps_invariant_in_order']),
    ('module', 'reply-budget-claimed-beyond-the-clock',
     [(REPLY_BUDGET, REPLY_BUDGET.replace("j + 2 <", "j + 1 <"))],
     r"hj\nhas type\n  j \+ 1 < U32\.max\nbut is expected to have type\n  j \+ 2 < U32\.max\nin the application\n  key j hj", ['initiator_receives_reply_successor']),
    ('module', 'reply-budget-claimed-one-operation-longer',
     [(REPLY_BUDGET, REPLY_BUDGET.replace("CounterRoom s'' j)", "CounterRoom s'' (j + 1))"))],
     r"\(key j hj\)\.right\nhas type\n  CounterRoom s'' j\nbut is expected to have type\n  CounterRoom s'' \(j \+ 1\)", ['initiator_receives_reply_successor']),
    ('module', 'reply-fresh-key-premise-claimed-against-the-initiator-key',
     [(REPLY_FRESH, REPLY_FRESH.replace("q.peerRatchetBytes", "q.ratchetBytes"))],
     r"hfreshB\nhas type\n  oracleB\.dhPublic dB ≠ arrayOf q\.ratchetBytes\nbut is expected to have type\n  oracleB\.dhPublic dB ≠ arrayOf q\.peerRatchetBytes\nin the application\n  UnitLifecycleResponderReplyReceipt\.initiator_receives_reply", ['initiator_receives_reply_successor']),
    ('module', 'reply-decrypt-claimed-from-the-source-before-the-send',
     [(REPLY_CALL, REPLY_CALL.replace("bytesR) rng' =", "bytesR) rng ="))],
     r"hcallA\nhas type\n  lifecycle\.Session\.decrypt rc crc s' bytesR\.deref rng' = ok \(core\.result\.Result\.Ok ptA, s'', rngA'\)\nbut is expected to have type\n  lifecycle\.Session\.decrypt rc crc s' bytesR\.deref rng = ok \(core\.result\.Result\.Ok ptA, s'', rngA'\)\nin the application\n  And\.intro hcallA", ['initiator_receives_reply_successor']),
    ('module', 'reply-session-claimed-to-refine-the-model-before-the-receipt',
     [(REPLY_REL, "        (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session := by\n")],
     r"hsess\nhas type\n  SessionRefines dh oracle\.braidKem s''\n    \(replyReceiptSession mA[\s\S]*?but is expected to have type\n  SessionRefines dh oracle\.braidKem s'' mA", ['initiator_receives_reply_successor']),
    ('module', 'first-receipt-room-claimed-for-one-more-operation',
     [(REG_TAIL, REG_TAIL.replace("Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB'", "CounterRoom sB' 1"))],
     r"\(counterRoom_zero sB'\)\.mp hroom0\nhas type\n  UnitLifecycleDecryptRunBounds\.CounterHeadroom sB'\nbut is expected to have type\n  CounterRoom sB' 1", ['responder_successor_via_preservation']),
    # leaf lemmas
    ('module', 'sparse-receive-claimed-with-an-agreement-output',
     [(SPQR_HEAD, SPQR_HEAD.replace("{e n : Nat}\n", "{e n : Nat} (o : Model.SparseRatchet.Output)\n")),
      (SPQR, SPQR.replace("st e none n", "st e (some o) n"))],
     r"unsolved goals\n[\s\S]*?match Model\.SparseRatchet\.advanceDetailed st o with", ['spqr_receive_inOrder']),
    ('module', 'budget-claimed-kept-without-a-unit-to-spend',
     [("    (hstep : InOrderReceiveStep oracle m m') (h : ModelCounterRoom m (k + 1)) : ModelCounterRoom m' k := by\n",
       "    (hstep : InOrderReceiveStep oracle m m') (h : ModelCounterRoom m k) : ModelCounterRoom m' k := by\n")],
     r"omega could not prove the goal:", ['modelCounterRoom_receive']),
    ('module', 'two-chunk-loop-claimed-for-equal-indices',
     [("    (hv : d.«have».val = [c1, c2]) (hne : c1.index ≠ c2.index) :\n",
       "    (hv : d.«have».val = [c1, c2]) (hne : c1.index = c2.index) :\n")],
     r"Function expected at\n  hne\nbut this term has type\n  c1\.index = c2\.index", ['two_chunk_loop']),
    ('module', 'decoder-step-claimed-for-two-chunks-held',
     [("    (hinv : tacenta_erasure.Decoder.invariant d = ok true) (hsmall : d.«have».val.length ≤ 1)\n",
       "    (hinv : tacenta_erasure.Decoder.invariant d = ok true) (hsmall : d.«have».val.length ≤ 2)\n")],
     r"unsolved goals\ncase inr\.cons\.cons\n[\s\S]*?hsmall : rest = \[\]\n⊢ d'\.invariant = ok true ∧ d'\.size = d\.size", ['decoder_step_keeps']),
    ('module', 'agreement-step-claimed-to-cover-the-ct2-completion',
     [("  | .keysSampled e _ _ _ _, .keysSampled e' _ _ _ _ => e' = e\n",
       "  | .keysSampled e _ _ _ _, .keysSampled e' _ _ _ _ => e' = e\n"
       "  | .ekSentCt1Received e _ _ _ _, .noHeaderReceived e' _ _ => e' = e + 1\n")],
     r"unsolved goals", ['keeps_output_none', 'keeps_epoch']),
    ('module', 'clear-pending-claimed-for-the-established-ephemeral',
     [("    lifecycle.Session.structural_invariant { s with pending_initial := none } = ok true := by\n",
       "    lifecycle.Session.structural_invariant { s with established_ephemeral := none } = ok true := by\n")],
     r"Did not find an occurrence of the pattern\n[\s\S]*?pending_initial := none, established_ephemeral := s\.established_ephemeral \}\nin the target expression\n[\s\S]*?established_ephemeral := none \}\.structural_invariant", ['structural_clear_pending']),
    ('module', 'in-order-scope-without-the-first-message-condition',
     [("    (m.classical.ckr = none ∨ m.classical.dhrPub = none ∨ h.dr.pn ≤ m.classical.nr) ∧ h.dr.n = 0\n",
       "    (m.classical.ckr = none ∨ m.classical.dhrPub = none ∨ h.dr.pn ≤ m.classical.nr)\n")],
     r"hord\.newChain\nhas type\n[\s\S]*?but is expected to have type\n[\s\S]*?∧ hdr\.dr\.n = 0\nin the application\n  modelRatchetInv_receive_inOrder hr hhdr hnp", ['modelTripleInv_receive_inOrder']),
    # statement-shape check (projects `decrypt_keeps_invariant_in_order`)
    ('module', 'model-step-corollary-claimed-at-decrypt-ratchet',
     [(MODEL_STEP_REL, MODEL_STEP_REL.replace("Model.Lifecycle.decrypt view", "Model.Lifecycle.decryptRatchet view"))],
     r"decrypt_inOrderStep view oracle m msgM inner hdisp hkeep hord\nhas type\n  InOrderReceiveStep oracle m \(Model\.Lifecycle\.decrypt view oracle m msgM\)\.session\nbut is expected to have type\n  InOrderReceiveStep oracle m \(Model\.Lifecycle\.decryptRatchet view oracle m msgM\)\.session", ['decrypt_keeps_invariant_model_step']),
    # the definition, with the pins kept
    ('pinned', 'agreement-state-epoch-equation-reversed-pinned',
     [("  | .noHeaderReceived e _ _, .noHeaderReceived e' _ _ => e' = e\n",
       "  | .noHeaderReceived e _ _, .noHeaderReceived e' _ _ => e = e'\n")],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleReceivePreserve.KeepsAgreementState')),
]

COMPOSING = {
    'decrypt_ratchet_keeps_invariant_in_order',
    'decrypt_keeps_invariant_in_order',
    'initiator_receives_reply_successor',
    'responder_successor_via_preservation',
}

# The controls labelled inside a composing proof, with the declaration each is refused in.  For each, the script also
# runs the changed copy with that theorem's proof replaced by `sorry` and requires Lean to accept the change there:
# the refusal is attributable to that proof.
INSIDE = {
    'decoder-scope-widened-to-two-chunks': 'decrypt_ratchet_keeps_invariant_in_order',
    'key-pair-clone-record-swapped-for-the-erasure-one': 'decrypt_ratchet_keeps_invariant_in_order',
    'budget-claimed-unspent': 'decrypt_ratchet_keeps_invariant_in_order',
    'relation-after-the-call-claimed-to-the-model-before-it': 'decrypt_ratchet_keeps_invariant_in_order',
    'canonical-key-law-swapped': 'decrypt_ratchet_keeps_invariant_in_order',
    'public-key-clause-claimed-at-one-key': 'decrypt_ratchet_keeps_invariant_in_order',
    'public-decoder-scope-widened-to-two-chunks': 'decrypt_keeps_invariant_in_order',
    'public-budget-claimed-unspent': 'decrypt_keeps_invariant_in_order',
    'reply-budget-claimed-beyond-the-clock': 'initiator_receives_reply_successor',
    'reply-budget-claimed-one-operation-longer': 'initiator_receives_reply_successor',
    'reply-fresh-key-premise-claimed-against-the-initiator-key': 'initiator_receives_reply_successor',
    'first-receipt-room-claimed-for-one-more-operation': 'responder_successor_via_preservation',
}

# The controls refused in a composing proof where it places a conjunct of a called theorem's conclusion unchanged,
# with that called theorem: projections, labelled neither inside nor statement-shape and not probed (the called
# theorem lives in another module).  Every other control refused in a composing proof must be labelled inside;
# `check_labels` holds both labels to the syntactic form of that standard (`passed_through`).
PROJECTION = {
    'reply-decrypt-claimed-from-the-source-before-the-send': 'initiator_receives_reply',
    'reply-session-claimed-to-refine-the-model-before-the-receipt': 'initiator_receives_reply',
}

# The theorems a statement-shape check may project: the composing theorems.
PROJECTED = set(COMPOSING)

# The statement-shape checks, with the theorem each projects.  For each, the script also runs the changed copy with
# that theorem's proof replaced by `sorry` and requires Lean still to refuse the change at its named place: the
# refusal does not depend on the projected theorem's proof.
STATEMENT_SHAPE = {
    'model-step-corollary-claimed-at-decrypt-ratchet': 'decrypt_keeps_invariant_in_order',
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
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='receive-preservation-logs-'))
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
    with tempfile.TemporaryDirectory(prefix='receive-preservation-controls-') as tmp:
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
