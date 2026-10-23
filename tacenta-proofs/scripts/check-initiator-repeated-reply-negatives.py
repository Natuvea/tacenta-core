#!/usr/bin/env python3
"""Hold the initiator's `decrypt` of the responder's reply delivered a second time against a planted fault.

`Translation/UnitLifecycleInitiatorRepeatedReply.lean` shows that, on the run of the initiator's first send, the
responder's receipt of it and its reply, at the session `s''` the initiator's first `decrypt` of the reply returns
(which passes `Session::invariant` and meets the four ceilings), the initiator's public `Session::decrypt` of the same
reply bytes, from a source whose trace holds a draw, returns `Triple(Classical(OutOfOrder))`, `s''` itself and the
source after exactly that draw, and that this refines the model's public `decrypt` step, which consumes the draw,
refuses `triple (classical outOfOrder)` and leaves the model session as it was, at every codeword view.

Ten controls carry the inside label, refused in the proofs that compose: the general step
`reply_again_refused_of_invariant` (which composes the decrypt refinement at a session with the invariant, the ceilings
and the relation, the model's step and the refusal frame) and the run's headline `initiator_repeated_reply_refused`
(which composes the first receipt's preservation result, the first receipt itself, the model session the first send
left and the general step on one run).  Each is a change to a composing theorem's statement.  **By reading, seven of the
ten are composition steps and three are not**:

  * composition steps, in `reply_again_refused_of_invariant`: the refusal claimed to take no draw (false: the candidate
    key is drawn before the Triple's receive), refused where the model's draws, rewritten by the model's step, are
    carried back; the code's refusal claimed to be `NoReceivingChain` and the session returned claimed to have its
    pending initial message cleared (false of an arbitrary session: a refusal writes nothing), each refused where
    `hcall`, bound from the decrypt refinement and rewritten (`rw [he] at hcall`, `rw [hs] at hcall`) to the refusal the
    model's step fixes and the session the refusal frame fixes, is placed; the agreement claimed failed, refused where
    the agreement's state is carried to the model's session after the reply; the source claimed a draw ahead of the
    oracle, refused where the oracle's draws are read;
  * composition steps, in `initiator_repeated_reply_refused`: the second draw claimed of the source the first send left,
    and the second source claimed to hold no draw before the rest, each refused where the headline builds the general
    step's oracle from the second source's premise and applies the general step;
  * not composition steps, by reading: the model's step claimed to keep the draw (refused in
    `reply_again_refused_of_invariant` at `exact reply_again_model_refused ...`, the leaf's conclusion placed unchanged
    after a rewrite of the goal); the model's step claimed on the reply's plaintext instead of its bytes (refused in
    `initiator_repeated_reply_refused` at `exact hM viewA`, the general step's model conjunct placed unchanged after a
    rewrite of the goal); and, borderline, the relation claimed with the second draw as the ratchet key (refused at
    `exact hsess`, the first receipt's relation rewritten to the reply's key and back).  They carry the inside label
    only because the label check reads a projection off a bare hypothesis marker alone (the refused term a
    hypothesis's name, then `has type`): a refused term printed applied (`hM viewA`) or a called theorem placed by
    `exact` reads as a composition step, and the check refuses the projection label for them.  The shared helper is
    not changed here; ASSURANCE-OBLIGATIONS.md records the limit.

The headline's other composition, identifying the session the first receipt returns in the preservation result with
the one in the receipt itself (by `encrypt` and `decrypt` being functions), has no control: no change to a statement
reaches it.

Three are projections, labelled neither inside nor statement-shape, all refused in `initiator_repeated_reply_refused`:
the second delivery claimed at the session before the first receipt (where the call conjunct of
`reply_again_refused_of_invariant` is placed unchanged), the invariant claimed at that session (where the invariant
conjunct of `initiator_receives_reply_successor` is placed unchanged; that session does pass the invariant, so this
shows only that the headline forwards the conjunct) and the first receipt claimed from the second source (where the call
conjunct of `initiator_receives_reply_successor` is placed unchanged).  They show that the headline forwards those
conjuncts, not that it composes them, and no emptied-proof run is made for them.

Two are statement-shape checks on the reach, each projecting `initiator_repeated_reply_refused`: the reach's second
delivery claimed from the source the first send left instead of the one the first receipt left, and claimed accepted.
Each is refused in `repeated_reply_refused_reachable` because its statement no longer matches the headline's, and the
script runs it again with the headline's proof replaced by `sorry` and requires the same refusal.

Five are on the leaf lemmas: the model's receive claimed to refuse `noReceivingChain` and claimed on a header carrying
the initiator's own sending key (refused in `reply_again_receive_outOfOrder`); the draw's agreement claimed refused
(refused in `reply_again_model_refused`, whose step is then the handshake refusal); the model's refusal claimed to keep the
oracle (refused in `reply_again_model_refused`: the draw is consumed); the byte trace claimed with its two runs swapped
(refused in `byteTrace_seed_two_extra`).  One holds a statement: `reply_again_receive_outOfOrder` with a bound
variable renamed and the module's pins kept (refused at that theorem's statement pin, `#check @`).

A proof that Lean accepts after the fact it rests on is removed would hold nothing, so this script makes one
change to a copy of the module and requires Lean to refuse it, at a named place, with an error that names what
the change removed.

A control refused in a composing theorem is a projection when it is refused where that proof places a conjunct of
a called theorem's conclusion unchanged, and a composition step, labelled inside, otherwise.  The script holds each
of the two labels to a syntactic form of that standard read off the module (`passed_through`: the refusal names a
hypothesis the proof binds by destructuring a called theorem's conclusion, never rewrites, simplifies or
substitutes, and places with a constructor), and requires every control refused in a composing theorem to carry
one of them.  For each inside control it also runs the changed copy with that theorem's proof replaced by `sorry`,
requiring Lean to accept the change there, so the refusal is attributable to that proof.  That probe verifies
attribution only: it cannot tell a composing step from a projection.  That the syntactic form is the right
standard, and that the theorems named in `COMPOSING` compose rather than project, is decided by reading.  Each
statement-shape check is run again with the projected theorem's proof replaced by `sorry`, and Lean must still
refuse it at its named place.  The labels are also held consistent (an inside control must be labelled with the
declaration it is refused in and with a composing theorem; no control carries two labels; every place a
projection may be refused must be a composing theorem; a statement-shape check may not be refused in a composing
theorem, and the theorem it projects must be in `PROJECTED`), at start-up.  With no control planted it refuses to
run.

Every change is to a statement or a definition; none replaces a proof step.  Each refusal is a proof-breakage
check at a named place: it shows that the proof there depends on what the change removed (or, for a definition
kept with its pins, that the pin holds the definition), not that the changed statement is false.

The changes are checked on a copy without the module's pins, so that the refusal comes from a proof and not from
a pin, except those kept with their pins.  The unmodified copies must be accepted first.  A compiler that does not
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

Dependencies must be built (`lake build Translation.UnitLifecycleReceivePreserve`).
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
MODULE = ROOT / 'translation/Translation/UnitLifecycleInitiatorRepeatedReply.lean'

GEN_TAIL = ("          tacenta_ratchet.RatchetError.OutOfOrder)), sA, rng') ∧\n"
            "      trace rng' = rest := by\n")
GEN_MODEL = ("          result := .error (.triple (.classical .outOfOrder))\n"
             "          oracle := { oracle with draws := rest } }) ∧\n"
             "    ∃ rng' : R,\n")
GEN_BRAID = ("    (hbraid : mA.braid = .keysSampled e auth dk ekVector enc)\n"
             "    (k : tacenta_boundary.dh.PrivateKey) (pk : tacenta_boundary.dh.PublicKeyBytes)\n")
GEN_TRACE = "    (rng : R) (htrace : trace rng = oracle.draws) (c : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key)\n"
HEAD_DRAW = ("    (hdrawA2 : trace rngA2 = dA2 :: restA2) :\n"
             "    ∃ (dSend x : Model.Lifecycle.Key) (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session)\n")
HEAD_MODEL_BYTES = "              (oracleB.dhPublic dB) (oracle.dhPublic dA) dA) (vecOf bytesR) =\n"
HEAD_REL = ("          (oracleB.dhPublic dB) (oracle.dhPublic dA) dA) ∧\n"
            "      (∀ viewA : Model.Lifecycle.CodewordView,\n")
HEAD_REPEAT = "      lifecycle.Session.decrypt rc crc s'' (alloc.vec.Vec.deref bytesR) rngA2 =\n"
HEAD_INV = "      lifecycle.Session.invariant s'' = ok true ∧\n"
HEAD_FIRST = ("      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' =\n"
              "        ok (core.result.Result.Ok ptA, s'', rngA') ∧\n"
              "      ptA.val = ptR.val ∧\n"
              "      lifecycle.Session.invariant s'' = ok true ∧\n")
REACH_REPEAT = ("      lifecycle.Session.decrypt byteRng byteCrc s'' (alloc.vec.Vec.deref bytesR) rngA' =\n"
                "        ok (core.result.Result.Err (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical\n"
                "          tacenta_ratchet.RatchetError.OutOfOrder)), s'', rngA3) := by\n")
LEAF_RECV = ("    Model.Triple.receiveDetailed (initiatorAfterReply rkA prk k1 k2 dSend x newPub candPub) (firstHeader newPub)\n"
             "        dR dS np out = .error (.classical .outOfOrder) := by\n")
LEAF_CAND = "    (dS : Key) (hcand : oracleA.dhAgree c newPub = some dS) :\n"
LEAF_KEEP = "        oracle := { oracleA with draws := rest } } := by\n"
LEAF_TRACE = "          e1.map Tacenta.SessionUnitBraidT3.u8 :: [e2.map Tacenta.SessionUnitBraidT3.u8] := by\n"
PIN_RECV = "theorem reply_again_receive_outOfOrder (rkA prk k1 k2 dSend x newPub candPub dR dS np : Key)\n"

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`, or ('pin', name, 'check') for that of
#  its statement pin `#check @name`)
MUTANTS = [
    # inside the composing proofs
    ('module', 'refusal-claimed-to-take-no-draw',
     [(GEN_TAIL, GEN_TAIL.replace("trace rng' = rest", "trace rng' = c :: rest"))],
     r"hdr\nhas type\n  trace \(res, sA2, rng'\)\.2\.2 =[\s\S]*?\.oracle\.draws\nbut is expected to have type\n  trace rng' = c :: rest\nin the application\n  ⟨hcall, hdr⟩", ['reply_again_refused_of_invariant']),
    ('module', 'refusal-claimed-for-no-receiving-chain',
     [(GEN_TAIL, GEN_TAIL.replace("RatchetError.OutOfOrder", "RatchetError.NoReceivingChain"))],
     r"hcall\nhas type\n  lifecycle\.Session\.decrypt rc crc sA msg rng =\n    ok\n      \(core\.result\.Result\.Err\n          \(lifecycle\.Error\.Triple \(tacenta_triple\.TripleError\.Classical tacenta_ratchet\.RatchetError\.OutOfOrder\)\),\n        sA, rng'\)\nbut is expected to have type\n[\s\S]*?RatchetError\.NoReceivingChain\)\),\n        sA, rng'\)", ['reply_again_refused_of_invariant']),
    ('module', 'refusal-claimed-to-clear-the-pending-message',
     [(GEN_TAIL, GEN_TAIL.replace("OutOfOrder)), sA, rng')", "OutOfOrder)),\n          { sA with pending_initial := none }, rng')"))],
     r"hcall\nhas type\n  lifecycle\.Session\.decrypt rc crc sA msg rng =\n[\s\S]*?\n        sA, rng'\)\nbut is expected to have type\n[\s\S]*?pending_initial := none, established_ephemeral := sA\.established_ephemeral \},\n        rng'\)", ['reply_again_refused_of_invariant']),
    ('module', 'model-refusal-claimed-to-keep-the-draw',
     [(GEN_MODEL, GEN_MODEL.replace("oracle := { oracle with draws := rest } })", "oracle := oracle })"))],
     r"Type mismatch\n  reply_again_model_refused view oracle oracleB mA[\s\S]*?draws := rest,[\s\S]*?but is expected to have type\n  Model\.Lifecycle\.decrypt view oracle mR[\s\S]*?\n      oracle := oracle \}", ['reply_again_refused_of_invariant']),
    ('module', 'agreement-claimed-failed',
     [(GEN_BRAID, GEN_BRAID.replace(".keysSampled e auth dk ekVector enc)", ".failed)"))],
     r"hbraid\nhas type\n  mA\.braid = Model\.Braid\.BraidState\.failed\nbut is expected to have type\n  \(replyReceiptSession mA rkA prk k1 k2 dSend x \(dh\.publicKey pk\) candPub c0\)\.braid =\n    Model\.Braid\.BraidState\.keysSampled e auth dk ekVector enc", ['reply_again_refused_of_invariant']),
    ('module', 'source-claimed-a-draw-ahead-of-the-oracle',
     [(GEN_TRACE, GEN_TRACE.replace("trace rng = oracle.draws", "trace rng = oracle.draws.tail"))],
     r"Eq\.trans \(Eq\.symm htrace\) hdraw\nhas type\n  oracle\.draws\.tail = c :: rest\nbut is expected to have type\n  oracle\.draws = c :: rest", ['reply_again_refused_of_invariant']),
    ('module', 'second-draw-claimed-of-the-first-receipt-source',
     [(HEAD_DRAW, HEAD_DRAW.replace("trace rngA2 = dA2", "trace rng' = dA2"))],
     r"hdrawA2\nhas type\n  trace rng' = dA2 :: restA2\nbut is expected to have type\n  trace rngA2 = oracleA2\.draws\nin the application\n  reply_again_refused_of_invariant", ['initiator_repeated_reply_refused']),
    ('module', 'second-source-claimed-to-hold-no-draw-first',
     [(HEAD_DRAW, HEAD_DRAW.replace("trace rngA2 = dA2 :: restA2", "trace rngA2 = restA2"))],
     r"hdrawA2\nhas type\n  trace rngA2 = restA2\nbut is expected to have type\n  trace rngA2 = oracleA2\.draws\nin the application\n  reply_again_refused_of_invariant", ['initiator_repeated_reply_refused']),
    ('module', 'model-step-claimed-on-the-plaintext',
     [(HEAD_MODEL_BYTES, HEAD_MODEL_BYTES.replace("(vecOf bytesR)", "(sliceOf ptR)"))],
     r"hM viewA\nhas type\n  Model\.Lifecycle\.decrypt viewA oracleA2\n[\s\S]*?\(sliceOf bytesR\.deref\) =\n[\s\S]*?but is expected to have type\n[\s\S]*?\(sliceOf ptR\) =", ['initiator_repeated_reply_refused']),
    ('module', 'relation-claimed-with-the-second-draw-as-ratchet-key',
     [(HEAD_REL, HEAD_REL.replace("(oracle.dhPublic dA) dA)", "(oracle.dhPublic dA2) dA2)"))],
     r"hsess\nhas type\n  SessionRefines dh oracle\.braidKem s''\n[\s\S]*?\(oracle\.dhPublic dA\) dA\)\nbut is expected to have type\n  SessionRefines dh oracle\.braidKem s''\n[\s\S]*?\(oracle\.dhPublic dA2\) dA2\)", ['initiator_repeated_reply_refused']),
    # projections
    ('module', 'repeat-claimed-at-the-session-before-the-first-receipt',
     [(HEAD_REPEAT, HEAD_REPEAT.replace("crc s'' (", "crc s' ("))],
     r"hcall2\nhas type\n  lifecycle\.Session\.decrypt rc crc s'' bytesR\.deref rngA2 =[\s\S]*?but is expected to have type\n  lifecycle\.Session\.decrypt rc crc s' bytesR\.deref rngA2 =[\s\S]*?in the application\n  And\.intro hcall2", ['initiator_repeated_reply_refused']),
    ('module', 'invariant-claimed-at-the-session-before-the-first-receipt',
     [(HEAD_INV, HEAD_INV.replace("invariant s''", "invariant s'"))],
     r"hinv\nhas type\n  s''\.invariant = ok true\nbut is expected to have type\n  s'\.invariant = ok true\nin the application\n  And\.intro hinv", ['initiator_repeated_reply_refused']),
    ('module', 'first-receipt-claimed-from-the-second-source',
     [(HEAD_FIRST, HEAD_FIRST.replace("bytesR) rng' =", "bytesR) rngA2 ="))],
     r"hcallA\nhas type\n  lifecycle\.Session\.decrypt rc crc s' bytesR\.deref rng' = ok \(core\.result\.Result\.Ok ptA, s'', rngA'\)\nbut is expected to have type\n  lifecycle\.Session\.decrypt rc crc s' bytesR\.deref rngA2 = ok \(core\.result\.Result\.Ok ptA, s'', rngA'\)\nin the application\n  And\.intro hcallA", ['initiator_repeated_reply_refused']),
    # statement-shape checks (project `initiator_repeated_reply_refused`)
    ('module', 'reach-repeat-claimed-from-the-first-send-source',
     [(REACH_REPEAT, REACH_REPEAT.replace("bytesR) rngA' =", "bytesR) rng' ="))],
     r"hcall2\nhas type\n  lifecycle\.Session\.decrypt byteRng byteCrc s'' bytesR\.deref rngA' =[\s\S]*?but is expected to have type\n  lifecycle\.Session\.decrypt byteRng byteCrc s'' bytesR\.deref rng' =", ['repeated_reply_refused_reachable']),
    ('module', 'reach-repeat-claimed-accepted',
     [(REACH_REPEAT, REACH_REPEAT.replace("ok (core.result.Result.Err (lifecycle.Error.Triple (tacenta_triple.TripleError.Classical\n          tacenta_ratchet.RatchetError.OutOfOrder)), s'', rngA3)", "ok (core.result.Result.Ok ptA, s'', rngA3)"))],
     r"hcall2\nhas type\n[\s\S]*?RatchetError\.OutOfOrder[\s\S]*?but is expected to have type\n  lifecycle\.Session\.decrypt byteRng byteCrc s'' bytesR\.deref rngA' = ok \(core\.result\.Result\.Ok ptA, s'', rngA3\)", ['repeated_reply_refused_reachable']),
    # leaf lemmas
    ('module', 'receive-claimed-refused-for-no-receiving-chain',
     [(LEAF_RECV, LEAF_RECV.replace(".outOfOrder)", ".noReceivingChain)"))],
     r"unsolved goals\nrkA prk k1 k2 dSend x newPub candPub dR dS np : Key\nout : Option Model\.SparseRatchet\.Output\n⊢ False", ['reply_again_receive_outOfOrder']),
    ('module', 'receive-claimed-on-the-key-the-initiator-sends-on',
     [(LEAF_RECV, LEAF_RECV.replace("(firstHeader newPub)", "(firstHeader candPub)"))],
     r"unsolved goals\nrkA prk k1 k2 dSend x newPub candPub dR dS np : Key\nout : Option Model\.SparseRatchet\.Output\n⊢ \(match\n      match\n        if newPub = candPub then", ['reply_again_receive_outOfOrder']),
    ('module', 'draw-agreement-claimed-refused',
     [(LEAF_CAND, LEAF_CAND.replace("= some dS)", "= none)"))],
     r"Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  Model\.Lifecycle\.tripleHeaderOf \(replyComposite newPub\)\nin the target expression\n  \{ session := mR,\n      result :=\n        Except\.error \(Model\.Lifecycle\.Refusal\.handshake Model\.Lifecycle\.HandshakeRefusal\.nonContributoryAgreement\)", ['reply_again_model_refused']),
    ('module', 'model-refusal-claimed-to-keep-the-oracle',
     [(LEAF_KEEP, LEAF_KEEP.replace("{ oracleA with draws := rest }", "oracleA"))],
     r"Tactic `rfl` failed: The left-hand side\n  match\n    \(match Except\.error \(Model\.Triple\.ReceiveRefusal\.classical Model\.Ratchet\.ReceiveRefusal\.outOfOrder\) with[\s\S]*?draws := rest,", ['reply_again_model_refused']),
    ('module', 'byte-trace-claimed-with-the-runs-swapped',
     [(LEAF_TRACE, LEAF_TRACE.replace("e1.map Tacenta.SessionUnitBraidT3.u8 :: [e2.map", "e2.map Tacenta.SessionUnitBraidT3.u8 :: [e1.map"))],
     r"unsolved goals\nseed e1 e2 : List U8[\s\S]*?⊢ List\.map SessionUnitBraidT3\.u8 e1 = List\.map SessionUnitBraidT3\.u8 e2", ['byteTrace_seed_two_extra']),
    # the statement, with the pins kept
    ('pinned', 'receive-variable-renamed-pinned',
     [(PIN_RECV, PIN_RECV.replace(" np :", " np' :")),
      ("        dR dS np out = .error (.classical .outOfOrder) := by\n",
       "        dR dS np' out = .error (.classical .outOfOrder) := by\n")],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleInitiatorRepeatedReply.reply_again_receive_outOfOrder', 'check')),
]

# The theorems that compose the run (decided by reading).
COMPOSING = {
    'reply_again_refused_of_invariant',
    'initiator_repeated_reply_refused',
}

# The controls labelled inside a composing proof, with the declaration each is refused in.  For each, the script
# also runs the changed copy with that theorem's proof replaced by `sorry` and requires Lean to accept the change
# there: the refusal is attributable to that proof.
INSIDE = {
    'refusal-claimed-to-take-no-draw': 'reply_again_refused_of_invariant',
    'refusal-claimed-for-no-receiving-chain': 'reply_again_refused_of_invariant',
    'refusal-claimed-to-clear-the-pending-message': 'reply_again_refused_of_invariant',
    'model-refusal-claimed-to-keep-the-draw': 'reply_again_refused_of_invariant',
    'agreement-claimed-failed': 'reply_again_refused_of_invariant',
    'source-claimed-a-draw-ahead-of-the-oracle': 'reply_again_refused_of_invariant',
    'second-draw-claimed-of-the-first-receipt-source': 'initiator_repeated_reply_refused',
    'second-source-claimed-to-hold-no-draw-first': 'initiator_repeated_reply_refused',
    'model-step-claimed-on-the-plaintext': 'initiator_repeated_reply_refused',
    'relation-claimed-with-the-second-draw-as-ratchet-key': 'initiator_repeated_reply_refused',
}

# The controls refused in a composing proof where it places a conjunct of a called theorem's conclusion unchanged,
# with that called theorem: projections, labelled neither inside nor statement-shape and not probed.  Every other
# control refused in a composing proof must be labelled inside; `check_labels` holds both labels to the syntactic
# form of that standard (`passed_through`).
PROJECTION = {
    'repeat-claimed-at-the-session-before-the-first-receipt': 'reply_again_refused_of_invariant',
    'invariant-claimed-at-the-session-before-the-first-receipt': 'initiator_receives_reply_successor',
    'first-receipt-claimed-from-the-second-source': 'initiator_receives_reply_successor',
}

# The theorems a statement-shape check may project: the composing theorems.
PROJECTED = set(COMPOSING)

# The statement-shape checks, with the theorem each projects.  For each, the script also runs the changed copy
# with that theorem's proof replaced by `sorry` and requires Lean still to refuse the change at its named place:
# the refusal does not depend on the projected theorem's proof.
STATEMENT_SHAPE = {
    'reach-repeat-claimed-from-the-first-send-source': 'initiator_repeated_reply_refused',
    'reach-repeat-claimed-accepted': 'initiator_repeated_reply_refused',
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
    if not MUTANTS:
        raise SystemExit('NO CONTROLS: MUTANTS is empty; a control with no planted change holds nothing')
    check_labels(without_pins(MODULE.read_text(), MODULE))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=900)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='initiator-repeated-reply-logs-'))
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
    with tempfile.TemporaryDirectory(prefix='initiator-repeated-reply-controls-') as tmp:
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
