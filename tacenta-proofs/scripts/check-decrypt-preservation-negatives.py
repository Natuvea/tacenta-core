#!/usr/bin/env python3
"""Hold `UnitLifecycleDecryptPreserve` against planted faults.

`Translation/UnitLifecycleDecryptPreserve.lean`: Session::decrypt and decrypt_ratchet keep Session::invariant and spend one unit of the counter budget at every agreement state, in the in-order scope with the agreement's output

The module shows that `Session::decrypt_ratchet` and `Session::decrypt` keep `Session::invariant` and spend at most
one unit of the counter budget (`CounterRoom`) at every agreement state, under the named laws of
`ReceiveInvariantLaws`, with the relation after the call and the model step (`ReceiveStep`) hypotheses, and that the
translated `Braid::receive` keeps `Braid::invariant` at every state.  The controls:

* inside the composing proofs: the receive step's budget claimed unspent and its relation after the call claimed to
  the model session before it, the laws' `Option<u64>` comparison shape dropped, and the laws' key-pair length law
  swapped for the encapsulation one (all refused in `decrypt_ratchet_keeps_invariant`); the key-pair clone record
  swapped for the erasure one (in `braid_receive_keeps_invariant`); the public call's budget claimed kept with no
  unit to spend (in `decrypt_keeps_invariant`); the reply run's budget claimed one operation past the clock (in
  `initiator_receives_reply_via_general`); the prepared receive's erasure agreement swapped for the key-pair clone
  record (in `prepared_receive_keeps_invariant`); the responder's step claimed from the session after the call (in
  `establish_responder_keeps_invariant`); the first frame's run without the `ct2` length law (in
  `responder_first_frame_via_general`);
* leaf lemmas: `Decoder::invariant` without its distinct-indices clause (`decoder_invariant_iff`); `add_chunk`
  claimed to grow `needed` (`add_chunk_keeps`); a completed message claimed one byte longer than the size
  (`decoder_message_len`); the model receive's role claimed kept through a failure (`receive_clauses`); the model's
  budget claimed kept with no unit to spend (`modelCounterRoom_receive_any`); clause (b) after a step claimed at the
  old sparse epoch (`step_frame_any`); the structural clauses with clause (b) read at the Triple before the call
  (`structural_after`); clause (b) read without the sparse epoch's room (`modelClauseB_of_structural`); the finished
  encapsulation without the `ct2` length law (`finish_encaps_inv`); the `KeysSampled` receive without the
  `ek_vector` length law (`step_receive_keysSampled`); the model receive claimed to keep the epoch
  (`receive_epoch_le`);
* statement shape: the model step's relation claimed to the model session before the call (refused in
  `decrypt_keeps_invariant_model_step`, which projects `decrypt_keeps_invariant`);
* the definition `KeyPairEkVectorLen` with its bound vector renamed and its pins kept (refused at its `#print` pin).

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

Dependencies must be built (`lake build Translation.UnitLifecycleEncryptPreserve`).
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
MODULE = ROOT / 'translation/Translation/UnitLifecycleDecryptPreserve.lean'

DR_TAIL = ("    (hrel' : SessionRefines dh K s' m') (hstep : ReceiveStep oracle m m') :\n"
           "    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k := by\n"
           "  obtain ⟨L⟩ := braidLens_of_totals")
D_ROOM = ("    (hinv : lifecycle.Session.invariant s = ok true) (hroom : CounterRoom s (k + 1))\n"
          "    (hrel : SessionRefines dh K s m)\n"
          "    (msg : Slice U8) (rng : R) (pt : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R)\n"
          "    (hcall : lifecycle.Session.decrypt rc")
PREP_HEAD = ("theorem prepared_receive_keeps_invariant (laws : ReceiveInvariantLaws)\n"
             "    (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees) {K : Model.Braid.Kem}\n")
EST_STEP = "      ∀ m', SessionRefines dh K s' m' → ReceiveStep oracle (responderModelOf dh p) m' →\n        lifecycle.Session.invariant s' = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s' := by\n  refine"
FRAME_LAWS = ("    (henc2 : Encapsulate2Len) :\n"
              "    lifecycle.Session.invariant sB' = ok true ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom sB' := by\n")
LAWS_EK = "  keyPairEkVector : KeyPairEkVectorLen\n"
LAWS_OEQ = "  optionEq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq)\n"
BR_HEAD = ("theorem braid_receive_keeps_invariant (L : BraidLens) (hkcl : Tacenta.SessionUnitBraidT3.KemCloneAgrees)\n")
RUN_BUDGET = "      (∀ j, j + 2 < Std.U32.max → CounterRoom s'' j) := by\n"
MS_REL = "    (hrel' : SessionRefines dh K s' (Model.Lifecycle.decrypt view oracle m msgM).session) :\n    lifecycle.Session.invariant s' = ok true ∧ CounterRoom s' k :=\n"

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`, or ('pin', name, 'check') for that of
#  its statement pin `#check @name`)
MUTANTS = [
    # inside the composing proofs
    ('module', 'receive-step-budget-claimed-unspent',
     [(DR_TAIL, DR_TAIL.replace("CounterRoom s' k := by", "CounterRoom s' (k + 1) := by"))],
     r"has type\n  CounterRoom s' k\nbut is expected to have type\n  CounterRoom s' \(k \+ 1\)", ['decrypt_ratchet_keeps_invariant']),
    ('module', 'receive-step-relation-claimed-to-the-model-before-the-call',
     [(DR_TAIL, DR_TAIL.replace("(hrel' : SessionRefines dh K s' m')", "(hrel' : SessionRefines dh K s' m)"))],
     r"Did not find an occurrence of the pattern\n  m'\.triple\.postQuantum\.direction\nin the target expression\n  m\.triple\.postQuantum\.direction = m\.triple\.postQuantum\.direction", ['decrypt_ratchet_keeps_invariant']),
    ('module', 'receive-laws-option-comparison-shape-dropped',
     [(LAWS_OEQ, "  optionEq : True\n")],
     r"hoeq\nhas type\n  True\nbut is expected to have type\n  UnitHeadroomInvariant\.OptionEqU64Shape @core\.option\.Option\.Insts\.CoreCmpPartialEqOption\.eq\nin the application\n  @modelClauseB_of_structural hoeq", ['decrypt_ratchet_keeps_invariant']),
    ('module', 'receive-laws-key-pair-length-law-swapped-for-the-encapsulation-one',
     [(LAWS_EK, "  keyPairEkVector : Encapsulate2Len\n")],
     r"laws\.keyPairEkVector\nhas type\n  Encapsulate2Len\nbut is expected to have type\n  KeyPairEkVectorLen\nin the application\n  braid_receive_keeps_invariant L laws\.kemClone laws\.divCeil laws\.truncate laws\.keyPairEkVector", ['decrypt_ratchet_keeps_invariant']),
    ('module', 'agreement-receive-key-pair-clone-record-swapped-for-the-erasure-one',
     [(BR_HEAD, BR_HEAD.replace("KemCloneAgrees)", "ErasureCloneAgrees)"))],
     r"hkcl\nhas type\n  SessionUnitBraidT3\.ErasureCloneAgrees\nbut is expected to have type\n  SessionUnitBraidT3\.KemCloneAgrees\nin the application\n  clone_inv L hkcl", ['braid_receive_keeps_invariant']),
    ('module', 'public-receive-budget-claimed-kept-without-a-unit-to-spend',
     [(D_ROOM, D_ROOM.replace("(hroom : CounterRoom s (k + 1))", "(hroom : CounterRoom s k)"))],
     r"hroom\nhas type\n  CounterRoom s k\nbut is expected to have type\n  CounterRoom s \(k \+ 1\)\nin the application\n  decrypt_ratchet_keeps_invariant laws rc crc dh codec K oracle hdhPublic s m \?m\.\d+ k hinv hroom", ['decrypt_keeps_invariant']),
    ('module', 'reply-run-budget-claimed-beyond-the-clock',
     [(RUN_BUDGET, RUN_BUDGET.replace("j + 2 <", "j + 1 <"))],
     r"hj\nhas type\n  j \+ 1 < U32\.max\nbut is expected to have type\n  j \+ 2 < U32\.max\nin the application\n  key j hj", ['initiator_receives_reply_via_general']),
    ('module', 'prepared-receive-erasure-agreement-swapped-for-the-key-pair-clone-record',
     [(PREP_HEAD, PREP_HEAD.replace("(hea : Tacenta.SessionUnitBraidT3.ErasureAgrees)", "(hea : Tacenta.SessionUnitBraidT3.KemCloneAgrees)"))],
     r"hea\nhas type\n  SessionUnitBraidT3\.KemCloneAgrees\nbut is expected to have type\n  SessionUnitBraidT3\.ErasureAgrees\nin the application\n  @UnitLifecycleEstablishResponder\.sessionRefines_responder_prepared", ['prepared_receive_keeps_invariant']),
    ('module', 'establish-responder-step-claimed-from-the-session-after-the-call',
     [(EST_STEP, EST_STEP.replace("ReceiveStep oracle (responderModelOf dh p) m' →", "ReceiveStep oracle m' m' →"))],
     r"hstep\nhas type\n  ReceiveStep oracle m' m'\nbut is expected to have type\n  ReceiveStep oracle \(responderModelOf dh p\) m'\nin the application\n  prepared_receive_keeps_invariant", ['establish_responder_keeps_invariant']),
    ('module', 'first-frame-run-without-the-ct2-length-law',
     [(FRAME_LAWS, FRAME_LAWS.replace("(henc2 : Encapsulate2Len) :", "(henc2 : KeyPairEkVectorLen) :"))],
     r"henc2\nhas type\n  KeyPairEkVectorLen\nbut is expected to have type\n  Encapsulate2Len\nin the application\n  ReceiveInvariantLaws\.mk", ['responder_first_frame_via_general']),
    # leaf lemmas
    ('module', 'decoder-invariant-without-distinct-indices',
     [("        d.«have».val.length ≤ d.needed.val ∧ (d.«have».val.map (fun c => c.index.val)).Nodup := by\n",
       "        d.«have».val.length ≤ d.needed.val := by\n")],
     r"unsolved goals\ncase pos[\s\S]*?⊢ \(List\.map \(fun c => ↑c\.index\) ↑d\.have\)\.Nodup", ['decoder_invariant_iff']),
    ('module', 'add-chunk-claimed-to-grow-needed',
     [("    tacenta_erasure.Decoder.invariant d' = ok true ∧ d'.size = d.size ∧ d'.needed = d.needed := by\n",
       "    tacenta_erasure.Decoder.invariant d' = ok true ∧ d'.size = d.size ∧ d'.needed.val = d.needed.val + 1 := by\n")],
     r"hn\nhas type\n  d'\.needed = d\.needed\nbut is expected to have type\n  ↑d'\.needed = ↑d\.needed \+ 1", ['add_chunk_keeps']),
    ('module', 'completed-message-claimed-one-byte-longer',
     [("    (h : tacenta_erasure.Decoder.message d = ok (some v)) : v.val.length = d.size.val := by\n",
       "    (h : tacenta_erasure.Decoder.message d = ok (some v)) : v.val.length = d.size.val + 1 := by\n")],
     r"omega could not prove the goal:[\s\S]*?a := ↑\(↑d\.have\)\.length", ['decoder_message_len']),
    ('module', 'model-receive-role-claimed-kept-through-failure',
     [("    ((Model.Braid.receive K st msg).2.2 = .failed ∨\n        modelIsInit (Model.Braid.receive K st msg).2.2 = modelIsInit st) ∧\n",
       "    (modelIsInit (Model.Braid.receive K st msg).2.2 = modelIsInit st) ∧\n")],
     r"unsolved goals\ncase h_1[\s\S]*?hn : sp \+ 1 = epoch✝", ['receive_clauses']),
    ('module', 'model-receive-budget-claimed-kept-without-a-unit-to-spend',
     [("    (hstep : ReceiveStep oracle m m') (h : ModelCounterRoom m (k + 1)) : ModelCounterRoom m' k := by\n",
       "    (hstep : ReceiveStep oracle m m') (h : ModelCounterRoom m k) : ModelCounterRoom m' k := by\n")],
     r"omega could not prove the goal:[\s\S]*?a - b - c ≥ 2", ['modelCounterRoom_receive_any']),
    ('module', 'receive-step-clause-b-claimed-at-the-old-sparse-epoch',
     [("      ModelClauseB m'.triple.postQuantum.epoch m'.braid ∧\n      (m'.braid = .failed ∨ modelIsInit m'.braid = modelIsInit m.braid) := by\n",
       "      ModelClauseB m.triple.postQuantum.epoch m'.braid ∧\n      (m'.braid = .failed ∨ modelIsInit m'.braid = modelIsInit m.braid) := by\n")],
     r"Did not find an occurrence of the pattern\n  m'\.triple\.postQuantum\.epoch\nin the target expression\n  ModelClauseB m\.triple\.postQuantum\.epoch \(Model\.Braid\.receive oracle\.braidKem m\.braid msgB\)\.2\.2", ['step_frame_any']),
    ('module', 'structural-clause-b-read-at-the-triple-before-the-call',
     [("        tacenta_braid.Braid.is_initiator b = tacenta_braid.Braid.is_initiator s.braid ∧ CodeClauseB t b)) :\n",
       "        tacenta_braid.Braid.is_initiator b = tacenta_braid.Braid.is_initiator s.braid ∧ CodeClauseB s.triple b)) :\n")],
     r"scalar_tac failed to prove the goal below[\s\S]*?hfold : 7#u8 ≤ T ∧ T ≤ 10#u8 → s\.triple\.post_quantum\.epoch = E", ['structural_after']),
    ('module', 'clause-b-read-without-the-sparse-epoch-room',
     [("    (hroomE : s.triple.post_quantum.epoch.val + 1 < Std.U64.max) :\n",
       "    (hroomE : s.triple.post_quantum.epoch.val + 1 < Std.U64.max ∨ True) :\n")],
     r"scalar_tac failed to prove the goal below", ['modelClauseB_of_structural']),
    ('module', 'finished-encapsulation-without-the-ct2-length-law',
     [("    (henc2 : Encapsulate2Len) (e : U64) (a : tacenta_braid.Auth) (es : tacenta_kem.EncapsState)\n",
       "    (henc2 : KeyPairEkVectorLen) (e : U64) (a : tacenta_braid.Auth) (es : tacenta_kem.EncapsState)\n")],
     r"es\nhas type\n  tacenta_kem\.EncapsState\nbut is expected to have type\n  tacenta_kem\.IncrementalKeyPair\nin the application\n  henc2 es", ['finish_encaps_inv']),
    ('module', 'key-sampled-receive-without-the-ek-vector-length-law',
     [("    (hekl : KeyPairEkVectorLen) (self : tacenta_braid.Braid)\n",
       "    (hekl : Encapsulate2Len) (self : tacenta_braid.Braid)\n")],
     r"kp\nhas type\n  tacenta_kem\.IncrementalKeyPair\nbut is expected to have type\n  tacenta_kem\.EncapsState\nin the application\n  hekl kp", ['step_receive_keysSampled']),
    ('module', 'model-receive-claimed-to-keep-the-epoch',
     [("    (Model.Braid.receive K st msg).2.2.epoch ≤ st.epoch + 1 := by\n",
       "    (Model.Braid.receive K st msg).2.2.epoch ≤ st.epoch := by\n")],
     r"unsolved goals\ncase h_2\.isTrue[\s\S]*?h✝² : msg\.epoch = epoch✝ ∧ msg\.type = Model\.Braid\.MsgType\.ct2", ['receive_epoch_le']),
    # statement-shape check (projects `decrypt_keeps_invariant`)
    ('module', 'model-step-relation-claimed-to-the-model-before-the-call',
     [(MS_REL, MS_REL.replace("(Model.Lifecycle.decrypt view oracle m msgM).session) :", "m) :"))],
     r"decrypt_receiveStep view oracle m msgM inner hdisp hord\nhas type\n  ReceiveStep oracle m \(Model\.Lifecycle\.decrypt view oracle m msgM\)\.session\nbut is expected to have type\n  ReceiveStep oracle m m", ['decrypt_keeps_invariant_model_step']),
    # the definitions, with the pins kept
    ('pinned', 'ek-vector-length-law-bound-vector-renamed-pinned',
     [("  ∀ (kp : tacenta_kem.IncrementalKeyPair) (v : alloc.vec.Vec Std.U8),\n"
       "    tacenta_kem.IncrementalKeyPair.ek_vector kp = ok v →\n"
       "      ∃ n : Usize, tacenta_kem.EK_VECTOR_LEN = ok n ∧ v.length = n.val\n",
       "  ∀ (kp : tacenta_kem.IncrementalKeyPair) (w : alloc.vec.Vec Std.U8),\n"
       "    tacenta_kem.IncrementalKeyPair.ek_vector kp = ok w →\n"
       "      ∃ n : Usize, tacenta_kem.EK_VECTOR_LEN = ok n ∧ w.length = n.val\n")],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleDecryptPreserve.KeyPairEkVectorLen')),
]

# The theorems that compose the run (decided by reading).
COMPOSING = {
    'decrypt_ratchet_keeps_invariant',
    'decrypt_keeps_invariant',
    'braid_receive_keeps_invariant',
    'initiator_receives_reply_via_general',
    'prepared_receive_keeps_invariant',
    'establish_responder_keeps_invariant',
    'responder_first_frame_via_general',
}

# The controls labelled inside a composing proof, with the declaration each is refused in.  For each, the script
# also runs the changed copy with that theorem's proof replaced by `sorry` and requires Lean to accept the change
# there: the refusal is attributable to that proof.
INSIDE = {
    'receive-step-budget-claimed-unspent': 'decrypt_ratchet_keeps_invariant',
    'receive-step-relation-claimed-to-the-model-before-the-call': 'decrypt_ratchet_keeps_invariant',
    'receive-laws-option-comparison-shape-dropped': 'decrypt_ratchet_keeps_invariant',
    'receive-laws-key-pair-length-law-swapped-for-the-encapsulation-one': 'decrypt_ratchet_keeps_invariant',
    'agreement-receive-key-pair-clone-record-swapped-for-the-erasure-one': 'braid_receive_keeps_invariant',
    'public-receive-budget-claimed-kept-without-a-unit-to-spend': 'decrypt_keeps_invariant',
    'reply-run-budget-claimed-beyond-the-clock': 'initiator_receives_reply_via_general',
    'prepared-receive-erasure-agreement-swapped-for-the-key-pair-clone-record': 'prepared_receive_keeps_invariant',
    'establish-responder-step-claimed-from-the-session-after-the-call': 'establish_responder_keeps_invariant',
    'first-frame-run-without-the-ct2-length-law': 'responder_first_frame_via_general',
}

# The controls refused in a composing proof where it places a conjunct of a called theorem's conclusion unchanged,
# with that called theorem: projections, labelled neither inside nor statement-shape and not probed.  Every other
# control refused in a composing proof must be labelled inside; `check_labels` holds both labels to the syntactic
# form of that standard (`passed_through`).
PROJECTION = {}

# The theorems a statement-shape check may project: the composing theorems.
PROJECTED = set(COMPOSING)

# The statement-shape checks, with the theorem each projects.  For each, the script also runs the changed copy
# with that theorem's proof replaced by `sorry` and requires Lean still to refuse the change at its named place:
# the refusal does not depend on the projected theorem's proof.
STATEMENT_SHAPE = {
    'model-step-relation-claimed-to-the-model-before-the-call': 'decrypt_keeps_invariant',
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
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='decrypt-preservation-logs-'))
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
    with tempfile.TemporaryDirectory(prefix='decrypt-preservation-controls-') as tmp:
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
