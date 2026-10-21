#!/usr/bin/env python3
"""Hold the initiator's receipt of the responder's reply against a planted fault.

`Translation/UnitLifecycleResponderReplyReceipt.lean` shows that, on the run in which the responder's `encrypt` at the
session `establish_responder` returned emits the bare reply frame, the initiator's public `Session::decrypt` of those
bytes, at the session its own first `encrypt` left and from the source that `encrypt` left, has exactly four outcomes,
and returns the responder's plaintext when the responder's fresh ratchet key is not the peer key the initiator holds.
A proof that Lean accepts after the fact it rests on is removed would hold nothing, so this script makes one change to
a copy of the module and requires Lean to refuse it, at a named place, with an error that names what the change
removed.

Eight controls sit inside the proofs that compose the run.  Each is a change to the composing theorem's statement,
refused by a step of its proof; the script checks this by also running each of the eight with that theorem's proof
replaced by `sorry` and requiring Lean to accept the change there:

  * in `initiator_receives_reply_outcomes`: the decrypt claimed from the source before the first send (whose draws
    that send took) instead of the source it left (refused where the refinement's call is placed); the reply's bytes
    claimed sealed under the key of the sparse chain `k1` the initiator sends on instead of `k2` (refused at the step
    that closes the bytes equation from the reply's run); the refusal on a stale ratchet key claimed to be `Aead`
    instead of `Triple(Classical(NoReceivingChain))` (refused where the model's refusal fixes the code's error); the
    stale-key arm claimed on a fresh key (refused where the model's case split fixes the key); the session after a
    success claimed to keep the pending initial message (refused where the walk of the public `decrypt` fixes what the
    call writes);
  * in `initiator_receives_reply`: the call claimed to take no draw (refused where the refinement fixes the source the
    call leaves); the freshness premise claimed against the initiator's own ratchet key instead of the peer key it
    holds (refused where the stale-key arm is excluded); the plaintext claimed to be the initiator's first plaintext
    instead of the responder's (refused where the open's plaintext is placed).

Eight are on the leaf lemmas:

  * the model's receive on a fresh key claimed under a premise about the sender's own ratchet key instead of the
    peer key (refused in `reply_receive_key`, which then cannot decide whether to take the Diffie-Hellman step);
  * the stale-key receive claimed to refuse `outOfOrder` (refused in `reply_receive_stale`);
  * the Triple after the reply's receipt claimed with previous chain length 0 instead of 1 (refused in
    `reply_receive_key`, which computes the step from a sender that has sent one message);
  * the joint model's public key made constant again, as in the first receipt's model (refused in
    `modelReply_notConstant`, whose witness key `1` then has the base point as its public key);
  * the responder's fresh private key claimed read by the view as its public key's bytes instead of the draw (refused
    in `fresh_public_of_draw`);
  * the initiator's first agreement claimed equal to the responder's agreement with the peer key instead of the
    initiator's ratchet key (refused in `initiator_reply_agreement`);
  * the model's stale-key outcome claimed to refuse `aead` (refused in `reply_receipt_model_outcomes`);
  * the model session the first send leaves claimed with the agreement at epoch 0 (refused in
    `first_send_model_session`).

One is a statement-shape check: the reach's decrypt claimed at the responder's session instead of the initiator's
(refused in `first_send_reply_receipt_reachable` because its statement no longer matches `reply_receipt_reach_run`; it
would be refused whatever that theorem's proof did).  One holds a definition: the model session after the reply's
receipt keeping the pending initial message, the module's pins kept (refused at the pin of `replyReceiptSession`).

Every change is to a statement or a definition; none replaces a proof step.  Each refusal is a proof-breakage check at
a named place: it shows that the proof there depends on what the change removed (or, for the last, that the pin holds
the definition), not that the changed statement is false.

The changes are checked on a copy without the module's pins, so that the refusal comes from a proof and not from a
pin, except the one kept with its pins.  The unmodified copies must be accepted first.  A timeout, a compiler that
does not start, a syntax error, an unrelated failure and a refusal elsewhere than the named place never count; an
error whose first line names a kind of failure that is not a refusal (an unresolved name, a syntax error) voids the
run anywhere in the copy, compared without regard to case, and the script checks at start that this guard fires on
the toolchain's own `Unknown identifier` and on the kernel's `unknown constant`, and not on an ordinary refusal.
These are controls on copies of the Lean; no source, olean or git state changes.

Dependencies must be built (`lake build Translation.UnitLifecycleResponderReply Translation.UnitLifecycleDecryptT3`).
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
MODULE = ROOT / 'translation/Translation/UnitLifecycleResponderReplyReceipt.lean'

OUTCOMES_CALL = ("      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' = ok (res, s'', rngA') ∧\n")

OUTCOMES_BYTES = ("        (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2 (arrayOf q.sparseReceive)) (sliceOf ptR) ∧\n"
                  "      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' = ok (res, s'', rngA') ∧\n")

STALE_ERROR = ("        (res = core.result.Result.Err (lifecycle.Error.Triple\n"
               "            (tacenta_triple.TripleError.Classical tacenta_ratchet.RatchetError.NoReceivingChain)) ∧\n")

STALE_KEY = "          oracleB.dhPublic dB = arrayOf q.peerRatchetBytes ∧ s'' = s') ∨\n"

OUTCOMES_WRITES = ("          s'' = { s' with\n"
                   "            triple := s''.triple, braid := s''.braid, ratchet_private := s''.ratchet_private,\n"
                   "            pending_initial := none } ∧\n")

SUCCESS_TAIL = "      ptA.val = ptR.val ∧ trace rngA' = restA ∧ s''.pending_initial = none ∧\n"

FRESH = "    (hfreshB : oracleB.dhPublic dB ≠ arrayOf q.peerRatchetBytes) :\n"

REACH_CALL = ("      lifecycle.Session.decrypt byteRng byteCrc s' (alloc.vec.Vec.deref bytesR) rng' =\n"
              "        ok (core.result.Result.Ok ptA, s'', rngA') ∧\n")

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
    # inside the composing proofs
    ('module', 'decrypt-claimed-from-the-source-before-the-first-send',
     [(OUTCOMES_CALL, OUTCOMES_CALL.replace("bytesR) rng' = ok (res", "bytesR) rng = ok (res"))],
     r"hcallA\nhas type\n  lifecycle\.Session\.decrypt rc crc s' bytesR\.deref rng' = ok \(res, s'', rngA'\)\nbut is expected to have type\n  lifecycle\.Session\.decrypt rc crc s' bytesR\.deref rng = ok \(res, s'', rngA'\)", ['initiator_receives_reply_outcomes']),
    ('module', 'reply-claimed-on-the-sparse-chain-k1',
     [(OUTCOMES_BYTES, OUTCOMES_BYTES.replace("(arrayOf q.sparseReceive)) (sliceOf ptR)", "(arrayOf q.sparseSend)) (sliceOf ptR)"))],
     r"⊢ replyFrame oracleB \(vecOf q\.identityAd\) \(oracleB\.dhPublic dB\)\n      \(firstKey \(Model\.State\.kdfRk \(arrayOf q\.rootKey\) dSend Model\.State\.LabelSet\.tacenta\)\.2 \(arrayOf q\.sparseReceive\)\)\n      \(sliceOf ptR\) =\n    replyFrame oracleB \(vecOf q\.identityAd\) \(oracleB\.dhPublic dB\)\n      \(firstKey \(Model\.State\.kdfRk \(arrayOf q\.rootKey\) dSend Model\.State\.LabelSet\.tacenta\)\.2 \(arrayOf q\.sparseSend\)\)", ['initiator_receives_reply_outcomes']),
    ('module', 'stale-key-refusal-claimed-as-aead',
     [(STALE_ERROR, "        (res = core.result.Result.Err lifecycle.Error.Aead ∧\n")],
     r"⊢ core\.result\.Result\.Err\n      \(lifecycle\.Error\.Triple \(tacenta_triple\.TripleError\.Classical tacenta_ratchet\.RatchetError\.NoReceivingChain\)\) =\n    core\.result\.Result\.Err lifecycle\.Error\.Aead", ['initiator_receives_reply_outcomes']),
    ('module', 'stale-key-arm-claimed-on-a-fresh-key',
     [(STALE_KEY, STALE_KEY.replace("dB = arrayOf q.peerRatchetBytes", "dB ≠ arrayOf q.peerRatchetBytes"))],
     r"hpeer\nhas type\n  oracleB\.dhPublic dB = arrayOf q\.peerRatchetBytes\nbut is expected to have type\n  oracleB\.dhPublic dB ≠ arrayOf q\.peerRatchetBytes", ['initiator_receives_reply_outcomes']),
    ('module', 'success-claimed-to-keep-the-pending-initial-message',
     [(OUTCOMES_WRITES, OUTCOMES_WRITES.replace("pending_initial := none }", "pending_initial := s'.pending_initial }"))],
     r"decrypt_ok_writes rc crc s' bytesR\.deref rng' ptA s'' rngA' hcallA\nhas type\n[\s\S]*?pending_initial := none, [\s\S]*?but is expected to have type\n[\s\S]*?pending_initial := s'\.pending_initial, ", ['initiator_receives_reply_outcomes']),
    ('module', 'success-claimed-without-a-draw',
     [(SUCCESS_TAIL, SUCCESS_TAIL.replace("trace rngA' = restA", "trace rngA' = dA :: restA"))],
     r"hdr\nhas type\n  trace rngA' = restA\nbut is expected to have type\n  trace rngA' = dA :: restA", ['initiator_receives_reply']),
    ('module', 'fresh-premise-claimed-against-the-initiator-own-key',
     [(FRESH, FRESH.replace("arrayOf q.peerRatchetBytes", "arrayOf q.ratchetBytes"))],
     r"hfreshB\nhas type\n  oracleB\.dhPublic dB ≠ arrayOf q\.ratchetBytes\nbut is expected to have type\n  ¬oracleB\.dhPublic dB = arrayOf q\.peerRatchetBytes\nin the application\n  absurd hpeer hfreshB", ['initiator_receives_reply']),
    ('module', 'plaintext-claimed-to-be-the-first-message',
     [(SUCCESS_TAIL, SUCCESS_TAIL.replace("ptA.val = ptR.val", "ptA.val = plaintext.val"))],
     r"hvec\nhas type\n  vecOf ptA = sliceOf ptR\nbut is expected to have type\n  List\.map SessionUnitBraidT3\.u8 ↑ptA = List\.map SessionUnitBraidT3\.u8 ↑plaintext", ['initiator_receives_reply']),
    # leaf lemmas
    ('module', 'fresh-key-receive-claimed-under-the-own-key-premise',
     [("theorem reply_receive_key (a4 peer rkA cksA prk k1 k2 dSend x newPub candPub : Key) (hne : newPub ≠ peer) :\n",
       "theorem reply_receive_key (a4 peer rkA cksA prk k1 k2 dSend x newPub candPub : Key) (hne : newPub ≠ a4) :\n")],
     r"hne : newPub ≠ a4\n⊢ \(match\n      match\n        if peer = newPub then", ['reply_receive_key']),
    ('module', 'stale-key-receive-claimed-to-refuse-out-of-order',
     [("        candPub none = .error (.classical .noReceivingChain) := by\n",
       "        candPub none = .error (.classical .outOfOrder) := by\n")],
     r"error: unsolved goals\na4 peer rkA cksA prk k1 k2 dSend x candPub : Key\n⊢ False", ['reply_receive_stale']),
    ('module', 'reply-receipt-triple-claimed-with-previous-chain-length-zero',
     [("        ns := 0, nr := 1, pn := 1, skipped := [], events := 1, labels := .tacenta }\n",
       "        ns := 0, nr := 1, pn := 0, skipped := [], events := 1, labels := .tacenta }\n")],
     r"error: unsolved goals\na4 peer rkA cksA prk k1 k2 dSend x newPub candPub : Key\nhne : newPub ≠ peer\n⊢ False", ['reply_receive_key']),
    ('module', 'joint-model-public-key-made-constant',
     [("    dhPrivPublicKey := fun k => ok (replyPub k)\n",
       "    dhPrivPublicKey := fun _ => ok Tacenta.UnitLifecycleEstablishResponder.basePoint\n")],
     r"replyPub_oneKey\nhas type\n  replyPub UnitLifecycleEstablishedDecrypt\.oneKey = UnitLifecycleEstablishedDecrypt\.oneKey\nbut is expected to have type\n  UnitLifecycleEstablishResponder\.basePoint = UnitLifecycleEstablishedDecrypt\.oneKey", ['modelReply_notConstant']),
    ('module', 'fresh-private-key-claimed-read-as-its-public-bytes',
     [("      arrayOf value = dB ∧ tacenta_boundary.dh.PrivateKey.from_bytes value = ok k ∧ dh.privateKey k = dB ∧\n",
       "      arrayOf value = dB ∧ tacenta_boundary.dh.PrivateKey.from_bytes value = ok k ∧ dh.privateKey k = arrayOf b ∧\n")],
     r"hval\nhas type\n  arrayOf value = dB\nbut is expected to have type\n  arrayOf value = arrayOf b\nin the application\n  Eq\.trans hkv hval", ['fresh_public_of_draw']),
    ('module', 'first-agreement-claimed-with-the-peer-key',
     [("      oracleB.dhAgree (dh.privateKey k) (arrayOf q.ratchetBytes) := by\n",
       "      oracleB.dhAgree (dh.privateKey k) (arrayOf q.peerRatchetBytes) := by\n")],
     r"Did not find an occurrence of the pattern\n  arrayOf q\.ratchetBytes\nin the target expression\n  Option\.map arrayOf ra = oracleB\.dhAgree \(dh\.privateKey k\) \(arrayOf q\.peerRatchetBytes\)", ['initiator_reply_agreement']),
    ('module', 'model-stale-key-outcome-claimed-as-aead',
     [("        { session := mA, result := .error (Model.Lifecycle.tripleReceiveRefusalOf (.classical .noReceivingChain)),\n",
       "        { session := mA, result := .error .aead,\n")],
     r"match Except\.error \(Model\.Triple\.ReceiveRefusal\.classical Model\.Ratchet\.ReceiveRefusal\.noReceivingChain\) with[\s\S]*?\{ session := mA, result := Except\.error Model\.Lifecycle\.Refusal\.aead", ['reply_receipt_model_outcomes']),
    ('module', 'first-send-model-session-claimed-at-epoch-zero',
     [("          braid := .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector encoder } := by\n",
       "          braid := .keysSampled 0 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector encoder } := by\n")],
     r"hsess\nhas type\n[\s\S]*?braid := Model\.Braid\.BraidState\.keysSampled 1 \(SessionUnitBraidT3\.AuthOf q\.auth\) dk ekVector encoder,[\s\S]*?but is expected to have type\n[\s\S]*?braid := Model\.Braid\.BraidState\.keysSampled 0 \(SessionUnitBraidT3\.AuthOf q\.auth\) dk ekVector encoder,", ['first_send_model_session']),
    # statement-shape check
    ('module', 'reach-decrypt-claimed-at-the-responder-session',
     [(REACH_CALL, REACH_CALL.replace("byteCrc s' (alloc", "byteCrc sB' (alloc"))],
     r"hcallA\nhas type\n  lifecycle\.Session\.decrypt byteRng byteCrc s' bytesR\.deref rng' = ok \(core\.result\.Result\.Ok ptA, s'', rngA'\)\nbut is expected to have type\n  lifecycle\.Session\.decrypt byteRng byteCrc sB' bytesR\.deref rng' = ok \(core\.result\.Result\.Ok ptA, s'', rngA'\)", ['first_send_reply_receipt_reachable']),
    # the definition, with the pins kept
    ('pinned', 'reply-receipt-session-keeping-the-pending-initial-message-pinned',
     [("    pendingInitial := none }\n", "    pendingInitial := mA.pendingInitial }\n")],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession')),
]

# The controls that sit inside a composing proof.  For each, the script also runs the changed copy with that
# theorem's proof replaced by `sorry` and requires Lean to accept the change there: the refusal must come from the
# proof, not from a statement it no longer matches.
INSIDE = {
    'decrypt-claimed-from-the-source-before-the-first-send': 'initiator_receives_reply_outcomes',
    'reply-claimed-on-the-sparse-chain-k1': 'initiator_receives_reply_outcomes',
    'stale-key-refusal-claimed-as-aead': 'initiator_receives_reply_outcomes',
    'stale-key-arm-claimed-on-a-fresh-key': 'initiator_receives_reply_outcomes',
    'success-claimed-to-keep-the-pending-initial-message': 'initiator_receives_reply_outcomes',
    'success-claimed-without-a-draw': 'initiator_receives_reply',
    'fresh-premise-claimed-against-the-initiator-own-key': 'initiator_receives_reply',
    'plaintext-claimed-to-be-the-first-message': 'initiator_receives_reply',
}

NOT_A_REFUSAL = ('unknown identifier', 'unknown constant', 'unexpected token', "expected '",
                 'unknown namespace', 'does not contain')


# Lean capitalises its error messages (`Unknown identifier`, `Unknown constant`, `Function expected`), so the
# guard is matched case-insensitively, on the first line of each error, where Lean names the kind of failure.
ERROR_HEAD = re.compile(r'^\S+\.lean:\d+:\d+: error(?:\([^)]*\))?: (.*)$', re.M)


def not_a_refusal(output, guards):
    """Whether an error of `output` is of a kind that is not a refusal (a name that does not resolve, a syntax
    error, ...), compared without regard to case."""
    heads = [head.lower() for head in ERROR_HEAD.findall(output)]
    return any(bad in head for head in heads for bad in guards)


def guard_self_test(guards):
    """The guard must fire on the toolchain's own spelling of an unresolved name."""
    sample = ("/tmp/x.lean:3:8: error(lean.unknownIdentifier): Unknown identifier `fooBar`\n"
              "/tmp/x.lean:4:2: error: unsolved goals\n")
    if not not_a_refusal(sample, guards):
        raise SystemExit('GUARD BROKEN: the not-a-refusal guard does not fire on `Unknown identifier`')
    kernel = ("/tmp/x.lean:5:8: error: (kernel) unknown constant 'Foo.bar'\n"
              "/tmp/x.lean:6:2: error: unsolved goals\n")
    if not not_a_refusal(kernel, guards):
        raise SystemExit('GUARD BROKEN: the not-a-refusal guard does not fire on the kernel\'s `unknown constant`')
    if not_a_refusal("/tmp/x.lean:4:2: error: unsolved goals\n", guards):
        raise SystemExit('GUARD BROKEN: the not-a-refusal guard fires on an ordinary refusal')


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
    refused = (status != 0 and 'error' in output and re.search(marker, output)
               and not not_a_refusal(output, NOT_A_REFUSAL))
    if not refused:
        raise SystemExit(f'FAILED control {name}: expected Lean to refuse it with `{marker}`, '
                         f'exit={status}; {log}')
    errors = {int(n) for n in ERROR_AT.findall(output)}
    if isinstance(where, tuple):
        line = pin_line(mutated, where[1])
        if line is None:
            raise SystemExit(f'FAILED control {name}: the copy has no `#print {where[1]}` pin, so '
                             f'its refusal cannot be the pin\'s; {log}')
        if line not in errors:
            raise SystemExit(f'FAILED control {name}: refused, but not at the pin of {where[1]} '
                             f'(line {line}); {log}')
        return f'the pin of {where[1]}'
    for decl in where:
        span = declaration_lines(mutated, decl)
        if span is None:
            raise SystemExit(f'Target changed for {name}: no declaration {decl} in the copy')
        if any(span[0] <= e <= span[1] for e in errors):
            return decl
    raise SystemExit(f'FAILED control {name}: refused, but in none of {", ".join(where)}; {log}')


def main():
    guard_self_test(NOT_A_REFUSAL)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=900)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='responder-reply-receipt-logs-'))
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
    with tempfile.TemporaryDirectory(prefix='responder-reply-receipt-controls-') as tmp:
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
            place = check_refused(name, status, output, marker, log, mutated, where)
            results['rejected'][f'{label}/{name}'] = {'exit': status, 'marker': marker, 'at': place}
            print(f'PASS: {label}/{name} refused by Lean in {place}', flush=True)
            if name in INSIDE:
                decl = INSIDE[name]
                emptied = gutted(mutated, decl)
                epath = tmp / f'{label}_{name}_emptied.lean'
                epath.write_text(emptied)
                elog = logs / f'{label}_{name}_emptied.log'
                status, output = run_lean(epath, elog, args.timeout)
                check_inside(name, decl, status, output, elog, emptied)
                results['rejected'][f'{label}/{name}']['inside'] = decl
                print(f'PASS: {label}/{name} accepted in {decl} with its proof emptied', flush=True)
    (logs / 'result.json').write_text(json.dumps(results, indent=2) + '\n')
    inside = sum(1 for r in results['rejected'].values() if 'inside' in r)
    print(f'{len(results["accepted"])} unmodified copies accepted, {len(results["rejected"])} changes '
          f'refused at their named places, {inside} of them inside a composing proof (accepted there with '
          f'that proof emptied); logs: {logs}', flush=True)


if __name__ == '__main__':
    sys.exit(main())
