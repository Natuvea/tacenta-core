#!/usr/bin/env python3
"""Hold the responder successor's invariant and ceilings against a planted fault.

`Translation/UnitLifecycleResponderSuccessor.lean` shows that the session `establish_responder` returns on the bytes
the initiator's first `encrypt` emits passes `Session::invariant` and meets the four counter ceilings, from a walk of
the successful `decrypt_ratchet`, the relation the first receipt proves (which fixes the Triple and the agreement's
state), and a walk of `Braid::receive` for the agreement's decoder.  A proof that Lean accepts after the fact it rests
on is removed would hold nothing, so this script makes one change to a copy of the module and requires Lean to refuse
it, at a named place, with an error that names what the change removed:

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
  * the walks: `Braid::receive` claimed to keep the decoder (refused in `braid_receive_noHeader`, where the chunk
    is added) and `decrypt_ratchet` claimed never to replace the ratchet key (refused in
    `decrypt_ratchet_ok_parts`);
  * the composition chain: the returned session's relation claimed to the prepared session's model instead of the
    step's (refused in `responder_first_frame_successor`), the invariant claimed of the initiator's session after its
    send instead of the responder's (refused in `initiator_first_send_responder_successor_admissible`), the responder's
    call taken on the plaintext instead of the bytes the first send returned (refused in the same theorem), and the
    reach's invariant claimed of the initiator's session (refused in `first_send_receive_successor_reachable`);
  * the definition of the session after the receive without its ratchet key, the module's pins kept (refused at the
    pin of `receivedSession`).

Every change is to a statement or a definition; none replaces a proof step.  Each refusal is a proof-breakage check at
a named place: it shows that the proof there depends on what the change removed (or, for the last, that the pin holds
the definition), not that the changed statement is false.  The four controls on the composition chain show that the
composed proofs are about the responder's returned session, its relation to the model's step and the bytes the first
send returned; they are not proofs that any other session fails the invariant.

The changes are checked on a copy without the module's pins, so that the refusal comes from a proof and not from a
pin, except the one kept with its pins.  The unmodified copies must be accepted first.  A timeout, a compiler that
does not start, a syntax error, an unrelated failure and a refusal elsewhere than the named place never count; an
error whose first line names a kind of failure that is not a refusal (an unresolved name, a syntax error) voids the
run anywhere in the copy, compared without regard to case, and the script checks at start that this guard fires on
the toolchain's own `Unknown identifier`.  These are controls on copies of the Lean; no source, olean or git state
changes.

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

STEP_RELATION = ("      SessionRefines dh oracleB.braidKem sB'\n"
                 "        (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)\n"
                 "          (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)\n"
                 "          (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) ∧\n")

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
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
       "    d' = d := by\n")],
     r'Invalid `⟨\.\.\.⟩` notation: The expected type of this term could not be determined', ['braid_receive_noHeader']),
    ('module', 'receive-claimed-never-to-replace-the-ratchet-key',
     [("          s' = { s with triple := s'.triple, braid := bc, ratchet_private := ck }) ∨\n",
       "          s' = { s with triple := s'.triple, braid := bc }) ∨\n")],
     r'ratchet_private := ck, identity_ad := s\.identity_ad,[\s\S]*?=\n    \{\n      triple :=[\s\S]*?braid := bc, ratchet_private := s\.ratchet_private', ['decrypt_ratchet_ok_parts']),
    ('module', 'relation-claimed-to-the-prepared-model',
     [(STEP_RELATION, "      SessionRefines dh oracleB.braidKem sB' (responderModelOf dh p) ∧\n")],
     r"has type\n  SessionRefines dh oracleB\.braidKem sB'\n    \(firstReceiptSession \(responderModelOf dh p\)[\s\S]*?but is expected to have type\n  SessionRefines dh oracleB\.braidKem sB' \(responderModelOf dh p\)", ['responder_first_frame_successor']),
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
    ('pinned', 'session-without-its-ratchet-key-pinned',
     [('    braid := ⟨tacenta_braid.State.NoHeaderReceived 1#u64 auth dec⟩\n'
       '    ratchet_private := rp }\n',
       '    braid := ⟨tacenta_braid.State.NoHeaderReceived 1#u64 auth dec⟩ }\n')],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleResponderSuccessor.receivedSession')),
]

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
            place = check_refused(name, status, output, marker, log, mutated, where)
            results['rejected'][f'{label}/{name}'] = {'exit': status, 'marker': marker, 'at': place}
            print(f'PASS: {label}/{name} refused by Lean in {place}', flush=True)
    (logs / 'result.json').write_text(json.dumps(results, indent=2) + '\n')
    print(f'{len(results["accepted"])} unmodified copies accepted, {len(results["rejected"])} changes '
          f'refused at their named places; logs: {logs}', flush=True)


if __name__ == '__main__':
    sys.exit(main())
