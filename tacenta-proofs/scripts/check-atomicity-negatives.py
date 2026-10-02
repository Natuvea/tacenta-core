#!/usr/bin/env python3
"""Plant one write in a copy of each translated lifecycle body and require the frame proof to fail.

`Translation/UnitLifecycleAtomicity.lean` proves, for `decrypt_ratchet`, `decrypt`, `encrypt` and
`establish_responder`, that a refusal returns the state it was given (with the one recorded
exception in `encrypt`) and that a success writes a named set of fields. Those proofs are one walk
over the generated body. A walk that could not tell a body with a write before a refusal from one
without would prove the same statements of any body, so this script holds the walk to it.

For each function it extracts the body from the generated `TacentaSessionUnit.lean`, renames the
copy, and:

  1. requires the UNMODIFIED copy to be accepted by the same proof the module uses (a harness that
     cannot prove the real body proves nothing about a mutant);
  2. applies one textual change to the copy, a write to the state on a refusal path or an extra
     field written on a success path, checks that the change was made exactly where the table says,
     and requires the proof to FAIL on a goal that shows the planted write (an unsolved goal or a failed `rfl`).

A timeout, a compiler that does not start, a syntax error in the copy, an unknown identifier and an
unrelated failure never count as a rejected mutation. These are proof-dependency controls: they
hold the proof method against a changed body, not the Rust against a changed source. Regenerating
the translation from a changed Rust source needs the pinned Linux toolchain.

Dependencies must be built (`lake build Translation.UnitLifecycleAtomicity`). No source, olean or git
state changes.
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
GENERATED = ROOT / 'translation/Translation/TacentaSessionUnit.lean'
MODULE = ROOT / 'translation/Translation/UnitLifecycleAtomicity.lean'

# target -> (generated definition, binders, statement of the copy, the module theorem whose proof is reused)
TARGETS = {
    'decrypt_ratchet': (
        'lifecycle.Session.decrypt_ratchet',
        '{R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) '
        '(self : lifecycle.Session) (message : Slice U8) (rng : R)',
        'Post (RatchetFrame self) (lifecycle.Session.decrypt_ratchet_ctl rc crc self message rng)',
        'decrypt_ratchet_frame',
    ),
    'decrypt': (
        'lifecycle.Session.decrypt',
        '{R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) '
        '(self : lifecycle.Session) (message : Slice U8) (rng : R)',
        'Post (DecryptFrame self) (lifecycle.Session.decrypt_ctl rc crc self message rng)',
        'decrypt_frame',
    ),
    'encrypt': (
        'lifecycle.Session.encrypt',
        '{R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) '
        '(self : lifecycle.Session) (plaintext : Slice U8) (rng : R)',
        'Post (EncryptFrame self) (lifecycle.Session.encrypt_ctl rc crc self plaintext rng)',
        'encrypt_frame',
    ),
    'establish_responder': (
        'lifecycle.establish_responder',
        '{R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) '
        '(identity : lifecycle.Identity) (store : lifecycle.PrekeyStore) '
        '(message : Slice U8) (rng : R)',
        'Post (ResponderFrame store) '
        '(lifecycle.establish_responder_ctl rc crc identity store message rng)',
        'establish_responder_frame',
    ),
}

# (target, name, pattern, replacement, marker, minimum occurrences in the body, occurrence[, forms]).
# The pattern is a regular expression; the match at index `occurrence` (0 is the first) is
# replaced, and the table says how many matches the unmodified body must have so that a
# regenerated translation that moves the text makes this script refuse instead of silently testing
# something else. The occurrence matters: a pattern can match first inside an arm where the planted
# write changes nothing (clearing a field of a session whose field is already `none`), and such a
# plant is refused only because the walk is syntactic, not because it found a real write. The two
# rows with occurrence 1 skip a first match that sits in the `| none =>` arm of a match on the field
# itself; the others plant at their first match, which is on a path where the field can differ. The
# marker is a regular expression that the unsolved goal must contain: the planted field,
# anchored to the side of the goal the unmodified proof never prints. A variable bound by a bind
# in the body is shown as an anonymous hypothesis (a dagger-marked name, U+271D after `a`), or under
# the name the walk gave it, so a marker for a planted `braid_candidate` is `braid := ` followed by
# a dagger-marked name, which the unmodified state `self.braid` never shows. The dagger is written
# as `\u271d` in the patterns below.
MUTANTS = [
    ('decrypt_ratchet', 'aead-refusal-commits-agreement',
     r'ok \(core\.result\.Result\.Err lifecycle\.Error\.Aead, self, rng1\)',
     'ok (core.result.Result.Err lifecycle.Error.Aead, { self with braid := braid_candidate }, rng1)',
     r'braid := a\u271d', 1, 0),
    ('decrypt_ratchet', 'triple-refusal-commits-ratchet-key',
     r'\(lifecycle\.Error\.Triple error\), self,',
     '(lifecycle.Error.Triple error), { self with ratchet_private := candidate_key },',
     r'ratchet_private := a\u271d', 1, 0),
    ('decrypt_ratchet', 'success-also-writes-pending-initial',
     r'triple := triple_candidate, braid := braid_candidate\n',
     'triple := triple_candidate, braid := braid_candidate, pending_initial := none\n',
     r'pending_initial := none', 1, 0),
    ('decrypt', 'refusal-clears-pending-initial',
     r'ok \(r1, self1, rng1\)',
     'ok (r1, { self1 with pending_initial := none }, rng1)',
     r'pending_initial := none,\s+established_ephemeral := [^\n]*\}\s*=\s*self\b', 2, 0),
    ('decrypt', 'repeat-refusal-drops-established-ephemeral',
     r'lifecycle\.Error\.NotARepeatedInitial,\s+self,',
     'lifecycle.Error.NotARepeatedInitial, { self with established_ephemeral := none },',
     r'established_ephemeral := none', 3, 1),
    ('encrypt', 'triple-refusal-commits-agreement',
     r'ok \(core\.result\.Result\.Err \(lifecycle\.Error\.Triple error\), self, rng1\)',
     'ok (core.result.Result.Err (lifecycle.Error.Triple error), { self with braid := braid_next }, rng1)',
     r'braid := (a\u271d|braidNext)', 1, 0),
    ('encrypt', 'terminal-guard-clears-pending-initial',
     r'ok \(core\.result\.Result\.Err lifecycle\.Error\.AgreementFailed, self, rng\)',
     'ok (core.result.Result.Err lifecycle.Error.AgreementFailed, { self with pending_initial := none }, rng)',
     r'pending_initial := none', 1, 0),
    ('encrypt', 'success-also-clears-pending-initial',
     r'\{ self with triple := candidate, braid := braid_next \}',
     '{ self with triple := candidate, braid := braid_next, pending_initial := none }',
     r'pending_initial := none', 2, 1),
    # The recorded exception arm of `encrypt`: the walk's step there is a conjunction of two `rfl`s, so
    # a plant is refused as an `Application type mismatch` and not as an unsolved goal. The eighth
    # element names the form accepted in place of the default, and the marker is anchored to the
    # planted value in the printed goal.
    ('encrypt', 'exception-arm-also-clears-pending-initial',
     r'\{ self with braid := braid_next \}',
     '{ self with braid := braid_next, pending_initial := none }',
     r'pending_initial := none,\s+established_ephemeral := self\.established_ephemeral \}\s*=', 1, 0,
     ('Application type mismatch',)),
    ('encrypt', 'exception-arm-returns-a-different-error',
     r'ok \(core\.result\.Result\.Err lifecycle\.Error\.AgreementFailed,\n\s+\{ self with braid := braid_next \}, rng1\)',
     'ok (core.result.Result.Err lifecycle.Error.Aead,\n        { self with braid := braid_next }, rng1)',
     r'Error\.Aead\s*=\s*lifecycle\.Error\.AgreementFailed', 1, 0, ('Application type mismatch',)),
    ('establish_responder', 'refusal-after-receive-changes-store',
     r'ok \(r8, our_prekeys, rng1\)',
     'ok (r8, { our_prekeys with next_id := 0#u32 }, rng1)',
     r'next_id := 0#u32', 1, 0),
    ('establish_responder', 'handshake-refusal-changes-store',
     r'\(lifecycle\.Error\.Handshake error\),\s+our_prekeys, rng\)',
     '(lifecycle.Error.Handshake error), { our_prekeys with next_id := 0#u32 }, rng)',
     r'next_id := 0#u32', 1, 0),
]

# Failures that mean the mutation or the harness is wrong, not that the proof refused the write.
REFUSAL_FORMS = ('unsolved goals', 'Tactic `rfl` failed')
NOT_A_REFUSAL = ('unknown identifier', 'unknown constant', 'unexpected token', "expected '",
                 'type mismatch', 'function expected', 'unknown namespace')


def extract(text, name):
    start = re.search(r'^def ' + re.escape(name) + r'$', text, re.M)
    if start is None:
        raise SystemExit(f'generated definition not found: {name}')
    end = re.search(r'\n\n(?=\S)', text[start.end():])
    if end is None:
        raise SystemExit(f'end of generated definition not found: {name}')
    body = text[start.start():start.end() + end.start()]
    renamed, n = re.subn(r'^def ' + re.escape(name) + r'$', 'def ' + name + '_ctl', body, count=1, flags=re.M)
    assert n == 1
    return renamed


def module_proof(module_text, theorem, name):
    """The proof of `theorem` as the module writes it, aimed at the renamed copy of `name`."""
    found = re.search(r'^theorem ' + re.escape(theorem) + r'\b.*?:= by\n(.*?)(?=^\S)',
                      module_text, re.M | re.S)
    if found is None:
        raise SystemExit(f'proof of {theorem} not found in {MODULE.name}')
    proof, n = re.subn(r'^(\s*unfold ' + re.escape(name) + r')$', r'\1_ctl', found.group(1),
                       count=1, flags=re.M)
    if n != 1:
        raise SystemExit(f'the proof of {theorem} does not start by unfolding {name}')
    return proof.rstrip('\n') + '\n'


def control_source(target, copy, module_text):
    name, binders, statement, theorem = TARGETS[target]
    return (
        'import Translation.UnitLifecycleAtomicity\n'
        'open Aeneas Aeneas.Std Result ControlFlow Error\n'
        'set_option maxHeartbeats 1000000\n'
        'set_option maxRecDepth 2048\n'
        'noncomputable section\n'
        'namespace tacenta_session_unit\n\n'
        f'{copy}\n\n'
        'end tacenta_session_unit\n\n'
        'open tacenta_session_unit Tacenta.UnitLifecycleAtomicity\n\n'
        f'theorem control_{target} {binders} :\n    {statement} := by\n'
        + module_proof(module_text, theorem, name)
    )


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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=300)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='atomicity-logs-'))
    logs.mkdir(parents=True, exist_ok=True)
    generated = GENERATED.read_text()
    results = {
        'generated_sha256': hashlib.sha256(generated.encode()).hexdigest(),
        'module_sha256': hashlib.sha256(MODULE.read_bytes()).hexdigest(),
        'accepted': {}, 'rejected': {},
    }
    module_text = MODULE.read_text()
    bodies = {t: extract(generated, TARGETS[t][0]) for t in TARGETS}
    with tempfile.TemporaryDirectory(prefix='atomicity-controls-') as tmp:
        tmp = Path(tmp)
        for target, body in bodies.items():
            path = tmp / f'baseline_{target}.lean'
            path.write_text(control_source(target, body, module_text))
            status, output = run_lean(path, logs / f'baseline_{target}.log', args.timeout)
            if status or 'sorry' in output or 'error' in output:
                raise SystemExit(f'BASELINE FAILED for {target}; no mutation evidence: '
                                 f'{logs / f"baseline_{target}.log"}')
            results['accepted'][target] = status
            print(f'PASS: the unmodified copy of {target} is accepted by the module proof', flush=True)
        for target, name, pattern, replacement, marker, minimum, occurrence, *extra in MUTANTS:
            body = bodies[target]
            matches = list(re.finditer(pattern, body))
            if len(matches) < minimum or len(matches) <= occurrence:
                raise SystemExit(f'Target changed for {name}: expected at least {minimum} '
                                 f'occurrence(s) of the pattern in {target}, found {len(matches)}')
            hit = matches[occurrence]
            mutated = body[:hit.start()] + replacement + body[hit.end():]
            if mutated == body:
                raise SystemExit(f'Mutation {name} left the body unchanged')
            path = tmp / f'{target}_{name}.lean'
            path.write_text(control_source(target, mutated, module_text))
            log = logs / f'{target}_{name}.log'
            status, output = run_lean(path, log, args.timeout)
            forms = extra[0] if extra else REFUSAL_FORMS
            not_refusals = ([bad for bad in NOT_A_REFUSAL if bad != 'type mismatch'] if extra
                            else NOT_A_REFUSAL)
            refused = (status != 0 and any(form in output for form in forms)
                       and re.search(marker, output)
                       and not any(bad in output for bad in not_refusals))
            if not refused:
                raise SystemExit(f'FAILED control {target}/{name}: expected a refused goal matching '
                                 f'`{marker}`, exit={status}; {log}')
            results['rejected'][f'{target}/{name}'] = {'exit': status, 'marker': marker}
            print(f'PASS: {target}/{name} rejected by Lean (the refused goal matches `{marker}`)', flush=True)
    (logs / 'result.json').write_text(json.dumps(results, indent=2) + '\n')
    print(f'{len(TARGETS)} unmodified bodies accepted, {len(MUTANTS)} planted changes rejected; '
          f'logs: {logs}', flush=True)


if __name__ == '__main__':
    sys.exit(main())
