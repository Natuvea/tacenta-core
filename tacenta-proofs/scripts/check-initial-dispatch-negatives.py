#!/usr/bin/env python3
"""Compile disposable proof copies; accept only the expected type failures.

These are proof-dependency controls, not protocol/runtime mutation tests.
Dependencies must already be built (`lake build Translation.UnitLifecycleInitialDispatch`).
No source, olean, or git worktree is changed by this script.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import signal
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'translation/Translation/UnitLifecycleInitialDispatch.lean'


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
    parser.add_argument('--timeout', type=int, default=180)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='initial-dispatch-logs-'))
    logs.mkdir(parents=True, exist_ok=True)
    source = SOURCE.read_text()
    results = {'source_sha256': hashlib.sha256(source.encode()).hexdigest(), 'mutations': {}}
    mutants = [
        ('bypass-ephemeral',
         '(hne : vecOf established ≠ vecOf decoded.ephemeral)',
         '(hne : vecOf established = vecOf decoded.ephemeral)', 'hne'),
        ('bypass-identity',
         'by_cases hi : vecOf decoded.identity =\n'
         '      Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public)',
         'by_cases hi : True', 'hi'),
        ('weaken-terminal-guard',
         '(hfailed : Model.Lifecycle.agreementFailed model = true) :',
         '(hfailed : Model.Lifecycle.agreementFailed model = false) :', 'hfailed'),
        ('restore-arbitrary-ceiling',
         '      oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →\n'
         '      ∃ draw rest, trace innerRng = draw :: rest',
         '      oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →\n'
         '      Model.Lifecycle.random32 oracle = none → False',
         'evidence.randomDraw input'),
        ('flatten-encrypt-generated-family',
         '  | .tripleRefusal _ _ _ _ =>\n'
         '      EncryptTripleRouteEvidence rc crc trace dh kem K view oracle real model plaintext rng',
         '  | .tripleRefusal _ _ _ _ =>\n'
         '      EncryptRouteEvidence rc crc trace dh K view oracle real model plaintext rng',
         'providers.noDrawRefusal'),
        ('invert-encrypt-no-draw-refusal-provider',
         'Model.Lifecycle.braidSendNeedsDraw model.braid = false',
         'Model.Lifecycle.braidSendNeedsDraw model.braid = true',
         'hdraw'),
        ('invert-encrypt-draw-refusal-provider',
         'Model.Lifecycle.braidSendNeedsDraw model.braid = true',
         'Model.Lifecycle.braidSendNeedsDraw model.braid = false',
         'hdraw'),
        ('invert-encrypt-no-draw-success-provider',
         'Model.Lifecycle.braidSendNeedsDraw model.braid = false',
         'Model.Lifecycle.braidSendNeedsDraw model.braid = true',
         'hdraw'),
        ('invert-encrypt-draw-success-provider',
         'Model.Lifecycle.braidSendNeedsDraw model.braid = true',
         'Model.Lifecycle.braidSendNeedsDraw model.braid = false',
         'hdraw'),
        ('invert-encrypt-braid-no-draw-trace',
         'Model.Lifecycle.braidSendNeedsDraw model.braid = false',
         'Model.Lifecycle.braidSendNeedsDraw model.braid = true',
         'hdraw'),
        ('invert-encrypt-braid-draw-trace',
         'Model.Lifecycle.braidSendNeedsDraw model.braid = true',
         'Model.Lifecycle.braidSendNeedsDraw model.braid = false',
         'hdraw'),
        ('invert-encrypt-braid-draw-post',
         'Model.Lifecycle.braidSendNeedsDraw model.braid = true',
         'Model.Lifecycle.braidSendNeedsDraw model.braid = false',
         'hdraw'),
    ]
    with tempfile.TemporaryDirectory(prefix='initial-dispatch-controls-') as tmp:
        tmp = Path(tmp)
        baseline = tmp / 'Baseline.lean'
        baseline.write_text(source)
        status, output = run_lean(baseline, logs / 'baseline.log', args.timeout)
        if status or 'declaration uses `sorry`' in output:
            raise SystemExit(f'BASELINE FAILED; no mutation evidence: {logs / "baseline.log"}')
        results['baseline_exit'] = status
        print('PASS: unmodified source elaborates', flush=True)
        for name, before, after, premise in mutants:
            # The guard premise occurs once: the mutation must target the
            # concrete terminal-discharge theorem, not a duplicated signature.
            # For the terminal guard, mutate its concrete-discharge theorem only.
            mutated = tmp / f'{name}.lean'
            if name == 'bypass-ephemeral':
                marker = '| initialAgreementAccepted'
                start = source.find(marker)
                target = source.find(before, start)
                if start < 0 or target < 0:
                    raise SystemExit(f'Target changed for {name}: accepted branch premise is missing')
                mutated.write_text(source[:target] + source[target:].replace(before, after, 1))
            elif name == 'weaken-terminal-guard':
                marker = 'theorem initial_ratchet_refines_terminal'
                start = source.find(marker)
                target = source.find(before, start)
                if start < 0 or target < 0:
                    raise SystemExit(f'Target changed for {name}: named discharge premise is missing')
                mutated.write_text(source[:target] + source[target:].replace(before, after, 1))
            elif name.startswith('invert-encrypt-'):
                markers = {
                    'invert-encrypt-no-draw-refusal-provider': '  noDrawRefusal :',
                    'invert-encrypt-draw-refusal-provider': '  drawRefusal :',
                    'invert-encrypt-no-draw-success-provider': '  noDrawSuccess :',
                    'invert-encrypt-draw-success-provider': '  drawSuccess :',
                    'invert-encrypt-braid-no-draw-trace': '  noDrawTrace :',
                    'invert-encrypt-braid-draw-trace': '  drawTrace :',
                    'invert-encrypt-braid-draw-post': '  drawPost :',
                }
                start = source.find(markers[name])
                target = source.find(before, start)
                if start < 0 or target < 0:
                    raise SystemExit(f'Target changed for {name}: named provider guard is missing')
                mutated.write_text(source[:target] + source[target:].replace(before, after, 1))
            else:
                if source.count(before) != 1:
                    raise SystemExit(f'Target changed for {name}: expected 1 occurrence')
                mutated.write_text(source.replace(before, after, 1))
            log = logs / f'{name}.log'
            status, output = run_lean(mutated, log, args.timeout)
            if name == 'flatten-encrypt-generated-family':
                mismatch = re.search(
                    r'error: Application type mismatch: The argument\s+'
                    r'providers\.noDrawRefusal.+?has type\s+'
                    r'EncryptEvidenceForGeneratedPrefix.+?but is expected to have type\s+'
                    r'EncryptTripleRouteEvidence', output, re.S)
            else:
                mismatch = re.search(
                    r'error: Application type mismatch: The argument\s+' + premise +
                    r'\s+has type\s+.+?but is expected to have type', output, re.S)
            if status != 1 or mismatch is None or not re.search(r'\b' + premise + r'\b', output):
                raise SystemExit(f'FAILED control {name}: expected premise type failure, exit={status}; {log}')
            results['mutations'][name] = {'exit': status, 'premise': premise}
            print(f'PASS: {name} rejected by Lean (exit 1, premise {premise})', flush=True)
    (logs / 'result.json').write_text(json.dumps(results, indent=2) + '\n')
    print(f'{len(mutants)} proof-dependency mutations rejected; logs: {logs}', flush=True)


if __name__ == '__main__':
    main()
