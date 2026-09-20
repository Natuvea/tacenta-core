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
         'by_cases he : vecOf established = vecOf decoded.ephemeral',
         'by_cases he : True', 'he'),
        ('bypass-identity',
         'by_cases hi : vecOf decoded.identity =\n'
         '            Model.PersistedState.SessionState.encodeEc (dh.publicKey real.peer_identity_public)',
         'by_cases hi : True', 'hi'),
        ('weaken-terminal-guard',
         '(hfailed : Model.Lifecycle.agreementFailed model = true) :',
         '(hfailed : Model.Lifecycle.agreementFailed model = false) :', 'hfailed'),
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
            expected = 2 if name == 'weaken-terminal-guard' else 1
            if source.count(before) != expected:
                raise SystemExit(f'Target changed for {name}: expected {expected} occurrences')
            # For the terminal guard, mutate its concrete-discharge theorem only.
            mutated = tmp / f'{name}.lean'
            mutated.write_text(source.replace(before, after, 1))
            log = logs / f'{name}.log'
            status, output = run_lean(mutated, log, args.timeout)
            mismatch = re.search(
                r'error: Application type mismatch: The argument\s+' + premise +
                r'\s+has type\s+.+?but is expected to have type', output, re.S)
            if status != 1 or mismatch is None or not re.search(r'\b' + premise + r'\b', output):
                raise SystemExit(f'FAILED control {name}: expected premise type failure, exit={status}; {log}')
            results['mutations'][name] = {'exit': status, 'premise': premise}
            print(f'PASS: {name} rejected by Lean (exit 1, premise {premise})', flush=True)
    (logs / 'result.json').write_text(json.dumps(results, indent=2) + '\n')
    print(f'3 proof-dependency mutations rejected; logs: {logs}', flush=True)


if __name__ == '__main__':
    main()
