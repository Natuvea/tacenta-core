#!/usr/bin/env python3
"""Hold the restated dispatch records and their witnesses against a changed statement.

`Translation/UnitLifecycleRepair.lean` shows that a view meets the send direction of the codeword
relation (`codewordViewSendOf_satisfiable`) and says when the two scoped chunk fields of
the Braid evidence record can be met (`scoped_chunk_fields_iff_consistent`); `UnitLifecycleT3.lean`
derives the run's candidate public key from the oracle (`candidate_public_eq_draw`). A witness
proof that Lean accepts for a wrong statement, or for a weaker definition, would make these hold
nothing, so this script makes one change to a copy of each and requires Lean to refuse it:

  * the module with a witness that does not send the codeword (the constant empty codeword);
  * the module claiming the old two-sided statement `CodewordViewOf` in place of the send-only one;
  * the module with a consistent-run definition that drops the codeword condition;
  * the module with a consistent-run definition that drops the fit condition;
  * the lemma with its link between the draw and the candidate key removed.

The unmodified module and the unmodified lemma must be accepted first. A timeout, a compiler that
does not start, a syntax error and an unrelated failure never count as a refusal. These are
proof-dependency controls on copies of the Lean; no source, olean or git state changes.

Dependencies must be built (`lake build Translation.UnitLifecycleRepair`).
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
MODULE = ROOT / 'translation/Translation/UnitLifecycleRepair.lean'
T3 = ROOT / 'translation/Translation/UnitLifecycleT3.lean'

# (name, pattern, replacement, a regular expression the refused output must contain)
MODULE_MUTANTS = [
    ('witness-does-not-send-the-codeword',
     r'modelCodewordOf \(Classical\.choose h\)',
     '{ index := 0, data := [] }',
     r'Tactic `rewrite` failed|unsolved goals'),
    ('claims-the-old-two-sided-statement',
     r'theorem codewordViewSendOf_satisfiable : ∃ view, CodewordViewSendOf view :=',
     'theorem codewordViewSendOf_satisfiable : ∃ view, CodewordViewOf view :=',
     r'Application type mismatch[^\n]*\n[^\n]*\n[^\n]*|CodewordViewOf'),
    ('consistent-run-without-the-codeword',
     r'\(match real\.ag_chunk with\n      \| none => True\n      \| some chunk => BCodewordOf source \{ index := chunk\.index, data := chunk\.data \}\) ∧\n',
     '',
     r'Invalid `⟨\.\.\.⟩` notation|No goals to be solved|unsolved goals'),
    ('consistent-run-without-the-fit',
     r' ∧\n    Tacenta\.SessionUnitBraidT3\.HonestChunk st\n      \(Model\.Lifecycle\.braidMessageOf \(constView source\) st model\)\n\n/-- The two chunk fields',
     '\n\n/-- The two chunk fields',
     r'Invalid `⟨\.\.\.⟩` notation|No goals to be solved|unsolved goals'),
]

# the lemma copied out of `UnitLifecycleT3.lean`, with one change
LEMMA = 'candidate_public_eq_draw'
LEMMA_MUTANTS = [
    ('draw-not-linked-to-the-candidate-key',
     r'\(hdraw : Model\.Lifecycle\.random32 oracle = some \(draw, oracleNext\)\)',
     '(hdraw : True)',
     r'Application type mismatch'),
]

NOT_A_REFUSAL = ('unknown identifier', 'unknown constant', 'unexpected token', "expected '",
                 'unknown namespace')


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


def lemma_source():
    text = T3.read_text()
    found = re.search(r'^theorem ' + LEMMA + r'\b.*?(?=^\S)', text, re.M | re.S)
    if found is None:
        raise SystemExit(f'{LEMMA} not found in {T3.name}')
    body = found.group(0)
    body = re.sub(r'^theorem ' + LEMMA + r'\b', 'theorem ' + LEMMA + '_ctl', body, count=1, flags=re.M)
    return (
        'import Translation.UnitLifecycleT3\n'
        'open Aeneas Aeneas.Std Result\n'
        'open tacenta_session_unit\n'
        'namespace Tacenta.UnitLifecycleT3\n\n'
        f'{body}\n'
        'end Tacenta.UnitLifecycleT3\n'
    )


def check_refused(name, status, output, marker, log):
    refused = (status != 0 and 'error' in output and re.search(marker, output)
               and not any(bad in output for bad in NOT_A_REFUSAL))
    if not refused:
        raise SystemExit(f'FAILED control {name}: expected Lean to refuse it with `{marker}`, '
                         f'exit={status}; {log}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=300)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='repair-logs-'))
    logs.mkdir(parents=True, exist_ok=True)
    module = MODULE.read_text()
    lemma = lemma_source()
    results = {
        'module_sha256': hashlib.sha256(module.encode()).hexdigest(),
        'accepted': [], 'rejected': {},
    }
    with tempfile.TemporaryDirectory(prefix='repair-controls-') as tmp:
        tmp = Path(tmp)
        for label, text in (('module', module), ('lemma', lemma)):
            path = tmp / f'baseline_{label}.lean'
            path.write_text(text)
            status, output = run_lean(path, logs / f'baseline_{label}.log', args.timeout)
            if status or 'sorry' in output or 'error' in output:
                raise SystemExit(f'BASELINE FAILED for the {label}; no mutation evidence: '
                                 f'{logs / f"baseline_{label}.log"}')
            results['accepted'].append(label)
            print(f'PASS: the unmodified {label} is accepted', flush=True)
        for source, mutants, label in ((module, MODULE_MUTANTS, 'module'),
                                       (lemma, [(n, p, r, m) for n, p, r, m in LEMMA_MUTANTS], 'lemma')):
            for name, pattern, replacement, marker in mutants:
                found = len(re.findall(pattern, source))
                if found != 1:
                    raise SystemExit(f'Target changed for {name}: expected 1 occurrence of the '
                                     f'pattern in the {label}, found {found}')
                mutated, n = re.subn(pattern, lambda _m: replacement, source, count=1)
                assert n == 1 and mutated != source
                path = tmp / f'{label}_{name}.lean'
                path.write_text(mutated)
                log = logs / f'{label}_{name}.log'
                status, output = run_lean(path, log, args.timeout)
                check_refused(name, status, output, marker, log)
                results['rejected'][f'{label}/{name}'] = {'exit': status, 'marker': marker}
                print(f'PASS: {label}/{name} refused by Lean (output matches `{marker}`)', flush=True)
    (logs / 'result.json').write_text(json.dumps(results, indent=2) + '\n')
    print(f'2 unmodified inputs accepted, {len(results["rejected"])} changes refused; logs: {logs}',
          flush=True)


if __name__ == '__main__':
    sys.exit(main())
