#!/usr/bin/env python3
"""Hold the `decrypt_ratchet` refinement, its retry-loop induction and its refusal closure against a planted fault.

`Translation/UnitLifecycleRetryLoopT3.lean` relates the generated eviction retry loop to the model loop
for every fuel (`receive_with_eviction_loop_refines`), and `Translation/UnitLifecycleDecryptRatchetT3.lean`
composes it into `decrypt_ratchet_refines`, whose conclusion has one open disjunct, `TripleRefusalOpen`.
`Translation/UnitLifecycleTripleRefusalT3.lean` relates every refusal of one Triple receive to the model's
(`triple_receive_refusal_refines`), and `Translation/UnitLifecycleDecryptRatchetCompleteT3.lean` closes the
disjunct with it (`decrypt_ratchet_refines_complete`); `Translation/UnitLifecycleDecryptRatchetCompleteScreen.lean`
shows the closed path reached. A proof that Lean accepts after the fact it rests on is removed would hold
nothing, and an open disjunct that grew would quietly absorb runs the theorem claims to cover, so this script
makes one change to a copy of a module and requires Lean to refuse it:

  * the retry loop with a batch relation whose covering arm no longer bounds the model batch;
  * the retry loop with an invariant that no longer maps the pending refusal to the model's;
  * the retry loop with a model stop lemma that no longer asks the refusal to be unclassified;
  * the retry loop with a first-batch lemma whose store bound leaves no room under the cap;
  * the composition with an open disjunct that holds of every refusal;
  * the composition with an open disjunct that also holds of the two full-store refusals;
  * the composition with a run record whose receive bounds leave no room under the cap;
  * the composition with a run record whose draw is not the trace's;
  * the composition with an open disjunct that holds of every refusal, with its pins kept;
  * the refusal refinement with the classical out-of-order refusal named as a missing chain;
  * the refusal refinement with the chain derivation's refusal no longer located past `u32::MAX`;
  * the refusal refinement with the sparse epoch bound weakened to the type's ceiling;
  * the refusal refinement with the Triple model reason fixed to one refusal;
  * the closure with a bridge that no longer gives the public mapping;
  * the closure with the open disjunct put back into the complete statement, with its pins kept;
  * the screen with the model's refusal at the screen's state named as a missing chain.

The changes are checked on copies without the module's pins, so that the refusal comes from a proof and
not from a pin, except the two marked "with its pins kept", which require the pin to refuse them. The
unmodified copies must be accepted first. A timeout, a compiler that does not start, a syntax error and an
unrelated failure never count as a refusal. These are proof-dependency controls on copies of the Lean; no
source, olean or git state changes.

Dependencies must be built (`lake build Translation.UnitLifecycleDecryptRatchetCompleteScreen`).
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
LOOP = ROOT / 'translation/Translation/UnitLifecycleRetryLoopT3.lean'
T3 = ROOT / 'translation/Translation/UnitLifecycleDecryptRatchetT3.lean'
REFUSAL = ROOT / 'translation/Translation/UnitLifecycleTripleRefusalT3.lean'
COMPLETE = ROOT / 'translation/Translation/UnitLifecycleDecryptRatchetCompleteT3.lean'
SCREEN = ROOT / 'translation/Translation/UnitLifecycleDecryptRatchetCompleteScreen.lean'

PROOF = (r'unsolved goals|Application type mismatch|Type mismatch|omega could not prove|made no progress'
         r'|rcases|Dependent elimination failed|Insufficient number of fields')

# (copy, name, pattern, replacement, a regular expression the refused output must contain)
MUTANTS = [
    ('loop', 'batch-covers-arm-without-the-model-bound',
     r'concrete\.val = model ∨ \(len ≤ concrete\.val ∧ len ≤ model\)',
     'concrete.val = model ∨ (len ≤ concrete.val ∧ True)', PROOF),
    ('loop', 'invariant-without-the-pending-map',
     r'  pending : tripleReceiveRefusalOfReal pending = some modelPending\n',
     '  pending : True\n', PROOF),
    ('loop', 'stop-lemma-without-the-classifier',
     r'    \(hFull : Model\.Lifecycle\.fullStore reason = none\) :\n',
     '    (hFull : True) :\n', PROOF),
    ('loop', 'first-batch-without-the-store-margin',
     r'\(hstore : Model\.Triple\.classicalSkippedLength modelState \+ Model\.State\.maxSkippedStore ≤',
     '(hstore : Model.Triple.classicalSkippedLength modelState ≤', PROOF),
    ('t3', 'open-disjunct-of-every-refusal',
     r'  ∃ reason, output\.1 = \.Err \(\.Triple reason\) ∧ lifecycle\.full_store reason = ok none\n',
     '  ∃ reason, output.1 = .Err reason\n', PROOF),
    ('t3', 'open-disjunct-with-the-full-store-refusals',
     r'  ∃ reason, output\.1 = \.Err \(\.Triple reason\) ∧ lifecycle\.full_store reason = ok none\n',
     '  ∃ reason, output.1 = .Err (.Triple reason)\n', PROOF),
    ('t3', 'run-bounds-without-the-store-margin',
     r'  classicalStore : state\.classical\.skipped\.length \+ Model\.State\.maxSkippedStore ≤\n',
     '  classicalStore : state.classical.skipped.length ≤\n', PROOF),
    ('t3', 'run-draw-not-tied-to-the-trace',
     r'  draw : ∃ draw rest, trace rng = draw :: rest\n',
     '  draw : ∃ (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),\n'
     '    draw :: rest = draw :: rest\n', PROOF),
    ('t3pinned', 'open-disjunct-of-every-refusal-pinned',
     r'  ∃ reason, output\.1 = \.Err \(\.Triple reason\) ∧ lifecycle\.full_store reason = ok none\n',
     '  ∃ reason, output.1 = .Err reason\n',
     r'Docstring on `#guard_msgs` does not match generated message'),
    ('refusal', 'tail-out-of-order-named-as-missing-chain',
     r'if n\.val < st2\.nr then \.error \.outOfOrder',
     'if n.val < st2.nr then .error .noReceivingChain', PROOF),
    ('refusal', 'derivation-refusal-not-located',
     r'e = RatchetError\.ChainExhausted ∧ Std\.U32\.max < start_n\.val \+ count\.val',
     'e = RatchetError.ChainExhausted ∧ start_n.val + count.val ≤ start_n.val + count.val + 1', PROOF),
    ('refusal', 'sparse-epoch-bound-at-the-ceiling',
     r'    \(hepoch : s\.epoch\.val \+ 1 < Std\.U64\.max\)\n',
     '    (hepoch : s.epoch.val < Std.U64.max)\n', PROOF),
    ('refusal', 'triple-model-reason-fixed',
     r'\(output\.map Tacenta\.SessionUnitTripleT3\.spqrOutputOf\) = \.error modelReason ⦄',
     '(output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) = .error (.classical .outOfOrder) ⦄', PROOF),
    ('complete', 'bridge-without-the-public-mapping',
     r'    ∃ modelReason, tripleReceiveRefusalOfReal realReason = some modelReason ∧\n',
     '    ∃ modelReason,\n', PROOF),
    ('completepinned', 'complete-statement-with-the-open-disjunct-pinned',
     r'        StepRefines trace dh oracle\.braidKem output\n'
     r'          \(Model\.Lifecycle\.decryptRatchet view oracle model \(sliceOf message\)\)\n\n',
     '        (StepRefines trace dh oracle.braidKem output\n'
     '          (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) ∨\n'
     '          TripleRefusalOpen output)\n\n',
     r'Docstring on `#guard_msgs` does not match generated message'),
    ('screen', 'screen-model-reason-misnamed',
     r'      \.error \(\.classical \.outOfOrder\) ∧\n    Model\.Lifecycle\.fullStore',
     '      .error (.classical .noReceivingChain) ∧\n    Model.Lifecycle.fullStore', PROOF),
]

NOT_A_REFUSAL = ('unknown identifier', 'unknown constant', 'unexpected token', "expected '",
                 'unknown namespace', 'does not contain')


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


def check_refused(name, status, output, marker, log):
    refused = (status != 0 and 'error' in output and re.search(marker, output)
               and not any(bad in output for bad in NOT_A_REFUSAL))
    if not refused:
        raise SystemExit(f'FAILED control {name}: expected Lean to refuse it with `{marker}`, '
                         f'exit={status}; {log}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=600)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='decrypt-ratchet-logs-'))
    logs.mkdir(parents=True, exist_ok=True)
    loop, t3 = LOOP.read_text(), T3.read_text()
    refusal, complete, screen = REFUSAL.read_text(), COMPLETE.read_text(), SCREEN.read_text()
    sources = {
        'loop': without_pins(loop, LOOP),
        't3': without_pins(t3, T3),
        't3pinned': t3,
        'refusal': without_pins(refusal, REFUSAL),
        'complete': without_pins(complete, COMPLETE),
        'completepinned': complete,
        'screen': without_pins(screen, SCREEN),
    }
    results = {
        'loop_sha256': hashlib.sha256(loop.encode()).hexdigest(),
        't3_sha256': hashlib.sha256(t3.encode()).hexdigest(),
        'refusal_sha256': hashlib.sha256(refusal.encode()).hexdigest(),
        'complete_sha256': hashlib.sha256(complete.encode()).hexdigest(),
        'screen_sha256': hashlib.sha256(screen.encode()).hexdigest(),
        'accepted': [], 'rejected': {},
    }
    with tempfile.TemporaryDirectory(prefix='decrypt-ratchet-controls-') as tmp:
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
        for label, name, pattern, replacement, marker in MUTANTS:
            source = sources[label]
            found = len(re.findall(pattern, source))
            if found != 1:
                raise SystemExit(f'Target changed for {name}: expected 1 occurrence of the '
                                 f'pattern in the {label} copy, found {found}')
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
    print(f'{len(results["accepted"])} unmodified copies accepted, {len(results["rejected"])} changes '
          f'refused; logs: {logs}', flush=True)


if __name__ == '__main__':
    sys.exit(main())
