#!/usr/bin/env python3
"""Hold the `decrypt_ratchet` refinement, its retry-loop induction and its refusal closure against a planted fault.

`Translation/UnitLifecycleRetryLoopT3.lean` relates the generated eviction retry loop to the model loop
for every fuel (`receive_with_eviction_loop_refines`), and `Translation/UnitLifecycleDecryptRatchetT3.lean`
composes it into `decrypt_ratchet_refines`, whose conclusion has one open disjunct, `TripleRefusalOpen`.
`Translation/UnitLifecycleTripleRefusalT3.lean` relates every refusal of one Triple receive to the model's
(`triple_receive_refusal_refines`), and `Translation/UnitLifecycleDecryptRatchetCompleteT3.lean` closes the
disjunct with it (`decrypt_ratchet_refines_complete`); `Translation/UnitLifecycleDecryptRatchetCompleteScreen.lean`
shows one state and one run on the model side of the closed path, and the generated output there under the boundary
records. A proof that Lean accepts after the fact it rests on is removed would hold nothing, and an open disjunct
that grew would quietly absorb runs the theorem claims to cover, so this script makes one change to a
copy of a module and requires Lean to refuse it, at a named place:

  * the retry loop with a batch relation whose covering arm no longer bounds the model batch
    (refused in the lemmas that use the relation);
  * the retry loop with an invariant that no longer maps the pending refusal to the model's
    (refused in `receive_with_eviction_loop_refines`);
  * the retry loop with a model stop lemma that no longer asks the refusal to be unclassified
    (refused in `receiveWithEvictionLoopResult_stop`);
  * the retry loop with a first-batch lemma whose store bound leaves no room under the cap
    (refused in `shortfall_classical_covers`);
  * the composition with an open disjunct that holds of every refusal, and one that also holds of
    the two full-store refusals (each refused in `tripleRefusalOpen_exactly`, the lemma that confines
    the disjunct, not only by the shape of the last step of the composition);
  * the composition with a run record whose receive bounds leave no room under the cap
    (refused in `RetryRunBounds.toRetryReceiveBounds`);
  * the composition with a run record whose draw is not the trace's (refused in the composition);
  * the composition with its conclusion widened to every refusal and its proof adjusted to match,
    leaving `TripleRefusalOpen` as it is (refused in `decrypt_ratchet_refines_unless_open`);
  * the composition and its screen together, with a run record that asks both skipped-key stores to
    be empty (refused in `evict_run_satisfiable`, the run that reaches an eviction round);
  * the composition with an open disjunct that holds of every refusal, with its pins kept (refused by
    the pin of `TripleRefusalOpen` itself: the refusal must be at that pin's line, so a copy without
    that pin is not counted as refused);
  * the refusal refinement with the classical out-of-order refusal named as a missing chain (refused in
    `ratchet_receive_tail_refusal_refines`), with the chain derivation's refusal no longer located past
    `u32::MAX` (refused in `ratchet_skip_refusal_refines`), with the sparse epoch bound weakened to the
    type's ceiling (refused in `spqr_receive_refusal_refines`), and with the Triple model reason fixed to
    one refusal (refused in `triple_receive_refusal_refines`);
  * the closure with a bridge that no longer gives the public mapping (refused in the bridge or in
    `openRefusal_closes`);
  * the closure with the open disjunct put back into the complete statement, with its pins kept (refused
    at the pin of `DecryptRatchetRefinesCompleteStatement`);
  * the closure's screen with the model's refusal at its state named as a missing chain (refused in
    `ref_model_triple_refuses`).

The changes are checked on copies without the module's pins, so that the refusal comes from a proof and
not from a pin, except the two kept with their pins. The unmodified copies must be accepted first. A timeout, a compiler
that does not start, a syntax error, an unrelated failure and a refusal elsewhere than the named place
never count. These are proof-dependency controls on copies of the Lean; no source, olean or git state
changes.

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
SCREEN = ROOT / 'translation/Translation/UnitLifecycleDecryptRatchetScreen.lean'
REFUSAL = ROOT / 'translation/Translation/UnitLifecycleTripleRefusalT3.lean'
COMPLETE = ROOT / 'translation/Translation/UnitLifecycleDecryptRatchetCompleteT3.lean'
COMPLETE_SCREEN = ROOT / 'translation/Translation/UnitLifecycleDecryptRatchetCompleteScreen.lean'

# The declaration that composes the loop into `decrypt_ratchet`.
COMPOSITION = 'decrypt_ratchet_refines_or_open'

PROOF = (r'unsolved goals|Application type mismatch|Type mismatch|omega could not prove|made no progress'
         r'|rcases|Dependent elimination failed|Insufficient number of fields')

# (copy, name, [(pattern, replacement), ...], a regular expression the refused output must contain,
#  where the refusal must be: declarations one of whose lines holds an error, or ('pin', name) for the
#  `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
    ('loop', 'batch-covers-arm-without-the-model-bound',
     [(r'concrete\.val = model ∨ \(len ≤ concrete\.val ∧ len ≤ model\)',
       'concrete.val = model ∨ (len ≤ concrete.val ∧ True)')], PROOF,
     ['evictHalf_congr_of_covers', 'batchCovers_double', 'shortfall_classical_covers',
      'shortfall_post_quantum_covers']),
    ('loop', 'invariant-without-the-pending-map',
     [(r'  pending : tripleReceiveRefusalOfReal pending = some modelPending\n', '  pending : True\n')],
     PROOF, ['receive_with_eviction_loop_refines']),
    ('loop', 'stop-lemma-without-the-classifier',
     [(r'    \(hFull : Model\.Lifecycle\.fullStore reason = none\) :\n', '    (hFull : True) :\n')],
     PROOF, ['receiveWithEvictionLoopResult_stop']),
    ('loop', 'first-batch-without-the-store-margin',
     [(r'\(hstore : Model\.Triple\.classicalSkippedLength modelState \+ Model\.State\.maxSkippedStore ≤',
       '(hstore : Model.Triple.classicalSkippedLength modelState ≤')], PROOF,
     ['shortfall_classical_covers']),
    ('t3', 'open-disjunct-of-every-refusal',
     [(r'  ∃ reason, output\.1 = \.Err \(\.Triple reason\) ∧ lifecycle\.full_store reason = ok none\n',
       '  ∃ reason, output.1 = .Err reason\n')], PROOF, ['tripleRefusalOpen_exactly']),
    ('t3', 'open-disjunct-with-the-full-store-refusals',
     [(r'  ∃ reason, output\.1 = \.Err \(\.Triple reason\) ∧ lifecycle\.full_store reason = ok none\n',
       '  ∃ reason, output.1 = .Err (.Triple reason)\n')], PROOF, ['tripleRefusalOpen_exactly']),
    ('t3', 'run-bounds-without-the-store-margin',
     [(r'  classicalStore : state\.classical\.skipped\.length \+ Model\.State\.maxSkippedStore ≤\n',
       '  classicalStore : state.classical.skipped.length ≤\n')], PROOF,
     ['RetryRunBounds.toRetryReceiveBounds']),
    ('t3', 'run-draw-not-tied-to-the-trace',
     [(r'  draw : ∃ draw rest, trace rng = draw :: rest\n',
       '  draw : ∃ (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),\n'
       '    draw :: rest = draw :: rest\n')], PROOF, [COMPOSITION]),
    ('t3', 'conclusion-widened-to-every-refusal',
     [(r'        TripleRefusalOpen output\) := by\n  obtain ⟨output, hcall, hstep⟩ := decrypt_ratchet_refines_or_open',
       '        (TripleRefusalOpen output ∨ ∃ e, output.1 = .Err e)) := by\n'
       '  obtain ⟨output, hcall, hstep⟩ := decrypt_ratchet_refines_or_open'),
      (r'exact ⟨output, hcall, hstep\.imp_right And\.right⟩',
       'exact ⟨output, hcall, hstep.imp_right (fun h => Or.inl h.2)⟩')], PROOF,
     ['decrypt_ratchet_refines_unless_open']),
    ('joint', 'run-bounds-with-empty-stores',
     [(r'  sparseStore : state\.postQuantum\.skipped\.length \+ Model\.SparseRatchet\.maxSkippedStore ≤\n'
       r'    UScalar\.cMax UScalarTy\.Usize\n',
       '  sparseStore : state.postQuantum.skipped.length + Model.SparseRatchet.maxSkippedStore ≤\n'
       '    UScalar.cMax UScalarTy.Usize\n'
       '  emptyStores : state.classical.skipped = [] ∧ state.postQuantum.skipped = []\n')], PROOF,
     ['evict_run_satisfiable']),
    ('t3pinned', 'open-disjunct-of-every-refusal-pinned',
     [(r'  ∃ reason, output\.1 = \.Err \(\.Triple reason\) ∧ lifecycle\.full_store reason = ok none\n',
       '  ∃ reason, output.1 = .Err reason\n')],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleDecryptRatchetT3.TripleRefusalOpen')),
    ('refusal', 'tail-out-of-order-named-as-missing-chain',
     [(r'if n\.val < st2\.nr then \.error \.outOfOrder',
       'if n.val < st2.nr then .error .noReceivingChain')], PROOF,
     ['ratchet_receive_tail_refusal_refines']),
    ('refusal', 'derivation-refusal-not-located',
     [(r'e = RatchetError\.ChainExhausted ∧ Std\.U32\.max < start_n\.val \+ count\.val',
       'e = RatchetError.ChainExhausted ∧ start_n.val + count.val ≤ start_n.val + count.val + 1')],
     PROOF, ['ratchet_skip_refusal_refines']),
    ('refusal', 'sparse-epoch-bound-at-the-ceiling',
     [(r'    \(hepoch : s\.epoch\.val \+ 1 < Std\.U64\.max\)\n',
       '    (hepoch : s.epoch.val < Std.U64.max)\n')], PROOF, ['spqr_receive_refusal_refines']),
    ('refusal', 'triple-model-reason-fixed',
     [(r'\(output\.map Tacenta\.SessionUnitTripleT3\.spqrOutputOf\) = \.error modelReason ⦄',
       '(output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) = .error (.classical .outOfOrder) ⦄')],
     PROOF, ['triple_receive_refusal_refines']),
    ('complete', 'bridge-without-the-public-mapping',
     [(r'    ∃ modelReason, tripleReceiveRefusalOfReal realReason = some modelReason ∧\n',
       '    ∃ modelReason,\n')], PROOF,
     ['concrete_receive_attempt_refusal_from_retry_bounds', 'openRefusal_closes']),
    ('completepinned', 'complete-statement-with-the-open-disjunct-pinned',
     [(r'        StepRefines trace dh oracle\.braidKem output\n'
       r'          \(Model\.Lifecycle\.decryptRatchet view oracle model \(sliceOf message\)\)\n\n',
       '        (StepRefines trace dh oracle.braidKem output\n'
       '          (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) ∨\n'
       '          TripleRefusalOpen output)\n\n')],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleDecryptRatchetCompleteT3.DecryptRatchetRefinesCompleteStatement')),
    ('completescreen', 'screen-model-reason-misnamed',
     [(r'      \.error \(\.classical \.outOfOrder\) ∧\n    Model\.Lifecycle\.fullStore',
       '      .error (.classical .noReceivingChain) ∧\n    Model.Lifecycle.fullStore')], PROOF,
     ['ref_model_triple_refuses']),
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


def split_imports(text):
    """The import lines of a module and the rest of it."""
    lines = text.split('\n')
    k = 0
    while k < len(lines) and (lines[k].startswith('import ') or lines[k] == ''):
        k += 1
    return [l for l in lines[:k] if l.startswith('import ')], '\n'.join(lines[k:])


def joint_copy(t3_text, screen_text):
    """The composition and its screen in one file: the screen's import of the composition is
    replaced by the composition's own text, so a change to a record the composition defines reaches
    the screen's witnesses."""
    t3_imports, t3_body = split_imports(t3_text)
    screen_imports, screen_body = split_imports(screen_text)
    module = 'import Translation.UnitLifecycleDecryptRatchetT3'
    if module not in screen_imports:
        raise SystemExit('the screen no longer imports the composition; the joint copy is stale')
    imports = []
    for line in t3_imports + [l for l in screen_imports if l != module]:
        if line not in imports:
            imports.append(line)
    return '\n'.join(imports) + '\n\n' + t3_body + '\n' + screen_body


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
               and not any(bad in output for bad in NOT_A_REFUSAL))
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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=900)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='decrypt-ratchet-logs-'))
    logs.mkdir(parents=True, exist_ok=True)
    loop, t3, screen = LOOP.read_text(), T3.read_text(), SCREEN.read_text()
    refusal, complete = REFUSAL.read_text(), COMPLETE.read_text()
    complete_screen = COMPLETE_SCREEN.read_text()
    sources = {
        'loop': without_pins(loop, LOOP),
        't3': without_pins(t3, T3),
        't3pinned': t3,
        'joint': joint_copy(without_pins(t3, T3), without_pins(screen, SCREEN)),
        'refusal': without_pins(refusal, REFUSAL),
        'complete': without_pins(complete, COMPLETE),
        'completepinned': complete,
        'completescreen': without_pins(complete_screen, COMPLETE_SCREEN),
    }
    results = {
        'loop_sha256': hashlib.sha256(loop.encode()).hexdigest(),
        't3_sha256': hashlib.sha256(t3.encode()).hexdigest(),
        'screen_sha256': hashlib.sha256(screen.encode()).hexdigest(),
        'refusal_sha256': hashlib.sha256(refusal.encode()).hexdigest(),
        'complete_sha256': hashlib.sha256(complete.encode()).hexdigest(),
        'complete_screen_sha256': hashlib.sha256(complete_screen.encode()).hexdigest(),
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
        for label, name, edits, marker, where in MUTANTS:
            source = sources[label]
            mutated = source
            for pattern, replacement in edits:
                found = len(re.findall(pattern, mutated))
                if found != 1:
                    raise SystemExit(f'Target changed for {name}: expected 1 occurrence of the '
                                     f'pattern in the {label} copy, found {found}')
                mutated, n = re.subn(pattern, lambda _m: replacement, mutated, count=1)
                assert n == 1
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
