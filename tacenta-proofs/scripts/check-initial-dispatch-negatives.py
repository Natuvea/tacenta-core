#!/usr/bin/env python3
"""Compile disposable proof copies; accept only the expected proof failures.

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
SOURCES = {
    'lifecycle': SOURCE,
    'classical': ROOT / 'translation/Translation/SessionUnitT3.lean',
    'sparse': ROOT / 'translation/Translation/SessionUnitSpqrT3.lean',
    'triple': ROOT / 'translation/Translation/SessionUnitTripleT3.lean',
}


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
    parser.add_argument(
        '--mutation', action='append', metavar='NAME',
        help='run only the named mutation (repeatable); default: run all',
    )
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='initial-dispatch-logs-'))
    logs.mkdir(parents=True, exist_ok=True)
    sources = {name: path.read_text() for name, path in SOURCES.items()}
    results = {
        'source_sha256': hashlib.sha256(sources['lifecycle'].encode()).hexdigest(),
        'source_sha256s': {
            name: hashlib.sha256(source.encode()).hexdigest()
            for name, source in sources.items()
        },
        'mutations': {},
    }
    mutants = [
        ('drop-retry-batch-cap',
         'def RetryBatchAgrees (concrete : Std.Usize) (model : Nat) : Prop :=\n'
         '  concrete.val = min Usize.max model',
         'def RetryBatchAgrees (concrete : Std.Usize) (model : Nat) : Prop :=\n'
         '  concrete.val = model',
         'Usize'),
        ('replace-retry-saturating-double-with-ordinary',
         '  have hGenerated :\n'
         '      batchNext.val = min Usize.max (batch.val + batch.val) := by',
         '  have hGenerated :\n'
         '      batchNext.val = batch.val + batch.val := by',
         'usize_saturating_add_val'),
        ('swap-classical-shortfall-model-half',
         '        (Model.Lifecycle.receiveShortfall .classical modelState modelComposite) := by',
         '        (Model.Lifecycle.receiveShortfall .postQuantum modelState modelComposite) := by',
         'postQuantumSkippedLength'),
        ('swap-classical-shortfall-bound-half',
         '    (hwidth : Model.Triple.classicalSkippedLength modelState +\n'
         '      (modelComposite.n.toNat - Model.Triple.receiveCount modelState) ≤ Usize.max) :',
         '    (hwidth : Model.Triple.postQuantumSkippedLength modelState +\n'
         '      (modelComposite.n.toNat - Model.Triple.receiveCount modelState) ≤ Usize.max) :',
         'hwidth'),
        ('shift-post-quantum-shortfall-receive-count',
         '          have hroom := hwidth chain.n.val hmodelCount',
         '          have hroom := hwidth (chain.n.val + 1) hmodelCount',
         'hmodelCount'),
        ('replace-classical-first-minimum-with-nonstrict',
         'concrete_classical_evict_one_step_model hvr hrel oldest hwidth hr hmin hfirst',
         'concrete_classical_evict_one_step_model hvr hrel oldest hwidth hr hmin hmin',
         'hmin'),
        ('weaken-classical-selector-width-to-usize-max',
         '(hwidth : s.skipped.val.length ≤ UScalar.cMax UScalarTy.Usize)\n'
         '    (hlen : s.skipped.val.length ≠ 0) :',
         '(hwidth : s.skipped.val.length ≤ Usize.max)\n'
         '    (hlen : s.skipped.val.length ≠ 0) :',
         'hwidth'),
        ('bypass-classical-retry-batch-cap',
         '      (mstate, evicted.val) := hcap.symm.trans hpair',
         '      (mstate, evicted.val) := hpair',
         'hpair'),
        ('invert-full-store-generated-comparison',
         '      lifecycle.FullStore.Insts.CoreCmpPartialEqFullStore left right = ok true) :\n'
         '    fullStoreOfReal left ≠ fullStoreOfReal right := by',
         '      lifecycle.FullStore.Insts.CoreCmpPartialEqFullStore left right = ok false) :\n'
         '    fullStoreOfReal left ≠ fullStoreOfReal right := by',
         'rfl'),
        ('replace-full-store-bounds-classical-room',
         '    hheader dhOutRecv dhOutSend newDhsPub output bounds.classicalMatch\n'
         '    bounds.classicalStoreRoom bounds.classicalEvents bounds.sparseEpoch',
         '    hheader dhOutRecv dhOutSend newDhsPub output bounds.classicalMatch\n'
         '    bounds.sparseStoreRoom bounds.classicalEvents bounds.sparseEpoch',
         'bounds.sparseStoreRoom'),
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
        ('swap-decrypt-refusal-cross-family-arm',
         'cross.refusalNotModelSuccess reason next rngNext modelNext',
         'cross.successNotModelRefusal reason next rngNext modelNext',
         'reason'),
        ('swap-decrypt-success-cross-family-arm',
         'cross.successNotModelRefusal plaintext next rngNext modelNext',
         'cross.refusalNotModelSuccess plaintext next rngNext modelNext',
         'plaintext'),
        ('replace-decrypt-first-dh-cross-family-leaf',
         'evidence.hdecodeReal evidence.hdecodeModel evidence.hcomposite hfirst',
         'evidence.hdecodeReal evidence.hdecodeModel evidence.hcomposite hdecode',
         'hdecode'),
        ('replace-decrypt-second-dh-cross-family-draw',
         'draw dhOutRecv hfirst hdraw hsecond',
         'draw dhOutRecv hfirst hfirst hsecond',
         'hfirst'),
        ('replace-decrypt-ceiling-random-success',
         'trace oracle rng htrace\n    htraceHead hdraw',
         'trace oracle rng htrace\n    htrace hdraw',
         'htrace'),
        ('replace-full-store-receive-call-evidence',
         '    simpa [lifecycle.receive_attempt] using hcall',
         '    simpa [lifecycle.receive_attempt] using hfull',
         'hfull'),
        ('replace-full-store-model-refusal-map',
         'hpost realReason modelReason rfl hmap',
         'hpost realReason modelReason rfl hreason',
         'hreason'),
        ('fix-full-store-model-half-classical',
         'Model.Lifecycle.fullStore modelReason = some (fullStoreOfReal half) := by',
         'Model.Lifecycle.fullStore modelReason = some .classical := by',
         'hmodelFull'),
        ('change-classical-full-store-refusal-to-too-many',
         '.error .skippedStoreFull ⦄ := by',
         '.error .tooManySkipped ⦄ := by',
         'tooManySkipped'),
        ('change-sparse-full-store-refusal-to-too-many',
         '.error .skippedStoreFull ⦄ := by',
         '.error .tooManySkipped ⦄ := by',
         'tooManySkipped'),
        ('swap-triple-classical-full-store-family',
         '| .Classical .SkippedStoreFull => some (.classical .skippedStoreFull)',
         '| .Classical .SkippedStoreFull => some (.postQuantum .skippedStoreFull)',
         'postQuantum'),
        ('swap-lifecycle-full-store-halves',
         '  | .Classical => .classical\n  | .PostQuantum => .postQuantum',
         '  | .Classical => .postQuantum\n  | .PostQuantum => .classical',
         'SkippedStoreFull'),
        ('replace-decrypt-derived-braid-message',
         '    braid.1 provider.hkem braid.2 (provider.hprivate successPrefix)',
         '    provider.hrel provider.hkem braid.2 (provider.hprivate successPrefix)',
         'provider.hrel'),
        ('replace-decrypt-derived-braid-state',
         '    braid.1 provider.hkem braid.2 (provider.hprivate successPrefix)',
         '    braid.1 provider.hkem provider.hrel (provider.hprivate successPrefix)',
         'provider.hrel'),
        ('restore-arbitrary-ceiling',
         '      oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →\n'
         '      ∃ draw rest, trace rng = draw :: rest',
         '      oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →\n'
         '      Model.Lifecycle.random32 oracle = none → False',
         'evidence.randomDraw input.decoded hdecode'),
        ('restore-preassembled-positive-receive-provider',
         '  receive : ∀ successPrefix : InitialRatchetSuccessPrefix rc crc real message\n'
         '      rng rngNext plaintext next,\n'
         '    Nonempty (InitialRatchetExactSuccessReceiveEvidence successPrefix modelPrefix)',
         '  receive : Nonempty (Sigma fun successPrefix : InitialRatchetSuccessPrefix rc crc real message\n'
         '      rng rngNext plaintext next =>\n'
         '    InitialRatchetExactSuccessReceiveEvidence successPrefix modelPrefix)',
         'provider.receive'),
        ('replace-positive-receive-real-key',
         '    (successPrefix.realTripleCandidate, successPrefix.realMk)\n'
         '    (modelTripleCandidate, modelMk)',
         '    (successPrefix.realTripleCandidate, successPrefix.recvSecret)\n'
         '    (modelTripleCandidate, modelMk)',
         'successPrefix.realMk'),
        ('replace-direct-attempt-with-outer-result',
         '  have hrealDirect := initial_ratchet_success_prefix_direct_receive successPrefix hAttempt',
         '  have hrealDirect := initial_ratchet_success_prefix_direct_receive successPrefix successPrefix.htriple',
         'successPrefix.htriple'),
        ('flatten-encrypt-generated-refusal-family',
         '  | .tripleRefusal _ _ _ _ =>\n'
         '      EncryptTripleRouteEvidence rc crc trace dh kem K view oracle real model plaintext rng',
         '  | .tripleRefusal _ _ _ _ =>\n'
         '      EncryptRouteEvidence rc crc trace dh K view oracle real model plaintext rng',
         'tripleEvidence'),
        ('flatten-encrypt-generated-success-family',
         '  | .tripleSuccess _ _ _ _ =>\n'
         '      EncryptTripleRouteEvidence rc crc trace dh kem K view oracle real model plaintext rng',
         '  | .tripleSuccess _ _ _ _ =>\n'
         '      EncryptRouteEvidence rc crc trace dh K view oracle real model plaintext rng',
         'tripleEvidence'),
        ('restore-preassembled-triple-success-provider',
         '    GeneratedTripleSuccessConditions model realEpoch sparseOutput',
         '    EncryptEvidenceForGeneratedPrefix (trace := trace) (dh := dh) (kem := kem)\n'
         '      (K := K) (view := view) (oracle := oracle) (model := model)\n'
         '      (realMessage := realMessage) (rngNext := rngNext)\n'
         '      (.tripleSuccess hnext hsparse hsendCandidate houtput)',
         'conditions'),
        ('invert-encrypt-triple-success-sparse-bridge',
         'braidEvidence.epoch hmodelOutput\n'
         '        htripleModel htripleNext hheader hmk\' hpending',
         'braidEvidence.epoch hmodelOutput.symm\n'
         '        htripleModel htripleNext hheader hmk\' hpending',
         'hmodelOutput'),
        ('replace-encrypt-triple-success-exact-result',
         "        htripleModel htripleNext hheader hmk' hpending",
         "        htripleAtRealEpoch htripleNext hheader hmk' hpending",
         'htripleAtRealEpoch'),
        ('replace-encrypt-associated-data-headroom',
         'Tacenta.UnitLifecycleT1.EncryptHeadroom.associatedData headroom',
         'Tacenta.UnitLifecycleT1.EncryptHeadroom.ratchetMessage headroom',
         'hrealAssociatedRoom'),
        ('replace-encrypt-aead-length-contract',
         'oracle_aead_seal_length_bound oracleOf aead',
         'oracle_aead_seal_length_bound oracleOf headroom',
         'headroom'),
        ('replace-encrypt-initial-headroom',
         'Tacenta.UnitLifecycleT1.EncryptHeadroom.initial headroom',
         'Tacenta.UnitLifecycleT1.EncryptHeadroom.ratchetMessage headroom',
         'hinitialHeadroom'),
        ('invert-encrypt-generated-braid-ready',
         'ready : Model.Lifecycle.agreementFailed model = false',
         'ready : Model.Lifecycle.agreementFailed model = true',
         'hready'),
        ('invert-encrypt-generated-braid-real-send',
         'realSend : tacenta_braid.Braid.send rc crc real.braid rng =\n'
         '    ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext)',
         'realSend : ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext) =\n'
         '    tacenta_braid.Braid.send rc crc real.braid rng',
         'hsend'),
        ('invert-encrypt-generated-braid-not-failed',
         'notFailed : Model.Lifecycle.braidFailed modelBraidNext = false',
         'notFailed : Model.Lifecycle.braidFailed modelBraidNext = true',
         'braidFailed'),
        ('shift-encrypt-generated-braid-epoch',
         'epoch : realEpoch.val = modelEpoch',
         'epoch : realEpoch.val + 1 = modelEpoch',
         'braidEvidence.epoch'),
        ('replace-encrypt-generated-braid-output',
         'output : Tacenta.SessionUnitBraidT3.OptionOutputRefines realOutput modelOutput',
         'output : realOutput = none ∧ modelOutput = none',
         'braidEvidence.output'),
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
    if args.mutation:
        requested = set(args.mutation)
        known = {name for name, _, _, _ in mutants}
        unknown = requested - known
        if unknown:
            raise SystemExit('Unknown mutation(s): ' + ', '.join(sorted(unknown)))
        mutants = [mutant for mutant in mutants if mutant[0] in requested]
    results['requested_mutations'] = args.mutation or 'all'
    mutation_sources = {
        'change-classical-full-store-refusal-to-too-many': 'classical',
        'change-sparse-full-store-refusal-to-too-many': 'sparse',
        'swap-triple-classical-full-store-family': 'triple',
    }
    with tempfile.TemporaryDirectory(prefix='initial-dispatch-controls-') as tmp:
        tmp = Path(tmp)
        source_names = list(dict.fromkeys(
            mutation_sources.get(name, 'lifecycle') for name, _, _, _ in mutants
        ))
        results['baseline_exits'] = {}
        for source_name in source_names:
            baseline = tmp / f'Baseline-{source_name}.lean'
            baseline.write_text(sources[source_name])
            log = logs / f'baseline-{source_name}.log'
            status, output = run_lean(baseline, log, args.timeout)
            if status or 'declaration uses `sorry`' in output:
                raise SystemExit(f'BASELINE FAILED; no mutation evidence: {log}')
            results['baseline_exits'][source_name] = status
            print(f'PASS: unmodified {source_name} source elaborates', flush=True)
        results['baseline_exit'] = 0
        for name, before, after, premise in mutants:
            source_name = mutation_sources.get(name, 'lifecycle')
            source = sources[source_name]
            # The guard premise occurs once: the mutation must target the
            # concrete terminal-discharge theorem, not a duplicated signature.
            # For the terminal guard, mutate its concrete-discharge theorem only.
            mutated = tmp / f'{name}.lean'
            if name == 'restore-arbitrary-ceiling':
                # The live per-run record, not the superseded all-states one.
                start = source.find('structure InitialRatchetConcreteBranchEvidenceRun')
                target = source.find(before, start)
                if start < 0 or target < 0:
                    raise SystemExit(f'Target changed for {name}: run draw field is missing')
                mutated.write_text(source[:target] + source[target:].replace(before, after, 1))
            elif name == 'bypass-ephemeral':
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
            elif (name.startswith('invert-encrypt-') and
                  name != 'invert-encrypt-triple-success-sparse-bridge'):
                markers = {
                    'invert-encrypt-generated-braid-ready':
                        'structure GeneratedBraidSuccessEvidence',
                    'invert-encrypt-generated-braid-real-send':
                        'structure GeneratedBraidSuccessEvidence',
                    'invert-encrypt-generated-braid-not-failed':
                        'structure GeneratedBraidSuccessEvidence',
                    'shift-encrypt-generated-braid-epoch':
                        'structure GeneratedBraidSuccessEvidence',
                    'replace-encrypt-generated-braid-output':
                        'structure GeneratedBraidSuccessEvidence',
                    'invert-encrypt-braid-no-draw-trace': '  noDrawTrace :',
                    'invert-encrypt-braid-draw-trace': '  drawTrace :',
                    'invert-encrypt-braid-draw-post': '  drawPost :',
                }
                # The three trace clauses are those of the live, counted agreement; the
                # superseded one-draw form earlier in the file is taken by no proof.
                base = (source.find('structure BraidSendTraceAgreementCounted')
                        if name.startswith('invert-encrypt-braid-') else 0)
                start = source.find(markers[name], base) if base >= 0 else -1
                target = source.find(before, start)
                if start < 0 or target < 0:
                    raise SystemExit(f'Target changed for {name}: named provider guard is missing')
                mutated.write_text(source[:target] + source[target:].replace(before, after, 1))
            elif name in {
                'restore-preassembled-triple-success-provider',
                'replace-encrypt-triple-success-exact-result',
            }:
                marker = {
                    'restore-preassembled-triple-success-provider':
                        'structure EncryptNonterminalRouteProviders',
                    'replace-encrypt-triple-success-exact-result':
                        'theorem encrypt_triple_success_evidence_of_generated',
                }[name]
                start = source.find(marker)
                target = source.find(before, start)
                if start < 0 or target < 0:
                    raise SystemExit(f'Target changed for {name}: generated success bridge is missing')
                mutated.write_text(source[:target] + source[target:].replace(before, after, 1))
            elif name == 'invert-encrypt-triple-success-sparse-bridge':
                marker = 'theorem encrypt_triple_success_evidence_of_generated'
                start = source.find(marker)
                target = source.find(before, start)
                if start < 0 or target < 0:
                    raise SystemExit(f'Target changed for {name}: sparse bridge use is missing')
                mutated.write_text(source[:target] + source[target:].replace(before, after, 1))
            elif name in {
                'restore-preassembled-positive-receive-provider',
                'replace-positive-receive-real-key',
                'replace-direct-attempt-with-outer-result',
            }:
                marker = {
                    'restore-preassembled-positive-receive-provider':
                        'structure InitialRatchetExactSuccessReceiveProvider',
                    'replace-positive-receive-real-key':
                        'structure InitialRatchetExactSuccessReceiveEvidence',
                    'replace-direct-attempt-with-outer-result':
                        'theorem initial_ratchet_exact_success_receive_of_direct_contracts',
                }[name]
                start = source.find(marker)
                target = source.find(before, start)
                if start < 0 or target < 0:
                    raise SystemExit(
                        f'Target changed for {name}: exact receive dependency is missing')
                mutated.write_text(source[:target] + source[target:].replace(before, after, 1))
            elif name in {
                'replace-full-store-receive-call-evidence',
                'replace-full-store-model-refusal-map',
                'fix-full-store-model-half-classical',
            }:
                marker = 'theorem concrete_receive_attempt_store_full_from_contracts'
                start = source.find(marker)
                target = source.find(before, start)
                if start < 0 or target < 0:
                    raise SystemExit(f'Target changed for {name}: full-store adapter is missing')
                mutated.write_text(source[:target] + source[target:].replace(before, after, 1))
            elif name in {
                'invert-full-store-generated-comparison',
                'replace-full-store-bounds-classical-room',
            }:
                markers = {
                    'invert-full-store-generated-comparison':
                        'theorem fullStoreOfReal_ne_of_generated_ne',
                    'replace-full-store-bounds-classical-room':
                        'theorem concrete_receive_attempt_store_full_from_retry_bounds',
                }
                start = source.find(markers[name])
                target = source.find(before, start)
                if start < 0 or target < 0:
                    raise SystemExit(
                        f'Target changed for {name}: retry prerequisite is missing')
                mutated.write_text(source[:target] + source[target:].replace(before, after, 1))
            elif name in {
                'change-classical-full-store-refusal-to-too-many',
                'change-sparse-full-store-refusal-to-too-many',
                'swap-triple-classical-full-store-family',
                'swap-lifecycle-full-store-halves',
            }:
                markers = {
                    'change-classical-full-store-refusal-to-too-many':
                        'theorem receive_store_full_refines',
                    'change-sparse-full-store-refusal-to-too-many':
                        'theorem receive_store_full_refines',
                    'swap-triple-classical-full-store-family':
                        'def receiveStoreFullRefusalOfReal',
                    'swap-lifecycle-full-store-halves': 'def fullStoreOfReal',
                }
                start = source.find(markers[name])
                target = source.find(before, start)
                if start < 0 or target < 0:
                    raise SystemExit(f'Target changed for {name}: semantic mapping is missing')
                mutated.write_text(source[:target] + source[target:].replace(before, after, 1))
            elif name in {
                'replace-classical-first-minimum-with-nonstrict',
                'weaken-classical-selector-width-to-usize-max',
            }:
                marker = 'theorem concrete_classical_evict_body_refines'
                start = source.find(marker)
                target = source.find(before, start)
                if start < 0 or target < 0:
                    raise SystemExit(
                        f'Target changed for {name}: concrete eviction body is missing')
                mutated.write_text(source[:target] + source[target:].replace(before, after, 1))
            else:
                if source.count(before) != 1:
                    raise SystemExit(f'Target changed for {name}: expected 1 occurrence')
                mutated.write_text(source.replace(before, after, 1))
            log = logs / f'{name}.log'
            status, output = run_lean(mutated, log, args.timeout)
            if name.startswith('flatten-encrypt-generated-'):
                mismatch = re.search(
                    r'error: Application type mismatch: The argument\s+'
                    + re.escape(premise) + r'.+?has type\s+'
                    r'.+?EncryptEvidenceForGeneratedPrefix.+?but is expected to have type\s+'
                    r'.+?EncryptTripleRouteEvidence', output, re.S)
            elif name == 'invert-encrypt-generated-braid-ready':
                mismatch = re.search(
                    r'error: Type mismatch\s+hready\s+has type\s+'
                    r'Model\.Lifecycle\.agreementFailed model = false\s+'
                    r'but is expected to have type\s+'
                    r'Model\.Lifecycle\.agreementFailed model = true', output, re.S)
            elif name == 'invert-encrypt-generated-braid-real-send':
                mismatch = re.search(
                    r'error: Type mismatch\s+hsend\s+has type\s+'
                    r'tacenta_braid\.Braid\.send.+?= ok.+?'
                    r'but is expected to have type\s+ok.+?= tacenta_braid\.Braid\.send',
                    output, re.S)
            elif name == 'invert-encrypt-generated-braid-not-failed':
                mismatch = re.search(
                    r'error: Type mismatch.+?has type\s+'
                    r'Model\.Lifecycle\.braidFailed modelBraidNext = false.+?'
                    r'but is expected to have type\s+'
                    r'Model\.Lifecycle\.braidFailed modelBraidNext = true', output, re.S)
            elif name == 'shift-encrypt-generated-braid-epoch':
                mismatch = re.search(
                    r'error: Type mismatch\s+braidEvidence\.epoch\s+has type\s+'
                    r'.+?\+ 1 = braidEvidence\.modelEpoch\s+'
                    r'but is expected to have type\s+'
                    r'.+?= braidEvidence\.modelEpoch', output, re.S)
            elif name == 'replace-encrypt-generated-braid-output':
                mismatch = re.search(
                    r'error: Type mismatch\s+braidEvidence\.output\s+has type\s+'
                    r'realOutput = none ∧ braidEvidence\.modelOutput = none\s+'
                    r'but is expected to have type\s+'
                    r'SessionUnitBraidT3\.OptionOutputRefines realOutput braidEvidence\.modelOutput',
                    output, re.S)
            elif name == 'restore-preassembled-triple-success-provider':
                mismatch = re.search(
                    r'error: Application type mismatch: The argument\s+conditions.+?has type\s+'
                    r'.+?EncryptEvidenceForGeneratedPrefix.+?but is expected to have type\s+'
                    r'.+?GeneratedTripleSuccessConditions', output, re.S)
            elif name == 'invert-encrypt-triple-success-sparse-bridge':
                mismatch = re.search(
                    r'error: Application type mismatch: The argument\s+Eq\.symm hmodelOutput.+?has type\s+'
                    r'.+?but is expected to have type', output, re.S)
            elif name == 'replace-encrypt-triple-success-exact-result':
                mismatch = re.search(
                    r'error: Application type mismatch: The argument\s+'
                    r'htripleAtRealEpoch.+?has type\s+'
                    r'.+?but is expected to have type', output, re.S)
            elif name == 'replace-decrypt-second-dh-cross-family-draw':
                mismatch = re.search(
                    r'error: Application type mismatch: The last\s+hfirst\s+'
                    r'argument has type\s+.+?but is expected to have type',
                    output, re.S)
            elif name == 'replace-decrypt-ceiling-random-success':
                mismatch = re.search(
                    r'error: Application type mismatch: The last\s+htrace\s+'
                    r'argument has type\s+.+?but is expected to have type',
                    output, re.S)
            elif name == 'restore-preassembled-positive-receive-provider':
                mismatch = re.search(
                    r'error: Function expected at\s+provider\.receive.+?'
                    r'but this term has type\s+.+?Nonempty', output, re.S)
            elif name == 'replace-positive-receive-real-key':
                mismatch = re.search(
                    r'error: Type mismatch.+?'
                    r'initial_ratchet_success_branch_of_aligned_case.+?'
                    r'successPrefix\.realMk.+?but is expected to have type.+?'
                    r'successPrefix\.recvSecret', output, re.S)
            elif name == 'replace-encrypt-associated-data-headroom':
                mismatch = re.search(
                    r'error: Application type mismatch: The argument\s+'
                    r'hrealAssociatedRoom.+?has type\s+'
                    r'.+?but is expected to have type', output, re.S)
            elif name == 'replace-encrypt-initial-headroom':
                mismatch = re.search(
                    r'error: Tactic `rewrite` failed: Did not find an occurrence.+?'
                    r'initialHeadroom', output, re.S)
            elif name == 'drop-retry-batch-cap':
                mismatch = re.search(
                    r'error:.+?Usize\.max', output, re.S)
            elif name == 'replace-retry-saturating-double-with-ordinary':
                mismatch = re.search(
                    r'error: Type mismatch.+?usize_saturating_add_val', output, re.S)
            elif name == 'swap-classical-shortfall-model-half':
                mismatch = re.search(
                    r'error: unsolved goals.+?postQuantumSkippedLength', output, re.S)
            elif name == 'swap-classical-shortfall-bound-half':
                mismatch = re.search(
                    r'error: Tactic `rewrite` failed:.+?postQuantumSkippedLength',
                    output, re.S)
            elif name == 'invert-full-store-generated-comparison':
                mismatch = re.search(
                    r'error: Application type mismatch: The argument\s+rfl\s+has type\s+'
                    r'.+?but is expected to have type\s+false = true', output, re.S)
            elif name == 'replace-full-store-receive-call-evidence':
                mismatch = re.search(
                    r'error: Type mismatch: After simplification, term\s+hfull\s+'
                    r'has type\s+lifecycle\.full_store realReason = ok \(some half\)\s+'
                    r'but is expected to have type\s+'
                    r's\.receive header dh_out_recv dh_out_send new_dhs_pub output = '
                    r'ok \(core\.result\.Result\.Err realReason\)', output, re.S)
            elif name == 'replace-full-store-model-refusal-map':
                mismatch = re.search(
                    r'error: Application type mismatch: The argument\s+hreason\s+'
                    r'has type\s+tripleReceiveRefusalOfReal realReason = some modelReason\s+'
                    r'but is expected to have type\s+'
                    r'SessionUnitTripleT3\.receiveStoreFullRefusalOfReal realReason = '
                    r'some modelReason', output, re.S)
            elif name == 'fix-full-store-model-half-classical':
                mismatch = re.search(
                    r'error: Application type mismatch: The argument\s+hmodelFull\s+'
                    r'has type\s+Model\.Lifecycle\.fullStore modelReason = '
                    r'some \(fullStoreOfReal half\)\s+'
                    r'but is expected to have type\s+Model\.Lifecycle\.fullStore '
                    r'modelReason = some Model\.Lifecycle\.FullStore\.classical', output, re.S)
            elif name == 'change-classical-full-store-refusal-to-too-many':
                mismatch = re.search(
                    r'error: unsolved goals.+?'
                    r'core\.result\.Result\.Err RatchetError\.SkippedStoreFull.+?'
                    r'Except\.error Model\.Ratchet\.ReceiveRefusal\.skippedStoreFull.+?'
                    r'Except\.error Model\.Ratchet\.ReceiveRefusal\.tooManySkipped',
                    output, re.S)
            elif name == 'change-sparse-full-store-refusal-to-too-many':
                mismatch = re.search(
                    r'error: Type mismatch\s+hresult\.right\s+has type.+?'
                    r'Err SpqrError\.SkippedStoreFull.+?'
                    r'Except\.error Model\.SparseRatchet\.ReceiveRefusal\.skippedStoreFull.+?'
                    r'but is expected to have type.+?'
                    r'Except\.error Model\.SparseRatchet\.ReceiveRefusal\.tooManySkipped',
                    output, re.S)
            elif name == 'swap-triple-classical-full-store-family':
                mismatch = re.search(
                    r'error: Type mismatch.+?'
                    r'Except\.error \(Model\.Triple\.ReceiveRefusal\.classical '
                    r'Model\.Ratchet\.ReceiveRefusal\.skippedStoreFull\).+?'
                    r'but is expected to have type.+?'
                    r'Except\.error \(Model\.Triple\.ReceiveRefusal\.postQuantum '
                    r'Model\.SparseRatchet\.ReceiveRefusal\.skippedStoreFull\)',
                    output, re.S)
            elif name == 'swap-lifecycle-full-store-halves':
                mismatch = re.search(
                    r'error: unsolved goals\s+case Classical\.SkippedStoreFull\.Classical.+?'
                    r'⊢ False.+?error: unsolved goals\s+'
                    r'case PostQuantum\.SkippedStoreFull\.PostQuantum.+?⊢ False',
                    output, re.S)
            elif name == 'replace-classical-first-minimum-with-nonstrict':
                mismatch = re.search(
                    r'error: Application type mismatch: The last\s+hmin\s+'
                    r'argument has type\s+.+?but is expected to have type', output, re.S)
            elif name == 'bypass-classical-retry-batch-cap':
                mismatch = re.search(
                    r'error: Type mismatch\s+hpair\s+has type\s+.+?'
                    r'but is expected to have type', output, re.S)
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
