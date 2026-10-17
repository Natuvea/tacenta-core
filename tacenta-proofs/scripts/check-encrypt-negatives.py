#!/usr/bin/env python3
"""Hold the established-encrypt theorems against a planted fault.

`Translation/UnitLifecycleEstablishedEncrypt.lean` composes the public `Session::encrypt` with every
successful `establish_initiator_for` output: the headroom record, the Triple condition records, the counted
draw record from the key-generation law, the model's two-outcome step, the session a successful send
leaves (its counter ceilings, its relation and `Session::invariant`), and one interpretation of every law
the premise lists rest on.  A proof that Lean accepts after the fact it rests on is removed would hold
nothing, so this script makes one change to a copy of the module and requires Lean to refuse it, at a named
place, for the reason named:

  * the headroom lemma without `KemCiphertextLenBound` (refused in `encryptHeadroom_parts`: the
    initial-message field's arithmetic has no bound on the ciphertext);
  * the headroom lemma at a plaintext bound one byte short, `+ 65769` (refused in `encryptHeadroom_parts`,
    the same field);
  * the Triple store facts restated at a model state whose sparse epoch is `u64::MAX - 1` (refused in
    `tripleStoreFacts_parts`, the epoch bound);
  * the counted draw record restated with one draw consumed (refused in
    `braidSendTraceCounted_of_keysUnsampled`: one draw is not the two the model counts);
  * `KeyGenSeededFor` weakened to some randomness, the `KemAgreesFor` form, with the proof adapted to use
    whatever randomness it gives (refused in `braidSendTraceCounted_of_keysUnsampled`: that randomness is
    not shown to be the draws' value);
  * the outcome theorem without the key-generation refusal arm, the proof adapted to rule it out (refused
    in `established_encrypt_outcomes`: the refusal is not ruled out);
  * the model Triple's first send claimed to refuse (refused in `established_triple_send_ok`);
  * the sparse message number of the first header claimed to be 0 (refused in
    `established_triple_send_ok`);
  * the wire message claimed to be the bare ratchet frame, the pending initial message ignored (refused in
    `established_encrypt_model_cases`);
  * the successor's chain counters claimed to stay at 0, the send not counted (refused in
    `established_triple_next_counters`);
  * `sentTriple` with the classical message counter at 0 (refused in `triple_eq_sent`: the relation fixes
    it at 1);
  * the encoder fact restated for the encoder before its `next_chunk` (refused in `encoder_of_refines`);
  * the successor invariant without `ValidateEkAgrees`, key-pair validity left to unfolding (refused in
    `established_encrypt_successor_admissible`, the `validate_ek` goal left unsolved);
  * the successor invariant without the size law `KeyGenSizesOf` (refused in
    `established_encrypt_successor_admissible`: the header-and-MAC message is not shown to be 96 bytes);
  * the joint model with key generation that reads nothing from the source (refused in `genFill_answers`:
    the source left is not the one the law names);
  * `KeyGenAnswersShape` with the refusing arm dropped, with the module's pins kept (refused at the pin of
    `KeyGenAnswersShape`).

The changes are checked on a copy without the module's pins, so that the refusal comes from a proof and not
from a pin, except the one kept with its pins.  The unmodified copies must be accepted first.  A timeout, a
compiler that does not start, a syntax error, an unrelated failure, a refusal elsewhere than the named
place and a refusal at the named place whose message does not match the control's reason never count.
These are proof-dependency controls on copies of the Lean; no source, olean or git state changes.

Dependencies must be built (`lake build Translation.UnitLifecycleEstablishedEncrypt`).
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
ENCRYPT = ROOT / 'translation/Translation/UnitLifecycleEstablishedEncrypt.lean'

PROOF = (r'unsolved goals|Application type mismatch|Type mismatch|type mismatch|omega could not prove'
         r'|made no progress|rcases|Insufficient number of fields|failed to prove|rewrite. failed'
         r'|The rfl tactic failed|rfl. failed|scalar_tac failed|simp failed|Tactic .* failed')

UNSOLVED = r'unsolved goals'

# (copy, name, [(pattern, replacement), ...], a regular expression the refused output must contain,
#  where the refusal must be: declarations one of whose lines holds an error, or ('pin', name) for the
#  `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
    ('encrypt', 'headroom-without-the-ciphertext-bound',
     [(re.escape('  have hkc := kemCiphertext_length_parts hct hbound p\n'), '  have hkc : True := trivial\n')],
     r'omega could not prove the goal(?:.*\n)*?.*p\.kemCiphertext', ['encryptHeadroom_parts']),
    ('encrypt', 'headroom-one-byte-short',
     [(re.escape('    (hroom : plaintext.val.length + 65770 ≤ Usize.max) :\n'
                 '    Tacenta.UnitLifecycleT1.EncryptHeadroom p.session plaintext := by\n'),
       '    (hroom : plaintext.val.length + 65769 ≤ Usize.max) :\n'
       '    Tacenta.UnitLifecycleT1.EncryptHeadroom p.session plaintext := by\n'),
      (re.escape('  exact encryptHeadroom_parts hdh hct hbound p plaintext hroom\n'),
       '  exact encryptHeadroom_parts hdh hct hbound p plaintext (by omega)\n')],
     r'omega could not prove the goal(?:.*\n)*?.*a - b ≥ 65769', ['encryptHeadroom_parts']),
    ('encrypt', 'triple-store-facts-at-the-last-sparse-epoch',
     [(re.escape('    (establishedModelOf dh p.session).triple.postQuantum.epoch + 1 < Std.U64.max ∧\n'
                 '    (∀ q ∈ (establishedModelOf dh p.session).triple.postQuantum.chains,\n'
                 '      ∀ ch : Model.SparseRatchet.Chain,'),
       '    (Std.U64.max - 1) + 1 < Std.U64.max ∧\n'
       '    (∀ q ∈ (establishedModelOf dh p.session).triple.postQuantum.chains,\n'
       '      ∀ ch : Model.SparseRatchet.Chain,')],
     r'expected type `False`|⊢ False', ['tripleStoreFacts_parts']),
    ('encrypt', 'draw-record-with-one-draw-consumed',
     [(re.escape("    refine ⟨[d1, d2], rest, ?_, by simpa using htr, by rw [hnext]; exact htr'⟩\n"),
       "    refine ⟨[d1], d2 :: rest, ?_, by simpa using htr, by rw [hnext]; exact htr'⟩\n")],
     r'(?:The rfl tactic failed|Type mismatch)(?:.*\n)*?.*(?:braidSendDrawCount|d2 :: rest)',
     ['braidSendTraceCounted_of_keysUnsampled']),
    ('encrypt', 'key-generation-law-at-some-randomness',
     [(re.escape("    KeyGenAnswersShape I K rc crc rng (Model.Lifecycle.braidRandomness (d1 ++ d2)) rng'\n"),
       "    ∃ rand, KeyGenAnswersShape I K rc crc rng rand rng'\n"),
      (re.escape("    KeyGenAnswers K rc crc rng (Model.Lifecycle.braidRandomness (d1 ++ d2)) rng'\n"),
       "    ∃ rand, KeyGenAnswers K rc crc rng rand rng'\n"),
      (re.escape("    obtain ⟨rng', htr', hans⟩ := hgen rng d1 d2 rest htr\n"),
       "    obtain ⟨rng', htr', rand, hans⟩ := hgen rng d1 d2 rest htr\n"),
      (re.escape("    obtain ⟨rng', -, hans⟩ := hgen rng d1 d2 rest (by simpa using htr)\n"),
       "    obtain ⟨rng', -, rand, hans⟩ := hgen rng d1 d2 rest (by simpa using htr)\n"),
      (re.escape("        (Model.Lifecycle.braidRandomness (d1 ++ d2)) rng' hans)\n"
                 "    have heq : result = ((m, ep, o, b), rngNext)"),
       "        rand rng' hans)\n    have heq : result = ((m, ep, o, b), rngNext)"),
      (re.escape('    refine ⟨Model.Lifecycle.braidRandomness (d1 ++ d2), by simp, ?_⟩\n'),
       '    refine ⟨rand, by simp, ?_⟩\n')],
     UNSOLVED + r'(?:.*\n)*?⊢ rand = Model\.Lifecycle\.braidRandomness \(d1 \+\+ d2\)',
     ['braidSendTraceCounted_of_keysUnsampled']),
    ('encrypt', 'outcomes-without-the-key-generation-refusal',
     [(re.escape('      ((oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = none ∧\n'
                 '          output.1 = core.result.Result.Err lifecycle.Error.AgreementFailed ∧\n'
                 '          output.2.1 = { s with braid := ⟨tacenta_braid.State.Failed⟩ }) ∨\n'
                 '        (∃ dk ekSeed ekVector,\n'
                 '          oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) =\n'
                 '            some (dk, ekSeed, ekVector) ∧\n'
                 '          ∃ bytes, output.1 = core.result.Result.Ok bytes ∧\n'
                 '          output.2.1 = { s with triple := output.2.1.triple, braid := output.2.1.braid } ∧\n'
                 '          (∃ auth kp encoder'),
       '      ((∃ dk ekSeed ekVector,\n'
       '          oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) =\n'
       '            some (dk, ekSeed, ekVector) ∧\n'
       '          ∃ bytes, output.1 = core.result.Result.Ok bytes ∧\n'
       '          output.2.1 = { s with triple := output.2.1.triple, braid := output.2.1.braid } ∧\n'
       '          (∃ auth kp encoder'),
      (re.escape('        exact Or.inl ⟨hkg, rfl, rfl⟩\n'), '        exfalso\n        simp_all\n'),
      (re.escape('      refine Or.inr ⟨dk, ekSeed, ekVector, hkg, bytes, rfl,\n'),
       '      refine ⟨dk, ekSeed, ekVector, hkg, bytes, rfl,\n')],
     UNSOLVED + r'(?:.*\n)*?⊢ False', ['established_encrypt_outcomes']),
    ('encrypt', 'first-triple-send-claimed-to-refuse',
     [(re.escape('    ∃ tripleNext header messageKey,\n'
                 '      Model.Triple.sendDetailed (establishedModelOf dh p.session).triple 0 none =\n'
                 '        .ok (tripleNext, header, messageKey) ∧\n'
                 '      header.dr.dh = (establishedModelOf dh p.session).triple.classical.dhsPub ∧\n'
                 '      header.dr.n = 0 ∧ header.dr.pn = 0 ∧ header.epoch = 0 ∧ header.pqN = 1 := by\n'),
       '    ∃ reason, Model.Triple.sendDetailed (establishedModelOf dh p.session).triple 0 none =\n'
       '        .error reason := by\n')],
     UNSOLVED + r'(?:.*\n)*?⊢ False', ['established_triple_send_ok']),
    ('encrypt', 'first-header-sparse-number-zero',
     [(re.escape('      header.dr.n = 0 ∧ header.dr.pn = 0 ∧ header.epoch = 0 ∧ header.pqN = 1 := by\n'
                 '  simp [Model.Triple.sendDetailed'),
       '      header.dr.n = 0 ∧ header.dr.pn = 0 ∧ header.epoch = 0 ∧ header.pqN = 0 := by\n'
       '  simp [Model.Triple.sendDetailed')],
     UNSOLVED + r'(?:.*\n)*?⊢ False', ['established_triple_send_ok']),
    ('encrypt', 'wire-claimed-to-be-the-bare-ratchet-frame',
     [(re.escape('            .ok (initialWire (establishedModelOf dh p.session) pending\n'
                 '              (firstFrame view oracle (establishedModelOf dh p.session) plaintext messageKey chunk)) ∧\n'),
       '            .ok (firstFrame view oracle (establishedModelOf dh p.session) plaintext messageKey chunk) ∧\n')],
     UNSOLVED + r'(?:.*\n)*?⊢ [^\n]*encodeInitial', ['established_encrypt_model_cases']),
    ('encrypt', 'successor-counters-claimed-uncounted',
     [(re.escape('        (q.2.send = some ch ∨ q.2.receive = some ch) → ch.n ≤ 1 := by\n'),
       '        (q.2.send = some ch ∨ q.2.receive = some ch) → ch.n ≤ 0 := by\n')],
     UNSOLVED + r'(?:.*\n)*?⊢ False', ['established_triple_next_counters']),
    ('encrypt', 'sent-triple-with-the-send-uncounted',
     [(re.escape('        ns := 1#u32, nr := 0#u32, pn := 0#u32, skipped := alloc.vec.Vec.new tacenta_ratchet.SkippedKey,\n'
                 '        events := 0#u32, labels := tacenta_ratchet.LabelSet.Tacenta },\n'
                 '    post_quantum :=\n'
                 '      { rk := prk, epoch := 0#u64, chains := sentChains c1 c2,'),
       '        ns := 0#u32, nr := 0#u32, pn := 0#u32, skipped := alloc.vec.Vec.new tacenta_ratchet.SkippedKey,\n'
       '        events := 0#u32, labels := tacenta_ratchet.LabelSet.Tacenta },\n'
       '    post_quantum :=\n'
       '      { rk := prk, epoch := 0#u64, chains := sentChains c1 c2,')],
     r'Tactic `rfl` failed(?:.*\n)*?.*ns := 1#u32', ['triple_eq_sent']),
    ('encrypt', 'successor-invariant-without-validate-ek',
     [(re.escape('  have hkp := keyPairValid_of_header hval kp hh0 v hhh hv ekSeed ekVector hhval hvval hs32 hvl hhl\n'),
       '  have hkp : tacenta_braid.key_pair_valid kp = ok true := by\n'
       '    unfold tacenta_braid.key_pair_valid\n'
       '    simp only [hhh, hv, bind_tc_ok]\n')],
     UNSOLVED + r'(?:.*\n)*?⊢ [^\n]*validate_ek', ['established_encrypt_successor_admissible']),
    ('encrypt', 'successor-invariant-without-the-seed-length',
     [(re.escape('    ekSeed.length = 32 ∧ ekVector.length = K.ekSize ∧ (K.hashEk ekSeed ekVector).length = 32\n'),
       '    ekVector.length = K.ekSize ∧ (K.hashEk ekSeed ekVector).length = 32\n'),
      (re.escape('  obtain ⟨hs32, hvl, hhl⟩ := hsizes _ _ _ _ hkg\n'),
       '  obtain ⟨hvl, hhl⟩ := hsizes _ _ _ _ hkg\n'
       '  have hs32 : ekSeed.length = 32 := by\n'
       '    have hl := congrArg List.length hhval\n'
       '    simp only [List.length_append] at hl\n'
       '    omega\n')],
     r'omega could not prove the goal(?:.*\n)*?.*ekSeed',
     ['established_encrypt_successor_admissible']),
    ('encrypt', 'joint-model-key-generation-that-leaves-the-source',
     [(re.escape("  let (rng', seed) ← rc.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros64\n"
                 "  let r := Model.Messages.leValue (sliceOf seed)\n"
                 "  ok (if r = 0 then .Err () else .Ok r, rng')\n"),
       "  let (_, seed) ← rc.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros64\n"
       "  let r := Model.Messages.leValue (sliceOf seed)\n"
       "  ok (if r = 0 then .Err () else .Ok r, rng)\n")],
     PROOF, ['genFill_answers']),
    ('encryptpinned', 'key-generation-answer-without-its-refusing-arm-pinned',
     [(re.escape('          K.decaps dk (sliceOf ct1) (sliceOf ct2) = none))) ∨\n'
                 "  ((∃ e, I.ikpGenerate rc crc rng = ok (core.result.Result.Err e, rng')) ∧ K.keyGen rand = none)\n"),
       '          K.decaps dk (sliceOf ct1) (sliceOf ct2) = none)))\n')],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenAnswersShape')),
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
    """The 1-based line of the `#guard_msgs in` that precedes `#print name` (a definition's pin) or
    `#check @name` (a theorem's statement pin), or None."""
    lines = text.split('\n')
    for k in range(1, len(lines)):
        if lines[k] in (f'#print {name}', f'#check @{name}') and lines[k - 1].startswith('#guard_msgs'):
            return k
    return None


MESSAGE_HEAD = re.compile(r'^\S+\.lean:(\d+):\d+: (error|warning|info)')


def errors_of(output):
    """Every error Lean printed, as (1-based line, message with its continuation lines)."""
    errors, current = [], None
    for line in output.split('\n'):
        m = MESSAGE_HEAD.match(line)
        if m:
            current = [int(m.group(1)), line] if m.group(2) == 'error' else None
            if current is not None:
                errors.append(current)
        elif current is not None:
            current[1] += '\n' + line
    return [(n, message) for n, message in errors]


def check_refused(name, status, output, marker, log, mutated, where):
    refused = (status != 0 and 'error' in output and re.search(marker, output)
               and not any(bad in output for bad in NOT_A_REFUSAL))
    if not refused:
        raise SystemExit(f'FAILED control {name}: expected Lean to refuse it with `{marker}`, '
                         f'exit={status}; {log}')
    errors = errors_of(output)
    if isinstance(where, tuple):
        line = pin_line(mutated, where[1])
        if line is None:
            raise SystemExit(f'FAILED control {name}: the copy has no pin of {where[1]}, so '
                             f'its refusal cannot be the pin\'s; {log}')
        if not any(e == line and re.search(marker, m) for e, m in errors):
            raise SystemExit(f'FAILED control {name}: refused, but not at the pin of {where[1]} '
                             f'(line {line}) with `{marker}`; {log}')
        return f'the pin of {where[1]}'
    for decl in where:
        span = declaration_lines(mutated, decl)
        if span is None:
            raise SystemExit(f'Target changed for {name}: no declaration {decl} in the copy')
        if any(span[0] <= e <= span[1] and re.search(marker, m) for e, m in errors):
            return decl
    raise SystemExit(f'FAILED control {name}: refused, but in none of {", ".join(where)} with '
                     f'`{marker}`; {log}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=900)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='encrypt-logs-'))
    logs.mkdir(parents=True, exist_ok=True)
    encrypt = ENCRYPT.read_text()
    sources = {
        'encrypt': without_pins(encrypt, ENCRYPT),
        'encryptpinned': encrypt,
    }
    results = {
        'encrypt_sha256': hashlib.sha256(encrypt.encode()).hexdigest(),
        'accepted': [], 'rejected': {},
    }
    with tempfile.TemporaryDirectory(prefix='encrypt-controls-') as tmp:
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
