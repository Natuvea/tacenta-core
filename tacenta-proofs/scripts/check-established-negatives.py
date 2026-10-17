#!/usr/bin/env python3
"""Hold the established-initiator theorems against a planted fault.

`Translation/UnitLifecycleEstablishInitiatorShape.lean` derives, at every successful
`establish_initiator_for` output, `Session::invariant` (under the laws `DhPublicValid` and
`KemCiphertextLenOf` and the recorded `OptionEqU64Shape`), the four ceilings of `CounterHeadroom` and the
relation to `establishedModelOf`, and shows the success case inhabited under `InitiatorSuccessShape`.  A
proof that Lean accepts after the fact it rests on is removed would hold nothing, so this script makes one
change to a copy of the module and requires Lean to refuse it, at a named place:

  * the Triple the walk reads off with its classical clock at 1 instead of the 0 `init_sender` writes
    (refused in `init_sender_ok`, so the shape is the generated code's);
  * the structural invariant without `DhPublicValid` for our identity key, without it for the pending
    ephemeral key, without `KemCiphertextLenOf` for the pending ciphertext, and without the inversion of
    `verify_bundle` for the peer's identity key (each refused in `structural_parts`);
  * `DhPublicValid` without its prime-order clause (refused in `dhPublicValid_valid`, where the identity
    clause first uses it);
  * the ceiling lemma restated at the output with the classical clock at the park, `u32::MAX - 1`, and with
    the Braid epoch at `u64::MAX - 1` (each refused in `counterHeadroom_parts`);
  * the model state with the Braid epoch one higher, and with empty associated data (each refused in
    `sessionRefines_parts`);
  * `InitiatorSuccessShape` without the self-equality of the key, which the expected-identity check needs
    (refused in `establish_initiator_for_succeeds`);
  * the joint model of `UnitLifecycleEstablishedDecrypt.lean` with the public key of `Interp.modelDecrypt`,
    the private key's bytes (refused in `established_decrypt_laws_model`, since such a key need not be
    canonical);
  * `DhPublicValid` without its prime-order clause with the module's pins kept (refused at the pin of
    `DhPublicValidShape`).

The changes are checked on copies without the modules' pins, so that the refusal comes from a proof and not
from a pin, except the one kept with its pins.  The unmodified copies must be accepted first.  A timeout, a
compiler that does not start, a syntax error, an unrelated failure and a refusal elsewhere than the named
place never count.  These are proof-dependency controls on copies of the Lean; no source, olean or git
state changes.

Dependencies must be built (`lake build Translation.UnitLifecycleEstablishedDecrypt`).
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
SHAPE = ROOT / 'translation/Translation/UnitLifecycleEstablishInitiatorShape.lean'
DECRYPT = ROOT / 'translation/Translation/UnitLifecycleEstablishedDecrypt.lean'

PROOF = (r'unsolved goals|Application type mismatch|Type mismatch|type mismatch|omega could not prove'
         r'|made no progress|rcases|Insufficient number of fields|failed to prove|rewrite. failed'
         r'|The rfl tactic failed|rfl. failed|scalar_tac failed|simp failed')

PARKED = ('{ p.session with triple := { p.session.triple with classical :=\n'
          '      { p.session.triple.classical with events := 4294967294#u32 } } }')
LAST_EPOCH = '{ p.session with braid := ⟨tacenta_braid.State.KeysUnsampled 18446744073709551614#u64 p.auth⟩ }'
LAW_SHAPE = (r'    ∃ a, I\.dhPubAsBytes pkb = ok a ∧ Tacenta\.SessionUnitT1\.canonicalX25519 a = true ∧\n'
             r'      I\.dhIsPrimeOrderPublic pkb = ok true\n')
LAW_SHAPE_WEAK = '    ∃ a, I.dhPubAsBytes pkb = ok a ∧ Tacenta.SessionUnitT1.canonicalX25519 a = true\n'
LAW_IS = (r'          Tacenta\.SessionUnitT1\.canonicalX25519 a = true ∧\n'
          r'          tacenta_boundary\.dh\.is_prime_order_public pkb = ok true :=\n')
LAW_IS_WEAK = '          Tacenta.SessionUnitT1.canonicalX25519 a = true :=\n'

# (copy, name, [(pattern, replacement), ...], a regular expression the refused output must contain,
#  where the refusal must be: declarations one of whose lines holds an error, or ('pin', name) for the
#  `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
    ('shape', 'triple-clock-not-the-generated-zero',
     [(r'        events := 0#u32, labels := tacenta_ratchet\.LabelSet\.Tacenta \},\n',
       '        events := 1#u32, labels := tacenta_ratchet.LabelSet.Tacenta },\n')], PROOF,
     ['init_sender_ok']),
    ('shape', 'structural-without-the-identity-law',
     [(r'  have hv := identity_public_valid hpub p\.hOurPublic\n', '  have hv : True := trivial\n')],
     PROOF, ['structural_parts']),
    ('shape', 'structural-without-the-ephemeral-law',
     [(r'  have hc := \(dhPublicValid_valid hpub p\.hEphemeralPublic\)\.2\n',
       '  have hc : True := trivial\n')], PROOF, ['structural_parts']),
    ('shape', 'structural-without-the-ciphertext-law',
     [(r'  obtain ⟨n, hctl, hlen0⟩ := kemCiphertextLenOf_is\.mp hct rc crc _ _ _ _ _ p\.hEncapsulate\n',
       '  obtain ⟨n, hctl, hlen0⟩ : ∃ n : Usize, True ∧ True := ⟨0#usize, trivial, trivial⟩\n')],
     PROOF, ['structural_parts']),
    ('shape', 'structural-without-the-verify-bundle-inversion',
     [(r'    tacenta_spqr\.State\.impl\.direction, hv, p\.hPeerValid, hc, hctl, hlen,\n',
       '    tacenta_spqr.State.impl.direction, hv, hc, hctl, hlen,\n')], PROOF, ['structural_parts']),
    ('shape', 'law-without-the-prime-order-clause',
     [(LAW_SHAPE, LAW_SHAPE_WEAK), (LAW_IS, LAW_IS_WEAK)], PROOF,
     ['dhPublicValid_valid']),
    ('shape', 'ceilings-at-the-parked-clock',
     [(r'    Tacenta\.UnitLifecycleDecryptRunBounds\.CounterHeadroom p\.session := by\n',
       '    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom\n      ' + PARKED + ' := by\n')],
     PROOF, ['counterHeadroom_parts']),
    ('shape', 'ceilings-at-the-last-braid-epoch',
     [(r'    Tacenta\.UnitLifecycleDecryptRunBounds\.CounterHeadroom p\.session := by\n',
       '    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom\n      ' + LAST_EPOCH + ' := by\n')],
     PROOF, ['counterHeadroom_parts']),
    ('shape', 'model-braid-epoch-one-higher',
     [(r'  \| \.KeysUnsampled epoch auth => \.keysUnsampled epoch\.val ',
       '  | .KeysUnsampled epoch auth => .keysUnsampled (epoch.val + 1) ')], PROOF,
     ['sessionRefines_parts']),
    ('shape', 'model-associated-data-empty',
     [(r'    identityAd := vecOf s\.identity_ad\n', '    identityAd := []\n')], PROOF,
     ['sessionRefines_parts']),
    ('shape', 'success-without-the-self-equality',
     [(r'    I\.dhIsPrimeOrderPublic pkb = ok true ∧ I\.dhPubEq pkb pkb = ok true ∧\n',
       '    I.dhIsPrimeOrderPublic pkb = ok true ∧\n')], PROOF,
     ['establish_initiator_for_succeeds']),
    ('decrypt', 'joint-model-with-the-decrypt-model-public-key',
     [(r'    dhPrivPublicKey := fun _ => ok Tacenta\.UnitLifecycleDecryptRatchetScreen\.zeros32 \}\n',
       '    dhPrivPublicKey := fun k => ok k }\n')], PROOF, ['established_decrypt_laws_model']),
    ('shapepinned', 'law-without-the-prime-order-clause-pinned',
     [(LAW_SHAPE, LAW_SHAPE_WEAK), (LAW_IS, LAW_IS_WEAK)],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape')),
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
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='established-logs-'))
    logs.mkdir(parents=True, exist_ok=True)
    shape = SHAPE.read_text()
    decrypt = DECRYPT.read_text()
    sources = {
        'shape': without_pins(shape, SHAPE),
        'shapepinned': shape,
        'decrypt': without_pins(decrypt, DECRYPT),
    }
    results = {
        'shape_sha256': hashlib.sha256(shape.encode()).hexdigest(),
        'decrypt_sha256': hashlib.sha256(decrypt.encode()).hexdigest(),
        'accepted': [], 'rejected': {},
    }
    with tempfile.TemporaryDirectory(prefix='established-controls-') as tmp:
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
