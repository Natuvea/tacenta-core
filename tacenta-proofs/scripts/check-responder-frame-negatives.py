#!/usr/bin/env python3
"""Hold the first-frame responder theorems against a planted fault.

`Translation/UnitLifecycleResponderFirstFrame.lean` feeds the bytes the initiator's first `encrypt` emits to
`establish_responder`, at a store whose `publish` returned the bundle the initiator used: only the three
refusals the store decides remain, or the call reaches the inner receive with the initiator's shared secret;
the laws hold in one interpretation and one run reaches the inner receive.  A proof that Lean accepts after
the fact it rests on is removed would hold nothing, so this script makes one change to a copy of the module
and requires Lean to refuse it, at a named place, with an error that names what the change removed:

  * the agreement law weakened to agree with itself (refused in `shared_secret_symmetric`: the responder's
    agreement with the initiator's identity key is no longer the initiator's with the signed prekey);
  * the joint model's agreement returning the private key, and its public key the zero key (refused in
    `modelFirstFrame_symmetric` and `first_frame_laws_model`: the agreement is no longer symmetric, and no
    published key agrees contributorily);
  * the per-run KEM premise saying nothing of what decapsulation returns (refused in
    `responder_first_frame_prepares`, where the decapsulated secret must be the initiator's);
  * the store's distinctness kept for the signed prekey's and the last-resort key's identifiers only, once
    for repeat-freedom and once for `ABSENT_ID`'s absence (refused in `distinct_kem_last` and
    `distinct_pool_last`);
  * the legacy refusal claimed when the marker does not list the key (refused in
    `responder_first_frame_prepares`) and the full-record refusal claimed at an empty record (refused in
    `replay_refusal_cause`);
  * the parts' shared secret claimed to be the ratchet agreement, and their peer identity key claimed to be
    the initiator's ephemeral key (refused in `responder_first_frame_prepares`), and the last-resort flag
    inverted (same place);
  * the decoded KEM identifier claimed to be the bundle's signed prekey identifier (refused in
    `decode_first_frame`), and `publish` claimed to name the first one-time KEM entry (refused in
    `publish_parts`);
  * the one-time KEM lookup without the premise that the identifier occurs nowhere earlier (refused in
    `kem_slot_one_time`: `u32_index` returns the first occurrence);
  * the initiator's ratchet agreement claimed to be with its identity key (refused in
    `establish_initiator_for_secret`);
  * the reach's store with a legacy marker on its last-resort key (refused in
    `first_send_responder_reachable`: the call may then refuse);
  * the composed statement's frame claimed to seal the empty plaintext whatever was sent (refused in
    `first_send_responder_prepares`);
  * the agreement law weakened with the module's pins kept (refused at the pin of `DhAgreeSymmetricShape`).

Every change is to a statement or a definition; none replaces a proof step.  So each refusal shows that the
changed statement is false, or contradicts a value the proof supplies, or (for the last) that the pin holds
the definition.

The changes are checked on a copy without the module's pins, so that the refusal comes from a proof and not
from a pin, except the one kept with its pins.  The unmodified copies must be accepted first.  A timeout, a
compiler that does not start, a syntax error, an unrelated failure and a refusal elsewhere than the named
place never count; an error whose first line names a kind of failure that is not a refusal (an unresolved
name, a syntax error) voids the run anywhere in the copy, compared without regard to case, and the script
checks at start that this guard fires on the toolchain's own `Unknown identifier`.  These are controls on
copies of the Lean; no source, olean or git state changes.

Dependencies must be built (`lake build Translation.UnitLifecycleResponderFirstFrame`).
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
MODULE = ROOT / 'translation/Translation/UnitLifecycleResponderFirstFrame.lean'

PREPARES_TAIL = (
    '        p.shared = q.shared ∧ p.secret = q.sharedBytes ∧ p.tripleSecret = q.sharedSlice ∧\n'
    '        p.braidSecret = q.sharedSlice ∧ p.peerIdentity = q.ourPublic ∧\n'
    '        p.peerEphemeral = q.ephemeralPublic ∧ p.kemSecret = q.kemSecret ∧\n'
    '        sliceOf (ResponderPreparedParts.message p) = frame ∧\n'
    '        (p.lastResort = true ↔ bundle.kem_prekey_id = storeB.kem_id) := by\n')

SYM_DEF = ('    I.dhPrivPublicKey b = ok pb → I.dhPrivAgree a pb = I.dhPrivAgree b pa\n',
           '    I.dhPrivPublicKey b = ok pb → I.dhPrivAgree a pb = I.dhPrivAgree a pb\n')
SYM_IS = ('      tacenta_boundary.dh.PrivateKey.agree a pb = tacenta_boundary.dh.PrivateKey.agree b pa := Iff.rfl\n',
          '      tacenta_boundary.dh.PrivateKey.agree a pb = tacenta_boundary.dh.PrivateKey.agree a pb := Iff.rfl\n')

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
    ('module', 'agreement-law-with-itself', [SYM_DEF, SYM_IS],
     r'Tactic `rfl` failed[\s\S]*spk\.agree pubA', ['shared_secret_symmetric']),
    ('module', 'joint-model-agreement-returns-the-private-key',
     [('    dhPrivAgree := fun _ p => ok (if p.val = Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none\n'
       '      else some p) }\n',
       '    dhPrivAgree := fun k p => ok (if p.val = Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none\n'
       '      else some k) }\n')],
     r'dhPrivAgree a UnitLifecycleEstablishResponder\.basePoint\nis not definitionally equal to the right-hand side\n  Interp\.modelFirstFrame\.dhPrivAgree b', ['modelFirstFrame_symmetric']),
    ('module', 'joint-model-public-key-zero',
     [('    dhPrivPublicKey := fun _ => ok Tacenta.UnitLifecycleEstablishResponder.basePoint\n',
       '    dhPrivPublicKey := fun _ => ok Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32\n')],
     r'dhPrivPublicKey UnitLifecycleDecryptRatchetScreen\.zeros32 =\n    ok UnitLifecycleEstablishResponder\.basePoint', ['first_frame_laws_model']),
    ('module', 'kem-premise-without-decapsulation',
     [('  ∃ pair, heldKemPair store id = some pair ∧\n'
       '    tacenta_boundary.kem.decapsulate pair (alloc.vec.Vec.deref ct) = ok (core.result.Result.Ok ss)\n',
       '  ∃ pair, heldKemPair store id = some pair ∧\n'
       '    tacenta_boundary.kem.decapsulate pair (alloc.vec.Vec.deref ct) =\n'
       '      tacenta_boundary.kem.decapsulate pair (alloc.vec.Vec.deref ct)\n')],
     r'but is expected to have type\n  tacenta_boundary\.kem\.decapsulate storeB\.kem \S+ = ok \(core\.result\.Result\.Ok q\.kemSecret\)', ['responder_first_frame_prepares']),
    ('module', 'distinct-without-repeat-freedom',
     [('    (storeIds store v.val).Nodup ∧ serialization.ABSENT_ID ∉ storeIds store v.val\n',
       '    ((storeIds store v.val).take 2).Nodup ∧ serialization.ABSENT_ID ∉ storeIds store v.val\n')],
     r'Did not find an occurrence of the pattern\n  @List\.Nodup[\s\S]*List\.take 2', ['distinct_kem_last']),
    ('module', 'distinct-without-absent-id',
     [('    (storeIds store v.val).Nodup ∧ serialization.ABSENT_ID ∉ storeIds store v.val\n',
       '    (storeIds store v.val).Nodup ∧ serialization.ABSENT_ID ∉ (storeIds store v.val).take 2\n')],
     r'e\.1 ∈ storeIds store ↑v\nbut is expected to have type\n  e\.1 ∈ List\.take 2', ['distinct_pool_last']),
    ('module', 'legacy-refusal-without-the-marker',
     [('  (e = lifecycle.Error.LegacyLastResortRecord ∧ store.kem_id ∈ store.legacy_last_resort_blocked.val) ∨\n',
       '  (e = lifecycle.Error.LegacyLastResortRecord ∧ store.kem_id ∉ store.legacy_last_resort_blocked.val) ∨\n')],
     r'storeB\.kem_id ∈ ↑storeB\.legacy_last_resort_blocked\nbut is expected to have type\n  storeB\.kem_id ∉', ['responder_first_frame_prepares']),
    ('module', 'full-record-refusal-at-an-empty-record',
     [('        (e = lifecycle.Error.LastResortRecordFull ∧ store.last_resort_seen.val ≠ [])) := by\n',
       '        (e = lifecycle.Error.LastResortRecordFull ∧ store.last_resort_seen.val = [])) := by\n')],
     r'↑store\.last_resort_seen ≠ \[\]\nbut is expected to have type\n  ↑store\.last_resort_seen = \[\]', ['replay_refusal_cause']),
    ('module', 'shared-secret-claimed-the-ratchet-agreement',
     [(PREPARES_TAIL, PREPARES_TAIL.replace('p.shared = q.shared', 'p.shared = q.dhOut'))],
     r'p\.shared = q\.shared\nbut is expected to have type\n  p\.shared = q\.dhOut', ['responder_first_frame_prepares']),
    ('module', 'peer-identity-claimed-the-ephemeral-key',
     [(PREPARES_TAIL, PREPARES_TAIL.replace('p.peerIdentity = q.ourPublic', 'p.peerIdentity = q.ephemeralPublic'))],
     r'p\.peerIdentity = q\.ourPublic\nbut is expected to have type\n  p\.peerIdentity = q\.ephemeralPublic', ['responder_first_frame_prepares']),
    ('module', 'last-resort-flag-inverted',
     [(PREPARES_TAIL, PREPARES_TAIL.replace('(p.lastResort = true ↔', '(p.lastResort = false ↔'))],
     r'but is expected to have type\n  true = false', ['responder_first_frame_prepares']),
    ('module', 'decoded-kem-identifier-the-signed-prekeys',
     [('      d.kem_prekey_id = bundle.kem_prekey_id ∧\n', '      d.kem_prekey_id = bundle.signed_prekey_id ∧\n')],
     r'kemPrekeyId := UInt32\.ofNat ↑bundle\.kem_prekey_id[\s\S]*but is expected to have type\n  UInt32\.ofNat ↑d\.kem_prekey_id = UInt32\.ofNat ↑bundle\.signed_prekey_id', ['decode_first_frame']),
    ('module', 'publish-names-the-first-kem-entry',
     [('      (∃ e, store.kem_one_time.val.getLast? = some e ∧ bundle.kem_prekey_id = e.1 ∧\n',
       '      (∃ e, store.kem_one_time.val.head? = some e ∧ bundle.kem_prekey_id = e.1 ∧\n')],
     r'getLast\? = some \(id, pair, sig\)\nbut is expected to have type\n  \(↑store\.kem_one_time\)\.head\?', ['publish_parts']),
    ('module', 'kem-lookup-without-first-occurrence',
     [('    (hprev : ∀ x, store.previous_kem = some x → x.2.1 ≠ e.1) (hpre : e.1 ∉ pre.map (·.1)) :\n',
       '    (hprev : ∀ x, store.previous_kem = some x → x.2.1 ≠ e.1) (hpre : True) :\n')],
     r'hpre\nhas type\n  True\nbut is expected to have type\n  e\.1 ∉', ['kem_slot_one_time']),
    ('module', 'ratchet-agreement-with-the-identity-key',
     [('  hDhOut : tacenta_boundary.dh.PrivateKey.agree ratchetPrivate bundle.bundle.signed_prekey = ok (some dhOut)\n',
       '  hDhOut : tacenta_boundary.dh.PrivateKey.agree identityKey bundle.bundle.signed_prekey = ok (some dhOut)\n')],
     r'Tactic `assumption` failed[\s\S]*⊢ \S+\.agree bundle\.bundle\.signed_prekey = ok \(some', ['establish_initiator_for_secret']),
    ('module', 'reach-store-with-a-legacy-marker',
     [('    next_id := 3#u32, last_resort_seen := alloc.vec.Vec.new _, legacy_last_resort_blocked := alloc.vec.Vec.new _ }\n',
       '    next_id := 3#u32, last_resort_seen := alloc.vec.Vec.new _,\n'
       '    legacy_last_resort_blocked := Tacenta.UnitHeadroomSatisfiable.vecOf [2#u32] (by simp) }\n')],
     r'hleg : 2#u32 ∈[\s\S]*⊢ False', ['first_send_responder_reachable']),
    ('module', 'composed-frame-claimed-for-the-empty-plaintext',
     [('            Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame view oracle (establishedModelOf dh s)\n'
       '              (sliceOf plaintext) messageKey chunk ∧\n',
       '            Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame view oracle (establishedModelOf dh s)\n'
       '              [] messageKey chunk ∧\n')],
     r'\(sliceOf plaintext\)\s+messageKey chunk[\s\S]*but is expected to have type[\s\S]*firstFrame view oracle \(establishedModelOf dh q\.session\) \[\]', ['first_send_responder_prepares']),
    ('pinned', 'agreement-law-with-itself-pinned', [SYM_DEF, SYM_IS],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetricShape')),
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
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='responder-frame-logs-'))
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
    with tempfile.TemporaryDirectory(prefix='responder-frame-controls-') as tmp:
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
