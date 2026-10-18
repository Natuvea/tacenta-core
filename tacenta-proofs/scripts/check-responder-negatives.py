#!/usr/bin/env python3
"""Hold the `establish_responder` theorems against a planted fault.

`Translation/UnitLifecycleEstablishResponder.lean` composes the translated `establish_responder` for
every input (three outcomes, each with its store and random-source effects), derives
`Session::invariant`, the four ceilings of `CounterHeadroom` and the relation to `responderModelOf` for the
session it hands to `decrypt_ratchet`, states what the success commit does to the store, and shows outcomes
reached and the premises jointly satisfiable.  A proof that Lean accepts after the fact it rests on is
removed would hold nothing, so this script makes one change to a copy of the module and requires Lean to
refuse it, at a named place, with the error the removed fact causes:

  * the structural invariant without `DhPublicValid` for our identity key, without the curve-input
    inversion for the initiator's identity key, and without the code's own decode check of the established
    ephemeral (each refused in `responder_structural`, at the clause that needs the fact);
  * the session handed to `decrypt_ratchet` with no established ephemeral (refused in
    `responder_structural`: the role clause compares `is_initiator = some false` with a responder flag that
    is now false);
  * the Braid decoder's size check restated without the MAC (refused in `hdr_decoder_checks`: the decoder is
    sized for the header and its MAC);
  * the fresh-decoder invariant without its chunk-count bound, and the decoder check without the bound on
    `HEADER_LEN` (refused in `fresh_decoder_invariant` and `hdr_decoder_checks`: the `MAX_CODEWORDS` check
    needs them);
  * the ceiling lemma restated at the intermediate session with the classical clock parked at
    `u32::MAX - 1` (refused in `counterHeadroom_responder_prepared`, by the clock's value);
  * the model session's Braid as the initiator's initial state, and its associated data empty (each refused
    in `sessionRefines_responder_prepared`);
  * `ReplayedLastResort` dropped from the refusals before the inner receive (refused in
    `establish_responder_cases`, at the replay arm);
  * the success commit with no one-time removal on the path without a fingerprint (refused in
    `establish_responder_cases`, where the store after the removals is returned);
  * an inner refusal claimed to return the source of randomness it was given (refused in
    `establish_responder_cases`: the call returns the source `decrypt_ratchet` returned);
  * the commit claimed to leave the replay record unchanged when a fingerprint was computed, and the
    one-time KEM prekeys claimed unchanged on the one-time path (each refused in `responderCommit_effects`);
  * an inner success claimed to give a draw back rather than take one (refused in
    `establish_responder_refines`) and a model success claimed to keep the oracle (refused in
    `decryptRatchet_oracle`);
  * the joint model at a base point equal to the zero key (refused in `responder_route_laws_model`: the
    model's agreement refuses the zero key, so the contributory clause fails);
  * the commit with the replay append dropped, with the module's pins kept (refused at the pin of
    `ResponderCommit`).

Each refusal is checked at its place and against a message that names what the change removed: the
clause left unsolved (the identity check of our key, of the initiator's key, the decode of the ephemeral,
the associated data's role order, the decoder's size, the chunk bound, the parked clock, the replay arm,
the record's appended pair, the oracle's draw, the draw list one longer than itself), or the value the proof
supplies against the one the change claims (the store after the removals, the source `decrypt_ratchet`
returned, the model's initial responder state, the associated data, the zero base point, the last-resort
flag the KEM prekeys' clause needs).  None is refused only by a goal that does not mention the change.  The changes are checked on a copy without the
module's pins, so that the refusal comes from a proof and not from a pin, except the one kept with its pins.
The unmodified copies must be accepted first.  A timeout, a compiler that does not start, a syntax error, an
unrelated failure and a refusal elsewhere than the named place never count.  These are proof-dependency
controls on copies of the Lean; no source, olean or git state changes.

Dependencies must be built (`lake build Translation.UnitLifecycleEstablishResponder`).
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
MODULE = ROOT / 'translation/Translation/UnitLifecycleEstablishResponder.lean'

PARKED = ('{ p.session with triple := { p.session.triple with classical :=\n'
          '      { p.session.triple.classical with events := 4294967294#u32 } } }')

# (copy, name, [(pattern, replacement), ...], a regular expression the refused output must contain,
#  where the refusal must be: declarations one of whose lines holds an error, or ('pin', name) for the
#  `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
    ('module', 'structural-without-the-identity-law',
     [(r'  have hv := identity_public_valid hpub p\.hOurPublic\n', '  have hv : True := trivial\n')],
     r'unsolved goals[\s\S]*is_valid_identity_key p\.ourPublic', ['responder_structural']),
    ('module', 'structural-without-the-peer-identity-check',
     [(r'  obtain ⟨-, hvalid, hdecEph⟩ := curve_inputs_ok _ _ _ _ p\.hCurve\n',
       '  obtain ⟨-, -, hdecEph⟩ := curve_inputs_ok _ _ _ _ p.hCurve\n  have hvalid : True := trivial\n')],
     r'unsolved goals[\s\S]*is_valid_identity_key p\.peerIdentity', ['responder_structural']),
    ('module', 'structural-without-the-ephemeral-decode-check',
     [(r'  obtain ⟨-, hvalid, hdecEph⟩ := curve_inputs_ok _ _ _ _ p\.hCurve\n',
       '  obtain ⟨-, hvalid, -⟩ := curve_inputs_ok _ _ _ _ p.hCurve\n  have hdecEph : True := trivial\n')],
     r'unsolved goals[\s\S]*decode_ec p\.decoded\.ephemeral\.deref', ['responder_structural']),
    ('module', 'session-without-the-established-ephemeral',
     [(r'    established_ephemeral := some p\.ephemeralCopy \}\n', '    established_ephemeral := none }\n')],
     r'unsolved goals[\s\S]*identity_ad p\.ourPublic p\.peerIdentity', ['responder_structural']),
    ('module', 'decoder-sized-without-the-mac',
     [(r'        let i1 ← i \+ tacenta_braid\.MAC_LEN\n        tacenta_braid\.decoder_sized d i1\) = ok true := by\n',
       '        tacenta_braid.decoder_sized d i) = ok true := by\n')],
     r'unsolved goals[\s\S]*⊢ n = hv', ['hdr_decoder_checks']),
    ('module', 'fresh-decoder-without-the-chunk-bound',
     [(r'    \(hle : needed\.val ≤ 65536\) :\n', '    (hle : True) :\n')],
     r'⊢ ↑needed ≤ 65536', ['fresh_decoder_invariant']),
    ('module', 'decoder-check-without-the-header-bound',
     [(r'  obtain ⟨hv\', hhv\', hle⟩ := hhdr\n',
       "  obtain ⟨hv', hhv', -⟩ := hhdr\n  have hle : True := trivial\n")],
     r'omega could not prove the goal[\s\S]*b ≥ 65537', ['hdr_decoder_checks']),
    ('module', 'ceilings-at-the-parked-clock',
     [(r'    Tacenta\.UnitLifecycleDecryptRunBounds\.CounterHeadroom p\.session := by\n',
       '    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom\n      ' + PARKED + ' := by\n')],
     r'unsolved goals[\s\S]*events := 4294967294#u32', ['counterHeadroom_responder_prepared']),
    ('module', 'model-braid-the-initiators',
     [(r'    braid := Model\.Braid\.initBob \(sliceOf p\.braidSecret\)\n',
       '    braid := Model.Braid.initAlice (sliceOf p.braidSecret)\n')],
     r'Model\.Braid\.initBob[\s\S]*but is expected to have type[\s\S]*\(responderModelOf dh p\)\.braid', ['sessionRefines_responder_prepared']),
    ('module', 'model-associated-data-empty',
     [(r'    identityAd := vecOf p\.identityAd\n', '    identityAd := []\n')],
     r'vecOf p\.session\.identity_ad = \(responderModelOf dh p\)\.identityAd', ['sessionRefines_responder_prepared']),
    ('module', 'refusals-without-replayed-last-resort',
     [(r'    e = lifecycle\.Error\.Kem ∨ e = lifecycle\.Error\.ReplayedLastResort ∨\n',
       '    e = lifecycle.Error.Kem ∨\n')],
     r'e6 = lifecycle\.Error\.ReplayedLastResort[\s\S]*⊢ False', ['establish_responder_cases']),
    ('module', 'commit-without-the-removals',
     [(r"      \| none => store' = store2\n", "      | none => store' = store\n")],
     r'\| none => store2 = store', ['establish_responder_cases']),
    ('module', 'inner-refusal-returns-the-given-source',
     [(r"      \(\(∃ e, inner\.1 = core\.result\.Result\.Err e ∧ out = \(core\.result\.Result\.Err e, store, inner\.2\.2\)\) ∨\n",
       "      ((∃ e, inner.1 = core.result.Result.Err e ∧ out = (core.result.Result.Err e, store, rng)) ∨\n")],
     r'out = \(core\.result\.Result\.Err e7, store, rng1\)\nbut is expected to have type\n  out = \(core\.result\.Result\.Err e7, store, rng\)', ['establish_responder_cases']),
    ('module', 'commit-record-unchanged-with-a-fingerprint',
     [(r"      store'\.last_resort_seen\.val = store\.last_resort_seen\.val\.concat \(kemId, fp\)\) := by\n",
       "      store'.last_resort_seen.val = store.last_resort_seen.val) := by\n")],
     r'hs : ↑seen = ↑store2\.last_resort_seen \+\+ \[\(kemId, fp\)\]\n⊢ False', ['responderCommit_effects']),
    ('module', 'commit-kem-prekeys-unchanged-on-the-one-time-path',
     [(r"    \(lastResort = true → store'\.kem_one_time = store\.kem_one_time\) ∧\n",
       "    (lastResort = false → store'.kem_one_time = store.kem_one_time) ∧\n")],
     r'h1b hl[\s\S]*lastResort = true', ['responderCommit_effects']),
    ('module', 'inner-success-gives-a-draw-back',
     [(r'          ∃ d, trace rng = d :: trace inner\.2\.2\)\) := by\n',
       '          ∃ d, trace inner.2.2 = d :: trace rng)) := by\n')],
     r'oracle\.draws =\n    c :: c ::', ['establish_responder_refines']),
    ('module', 'model-success-keeps-the-oracle',
     [(r'    \(∀ pt, \(Model\.Lifecycle\.decryptRatchet view oracle session message\)\.result = \.ok pt →\n'
       r'      ∃ c, Model\.Lifecycle\.random32 oracle =\n'
       r'        some \(c, \(Model\.Lifecycle\.decryptRatchet view oracle session message\)\.oracle\)\) := by\n',
       '    (∀ pt, (Model.Lifecycle.decryptRatchet view oracle session message).result = .ok pt →\n'
       '      (Model.Lifecycle.decryptRatchet view oracle session message).oracle = oracle) := by\n')],
     r'⊢ o = oracle', ['decryptRatchet_oracle']),
    ('module', 'joint-model-at-the-zero-base-point',
     [(r'def basePointBytes : List UInt8 := 9 :: List\.replicate 31 0\n',
       'def basePointBytes : List UInt8 := 0 :: List.replicate 31 0\n'),
      (r'theorem basePoint_length : \(9#u8 :: List\.replicate 31 0#u8\)\.length = \(32#usize\)\.val := by simp\n',
       'theorem basePoint_length : (0#u8 :: List.replicate 31 0#u8).length = (32#usize).val := by simp\n'),
      (r'def basePoint : Array U8 32#usize := ⟨9#u8 :: List\.replicate 31 0#u8, basePoint_length⟩\n',
       'def basePoint : Array U8 32#usize := ⟨0#u8 :: List.replicate 31 0#u8, basePoint_length⟩\n')],
     r'proved that the proposition\n  ↑basePoint ≠ ↑UnitLifecycleDecryptRatchetScreen\.zeros32\nis false', ['responder_route_laws_model']),
    ('pinned', 'commit-without-the-replay-append-pinned',
     [(r"          store' = \{ store2 with last_resort_seen := seen \}\)\n",
       "          store' = store2)\n")],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleEstablishResponder.ResponderCommit')),
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
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='responder-logs-'))
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
    with tempfile.TemporaryDirectory(prefix='responder-controls-') as tmp:
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
