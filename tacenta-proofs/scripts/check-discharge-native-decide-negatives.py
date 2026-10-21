#!/usr/bin/env python3
"""Hold the kernel proofs of the Session unit's refinement constants against a planted fault.

Until 2026-10-21 the sparse ratchet's four labels, its two skip bounds and `MAX_SKIP`'s value, one step of
`receive_refines_continuation` (that `(1 : u64)` has value one) and the Triple's combine and split labels were decided
by `native_decide`, which put a compiler-trust axiom under every lifecycle result through them.  They are now proved by
`simp`, `rfl` and `decide`, in `Translation/SessionUnitSpqrT3.lean` and `Translation/SessionUnitTripleT3.lean` (the
copies the port scripts generate from `SpqrT3.lean` and `UnitTripleT3.lean`), and their pins in
`Translation/AxiomAuditSessionUnit.lean` list the kernel's three axioms.  A kernel proof that Lean accepts after the
fact it states is changed would hold nothing, so this script makes one change to a copy of a module and requires
Lean to refuse it, at a named place, with an error that names the changed fact:

  * a label claimed with one byte changed (`<label>.set 0 0`): `protocol_info_agrees`, `chain_start_agrees`,
    `root_label_agrees`, `chain_label_agrees`, `combine_info_agrees`, `split_info_agrees`, each refused at its own
    declaration by `rfl`, which shows the translated bytes and the changed model bytes are not the same list;
  * a bound claimed wrong: `max_skip_agrees` claiming `MAX_SKIP` is the store cap (refused: `maxSkippedStore = 1000`
    is left unsolved), `max_skipped_store_agrees` claiming the store cap is `maxSkip` (refused: `maxSkip = 2000` left
    unsolved), `max_skip_val` claiming 1001 (refused: `False` left unsolved);
  * the closed fact inside `receive_refines_continuation` claimed as `(1#u64).bv.toNat = 2` (refused there:
    `decide` proves the proposition false);
  * `export_message_fits` (`UnitLifecycleSessionRoundTrip.lean`) claiming the 51-byte message fits 42 bytes (refused
    there: `decide` proves the proposition false);
  * the pin: `native_decide` restored as the proof of `protocol_info_agrees` in a copy carrying that theorem's live pin
    from `AxiomAuditSessionUnit.lean` (refused at the pin, whose generated message lists the compiler-trust axiom).

And one check outside Lean's refusals: `export_message_fits` must state exactly the proposition of the compiler-trust
axiom `export` carries (`tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1`).  A probe built on a
copy of the module compares the two types as expressions and must print `same-type: true`; the same probe on a copy
whose theorem drops one word of the message must print `same-type: false`, or the comparison holds nothing.

Every change is to a statement (for the `(1 : u64)` step, to the statement of the step); none replaces a proof step,
except the pin control, which restores the old proof.  Each refusal is a proof-breakage check at a named place: it shows
that the proof there decides the changed fact, not that the original statement is the only true one.  Not controlled:
the zero-array step of `split_secret_refines`, which sits inside a `try`, so a changed step fails the theorem only as
an unsolved goal elsewhere in it, and the leaf and three-leaf copies (`SpqrT3.lean`, `UnitSpqrT3.lean`,
`UnitTripleT3.lean`), whose bodies the port scripts' `--check` holds byte for byte to the ones controlled here up to the
renamings they list.

The changes are checked on copies without the modules' pins, so that a refusal comes from a proof and not from a pin,
except the pin control.  The unmodified copies must be accepted first.  The label of each control is held to where Lean
refuses it: the first error in the copy must be inside the named declaration (or at the named pin), and an error there,
not a timeout, must match the control's marker.  A timeout, a compiler that does not start, a syntax error, an
unrelated failure and a refusal elsewhere than the named place never count; an error whose first line names a kind of
failure that is not a refusal (an unresolved name in the elaborator's spelling, `Unknown identifier`, or the kernel's,
`unknown constant`, a syntax error) voids the run anywhere in the copy, compared without regard to case.  The script
checks at start that this guard fires on both spellings and not on an ordinary refusal, and that a heartbeat timeout is
recognised as one and never counted as the named refusal.  These are controls on copies of the Lean; no source, olean
or git state changes.

Dependencies must be built (`lake build Translation.AxiomAuditSessionUnit`).
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
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
TR = ROOT / 'translation/Translation'
SPQR = TR / 'SessionUnitSpqrT3.lean'
TRIPLE = TR / 'SessionUnitTripleT3.lean'
ROUNDTRIP = TR / 'UnitLifecycleSessionRoundTrip.lean'
AUDIT = TR / 'AxiomAuditSessionUnit.lean'

AXIOM = 'tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1'
FITS = 'Tacenta.UnitLifecycleSessionRoundTrip.export_message_fits'
MESSAGE = '"the size arithmetic above drifted from the encoding"'


def label(name, model):
    return (f'theorem {name} : sliceOf {model[0]} = {model[1]} := by',
            f'theorem {name} : sliceOf {model[0]} = {model[1]}.set 0 0 := by')


def rfl_marker(model):
    return (r'Tactic `rfl` failed: The left-hand side\n  List\.map u8[\s\S]*is not definitionally equal to the '
            r'right-hand side\n  ' + re.escape(model) + r'\.set 0 0')


PROTOCOL = ('theorem protocol_info_agrees : sliceOf PROTOCOL_INFO = Model.SparseRatchet.protocolInfo := by\n'
            '  simp [sliceOf, PROTOCOL_INFO]; rfl\n')

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression an error at the named
#  place must match, where: a declaration name, or ('pin', name) for the `#guard_msgs` line of the pin of `name`)
MUTANTS = [
    ('spqr', 'protocol-info-byte-changed',
     [label('protocol_info_agrees', ('PROTOCOL_INFO', 'Model.SparseRatchet.protocolInfo'))],
     rfl_marker('Model.SparseRatchet.protocolInfo'), 'protocol_info_agrees'),
    ('spqr', 'chain-start-byte-changed',
     [label('chain_start_agrees', ('CHAIN_START_LABEL', 'Model.SparseRatchet.chainStart'))],
     rfl_marker('Model.SparseRatchet.chainStart'), 'chain_start_agrees'),
    ('spqr', 'root-label-byte-changed',
     [label('root_label_agrees', ('ROOT_LABEL', 'Model.SparseRatchet.rootLabel'))],
     rfl_marker('Model.SparseRatchet.rootLabel'), 'root_label_agrees'),
    ('spqr', 'chain-label-byte-changed',
     [label('chain_label_agrees', ('CHAIN_LABEL', 'Model.SparseRatchet.chainLabel'))],
     rfl_marker('Model.SparseRatchet.chainLabel'), 'chain_label_agrees'),
    ('spqr', 'max-skip-claimed-the-store-cap',
     [('theorem max_skip_agrees : MAX_SKIP.val = Model.SparseRatchet.maxSkip := by',
       'theorem max_skip_agrees : MAX_SKIP.val = Model.SparseRatchet.maxSkippedStore := by')],
     r'unsolved goals\n⊢ Model\.SparseRatchet\.maxSkippedStore = 1000', 'max_skip_agrees'),
    ('spqr', 'store-cap-claimed-max-skip',
     [('    MAX_SKIPPED_STORE.val = Model.SparseRatchet.maxSkippedStore := by',
       '    MAX_SKIPPED_STORE.val = Model.SparseRatchet.maxSkip := by')],
     r'unsolved goals\n⊢ Model\.SparseRatchet\.maxSkip = 2000', 'max_skipped_store_agrees'),
    ('spqr', 'max-skip-value-1001',
     [('theorem max_skip_val : MAX_SKIP.val = 1000 := by', 'theorem max_skip_val : MAX_SKIP.val = 1001 := by')],
     r'unsolved goals\n⊢ False', 'max_skip_val'),
    ('spqr', 'one-claimed-two-in-the-continuation',
     [('      have h1 : (1#u64 : Std.U64).bv.toNat = 1 := by decide\n',
       '      have h1 : (1#u64 : Std.U64).bv.toNat = 2 := by decide\n')],
     r'Tactic `decide` proved that the proposition\n  1#u64\.bv\.toNat = 2\nis false', 'receive_refines_continuation'),
    ('triple', 'combine-info-byte-changed',
     [label('combine_info_agrees', ('COMBINE_INFO', 'Model.TripleRatchet.combineInfo'))],
     rfl_marker('Model.TripleRatchet.combineInfo'), 'combine_info_agrees'),
    ('triple', 'split-info-byte-changed',
     [label('split_info_agrees', ('SPLIT_INFO', 'Model.TripleRatchet.splitInfo'))],
     rfl_marker('Model.TripleRatchet.splitInfo'), 'split_info_agrees'),
    ('roundtrip', 'message-claimed-to-fit-42-bytes',
     [(f'    decide ({MESSAGE}.toByteArray.size ≤ U32.max) = true := by',
       f'    decide ({MESSAGE}.toByteArray.size ≤ U32.max / 100000000) = true := by')],
     r'Tactic `decide` proved that the proposition\n  "the size arithmetic above drifted from the encoding"\.utf8ByteSize ≤'
     r'[\s\S]*\nis false', 'export_message_fits'),
    ('spqr-pinned', 'native-decide-restored-under-the-pin',
     [(PROTOCOL, PROTOCOL.replace('  simp [sliceOf, PROTOCOL_INFO]; rfl\n', '  native_decide\n'))],
     r'Docstring on `#guard_msgs` does not match generated message:[\s\S]*\n\+ +'
     r'Tacenta\.SessionUnitSpqrT3\.protocol_info_agrees\._native\.native_decide\.ax_1_1',
     ('pin', 'Tacenta.SessionUnitSpqrT3.protocol_info_agrees')),
]

NOT_A_REFUSAL = ('unknown identifier', 'unknown constant', 'unexpected token', "expected '",
                 'unknown namespace', 'does not contain')
TIMEOUT = ('timeout', 'maxheartbeats', 'heartbeats', 'deterministic')

# Lean capitalises its error messages (`Unknown identifier`) and the kernel does not (`(kernel) unknown constant`), so
# the guards are matched case-insensitively, on the first line of each error, where Lean names the kind of failure.
ERROR_HEAD = re.compile(r'^\S+\.lean:(\d+):\d+: error(?:\([^)]*\))?: (.*)$', re.M)
MESSAGE_HEAD = re.compile(r'^\S+\.lean:\d+:\d+: (?:error|warning|info)', re.M)


def error_blocks(output):
    """Each error as (line, first line, whole text up to the next message)."""
    heads = list(MESSAGE_HEAD.finditer(output))
    blocks = []
    for k, m in enumerate(heads):
        end = heads[k + 1].start() if k + 1 < len(heads) else len(output)
        text = output[m.start():end]
        e = ERROR_HEAD.match(text)
        if e:
            blocks.append((int(e.group(1)), e.group(2), text))
    return blocks


def not_a_refusal(output, guards):
    return any(bad in head.lower() for _, head, _ in error_blocks(output) for bad in guards)


def is_timeout(head):
    return any(t in head.lower() for t in TIMEOUT)


def self_test():
    """The guards must fire on the toolchain's own spellings, and only there."""
    unknown_id = ("/tmp/x.lean:3:8: error(lean.unknownIdentifier): Unknown identifier `fooBar`\n"
                  "/tmp/x.lean:4:2: error: unsolved goals\n")
    unknown_const = "/tmp/x.lean:9:0: error: (kernel) unknown constant 'Foo.bar'\n"
    ordinary = "/tmp/x.lean:4:2: error: unsolved goals\n⊢ False\n"
    timeout = ("/tmp/x.lean:5:2: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has "
               "been reached\n⊢ False\n")
    if not not_a_refusal(unknown_id, NOT_A_REFUSAL):
        raise SystemExit('GUARD BROKEN: the not-a-refusal guard does not fire on `Unknown identifier`')
    if not not_a_refusal(unknown_const, NOT_A_REFUSAL):
        raise SystemExit("GUARD BROKEN: the not-a-refusal guard does not fire on the kernel's `unknown constant`")
    if not_a_refusal(ordinary, NOT_A_REFUSAL):
        raise SystemExit('GUARD BROKEN: the not-a-refusal guard fires on an ordinary refusal')
    if not is_timeout(error_blocks(timeout)[0][1]) or is_timeout(error_blocks(ordinary)[0][1]):
        raise SystemExit('GUARD BROKEN: a heartbeat timeout is not told apart from an ordinary refusal')
    # A timeout at the named place whose text happens to match the marker is not the named refusal.
    at_place = ("/tmp/x.lean:2:2: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has "
                "been reached\n⊢ False\n")
    try:
        place_of('self-test', 1, at_place, r'⊢ False', 'x', 'theorem x : False := by\n  sorry\n', Path('/dev/null'))
    except SystemExit as e:
        if 'TIMEOUT' not in str(e):
            raise SystemExit(f'GUARD BROKEN: a timeout was refused for another reason: {e}')
    else:
        raise SystemExit('GUARD BROKEN: a timeout at the named place counted as the named refusal')


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


def without_pins(text):
    cut = text.find('\n/-! ## Pins')
    if cut >= 0:
        text = text[:cut] + '\n'
    if '#guard_msgs' in text:
        raise SystemExit('a copy meant to carry no pins still has a `#guard_msgs` block')
    return text


def pin_block(name):
    """The live axiom pin of `name` in the audit module, verbatim."""
    text = AUDIT.read_text()
    m = re.search(r'/--\ninfo: \'' + re.escape(name) + r'\' depends on axioms: [^\n]*\n-/\n#guard_msgs in\n'
                  r'#print axioms ' + re.escape(name) + r'\n', text)
    if not m:
        raise SystemExit(f'no one-line kernel-only pin of {name} in {AUDIT.name}')
    return m.group(0)


DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*'
                  r'(theorem|lemma|def|abbrev|structure|instance|inductive)\s+(\S+)')
COMMAND = re.compile(r'^(?:@\[|/--|/-!|#|theorem |lemma |def |abbrev |structure |instance |'
                     r'inductive |private |protected |noncomputable |set_option |attribute |open |'
                     r'namespace |section |end |variable )')


def declaration_lines(text, name):
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
    lines = text.split('\n')
    for k in range(1, len(lines)):
        if lines[k] == f'#print axioms {name}' and lines[k - 1].startswith('#guard_msgs'):
            return k
    return None


def place_of(name, status, output, marker, where, mutated, log):
    """Where Lean refused the control, if at its named place for the named reason; otherwise stop."""
    blocks = error_blocks(output)
    if status == 0 or not blocks:
        raise SystemExit(f'FAILED control {name}: Lean accepted it (exit {status}); {log}')
    if not_a_refusal(output, NOT_A_REFUSAL):
        raise SystemExit(f'FAILED control {name}: an error is of a kind that is not a refusal; {log}')
    if isinstance(where, tuple):
        line = pin_line(mutated, where[1])
        if line is None:
            raise SystemExit(f'FAILED control {name}: the copy has no pin of {where[1]}; {log}')
        span, label = (line, line), f'the pin of {where[1]}'
    else:
        span = declaration_lines(mutated, where)
        if span is None:
            raise SystemExit(f'Target changed for {name}: no declaration {where} in the copy')
        label = where
    first = min(blocks, key=lambda b: b[0])
    if not span[0] <= first[0] <= span[1]:
        raise SystemExit(f'FAILED control {name}: the first error is at line {first[0]}, outside {label} '
                         f'(lines {span[0]}-{span[1]}); {log}')
    at = [b for b in blocks if span[0] <= b[0] <= span[1]]
    named = [b for b in at if not is_timeout(b[1]) and re.search(marker, b[2])]
    if not named:
        if any(is_timeout(b[1]) for b in at):
            raise SystemExit(f'TIMEOUT (not a passing control): {name} timed out at {label}; {log}')
        raise SystemExit(f'FAILED control {name}: refused at {label}, but not with `{marker}`; {log}')
    return label


IDENTITY = f'''
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let some a := env.find? `{AXIOM} | throwError "no axiom {AXIOM}"
  let some b := env.find? `{FITS} | throwError "no theorem {FITS}"
  logInfo m!"same-type: {{a.type == b.type}}"
'''


def identity(text, tmp, logs, tag, timeout):
    path = tmp / f'identity_{tag}.lean'
    path.write_text(text + IDENTITY)
    status, output = run_lean(path, logs / f'identity_{tag}.log', timeout)
    m = re.findall(r'same-type: (true|false)', output)
    if status != 0 or len(m) != 1 or error_blocks(output):
        raise SystemExit(f'IDENTITY PROBE FAILED ({tag}): exit {status}; {logs / f"identity_{tag}.log"}')
    return m[0] == 'true'


def main():
    self_test()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=900)
    parser.add_argument('--jobs', type=int, default=4)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='discharge-native-decide-logs-'))
    logs.mkdir(parents=True, exist_ok=True)
    spqr, triple, roundtrip = SPQR.read_text(), TRIPLE.read_text(), ROUNDTRIP.read_text()
    if AXIOM not in roundtrip:
        raise SystemExit(f'{ROUNDTRIP.name} no longer names {AXIOM}; the identity check would compare the wrong axiom')
    sources = {
        'spqr': without_pins(spqr),
        'triple': without_pins(triple),
        'roundtrip': without_pins(roundtrip),
        'spqr-pinned': without_pins(spqr) + '\n' + pin_block('Tacenta.SessionUnitSpqrT3.protocol_info_agrees'),
    }
    results = {
        'sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in (SPQR, TRIPLE, ROUNDTRIP, AUDIT)},
        'accepted': [], 'rejected': {}, 'identity': {},
    }
    with tempfile.TemporaryDirectory(prefix='discharge-native-decide-controls-') as tmp:
        tmp = Path(tmp)

        def baseline(item):
            label, text = item
            path = tmp / f'baseline_{label.replace("-", "_")}.lean'
            path.write_text(text)
            status, output = run_lean(path, logs / f'baseline_{label}.log', args.timeout)
            if status or 'sorry' in output or error_blocks(output):
                raise SystemExit(f'BASELINE FAILED for the {label} copy; no mutation evidence: '
                                 f'{logs / f"baseline_{label}.log"}')
            return label

        with ThreadPoolExecutor(args.jobs) as pool:
            for label in pool.map(baseline, sources.items()):
                results['accepted'].append(label)
                print(f'PASS: the unmodified {label} copy is accepted', flush=True)

        def control(mutant):
            label, name, edits, marker, where = mutant
            source = sources[label]
            mutated = source
            for old, new in edits:
                found = mutated.count(old)
                if found != 1:
                    raise SystemExit(f'Target changed for {name}: expected 1 occurrence of the text in the '
                                     f'{label} copy, found {found}')
                mutated = mutated.replace(old, new, 1)
            assert mutated != source
            path = tmp / f'{label.replace("-", "_")}_{name.replace("-", "_")}.lean'
            path.write_text(mutated)
            log = logs / f'{label}_{name}.log'
            status, output = run_lean(path, log, args.timeout)
            return label, name, status, marker, place_of(name, status, output, marker, where, mutated, log)

        with ThreadPoolExecutor(args.jobs) as pool:
            for label, name, status, marker, place in pool.map(control, MUTANTS):
                results['rejected'][f'{label}/{name}'] = {'exit': status, 'marker': marker, 'at': place}
                print(f'PASS: {label}/{name} refused by Lean at {place}', flush=True)

        base = sources['roundtrip']
        if not identity(base, tmp, logs, 'unmodified', args.timeout):
            raise SystemExit(f'FAILED: {FITS} does not state the proposition of {AXIOM}')
        results['identity']['unmodified'] = True
        print(f'PASS: {FITS} states exactly the type of {AXIOM}', flush=True)
        stated = f'    decide ({MESSAGE}.toByteArray.size ≤ U32.max) = true := by'
        if base.count(stated) != 1:
            raise SystemExit(f'Target changed for the identity control: the statement of {FITS} moved')
        altered = base.replace(stated, stated.replace('drifted from the encoding', 'drifted from encoding'))
        if identity(altered, tmp, logs, 'message-word-dropped', args.timeout):
            raise SystemExit('FAILED control message-word-dropped: the identity check accepted a different message')
        results['identity']['message-word-dropped'] = False
        print('PASS: roundtrip/message-word-dropped refused by the identity check (same-type: false)', flush=True)
    (logs / 'result.json').write_text(json.dumps(results, indent=2) + '\n')
    print(f'{len(results["accepted"])} unmodified copies accepted, {len(results["rejected"])} changes refused at '
          f'their named places, 1 identity check held and 1 refused; logs: {logs}', flush=True)


if __name__ == '__main__':
    sys.exit(main())
