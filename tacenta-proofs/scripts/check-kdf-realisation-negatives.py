#!/usr/bin/env python3
"""Hold `UnitLifecycleKdf` against planted faults.

`Translation/UnitLifecycleKdf.lean`: The Session unit's HMAC-SHA256 and HKDF-SHA256, now translated from the copied bodies of tacenta-kdf, return and equal tacenta-model's: HmacAgrees and HkdfAgrees as theorems, the KDF propositions the lifecycle results take, and decrypt_ratchet's complete refinement without them.

The module states tacenta-core's `HmacAgrees` and `HkdfAgrees` as theorems about the Session unit's translated
KDF (`hmacAgrees`, `hkdfAgrees`, each composing the copied T3 specification with the model bridge), derives the
other KDF propositions the unit's results take from them, builds `decrypt_ratchet`'s agreement record without its
KDF fields (`DecryptRatchetAgreements.of_kdf`) and states the complete refinement that way
(`decrypt_ratchet_refines_complete_of_kdf`).  This script plants 8 faults:

- labelled inside a composing proof (`INSIDE`): HKDF's bound moved to 8161 bytes, refused in `hkdfAgrees`; HMAC's
  output read backwards, refused in `hmacAgrees`.  2 controls are labelled inside.
- the composing proof copied, word for word, under a changed statement beside the original (so that the
  theorems using the original are not disturbed): HKDF's salt and input keying material exchanged on the
  model's side, refused in `hkdfAgrees_salt_ikm_swapped`; HMAC's key and message exchanged, refused in
  `hmacAgrees_key_data_swapped`.
- statement-shape (`STATEMENT_SHAPE`): the Session leaf's HKDF totality claimed at 8161 bytes, refused in
  `sessionHkdfTotal`, which projects `hkdfAgrees`, and still refused with `hkdfAgrees`'s proof emptied.  1
  control is statement-shape.
- the record's `kemClone` field given another field's type, refused in `DecryptRatchetAgreements.of_kdf`; the
  corollary's trace premise weakened to an empty trace, refused in `decrypt_ratchet_refines_complete_of_kdf`,
  which passes it to the complete refinement.
- the definition held by its pin: the record given an extra field with the pins kept, refused at the `#print`
  pin of `KdfFreeAgreements`.

What it does not hold: the copied `Kdf*` proofs themselves (a change to the copied Rust is a re-translation, which
these copies of one module cannot make; the source implementation's own proof mutants are not re-run here), and
the translation's fidelity.

A proof that Lean accepts after the fact it rests on is removed would hold nothing, so this script makes one
change to a copy of the module and requires Lean to refuse it, at a named place, with an error that names what
the change removed.  Each control labelled inside a composing proof is also run with that theorem's proof
replaced by `sorry`, and Lean must accept the change there, so the refusal is attributable to that proof.  Each
statement-shape check is run again with the projected theorem's proof replaced by `sorry`, and Lean must still
refuse it at its named place.  The labels are held consistent (an inside control must be labelled with the
declaration it is refused in and with a composing theorem; a control cannot be labelled both inside and
statement-shape; a statement-shape check may not be refused in a composing theorem) at start-up and again at
run time.  That a labelled control is refused by a composing step rather than by a projection, and that the
theorems named in `COMPOSING` compose rather than project, is decided by reading.

Every change is to a statement or a definition; none replaces a proof step.  Each refusal is a proof-breakage
check at a named place: it shows that the proof there depends on what the change removed (or, for a definition
kept with its pins, that the pin holds the definition), not that the changed statement is false.

The changes are checked on a copy without the module's pins, so that the refusal comes from a proof and not
from a pin, except those kept with their pins.  The unmodified copies must be accepted first.  A compiler that
does not start, a syntax error, an unrelated failure and a refusal elsewhere than the named place never count:
the named refusal must be an error at the named place that matches the expected message.  An error whose first
line names a kind of failure that is not a refusal (an unresolved name, a syntax error) voids the run anywhere in
the copy, compared without regard to case.  A timeout (heartbeat or deterministic) never counts as the named
refusal; one elsewhere in the copy is logged in the result and does not void a separate matching error at the
named place.  The script checks at start that the guard fires on the toolchain's own `Unknown identifier` and on
the kernel's `unknown constant` and not on an ordinary refusal, and that a heartbeat timeout is told apart from
a refusal.  These are controls on copies of the Lean; no source, olean or git state changes.

Dependencies must be built (`lake build Translation.KdfT3Kdf`).
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
MODULE = ROOT / 'translation/Translation/UnitLifecycleKdf.lean'

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`)
HMAC_HEAD = 'theorem hmacAgrees : Tacenta.SessionUnitT3.HmacAgrees := by\n'
HKDF_HEAD = 'theorem hkdfAgrees : Tacenta.SessionUnitT3.HkdfAgrees := by\n'
SESSION_TOTAL_HEAD = 'theorem sessionHkdfTotal : Tacenta.SessionUnitSessionT1.HkdfTotal := by\n'


def hmac_stated(conclusion):
    """`hmacAgrees` with its statement written out and its conclusion replaced."""
    return ('theorem hmacAgrees : ∀ (key data : Slice Std.U8), ∃ r, tacenta_kdf.hmac_sha256 key data = ok r ∧\n'
            f'    {conclusion} := by\n')


def hkdf_stated(bound, conclusion):
    """`hkdfAgrees` with its statement written out, its bound and its conclusion replaced."""
    return ('theorem hkdfAgrees : ∀ (N : Usize) (key salt info : Slice Std.U8), '
            f'N.val ≤ {bound} → ∃ r,\n'
            '    tacenta_kdf.hkdf_sha256 N key salt info = ok r ∧\n'
            f'    {conclusion} := by\n')


KEY = 'Tacenta.SessionUnitT3.keyOf r'


def beside(head, name, statement):
    """The theorem that starts at `head`, unchanged, followed by a copy of it named `name` whose statement is
    `statement` (written as `hmac_stated`/`hkdf_stated` write it) and whose proof is the original's, word for
    word.  The changed statement is refused where the copy's proof breaks; the original stays, so the
    theorems that use it are not disturbed and no refusal reaches them."""
    text = MODULE.read_text()
    start = text.index(head)
    end = text.index('\n\n', start) + 1
    block = text[start:end]
    proof = block[len(head):]
    copy = statement.replace('theorem hmacAgrees :', f'theorem {name} :').replace(
        'theorem hkdfAgrees :', f'theorem {name} :')
    return block, block + '\n' + copy + proof

SL = 'Tacenta.SessionUnitT3.sliceOf'

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
    # HKDF's bound moved past RFC 5869's 8160 bytes: the copied Rust panics at 8161, and the T3 specification
    # it composes asks for the bound.
    ('module', 'hkdf-bound-8161',
     [(HKDF_HEAD, hkdf_stated(8161, f'{KEY} = Model.Kdf.hkdf ({SL} key) ({SL} salt) ({SL} info) N.val'))],
     r'type mismatch', ['hkdfAgrees']),
    # HKDF's salt and input keying material exchanged on the model's side.
    # Both are copies of the composing proof under the changed statement, beside the original (`beside`).
    ('module', 'hkdf-salt-ikm-swapped',
     [beside(HKDF_HEAD, 'hkdfAgrees_salt_ikm_swapped',
             hkdf_stated(8160, f'{KEY} = Model.Kdf.hkdf ({SL} salt) ({SL} key) ({SL} info) N.val'))],
     r'unsolved goals', ['hkdfAgrees_salt_ikm_swapped']),
    # HMAC's key and message exchanged on the model's side.
    ('module', 'hmac-key-data-swapped',
     [beside(HMAC_HEAD, 'hmacAgrees_key_data_swapped',
             hmac_stated(f'{KEY} = Model.Kdf.hmac ({SL} data) ({SL} key)'))],
     r'unsolved goals', ['hmacAgrees_key_data_swapped']),
    # HMAC's output read backwards.
    ('module', 'hmac-output-reversed',
     [(HMAC_HEAD, hmac_stated(f'({KEY}).reverse = Model.Kdf.hmac ({SL} key) ({SL} data)'))],
     r'unsolved goals', ['hmacAgrees']),
    # The Session leaf's totality claimed one byte past the bound: refused where it projects `hkdfAgrees`,
    # whatever that theorem's proof is.
    ('module', 'session-total-bound-8161',
     [(SESSION_TOTAL_HEAD,
       'theorem sessionHkdfTotal : ∀ (N : Usize) (salt ikm info : Slice Std.U8), N.val ≤ 8161 →\n'
       '    ∃ r, tacenta_kdf.hkdf_sha256 N salt ikm info = ok r := by\n')],
     r'type mismatch', ['sessionHkdfTotal']),
    # The record's `kemClone` field given another field's type: the record no longer supplies what
    # `DecryptRatchetAgreements` asks.
    ('module', 'kdf-free-record-wrong-field',
     [('  kemClone : Tacenta.SessionUnitBraidT3.KemCloneAgrees\n',
       '  kemClone : Tacenta.SessionUnitBraidT3.ValidateEkAgrees K\n')],
     r'type mismatch', ['DecryptRatchetAgreements.of_kdf']),
    # The corollary's trace premise weakened to an empty trace: the complete refinement it composes asks for
    # the oracle's draws.
    ('module', 'corollary-trace-emptied',
     [('    (htrace : trace rng = oracle.draws)\n', '    (htrace : trace rng = [])\n')],
     r'type mismatch', ['decrypt_ratchet_refines_complete_of_kdf']),
    # The record gains a field, with its pins kept: the `#print` pin holds the definition.
    ('pinned', 'kdf-free-record-gains-a-field',
     [('  zeroizing32 : ZeroizingRoundTrips (Array Std.U8 32#usize)\n',
       '  zeroizing32 : ZeroizingRoundTrips (Array Std.U8 32#usize)\n  extra : True\n')],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleKdf.KdfFreeAgreements')),
]

# The theorems that compose the run (decided by reading): the two that compose the copied T3 specifications
# with the model bridge, and the corollary that composes the complete refinement with the record built from
# them.
COMPOSING = {'hmacAgrees', 'hkdfAgrees', 'decrypt_ratchet_refines_complete_of_kdf'}

# The controls labelled inside a composing proof, with the declaration each is refused in.  For each, the script
# also runs the changed copy with that theorem's proof replaced by `sorry` and requires Lean to accept the change
# there: the refusal is attributable to that proof.
INSIDE = {
    'hkdf-bound-8161': 'hkdfAgrees',
    'hmac-output-reversed': 'hmacAgrees',
}

# The theorems a statement-shape check may project: the composing theorems and the runs the reaches apply.
PROJECTED = COMPOSING | set()

# The statement-shape checks, with the theorem each projects.  For each, the script also runs the changed copy
# with that theorem's proof replaced by `sorry` and requires Lean still to refuse the change at its named place:
# the refusal does not depend on the projected theorem's proof.
STATEMENT_SHAPE = {'session-total-bound-8161': 'hkdfAgrees'}


def check_labels():
    """The inside and statement-shape labels are consistent with each other and with where each control is
    refused."""
    if not MUTANTS:
        raise SystemExit('NO CONTROLS: MUTANTS is empty; a control with no planted change holds nothing')
    wheres = {name: where for _, name, _, _, where in MUTANTS}
    if len(wheres) != len(MUTANTS):
        raise SystemExit('LABELS BROKEN: two controls have one name')
    for name, decl in list(INSIDE.items()) + list(STATEMENT_SHAPE.items()):
        if name not in wheres:
            raise SystemExit(f'LABELS BROKEN: {name} is labelled but is not a control')
    both = set(INSIDE) & set(STATEMENT_SHAPE)
    if both:
        raise SystemExit(f'LABELS BROKEN: {", ".join(sorted(both))} labelled both inside and statement-shape')
    for name, decl in INSIDE.items():
        if isinstance(wheres[name], tuple) or decl not in wheres[name]:
            raise SystemExit(f'LABELS BROKEN: {name} is labelled inside {decl}, which is not where it is refused')
        if decl not in COMPOSING:
            raise SystemExit(f'LABELS BROKEN: {name} is labelled inside {decl}, which is not a composing proof')
    for name, decl in STATEMENT_SHAPE.items():
        if isinstance(wheres[name], tuple) or any(d in COMPOSING for d in wheres[name]):
            raise SystemExit(f'LABELS BROKEN: the statement-shape check {name} is refused in a composing proof')
        if decl not in PROJECTED:
            raise SystemExit(f'LABELS BROKEN: the statement-shape check {name} projects {decl}, which is not in '
                             f'PROJECTED')


NOT_A_REFUSAL = ('unknown identifier', 'unknown constant', 'unexpected token', "expected '",
                 'unknown namespace', 'does not contain')

# A timeout (a heartbeat or deterministic timeout) is never a refusal: it never counts as the named refusal, and
# one elsewhere in the copy is logged.  It does not void a run whose named refusal is a separate error at the
# named place that matches the expected message.
TIMEOUT = ('timeout', 'maxheartbeats', 'heartbeats', 'deterministic')


# Lean capitalises its error messages (`Unknown identifier`, `Unknown constant`, `Function expected`), so the
# guard is matched case-insensitively, on the first line of each error, where Lean names the kind of failure.
ERROR_HEAD = re.compile(r'^\S+\.lean:\d+:\d+: error(?:\([^)]*\))?: (.*)$', re.M)
MESSAGE = re.compile(r'^\S+\.lean:(\d+):\d+: (error|warning|info|information)(?:\([^)]*\))?: (.*)$', re.M)


def not_a_refusal(output, guards):
    """Whether an error of `output` is of a kind that is not a refusal (a name that does not resolve, a syntax
    error, ...), compared without regard to case."""
    heads = [head.lower() for head in ERROR_HEAD.findall(output)]
    return any(bad in head for head in heads for bad in guards)


def error_blocks(output):
    """Each error of `output` as (line, first line, whole text)."""
    found = list(MESSAGE.finditer(output))
    blocks = []
    for k, m in enumerate(found):
        end = found[k + 1].start() if k + 1 < len(found) else len(output)
        if m.group(2) == 'error':
            blocks.append((int(m.group(1)), m.group(3), output[m.start():end]))
    return blocks


def is_timeout(head):
    return any(t in head.lower() for t in TIMEOUT)


def guard_self_test(guards):
    """The guard must fire on the toolchain's own spelling of an unresolved name, and a timeout must be told
    apart from a refusal."""
    sample = ("/tmp/x.lean:3:8: error(lean.unknownIdentifier): Unknown identifier `fooBar`\n"
              "/tmp/x.lean:4:2: error: unsolved goals\n")
    if not not_a_refusal(sample, guards):
        raise SystemExit('GUARD BROKEN: the not-a-refusal guard does not fire on `Unknown identifier`')
    kernel = ("/tmp/x.lean:5:8: error: (kernel) unknown constant 'Foo.bar'\n"
              "/tmp/x.lean:6:2: error: unsolved goals\n")
    if not not_a_refusal(kernel, guards):
        raise SystemExit('GUARD BROKEN: the not-a-refusal guard does not fire on the kernel\'s `unknown constant`')
    if not_a_refusal("/tmp/x.lean:4:2: error: unsolved goals\n", guards):
        raise SystemExit('GUARD BROKEN: the not-a-refusal guard fires on an ordinary refusal')
    timeout = ("/tmp/x.lean:7:2: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) "
               "has been reached\nUse `set_option maxHeartbeats <num>` to set the limit.\n")
    blocks = error_blocks(timeout)
    if len(blocks) != 1 or not is_timeout(blocks[0][1]):
        raise SystemExit('GUARD BROKEN: a heartbeat timeout is not recognised as a timeout')
    if any(is_timeout(h) for _, h, _ in error_blocks("/tmp/x.lean:4:2: error: unsolved goals\nx : T\n")):
        raise SystemExit('GUARD BROKEN: an ordinary refusal is taken for a timeout')


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


def gutted(text, name):
    """`text` with the proof of the theorem `name` (from the line after its `:= by` to the next command)
    replaced by `sorry`."""
    span = declaration_lines(text, name)
    if span is None:
        raise SystemExit(f'no declaration {name} to empty')
    lines = text.split('\n')
    start = next((k for k in range(span[0] - 1, span[1]) if lines[k].rstrip().endswith(':= by')), None)
    if start is None:
        raise SystemExit(f'no tactic proof found in {name}')
    end = start + 1
    while end < len(lines) and not COMMAND.match(lines[end]):
        end += 1
    return '\n'.join(lines[:start + 1] + ['  sorry'] + lines[end:])


def check_inside(name, decl, status, output, log, emptied):
    """With the composing proof emptied, the change must not be refused there."""
    if 'declaration uses `sorry`' not in output:
        raise SystemExit(f'FAILED inside check {name}: the emptied copy did not elaborate to `sorry`; {log}')
    span = declaration_lines(emptied, decl)
    errors = {int(n) for n in ERROR_AT.findall(output)}
    if any(span[0] <= e <= span[1] for e in errors):
        raise SystemExit(f'FAILED inside check {name}: still refused in {decl} with its proof emptied, so the '
                         f'refusal is not the proof\'s; {log}')


def check_refused(name, status, output, marker, log, mutated, where):
    """Refused at the named place, by an error there that is not a timeout and that matches the expected
    message; an error that is not a refusal voids the run anywhere in the copy; a timeout elsewhere is returned
    for the log."""
    if status == 0 or not_a_refusal(output, NOT_A_REFUSAL):
        raise SystemExit(f'FAILED control {name}: expected Lean to refuse it with `{marker}`, '
                         f'exit={status}; {log}')
    blocks = error_blocks(output)
    if isinstance(where, tuple):
        line = pin_line(mutated, where[1])
        if line is None:
            raise SystemExit(f'FAILED control {name}: the copy has no `#print {where[1]}` pin, so '
                             f'its refusal cannot be the pin\'s; {log}')
        spans = [(where[1], (line, line))]
    else:
        spans = []
        for decl in where:
            span = declaration_lines(mutated, decl)
            if span is None:
                raise SystemExit(f'Target changed for {name}: no declaration {decl} in the copy')
            spans.append((decl, span))
    for decl, (lo, hi) in spans:
        if any(lo <= ln <= hi and not is_timeout(head) and re.search(marker, text) for ln, head, text in blocks):
            place = decl if not isinstance(where, tuple) else f'the pin of {where[1]}'
            timeouts = sorted(ln for ln, head, _ in blocks if is_timeout(head))
            return place, timeouts
    raise SystemExit(f'FAILED control {name}: no error at the named place ({", ".join(d for d, _ in spans)}) '
                     f'that is not a timeout matches `{marker}`; {log}')


def main():
    guard_self_test(NOT_A_REFUSAL)
    check_labels()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=900)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='kdf-realisation-logs-'))
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
    with tempfile.TemporaryDirectory(prefix='kdf-realisation-controls-') as tmp:
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
            place, timeouts = check_refused(name, status, output, marker, log, mutated, where)
            results['rejected'][f'{label}/{name}'] = {'exit': status, 'marker': marker, 'at': place}
            if timeouts:
                results['rejected'][f'{label}/{name}']['timeouts_elsewhere'] = timeouts
                print(f'NOTE: {label}/{name} also has a timeout at line(s) {timeouts}, not counted', flush=True)
            print(f'PASS: {label}/{name} refused by Lean in {place}', flush=True)
            if name in INSIDE:
                decl = INSIDE[name]
                if place != decl:
                    raise SystemExit(f'FAILED inside check {name}: refused in {place}, labelled inside {decl}; {log}')
                emptied = gutted(mutated, decl)
                epath = tmp / f'{label}_{name}_emptied.lean'
                epath.write_text(emptied)
                elog = logs / f'{label}_{name}_emptied.log'
                status, output = run_lean(epath, elog, args.timeout)
                check_inside(name, decl, status, output, elog, emptied)
                results['rejected'][f'{label}/{name}']['inside'] = decl
                print(f'PASS: {label}/{name} accepted in {decl} with its proof emptied', flush=True)
            if name in STATEMENT_SHAPE:
                decl = STATEMENT_SHAPE[name]
                emptied = gutted(mutated, decl)
                epath = tmp / f'{label}_{name}_projected_emptied.lean'
                epath.write_text(emptied)
                elog = logs / f'{label}_{name}_projected_emptied.log'
                status, output = run_lean(epath, elog, args.timeout)
                check_refused(name, status, output, marker, elog, emptied, where)
                results['rejected'][f'{label}/{name}']['projects'] = decl
                print(f'PASS: {label}/{name} still refused with the proof of {decl} emptied', flush=True)
    (logs / 'result.json').write_text(json.dumps(results, indent=2) + '\n')
    inside = sum(1 for r in results['rejected'].values() if 'inside' in r)
    shape = sum(1 for r in results['rejected'].values() if 'projects' in r)
    print(f'{len(results["accepted"])} unmodified copies accepted, {len(results["rejected"])} changes '
          f'refused at their named places, {inside} of them labelled inside a composing proof (accepted there '
          f'with that proof emptied) and {shape} labelled statement-shape (still refused with the projected '
          f'proof emptied); logs: {logs}', flush=True)


if __name__ == '__main__':
    sys.exit(main())
