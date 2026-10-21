#!/usr/bin/env python3
"""Hold the restored-session theorems against a planted fault.

`Translation/UnitLifecycleRestoredSession.lean` shows that every session `Session::import` accepts passes
`Session::invariant`, states `CounterHeadroom` at an accepted import as the decidable `headroomCheck`,
relates an accepted session in scope (`RestoredScope`: Braid in `KeysUnsampled` or `Failed`) to
`restoredModelOf`, and, with `UnitLifecycleSessionCodec.lean` and `UnitLifecycleSessionRoundTrip.lean`,
proves that `import` of `export` returns every established initiator session unchanged.  A proof that Lean
accepts after the fact it rests on is removed would hold nothing, so this script makes one change to a copy
of a module and requires Lean to refuse it, at a named place:

  * the invariant inversion, run against a copy of `import` with the `Inconsistent` refusal removed and
    with the proof adapted to that body (refused in `import_ok_gives_invariant`, the invariant goal left
    unsolved);
  * `headroomCheck` without its sparse-epoch clause, with the proof adapted to the shorter check (refused
    in `counterHeadroom_iff_check`, the sparse-epoch goal left unsolved);
  * `RestoredScope` widened to a `KeysSampled` Braid, which holds a fresh key pair and an encoder (refused in
    `sessionRefines_restored`);
  * the round trip concluding a session with one field altered, the associated data emptied (refused in
    `export_import_of_shape`);
  * the round trip without the `Vec::as_slice` law (refused in `export_import_of_shape`);
  * the classical ratchet encoding with two counters in the wrong order (refused in
    `ratchet_to_bytes_spec`);
  * the Braid epoch reader without the hypothesis that the epoch is not `u64::MAX`, which it refuses
    (refused in `read_epoch_of`, the goal `epoch ≠ u64::MAX` left unsolved);
  * `OptionBranchSomeShape` weakened to allow `Option::branch` on `Some x` to break, with the proof adapted
    to take both cases (refused in `lifecycle_take_len_prefixed_of`, the break cases left unsolved);
  * the established round trip's shape without the ciphertext length bound (refused in
    `codecShape_parts`);
  * the round-trip half of the joint model at an interpretation whose public-key reader ignores its bytes
    (refused in `restored_laws_model_established`, where that law's round trip fails);
  * `KemCiphertextLenBoundShape` with its bound dropped, with the module's pins kept (refused at the pin of
    `KemCiphertextLenBoundShape`);
  * the joint model of the composed premise list with its round-trip half at `Interp.model` and its decrypt
    half at `Interp.modelEstablished`, two interpretations, proved from `restored_laws_model`, with the
    module's pins kept (refused at the statement pin of `restored_decrypt_laws_model`).

The changes are checked on copies without the modules' pins, so that the refusal comes from a proof and not
from a pin, except the two kept with their pins.  The unmodified copies must be accepted first.  A timeout, a
compiler that does not start, a syntax error, an unrelated failure, a refusal elsewhere than the named
place and a refusal at the named place whose message does not match the control's reason never count.  An error whose first line names a kind of failure that is not a refusal (an
unresolved name, a syntax error) voids the run anywhere in the copy, compared without regard to case, and the
script checks at start that this guard fires on the toolchain's own `Unknown identifier`.  These are proof-dependency controls on copies of the Lean; no source, olean or git
state changes.

Dependencies must be built (`lake build Translation.UnitLifecycleRestoredSession`).
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
CODEC = ROOT / 'translation/Translation/UnitLifecycleSessionCodec.lean'
ROUNDTRIP = ROOT / 'translation/Translation/UnitLifecycleSessionRoundTrip.lean'
RESTORED = ROOT / 'translation/Translation/UnitLifecycleRestoredSession.lean'

PROOF = (r'unsolved goals|Application type mismatch|Type mismatch|type mismatch|omega could not prove'
         r'|made no progress|rcases|Insufficient number of fields|failed to prove|rewrite. failed'
         r'|The rfl tactic failed|rfl. failed|scalar_tac failed|simp failed|Tactic .* failed')

UNSOLVED = r'unsolved goals'

IMPORT_WITHOUT_CHECK = (
    '/-- `import` with the `Inconsistent` refusal removed (a planted fault). -/\n'
    'noncomputable def importWithoutInvariant (bytes : Slice Std.U8) :\n'
    '    Result (core.result.Result lifecycle.Session lifecycle.SessionDecodeError) := do\n'
    '  let r ← lifecycle.Session.import_unchecked bytes\n'
    '  let cf ← core.result.Result.Insts.CoreOpsTry.branch r\n'
    '  match cf with\n'
    '  | core.ops.control_flow.ControlFlow.Continue val =>\n'
    '    let z ← lifecycle.Session.export val\n'
    '    let v ← zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref (alloc.vec.Vec.Insts.ZeroizeZeroize\n'
    '      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) z\n'
    '    let s ← alloc.vec.Vec.as_slice Global v\n'
    '    let b ← core.cmp.impls.PartialEqShared.ne (Slice.Insts.CoreCmpPartialEqSlice\n'
    '      core.cmp.PartialEqU8) s bytes\n'
    '    if b then ok (core.result.Result.Err lifecycle.SessionDecodeError.NonCanonical)\n'
    '    else ok (core.result.Result.Ok val)\n'
    '  | core.ops.control_flow.ControlFlow.Break residual =>\n'
    '    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual\n'
    '      lifecycle.Session (core.convert.FromSame lifecycle.SessionDecodeError) residual\n\n'
    '/-- Every session `Session::import` accepts')

# (copy, name, [(pattern, replacement), ...], a regular expression the refused output must contain,
#  where the refusal must be: declarations one of whose lines holds an error, or ('pin', name) for the
#  `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
    ('restored', 'invariant-inversion-without-the-inconsistent-refusal',
     [(r'/-- \*\*Every session `Session::import` accepts', IMPORT_WITHOUT_CHECK + '**'),
      (r'    \(h : lifecycle\.Session\.import b = ok \(core\.result\.Result\.Ok s\)\) :\n'
       r'    lifecycle\.Session\.invariant s = ok true := by\n  unfold lifecycle\.Session\.import at h\n'
       r'((?:.*\n)*?)    split at h\n    · simp at h\n    · obtain ⟨b1, hb1, h⟩ := bind_eq_ok_inv h\n'
       r'      split at h\n      · simp only \[ok\.injEq, core\.result\.Result\.Ok\.injEq\] at h\n'
       r'        subst h\n        simp_all\n      · simp at h\n',
       '    (h : importWithoutInvariant b = ok (core.result.Result.Ok s)) :\n'
       '    lifecycle.Session.invariant s = ok true := by\n  unfold importWithoutInvariant at h\n'
       '  obtain ⟨r, -, h⟩ := bind_eq_ok_inv h\n'
       '  rcases r with val | e\n'
       '  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h\n'
       '    obtain ⟨z, -, h⟩ := bind_eq_ok_inv h\n'
       '    obtain ⟨v, -, h⟩ := bind_eq_ok_inv h\n'
       '    obtain ⟨sl, -, h⟩ := bind_eq_ok_inv h\n'
       '    obtain ⟨c, -, h⟩ := bind_eq_ok_inv h\n'
       '    split at h\n'
       '    · simp at h\n'
       '    · simp only [ok.injEq, core.result.Result.Ok.injEq] at h\n'
       '      subst h\n'
       '      try simp_all\n')],
     UNSOLVED + r'[^\n]*\n(?:.*\n)*?⊢ [^\n]*invariant[^\n]*= ok true', ['import_ok_gives_invariant']),
    ('restored', 'ceiling-check-without-the-sparse-epoch',
     [(r'  decide \(s\.triple\.post_quantum\.epoch\.val \+ 1 < Std\.U64\.max\) &&\n', ''),
      (r'    refine ⟨⟨⟨h1, h2⟩, \?_⟩, h4⟩\n', '    refine ⟨⟨h1, ?_⟩, h4⟩\n'),
      (r'    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h\n    refine ⟨h1, h2, \?_, h4⟩\n',
       '    obtain ⟨⟨h1, h3⟩, h4⟩ := h\n    refine ⟨h1, ?_, ?_, h4⟩\n'
       '    · try (first | omega | simp_all)\n')],
     UNSOLVED + r'[^\n]*\n(?:.*\n)*?⊢ [^\n]*post_quantum\.epoch', ['counterHeadroom_iff_check']),
    ('restored', 'scope-widened-to-a-sampled-braid',
     [(r'    s\.braid\.state = tacenta_braid\.State\.Failed\n\n',
       '    s.braid.state = tacenta_braid.State.Failed ∨\n'
       '    ∃ epoch auth ikp enc, s.braid.state = tacenta_braid.State.KeysSampled epoch auth ikp enc\n\n')],
     PROOF, ['sessionRefines_restored']),
    ('roundtrip', 'round-trip-with-the-associated-data-altered',
     [(r'      lifecycle\.Session\.import \(alloc\.vec\.Vec\.deref v\) = ok \(core\.result\.Result\.Ok s\) := by\n'
       r'  obtain ⟨hinvT, hinvB⟩',
       '      lifecycle.Session.import (alloc.vec.Vec.deref v) =\n'
       '        ok (core.result.Result.Ok { s with identity_ad := alloc.vec.Vec.new U8 }) := by\n'
       '  obtain ⟨hinvT, hinvB⟩')],
     PROOF, ['export_import_of_shape']),
    ('roundtrip', 'round-trip-without-the-as-slice-law',
     [(r'  have hsv : alloc\.vec\.Vec\.as_slice Global v = ok \(alloc\.vec\.Vec\.deref v\) := hsl v\n',
       '  have hsv : True := trivial\n')],
     PROOF, ['export_import_of_shape']),
    ('codec', 'ratchet-encoding-with-two-counters-swapped',
     [(r'\(be32 r\.ns \+\+ \(be32 r\.nr ', '(be32 r.nr ++ (be32 r.ns ')],
     PROOF, ['ratchet_to_bytes_spec']),
    ('codec', 'braid-epoch-reader-without-its-bound',
     [(r'    \(h : bytes\.val\.drop pos\.val = be64 epoch \+\+ rest\) \(hmax : epoch ≠ core\.num\.U64\.MAX\) :\n'
       r'    tacenta_braid\.read_epoch bytes pos = ok \(some epoch\) := by\n'
       r'  unfold tacenta_braid\.read_epoch\n  rw \[read_u64_of bytes pos epoch rest h\]\n  simp \[hmax\]\n',
       '    (h : bytes.val.drop pos.val = be64 epoch ++ rest) :\n'
       '    tacenta_braid.read_epoch bytes pos = ok (some epoch) := by\n'
       '  unfold tacenta_braid.read_epoch\n  rw [read_u64_of bytes pos epoch rest h]\n  simp\n'),
      (r'  rw \[read_epoch_of bytes pos epoch _ h hmax\]\n', '  rw [read_epoch_of bytes pos epoch _ h]\n')],
     UNSOLVED + r'[^\n]*\n(?:.*\n)*?⊢ [^\n]*U64\.rMax', ['read_epoch_of']),
    ('codec', 'option-branch-law-weakened',
     [(r'  ∀ \(T : Type\) \(x : T\), br \(some x\) = ok \(core\.ops\.control_flow\.ControlFlow\.Continue x\)\n',
       '  ∀ (T : Type) (x : T), br (some x) = ok (core.ops.control_flow.ControlFlow.Continue x) ∨\n'
       '    br (some x) = ok (core.ops.control_flow.ControlFlow.Break none)\n'),
      (r'    · simp only at ho; exact ⟨s, rfl, ho\.2\.1⟩\n  rw \[hbr\]\n',
       '    · simp only at ho; exact ⟨s, rfl, ho.2.1⟩\n  rcases hbr _ s with hb | hb <;> rw [hb]\n'),
      (r'    · simp only at ho1; exact ⟨e, rfl, ho1\.2\.1⟩\n  rw \[hbr\]\n',
       '    · simp only at ho1; exact ⟨e, rfl, ho1.2.1⟩\n  rcases hbr _ e with hb | hb <;> rw [hb]\n')],
     UNSOLVED + r'[^\n]*\n(?:.*\n)*?⊢ \(do\n\s+let cf1? ← ok \(core\.ops\.control_flow\.ControlFlow\.Break none\)',
     ['lifecycle_take_len_prefixed_of']),
    ('restored', 'established-shape-without-the-ciphertext-bound',
     [(r'  obtain ⟨n, hn, hnle⟩ := hbound\n',
       '  obtain ⟨n, hn, -⟩ := hbound\n  have hnle : True := trivial\n')],
     PROOF, ['codecShape_parts']),
    ('restored', 'joint-model-with-a-public-key-reader-that-drops-the-key',
     [(r'/-- \*\*The six laws of the round trip hold at the interpretation the decrypt joint model uses\*\*',
       '/-- `Interp.modelEstablished` with a public-key reader that ignores its bytes (a planted fault). -/\n'
       'noncomputable def modelFaulty : Tacenta.UnitSatisfiabilityJoint.Interp :=\n'
       '  { Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished with\n'
       '    dhPubFromBytes := fun _ => ok Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32 }\n\n'
       '/-- **The six laws of the round trip hold at the interpretation the decrypt joint model uses**'),
      (r'      DhPublicBytesRoundTripShape Tacenta\.UnitLifecycleEstablishedDecrypt\.Interp\.modelEstablished ∧\n'
       r'      OptionBranchSomeShape @optionBranchImpl ∧ VecAsSliceShape @vecAsSliceImpl ∧\n'
       r'      KemCiphertextLenBoundShape \(ok 0#usize\) :=\n',
       '      DhPublicBytesRoundTripShape modelFaulty ∧\n'
       '      OptionBranchSomeShape @optionBranchImpl ∧ VecAsSliceShape @vecAsSliceImpl ∧\n'
       '      KemCiphertextLenBoundShape (ok 0#usize) :=\n')],
     r'[Tt]ype mismatch(?:.*\n)*?.*expected to have type\n\s+modelFaulty\.dhPubFromBytes \S+ = ok ',
     ['restored_laws_model_established']),
    ('restoredpinned', 'ciphertext-bound-law-without-its-bound-pinned',
     [(r'  ∃ n : Usize, ciphertextLen = ok n ∧ n\.val ≤ 65536\n', '  ∃ n : Usize, ciphertextLen = ok n\n'),
      (r'  ⟨0#usize, rfl, by simp⟩\n', '  ⟨0#usize, rfl⟩\n'),
      (r'  obtain ⟨n, hn, hnle⟩ := hbound\n',
       '  obtain ⟨n, hn⟩ := hbound\n  have hnle : n.val ≤ 65536 := sorry\n')],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape')),
    ('restoredpinned', 'joint-model-at-two-interpretations-pinned',
     [(r'    \(ZeroizingVecRoundTripShape Tacenta\.UnitLifecycleEstablishedDecrypt\.Interp\.modelEstablished ∧\n'
       r'      DhPrivateBytesRoundTripShape Tacenta\.UnitLifecycleEstablishedDecrypt\.Interp\.modelEstablished ∧\n'
       r'      DhPublicBytesRoundTripShape Tacenta\.UnitLifecycleEstablishedDecrypt\.Interp\.modelEstablished ∧\n'
       r'      OptionBranchSomeShape @optionBranchImpl ∧ VecAsSliceShape @vecAsSliceImpl ∧\n'
       r'      KemCiphertextLenBoundShape \(ok 0#usize\)\) :=\n'
       r'  ⟨established_decrypt_laws_model, restored_laws_model_established⟩\n',
       '    (ZeroizingVecRoundTripShape Interp.model ∧ DhPrivateBytesRoundTripShape Interp.model ∧\n'
       '      DhPublicBytesRoundTripShape Interp.model ∧\n'
       '      OptionBranchSomeShape @optionBranchImpl ∧ VecAsSliceShape @vecAsSliceImpl ∧\n'
       '      KemCiphertextLenBoundShape (ok 0#usize)) :=\n'
       '  ⟨established_decrypt_laws_model, restored_laws_model.1, restored_laws_model.2.1,\n'
       '    restored_laws_model.2.2.1, restored_laws_model.2.2.2.1, restored_laws_model.2.2.2.2.1,\n'
       '    restored_laws_model.2.2.2.2.2.1⟩\n')],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleRestoredSession.restored_decrypt_laws_model')),
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
               and not not_a_refusal(output, NOT_A_REFUSAL))
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
    guard_self_test(NOT_A_REFUSAL)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=900)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='restored-logs-'))
    logs.mkdir(parents=True, exist_ok=True)
    codec = CODEC.read_text()
    roundtrip = ROUNDTRIP.read_text()
    restored = RESTORED.read_text()
    sources = {
        'codec': without_pins(codec, CODEC),
        'roundtrip': without_pins(roundtrip, ROUNDTRIP),
        'restored': without_pins(restored, RESTORED),
        'restoredpinned': restored,
    }
    results = {
        'codec_sha256': hashlib.sha256(codec.encode()).hexdigest(),
        'roundtrip_sha256': hashlib.sha256(roundtrip.encode()).hexdigest(),
        'restored_sha256': hashlib.sha256(restored.encode()).hexdigest(),
        'accepted': [], 'rejected': {},
    }
    with tempfile.TemporaryDirectory(prefix='restored-controls-') as tmp:
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
