#!/usr/bin/env bash
# Hold `check-audit-reach.sh` to a module the audit never walks and to the audit's own call.
#
# The axiom audit refuses an axiom, an opaque, an `unsafe`, `partial` or `implemented_by` declaration, but
# only in the environment of the module that runs it, and each package's audit module carries a hand-kept
# import list. `check-audit-reach.sh` fails when a first-party module is outside that closure, or when an
# audit is called with other prefixes or in a form it cannot read. Until now it had one recorded one-off run
# (`GATE-MUTATION-RECORD.md`) and no retained case.
#
# Each case plants one change in a disposable worktree of the commit under test, with the three packages'
# build directories (`.lake`) linked in from the checkout so that `lake env` and `lean --deps` resolve every
# import, and requires the script to refuse with the reason that change should give:
#
#   an orphan module, in each of the four source directories the script reads
#   an import dropped from an audit module, so a generated module it reached is left out
#   a deleted audit module
#   an audit called with other prefixes, called in a parenthesised form, called twice, and not called
#
# and first requires the unchanged tree to be accepted. Needs the three packages built (`no-sorry.sh` runs
# this after its builds). The caller's tree is not touched; what is tested is the committed tree.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
for package in tacenta-model tacenta-proofs tacenta-proofs/translation; do
  [ -d "$root/$package/.lake/build" ] \
    || { echo "audit-reach negatives: $package is not built; run the builds first" >&2; exit 1; }
done
work="$(mktemp -d)"
cleanup() { git -C "$root" worktree remove --force "$work/tree" >/dev/null 2>&1 || true; rm -rf "$work"; }
trap cleanup EXIT
git -C "$root" worktree add -q --detach "$work/tree" HEAD >/dev/null
tree="$work/tree"
for package in tacenta-model tacenta-proofs tacenta-proofs/translation; do
  ln -s "$root/$package/.lake" "$tree/$package/.lake"
done
t=tacenta-proofs/translation/Translation
cases=0

reset() { git -C "$tree" reset -q --hard HEAD && git -C "$tree" clean -fdq -e .lake; }

run_reach() {
  set +e
  out="$(cd "$tree" && bash tacenta-proofs/scripts/check-audit-reach.sh 2>&1)"
  rc=$?
  set -e
}

refuse() {  # name needle...: every needle must be in the refusal
  local name="$1" needle
  shift
  run_reach
  cases=$((cases + 1))
  if [ "$rc" -eq 0 ]; then
    echo "audit-reach negative $name: the script accepted the change" >&2
    exit 1
  fi
  for needle in "$@"; do
    if ! grep -qF -- "$needle" <<<"$out"; then
      echo "audit-reach negative $name: refused, but without '$needle':" >&2
      printf '%s\n' "$out" | head -20 >&2
      exit 1
    fi
  done
}

# once <file> <old> <new>: replace a text that occurs exactly once.
once() {
  python3 - "$tree/$1" "$2" "$3" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
if text.count(sys.argv[2]) != 1:
    raise SystemExit(f"control: {sys.argv[2]!r} occurs {text.count(sys.argv[2])} times in {path}")
path.write_text(text.replace(sys.argv[2], sys.argv[3]))
PY
}

run_reach
cases=$((cases + 1))
if [ "$rc" -ne 0 ]; then
  echo "audit-reach negative baseline: the unchanged tree was refused" >&2
  printf '%s\n' "$out" | head -20 >&2
  exit 1
fi

# An orphan in each directory the script reads: nothing imports it, so no audit walks it.
for orphan in tacenta-model/Model tacenta-model/Properties tacenta-proofs/Proofs "$t"; do
  reset
  : > "$tree/$orphan/GateControlOrphan.lean"
  module="$(printf '%s' "${orphan#tacenta-proofs/translation/}" | sed 's|^tacenta-model/||; s|^tacenta-proofs/||; s|/|.|g').GateControlOrphan"
  refuse "an orphan module in $orphan" 'outside the import closure' "$module"
done

# A module an audit reached, left out: the lifecycle audit's only import is the generated lifecycle module.
reset
once "$t/AxiomAuditLifecycle.lean" 'import Translation.TacentaLifecycle' ''
refuse 'an audit that no longer imports the lifecycle translation' 'outside the import closure' 'Translation.TacentaLifecycle'

# A deleted audit module: what it reached is no longer walked.
reset
git -C "$tree" rm -q "$t/AxiomAuditLifecycle.lean"
refuse 'a deleted audit module' 'outside the import closure' 'Translation.TacentaLifecycle'

# The audit's call.
call='run_cmd Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation]'
reset
once "$t/AxiomAuditLifecycle.lean" "$call" 'run_cmd Model.AxiomAudit.run #[`Model, `Properties, `Proofs]'
refuse 'an audit called with fewer prefixes' 'the audit runs with prefixes'
reset
once "$t/AxiomAuditLifecycle.lean" "$call" 'run_cmd (Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation])'
refuse 'an audit called in a parenthesised form' 'mentions Model.AxiomAudit.run 1 time(s) but only 0 are a plain'
# One plain call and one in another form in the same module: the second is a mention the plain pattern does not
# read, and an audit that is called twice is not called once.
reset
once "$t/AxiomAuditLifecycle.lean" "$call" "$call"$'\n''run_cmd (Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation])'
refuse 'an audit called once plainly and once in another form' 'mentions Model.AxiomAudit.run 2 time(s) but only 1 are a plain'
reset
once "$t/AxiomAuditLifecycle.lean" "$call" ''
refuse 'an audit module that does not call the audit' 'expected exactly one `run_cmd Model.AxiomAudit.run` line, found 0'
reset
once "$t/AxiomAuditLifecycle.lean" "$call" "$call"$'\n'"$call"
refuse 'an audit called twice' 'expected exactly one `run_cmd Model.AxiomAudit.run` line, found 2'

echo "audit-reach negatives: $cases cases (an orphan in each source directory, an import dropped, a deleted audit module, and five wrong audit calls) gave the expected result"
