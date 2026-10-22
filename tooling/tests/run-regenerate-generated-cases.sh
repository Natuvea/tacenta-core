#!/usr/bin/env bash
# Negative controls for tooling/regenerate-generated.sh and tooling/resolve-insertion-conflicts.py, which it runs
# first, on a disposable clone of the commit under test.
#
#   a merge that leaves a hand-written file unmerged          refused, nothing written
#   a conflict marker in a tracked hand-written file          refused, nothing written
#   the attestation negatives' case count unmerged            refused without --count
#   a line both sides changed in a shared list               the resolver refuses, nothing written
#   two insertions at one place that share a line             the resolver refuses, nothing written
#   two branches that each scaffold a module sorting after    every shared list and the generated inventory
#     the same entries, merged (with merge.conflictStyle      conflict; the script resolves the insertions,
#     diff3 set, which the resolver does not depend on)       writes the generated files again, stages them,
#                                                             and every check it runs passes, both modules wired
#   a branch built on another, merging main after main        the resolver keeps the shared module's entries
#     squash-merged the other                                 once and adds the branch's own; --verify passes
#   an entry planted twice, an evidence line repeated         --verify names it
#   one prose line edited on one side, one clause edited      the resolver refuses
#   a closing fi alone on one side, a block on the other     resolved with both, or refused; never a file that
#                                                             does not parse
#
# What this does not show: that the generators are right. Each has its own controls; this holds the script
# that runs them after a merge.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
work="$(mktemp -d "${TMPDIR:-/tmp}/regenerate-cases.XXXXXX")"
trap 'rm -rf "$work"' EXIT
cases=0
out=""
clone="$work/clone"
git clone -q --shared --no-checkout "$root" "$clone"
git -C "$clone" checkout -q --detach "$(git -C "$root" rev-parse HEAD)"
g() { git -C "$clone" -c user.name=control -c user.email=control@example.invalid "$@"; }
base="$(g rev-parse HEAD)"

fail_case() {
  echo "WRONG  regenerate-generated $1" >&2
  shift
  [ $# -eq 0 ] || printf '%s\n' "$@" >&2
  exit 1
}
reset() { g merge --abort >/dev/null 2>&1 || true; g reset -q --hard "$base"; g clean -fdq; }
run() {  # name want-exit needle [args]
  local name="$1" want="$2" needle="$3" rc
  shift 3
  set +e
  out="$(cd "$clone" && bash tooling/regenerate-generated.sh "$@" 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if { [ "$want" = 0 ] && [ "$rc" -ne 0 ]; } || { [ "$want" != 0 ] && [ "$rc" -eq 0 ]; } \
     || ! grep -qF -- "$needle" <<<"$out"; then
    fail_case "$name: expected exit $want and '$needle', got exit $rc" "$out"
  fi
}
untouched() {  # name: no generated file was written
  cases=$((cases + 1))
  local diff
  diff="$(g diff --name-only HEAD -- tacenta-proofs/GATE-INVENTORY.md tacenta-proofs/manifests tooling/required-steps.json \
    | grep -v '^tacenta-proofs/scripts/attest-negatives-case-count.txt$' || true)"
  [ -z "$diff" ] || fail_case "$1: a generated file was written: $diff"
}
# branch <file> <python program over text t> <message>: commit an edit on a detached branch from base, print it
branch() {
  g checkout -q --detach "$base"
  python3 - "$clone/$1" "$2" <<'PY'
import sys
path, program = sys.argv[1:]
t = open(path).read()
exec(program)
open(path, "w").write(t)
PY
  g commit -q -am "$3"
  g rev-parse HEAD
}

# A hand-written file left unmerged.
a="$(branch CONTRIBUTING.md "t = t.replace('# Contributing', '# Contributing to this repository', 1)" a)"
b="$(branch CONTRIBUTING.md "t = t.replace('# Contributing', '# How to contribute', 1)" b)"
g checkout -q --detach "$a"
g merge -q --no-edit "$b" >/dev/null 2>&1 && fail_case "hand-unmerged: the fixture merge did not conflict"
git -C "$clone" show "$a:CONTRIBUTING.md" > "$clone/CONTRIBUTING.md"
run hand-unmerged-without-markers 1 "unmerged files that are not generated: CONTRIBUTING.md"
g checkout -m -- CONTRIBUTING.md
run hand-unmerged 1 "unmerged files that are not generated: CONTRIBUTING.md"
untouched hand-unmerged
reset

# A conflict marker committed or left in a tracked hand-written file.
printf '<<<<<<< ours\n' >> "$clone/CONTRIBUTING.md"
run hand-marker 1 "conflict markers in files that are not generated: CONTRIBUTING.md"
untouched hand-marker
reset

# The case count unmerged.
a="$(branch tacenta-proofs/scripts/attest-negatives-case-count.txt "t = str(int(t) + 1) + '\n'" a)"
b="$(branch tacenta-proofs/scripts/attest-negatives-case-count.txt "t = str(int(t) + 2) + '\n'" b)"
g checkout -q --detach "$a"
g merge -q --no-edit "$b" >/dev/null 2>&1 && fail_case "count-unmerged: the fixture merge did not conflict"
# Its markers removed by taking one side, but left unmerged, it is refused; with its markers, too.
git -C "$clone" show "$a:tacenta-proofs/scripts/attest-negatives-case-count.txt" > "$clone/tacenta-proofs/scripts/attest-negatives-case-count.txt"
run count-unmerged-without-markers 1 "the attestation negatives' case count is unmerged; run with --count"
g checkout -m -- tacenta-proofs/scripts/attest-negatives-case-count.txt
run count-unmerged 1 "the attestation negatives' case count is unmerged; run with --count"
untouched count-unmerged
reset

# A line both sides changed in a shared wiring file is left unmerged, and the run refused.
a="$(branch tacenta-proofs/scripts/no-sorry-parts.txt "t = t.replace('  repair\n', '  repair-a\n', 1)" a)"
b="$(branch tacenta-proofs/scripts/no-sorry-parts.txt "t = t.replace('  repair\n', '  repair-b\n', 1)" b)"
g checkout -q --detach "$a"
g merge -q --no-edit "$b" >/dev/null 2>&1 && fail_case "both-changed: the fixture merge did not conflict"
run both-changed 1 "REFUSED: tacenta-proofs/scripts/no-sorry-parts.txt: a conflict at line"
says_also() { cases=$((cases + 1)); grep -qF -- "$2" <<<"$out" || fail_case "$1: expected '$2'" "$out"; }
says_also both-changed "nothing was written; 1 file(s) need a hand resolution"
untouched both-changed
reset

# Two insertions at one place that share a line are refused.
a="$(branch tacenta-proofs/scripts/no-sorry-parts.txt "t = t.replace('  responder-receipt\n', '  responder-receipt\n  aa\n  bb\n', 1)" a)"
b="$(branch tacenta-proofs/scripts/no-sorry-parts.txt "t = t.replace('  responder-receipt\n', '  responder-receipt\n  bb\n  cc\n', 1)" b)"
g checkout -q --detach "$a"
g merge -q --no-edit "$b" >/dev/null 2>&1 && fail_case "overlapping: the fixture merge did not conflict"
run overlapping 1 "the two insertions at line"
says_also overlapping "share a line: 'bb'"
untouched overlapping
reset

# An entry planted twice is named by --verify.
resolver_out() { set +e; out="$(cd "$clone" && python3 tooling/resolve-insertion-conflicts.py "$@" 2>&1)"; rc=$?; set -e; }
python3 - "$clone/tacenta-proofs/translation/Translation/AxiomAuditSessionUnit.lean" <<'PY'
import sys
p = sys.argv[1]; t = open(p).read()
open(p, "w").write(t.replace("import Translation.UnitLifecycleT3\n", "import Translation.UnitLifecycleT3\nimport Translation.UnitLifecycleT3\n", 1))
PY
resolver_out --verify
cases=$((cases + 1))
[ "$rc" -eq 1 ] && grep -qF "the audit's imports: 'import Translation.UnitLifecycleT3' appears twice" <<<"$out" \
  || fail_case "verify-duplicate: expected --verify to name the repeated import" "$out"
reset
# An evidence line of the obligations file repeated verbatim is named by --verify.
python3 - "$clone/ASSURANCE-OBLIGATIONS.md" <<'PY'
import sys
p = sys.argv[1]; lines = open(p).read().split("\n")
k = next(i for i, l in enumerate(lines) if l.startswith("  `check-restored-negatives.py` ("))
lines.insert(k, lines[k])
open(p, "w").write("\n".join(lines))
PY
resolver_out --verify
cases=$((cases + 1))
[ "$rc" -eq 1 ] && grep -qF "'check-restored-negatives.py (' appears twice" <<<"$out" \
  || fail_case "verify-evidence-repeat: expected --verify to name the repeated evidence line" "$out"
reset

# The same prose line edited on one side and kept on the other (a predecessor's text reworded before its squash)
# is refused: both sides hold prose at one place.
prose_at() { echo "i = t.index('  the Session Braid port scripts refuse a source whose anchor moved.'); t = t[:i] + '$1\\n' + t[i:]"; }
a="$(branch ASSURANCE-OBLIGATIONS.md "$(prose_at '  the alpha fixture keeps its frame;')" a)"
b="$(branch ASSURANCE-OBLIGATIONS.md "$(prose_at '  the alpha fixture keeps its frame and its key;')" b)"
g checkout -q --detach "$a"
g merge -q --no-edit "$b" >/dev/null 2>&1 && fail_case "prose-edited: the fixture merge did not conflict"
resolver_out
cases=$((cases + 1))
[ "$rc" -eq 1 ] && grep -qF "both insertions at line" <<<"$out" && grep -qF "hold prose" <<<"$out" \
  || fail_case "prose-edited: expected the resolver to refuse prose on both sides" "$out"
reset
# The same keyed entry with other text on the two sides (the scaffold's clause, edited) is refused.
a="$(branch ASSURANCE-OBLIGATIONS.md "$(prose_at '  QQcheck-alpha-negatives.pyQQ: the alpha fixture (to be written);') ; t = t.replace('QQ', chr(96))" a)"
b="$(branch ASSURANCE-OBLIGATIONS.md "$(prose_at '  QQcheck-alpha-negatives.pyQQ: the alpha fixture keeps its frame;') ; t = t.replace('QQ', chr(96))" b)"
g checkout -q --detach "$a"
g merge -q --no-edit "$b" >/dev/null 2>&1 && fail_case "entry-edited: the fixture merge did not conflict"
resolver_out
cases=$((cases + 1))
[ "$rc" -eq 1 ] && grep -qF "hold an entry for 'check-alpha-negatives.py' with other text" <<<"$out" \
  || fail_case "entry-edited: expected the resolver to refuse one entry edited" "$out"
reset
# A closing `fi` alone on one side, where the other inserts a block ending in `fi`, is not taken as held by it:
# both are kept, and the file still parses.
a="$(branch tacenta-proofs/scripts/no-sorry.sh "t = t.replace('python3 scripts/check-restored-negatives.py || fail=1\n', 'if true; then\npython3 scripts/check-restored-negatives.py || fail=1\nfi\n', 1)" a)"
b="$(branch tacenta-proofs/scripts/no-sorry.sh "t = t.replace('python3 scripts/check-restored-negatives.py || fail=1\n', 'python3 scripts/check-restored-negatives.py || fail=1\nif false; then\n  :\nfi\n', 1)" b)"
g checkout -q --detach "$a"
g merge -q --no-edit "$b" >/dev/null 2>&1 || true
resolver_out
if [ "$rc" -eq 0 ]; then
  cases=$((cases + 1))
  bash -n "$clone/tacenta-proofs/scripts/no-sorry.sh" || fail_case "closing-fi: the resolution does not parse"
else
  cases=$((cases + 1))
  grep -qF "REFUSED" <<<"$out" || fail_case "closing-fi: neither resolved nor refused" "$out"
fi
reset

# Two branches that each scaffold a module whose entries sort after the same existing entries, and write the
# generated inventory: every shared list conflicts with two insertions at one place, and so does the inventory.
# The script resolves the insertions, writes the generated files again from the merged tree, stages them, and
# every check it runs passes, with both modules wired.
scaffold() {  # module script
  g checkout -q --detach "$base"
  (cd "$clone" && python3 tacenta-proofs/scripts/new-lifecycle-module.py scaffold --module "$1" --negatives "$2" \
    --part decrypt --description "A fixture module." --no-regenerate >/dev/null \
    && python3 tooling/gate-inventory.py --write >/dev/null)
  g add -A
  g commit -q -m "$1"
  g rev-parse HEAD
}
a="$(scaffold UnitLifecycleResponderRelay check-responder-relay-negatives.py)"
b="$(scaffold UnitLifecycleResponderRelayReceipt check-responder-relay-receipt-negatives.py)"
g config merge.conflictStyle diff3
g checkout -q --detach "$a"
g merge -q --no-edit "$b" >/dev/null 2>&1 && fail_case "adjacent-modules: the fixture merge did not conflict"
cases=$((cases + 1))
conflicted="$(g diff --name-only --diff-filter=U | wc -l | tr -d ' ')"
[ "$conflicted" -ge 7 ] || fail_case "adjacent-modules: expected the shared lists to conflict" "$(g status --short)"
run adjacent-modules 0 "regenerate-generated: done"
says_also adjacent-modules "resolve-insertion-conflicts: resolved"
cases=$((cases + 1))
[ -z "$(g diff --name-only --diff-filter=U)" ] || fail_case "adjacent-modules: a file is still unmerged" "$(g status --short)"
for f in check-responder-relay-negatives.py check-responder-relay-receipt-negatives.py; do
  cases=$((cases + 1))
  grep -qF "python3 scripts/$f || fail=1" "$clone/tacenta-proofs/scripts/no-sorry.sh" \
    && grep -qF "tacenta-proofs/scripts/$f" "$clone/tacenta-proofs/GATE-INVENTORY.md" \
    && grep -qF "  \`$f\`," "$clone/ASSURANCE-OBLIGATIONS.md" \
    || fail_case "adjacent-modules: $f is not wired in the merged tree"
done
cases=$((cases + 1))
! g grep -I -q -E '^(<<<<<<<|=======|>>>>>>>)' -- . ':!*.patch' \
  || fail_case "adjacent-modules: a conflict marker is left" "$(g grep -I -n -E '^(<<<<<<<|=======|>>>>>>>)' -- . ':!*.patch')"
g config --unset merge.conflictStyle
reset

# A branch built on another: A scaffolds Alpha; B is A plus Beta; main squash-merges A; B then merges main. Both
# sides hold Alpha's entries; the resolver must keep them once and add Beta's, and --verify must pass.
a="$(scaffold UnitLifecycleResponderAlpha check-responder-alpha-negatives.py)"
(cd "$clone" && python3 tacenta-proofs/scripts/new-lifecycle-module.py scaffold --module UnitLifecycleResponderBeta \
  --negatives check-responder-beta-negatives.py --part decrypt --description "A fixture module." --no-regenerate >/dev/null \
  && python3 tooling/gate-inventory.py --write >/dev/null)
g add -A; g commit -q -m beta; b="$(g rev-parse HEAD)"
squash="$(g commit-tree "$(g rev-parse "$a^{tree}")" -p "$base" -m "squash of alpha")"
g checkout -q --detach "$b"
g merge -q --no-edit "$squash" >/dev/null 2>&1 || true
resolver_out
cases=$((cases + 1))
[ "$rc" -eq 0 ] && grep -qE "resolved [1-9][0-9]* file" <<<"$out" \
  || fail_case "squash-predecessor: the resolver refused or had nothing to resolve" "$out"
resolver_out --verify
cases=$((cases + 1))
[ "$rc" -eq 0 ] || fail_case "squash-predecessor: --verify found a problem after the resolution" "$out"
for f in check-responder-alpha-negatives.py check-responder-beta-negatives.py; do
  cases=$((cases + 1))
  [ "$(grep -c "^python3 scripts/$f || fail=1$" "$clone/tacenta-proofs/scripts/no-sorry.sh")" = 1 ] \
    && [ "$(grep -c "^  \`$f\`,$" "$clone/ASSURANCE-OBLIGATIONS.md")" = 1 ] \
    || fail_case "squash-predecessor: $f is not wired exactly once"
done
reset

echo "regenerate-generated-cases: $cases cases (a hand-written file unmerged or holding a marker and an unmerged case count refused with nothing written; a line both sides changed and overlapping insertions refused; two modules' insertions at one place resolved under diff3 style and the generated files written again, staged and checked; a squash-merged predecessor's entries kept once; a planted duplicate named) gave the expected result"
