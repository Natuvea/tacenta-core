#!/usr/bin/env bash
# Negative controls for tooling/check-merge-exactness.sh, on a throwaway repository:
#
#   a clean merge                                   PASS, exact
#   a merge with one of the second side's hunks dropped   FAIL, the file named, a line missing
#   a merge with a hunk neither side made           FAIL, the file named, a line in the merge
#   a merge that differs only in a generated file   PASS, the file listed as allowed
#   a resolved conflict                             REVIEW (exit 3), the file named
#   that resolution with a file added elsewhere     FAIL, the added file named
#   a conflict resolved by taking one side whole    FAIL: the other side's clean hunk in that file is missing
#   the same change on both sides (a squash-merged  PASS: git's own merge is the merge
#     predecessor)
#   an adapting edit after the merge / inside it    the merge PASS / FAIL
#   a merge that commits a conflict marker          FAIL, the marker listed
#   a merge that is not signed off                  FAIL
#   a commit that is not a merge, two merge bases   refused (exit 2); an explicit base is used
set -euo pipefail

script="$(cd "$(dirname "$0")/.." && pwd)/check-merge-exactness.sh"
work="$(mktemp -d "${TMPDIR:-/tmp}/merge-exactness-cases.XXXXXX")"
trap 'rm -rf "$work"' EXIT
repo="$work/repo"
cases=0
git init -q -b main "$repo"
g() { git -C "$repo" -c user.name=control -c user.email=control@example.invalid -c commit.gpgsign=false "$@"; }
sign="Signed-off-by: control <control@example.invalid>"

fail_case() {
  echo "WRONG  merge-exactness $1" >&2
  shift
  [ $# -eq 0 ] || printf '%s\n' "$@" >&2
  exit 1
}
check() {  # name want-exit needle... : run the script on HEAD (and an optional base in $BASE_ARG)
  local name="$1" want="$2" out rc needle
  shift 2
  set +e
  out="$(cd "$repo" && bash "$script" "${REV:-HEAD}" ${BASE_ARG:-} 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  [ "$rc" -eq "$want" ] || fail_case "$name: expected exit $want, got $rc" "$out"
  for needle in "$@"; do
    grep -qF -- "$needle" <<<"$out" || fail_case "$name: expected '$needle'" "$out"
  done
}
lines() { seq 1 20 | sed "s/^/$1 line /"; }

mkdir -p "$repo/tacenta-proofs"
lines a > "$repo/a.txt"
lines b > "$repo/b.txt"
lines g > "$repo/tacenta-proofs/GATE-INVENTORY.md"
g add -A
g commit -q -m "base" -m "$sign"
base="$(g rev-parse HEAD)"
g checkout -q -b one
sed -i.bak 's/^a line 2$/a line 2 (one)/' "$repo/a.txt"
sed -i.bak 's/^g line 3$/g line 3 (one)/' "$repo/tacenta-proofs/GATE-INVENTORY.md"
rm -f "$repo"/*.bak "$repo"/tacenta-proofs/*.bak
g commit -q -am "one" -m "$sign"
g checkout -q -b two "$base"
sed -i.bak 's/^a line 15$/a line 15 (two)/' "$repo/a.txt"
sed -i.bak 's/^b line 5$/b line 5 (two)/' "$repo/b.txt"
sed -i.bak 's/^g line 17$/g line 17 (two)/' "$repo/tacenta-proofs/GATE-INVENTORY.md"
rm -f "$repo"/*.bak "$repo"/tacenta-proofs/*.bak
g commit -q -am "two" -m "$sign"

merge_two() {  # a fresh clean merge of two into one, not yet committed
  g checkout -q -f one
  g checkout -q --detach
  g merge -q --no-ff --no-commit two >/dev/null 2>&1
}
commit_merge() { g commit -q -m "merge two" -m "${1:-$sign}"; }

merge_two; commit_merge
check clean 0 "exact: the merge holds each side's changes and nothing else" "verdict: PASS"
BASE_ARG=nosuchref check unknown-base 2 "nosuchref is not a commit"

merge_two
sed -i.bak 's/^a line 15 (two)$/a line 15/' "$repo/a.txt"; rm -f "$repo"/*.bak
g add -A; commit_merge
check dropped-hunk 1 "DIFFERS  a.txt: not git's own clean merge of the two sides" "NOT EXACT: 1 file(s) differ from git's own merge outside its conflicts: a.txt" "verdict: FAIL"

merge_two
printf 'b line added in the merge\n' >> "$repo/b.txt"
g add -A; commit_merge
check added-hunk 1 "DIFFERS  b.txt: not git's own clean merge of the two sides" "verdict: FAIL"

merge_two
sed -i.bak 's/^g line 9$/g line 9 (regenerated)/' "$repo/tacenta-proofs/GATE-INVENTORY.md"; rm -f "$repo"/tacenta-proofs/*.bak
g add -A; commit_merge
check generated-only 0 "allowed  tacenta-proofs/GATE-INVENTORY.md (generated)" "exact outside the generated files; 1 generated file(s) differ" "verdict: PASS"

merge_two
printf '<<<<<<< ours\n' >> "$repo/b.txt"
g add -A; commit_merge
check marker 1 "conflict markers in the merge's tree:" "b.txt:21:<<<<<<< ours" "verdict: FAIL"

merge_two; commit_merge "no trailer"
check unsigned 1 "NOT signed off by its author (control <control@example.invalid>)" "verdict: FAIL"

# A resolved conflict: both sides change one line; the merge takes a third text.
g checkout -q -b three "$base"
sed -i.bak 's/^a line 2$/a line 2 (three)/' "$repo/a.txt"; rm -f "$repo"/*.bak
g commit -q -am "three" -m "$sign"
g checkout -q -f one; g checkout -q --detach
g merge -q --no-ff --no-commit three >/dev/null 2>&1 && fail_case "resolved-conflict: the fixture did not conflict"
lines a | sed 's/^a line 2$/a line 2 (one and three)/' > "$repo/a.txt"
g add -A; commit_merge
check resolved-conflict 3 "1 file(s) resolved by hand where git's own merge conflicts, to read (the rest of each is git's merge): a.txt" "verdict: REVIEW"

# The same resolution with a hunk of the other side dropped in a file git merges cleanly fails.
g checkout -q -f one; g checkout -q --detach
g merge -q --no-ff --no-commit three >/dev/null 2>&1 || true
lines a | sed 's/^a line 2$/a line 2 (one and three)/' > "$repo/a.txt"
printf 'c\n' > "$repo/c.txt"
g add -A; commit_merge
check resolved-and-added 1 "NOT EXACT: 1 file(s) differ from git's own merge outside its conflicts: c.txt" "verdict: FAIL"

# A conflict resolved by taking the other side's whole file drops this side's clean hunk elsewhere in that file.
g checkout -q -b five "$base"
sed -i.bak -e 's/^a line 2$/a line 2 (five)/' -e 's/^a line 18$/a line 18 (five)/' "$repo/a.txt"; rm -f "$repo"/*.bak
g commit -q -am "five" -m "$sign"
g checkout -q --detach
g merge -q --no-ff --no-commit three >/dev/null 2>&1 && fail_case "theirs-whole: the fixture did not conflict"
g checkout -q --theirs a.txt
g add -A; commit_merge
check theirs-whole 1 "DIFFERS  a.txt: a part git merged cleanly, outside the conflict regions, is not in the merge" "verdict: FAIL"

# The same change on both sides (here a branch built on another that was squash-merged first) merges cleanly
# and is exact, though the two diffs differ.
g checkout -q -b squashed "$base"
sed -i.bak 's/^b line 5$/b line 5 (two)/' "$repo/b.txt"; rm -f "$repo"/*.bak
g commit -q -am "two's b change, squash-merged" -m "$sign"
g checkout -q -f two; g checkout -q --detach
sed -i.bak 's/^b line 12$/b line 12 (after)/' "$repo/b.txt"; rm -f "$repo"/*.bak
g commit -q -am "built on two" -m "$sign"
g merge -q --no-ff -m "merge the squash" -m "$sign" squashed >/dev/null 2>&1
check same-change 0 "exact: the merge holds each side's changes and nothing else" "verdict: PASS"
# An edit that adapts the merged tree, in a commit of its own after the merge, leaves the merge exact.
printf 'adapted\n' >> "$repo/b.txt"; g commit -q -am "adapt" -m "$sign"
REV=HEAD~1 check adaptation-after 0 "verdict: PASS"
# The same edit inside the merge commit fails.
g reset -q --hard HEAD~2
g merge -q --no-ff --no-commit squashed >/dev/null 2>&1
printf 'adapted\n' >> "$repo/b.txt"; g add -A; commit_merge
check adaptation-inside 1 "DIFFERS  b.txt: not git's own clean merge of the two sides" "verdict: FAIL"

# Not a merge; an unknown commit.
g checkout -q -f one
check not-a-merge 2 "is not a merge of two parents"

# Two merge bases (a criss-cross) are refused unless a base is named; with one named, it is used.
g checkout -q --detach "$base"; printf 'x\n' > "$repo/x.txt"; g add -A; g commit -q -m x -m "$sign"; x="$(g rev-parse HEAD)"
g checkout -q --detach "$base"; printf 'y\n' > "$repo/y.txt"; g add -A; g commit -q -m y -m "$sign"; y="$(g rev-parse HEAD)"
g checkout -q --detach "$x"; g merge -q --no-ff -m "x+y" -m "$sign" "$y" >/dev/null 2>&1
printf 'x2\n' >> "$repo/x.txt"; g commit -q -am x2 -m "$sign"; xm="$(g rev-parse HEAD)"
g checkout -q --detach "$y"; g merge -q --no-ff -m "y+x" -m "$sign" "$x" >/dev/null 2>&1
printf 'y2\n' >> "$repo/y.txt"; g commit -q -am y2 -m "$sign"
g merge -q --no-ff -m "criss-cross" -m "$sign" "$xm" >/dev/null 2>&1
check two-bases 2 "have 2 merge bases; name the base"
BASE_ARG="$x" check named-base 3 "over base $(g rev-parse --short "$x")" "resolved by hand where git's own merge conflicts, to read (the rest of each is git's merge): y.txt"

echo "merge-exactness-cases: $cases cases (a clean merge, the same change on both sides and a merge followed by an adapting commit passed; a resolved conflict sent to review; a one-side-whole resolution and an adapting edit inside the merge failed; a dropped hunk, an added hunk, a file added beside a resolution, a conflict marker and a missing sign-off failed; a generated-only difference allowed; a non-merge, an unknown base and two merge bases refused; a named base used) gave the expected result"
