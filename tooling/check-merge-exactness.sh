#!/usr/bin/env bash
# Check that a merge commit brought in each side's changes and nothing else.
#
#   bash tooling/check-merge-exactness.sh <merge-commit> [<base>]
#
# For a merge M with parents P1 and P2 and base B (the one merge base of P1 and P2 unless given), the reference is
# git's own merge of P1 and P2 over B (`git merge-tree --write-tree`, git 2.40 or later):
#
#   a file where M is git's clean merge                exact, whatever the two diffs say (the same change on both
#                                                       sides, as after a squash-merged shared predecessor, is not
#                                                       a hand edit)
#   a file git merges cleanly where M differs           FAIL: a hunk dropped, added or rewritten in the merge commit
#   a file git's merge conflicts in                     REVIEW, listed to be read, provided every part of git's
#                                                       merge outside the conflict regions is in M, in order; a
#                                                       part missing (a side's hunk dropped by taking one side
#                                                       whole) is a FAIL
#
# So edits that adapt the merged tree (a new part wired into the workflow, say) belong in a commit of their own
# after the merge: inside the merge commit they are a FAIL here, by design. Without `merge-tree`, the check falls
# back to comparing `git diff P1 M` with `git diff B P2` and `git diff P2 M` with `git diff B P1`, as the lines each
# removes and adds, which also flags a change both sides made alike.
#
# Differences in generated files are listed as allowed and do not fail the check, since those are written again
# from the merged tree rather than merged (`tooling/regenerate-generated.sh`):
#
#   tacenta-proofs/manifests/*.json, tacenta-proofs/GATE-INVENTORY.md, tooling/required-steps.json,
#   tacenta-proofs/scripts/attest-negatives-case-count.txt
#
# It also refuses a conflict marker in any file of M's tree (the rule of tooling/check-conflict-markers.sh) and a
# merge commit that is not signed off by its author (the rule of tooling/check-signoff.sh). It prints a short
# verdict and exits
#
#   0  PASS    exact outside the generated files, no marker, signed off
#   3  REVIEW  the same, except for the files git's merge conflicts in, which differ and are listed to be read
#   1  FAIL    a difference elsewhere, a marker or no sign-off
#   2          it cannot judge: not a merge of two parents, an unknown commit, several merge bases and no base
#
# What it does not check: that the generated files are current (`attest.py --check`, `gate-inventory.py --check`),
# that a resolution is right, or that a change that appears on both sides unchanged was meant to.
set -euo pipefail

usage() {
  echo "usage: check-merge-exactness.sh <merge-commit> [<base>]" >&2
  exit 2
}
[ $# -ge 1 ] && [ $# -le 2 ] || usage

merge="$(git rev-parse --verify --quiet "$1^{commit}")" || { echo "merge-exactness: $1 is not a commit" >&2; exit 2; }
parents="$(git rev-list --parents -n 1 "$merge" | cut -d' ' -f2-)"
p1="$(printf '%s\n' $parents | sed -n 1p)"
p2="$(printf '%s\n' $parents | sed -n 2p)"
p3="$(printf '%s\n' $parents | sed -n 3p)"
if [ -z "$p2" ] || [ -n "$p3" ]; then
  echo "merge-exactness: $(git rev-parse --short "$merge") is not a merge of two parents" >&2
  exit 2
fi
if [ -n "${2:-}" ]; then
  base="$(git rev-parse --verify --quiet "$2^{commit}")" || { echo "merge-exactness: $2 is not a commit" >&2; exit 2; }
else
  bases="$(git merge-base --all "$p1" "$p2")"
  if [ "$(printf '%s\n' "$bases" | grep -c .)" -ne 1 ]; then
    echo "merge-exactness: $(git rev-parse --short "$p1") and $(git rev-parse --short "$p2") have" \
      "$(printf '%s\n' "$bases" | grep -c .) merge bases; name the base" >&2
    exit 2
  fi
  base="$bases"
fi

short() { git rev-parse --short "$1"; }
echo "merge-exactness: $(short "$merge") merges $(short "$p1") and $(short "$p2") over base $(short "$base")"

work="$(mktemp -d "${TMPDIR:-/tmp}/merge-exactness.XXXXXX")"
trap 'rm -rf "$work"' EXIT
git diff --no-renames --no-ext-diff --binary -U0 "$p1" "$merge" > "$work/p1-m"
git diff --no-renames --no-ext-diff --binary -U0 "$base" "$p2" > "$work/b-p2"
git diff --no-renames --no-ext-diff --binary -U0 "$p2" "$merge" > "$work/p2-m"
git diff --no-renames --no-ext-diff --binary -U0 "$base" "$p1" > "$work/b-p1"

# The files git's own merge of the two sides leaves in conflict, and those where the merge differs from git's
# merge: a difference in a file git merged cleanly was made by hand. Needs `git merge-tree --write-tree`
# (git 2.40 or later); without it the comparison of the diffs alone decides.
: > "$work/conflicted"
: > "$work/by-hand"
auto="$(git merge-tree --write-tree --name-only --merge-base="$base" "$p1" "$p2" 2>/dev/null || true)"
tree="${auto%%$'\n'*}"
if printf '%s\n' "$tree" | grep -qE '^[0-9a-f]{40,64}$'; then
  printf '%s\n' "$auto" | sed -n '2,/^$/p' | sed '/^$/d' > "$work/conflicted"
  git diff --no-renames --name-only "$tree" "$merge" > "$work/by-hand"
  printf '%s\n%s\n' "$tree" "$merge" > "$work/trees"
  echo "merge-exactness: git's own merge of the two sides conflicts in $(grep -c . "$work/conflicted" || true) file(s)"
else
  echo "merge-exactness: this git has no \`merge-tree --write-tree\`; the two diffs alone decide" >&2
  echo "unknown" > "$work/conflicted"
fi

status=0
python3 - "$work" <<'PY' || status=$?
import fnmatch, sys
from collections import Counter
from pathlib import Path

work = Path(sys.argv[1])
GENERATED = ["tacenta-proofs/manifests/*.json", "tacenta-proofs/GATE-INVENTORY.md", "tooling/required-steps.json",
             "tacenta-proofs/scripts/attest-negatives-case-count.txt"]


def per_file(path):
    """{file: (Counter of removed lines, Counter of added lines, [the +/- lines in order])} of a -U0 diff."""
    files, current = {}, None
    for line in path.read_text(errors="replace").split("\n"):
        if line.startswith("diff --git "):
            current = line.split(" b/", 1)[1] if " b/" in line else line
            files[current] = (Counter(), Counter(), [])
        elif current is None or line.startswith(("index ", "--- ", "+++ ", "@@", "new file", "deleted file",
                                                 "old mode", "new mode", "similarity", "Binary files",
                                                 "GIT binary patch", "\\ No newline")):
            if current is not None and line.startswith(("new file", "deleted file", "old mode", "new mode",
                                                       "Binary files", "GIT binary patch")):
                files[current][2].append(line)
        elif line.startswith("-"):
            files[current][0][line[1:]] += 1
            files[current][2].append(line)
        elif line.startswith("+"):
            files[current][1][line[1:]] += 1
            files[current][2].append(line)
        elif current is not None and line:
            files[current][2].append(line)  # binary patch data
    return files


def compare(merge_side, side, label):
    a, b = per_file(work / merge_side), per_file(work / side)
    bad, allowed = [], []
    for name in sorted(set(a) | set(b)):
        ra, aa, oa = a.get(name, (Counter(), Counter(), []))
        rb, ab, ob = b.get(name, (Counter(), Counter(), []))
        if oa == ob:
            continue
        extra = sum(((ra - rb) + (aa - ab)).values())
        missing = sum(((rb - ra) + (ab - aa)).values())
        if extra == 0 and missing == 0:
            note = "the same lines, in another order or in a binary or mode change"
        else:
            note = f"{extra} line(s) in the merge's diff that the side's change lacks, {missing} line(s) of the side's change missing"
        (allowed if any(fnmatch.fnmatch(name, g) for g in GENERATED) else bad).append((name, note))
    for name, note in bad:
        print(f"  DIFFERS  {label}: {name}: {note}")
    for name, note in allowed:
        print(f"  allowed  {label}: {name} (generated): {note}")
    return bad, allowed


import subprocess

conflicted_text = (work / "conflicted").read_text().split()
known = conflicted_text != ["unknown"]
conflicted = set(conflicted_text) if known else set()
by_hand = set((work / "by-hand").read_text().split())
is_generated = lambda n: any(fnmatch.fnmatch(n, g) for g in GENERATED)


def blob(rev, name):
    r = subprocess.run(["git", "show", f"{rev}:{name}"], capture_output=True)
    return r.stdout.decode("utf-8", "replace").split("\n") if r.returncode == 0 else []


def clean_segments(lines):
    """The runs of lines of git's merge of a file outside its conflict regions."""
    segments, current, depth = [], [], 0
    for line in lines:
        if line.startswith("<<<<<<< "):
            depth += 1
            if current:
                segments.append(current)
            current = []
        elif line.startswith(">>>>>>> ") and depth:
            depth -= 1
        elif not depth:
            current.append(line)
    if current:
        segments.append(current)
    return segments


def holds_in_order(merged, segments):
    """The first segment of git's merge that the file does not hold, in order and contiguous, or None."""
    at = 0
    for seg in segments:
        found = next((k for k in range(at, len(merged) - len(seg) + 1) if merged[k:k + len(seg)] == seg), None)
        if found is None:
            return seg
        at = found + len(seg)
    return None


if known:
    # Git's own merge decides: a file equal to it is exact, whatever the two diffs say (the same change on both
    # sides, as after a squash-merged shared predecessor, merges cleanly and is not a hand edit).
    clean_changed = sorted(n for n in by_hand if n not in conflicted and not is_generated(n))
    resolved = sorted(n for n in conflicted if not is_generated(n))
    generated = sorted(n for n in by_hand if is_generated(n))
    tree, merge = (work / "trees").read_text().split()
    dropped = []
    for name in resolved:
        seg = holds_in_order(blob(merge, name), clean_segments(blob(tree, name)))
        if seg is not None:
            dropped.append(name)
            print(f"  DIFFERS  {name}: a part git merged cleanly, outside the conflict regions, is not in the merge "
                  f"({len(seg)} line(s) from {seg[0][:60]!r})")
    for name in clean_changed:
        print(f"  DIFFERS  {name}: not git's own clean merge of the two sides (a change made by hand in the merge commit)")
    for name in generated:
        print(f"  allowed  {name} (generated)")
    clean_changed = sorted(set(clean_changed) | set(dropped))
    resolved = [n for n in resolved if n not in dropped]
else:
    bad1, allowed1 = compare("p1-m", "b-p2", "the second parent's change into the first")
    bad2, allowed2 = compare("p2-m", "b-p1", "the first parent's change into the second")
    clean_changed = sorted({n for n, _ in bad1 + bad2})
    generated = sorted({n for n, _ in allowed1 + allowed2})
    resolved = []
if clean_changed:
    print(f"merge-exactness: NOT EXACT: {len(clean_changed)} file(s) differ from "
          + ("git's own merge outside its conflicts" if known else "what each side changed")
          + f": {', '.join(clean_changed)}")
if resolved:
    print(f"merge-exactness: {len(resolved)} file(s) resolved by hand where git's own merge conflicts, to read "
          "(the rest of each is git's merge): " + ", ".join(resolved))
if clean_changed:
    sys.exit(1)
if resolved:
    sys.exit(3)
if generated:
    print(f"merge-exactness: exact outside the generated files; {len(generated)} generated file(s) differ: {', '.join(generated)}")
else:
    print("merge-exactness: exact: the merge holds each side's changes and nothing else")
PY

markers="$(git grep -I -n -E '^(<<<<<<<|=======|>>>>>>>)' "$merge" -- . ':!*.patch' || true)"
if [ -n "$markers" ]; then
  echo "merge-exactness: conflict markers in the merge's tree:"
  printf '%s\n' "$markers" | sed "s/^$merge://; s/^/  /"
  status=1
else
  echo "merge-exactness: no conflict markers"
fi

author="$(git show -s --format='%an <%ae>' "$merge")"
if git show -s --format='%(trailers:key=Signed-off-by,valueonly)' "$merge" | grep -qxF -- "$author"; then
  echo "merge-exactness: signed off by its author ($author)"
else
  echo "merge-exactness: NOT signed off by its author ($author)"
  status=1
fi

case "$status" in
  0) echo "merge-exactness: verdict: PASS" ;;
  3) echo "merge-exactness: verdict: REVIEW (exact outside the files resolved by hand; read those)" ;;
  *) echo "merge-exactness: verdict: FAIL"; status=1 ;;
esac
exit "$status"
