#!/usr/bin/env bash
# Hold `tooling/check-precondition-shapes.py` to its cases.
#
#   bash tooling/tests/run-check-precondition-shapes-cases.sh
#
# Each directory under `check-precondition-shapes-cases/` is one case. Its
# `expect` file is `pass`, or `fail: <text>` where the text must appear in the
# script's output, so a case that fails for some other reason is caught rather
# than counted.
#
# Every case runs against a throwaway repository root holding the full scan
# skeleton -- every scanned directory, every root file, and the real
# `PreconditionShapes.lean` -- because the script refuses a root with any of
# those missing, and a bare root would fail every case for that reason alone.
# A case then changes that root with any of:
#
#   files/          copied over the skeleton, repository-relative
#   insert_before   first line a marker in PreconditionShapes.lean; the rest is
#                   inserted before it, so a case can add a declaration inside
#                   the refutations' own namespace
#   remove          repository-relative paths to delete
#   symlink         lines of `<link> <target>`
#   binary          repository-relative paths to overwrite with invalid UTF-8
#   count           the exact number of `::error::` lines a refused case must
#                   produce. Without it a case checks only that the script
#                   refused and why, which cannot see two sites reported as one.
#   location        lines of `path:line:col:`, each of which must appear. A
#                   review found every reported column pointing at the maximum
#                   after the one at fault, and no case had looked.
#
# The script is not changed to run these. It reads a root, and this assembles
# one per case, so no case file ever sits where the real run would read it.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
cases="$here/check-precondition-shapes-cases"
shapes_rel="tacenta-proofs/translation/Translation/PreconditionShapes.lean"
real="$root/$shapes_rel"
script="$root/tooling/check-precondition-shapes.py"

# Kept in step with SCAN_DIRS and SCAN_FILES in the script. The fail-shape-in-*
# and fail-missing-* cases go red if the two lists drift apart.
dirs=(tacenta-model/Model tacenta-model/Properties tacenta-proofs/Proofs
      tacenta-proofs/translation/Translation)
roots=(tacenta-model/Vectors.lean tacenta-model/Difftest.lean
       tacenta-model/lakefile.lean tacenta-proofs/lakefile.lean
       tacenta-proofs/translation/Translation.lean)

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

wrong=0
total=0
for dir in "$cases"/*/; do
  name=$(basename "$dir")
  total=$((total + 1))
  cr="$tmp/$name"
  for d in "${dirs[@]}"; do mkdir -p "$cr/$d"; done
  for r in "${roots[@]}"; do mkdir -p "$(dirname "$cr/$r")"; : > "$cr/$r"; done
  cp "$real" "$cr/$shapes_rel"

  if [ -d "$dir/files" ]; then cp -R "$dir/files/." "$cr/"; fi
  if [ -f "$dir/insert_before" ]; then
    python3 - "$cr/$shapes_rel" "$dir/insert_before" <<'PY'
import sys
target, spec = sys.argv[1], sys.argv[2]
marker, _, text = open(spec, encoding="utf-8").read().partition("\n")
s = open(target, encoding="utf-8").read()
i = s.find(marker)
if i < 0:
    sys.exit("insert_before: marker not found in PreconditionShapes.lean: %r" % marker)
open(target, "w", encoding="utf-8").write(s[:i] + text + s[i:])
PY
  fi
  if [ -f "$dir/remove" ]; then
    while IFS= read -r p || [ -n "$p" ]; do
      [ -n "$p" ] && rm -rf "${cr:?}/$p"
    done < "$dir/remove"
  fi
  if [ -f "$dir/symlink" ]; then
    while IFS=' ' read -r link target || [ -n "$link" ]; do
      [ -n "$link" ] && ln -s "$target" "$cr/$link"
    done < "$dir/symlink"
  fi
  if [ -f "$dir/binary" ]; then
    while IFS= read -r p || [ -n "$p" ]; do
      [ -n "$p" ] && printf '\xff\xfe theorem\n' > "$cr/$p"
    done < "$dir/binary"
  fi

  expect=$(head -1 "$dir/expect")
  set +e
  out=$(python3 "$script" --root "$cr" 2>&1)
  status=$?
  set -e

  if [ "$expect" = "pass" ]; then
    if [ $status -ne 0 ]; then
      wrong=$((wrong + 1))
      echo "WRONG  $name: expected accepted, was refused:"
      echo "$out" | sed 's/^/    /'
    fi
    continue
  fi
  reason=${expect#fail: }
  if [ $status -eq 0 ]; then
    wrong=$((wrong + 1))
    echo "WRONG  $name: expected refused ($reason), was accepted"
  elif [[ "$out" != *"$reason"* ]]; then
    wrong=$((wrong + 1))
    echo "WRONG  $name: refused, but not for '$reason':"
    echo "$out" | sed 's/^/    /'
  else
    if [ -f "$dir/count" ]; then
      want=$(tr -d ' \n' < "$dir/count")
      got=$(printf '%s\n' "$out" | grep -c '^::error::' || true)
      if [ "$got" != "$want" ]; then
        wrong=$((wrong + 1))
        echo "WRONG  $name: refused for the right reason, but reported $got problem(s), expected $want:"
        echo "$out" | sed 's/^/    /'
        continue
      fi
    fi
    if [ -f "$dir/location" ]; then
      while IFS= read -r want_loc || [ -n "$want_loc" ]; do
        [ -z "$want_loc" ] && continue
        if [[ "$out" != *"check-precondition-shapes: $want_loc"* ]]; then
          wrong=$((wrong + 1))
          echo "WRONG  $name: no report at $want_loc:"
          echo "$out" | sed 's/^/    /'
          break
        fi
      done < "$dir/location"
    fi
  fi
done

if [ $wrong -ne 0 ]; then
  echo "check-precondition-shapes-cases: $wrong of $total case(s) gave the wrong result"
  exit 1
fi
echo "check-precondition-shapes-cases: $total case(s) gave the expected result"
