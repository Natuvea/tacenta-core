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
# Every case runs against a throwaway repository root holding the real
# `PreconditionShapes.lean`, because the script requires its allow-listed
# refutations to be present and a root without them would fail every case for
# that reason alone. A case can override that file by shipping its own
# `PreconditionShapes.lean`, which is how the allow-list itself is tested. Any
# other `.lean` in the case directory is added beside it.
#
# The script is not changed to run these. It reads a root, and this assembles
# one per case, so no case file ever sits where the real run would read it.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
cases="$here/check-precondition-shapes-cases"
real="$root/tacenta-proofs/translation/Translation/PreconditionShapes.lean"
script="$root/tooling/check-precondition-shapes.py"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

wrong=0
total=0
for dir in "$cases"/*/; do
  name=$(basename "$dir")
  total=$((total + 1))
  case_root="$tmp/$name"
  dest="$case_root/tacenta-proofs/translation/Translation"
  mkdir -p "$dest"
  if [ -f "$dir/PreconditionShapes.lean" ]; then
    cp "$dir/PreconditionShapes.lean" "$dest/PreconditionShapes.lean"
  else
    cp "$real" "$dest/PreconditionShapes.lean"
  fi
  for f in "$dir"*.lean; do
    [ -e "$f" ] || continue
    [ "$(basename "$f")" = "PreconditionShapes.lean" ] && continue
    cp "$f" "$dest/"
  done

  expect=$(head -1 "$dir/expect")
  set +e
  out=$(python3 "$script" --root "$case_root" 2>&1)
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
  fi
done

if [ $wrong -ne 0 ]; then
  echo "check-precondition-shapes-cases: $wrong of $total case(s) gave the wrong result"
  exit 1
fi
echo "check-precondition-shapes-cases: $total case(s) gave the expected result"
