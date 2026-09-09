#!/usr/bin/env bash
# Hold `tooling/check-bundle-drift.py` to its cases.
#
#   bash tooling/tests/run-check-bundle-drift-cases.sh
#
# Each directory under `check-bundle-drift-cases/` is one small pair of files
# to compare. A `pass-*` case must be accepted; a `fail-*` case must be
# refused, and refused for the stated reason: the first line of its
# `TripleT3.lean` is `-- expect: <text>`, and that text must appear in the
# checker's output, so a case that fails for some other reason (a fixture that
# stopped parsing, say) is caught rather than counted.
#
# The two leaf files under `_leaves/` are shared: they stand in for
# `Translation/T3.lean` and `Translation/SpqrT3.lean`, cut to the theorems the
# bundles mirror. A case directory holds only the files it changes, which for
# every case here is `TripleT3.lean`, so the diff between a case and
# `pass-matching` is the whole of what the case is about. A case that wants to
# move a *leaf* instead can drop its own `T3.lean` or `SpqrT3.lean` beside it
# and that copy wins.
#
# The checker is not changed to run these. It reads a translation directory,
# and this script assembles one per case in a temporary directory, so the case
# files never sit under a `Translation/` path the real run would read. The
# script runs in `tooling/ci.sh` and in the workflow's `checks` job right after
# the checker itself, so a substitution loosened by mistake fails the gate on
# the same push rather than at the next reader.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
checker="$root/tooling/check-bundle-drift.py"
cases="$here/check-bundle-drift-cases"

# Unlike the workflow cases there is nothing optional to skip on: the checker
# needs `python3` and the files, and `tooling/ci.sh` has already used `python3`
# by the time it reaches here.
if ! command -v python3 >/dev/null 2>&1; then
  echo "check-bundle-drift-cases: python3 not found" >&2
  exit 1
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

wrong=0
total=0
for case in "$cases"/pass-* "$cases"/fail-*; do
  [ -d "$case" ] || continue
  total=$((total + 1))
  name="$(basename "$case")"
  tree="$work/$name/Translation"
  mkdir -p "$tree"
  cp "$cases"/_leaves/*.lean "$tree/"
  cp "$case"/*.lean "$tree/"
  set +e
  out="$(python3 "$checker" --translation-dir "$tree" 2>&1)"
  rc=$?
  set -e
  case "$name" in
    pass-*)
      if [ "$rc" -ne 0 ]; then
        echo "WRONG  $name: expected accepted, was refused:" >&2
        printf '  %s\n' "$out" >&2
        wrong=$((wrong + 1))
      fi
      ;;
    fail-*)
      expect="$(sed -n '1s/^-- expect: //p' "$case/TripleT3.lean")"
      if [ -z "$expect" ]; then
        echo "WRONG  $name: a fail case's first line must be '-- expect: <text>'" >&2
        wrong=$((wrong + 1))
      elif [ "$rc" -eq 0 ]; then
        echo "WRONG  $name: expected refused ($expect), was accepted" >&2
        wrong=$((wrong + 1))
      elif ! printf '%s' "$out" | grep -qF -- "$expect"; then
        echo "WRONG  $name: refused, but not for '$expect':" >&2
        printf '  %s\n' "$out" >&2
        wrong=$((wrong + 1))
      fi
      ;;
  esac
done

if [ "$total" -eq 0 ]; then
  echo "check-bundle-drift-cases: no cases found under $cases" >&2
  exit 1
fi
if [ "$wrong" -ne 0 ]; then
  echo "check-bundle-drift-cases: $wrong of $total case(s) gave the wrong result" >&2
  exit 1
fi
echo "check-bundle-drift-cases: $total case(s) gave the expected result"
