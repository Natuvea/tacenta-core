#!/usr/bin/env bash
# Hold actionlint's added expression coverage to a passing and failing control.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
actionlint="${ACTIONLINT_BIN:-}"
if [ -z "$actionlint" ]; then
  actionlint="$(command -v actionlint || true)"
fi
if [ -z "$actionlint" ] || [ ! -x "$actionlint" ]; then
  echo "check-actionlint-cases: actionlint is not installed" >&2
  exit 1
fi

work="$(mktemp -d)"
cleanup() { rm -rf "$work"; }
trap cleanup EXIT

cat > "$work/pass.yml" <<'YAML'
name: actionlint pass control
on: push
permissions:
  contents: read
jobs:
  check:
    runs-on: ubuntu-latest
    if: ${{ github.event_name == 'push' }}
    steps:
      - run: true
YAML
"$actionlint" -color=false "$work/pass.yml"

cat > "$work/fail.yml" <<'YAML'
name: actionlint expression control
on: push
permissions:
  contents: read
jobs:
  check:
    runs-on: ubuntu-latest
    if: ${{ github.event_name == }}
    steps:
      - run: true
YAML
set +e
out="$("$actionlint" -color=false "$work/fail.yml" 2>&1)"
rc=$?
set -e
if [ "$rc" -eq 0 ]; then
  echo "WRONG  malformed-expression: expected refusal, was accepted" >&2
  exit 1
fi
if [[ "$out" != *"unexpected end of input"* ]]; then
  echo "WRONG  malformed-expression: refused, but not for expression syntax:" >&2
  printf '%s\n' "$out" >&2
  exit 1
fi
echo "check-actionlint-cases: pass and malformed-expression controls gave the expected result"
