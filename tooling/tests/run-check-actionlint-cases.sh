#!/usr/bin/env bash
# Hold actionlint's added expression coverage to a passing and failing control.
set -euo pipefail
# Exit-status guard. With an EXIT trap set, macOS /bin/bash 3.2 and /bin/sh exit 0 when a shell-fatal error
# (an unset variable under -u, ${x:?}, a missing sourced file) stops a `set -e` script, so the trap refuses a
# run that reached neither `finished=yes` nor done_ok. Cases: tooling/tests/run-exit-trap-status-cases.sh.
finished=no
done_ok() { finished=yes; exit 0; }
exit_guard() {  # <status the EXIT trap began with>
  if [ "$1" -eq 0 ] && [ "$finished" != yes ]; then
    echo "$0: stopped before its end with status 0 (a shell-fatal error, a signal, or exit 0 without done_ok); not a pass" >&2
    exit 1
  fi
  exit "$1"
}

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
trap 'exit_guard_rc=$?; set +e; cleanup; exit_guard "$exit_guard_rc"' EXIT

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

cat > "$work/schema.yml" <<'YAML'
name: actionlint schema control
on: push
permissions:
  contents: read
unknown_top_level: true
jobs:
  check:
    runs-on: ubuntu-latest
    steps:
      - run: true
YAML
set +e
out="$("$actionlint" -color=false "$work/schema.yml" 2>&1)"
rc=$?
set -e
if [ "$rc" -eq 0 ]; then
  echo "WRONG  unknown-schema-key: expected refusal, was accepted" >&2
  exit 1
fi
if [[ "$out" != *'unexpected key "unknown_top_level"'* ]]; then
  echo "WRONG  unknown-schema-key: refused, but not for schema validation:" >&2
  printf '%s\n' "$out" >&2
  exit 1
fi
echo "check-actionlint-cases: pass, malformed-expression and unknown-schema-key controls gave the expected result"
finished=yes
