#!/usr/bin/env bash
# Prove the lifecycle public-root coverage gate fails when one generated root
# disappears. The mutation changes only the gate input, never the repository.
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

here="$(cd "$(dirname "$0")" && pwd)"
source_file="$here/../translation/Translation/TacentaLifecycle.lean"
work="$(mktemp -d)"
trap 'exit_guard_rc=$?; set +e; rm -rf "$work"; exit_guard "$exit_guard_rc"' EXIT
mutant="$work/TacentaLifecycle.lean"
cp "$source_file" "$mutant"
python3 - "$mutant" <<'PY'
from pathlib import Path
import sys

p = Path(sys.argv[1])
text = p.read_text()
needle = "def lifecycle.Identity.generate"
if text.count(needle) != 1:
    raise SystemExit(f"expected one {needle!r}, found {text.count(needle)}")
p.write_text(text.replace(needle, "def lifecycle.Identity.generate_removed", 1))
PY

if python3 "$here/check-lifecycle-translation-coverage.py" "$mutant" >"$work/out" 2>&1; then
  echo "::error::lifecycle coverage gate accepted a missing generated public root" >&2
  exit 1
fi
grep -q "missing generated public lifecycle operation: lifecycle.Identity.generate" "$work/out"
# The gate needs its input: with no argument, or with a path that is not a file, it must refuse (exit 2) and
# say how it is used, and not pass for a coverage check it did not make.
for args in "" "$work/no-such-file.lean"; do
  set +e
  python3 "$here/check-lifecycle-translation-coverage.py" $args >"$work/usage-out" 2>&1
  rc=$?
  set -e
  if [ "$rc" -ne 2 ] || ! grep -q "usage: check-lifecycle-translation-coverage.py" "$work/usage-out"; then
    echo "::error::lifecycle coverage gate did not refuse a missing input (exit $rc)" >&2
    exit 1
  fi
done
echo "lifecycle-translation-coverage-negatives: missing-root mutation refused; a missing input refused"
finished=yes
