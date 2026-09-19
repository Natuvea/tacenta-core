#!/usr/bin/env bash
# Prove the Session contract coverage depends on every named witness.
set -euo pipefail

cd "$(dirname "$0")/.."
src="translation/Translation/UnitSatisfiabilitySession.lean"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT INT TERM

# Rename one witness while leaving the ten-contract coverage theorem intact.
# The copy must stop elaborating at the missing name.
python3 - "$src" "$tmp/UnitSatisfiabilitySessionMissingWitness.lean" <<'PY'
from pathlib import Path
import sys

source = Path(sys.argv[1]).read_text()
old = "theorem random32_satisfiable :"
if source.count(old) != 1:
    raise SystemExit(f"expected one witness declaration, found {source.count(old)}")
Path(sys.argv[2]).write_text(source.replace(
    old, "theorem random32_satisfiable_removed :"))
PY

if (cd translation && lake env lean \
    "$tmp/UnitSatisfiabilitySessionMissingWitness.lean") >"$tmp/out" 2>&1; then
  echo "session-satisfiability negative: removing a named witness still built" >&2
  exit 1
fi
if ! grep -q 'Unknown identifier.*random32_satisfiable' "$tmp/out"; then
  echo "session-satisfiability negative: failed for the wrong reason" >&2
  cat "$tmp/out" >&2
  exit 1
fi

echo "session-satisfiability negative: removing a named witness is refused"
