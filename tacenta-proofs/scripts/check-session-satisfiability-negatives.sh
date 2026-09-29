#!/usr/bin/env bash
# Prove the Session contract coverage depends on every named witness.
set -euo pipefail

cd "$(dirname "$0")/.."
src="translation/Translation/UnitSatisfiabilitySession.lean"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT INT TERM

# Rename one witness while leaving the thirteen-contract coverage theorem
# intact. The copy must stop elaborating at the missing name. Two witnesses are
# tried: the first one the coverage theorem listed, and the identity-key
# contract's, added after it, so that a witness missing from the theorem's list
# is noticed by this control.
for witness in random32_satisfiable dh_identity_satisfiable; do
  python3 - "$src" "$tmp/UnitSatisfiabilitySessionMissingWitness.lean" "$witness" <<'PY'
from pathlib import Path
import sys

source = Path(sys.argv[1]).read_text()
old = f"theorem {sys.argv[3]} :"
if source.count(old) != 1:
    raise SystemExit(f"expected one witness declaration, found {source.count(old)}")
Path(sys.argv[2]).write_text(source.replace(
    old, f"theorem {sys.argv[3]}_removed :"))
PY

  if (cd translation && lake env lean \
      "$tmp/UnitSatisfiabilitySessionMissingWitness.lean") >"$tmp/out" 2>&1; then
    echo "session-satisfiability negative: removing $witness still built" >&2
    exit 1
  fi
  if ! grep -q "Unknown identifier.*$witness" "$tmp/out"; then
    echo "session-satisfiability negative: removing $witness failed for the wrong reason" >&2
    cat "$tmp/out" >&2
    exit 1
  fi
done

echo "session-satisfiability negative: removing a named witness is refused"
