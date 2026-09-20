#!/usr/bin/env bash
# Prove the lifecycle public-root coverage gate fails when one generated root
# disappears. The mutation changes only the gate input, never the repository.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
source_file="$here/../translation/Translation/TacentaLifecycle.lean"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
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
echo "lifecycle-translation-coverage-negatives: missing-root mutation refused"
