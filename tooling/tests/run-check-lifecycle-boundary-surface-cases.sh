#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
checker="$root/tooling/check-lifecycle-boundary-surface.py"
source_file="$root/tacenta-proofs/translation/Translation/TacentaLifecycle.lean"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

python3 "$checker" --translation "$source_file" >/dev/null

# A newly reachable operation is refused even when the declaration already
# existed elsewhere in the generated leaf.
python3 - "$source_file" "$tmp/unexpected.lean" <<'PY'
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text()
needle = "def lifecycle.Session.encrypt\n"
start = text.index(needle)
body = text.index(":= do", start) + len(":= do")
text = text[:body] + "\n  let _new_boundary_call := tacenta_boundary.kem.KeyPair.generate\n" + text[body:]
Path(sys.argv[2]).write_text(text)
PY
if python3 "$checker" --translation "$tmp/unexpected.lean" >"$tmp/out" 2>&1; then
  echo "boundary-surface case: accepted an unclassified reachable operation" >&2
  exit 1
fi
grep -q 'unclassified reachable operation(s): tacenta_boundary.kem.KeyPair.generate' "$tmp/out"

# Losing an expected call is a surface change too, rather than permission to
# delete its contract silently.
sed 's/tacenta_boundary\.kem\.ciphertext_len/tacenta_boundary.kem.ciphertext_len_removed/g' \
  "$source_file" >"$tmp/missing.lean"
if python3 "$checker" --translation "$tmp/missing.lean" >"$tmp/out" 2>&1; then
  echo "boundary-surface case: accepted a missing expected operation" >&2
  exit 1
fi
grep -q 'expected operation(s) no longer reachable: tacenta_boundary.kem.ciphertext_len' "$tmp/out"

# Prose is not a call.  This guards the scanner itself against comment-shaped
# false evidence.
python3 - "$source_file" "$tmp/comment.lean" <<'PY'
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text()
needle = "def lifecycle.Session.encrypt\n"
start = text.index(needle)
text = text[:start] + "-- tacenta_boundary.kem.KeyPair.generate is not called here\n" + text[start:]
Path(sys.argv[2]).write_text(text)
PY
python3 "$checker" --translation "$tmp/comment.lean" >/dev/null

# The pure header adapters must not regain the opaque Option calls that the
# explicit Rust matches removed.
python3 - "$source_file" "$tmp/opaque-option.lean" <<'PY'
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text()
needle = "def lifecycle.composite_of\n"
start = text.index(needle)
body = text.index(":= do", start) + len(":= do")
text = text[:body] + "\n  let _opaque := core.option.Option.as_ref m.data\n" + text[body:]
Path(sys.argv[2]).write_text(text)
PY
if python3 "$checker" --translation "$tmp/opaque-option.lean" >"$tmp/out" 2>&1; then
  echo "boundary-surface case: accepted an opaque Option call in a header adapter" >&2
  exit 1
fi
grep -q 'header adapters regained opaque Option operation(s): core.option.Option.as_ref' "$tmp/out"

echo "4 lifecycle boundary-surface cases gave the expected result"
