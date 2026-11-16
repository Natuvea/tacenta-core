#!/usr/bin/env bash
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

root="$(cd "$(dirname "$0")/../.." && pwd)"
checker="$root/tooling/check-lifecycle-boundary-surface.py"
source_file="$root/tacenta-proofs/translation/Translation/TacentaLifecycle.lean"
tmp="$(mktemp -d)"
trap 'exit_guard_rc=$?; set +e; rm -rf "$tmp"; exit_guard "$exit_guard_rc"' EXIT

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

# The identity-key predicate is one of the pinned operations: losing it is a
# surface change, and the contract that covers it is named in the refusal.
sed 's/tacenta_boundary\.dh\.is_prime_order_public/tacenta_boundary.dh.is_prime_order_public_removed/g' \
  "$source_file" >"$tmp/no-identity-predicate.lean"
if python3 "$checker" --translation "$tmp/no-identity-predicate.lean" >"$tmp/out" 2>&1; then
  echo "boundary-surface case: accepted a lifecycle without the identity-key predicate" >&2
  exit 1
fi
grep -q 'expected operation(s) no longer reachable: tacenta_boundary.dh.is_prime_order_public' "$tmp/out"

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

# No Session proof root may regain any opaque standard-library adapter that the
# explicit Rust matches removed. Exercise every refused operation against the
# real root rather than only an adapter.
for operation in \
  core.option.Option.as_ref \
  core.option.Option.as_deref \
  core.option.Option.map \
  core.option.Option.map_or \
  core.option.Option.ok_or \
  core.result.Result.map_err
do
python3 - "$source_file" "$tmp/opaque-operation.lean" "$operation" <<'PY_INNER'
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text()
operation = sys.argv[3]
if f"axiom {operation}" not in text:
    text = f"axiom {operation} : Unit\n" + text
needle = "def lifecycle.Session.encrypt\n"
start = text.index(needle)
body = text.index(":= do", start) + len(":= do")
text = text[:body] + f"\n  let _opaque := {operation} m.data\n" + text[body:]
Path(sys.argv[2]).write_text(text)
PY_INNER
if python3 "$checker" --translation "$tmp/opaque-operation.lean" >"$tmp/out" 2>&1; then
  echo "boundary-surface case: accepted $operation in a Session root" >&2
  exit 1
fi
grep -q "Session proof surface regained opaque standard operation(s): $operation" "$tmp/out"
done

# A proof root that is not in the translation at all must be refused by name, and not walked as if it
# held no calls: the checker would otherwise report an empty surface for a root it never read.
sed 's/^def lifecycle\.Session\.encrypt$/def lifecycle.Session.encrypt_removed/' "$source_file" >"$tmp/no-root.lean"
if cmp -s "$source_file" "$tmp/no-root.lean"; then
  echo "boundary-surface case: the edit that removes a root changed nothing" >&2
  exit 1
fi
if python3 "$checker" --translation "$tmp/no-root.lean" >"$tmp/out" 2>&1; then
  echo "boundary-surface case: accepted a translation with a Session root missing" >&2
  exit 1
fi
grep -q 'missing proof root(s): lifecycle.Session.encrypt' "$tmp/out"

echo "10 lifecycle boundary-surface cases gave the expected result"
finished=yes
