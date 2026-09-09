#!/usr/bin/env bash
# The label registry and the source agree, and new labels are prefix-free.
#
#   check-labels.sh
#
# The derivation labels are protocol constants and are frozen in a registry,
# `tacenta-core/LABELS.md`; this makes the registry binding rather than
# aspirational, so a label cannot be added, changed or removed without the table
# moving with it.
#
# **Prefix-freedom, not just distinctness.** Distinctness is what a casual check
# tests and it is not the property that matters: two labels that differ only by
# a suffix can collide once either is adjacent to variable-length data. Two such
# pairs exist today and are frozen deliberately -- see the registry for why
# neither is reachable -- so the check grandfathers exactly those pairs and
# refuses any new one.
#
# **What counts as a label, and where it is looked for.** Any `const` or
# `static` byte-string whose name ends in `INFO` or `LABEL`, `pub` or not, in
# every `.rs` file under `tacenta-core/src` and under each leaf crate's `src`,
# so that the root crate's own labels -- the application signing label and the
# last-resort handshake fingerprint label -- are inside the registry along with
# the leaf crates', and `LABELS.md` can say every domain-separation string is
# in one place.
#
set -euo pipefail

cd "$(cd "$(dirname "$0")/.." && pwd)"

registry="tacenta-core/LABELS.md"
status=0

# Source of truth: the constants themselves. One extraction, used by both
# halves below, so the two cannot disagree about what a label is.
extract_labels() {
  grep -rhoE '^[[:space:]]*(pub(\([^)]*\))?[[:space:]]+)?(const|static)[[:space:]]+[A-Z_]*(INFO|LABEL):[[:space:]]*&('\''static[[:space:]]+)?\[u8\][[:space:]]*=[[:space:]]*b"[^"]*"' \
    --include='*.rs' tacenta-core/src tacenta-core/*/src 2>/dev/null \
    | sed 's/.*b"//; s/"$//'
}

from_source_raw=$(extract_labels)
from_source=$(printf '%s\n' "$from_source_raw" | sort -u)
from_registry=$(
  grep -oE '^\| `tacenta-[a-z]+` \| `[A-Z_]+` \| `[^`]*` \|' "$registry" 2>/dev/null \
    | sed 's/.*| `//; s/` |$//' | sort -u
)

if [ "$from_source" != "$from_registry" ]; then
  echo "" >&2
  echo "REFUSING: $registry and the source disagree." >&2
  echo "  in source, not registered:" >&2
  comm -23 <(printf '%s\n' "$from_source") <(printf '%s\n' "$from_registry") | sed 's/^/    /' >&2
  echo "  registered, not in source:" >&2
  comm -13 <(printf '%s\n' "$from_source") <(printf '%s\n' "$from_registry") | sed 's/^/    /' >&2
  echo "" >&2
  echo "A derivation label is a protocol constant. Adding one without" >&2
  echo "registering it is how a codebase ends up with labels nobody can" >&2
  echo "enumerate." >&2
  status=1
fi

# Distinctness, and prefix-freedom outside the grandfathered pairs.
#
# Distinctness is checked on the *raw* list, before `sort -u`: a deduplicated
# list compared with the length of its own set is equal by construction, so
# "two labels are identical" could never fire on it.
#
# Pairs are `prefix|longer`, separated by `;`. Both are spelling facts in the
# registry: the Triple Ratchet's combine and split labels, and the sparse
# ratchet's chain label against the specification's chain-start suffix
# (CR-32).
GRANDFATHERED="Tacenta_CURVE25519_SHA-256_MLKEM1024|Tacenta_CURVE25519_SHA-256_MLKEM1024:Split;Chain|Chain Start"
python3 - "$GRANDFATHERED" "$from_source_raw" <<'PYEOF' || status=1
import collections, sys

allowed = set()
for pair in sys.argv[1].split(";"):
    a, b = pair.split("|")
    allowed.add((a, b))

raw = [l for l in sys.argv[2].splitlines() if l]
dupes = [l for l, n in collections.Counter(raw).items() if n > 1]
if dupes:
    print("REFUSING: the same label value is declared more than once:", file=sys.stderr)
    for d in dupes:
        print(f"    {d!r}", file=sys.stderr)
    print("Two constants with one value are one label with two names, and a", file=sys.stderr)
    print("reader of either cannot tell the derivations apart.", file=sys.stderr)
    sys.exit(1)

labels = sorted(set(raw))
bad = [(x, y) for x in labels for y in labels
       if x != y and y.startswith(x) and (x, y) not in allowed]
if bad:
    print("", file=sys.stderr)
    print("REFUSING: a label is a strict prefix of another, and is not a pair", file=sys.stderr)
    print("the registry grandfathers:", file=sys.stderr)
    for x, y in bad:
        print(f"    {x!r}", file=sys.stderr)
        print(f"      is a prefix of {y!r}", file=sys.stderr)
    print("", file=sys.stderr)
    print("Prefix-freedom is the property distinctness does not give you: two", file=sys.stderr)
    print("labels differing only by a suffix collide once either sits beside", file=sys.stderr)
    print("variable-length data. New labels must be prefix-free.", file=sys.stderr)
    sys.exit(1)

print(f"  {len(labels)} labels, distinct, prefix-free apart from the {len(allowed)} registered pairs")
PYEOF

if [ "$status" -ne 0 ]; then
  exit 1
fi
echo "check-labels: the registry matches the source"
