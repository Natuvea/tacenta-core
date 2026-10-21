#!/usr/bin/env bash
# Fail if `lean_code` in `tacenta-proofs/scripts/attest.py` strips any input differently from the
# character loop it replaced, or if `strip_lean` in `tacenta-proofs/scripts/check-lean-constructs.sh`
# (the other copy of that loop) does.
#
# Every scan of `attest.py` reads Lean through `lean_code`, which blanks comments, strings and char
# literals. It was rewritten for speed (a scan that copies ordinary code a stretch at a time, and a
# per-run memo of its results); `lean-code-differential.py` holds the rewrite to the old loop, kept
# there verbatim, on every tracked Lean file, on hand-written hostile inputs and on seeded random ones,
# and shows it can fail by telling thirteen single edits of the new stripper from the old loop. It reads
# the tree and writes nothing. It needs python3 and git, no Lean toolchain.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
python3 "$here/lean-code-differential.py" "$root"
