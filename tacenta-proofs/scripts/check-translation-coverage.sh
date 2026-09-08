#!/usr/bin/env bash
# Fail if any first-party translation module was not elaborated by the build.
#
# `lake build` only elaborates the modules its target selects. A library
# without a glob builds exactly what its root module imports, and a theorem in
# a module the root does not import is claimed in CLAIMS.md, counted by
# attest.py, and never checked by CI. `lakefile.toml` globs `Translation.*`;
# this script is the assertion that the glob keeps covering every file, so a
# module that drops out of the target fails loudly instead of becoming a proof
# nothing is holding.
#
# Run after `lake build` in translation/ (no-sorry.sh does), from the
# tacenta-proofs directory.
set -euo pipefail

cd "$(dirname "$0")/.."

src=translation/Translation
lib=translation/.lake/build/lib/lean/Translation

fail=0
n=0
for f in "$src"/*.lean; do
  m=$(basename "$f" .lean)
  n=$((n + 1))
  if [ ! -f "$lib/$m.olean" ]; then
    echo "::error::translation module not built: Translation/$m.lean has no olean" >&2
    fail=1
  fi
done

# An olean from an earlier build can remain in a warm `.lake` after a module
# leaves the target, so existence alone does not settle membership there. The
# glob itself is the thing that decides membership: it must be exactly the
# non-recursive `Translation.*`, and no module may sit in a subdirectory it
# would not reach. CI runs on a clean checkout, where existence is exact.
if ! grep -q '^globs = \["Translation\.\*"\]' translation/lakefile.toml; then
  echo "::error::translation/lakefile.toml no longer globs exactly Translation.*; coverage cannot be asserted" >&2
  fail=1
fi
if find "$src" -mindepth 2 -name '*.lean' | grep -q .; then
  echo "::error::a .lean file sits in a subdirectory of Translation/, outside the Translation.* glob" >&2
  find "$src" -mindepth 2 -name '*.lean' >&2
  fail=1
fi

# Existence is the right assertion, not mtime: lake decides rebuilds by content
# hash (.trace/.hash), so a module in the target always has a current olean
# after a successful `lake build`, while git checkouts and renames bump .lean
# mtimes without changing content and would make an mtime comparison cry wolf.
if [ "$fail" -eq 0 ]; then
  echo "translation-coverage: all $n Translation/*.lean modules are in the build target and built"
fi
exit "$fail"
