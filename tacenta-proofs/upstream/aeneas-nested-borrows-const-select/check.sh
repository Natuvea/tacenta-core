#!/usr/bin/env sh
# Assert that the reproducer still reproduces.
#
# Both halves are checked. `control` must translate, so that a regression
# breaking the working case is not mistaken for the bug. `repro` must not, which
# is the bug itself.
#
# A failure on the second check is good news: it means the construct is
# supported and the issue can be closed.
set -eu

out=${1:-out}
cargo build
charon cargo --preset=aeneas

# Aeneas exits non-zero because it cannot translate `repro`. That is expected
# here, so the exit status is not the assertion; the emitted file is.
aeneas -backend lean -dest "$out" nested_borrows_const_select.llbc || true

lean="$out/NestedBorrowsConstSelect.lean"
if [ ! -f "$lean" ]; then
  echo "FAIL: aeneas emitted no Lean file at $lean" >&2
  exit 1
fi

if ! grep -q "def control" "$lean"; then
  echo "FAIL: control is missing from the output" >&2
  exit 1
fi

if grep -A3 "def control" "$lean" | grep -q "sorry"; then
  echo "FAIL: control no longer translates. The control case has regressed." >&2
  exit 1
fi

if ! grep -A3 "def repro" "$lean" | grep -q "sorry"; then
  echo "FIXED: repro translates now. The construct is supported." >&2
  echo "Close the issue and delete this repository." >&2
  exit 1
fi

echo "The reproducer holds: control translates, repro does not."
