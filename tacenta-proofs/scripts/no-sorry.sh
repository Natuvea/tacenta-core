#!/usr/bin/env bash
# Fail if any first-party proof is incomplete.
#
# This asks the compiler rather than grepping the source. Lean emits
# "declaration uses `sorry`" for every incomplete declaration it elaborates, so
# a build log is an exhaustive and authoritative list, where a grep is neither:
# it sees only the files it is pointed at, and matches the word wherever it
# appears, including in prose explaining that there is no sorry.
#
# Third-party sorries are not ours and are not failed on: Aeneas's own library
# ships four. They cannot be filtered by looking for `.lake` in the path,
# because a dependency reports its files relative to its own package root
# (`Aeneas/Std/Slice.lean`, with nothing to distinguish it). So the filter is
# positive, naming the directories that are ours, and anything it does not
# recognise is treated as third-party rather than as first-party.
set -euo pipefail

cd "$(dirname "$0")/.."

fail=0

# check <lake package dir> <regex matching our source paths> <label>
check() {
  local dir="$1" ours="$2" label="$3"
  echo "no-sorry: building $label"
  local log
  log="$(mktemp)"
  # The build must succeed on its own terms first: an incomplete proof is a
  # different failure from one that does not compile, and both must be caught.
  (cd "$dir" && lake build 2>&1) | tee "$log"

  local found
  found="$(grep -E "declaration uses" "$log" | grep -E "$ours" || true)"
  if [ -n "$found" ]; then
    echo "::error::$label contains an incomplete declaration:" >&2
    echo "$found" >&2
    fail=1
  else
    echo "no-sorry: $label is complete"
  fi
  rm -f "$log"
}

check translation '(^|[^/[:alnum:]])Translation/' "the translation and its T1/T3 proofs"
# A module outside the build target is a proof nothing is holding: the log
# scan above can only see what `lake build` elaborated. Assert every
# Translation/*.lean produced a current olean.
bash scripts/check-translation-coverage.sh || fail=1
check .           '(^|[^/[:alnum:]])(Proofs|Model)/' "the model-layer proofs"
# The model package on its own terms, so that `Properties/` is built and
# scanned. Nothing in `Proofs/` imports the forward-secrecy, post-compromise,
# secrecy and authentication theorems, so the check above does not elaborate
# them; this one does, and its regex names `Properties` so a `sorry` in any of
# those five files is failed on.
check ../tacenta-model '(^|[^/[:alnum:]])(Model|Properties)/' "the model and its property theorems"

# Constructs a `sorry` grep cannot see. An `axiom`, an `@[implemented_by]` or
# `@[extern]` (which swap a definition's meaning for a compiled program's), a
# `partial def` or `unsafe` in hand-written Lean each widen the trust base
# without any compiler warning. None is present today; this keeps it so.
# Relative to this package's directory, which the `cd` at the top made the
# working directory; `$(dirname "$0")` would be relative to where the caller
# was, which on the runner is not this package.
bash scripts/check-lean-constructs.sh || fail=1

exit "$fail"
