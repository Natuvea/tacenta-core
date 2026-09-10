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

# check <lake package dir> <regex matching our source paths> <label> [<keep log at>]
check() {
  local dir="$1" ours="$2" label="$3" keep="${4:-}"
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
  if [ -n "$keep" ]; then
    mv "$log" "$keep"
  else
    rm -f "$log"
  fi
}

translation_log="$(mktemp)"
check translation '(^|[^/[:alnum:]])Translation/' "the translation and its T1/T3 proofs" "$translation_log"
# A module outside the build target is a proof nothing is holding: the log
# scan above can only see what `lake build` elaborated. Assert every
# Translation/*.lean produced a current olean.
bash scripts/check-translation-coverage.sh || fail=1
# The generated files' axiom sets, as the environment has them. The axiom
# audit that ran inside the build above walked the elaborated environment and
# printed every axiom it found in a generated `Translation.Tacenta*` module as
# an `audit-axiom:` line (Lake replays the lines from its log for an
# up-to-date module, so a cached build carries them too). `attest.py --check`
# holds the same files to the recorded manifest by reading their *text*; this
# compares the manifest with what the text elaborated to, so an axiom the
# text scan cannot recognise (one a macro produced, or a command added) and
# a recorded axiom the environment no longer holds both fail here.
if grep -q "audit-axiom:" "$translation_log"; then
  python3 scripts/attest.py --compare-audit "$translation_log" || fail=1
else
  echo "::error::the translation build log carries no audit-axiom lines; the axiom audit did not run" >&2
  fail=1
fi
rm -f "$translation_log"
check .           '(^|[^/[:alnum:]])(Proofs|Model)/' "the model-layer proofs"
# The model package on its own terms, so that `Properties/` is built and
# scanned. Nothing in `Proofs/` imports the forward-secrecy, post-compromise,
# secrecy and authentication theorems, so the check above does not elaborate
# them; this one does, and its regex names `Properties` so a `sorry` in any of
# those five files is failed on.
check ../tacenta-model '(^|[^/[:alnum:]])(Model|Properties)/' "the model and its property theorems"

# Constructs a `sorry` grep cannot see. An `axiom`, an `opaque`, an
# `@[implemented_by]` or `@[extern]` (which swap a definition's meaning for a
# compiled program's), a `partial def` or `unsafe` in hand-written Lean each
# widen the trust base without any compiler warning. The builds above already
# refused them from the elaborated environment (`Model.AxiomAudit`, run by the
# `AxiomAudit` modules in each package); this is the textual second line, and
# the only one that sees `set_option debug.skipKernelTC`. Relative to this
# package's directory, which the `cd` at the top made the working directory;
# `$(dirname "$0")` would be relative to where the caller was, which on the
# runner is not this package.
bash scripts/check-lean-constructs.sh || fail=1

# The audit above walks only what its invoking module imports, and each
# package's audit module carries a hand-maintained import list. A first-party
# module missing from every list is built, scanned and replayed, and never
# audited. This asks Lean for each module's imports and fails if any
# first-party module (the generated `Tacenta*.lean` included, since the
# `audit-axiom:` comparison above sees only the generated modules the audit
# reached) is outside the four audit modules' import closure.
bash scripts/check-audit-reach.sh || fail=1

# Both of the checks above ask what the audit found. This one asks whether the
# audit finds anything: it plants declarations the rule says to refuse, and the
# one shape the rule says to allow, in a throwaway first-party module and
# compares the outcome with the rule. It is the only check that would notice
# the audit going quiet, which matters most for the waiver `compilerTrust`
# grants an unmentioned compiler-trust axiom.
bash scripts/check-audit-negatives.sh || fail=1

# Replay every first-party module through the kernel from its olean.
#
# `lake build` checks a declaration with the kernel when it adds it, unless
# something asked it not to: `set_option debug.skipKernelTC true` adds the
# next declaration on the elaborator's word alone, and nothing in the
# environment records that afterwards, so neither the axiom audit nor the
# pins can see it. `leanchecker`, which ships with the pinned toolchain,
# re-checks each declaration of a module against the kernel starting from the
# module's imports; a declaration the kernel would have refused fails here.
# It is not an external verifier (it is Lean's own kernel), but it is the
# direct defence against environment hacking, and it costs about a minute.
# Four at a time for the translation package, whose modules import Mathlib
# and take a few seconds each to load; the other two are quick in sequence.
replay() {
  local dir="$1" label="$2" jobs="$3"
  shift 3
  echo "no-sorry: replaying $label through the kernel (leanchecker)"
  local failed
  failed="$(cd "$dir" && printf '%s\n' "$@" | xargs -P "$jobs" -n 1 sh -c \
    'lake env leanchecker "$0" > /dev/null 2>&1 || echo "$0"')"
  if [ -n "$failed" ]; then
    echo "::error::the kernel refused a declaration in $label:" >&2
    echo "$failed" >&2
    fail=1
  else
    echo "no-sorry: $label replays clean ($# modules)"
  fi
}
modules() {
  # <dir> <subdir>...: the module name of every .lean under each subdir.
  local dir="$1"; shift
  for sub in "$@"; do
    (cd "$dir" && ls "$sub"/*.lean) | sed 's|/|.|g; s|\.lean$||'
  done
}
replay translation "the translation and its T1/T3 proofs" 4 $(modules translation Translation)
replay .           "the model-layer proofs" 1 $(modules . Proofs)
replay ../tacenta-model "the model and its property theorems" 1 $(modules ../tacenta-model Model Properties)

exit "$fail"
