#!/usr/bin/env bash
# Negative controls for the differential harness's required-input rule.
#
# `tacenta-test-vectors/runners/rust/tests/differential.rs` compares the Rust core with the model's `difftest`
# executable. A gate that cannot run must not report green where it is meant to run, so the test panics when
# the executable is missing and either `GITHUB_ACTIONS=true` or `TACENTA_DIFFTEST_REQUIRED` is set, and skips
# (printing how to build the model) otherwise. The `vectors` job sets the variable and installs Lean; nothing
# showed that the panic is there. Each case runs the one test with `TACENTA_DIFFTEST` naming a path that is
# not a file, so the model need not be built, and reads the exit status and the message:
#
#   required by the variable       fails, naming the missing executable
#   required by GITHUB_ACTIONS     fails, the same
#   a directory, not a file        fails: only a file counts as the executable
#   neither required               skips, says so, and passes (the local rule, held so that a change that makes
#                                  every run fail is seen as well)
#
# The test is compiled once, which needs the Rust toolchain and the locked dependencies.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$root/tacenta-test-vectors/runners/rust"
test_name=the_model_and_the_core_agree_on_generated_sequences
cargo test --locked --test differential --no-run --quiet
cases=0

run_case() {  # name expected-exit(0|nonzero) needle  VAR=value...
  local name="$1" want="$2" needle="$3" out rc
  shift 3
  set +e
  out="$(env -u GITHUB_ACTIONS -u TACENTA_DIFFTEST_REQUIRED "$@" \
    cargo test --locked --test differential "$test_name" -- --nocapture 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if { [ "$want" = 0 ] && [ "$rc" -ne 0 ]; } || { [ "$want" != 0 ] && [ "$rc" -eq 0 ]; } || ! grep -qF -- "$needle" <<<"$out"; then
    echo "WRONG  differential required-input $name: expected exit $want and '$needle', got exit $rc" >&2
    printf '%s\n' "$out" | tail -15 >&2
    exit 1
  fi
}

missing="$(mktemp -d)/no-such-difftest"
run_case 'required by TACENTA_DIFFTEST_REQUIRED' nonzero "the model's difftest executable is missing" \
  TACENTA_DIFFTEST="$missing" TACENTA_DIFFTEST_REQUIRED=1
run_case 'required by GITHUB_ACTIONS' nonzero "the model's difftest executable is missing" \
  TACENTA_DIFFTEST="$missing" GITHUB_ACTIONS=true
run_case 'a directory is not the executable' nonzero "the model's difftest executable is missing" \
  TACENTA_DIFFTEST="$(dirname "$missing")" TACENTA_DIFFTEST_REQUIRED=1
run_case 'not required: skipped and passed' 0 'differential: no model executable, skipping' \
  TACENTA_DIFFTEST="$missing"

echo "differential-required-input-cases: $cases cases (a missing model executable fails when required by the variable or by CI, and skips otherwise) gave the expected result"
