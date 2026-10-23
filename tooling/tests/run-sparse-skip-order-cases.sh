#!/usr/bin/env bash
# The case runner for `tacenta-core/tests/sparse_skip_order.rs`, the public-API tests of a sparse skip's two
# bounds and their order (sparse-pq-ratchet.md, The store also has a total bound). The rows `SK-*` of
# `tooling/gate-mutations.json` edit `tacenta-core/spqr/src/lib.rs` one at a time and run this, so that
# `tooling/mutate-gates.py` shows which test each edit of the library breaks. CI runs the test file itself, in
# `cargo test --locked --workspace`; nothing in CI runs this runner or the mutations.
#
# It runs `cargo test --locked --test sparse_skip_order` in `tacenta-core` and prints, for each test that
# failed, `WRONG  sparse-skip-order: <test> failed` followed by that test's panic output, indented. The name of
# a test is printed only when it failed: the harness takes an edit as caught for its stated reason only when the
# runner's output names the test the row expects, so a runner that echoed every name would let a wrong reason
# through. Cargo's own output is kept out of what this prints, for the same reason.
#
# It fails, never skips: when cargo is not on PATH, when the test does not build, when the run does not report
# exactly the tests named below (a test file compiled out by a cfg runs 0 tests and passes), and when a named
# test does not report `ok`.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
file="$root/tacenta-core/tests/sparse_skip_order.rs"
expected=(
  a_request_past_both_bounds_is_refused_as_too_many_skipped
  the_store_bound_alone_is_refused_as_skipped_store_full
  keys_under_another_epoch_count_against_the_store
  another_epochs_keys_in_the_range_are_neither_purged_nor_free
  a_replacement_at_the_cap_through_the_public_api
)

wrong() {
  echo "WRONG  sparse-skip-order: $1"
}

if [ ! -f "$file" ]; then
  wrong "the test file tacenta-core/tests/sparse_skip_order.rs is missing"
  exit 1
fi
# The file holds exactly the tests named above, so a test added there is added here too, and a test removed
# there cannot pass here unnoticed.
declared=0
while IFS= read -r line; do
  if [ "$line" = "#[test]" ]; then
    declared=$((declared + 1))
  fi
done < "$file"
if [ "$declared" -ne "${#expected[@]}" ]; then
  wrong "the test file declares $declared tests, this runner names ${#expected[@]}"
  exit 1
fi
if ! command -v cargo > /dev/null 2>&1; then
  wrong "cargo is not on PATH, so the tests cannot run (a missing toolchain is a failure, not a skip)"
  exit 1
fi

out="$(mktemp)"
trap 'rm -f "$out"' EXIT
set +e
(cd "$root/tacenta-core" && cargo test --locked --test sparse_skip_order -- --test-threads=1) > "$out" 2>&1
status=$?
set -e

running=""
ok_names=" "
failed_names=" "
while IFS= read -r line; do
  if [[ "$line" =~ ^running\ ([0-9]+)\ tests?$ ]]; then
    running="${running}${BASH_REMATCH[1]} "
  elif [[ "$line" =~ ^test\ ([A-Za-z0-9_]+)\ \.\.\.\ ok$ ]]; then
    ok_names="${ok_names}${BASH_REMATCH[1]} "
  elif [[ "$line" =~ ^test\ ([A-Za-z0-9_]+)\ \.\.\.\ FAILED$ ]]; then
    failed_names="${failed_names}${BASH_REMATCH[1]} "
  fi
done < "$out"

if [ -z "$running" ]; then
  wrong "cargo test did not run the test binary (exit $status); the build failed or the target is missing"
  while IFS= read -r line; do
    case "$line" in
      error*) echo "    $line" ;;
    esac
  done < "$out"
  exit 1
fi
if [ "$running" != "${#expected[@]} " ]; then
  wrong "the run reported 'running ${running% }' tests, not ${#expected[@]}"
  exit 1
fi

failures=0
for name in "${expected[@]}"; do
  case "$failed_names" in
    *" $name "*)
      wrong "$name failed"
      failures=$((failures + 1))
      # The test's own output: the lines from its `---- <name> stdout ----` header to the next header or to the
      # list of failures.
      printing=0
      while IFS= read -r line; do
        if [ "$line" = "---- $name stdout ----" ]; then
          printing=1
          continue
        fi
        if [ "$printing" = 1 ]; then
          case "$line" in
            "---- "*" stdout ----" | "failures:") break ;;
          esac
          echo "    $line"
        fi
      done < "$out"
      ;;
    *)
      case "$ok_names" in
        *" $name "*) ;;
        *)
          wrong "a test the runner names did not report ok or FAILED; is it still in the file? (see the list in this runner)"
          failures=$((failures + 1))
          ;;
      esac
      ;;
  esac
done

if [ "$failures" -ne 0 ]; then
  exit 1
fi
if [ "$status" -ne 0 ]; then
  wrong "cargo test exited $status with every named test ok"
  exit 1
fi
echo "sparse-skip-order: ${#expected[@]} tests ran and passed (the two bounds' order, another epoch's keys, the edge at the cap)"
