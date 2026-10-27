#!/usr/bin/env bash
# The case runner for the message size bound's tests (tacenta-spec/protocol/message-format.md, Message size):
# `tacenta-core/tests/message_size.rs` (the sender's rule and the size rule at the real constants, through the
# public entries, with their effects), `message_size_preflight.rs` (the rule's arithmetic on length values, to
# `usize::MAX`), `message_size_alloc.rs` (a size refusal copies nothing) and `fuzz_frame_size_seeds.rs` (the
# `frame_size_boundary` fuzz target's seeds through its entry, every branch of the rule taken). The rows `MS-*` of
# `tooling/gate-mutations.json` edit `tacenta-core/lifecycle/src/lifecycle.rs` and
# `tacenta-core/lifecycle/src/serialization/mod.rs` one at a time and run this, so that
# `tooling/mutate-gates.py` shows which test each edit of the library breaks. CI runs the four test files
# themselves, in `cargo test --locked --workspace`; nothing in CI runs this runner or the mutations.
#
# It runs `cargo test --locked --test <file>` in `tacenta-core` for each file and prints, for each test that
# failed, `WRONG  message-size: <test> failed` followed by that test's panic output, indented. The name of a
# test is printed only when it failed: the harness takes an edit as caught for its stated reason only when the
# runner's output names the test the row expects, so a runner that echoed every name would let a wrong reason
# through. Cargo's own output is kept out of what this prints, for the same reason.
#
# It fails, never skips: when cargo is not on PATH, when a test file does not build, when a run does not report
# exactly the tests named below (a test file compiled out by a cfg runs 0 tests and passes), and when a named
# test does not report `ok`.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
files="message_size message_size_preflight message_size_alloc fuzz_frame_size_seeds"

# The tests each file declares, one name per line. A function rather than arrays named after the files, since
# the bash macOS ships (3.2) has no name references.
expected_tests() {
  case "$1" in
    message_size)
      printf '%s\n' \
        the_constants_are_the_specified_ones \
        a_plaintext_at_the_maximum_round_trips_in_a_ratchet_frame_of_the_maximum \
        a_plaintext_one_over_is_refused_before_any_draw_on_an_established_session \
        a_pending_initiator_sends_the_maximum_as_an_initial_frame_of_the_maximum \
        a_plaintext_one_over_is_refused_before_any_draw_on_a_pending_session \
        the_first_initial_message_is_held_to_the_sender_rule \
        a_ratchet_frame_one_over_is_refused_before_any_draw \
        an_initial_frame_one_over_is_refused_by_the_session_and_the_responder \
        a_rewrapped_repeat_with_an_empty_kem_ciphertext_cannot_carry_an_oversized_ratchet_message \
        an_oversized_input_is_refused_as_too_long_whatever_else_is_wrong_with_it \
        a_frame_the_rule_admits_keeps_its_existing_refusal \
        a_terminal_session_refuses_oversized_inputs_as_too_long
      ;;
    message_size_preflight)
      printf '%s\n' \
        the_value_functions_agree_with_the_reference_at_every_edge \
        the_kem_length_addition_does_not_wrap_at_the_top_of_usize \
        the_three_rules_at_their_edges \
        the_nested_check_does_not_assume_the_kem_length \
        the_size_rule_leaves_kem_length_acceptance_unchanged \
        nested_len_matches_the_reference \
        too_long_matches_the_reference \
        too_long_matches_the_reference_near_the_bounds \
        the_byte_functions_read_what_the_value_functions_take
      ;;
    message_size_alloc)
      printf '%s\n' size_refusals_allocate_nothing_proportional_to_the_frame
      ;;
    fuzz_frame_size_seeds)
      printf '%s\n' the_boundary_seeds_take_every_branch_of_the_size_rule
      ;;
  esac
}

wrong() {
  echo "WRONG  message-size: $1"
}

if ! command -v cargo > /dev/null 2>&1; then
  wrong "cargo is not on PATH, so the tests cannot run (a missing toolchain is a failure, not a skip)"
  exit 1
fi

out="$(mktemp)"
trap 'rm -f "$out"' EXIT
failures=0
total=0
for name_of_file in $files; do
  file="$root/tacenta-core/tests/$name_of_file.rs"
  expected="$(expected_tests "$name_of_file")"
  count=0
  for name in $expected; do
    count=$((count + 1))
  done
  if [ ! -f "$file" ]; then
    wrong "the test file tacenta-core/tests/$name_of_file.rs is missing"
    exit 1
  fi
  # The file holds exactly the tests named above, so a test added there is added here too, and a test
  # removed there cannot pass here unnoticed. A proptest function carries `#[test]` as well.
  declared=0
  while IFS= read -r line; do
    case "$line" in
      "#[test]" | "    #[test]") declared=$((declared + 1)) ;;
    esac
  done < "$file"
  if [ "$declared" -ne "$count" ]; then
    wrong "$name_of_file.rs declares $declared tests, this runner names $count"
    exit 1
  fi

  set +e
  (cd "$root/tacenta-core" && cargo test --locked --test "$name_of_file" -- --test-threads=1) > "$out" 2>&1
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
    wrong "cargo test did not run $name_of_file (exit $status); the build failed or the target is missing"
    while IFS= read -r line; do
      case "$line" in
        error*) echo "    $line" ;;
      esac
    done < "$out"
    exit 1
  fi
  if [ "$running" != "$count " ]; then
    wrong "the run of $name_of_file reported 'running ${running% }' tests, not $count"
    exit 1
  fi

  for name in $expected; do
    case "$failed_names" in
      *" $name "*)
        wrong "$name failed"
        failures=$((failures + 1))
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
            wrong "a test the runner names did not report ok or FAILED: $name; is it still in $name_of_file.rs?"
            failures=$((failures + 1))
            ;;
        esac
        ;;
    esac
  done
  if [ "$failures" -eq 0 ] && [ "$status" -ne 0 ]; then
    wrong "cargo test of $name_of_file exited $status with every named test ok"
    exit 1
  fi
  total=$((total + count))
done

if [ "$failures" -ne 0 ]; then
  exit 1
fi
echo "message-size: $total tests ran and passed (the sender's rule, the size rule and its nested bound, precedence, effects, arithmetic, no copy)"
