#!/usr/bin/env bash
# Negative controls for the production assembly reader's callee allow-list.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
# shellcheck source=../check-constant-time-asm.sh
source "$root/tooling/check-constant-time-asm.sh"

tmp="$(mktemp -d)"
cleanup() { rm -rf "$tmp"; }
trap cleanup EXIT

write_case() {
  cat >"$tmp/case.s" <<EOF
fixture_calculate_key_pair:
  .cfi_startproc
  callq $1
  retq
  .cfi_endproc
EOF
}

summary_for() {
  analyse "$tmp/case.s" calculate_key_pair x86 0 compress | tail -n 1
}

# The exact identifier component `compress` is allowed.
write_case '_RNvCs1234_4demo8compress'
summary="$(summary_for)"
grep -q 'found=1 branches=0 allowed=0 callees=1 bad_callees=0' <<<"$summary" || {
  echo "constant-time asm control: exact allowed identifier did not pass: $summary" >&2
  exit 1
}

# A longer identifier containing the allowed word must be refused. The old
# substring regex admitted this deliberately wrong callee.
write_case '_RNvCs1234_4demo20compress_sign_fixup'
summary="$(summary_for)"
grep -q 'found=1 branches=0 allowed=0 callees=1 bad_callees=1' <<<"$summary" || {
  echo "constant-time asm control: substring lookalike was not refused: $summary" >&2
  exit 1
}

# With no allow-list, even a named callee is refused.
summary="$(analyse "$tmp/case.s" calculate_key_pair x86 0 '' | tail -n 1)"
grep -q 'found=1 branches=0 allowed=0 callees=1 bad_callees=1' <<<"$summary" || {
  echo "constant-time asm control: empty allow-list admitted a callee: $summary" >&2
  exit 1
}

echo "constant-time asm controls: exact identifier passed; substring lookalike and empty allow-list refused"
