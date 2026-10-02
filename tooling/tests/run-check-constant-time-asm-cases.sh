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

# The rest of the reader: the branch counter on both architectures, indirect transfers, the refusal of
# `subtle` and `conditional_` callees, the one allowed length compare, and the rules `main` applies to
# what the reader found. Each case is a fixture the production `analyse` reads; the expected summary
# line is exact, so a case fails when the count it protects changes in either direction.
#   fixture <arch> <allow> <callee-allow> <expected summary> <name>   (the body is read from stdin)
# `fixture` reads its body from a pipe, so it runs in a subshell: the count goes through a file.
: >"$tmp/checked"
fixture() {
  local arch="$1" allow="$2" callees="$3" want="$4" name="$5" got
  { printf 'fixture_calculate_key_pair:\n  .cfi_startproc\n'; cat; printf '  .cfi_endproc\n'; } >"$tmp/body.s"
  got="$(analyse "$tmp/body.s" calculate_key_pair "$arch" "$allow" "$callees" | tail -n 1)"
  if [ "$got" != "$want" ]; then
    echo "constant-time asm control $name ($arch): expected '$want', got '$got'" >&2
    analyse "$tmp/body.s" calculate_key_pair "$arch" "$allow" "$callees" >&2 || true
    exit 1
  fi
  echo . >>"$tmp/checked"
}
none='found=1 branches=0 allowed=0 callees=0 bad_callees=0'
one_branch='found=1 branches=1 allowed=0 callees=0 bad_callees=0'

# x86_64: every `j*` except `jmp` is a conditional branch, a `jmp` to a local label is not.
for mn in jae ja jbe jb jc jcxz jecxz jrcxz je jge jg jle jl jnae jna jnbe jnb jnc jne jnge jng jnle jnl jno jnp jns jnz jo jpe jpo jp js jz; do
  printf '  testq %%rax, %%rax\n  %s .LBB0_2\n  retq\n' "$mn" | fixture x86 0 '' "$one_branch" "x86 $mn counted"
done
printf '  jmp .LBB0_2\n  retq\n' | fixture x86 0 '' "$none" 'x86 jmp to a local label is straight-line'
printf '  cmovne %%rcx, %%rax\n  sete %%dl\n  retq\n' | fixture x86 0 '' "$none" 'x86 cmov and setcc are selects, not branches'
# aarch64: `b.<cond>`, cbz, cbnz, tbz and tbnz are conditional branches; `b` to a local label is not.
for ins in 'b.eq LBB0_2' 'b.ne LBB0_2' 'b.cs LBB0_2' 'b.hs LBB0_2' 'b.cc LBB0_2' 'b.lo LBB0_2' 'b.mi LBB0_2' 'b.pl LBB0_2' 'b.vs LBB0_2' 'b.vc LBB0_2' 'b.hi LBB0_2' 'b.ls LBB0_2' 'b.ge LBB0_2' 'b.lt LBB0_2' 'b.gt LBB0_2' 'b.le LBB0_2' 'cbz x0, LBB0_2' 'cbnz x0, LBB0_2' 'tbz w0, #0, LBB0_2' 'tbnz w0, #0, LBB0_2'; do
  printf '  %s\n  ret\n' "$ins" | fixture aarch64 0 '' "$one_branch" "aarch64 ${ins%% *} counted"
done
printf '  b LBB0_2\n  csel x0, x1, x2, ne\n  cset w8, eq\n  ret\n' | fixture aarch64 0 '' "$none" 'aarch64 b to a local label and csel are straight-line'

# Indirect jumps and calls: the target is decided at run time.
indirect='found=1 branches=1 allowed=0 callees=0 bad_callees=0'
printf '  jmpq *%%rax\n' | fixture x86 0 '' "$indirect" 'x86 indirect jump through a register'
printf '  jmp *.LJTI0_0(,%%rax,8)\n' | fixture x86 0 '' "$indirect" 'x86 jump table'
printf '  callq *%%rax\n  retq\n' | fixture x86 0 '' "$indirect" 'x86 indirect call'
printf '  br x8\n' | fixture aarch64 0 '' "$indirect" 'aarch64 br register'
printf '  blr x8\n  ret\n' | fixture aarch64 0 '' "$indirect" 'aarch64 blr register'

# A named callee on the allow-list passes; `subtle` and `conditional_` callees are refused even when the
# allow-list names them, so the refusal is not an effect of the allow-list.
printf '  callq _ZN4demo9black_box17h0123456789abcdefE\n  retq\n' \
  | fixture x86 0 'black_box' 'found=1 branches=0 allowed=0 callees=1 bad_callees=0' 'subtle::black_box is allowed when listed'
printf '  callq _ZN6subtle21ConditionallySelectable17conditional_selectE\n  retq\n' \
  | fixture x86 0 'conditional_select,ConditionallySelectable,subtle' 'found=1 branches=0 allowed=0 callees=1 bad_callees=1' 'a subtle callee is refused although listed'
printf '  bl _ZN4demo17conditional_negate17h0123456789abcdefE\n  ret\n' \
  | fixture aarch64 0 'conditional_negate' 'found=1 branches=0 allowed=0 callees=1 bad_callees=1' 'a conditional_ callee is refused although listed'
printf '  bl _ZN4demo9black_box17h0123456789abcdefE\n  bl _ZN4demo6subtle9do_selectE\n  ret\n' \
  | fixture aarch64 0 'black_box,do_select' 'found=1 branches=0 allowed=0 callees=2 bad_callees=1' 'a subtle callee beside a black_box callee is refused'

# `mac_eq` may carry exactly one branch, the public length compare, before any load. A second branch, a
# branch after a load, and the same branch in a function that allows none are all refused.
printf '  cmpq %%rsi, %%rcx\n  jne .LBB0_9\n  retq\n' \
  | fixture x86 1 '' 'found=1 branches=0 allowed=1 callees=0 bad_callees=0' 'x86 length compare before any load is allowed'
printf '  cmpq %%rsi, %%rcx\n  jne .LBB0_9\n  testq %%rax, %%rax\n  je .LBB0_8\n  retq\n' \
  | fixture x86 1 '' 'found=1 branches=1 allowed=1 callees=0 bad_callees=0' 'x86 a second branch is refused'
printf '  movzbl (%%rdi), %%eax\n  cmpb (%%rsi), %%al\n  jne .LBB0_9\n  retq\n' \
  | fixture x86 1 '' "$one_branch" 'x86 a branch after a load is refused'
printf '  cmpq %%rsi, %%rcx\n  jne .LBB0_9\n  retq\n' \
  | fixture x86 0 '' "$one_branch" 'x86 the length compare is refused where none is allowed'
printf '  cmp x1, x3\n  b.ne LBB0_9\n  ret\n' \
  | fixture aarch64 1 '' 'found=1 branches=0 allowed=1 callees=0 bad_callees=0' 'aarch64 length compare before any load is allowed'
printf '  ldrb w8, [x0]\n  cmp w8, w9\n  b.ne LBB0_9\n  ret\n' \
  | fixture aarch64 1 '' "$one_branch" 'aarch64 a branch after a load is refused'
# Every load form the counter reads: a pair, an unscaled load, a halfword, a plain `ldr`.
for ld in 'ldp x8, x9, [x0]' 'ldur x8, [x0, #-8]' 'ldrh w8, [x0]' 'ldr x8, [x0]' 'ldrsb x8, [x0]'; do
  printf '  %s\n  cmp x8, x9\n  b.ne LBB0_9\n  ret\n' "$ld" \
    | fixture aarch64 1 '' "$one_branch" "aarch64 a branch after ${ld%% *} is refused"
done
# `lea` computes an address and touches no memory: it does not end the allowed length compare.
printf '  leaq 8(%%rdi), %%rax\n  cmpq %%rsi, %%rcx\n  jne .LBB0_9\n  retq\n' \
  | fixture x86 1 '' 'found=1 branches=0 allowed=1 callees=0 bad_callees=0' 'x86 lea before the length compare is not a load'
# `subtle::black_box` is an identity function that exists to stop the optimiser: allowed when listed, though
# its symbol names `subtle`.
printf '  callq _ZN6subtle9black_box17h0123456789abcdefE\n  retq\n' \
  | fixture x86 0 'black_box' 'found=1 branches=0 allowed=0 callees=1 bad_callees=0' 'a subtle::black_box callee is allowed when listed'

# `analyse` reports no function at all when the symbol is absent; `main` must refuse that, and the other
# findings, and in CI must refuse a run with neither Linux target. These run the production script in a
# disposable tree, with `rustc`, `rustup` and `cargo` replaced by stubs that write the fixture assembly.
sandbox="$tmp/sandbox"
mkdir -p "$sandbox/tooling" "$sandbox/tacenta-core" "$sandbox/bin"
cp "$root/tooling/check-constant-time-asm.sh" "$sandbox/tooling/"
cat >"$sandbox/bin/rustc" <<'STUB'
#!/usr/bin/env bash
[ "$1" = "-vV" ] && { echo "host: ${STUB_HOST:-x86_64-unknown-linux-gnu}"; exit 0; }
exit 1
STUB
cat >"$sandbox/bin/rustup" <<'STUB'
#!/usr/bin/env bash
printf '%s' "${STUB_INSTALLED:-}"
STUB
cat >"$sandbox/bin/cargo" <<'STUB'
#!/usr/bin/env bash
# `cargo clean ...` and `cargo rustc ... --target T -p CRATE ...`: write one assembly file per crate.
[ "$1" = "clean" ] && exit 0
crate="" target=""
while [ $# -gt 0 ]; do
  case "$1" in -p) crate="$2"; shift ;; --target) target="$2"; shift ;; esac
  shift
done
stem="${crate//-/_}"
mkdir -p "target/$target/release/deps"
for n in $(seq 1 "${STUB_FILES:-1}"); do
  cp "$STUB_FIXTURES/$stem.s" "target/$target/release/deps/${stem}-$n.s"
done
STUB
chmod +x "$sandbox/bin/"*

braid_ok() { printf 'fixture_mac_eq:\n  .cfi_startproc\n  cmpq %%rsi, %%rcx\n  jne .LBB0_9\n  retq\n  .cfi_endproc\n'; }
boundary_ok() { printf 'fixture_calculate_key_pair:\n  .cfi_startproc\n  callq _ZN4demo8compress17h0123456789abcdefE\n  retq\n  .cfi_endproc\n'; }
fixtures="$tmp/fixtures"
mkdir -p "$fixtures"
reset_fixtures() { braid_ok >"$fixtures/tacenta_braid.s"; boundary_ok >"$fixtures/tacenta_boundary.s"; }

# main <name> <expected exit: 0|1> <expected text> [VAR=value ...]
main_case() {
  local name="$1" want_rc="$2" needle="$3" out rc
  shift 3
  set +e
  out="$(cd "$sandbox" && env -u GITHUB_ACTIONS PATH="$sandbox/bin:$PATH" STUB_FIXTURES="$fixtures" "$@" \
    bash tooling/check-constant-time-asm.sh 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -ne "$want_rc" ] || ! grep -qF -- "$needle" <<<"$out"; then
    echo "constant-time asm control $name: expected exit $want_rc and '$needle', got exit $rc" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
  echo . >>"$tmp/checked"
}

reset_fixtures
main_case 'clean fixtures on a Linux host are accepted' 0 'every constant-time function compiles to straight-line code' STUB_HOST=x86_64-unknown-linux-gnu
main_case 'no Linux target outside CI checks the host only' 0 'neither Linux target is installed; checking the host only' STUB_HOST=aarch64-apple-darwin
main_case 'no Linux target in CI is a failure' 1 'this is CI and neither Linux target is installed' STUB_HOST=aarch64-apple-darwin GITHUB_ACTIONS=true
main_case 'a Linux target installed in CI is accepted' 0 'every constant-time function compiles to straight-line code' STUB_HOST=aarch64-apple-darwin GITHUB_ACTIONS=true STUB_INSTALLED=aarch64-unknown-linux-gnu
printf 'some_other_function:\n  .cfi_startproc\n  retq\n  .cfi_endproc\n' >"$fixtures/tacenta_braid.s"
main_case 'an absent mac_eq symbol is a failure' 1 'is not in' STUB_HOST=x86_64-unknown-linux-gnu
reset_fixtures
printf 'fixture_calculate_key_pair:\n  .cfi_startproc\n  testq %%rax, %%rax\n  jne .LBB0_2\n  retq\n  .cfi_endproc\n' >"$fixtures/tacenta_boundary.s"
main_case 'a conditional branch in calculate_key_pair is a failure' 1 'conditional branch(es) or indirect jump(s)' STUB_HOST=x86_64-unknown-linux-gnu
reset_fixtures
printf 'fixture_calculate_key_pair:\n  .cfi_startproc\n  callq memcmp\n  retq\n  .cfi_endproc\n' >"$fixtures/tacenta_boundary.s"
main_case 'an unexpected callee is a failure' 1 'the gate refuses or does not know' STUB_HOST=x86_64-unknown-linux-gnu
reset_fixtures
main_case 'two assembly files for one crate are a failure' 1 'expected one assembly file' STUB_HOST=x86_64-unknown-linux-gnu STUB_FILES=2

echo "constant-time asm controls: $(wc -l <"$tmp/checked" | tr -d ' ') further cases (branch counter on x86_64 and aarch64, indirect transfers, subtle and conditional_ callees, the length compare, the rules of main including the CI rule) each gave the expected result"
