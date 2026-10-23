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
for ins in 'b.eq LBB0_2' 'b.ne LBB0_2' 'b.cs LBB0_2' 'b.hs LBB0_2' 'b.cc LBB0_2' 'b.lo LBB0_2' 'b.mi LBB0_2' 'b.pl LBB0_2' 'b.vs LBB0_2' 'b.vc LBB0_2' 'b.hi LBB0_2' 'b.ls LBB0_2' 'b.ge LBB0_2' 'b.lt LBB0_2' 'b.gt LBB0_2' 'b.le LBB0_2' 'cbz x0, LBB0_2' 'cbnz x0, LBB0_2' 'tbz w0, #0, LBB0_2' 'tbnz w0, #0, LBB0_2' 'bc.eq LBB0_2' 'bc.ne LBB0_2'; do
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

# The key derivation's inventory reader. Each fixture is read by the production `kdf_inventory`; the
# expected items are exact, so a case fails when the reader drops, adds or respells an item.
#   inv_case <arch> <expected inventory> <name>   (the function body is read from stdin)
inv_case() {
  local arch="$1" want="$2" name="$3" got
  { printf '_fixture_kdf:\n  .cfi_startproc\n'; cat; printf '  .cfi_endproc\n'; } >"$tmp/kdf.s"
  got="$(kdf_inventory "$tmp/kdf.s" "$arch" | LC_ALL=C sort)"
  if [ "$got" != "$want" ]; then
    echo "constant-time asm control $name ($arch): expected:" >&2; printf '%s\n' "$want" >&2
    echo "got:" >&2; printf '%s\n' "$got" >&2
    exit 1
  fi
  echo . >>"$tmp/checked"
}
printf '  cmp x0, #64\n  b.ne LBB3_2\n  ret\n' \
  | inv_case aarch64 $'FUNC fixture_kdf\nITEM fixture_kdf branch b.ne L | cmp x0, #64' 'kdf aarch64 branch listed with its compare'
printf '  ldrb w8, [x0]\n  cbz w8, LBB3_2\n  ret\n' \
  | inv_case aarch64 $'FUNC fixture_kdf\nITEM fixture_kdf branch cbz w8, L | ldrb w8, [x0]' 'kdf aarch64 a branch on a loaded byte is listed with the load'
printf '  ldrb w8, [x22, x20]\n  strb w8, [x21, x0]\n  ret\n' \
  | inv_case aarch64 $'FUNC fixture_kdf\nITEM fixture_kdf indexed ldrb w8, [x22, x20]\nITEM fixture_kdf indexed strb w8, [x21, x0]' 'kdf aarch64 register-indexed accesses listed'
printf '  udiv x0, x1, x2\n  ret\n' \
  | inv_case aarch64 $'FUNC fixture_kdf\nITEM fixture_kdf divide udiv x0, x1, x2' 'kdf aarch64 divide listed'
printf '  blr x8\n  bl _memcpy\n  ret\n' \
  | inv_case aarch64 $'FUNC fixture_kdf\nITEM fixture_kdf call _memcpy\nITEM fixture_kdf indirect blr x8' 'kdf aarch64 indirect call and named callee'
printf '  cmpq $63, %%rdi\n  ja .LBB5_44\n  retq\n' \
  | inv_case x86 $'FUNC fixture_kdf\nITEM fixture_kdf branch ja L | cmpq $63, %rdi' 'kdf x86 branch listed with its compare'
# Order matters for the mutation record: the first x86 case a weakened indexed-access regex fails names it.
printf '  movzbl (%%r15,%%rbx), %%eax\n  divq %%rcx\n  retq\n' \
  | inv_case x86 $'FUNC fixture_kdf\nITEM fixture_kdf divide divq %rcx\nITEM fixture_kdf indexed movzbl (%r15,%rbx), %eax' 'kdf x86 indexed load and divide listed'
printf '  movl K(,%%rcx,4), %%eax\n  retq\n' \
  | inv_case x86 $'FUNC fixture_kdf\nITEM fixture_kdf indexed movl K(,%rcx,4), %eax' 'kdf x86 index-only operand listed'
printf '  callq *memcpy@GOTPCREL(%%rip)\n  callq *%%rax\n  jmp *.LJTI0_0(,%%rax,8)\n  retq\n' \
  | inv_case x86 $'FUNC fixture_kdf\nITEM fixture_kdf call memcpy\nITEM fixture_kdf indexed jmp *L(,%rax,8)\nITEM fixture_kdf indirect callq *%rax\nITEM fixture_kdf indirect jmp *L(,%rax,8)\nITEM fixture_kdf table jmp *L(,%rax,8)' 'kdf x86 GOT call named, other indirect transfers and the table listed'
printf '  ldr w8, [x9], x10\n  ret\n' \
  | inv_case aarch64 $'FUNC fixture_kdf\nITEM fixture_kdf indexed ldr w8, [x9], x10' 'kdf aarch64 register post-index listed'
printf '  ldr w8, [sp, x9, lsl #2]\n  ldrb w10, [sp, x11]\n  ret\n' \
  | inv_case aarch64 $'FUNC fixture_kdf\nITEM fixture_kdf indexed ldr w8, [sp, x9, lsl #2]\nITEM fixture_kdf indexed ldrb w10, [sp, x11]' 'kdf aarch64 stack-pointer base with a register offset listed'
printf '  cmp x0, #64\n  bc.ne LBB3_2\n  ret\n' \
  | inv_case aarch64 $'FUNC fixture_kdf\nITEM fixture_kdf branch bc.ne L | cmp x0, #64' 'kdf aarch64 bc.cond branch listed with its compare'

# `analyse` reports no function at all when the symbol is absent; `main` must refuse that, and the other
# findings, and in CI must refuse a run missing either Linux target. These run the production script in a
# disposable tree, with `rustc`, `rustup` and `cargo` replaced by stubs that write the fixture assembly.
sandbox="$tmp/sandbox"
mkdir -p "$sandbox/tooling" "$sandbox/tacenta-core" "$sandbox/bin"
cp "$root/tooling/check-constant-time-asm.sh" "$sandbox/tooling/"
# `rustc +TOOLCHAIN -V` is the pinned toolchain's compiler (`STUB_RUSTC`); plain `rustc -V` the running one.
cat >"$sandbox/bin/rustc" <<'STUB'
#!/usr/bin/env bash
tc=""; case "$1" in +*) tc="${1#+}"; shift ;; esac
[ "$1" = "-vV" ] && { echo "host: ${STUB_HOST:-x86_64-unknown-linux-gnu}"; exit 0; }
[ "$1" = "-V" ] && [ -n "$tc" ] && { echo "${STUB_RUSTC:-rustc fixture 1.0}"; exit 0; }
[ "$1" = "-V" ] && { echo "rustc stable-fixture 9.0"; exit 0; }
exit 1
STUB
# `rustup toolchain list`; `rustup target list --installed` (the running toolchain's targets) and
# `rustup +TOOLCHAIN target list --installed` (the pinned one's, `STUB_KDF_INSTALLED`, by default the same).
cat >"$sandbox/bin/rustup" <<'STUB'
#!/usr/bin/env bash
tc=""; case "$1" in +*) tc="${1#+}"; shift ;; esac
if [ "$1" = "toolchain" ]; then
  printf '%s\n' "${STUB_TOOLCHAINS-stable-x86_64-unknown-linux-gnu (default)
fixture-tc-x86_64-unknown-linux-gnu}"
elif [ -n "$tc" ]; then
  printf '%s' "${STUB_KDF_INSTALLED-${STUB_INSTALLED:-}}"
else
  printf '%s' "${STUB_INSTALLED:-}"
fi
STUB
cat >"$sandbox/bin/cargo" <<'STUB'
#!/usr/bin/env bash
# `cargo [+TOOLCHAIN] clean ...` and `cargo [+TOOLCHAIN] rustc ... --target T -p CRATE ...`: write one
# assembly file per crate, and, when `STUB_LOG` names a file, record which toolchain built which crate.
tc=default; case "$1" in +*) tc="${1#+}"; shift ;; esac
[ "$1" = "clean" ] && exit 0
crate="" target=""
while [ $# -gt 0 ]; do
  case "$1" in -p) crate="$2"; shift ;; --target) target="$2"; shift ;; esac
  shift
done
stem="${crate//-/_}"
[ -n "${STUB_LOG:-}" ] && echo "$crate $target $tc" >>"$STUB_LOG"
mkdir -p "target/$target/release/deps"
files=1; [ "${STUB_FILES_CRATE:-$crate}" = "$crate" ] && files="${STUB_FILES:-1}"
for n in $(seq 1 "$files"); do
  cp "$STUB_FIXTURES/$stem.s" "target/$target/release/deps/${stem}-$n.s"
done
STUB
chmod +x "$sandbox/bin/"*

braid_ok() { printf 'fixture_mac_eq:\n  .cfi_startproc\n  cmpq %%rsi, %%rcx\n  jne .LBB0_9\n  retq\n  .cfi_endproc\n'; }
boundary_ok() { printf 'fixture_calculate_key_pair:\n  .cfi_startproc\n  callq _ZN4demo8compress17h0123456789abcdefE\n  retq\n  .cfi_endproc\n'; }
fixtures="$tmp/fixtures"
mkdir -p "$fixtures"
kdf_ok() { printf '_fixture_kdf:\n  .cfi_startproc\n  cmpq $63, %%rdi\n  ja .LBB5_44\n  retq\n  .cfi_endproc\n'; }
# The reviewed baselines of the sandbox: the fixture's own inventory, per target the cases use.
write_kdf_baselines() {
  local t a
  mkdir -p "$sandbox/tooling/ct-baselines"
  for t in x86_64-unknown-linux-gnu aarch64-apple-darwin aarch64-unknown-linux-gnu; do
    case "$t" in x86_64-*) a=x86 ;; *) a=aarch64 ;; esac
    kdf_inventory "$fixtures/tacenta_kdf.s" "$a" | LC_ALL=C sort >"$sandbox/tooling/ct-baselines/tacenta_kdf-$t.txt"
  done
  echo 'rustc fixture 1.0' >"$sandbox/tooling/ct-baselines/rustc-version.txt"
  echo 'fixture-tc' >"$sandbox/tooling/ct-baselines/rust-toolchain.txt"
}
reset_fixtures() {
  braid_ok >"$fixtures/tacenta_braid.s"; boundary_ok >"$fixtures/tacenta_boundary.s"; kdf_ok >"$fixtures/tacenta_kdf.s"
  write_kdf_baselines
}

# main <name> <expected exit: 0|1> <expected text> [VAR=value ...] [--argument ...]
main_case() {
  local name="$1" want_rc="$2" needle="$3" out rc a
  local -a vars=() args=()
  shift 3
  for a in "$@"; do
    case "$a" in --*) args+=("$a") ;; *) vars+=("$a") ;; esac
  done
  set +e
  out="$(cd "$sandbox" && env -u GITHUB_ACTIONS PATH="$sandbox/bin:$PATH" STUB_FIXTURES="$fixtures" ${vars[@]+"${vars[@]}"} \
    bash tooling/check-constant-time-asm.sh ${args[@]+"${args[@]}"} 2>&1)"
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
# The runner's real shape first: an x86_64 Linux host, where the host alone is a Linux target.
main_case 'in CI, on an x86_64 Linux host, a missing aarch64 target is a failure' 1 'this is CI and aarch64-unknown-linux-gnu is not installed' STUB_HOST=x86_64-unknown-linux-gnu GITHUB_ACTIONS=true STUB_INSTALLED= STUB_KDF_INSTALLED=aarch64-unknown-linux-gnu
main_case 'no Linux target in CI is a failure' 1 'this is CI and x86_64-unknown-linux-gnu is not installed' STUB_HOST=aarch64-apple-darwin GITHUB_ACTIONS=true
main_case 'both Linux targets in CI, on an x86_64 Linux host, are accepted' 0 'every constant-time function compiles to straight-line code, on: x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu' STUB_HOST=x86_64-unknown-linux-gnu GITHUB_ACTIONS=true STUB_INSTALLED=aarch64-unknown-linux-gnu
printf 'some_other_function:\n  .cfi_startproc\n  retq\n  .cfi_endproc\n' >"$fixtures/tacenta_braid.s"
main_case 'an absent mac_eq symbol is a failure' 1 'is not in' STUB_HOST=x86_64-unknown-linux-gnu
reset_fixtures
printf 'fixture_calculate_key_pair:\n  .cfi_startproc\n  testq %%rax, %%rax\n  jne .LBB0_2\n  retq\n  .cfi_endproc\n' >"$fixtures/tacenta_boundary.s"
main_case 'a conditional branch in calculate_key_pair is a failure' 1 'conditional branch(es) or indirect jump(s)' STUB_HOST=x86_64-unknown-linux-gnu
reset_fixtures
printf 'fixture_calculate_key_pair:\n  .cfi_startproc\n  callq memcmp\n  retq\n  .cfi_endproc\n' >"$fixtures/tacenta_boundary.s"
main_case 'an unexpected callee is a failure' 1 'the gate refuses or does not know' STUB_HOST=x86_64-unknown-linux-gnu
reset_fixtures
main_case 'two assembly files for a straight-line crate are a failure' 1 'expected one assembly file for tacenta-braid' STUB_HOST=x86_64-unknown-linux-gnu STUB_FILES=2 STUB_FILES_CRATE=tacenta-braid
reset_fixtures
main_case 'two assembly files for the key derivation are a failure' 1 'expected one assembly file for tacenta-kdf' STUB_HOST=x86_64-unknown-linux-gnu STUB_FILES=2 STUB_FILES_CRATE=tacenta-kdf
reset_fixtures
main_case 'the key derivation at its baseline is accepted' 0 'tacenta_kdf: inventory matches the reviewed baseline (1 items in 1 functions, 1 of them branches)' STUB_HOST=x86_64-unknown-linux-gnu
printf '_fixture_kdf:\n  .cfi_startproc\n  cmpq $63, %%rdi\n  ja .LBB5_44\n  testb %%al, %%al\n  jne .LBB5_45\n  retq\n  .cfi_endproc\n' >"$fixtures/tacenta_kdf.s"
main_case 'a new branch in the key derivation is a failure' 1 'the inventory differs from tooling/ct-baselines/tacenta_kdf-x86_64-unknown-linux-gnu.txt' STUB_HOST=x86_64-unknown-linux-gnu
printf '_fixture_kdf:\n  .cfi_startproc\n  cmpq $64, %%rdi\n  ja .LBB5_44\n  retq\n  .cfi_endproc\n' >"$fixtures/tacenta_kdf.s"
main_case 'a changed compare in the key derivation is a failure' 1 'every new or changed item must be read' STUB_HOST=x86_64-unknown-linux-gnu
reset_fixtures
rm "$sandbox/tooling/ct-baselines/tacenta_kdf-x86_64-unknown-linux-gnu.txt"
main_case 'a missing key-derivation baseline is a failure' 1 'tacenta_kdf: no reviewed baseline' STUB_HOST=x86_64-unknown-linux-gnu
reset_fixtures
printf '_fixture_kdf:\n  .cfi_startproc\n  cmpq $63, %%rdi\n  ja .LBB5_44\n  divq %%rcx\n  retq\n  .cfi_endproc\n' >"$fixtures/tacenta_kdf.s"
write_kdf_baselines
main_case 'a hardware divide in the key derivation is a failure even in its baseline' 1 'hardware divide instruction(s)' STUB_HOST=x86_64-unknown-linux-gnu
reset_fixtures
printf 'some_data:\n  .quad 0\n' >"$fixtures/tacenta_kdf.s"
main_case 'a key derivation with no function is a failure' 1 'tacenta_kdf: no function found' STUB_HOST=x86_64-unknown-linux-gnu
reset_fixtures
main_case 'another compiler than the baselines were read from is a failure' 1 'but the baselines were read from rustc fixture 1.0; the compiler differs' STUB_HOST=x86_64-unknown-linux-gnu 'STUB_RUSTC=rustc other 2.0'
main_case 'a compiler mismatch is named as the cause' 1 'its pinned toolchain is not the compiler its baselines were read from' STUB_HOST=x86_64-unknown-linux-gnu 'STUB_RUSTC=rustc other 2.0'
rm "$sandbox/tooling/ct-baselines/rustc-version.txt"
# Without the pinned toolchain first: with the refusal removed, that run would skip the KDF half and pass.
main_case 'baselines that name no compiler are a failure even without the pinned toolchain' 1 'rustc-version.txt is missing or empty' STUB_HOST=x86_64-unknown-linux-gnu 'STUB_TOOLCHAINS=stable-x86_64-unknown-linux-gnu (default)'
main_case 'baselines that name no compiler are a failure' 1 'rustc-version.txt is missing or empty' STUB_HOST=x86_64-unknown-linux-gnu
reset_fixtures
rm "$sandbox/tooling/ct-baselines/rust-toolchain.txt"
main_case 'baselines that name no toolchain are a failure' 1 'rust-toolchain.txt is missing or empty' STUB_HOST=x86_64-unknown-linux-gnu
reset_fixtures
main_case 'without the pinned toolchain, outside CI, the key derivation is skipped and named' 0 'the key derivation was not checked: the toolchain fixture-tc its baselines were read from is not installed' STUB_HOST=x86_64-unknown-linux-gnu 'STUB_TOOLCHAINS=stable-x86_64-unknown-linux-gnu (default)'
main_case 'without the pinned toolchain, in CI, the run fails' 1 "this is CI and the KDF's toolchain fixture-tc is not installed" STUB_HOST=x86_64-unknown-linux-gnu GITHUB_ACTIONS=true STUB_INSTALLED=aarch64-unknown-linux-gnu 'STUB_TOOLCHAINS=stable-x86_64-unknown-linux-gnu (default)'
main_case 'a Linux target the pinned toolchain lacks is skipped outside CI' 0 'skipping, fixture-tc has no aarch64-unknown-linux-gnu target' STUB_HOST=aarch64-apple-darwin STUB_INSTALLED=aarch64-unknown-linux-gnu STUB_KDF_INSTALLED=
main_case 'a Linux target the pinned toolchain lacks fails in CI' 1 'has no aarch64-unknown-linux-gnu target; the workflow' STUB_HOST=x86_64-unknown-linux-gnu GITHUB_ACTIONS=true STUB_INSTALLED=aarch64-unknown-linux-gnu STUB_KDF_INSTALLED=
# Which toolchain built which crate: the straight-line functions with the running toolchain, the key
# derivation with the pinned one, on every target read.
: >"$tmp/toolchains.log"
main_case 'the straight-line functions and the key derivation are read' 0 'the key derivation matches its reviewed inventory under fixture-tc, on: aarch64-apple-darwin aarch64-unknown-linux-gnu' STUB_HOST=aarch64-apple-darwin STUB_INSTALLED=aarch64-unknown-linux-gnu "STUB_LOG=$tmp/toolchains.log"
want_log=$'tacenta-boundary aarch64-apple-darwin default\ntacenta-boundary aarch64-unknown-linux-gnu default\ntacenta-braid aarch64-apple-darwin default\ntacenta-braid aarch64-unknown-linux-gnu default\ntacenta-kdf aarch64-apple-darwin fixture-tc\ntacenta-kdf aarch64-unknown-linux-gnu fixture-tc'
got_log="$(LC_ALL=C sort "$tmp/toolchains.log")"
if [ "$got_log" != "$want_log" ]; then
  echo "constant-time asm control the toolchain each crate is built with: expected:" >&2
  printf '%s\n' "$want_log" >&2; echo "got:" >&2; printf '%s\n' "$got_log" >&2
  exit 1
fi
echo . >>"$tmp/checked"
main_case 'rewriting the baselines in CI is refused' 1 'is not run in CI' STUB_HOST=x86_64-unknown-linux-gnu GITHUB_ACTIONS=true STUB_INSTALLED=aarch64-unknown-linux-gnu --update-kdf-baseline

echo "constant-time asm controls: $(wc -l <"$tmp/checked" | tr -d ' ') further cases (branch counter on x86_64 and aarch64, indirect transfers, subtle and conditional_ callees, the length compare, the key derivation's inventory reader and baseline rules, the rules of main including the CI rule) each gave the expected result"
