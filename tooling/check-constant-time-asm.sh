#!/usr/bin/env bash
# The two hand-written constant-time functions compile to straight-line code.
#
#   bash tooling/check-constant-time-asm.sh
#
# `LIMITATIONS.md` says of the Braid's MAC comparison that "nothing in the
# language stops a compiler from recognising the shape and shortening it",
# and of XEdDSA's key derivation that whether its conditional negation stays
# branch-free "is not a question `tests/timing.rs` can settle". Both are
# questions about generated code, and this reads it. The timing harness
# cannot: a byte-at-a-time short-circuit inside a 3 µs path is below what a
# wall-clock median resolves, and one conditional negation inside a scalar
# multiplication is below it by orders of magnitude (see the two floors in
# `tacenta-core/tests/timing.rs`).
#
# What it does. For the host target and, when installed, for
# x86_64-unknown-linux-gnu and aarch64-unknown-linux-gnu, it builds
# `tacenta-braid` and `tacenta-core` in release with
# `cargo rustc --release --lib -- --emit=asm -C codegen-units=1` (the release
# profile is what ships, one codegen unit so each crate is one file, and
# `--emit=asm` needs no linker, so a target needs only its `rust-std`), then
# extracts from the assembly every function whose symbol names
# `mac_eq` (tacenta_braid) or `calculate_key_pair` (tacenta_core's xeddsa),
# from its label to its `.cfi_endproc`, and:
#
# 1. fails if either symbol is absent -- inlined away, renamed, or dropped --
#    since a function the gate cannot find is a function it is not checking
#    (`calculate_key_pair` carries `#[inline(never)]` for this reason;
#    `mac_eq` has two callers and has stayed out of line so far);
# 2. fails on any conditional-branch mnemonic in the body: on aarch64
#    `b.<cond>`, `cbz`, `cbnz`, `tbz`, `tbnz`; on x86_64 every `j*` except
#    `jmp`. Calls, unconditional branches, returns, and conditional *selects*
#    (`csel`, `cmov`, `sete`) are not branches and pass;
# 3. allows exactly one branch, in `mac_eq` only: the public length compare
#    (`if a.len() != b.len()`), recognised as the first conditional branch in
#    the function when no load from memory has yet run -- the lengths arrive
#    in registers and the bytes do not, so a branch before the first load
#    cannot depend on the bytes. A second branch, or a branch after a load,
#    fails.
#
# It prints, per target and function, the branch count and any allowed one,
# so the record of a run says what was read and not only that it passed.
#
# What a failure means. Not necessarily a leak: an overflow check is a
# compare-and-branch into a panic block, and the workspace's release profile
# keeps overflow checks on. One such branch used to appear in
# `calculate_key_pair`, from `subtle`'s `-(choice as i8)` mask construction;
# it could never be taken (a `Choice` is 0 or 1) but it was a branch, and
# `tacenta-core/Cargo.toml` now compiles `subtle` without overflow checks
# rather than teaching this gate to excuse it. A branch this gate reports is
# for a human to read: the line is printed with the target it came from.
#
# Targets. The host is always checked. Of the two Linux targets, each that
# `rustup target list --installed` lists is checked and each that is not is
# skipped with a line saying so; in CI (`GITHUB_ACTIONS`), where the workflow
# installs the aarch64 target beside the x86_64 host, a run with neither Linux
# target present fails rather than reporting green on the host alone.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root/tacenta-core"

say() { echo "check-constant-time-asm: $*"; }
fail() { echo "check-constant-time-asm: $*" >&2; exit 1; }

host="$(rustc -vV | sed -n 's/^host: //p')"
[ -n "$host" ] || fail "cannot determine the host target from rustc -vV"
installed="$(rustup target list --installed 2>/dev/null || true)"

targets=("$host")
linux_present=0
for t in x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu; do
  if [ "$t" = "$host" ]; then
    linux_present=1
  elif printf '%s\n' "$installed" | grep -qx "$t"; then
    targets+=("$t")
    linux_present=1
  else
    say "$t is not installed, skipping it (rustup target add $t)"
  fi
done
if [ "$linux_present" -eq 0 ]; then
  if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    fail "this is CI and neither Linux target is installed; the workflow's rust job runs 'rustup target add aarch64-unknown-linux-gnu'"
  fi
  say "neither Linux target is installed; checking the host only"
fi

# Read one function out of a .s file and count its conditional branches.
#   analyse <file> <symbol-substring> <arch: x86|aarch64> <allow-length-compare: 0|1>
# Prints one line per branch found (allowed or not) and a final line
# "found=<functions> branches=<disallowed> allowed=<allowed>".
analyse() {
  awk -v sym="$2" -v arch="$3" -v allow="$4" '
    BEGIN { found = 0; inbody = 0; loads = 0; branches = 0; allowed = 0 }
    # A function label: the symbol name (legacy or v0 mangling, with or
    # without the Mach-O underscore) on a line of its own.
    $0 ~ ("^[A-Za-z0-9_.$]*" sym "[A-Za-z0-9_.$]*:$") {
      found++; inbody = 1; loads = 0; name = $0; sub(/:$/, "", name)
      print "  function " name
      next
    }
    inbody && /^[ \t]*\.cfi_endproc/ { inbody = 0; next }
    inbody && /^[ \t]*[.#;@]/ { next }      # directives and comments
    inbody && /^[A-Za-z0-9_.$]+:/ { next }  # local labels
    inbody && NF > 0 {
      mn = $1
      is_branch = 0; is_load = 0
      if (arch == "x86") {
        if (mn ~ /^j/ && mn !~ /^jmp/) is_branch = 1
        # A memory operand is parenthesised in AT&T syntax; `lea` computes an
        # address without touching it.
        else if ($0 ~ /\(/ && mn !~ /^lea/) is_load = 1
      } else {
        if (mn ~ /^b\./ || mn ~ /^(cbz|cbnz|tbz|tbnz)$/) is_branch = 1
        else if (mn ~ /^ld/) is_load = 1
      }
      if (is_branch) {
        if (allow == 1 && branches == 0 && allowed == 0 && loads == 0) {
          allowed++
          print "  allowed (public length compare, before any load): " $0
        } else {
          branches++
          print "  CONDITIONAL BRANCH: " $0
        }
      } else if (is_load) {
        loads++
      }
    }
    END { print "found=" found " branches=" branches " allowed=" allowed }
  ' "$1"
}

status=0
for t in "${targets[@]}"; do
  case "$t" in
    x86_64-*) arch=x86 ;;
    aarch64-*) arch=aarch64 ;;
    *) fail "no branch mnemonics known for target $t" ;;
  esac
  echo "== $t =="
  for crate in tacenta-braid tacenta-core; do
    file_stem="${crate//-/_}"
    rm -f "target/$t/release/deps/${file_stem}"-*.s
    cargo rustc --release --locked -p "$crate" --lib --target "$t" --quiet -- \
      --emit=asm -C codegen-units=1
    files=( "target/$t/release/deps/${file_stem}"-*.s )
    [ "${#files[@]}" -eq 1 ] && [ -f "${files[0]}" ] \
      || fail "$t: expected one assembly file for $crate, found ${#files[@]}"
    case "$crate" in
      tacenta-braid) sym=mac_eq; allow=1; label="tacenta_braid::mac_eq" ;;
      tacenta-core) sym=calculate_key_pair; allow=0; label="tacenta_core::primitives::xeddsa::calculate_key_pair" ;;
    esac
    out="$(analyse "${files[0]}" "$sym" "$arch" "$allow")"
    summary="$(printf '%s\n' "$out" | tail -n 1)"
    printf '%s\n' "$out" | sed '$d'
    found="$(sed -n 's/.*found=\([0-9]*\).*/\1/p' <<<"$summary")"
    branches="$(sed -n 's/.*branches=\([0-9]*\).*/\1/p' <<<"$summary")"
    allowed="$(sed -n 's/.*allowed=\([0-9]*\).*/\1/p' <<<"$summary")"
    if [ "$found" -eq 0 ]; then
      say "$t: $label is not in ${files[0]} -- inlined away or renamed; a function the gate cannot find is one it is not checking" >&2
      status=1
    elif [ "$branches" -ne 0 ]; then
      say "$t: $label has $branches conditional branch(es) beyond the allowed length compare; read them above" >&2
      status=1
    else
      say "$t: $label: 0 conditional branches ($found function(s), $allowed allowed length compare)"
    fi
  done
done

[ "$status" -eq 0 ] || fail "a constant-time function does not compile to straight-line code"
say "every constant-time function compiles to straight-line code on: ${targets[*]}"
