#!/usr/bin/env bash
# The two hand-written constant-time functions compile to straight-line code,
# and the key derivation's compiled control flow and memory indexing are the
# reviewed inventory.
#
#   bash tooling/check-constant-time-asm.sh
#   bash tooling/check-constant-time-asm.sh --update-kdf-baseline   # rewrite the
#        KDF baselines of the targets checked; read the diff before committing
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
# `tacenta-braid` and `tacenta-boundary` in release with
# `cargo rustc --release --lib -- --emit=asm -C codegen-units=1` (the release
# profile is what ships, one codegen unit so each crate is one file, and
# `--emit=asm` needs no linker, so a target needs only its `rust-std`), then
# extracts from the assembly every function whose symbol names
# `mac_eq` (tacenta_braid) or `calculate_key_pair` (tacenta_boundary's xeddsa),
# from its label to its `.cfi_endproc`, and:
#
# 1. fails if either symbol is absent -- inlined away, renamed, or dropped --
#    since a function the gate cannot find is a function it is not checking
#    (`calculate_key_pair` carries `#[inline(never)]` for this reason;
#    `mac_eq` has two callers and has stayed out of line so far);
# 2. fails on any conditional-branch mnemonic in the body: on aarch64
#    `b.<cond>`, `cbz`, `cbnz`, `tbz`, `tbnz`; on x86_64 every `j*` except
#    `jmp`. Conditional *selects* (`csel`, `cmov`, `sete`) are not branches
#    and pass; so do returns, calls to a named symbol, and unconditional
#    jumps to a label or a named symbol;
# 3. fails on an indirect jump -- aarch64 `br <reg>`, x86_64 `jmp *<reg>` or
#    `jmp *<table>(...)` -- and on an indirect call (`blr <reg>`,
#    `call *<reg>`): the target of either is decided at run time, so the
#    reader cannot say what runs next, and a jump table is the compiled form
#    of a `match` on data. `jmp <label>` and `call <symbol>` are named and
#    are read as such;
# 4. reads the *callees*, not only the body. A conditional select that the
#    compiler outlines into a helper is invisible to rule 2, which inspects
#    one function's instructions; so every `bl`/`call`/tail-jump target is
#    collected and printed, and the function fails on a callee whose symbol
#    names `subtle` (other than `subtle::black_box`, an identity function
#    that exists to stop the optimiser) or `conditional_` (a `subtle` select
#    or negation that did not inline), and on any callee outside the
#    function's allow-list. The allow-list is the callee set seen today, by
#    exact Rust identifier component: for `calculate_key_pair`, `Scalar`'s `Neg`,
#    `mul_base`, `compress`, `from_bytes_mod_order`, `black_box`, `zeroize`,
#    `drop_in_place`, and the unwind-path pair `panic_in_cleanup` and
#    `_Unwind_Resume` that the `Zeroizing` drops bring; for `mac_eq`,
#    nothing, since it calls nothing. A new callee is for a human to read
#    (a `memcmp` in `mac_eq` would be the short-circuit this gate exists to
#    catch) and is added here by name once read;
# 5. allows exactly one branch, in `mac_eq` only: the public length compare
#    (`if a.len() != b.len()`), recognised as the first conditional branch in
#    the function when no load from memory has yet run -- the lengths arrive
#    in registers and the bytes do not, so a branch before the first load
#    cannot depend on the bytes. A second branch, or a branch after a load,
#    fails.
#
# What it does not do. It reads the two named functions and the names of what
# they call, one level down; it does not read the callees' bodies. `Scalar`
# negation, `mul_base` and `compress` are curve25519-dalek's, whose
# constant-time discipline is inherited rather than re-established here (as
# `LIMITATIONS.md` says of the whole trusted boundary), and `subtle::black_box`
# is an identity. What the gate settles is that the code *this tree writes*
# -- the loop in `mac_eq`, the conditional negation and the clamping in
# `calculate_key_pair` -- reached the assembler without a data-dependent
# branch, and that nothing it wrote was split into a helper the gate did not
# look at.
#
# It prints, per target and function, the branch count, any allowed branch,
# and the callee list with counts, so the record of a run says what was read
# and not only that it passed.
#
# What a failure means. Not necessarily a leak: an overflow check is a
# compare-and-branch into a panic block, and the workspace's release profile
# keeps overflow checks on. One such branch used to appear in
# `calculate_key_pair`, from `subtle`'s `-(choice as i8)` mask construction;
# it could never be taken (a `Choice` is 0 or 1) but it was a branch, and
# `tacenta-core/Cargo.toml` now compiles `subtle` without overflow checks in
# this workspace's release profile rather than teaching this gate to excuse
# it. A branch this gate reports is for a human to read: the line is printed
# with the target it came from.
#
# Each build starts from `cargo clean -p <crate>` for that target and profile.
# Cargo does not track a `--emit=asm` output: on a warm target directory a
# second `cargo rustc` reports Finished and writes no `.s`, and a gate that
# then read a stale file, or none, would be reporting on a build it did not
# make. Cleaning the one crate costs one crate's compile per target, which is
# what the gate wants to pay: the assembly it reads is the assembly it built.
#
# The key derivation, `tacenta-kdf`. Its SHA-256, HMAC and HKDF are loops: they
# branch on lengths, buffer fill counts and loop counters by design, and this
# workspace's release profile adds an overflow check (a compare and a branch to
# a panic) to every counter step. So the rule above, no conditional branch at
# all, cannot hold, and the crate is held instead to an exact inventory read by
# hand, the method of the independent verified implementation its bodies were
# copied from. For each target it builds `tacenta-kdf` the same way (release,
# `overflow-checks = true` from the workspace profile, one codegen unit,
# `--emit=asm`) and lists, for every function in the crate's assembly:
#
# - each conditional branch, with the instruction before it (so a compare of a
#   secret cannot stand in for a public compare with the same branch);
# - each indirect jump or call (a call through the x86_64 Linux GOT slot of a
#   named symbol is read as a call to that symbol);
# - each jump-table or lookup-table reference;
# - each memory access whose address uses a second register (where a
#   secret-indexed table lookup would show);
# - each named callee, and each hardware divide.
#
# Local labels, crate hashes and symbol hashes are normalised; registers and
# immediates are kept, so a register-allocation change is a changed item. The
# sorted list must equal `tooling/ct-baselines/tacenta_kdf-<target>.txt`
# exactly: a new branch, a changed compare, a new loop, a new callee, a table
# or a vanished function fails, and so does a missing baseline. Any hardware
# divide fails on its own as well. What each baseline item depends on was read
# against the rule in `tooling/ct-baselines/kdf-review-notes.txt` (a branch or
# index may depend on a length, a loop counter, a buffer fill count or a public
# constant, never on a key, message or state byte); the reading was made by a
# tool-assisted session, not by an independent human reader. A change to the
# code or the compiler changes items: `--update-kdf-baseline` rewrites the
# baselines of the targets this run checks, and refuses in CI, and every
# changed item must be read before the result is committed.
#
# What it does not do for the KDF: read the callees' bodies (`memcpy`, `bzero`
# and the panic functions, all of which take public lengths here), cover an
# LTO build (the crate's functions would be inlined into their callers and
# these per-function lists would not apply), or measure time. The Linux
# targets are read as cross-compiled assembly; nothing here has run on Linux
# hardware.
#
# Targets. The host is always checked. Of the two Linux targets, each that
# `rustup target list --installed` lists is checked and each that is not is
# skipped with a line saying so; in CI (`GITHUB_ACTIONS`), where the workflow
# installs the aarch64 target beside the x86_64 host, a run with neither Linux
# target present fails rather than reporting green on the host alone.
set -euo pipefail
shopt -s nullglob

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

say() { echo "check-constant-time-asm: $*"; }
fail() { echo "check-constant-time-asm: $*" >&2; exit 1; }

# Read one function out of a .s file: count its conditional branches and
# indirect jumps, and collect its callees.
#   analyse <file> <symbol-substring> <arch: x86|aarch64> <allow-length-compare: 0|1> <comma-separated-exact-callee-identifiers>
# Prints one line per branch found (allowed or not), one per callee, and a
# final line "found=<functions> branches=<disallowed> allowed=<allowed>
# callees=<distinct> bad_callees=<refused>". An empty allow-list allows no
# callee at all. Rust v0 and legacy mangling both length-prefix identifier
# components, so `8compress` admits the identifier `compress` while refusing
# `compress_sign_fixup`; unmangled external symbols must match exactly.
analyse() {
  awk -v sym="$2" -v arch="$3" -v allow="$4" -v callee_allow="$5" '
    BEGIN {
      found = 0; inbody = 0; loads = 0; branches = 0; allowed = 0; ncallees = 0; bad = 0
      nallowed_callees = split(callee_allow, allowed_callees, ",")
    }
    function callee_is_allowed(c, i, identifier, token) {
      if (callee_allow == "") return 0
      for (i = 1; i <= nallowed_callees; i++) {
        identifier = allowed_callees[i]
        if (c == identifier) return 1
        token = length(identifier) identifier
        if (index(c, token) != 0) return 1
      }
      return 0
    }
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
      is_branch = 0; is_load = 0; is_transfer = 0
      if (arch == "x86") {
        if (mn ~ /^j/ && mn !~ /^jmp/) is_branch = 1
        else if (mn ~ /^(jmp|call)/) is_transfer = 1
        # A memory operand is parenthesised in AT&T syntax; `lea` computes an
        # address without touching it.
        else if ($0 ~ /\(/ && mn !~ /^lea/) is_load = 1
      } else {
        if (mn ~ /^b\./ || mn ~ /^(cbz|cbnz|tbz|tbnz)$/) is_branch = 1
        else if (mn ~ /^(b|bl|br|blr)$/) is_transfer = 1
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
      } else if (is_transfer) {
        # The operand: strip the AT&T `*` and any `@PLT` / `@GOTPCREL(%rip)`
        # suffix, which name a symbol through a table but still name it.
        op = $2; sub(/^\*/, "", op); sub(/@[A-Za-z]+(\([^)]*\))?$/, "", op)
        if (op ~ /^%/ || op ~ /\(/ || op ~ /^[xw][0-9]+$/ || op ~ /^(lr|sp)$/) {
          # A register or a computed address: the target is not in the text.
          branches++
          if (mn ~ /^(bl|blr|call)/) print "  INDIRECT CALL: " $0
          else print "  INDIRECT JUMP: " $0
        } else if (op ~ /^\.?L[A-Za-z]*[0-9]/) {
          # `jmp .LBB0_3` / `b LBB0_3`: a local label, straight-line control
          # flow within the function.
        } else {
          # A named symbol: a call, or a tail call. Read it as a callee.
          if (!(op in callees)) { order[++ncallees] = op }
          callees[op]++
        }
      } else if (is_load) {
        loads++
      }
    }
    END {
      for (i = 1; i <= ncallees; i++) {
        c = order[i]
        if ((c ~ /subtle/ && c !~ /black_box/) || c ~ /conditional_/) {
          bad++; print "  REFUSED CALLEE (subtle or conditional_ outlined): " callees[c] " x " c
        } else if (callee_is_allowed(c)) {
          print "  callee: " callees[c] " x " c
        } else {
          bad++; print "  UNEXPECTED CALLEE (not on the allow-list): " callees[c] " x " c
        }
      }
      print "found=" found " branches=" branches " allowed=" allowed " callees=" ncallees " bad_callees=" bad
    }
  ' "$1"
}

# The inventory of one assembly file, every function in it.
#   kdf_inventory <file> <arch: x86|aarch64>
# Prints `FUNC <name>` per function and `ITEM <name> <kind> <signature>` per
# item (kinds: branch, indirect, table, indexed, call, divide), unsorted.
kdf_inventory() {
  awk -v arch="$2" '
    function norm(t) {
      gsub(/[ \t]+/, " ", t); sub(/^ /, "", t); sub(/ $/, "", t)
      gsub(/\.?L(BB|tmp|JTI|CPI|loh)[0-9_]+/, "L", t)
      gsub(/lCPI[0-9_]+/, "L", t)
      gsub(/l_anon\.[0-9a-f]+\.[0-9]+/, "l_anon", t)
      gsub(/Cs[0-9A-Za-z]+_/, "Cs_", t)
      gsub(/17h[0-9a-f]+E/, "17hE", t)
      return t
    }
    function emit(kind, sig) { print "ITEM " fname " " kind " " sig }
    BEGIN { inbody = 0; pending = ""; prev = "" }
    # A function: a label that is not a local one, followed by .cfi_startproc.
    /^[A-Za-z0-9_.$]+:$/ && $0 !~ /^(\.?L|l_|ltmp|lCPI)/ { pending = $0; sub(/:$/, "", pending); next }
    /^[ \t]*\.cfi_startproc/ {
      if (pending != "") { fname = norm(pending); sub(/^_+/, "", fname); print "FUNC " fname; inbody = 1; prev = "(entry)" }
      next
    }
    inbody && /^[ \t]*\.cfi_endproc/ { inbody = 0; pending = ""; next }
    inbody && /^[ \t]*[.#;@]/ { next }
    inbody && /^[A-Za-z0-9_.$]+:/ { next }
    inbody && NF > 0 {
      line = $0; sub(/[ \t]*(;|\/\/).*$/, "", line)
      if (arch == "x86") sub(/[ \t]*#.*$/, "", line)
      mn = $1; ins = norm(line)
      if (arch == "x86") {
        if ((mn ~ /^j/ && mn !~ /^jmp/) || mn ~ /^loop/) emit("branch", ins " | " prev)
        else if (mn ~ /^(jmp|call)/) {
          op = $2
          if (op ~ /^\*/) {
            if (op ~ /^\*[A-Za-z_$][A-Za-z0-9_.$]*@GOTPCREL\(%rip\)$/) { o = op; sub(/^\*/, "", o); sub(/@.*/, "", o); emit("call", norm(o)) }
            else emit("indirect", ins)
          } else if (op !~ /^\.?L[A-Za-z]*[0-9]/) { o = op; sub(/@[A-Za-z]+$/, "", o); emit("call", norm(o)) }
        }
        if (mn ~ /^(div|idiv)/) emit("divide", ins)
        if (line ~ /\(%[a-z0-9]+,%[a-z0-9]+/) emit("indexed", ins)
      } else {
        if (mn ~ /^b\./ || mn ~ /^(cbz|cbnz|tbz|tbnz)$/) emit("branch", ins " | " prev)
        else if (mn ~ /^(br|blr)$/) emit("indirect", ins)
        else if (mn ~ /^(b|bl)$/ && $2 !~ /^\.?L[A-Za-z]*[0-9]/) emit("call", norm($2))
        if (mn ~ /^(udiv|sdiv)$/) emit("divide", ins)
        if (line ~ /\[[xw][0-9]+, *[xw][0-9]+/) emit("indexed", ins)
      }
      if (line ~ /(LJTI|switch\.table)/) emit("table", ins)
      prev = ins
    }
  ' "$1"
}

main() {
  local update_kdf=0 arg
  for arg in "$@"; do
    case "$arg" in
      --update-kdf-baseline) update_kdf=1 ;;
      *) fail "unknown argument: $arg" ;;
    esac
  done
  if [ "$update_kdf" -eq 1 ] && [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    fail "--update-kdf-baseline rewrites reviewed baselines; it is not run in CI"
  fi
  cd "$root/tacenta-core"

  local host installed linux_present t arch crate file_stem sym allow label
  local callee_allow out summary found branches allowed callees bad_callees
  local status=0
  local -a targets files

  host="$(rustc -vV | sed -n 's/^host: //p')"
  [ -n "$host" ] || fail "cannot determine the host target from rustc -vV"
  installed="$(rustup target list --installed 2>/dev/null || true)"

  targets=("$host")
  linux_present=0
  for t in x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu; do
    if [ "$t" = "$host" ]; then
      linux_present=1
    elif grep -qx "$t" <<<"$installed"; then
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

  for t in "${targets[@]}"; do
  case "$t" in
    x86_64-*) arch=x86 ;;
    aarch64-*) arch=aarch64 ;;
    *) fail "no branch mnemonics known for target $t" ;;
  esac
  echo "== $t =="
  for crate in tacenta-braid tacenta-boundary; do
    file_stem="${crate//-/_}"
    # Start from nothing for this crate, target and profile: see the header
    # on why a warm target directory otherwise yields no assembly.
    cargo clean --release --target "$t" -p "$crate" --quiet
    rm -f "target/$t/release/deps/${file_stem}"-*.s
    cargo rustc --release --locked -p "$crate" --lib --target "$t" --quiet -- \
      --emit=asm -C codegen-units=1
    files=( "target/$t/release/deps/${file_stem}"-*.s )
    [ "${#files[@]}" -eq 1 ] \
      || fail "$t: expected one assembly file for $crate under target/$t/release/deps, found ${#files[@]} (${files[*]:-none})"
    case "$crate" in
      tacenta-braid)
        sym=mac_eq; allow=1; label="tacenta_braid::mac_eq"
        callee_allow="" ;;
      tacenta-boundary)
        sym=calculate_key_pair; allow=0; label="tacenta_boundary::xeddsa::calculate_key_pair"
        callee_allow='Neg,neg,mul_base,compress,from_bytes_mod_order,black_box,zeroize,drop_in_place,drop_glue,panic_in_cleanup,_Unwind_Resume,__Unwind_Resume' ;;
    esac
    out="$(analyse "${files[0]}" "$sym" "$arch" "$allow" "$callee_allow")"
    summary="$(printf '%s\n' "$out" | tail -n 1)"
    printf '%s\n' "$out" | sed '$d'
    found="$(sed -n 's/.*found=\([0-9]*\).*/\1/p' <<<"$summary")"
    branches="$(sed -n 's/.*branches=\([0-9]*\).*/\1/p' <<<"$summary")"
    allowed="$(sed -n 's/.*allowed=\([0-9]*\).*/\1/p' <<<"$summary")"
    callees="$(sed -n 's/.* callees=\([0-9]*\).*/\1/p' <<<"$summary")"
    bad_callees="$(sed -n 's/.*bad_callees=\([0-9]*\).*/\1/p' <<<"$summary")"
    if [ "$found" -eq 0 ]; then
      say "$t: $label is not in ${files[0]} -- inlined away or renamed; a function the gate cannot find is one it is not checking" >&2
      status=1
    elif [ "$branches" -ne 0 ]; then
      say "$t: $label has $branches conditional branch(es) or indirect jump(s) beyond the allowed length compare; read them above" >&2
      status=1
    elif [ "$bad_callees" -ne 0 ]; then
      say "$t: $label calls $bad_callees function(s) the gate refuses or does not know; read them above and, if they are what they say, add them to the allow-list by name" >&2
      status=1
    else
      say "$t: $label: 0 conditional branches, 0 indirect jumps ($found function(s), $allowed allowed length compare, $callees distinct callee(s), all on the allow-list)"
    fi
  done

  # The key derivation: the whole crate's inventory against its reviewed baseline.
  local kdf_file kdf_base kdf_inv divides
  cargo clean --release --target "$t" -p tacenta-kdf --quiet
  rm -f "target/$t/release/deps/tacenta_kdf"-*.s
  cargo rustc --release --locked -p tacenta-kdf --lib --target "$t" --quiet -- \
    --emit=asm -C codegen-units=1
  files=( "target/$t/release/deps/tacenta_kdf"-*.s )
  [ "${#files[@]}" -eq 1 ] \
    || fail "$t: expected one assembly file for tacenta-kdf under target/$t/release/deps, found ${#files[@]} (${files[*]:-none})"
  kdf_file="${files[0]}"
  kdf_inv="$(kdf_inventory "$kdf_file" "$arch" | LC_ALL=C sort)"
  kdf_base="$root/tooling/ct-baselines/tacenta_kdf-$t.txt"
  divides="$(grep -c '^ITEM [^ ]* divide ' <<<"$kdf_inv" || true)"
  if ! grep -q '^FUNC ' <<<"$kdf_inv"; then
    say "$t: tacenta_kdf: no function found in $kdf_file; a crate the gate cannot read is a crate it is not checking" >&2
    status=1
  elif [ "$divides" -ne 0 ]; then
    say "$t: tacenta_kdf: $divides hardware divide instruction(s):" >&2
    grep '^ITEM [^ ]* divide ' <<<"$kdf_inv" | sed 's/^/    /' >&2
    status=1
  elif [ "$update_kdf" -eq 1 ]; then
    mkdir -p "$(dirname "$kdf_base")"
    printf '%s\n' "$kdf_inv" >"$kdf_base"
    say "$t: tacenta_kdf: wrote $(grep -c '^ITEM' "$kdf_base") items to ${kdf_base#"$root"/}; read every changed item before committing"
  elif [ ! -f "$kdf_base" ]; then
    say "$t: tacenta_kdf: no reviewed baseline ${kdf_base#"$root"/}; read the inventory and write one with --update-kdf-baseline" >&2
    status=1
  elif ! diff -u "$kdf_base" <(printf '%s\n' "$kdf_inv") >/dev/null; then
    say "$t: tacenta_kdf: the inventory differs from ${kdf_base#"$root"/}; every new or changed item must be read:" >&2
    diff -u "$kdf_base" <(printf '%s\n' "$kdf_inv") | sed -n '3,$p' | head -60 | sed 's/^/    /' >&2
    status=1
  else
    say "$t: tacenta_kdf: inventory matches the reviewed baseline ($(grep -c '^ITEM' <<<"$kdf_inv") items in $(grep -c '^FUNC' <<<"$kdf_inv") functions, $(grep -c '^ITEM [^ ]* branch ' <<<"$kdf_inv") of them branches)"
  fi
  done

  [ "$status" -eq 0 ] || fail "a constant-time function does not compile to straight-line code, or the key derivation's inventory is not the reviewed one"
  say "every constant-time function compiles to straight-line code, and the key derivation matches its reviewed inventory, on: ${targets[*]}"
}

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  main "$@"
fi
