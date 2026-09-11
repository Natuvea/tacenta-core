#!/bin/sh
# Assemble `tacenta-core/braid-unit`, the Braid-and-erasure translation unit,
# from the two leaf crates' sources.
#
# ## Why it exists
#
# `tacenta-braid` calls `tacenta-erasure` for every codeword it sends or
# collects and for every coder in its persisted state. Charon translates one
# crate at a time, so in a translation of the Braid on its own every erasure
# type and operation is an opaque axiom -- twenty-three of them -- and the
# Braid's proofs have to assume them: total (`BraidT1`'s `EncoderNewTotal` and
# six more) and agreeing with the model (`BraidT3`'s `ErasureAgrees` and
# `ErasureCloneAgrees`). That is so although the erasure crate is translated
# and proved on its own; the two translations simply never meet. Compiled as
# one crate, the two leaves are one translation: the erasure types are real
# types and its operations real bodies, so those assumptions can become
# theorems about the same code.
#
# ## What the unit is, and what it is not
#
# The same arrangement, for the same reasons and held by the same checks, as
# `assemble-triple-unit.sh`, whose header says at length what a translation
# unit is and is not; all of it applies here. In short: it is the same source
# text compiled as one crate, it is never shipped and nothing links against it,
# and the gap between it and the shipping crate graph is a crate boundary,
# which `LIMITATIONS.md` records. The erasure leaf is loaded with `#[path]`.
# The Braid's `lib.rs` is copied with one inserted `use`, because it names
# `tacenta_erasure` by crate name and inside the unit that is a sibling module;
# this script verifies the inserted lines are the entire difference.
#
# The KEM stays outside. `tacenta-kem` wraps a third-party ML-KEM
# implementation and is a trusted primitive zone in `attest.py`, not a verified
# one, so its declarations are opaque in the unit exactly as they are in the
# Braid's own translation.
#
# ## Usage
#
#   scripts/assemble-braid-unit.sh            write tacenta-core/braid-unit
#   scripts/assemble-braid-unit.sh --check    fail if the tree differs from it
#
# Deterministic: the same two leaves produce byte-identical output. `--check`
# assembles into a temporary directory and diffs, and needs no Charon, Aeneas or
# Lean. `scripts/run-aeneas.sh` runs the first form before it translates.
set -eu

here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
core="$root/tacenta-core"

check=0
if [ $# -gt 0 ]; then
  case "$1" in
    --check) check=1 ;;
    *) echo "usage: assemble-braid-unit.sh [--check]" >&2; exit 2 ;;
  esac
fi

# One trap for everything this script may have to remove (see the Triple unit's
# script for why two traps would not compose).
unit_tmp=""
stripped=""
inject_file=""
note_file=""
cleanup() {
  [ -n "$unit_tmp" ] && rm -rf "$unit_tmp"
  [ -n "$stripped" ] && rm -f "$stripped"
  [ -n "$inject_file" ] && rm -f "$inject_file"
  [ -n "$note_file" ] && rm -f "$note_file"
  return 0
}
trap cleanup EXIT INT TERM

unit="$core/braid-unit"
if [ "$check" -eq 1 ]; then
  unit_tmp=$(mktemp -d)
  unit="$unit_tmp"
fi

mkdir -p "$unit/src"

generated_note() {
  comment="$1"
  cat <<EOF
$comment GENERATED FILE -- DO NOT EDIT.
$comment
$comment Written by tacenta-proofs/scripts/assemble-braid-unit.sh from the two
$comment leaf crates. Edit the leaves; run the script. An edit here is undone by
$comment the next run and refused by \`assemble-braid-unit.sh --check\`, which
$comment tooling/ci.sh runs, and by \`attest.py --check\`, which holds this crate
$comment to the hashes of the script and of both leaf trees.
EOF
}

# ---------------------------------------------------------------------------
# Cargo.toml
# ---------------------------------------------------------------------------
#
# A workspace member, so the unit resolves against the same `Cargo.lock` and
# compiles under the same `[profile]` tables as the leaves (`overflow-checks`
# above all). The dependencies are the union of the two leaves', less the
# erasure crate, whose source is in the unit: the trusted key-derivation and
# KEM boundaries, `zeroize` and `rand_core`. The Braid's `conformance` feature is
# declared so the copied leaf's `cfg(feature = "conformance")` items resolve as
# they do in the leaf; like every translation, the unit is built without it.
{
  generated_note "#"
  cat <<'EOF'

[package]
name = "tacenta-braid-unit"
license = "Apache-2.0"
version = "0.0.0"
edition = "2024"
rust-version = "1.87"
description = "The ML-KEM Braid and its erasure codec compiled as one crate, so Charon translates the Braid with the codec's bodies rather than over opaque axioms. Generated; not shipped."
publish = false

[dependencies]
tacenta-kdf = { path = "../kdf" }
tacenta-kem = { path = "../kem" }
zeroize = { version = "1", features = ["derive"] }
rand_core = "0.6"

[features]
conformance = []

[lib]
test = false
doctest = false
EOF
} > "$unit/Cargo.toml"

# ---------------------------------------------------------------------------
# src/lib.rs
# ---------------------------------------------------------------------------
#
# `pub mod` and `#[cfg(not(test))]` for the reasons the Triple unit's script
# gives: a private wrapper would make the surface dead code, and the leaves'
# test modules must not be compiled a second time here.
{
  generated_note "//"
  cat <<'EOF'

//! `tacenta-braid-unit`: the ML-KEM Braid and its erasure codec compiled as one
//! crate.
//!
//! The two modules below are the two leaf `lib.rs` files. The erasure codec is
//! the leaf file itself, reached with `#[path]`; the Braid is a copy of
//! `tacenta-core/braid/src/lib.rs` carrying a generated header and one inserted
//! `use`, and identical to the leaf once those are removed, which the assembly
//! script checks by removing them. Nothing here adds, removes or reorders a
//! declaration.
//!
//! Nothing links against this crate. It exists so that Charon sees the Braid
//! and the erasure codec in one translation unit, where the codec's operations
//! are bodies rather than axioms.

// Each leaf keeps its own `#![forbid(unsafe_code)]`, which bounds its module.
// The root carries one too, for the few lines that are this file.
#![forbid(unsafe_code)]

#[cfg(not(test))]
#[path = "../../erasure/src/lib.rs"]
pub mod tacenta_erasure;

#[cfg(not(test))]
pub mod tacenta_braid;
EOF
} > "$unit/src/lib.rs"

# ---------------------------------------------------------------------------
# src/tacenta_braid.rs
# ---------------------------------------------------------------------------
#
# The one copied leaf. The inserted block goes after the last inner attribute,
# and the rest of the file is the leaf byte for byte.
leaf="$core/braid/src/lib.rs"
copy="$unit/src/tacenta_braid.rs"

header_end=$(awk '
  BEGIN { last = 0; in_attr = 0; depth = 0 }
  {
    if (in_attr) {
      depth += gsub(/\[/, "["); depth -= gsub(/\]/, "]")
      if (depth <= 0) { in_attr = 0; last = NR }
      next
    }
    if ($0 ~ /^[[:space:]]*#!\[/) {
      depth = gsub(/\[/, "[") - gsub(/\]/, "]")
      if (depth <= 0) { last = NR } else { in_attr = 1 }
      next
    }
    if ($0 ~ /^[[:space:]]*\/\/!/) { last = NR; next }
    if ($0 ~ /^[[:space:]]*\/\// || $0 ~ /^[[:space:]]*$/) { next }
    exit
  }
  END { print last }
' "$leaf")

if [ "$header_end" -eq 0 ]; then
  echo "assemble-braid-unit: no inner attribute block in $leaf; refusing to" >&2
  echo "  guess where the inserted \`use\` may go." >&2
  exit 1
fi

inject_block() {
  cat <<'EOF'

// Inserted by tacenta-proofs/scripts/assemble-braid-unit.sh. These lines are
// the *entire* difference between this file and
// tacenta-core/braid/src/lib.rs; everything above and below is that file byte
// for byte, and the script verifies it by finding these lines again, deleting
// them, and diffing against the leaf.
//
// In the shipping crate graph `tacenta_erasure` is a dependency, and its name
// comes from the extern prelude. Here it is a sibling module of this one, and a
// path's first segment is resolved in the current module and the extern
// prelude, never in the parent, so the name has to be brought into scope.
// Every path below then reads exactly as it does in the leaf.
use crate::tacenta_erasure;
EOF
}
inject_lines=$(inject_block | wc -l | tr -d ' ')

{
  generated_note "//"
  echo ""
  sed -n "1,${header_end}p" "$leaf"
  inject_block
  sed -n "$((header_end + 1)),\$p" "$leaf"
} > "$copy"

# The byte-identity check, read back from the file: match the generated header
# at the front, find the inserted block by its text (exactly once), delete
# both, and diff the rest against the leaf. The Triple unit's script explains
# why the block is located by content rather than by the line ranges the write
# used.
note_file=$(mktemp)
{ generated_note "//"; echo ""; } > "$note_file"
stripped=$(mktemp)
inject_file=$(mktemp)
inject_block > "$inject_file"

if ! python3 - "$copy" "$inject_file" "$note_file" "$stripped" <<'PYEOF'; then
import sys
copy, inject_file, note_file, out = sys.argv[1:]
copy_lines = open(copy).read().splitlines(keepends=True)
inject = open(inject_file).read().splitlines(keepends=True)
note = open(note_file).read().splitlines(keepends=True)

if copy_lines[:len(note)] != note:
    sys.stderr.write(
        f"assemble-braid-unit: ERROR: {copy} does not begin with the generated "
        f"header this script writes.\n")
    sys.exit(1)
rest = copy_lines[len(note):]

hits = [i for i in range(len(rest) - len(inject) + 1)
        if rest[i:i + len(inject)] == inject]
if len(hits) != 1:
    sys.stderr.write(
        f"assemble-braid-unit: ERROR: the inserted block occurs {len(hits)} "
        f"times in {copy} after its header; expected exactly one.\n")
    sys.exit(1)
at = hits[0]

open(out, "w").writelines(rest[:at] + rest[at + len(inject):])
sys.exit(0)
PYEOF
  exit 1
fi

if ! diff -q "$stripped" "$leaf" > /dev/null; then
  echo "assemble-braid-unit: ERROR: the copy is not the leaf plus the inserted" >&2
  echo "  block. Removing the generated header and the inserted lines from" >&2
  echo "  $copy did not reproduce $leaf:" >&2
  diff "$stripped" "$leaf" | head -20 >&2
  exit 1
fi

# Where the block landed, which byte identity says nothing about: the inserted
# `use` must follow every top-level inner attribute and inner doc comment
# (rustc refuses otherwise, E0753). The scan runs from the `use` to the first
# item and no further, for the reasons the Triple unit's script gives.
use_line=$(grep -n '^use crate::tacenta_erasure;$' "$copy" | cut -d: -f1)
if [ "$(echo "$use_line" | wc -l | tr -d ' ')" != 1 ] || [ -z "$use_line" ]; then
  echo "assemble-braid-unit: ERROR: expected exactly one inserted \`use\` line in" >&2
  echo "  $copy; found $(echo "$use_line" | wc -w | tr -d ' ')." >&2
  exit 1
fi
late=$(awk -v start="$use_line" '
  NR <= start { next }
  /^(#!\[|\/\/!)/ { print NR ": " $0; if (++n == 3) exit; next }
  /^[[:space:]]*$/ { next }
  /^[[:space:]]*\/\// { next }
  /^#\[/ { next }
  { exit }
' "$copy")
if [ -n "$late" ]; then
  echo "assemble-braid-unit: ERROR: the inserted \`use\` landed before a top-level" >&2
  echo "  inner attribute in $copy, which rustc refuses (E0753). The leaf's" >&2
  echo "  header run was read as ending at line $header_end; it ends later." >&2
  echo "$late" | sed 's/^/    line /' >&2
  exit 1
fi

rm -f "$stripped" "$inject_file" "$note_file"
stripped=""
inject_file=""
note_file=""

# ---------------------------------------------------------------------------
# src/tacenta_braid/tests.rs
# ---------------------------------------------------------------------------
#
# A stand-in for the leaf's `#[cfg(test)] mod tests;`, which is one of the lines
# copied verbatim above: never compiled, but `rustfmt` resolves `mod`
# declarations without reading `cfg`. The erasure leaf needs none -- its tests
# are an inline `mod tests { ... }` -- and it is reached with `#[path]` anyway.
mkdir -p "$unit/src/tacenta_braid"
{
  generated_note "//"
  cat <<'EOF'

//! Not the leaf's tests: an empty stand-in.
//!
//! `tacenta-core/braid/src/lib.rs` declares `#[cfg(test)] mod tests;`, and that
//! line is in the copy beside this file, verbatim, like every other line of it.
//! Nothing in this crate is ever compiled under `cfg(test)`, so this file exists
//! only so that tools which resolve modules without reading `cfg` -- `rustfmt`
//! -- find something.
//!
//! The Braid's tests live and run in `tacenta-core/braid`.
EOF
} > "$unit/src/tacenta_braid/tests.rs"

if [ "$check" -eq 1 ]; then
  if diff -ru "$core/braid-unit" "$unit" > /dev/null 2>&1; then
    echo "assemble-braid-unit: tacenta-core/braid-unit is what the leaves assemble to"
    exit 0
  fi
  echo "assemble-braid-unit: ERROR: tacenta-core/braid-unit is not what the two" >&2
  echo "  leaf crates assemble to. Either it was edited by hand, or a leaf" >&2
  echo "  changed and nobody re-assembled. Regenerate with" >&2
  echo "  tacenta-proofs/scripts/assemble-braid-unit.sh -- and then re-translate" >&2
  echo "  with scripts/run-aeneas.sh, since the unit's translation is stale too." >&2
  diff -ru "$core/braid-unit" "$unit" >&2 || true
  exit 1
fi

echo "assemble-braid-unit: wrote tacenta-core/braid-unit"
echo "assemble-braid-unit:   Cargo.toml              (workspace member, kdf + kem + zeroize + rand_core)"
echo "assemble-braid-unit:   src/lib.rs              (two modules; the erasure codec is #[path] to its leaf)"
echo "assemble-braid-unit:   src/tacenta_braid.rs    (the leaf plus $inject_lines inserted lines, verified)"
echo "assemble-braid-unit:   src/tacenta_braid/tests.rs (empty stand-in; nothing here is built under cfg(test))"
