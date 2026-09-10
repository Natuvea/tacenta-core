#!/bin/sh
# Assemble `tacenta-core/triple-unit`, the three-leaf translation unit, from
# the three leaf crates' sources.
#
# ## Why it exists
#
# `tacenta-triple` composes `tacenta-ratchet` and `tacenta-spqr`. Charon
# translates one crate at a time, so in the Triple's own translation both inner
# `State` types are bare opaque axioms and every inner operation is an axiom
# with no precondition: `TripleT1.lean` assumes the unconditional totality of
# about twenty operations whose leaf theorems carry hypotheses, and
# `TripleT3.lean` restates two leaf refinement results by hand because Lean
# cannot reach them (`tooling/check-bundle-drift.py` is the comparison the
# build cannot make). Panic-freedom therefore does not close for the
# composition that ships, which is what `CLAIMS.md` and `LIMITATIONS.md` say.
#
# Compiled as **one** crate, the three leaves are one Charon translation: the
# inner types are real types, the inner operations are real bodies, and the
# preconditions the leaf theorems carry are in scope for the composition. This
# script builds that crate.
#
# ## What the unit is, and what it is not
#
# It is the same source text compiled as one crate. It is **not** the crate as
# shipped: `tacenta-triple`, `tacenta-ratchet` and `tacenta-spqr` ship as three
# crates, and the unit exists only to be translated. Nothing links against it
# and no consumer ever sees it.
#
# The gap between the two is a crate boundary, and a crate boundary does not
# change the meaning of a function body: name resolution, monomorphisation and
# the borrow check all run after it, the profiles and the lockfile are the
# workspace's either way (the unit is a workspace member for exactly that
# reason), and each leaf's `#![forbid(unsafe_code)]` still bounds its own
# module. What does change is *when* the compiler sees the bodies together,
# which is the whole point: it is the difference between an axiom and a
# definition on the Lean side.
#
# The byte-identity is attestable rather than asserted. Two of the three files
# are not copied at all -- they are the leaf files, loaded with `#[path]` --
# and the third is a copy that differs from its leaf by a generated header and
# one inserted `use` and by nothing else. This script verifies that by reading
# the copy back: it finds the inserted block by its text, requires exactly one
# of it, deletes it, and diffs the remainder against the leaf; then it checks
# separately that no top-level inner attribute follows the inserted `use`,
# which byte identity alone would not catch. `attest.py --check` holds the
# committed unit to the hashes of this script and of all three leaf trees.
#
# A sceptical reader may still count "same text, different crate graph" as a
# gap between what is proved and what ships. That is a fair reading, and
# `LIMITATIONS.md` records it under "The three-leaf translation unit".
#
# ## What the assembly does beyond `include!`
#
# The obvious assembly -- three modules each `include!`-ing a leaf `lib.rs` --
# does not compile. Two things are in the way.
#
# 1. **Inner attributes.** Every leaf begins with a module doc (`//!`, which is
#    an inner attribute) and `#![forbid(unsafe_code)]` /
#    `#![allow(clippy::question_mark)]`. An `include!` expands in item
#    position, where an inner attribute is an error (E0753). A *module file*
#    is the one place they are legal, so each leaf is loaded as a module file
#    with `#[path]` instead of being included, and the attributes keep the
#    meaning they have in the leaf: the doc documents the module, and
#    `forbid(unsafe_code)` bounds it.
#
# 2. **The Triple names the other two by crate name.** `tacenta_triple`'s
#    `lib.rs` writes `tacenta_ratchet::State`, `tacenta_spqr::State`,
#    `pub use tacenta_ratchet::{...}` and so on. Inside the unit those are
#    sibling *modules*, and a path's first segment resolves in the current
#    module and the extern prelude -- never in the parent module -- so the leaf
#    text does not resolve as it stands. One `use crate::{...}` in that module
#    puts both names in its scope and every path below then reads exactly as it
#    does in the leaf. There is no way to inject that line from outside the
#    module, so this is the one leaf that is copied rather than referenced, and
#    the inserted lines are the entire difference.
#
# The leaf `lib.rs` files are the source of truth and are never edited.
#
# ## Reproducibility
#
# Deterministic: the same three leaves produce byte-identical output. `--check`
# assembles into a temporary directory and diffs, so a hand-edited unit crate,
# or one left behind by an older leaf, fails without needing Charon, Aeneas or
# a Lean toolchain. `tooling/ci.sh` runs that.
#
# ## Usage
#
#   scripts/assemble-triple-unit.sh            write tacenta-core/triple-unit
#   scripts/assemble-triple-unit.sh --check    fail if the tree differs from it
#
# `scripts/run-aeneas.sh` runs the first form before it translates.
set -eu

here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
core="$root/tacenta-core"

check=0
if [ $# -gt 0 ]; then
  case "$1" in
    --check) check=1 ;;
    *) echo "usage: assemble-triple-unit.sh [--check]" >&2; exit 2 ;;
  esac
fi

# Everything this script may have to remove, and one trap for all of it.
# Two traps on EXIT would not compose: the second silently replaces the first,
# and the temporary tree `--check` assembles into would be left behind on every
# run. That happened once.
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

unit="$core/triple-unit"
if [ "$check" -eq 1 ]; then
  unit_tmp=$(mktemp -d)
  unit="$unit_tmp"
fi

mkdir -p "$unit/src"

# The generated header every file in the unit carries. Kept identical across
# the three so that a reader who opens any of them lands on the same sentence.
generated_note() {
  comment="$1"
  cat <<EOF
$comment GENERATED FILE -- DO NOT EDIT.
$comment
$comment Written by tacenta-proofs/scripts/assemble-triple-unit.sh from the three
$comment leaf crates. Edit the leaves; run the script. An edit here is undone by
$comment the next run and refused by \`assemble-triple-unit.sh --check\`, which
$comment tooling/ci.sh runs, and by \`attest.py --check\`, which holds this crate
$comment to the hashes of the script and of all three leaf trees.
EOF
}

# ---------------------------------------------------------------------------
# Cargo.toml
# ---------------------------------------------------------------------------
#
# A workspace member, listed in `tacenta-core/Cargo.toml`, so the unit resolves
# against the same `Cargo.lock` and compiles under the same `[profile]` tables
# as the leaves -- `overflow-checks` above all, which decides whether an
# addition panics or wraps in the code being translated. A standalone package
# would resolve its own dependency versions and carry its own profiles, and
# then the unit would not be the leaves' compilation.
#
# The dependencies are the union of the three leaves', which is the two the
# leaves share: the trusted key-derivation boundary and `zeroize`. The unit
# does not depend on `tacenta-ratchet` or `tacenta-spqr` -- that is the point;
# their source is *in* it.
#
# `test = false` and `doctest = false`. The unit is translated, never tested:
# the leaves carry the tests and run them, and running them again here would
# test the same bodies a second time under a crate that exists only to be
# translated. The doc examples are written against the leaf crate names and
# would not resolve here at all.
{
  generated_note "#"
  cat <<'EOF'

[package]
name = "tacenta-triple-unit"
license = "Apache-2.0"
version = "0.0.0"
edition = "2024"
rust-version = "1.87"
description = "The Triple Ratchet and both inner ratchets compiled as one crate, so Charon translates the composition with its leaves rather than over opaque axioms. Generated; not shipped."
publish = false

[dependencies]
tacenta-kdf = { path = "../kdf" }
zeroize = { version = "1", features = ["derive"] }

[lib]
test = false
doctest = false
EOF
} > "$unit/Cargo.toml"

# ---------------------------------------------------------------------------
# src/lib.rs
# ---------------------------------------------------------------------------
#
# `pub mod`, not `mod`: every item in the three leaves is `pub` within its own
# crate, and a private wrapping module would make the whole surface unreachable
# and so dead code. Public modules keep the surface reachable, which is also
# what makes the translated surface the leaves' surface.
#
# `#[cfg(not(test))]` on all three: under `cfg(test)` this crate is empty. The
# leaves' own `#[cfg(test)]` test modules would otherwise be compiled a second
# time here, inside a crate with none of their dev-dependencies, and
# `cargo clippy --all-targets` builds a lib's test target whatever `test =
# false` says. Charon and every ordinary build see `cfg(test)` off and so see
# all three modules; nothing that is translated is behind this.
{
  generated_note "//"
  cat <<'EOF'

//! `tacenta-triple-unit`: the Triple Ratchet's three leaf crates compiled as
//! one crate.
//!
//! The three modules below are the three leaf `lib.rs` files. Two are the leaf
//! files themselves, reached with `#[path]`; the third is a copy of
//! `tacenta-core/triple/src/lib.rs` carrying a generated header and one
//! inserted `use`, and identical to the leaf once those are removed, which
//! the assembly script checks by removing them (see the comment at the
//! insertion point in `src/tacenta_triple.rs`). Nothing here adds, removes or
//! reorders a declaration.
//!
//! Nothing links against this crate. It exists so that Charon sees the
//! composition and its two inner ratchets in one translation unit, where the
//! inner operations are bodies rather than axioms.

// Each leaf keeps its own `#![forbid(unsafe_code)]`, which bounds its module.
// The root carries one too, for the few lines that are this file.
#![forbid(unsafe_code)]

#[cfg(not(test))]
#[path = "../../ratchet/src/lib.rs"]
pub mod tacenta_ratchet;

#[cfg(not(test))]
#[path = "../../spqr/src/lib.rs"]
pub mod tacenta_spqr;

#[cfg(not(test))]
pub mod tacenta_triple;
EOF
} > "$unit/src/lib.rs"

# ---------------------------------------------------------------------------
# src/tacenta_triple.rs
# ---------------------------------------------------------------------------
#
# The one copied leaf. The inserted block goes after the last inner attribute
# (an inner attribute must precede every item, and the module doc is one), and
# the rest of the file is the leaf byte for byte.
leaf="$core/triple/src/lib.rs"
copy="$unit/src/tacenta_triple.rs"

# The last line of the leading run of inner doc comments, inner attributes,
# ordinary comments and blank lines: the last line after which an item may
# still be preceded by an inner attribute. A multi-line `#![...]` is followed
# to its closing bracket rather than assumed to end on its own line.
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
  echo "assemble-triple-unit: no inner attribute block in $leaf; refusing to" >&2
  echo "  guess where the inserted \`use\` may go. The insertion has to follow" >&2
  echo "  the last inner attribute, and this file appears to have none." >&2
  exit 1
fi

# The inserted block, and nothing else, is the difference between this file and
# the leaf. Its length is checked against the leaf below.
inject_block() {
  cat <<'EOF'

// Inserted by tacenta-proofs/scripts/assemble-triple-unit.sh. These lines are
// the *entire* difference between this file and
// tacenta-core/triple/src/lib.rs; everything above and below is that file byte
// for byte, and the script verifies it by finding these lines again, deleting
// them, and diffing against the leaf.
//
// In the shipping crate graph `tacenta_ratchet` and `tacenta_spqr` are
// dependencies, and their names come from the extern prelude. Here they are
// sibling modules of this one, and a path's first segment is resolved in the
// current module and the extern prelude, never in the parent, so the names
// have to be brought into scope. Every path below then reads exactly as it
// does in the leaf.
use crate::{tacenta_ratchet, tacenta_spqr};
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

# Two checks on the copy, both read back from the file rather than recomputed
# from the variables that wrote it.
#
# The first is the byte-identity claim: match the generated header against its
# own text at the front of the file, find the inserted block by its text
# wherever it is, delete both, and what is left must be the leaf exactly.
# Locating the block by content is the point. Deleting the same line ranges the
# write used would reconstruct the leaf whatever those ranges were, so it would
# check the arithmetic against itself and pass on any `header_end`; an earlier
# version of this script did exactly that and called it a check. The header is
# matched rather than counted for the same reason, even though its position is
# not in question.
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

# The generated header, matched against its own text at the front of the file.
if copy_lines[:len(note)] != note:
    sys.stderr.write(
        f"assemble-triple-unit: ERROR: {copy} does not begin with the generated "
        f"header this script writes.\n")
    sys.exit(1)
rest = copy_lines[len(note):]

# The inserted block, wherever it is, and there must be exactly one of it.
hits = [i for i in range(len(rest) - len(inject) + 1)
        if rest[i:i + len(inject)] == inject]
if len(hits) != 1:
    sys.stderr.write(
        f"assemble-triple-unit: ERROR: the inserted block occurs {len(hits)} "
        f"times in {copy} after its header; expected exactly one.\n")
    sys.exit(1)
at = hits[0]

open(out, "w").writelines(rest[:at] + rest[at + len(inject):])
sys.exit(0)
PYEOF
  exit 1
fi

if ! diff -q "$stripped" "$leaf" > /dev/null; then
  echo "assemble-triple-unit: ERROR: the copy is not the leaf plus the inserted" >&2
  echo "  block. Removing the generated header and the inserted lines from" >&2
  echo "  $copy did not reproduce $leaf:" >&2
  diff "$stripped" "$leaf" | head -20 >&2
  exit 1
fi

# The second check is where the block landed, which byte identity says nothing
# about: the same lines inserted inside the leaf's `//!` block reproduce the
# leaf just as exactly, and give a file rustc refuses with E0753. An inner
# attribute and an inner doc comment may only precede the items of their
# module, so the inserted `use` must come after the last of them.
#
# The scan runs from the `use` to the first line that begins an item, and no
# further. That bound is what keeps it honest in both directions. Stopping
# early would miss the failure, since a misread header leaves the rest of the
# leaf's `//!` run immediately after the `use`, before any item. Running on
# would report legal Rust: a `//!` at column 0 inside a raw string literal, or
# a `#![...]` opening an inline nested module, are both fine where they sit and
# both appear only after items have started.
use_line=$(grep -n '^use crate::{tacenta_ratchet, tacenta_spqr};$' "$copy" | cut -d: -f1)
if [ "$(echo "$use_line" | wc -l | tr -d ' ')" != 1 ] || [ -z "$use_line" ]; then
  echo "assemble-triple-unit: ERROR: expected exactly one inserted \`use\` line in" >&2
  echo "  $copy; found $(echo "$use_line" | wc -w | tr -d ' ')." >&2
  exit 1
fi
late=$(awk -v start="$use_line" '
  NR <= start { next }
  # An inner attribute or inner doc comment at the top level, before any item
  # has started: this is the failure.
  /^(#!\[|\/\/!)/ { print NR ": " $0; if (++n == 3) exit; next }
  # Still in the leading run: blank, an ordinary comment, or an outer
  # attribute introducing the item that ends the scan.
  /^[[:space:]]*$/ { next }
  /^[[:space:]]*\/\// { next }
  /^#\[/ { next }
  # Anything else is the first item. Stop.
  { exit }
' "$copy")
if [ -n "$late" ]; then
  echo "assemble-triple-unit: ERROR: the inserted \`use\` landed before a top-level" >&2
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
# src/tacenta_triple/tests.rs
# ---------------------------------------------------------------------------
#
# A stand-in for the leaf's `#[cfg(test)] mod tests;`, which is one of the
# lines copied verbatim above.
#
# It is never compiled: `#[cfg(not(test))]` on the module declaration in
# `lib.rs` removes the whole module under `cfg(test)`, and `test = false` keeps
# `cargo test` away. But `rustfmt` resolves `mod` declarations without reading
# `cfg`, so `cargo fmt` walks into it and fails on a file that is not there.
# The other two leaves need no stand-in, for different reasons. The Double
# Ratchet's tests are an inline `mod tests { ... }`, so there is no file to
# resolve. The sparse ratchet's are a `mod tests;` beside its `lib.rs`, and
# `#[path]` sets a module's directory to that of the file it names, so the
# declaration resolves to `spqr/src/tests.rs` -- the leaf's own tests -- exactly
# as it does in the leaf crate. Only the Triple is copied rather than pointed
# at, and only a copy leaves a `mod tests;` with nothing beside it.
#
# The stand-in is empty on purpose. Copying the leaf's tests in would be
# copying source that is not translated, into a crate that cannot run it.
mkdir -p "$unit/src/tacenta_triple"
{
  generated_note "//"
  cat <<'EOF'

//! Not the leaf's tests: an empty stand-in.
//!
//! `tacenta-core/triple/src/lib.rs` declares `#[cfg(test)] mod tests;`, and
//! that line is in the copy beside this file, verbatim, like every other line
//! of it. Nothing in this crate is ever compiled under `cfg(test)` (see the
//! `#[cfg(not(test))]` on the module declarations in `lib.rs`), so this file
//! exists only so that tools which resolve modules without reading `cfg` --
//! `rustfmt` -- find something.
//!
//! The Triple Ratchet's tests live and run in `tacenta-core/triple`.
EOF
} > "$unit/src/tacenta_triple/tests.rs"

if [ "$check" -eq 1 ]; then
  if diff -ru "$core/triple-unit" "$unit" > /dev/null 2>&1; then
    echo "assemble-triple-unit: tacenta-core/triple-unit is what the leaves assemble to"
    exit 0
  fi
  echo "assemble-triple-unit: ERROR: tacenta-core/triple-unit is not what the" >&2
  echo "  three leaf crates assemble to. Either it was edited by hand, or a" >&2
  echo "  leaf changed and nobody re-assembled. Regenerate with" >&2
  echo "  tacenta-proofs/scripts/assemble-triple-unit.sh -- and then re-translate" >&2
  echo "  with scripts/run-aeneas.sh, since the unit's translation is stale too." >&2
  diff -ru "$core/triple-unit" "$unit" >&2 || true
  exit 1
fi

echo "assemble-triple-unit: wrote tacenta-core/triple-unit"
echo "assemble-triple-unit:   Cargo.toml              (workspace member, kdf + zeroize)"
echo "assemble-triple-unit:   src/lib.rs              (three modules; two are #[path] to the leaves)"
echo "assemble-triple-unit:   src/tacenta_triple.rs   (the leaf plus $inject_lines inserted lines, verified)"
echo "assemble-triple-unit:   src/tacenta_triple/tests.rs (empty stand-in; nothing here is built under cfg(test))"
