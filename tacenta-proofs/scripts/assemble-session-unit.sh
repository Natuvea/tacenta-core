#!/bin/sh
# Assemble the eight-leaf Session translation unit.
#
# The shipping lifecycle crate calls seven verified leaf crates through crate
# boundaries. Translating it alone turns their types and operations into opaque
# declarations. This generated crate compiles the lifecycle, Double Ratchet,
# sparse ratchet, Triple Ratchet, erasure codec, Braid, session derivation and
# wire codec as one Charon unit, so orchestration proofs can use the leaf bodies.
# Nothing links against this crate and it is never published.
# assembly-source: ratchet
# assembly-source: spqr
# assembly-source: triple
# assembly-source: erasure
# assembly-source: braid
# assembly-source: session
# assembly-source: wire
# assembly-source: lifecycle
#
# Usage: assemble-session-unit.sh [--check]
set -eu

here=$(cd "$(dirname "$0")/.." && pwd)
core="$here/../tacenta-core"
check=0
if [ $# -gt 0 ]; then
  case "$1" in
    --check) check=1 ;;
    *) echo "usage: assemble-session-unit.sh [--check]" >&2; exit 2 ;;
  esac
fi

# The Session unit uses the two smaller units' byte-checked copies.
if [ "$check" -eq 1 ]; then
  sh "$here/scripts/assemble-triple-unit.sh" --check
  sh "$here/scripts/assemble-braid-unit.sh" --check
else
  sh "$here/scripts/assemble-triple-unit.sh"
  sh "$here/scripts/assemble-braid-unit.sh"
fi

python3 - "$core" "$check" <<'PY'
from __future__ import annotations

import filecmp
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

core = Path(sys.argv[1]).resolve()
check = sys.argv[2] == "1"
target = core / "session-unit"
temporary = Path(tempfile.mkdtemp(prefix="tacenta-session-unit.")) if check else target

NOTE = """// GENERATED FILE -- DO NOT EDIT.
//
// Written by tacenta-proofs/scripts/assemble-session-unit.sh from the eight
// Session leaf crates. Edit the leaves and run the script. The --check mode
// reconstructs this tree and refuses any hand edit or stale generated copy.

"""

ROOT_BLOCK = """#![cfg(not(test))]

// The seven sibling leaves. The lifecycle leaf is the crate root below.
#[cfg(not(test))]
#[path = "tacenta_braid.rs"]
pub mod tacenta_braid;
#[cfg(not(test))]
#[path = "../../erasure/src/lib.rs"]
pub mod tacenta_erasure;
#[cfg(not(test))]
#[path = "../../ratchet/src/lib.rs"]
pub mod tacenta_ratchet;
#[cfg(not(test))]
#[allow(unused_attributes)]
#[path = "../../session/src/lib.rs"]
pub mod tacenta_session;
#[cfg(not(test))]
#[path = "../../spqr/src/lib.rs"]
pub mod tacenta_spqr;
#[cfg(not(test))]
#[path = "tacenta_triple.rs"]
pub mod tacenta_triple;
#[cfg(not(test))]
#[path = "../../wire/src/lib.rs"]
pub mod tacenta_wire;

"""

RATCHET_IMPORT = "    use crate::tacenta_ratchet;\n"
LIFECYCLE_IMPORT = "use crate::{tacenta_braid, tacenta_erasure, tacenta_spqr, tacenta_triple};\n\n"
WIRE_IMPORT = "use crate::tacenta_wire;\n\n"


def after_module_docs(source: str, block: str) -> str:
    lines = source.splitlines(keepends=True)
    at = 0
    # Skip the module docs and the crate's inner attributes (`#![...]`, with
    # any comment lines among them): the inserted block holds items, and an
    # inner attribute after an item is an error (E0753), as the triple-unit
    # assembler's header explains.
    while at < len(lines) and (
        lines[at].startswith("//!")
        or lines[at].startswith("#![")
        or lines[at].startswith("//")
        or not lines[at].strip()
    ):
        at += 1
    # rustfmt wants no blank line between the crate's inner attributes and the
    # inserted `#![cfg(not(test))]`, so back up over any trailing blank lines.
    while at > 0 and not lines[at - 1].strip():
        at -= 1
    if at == 0:
        raise SystemExit("assemble-session-unit: source has no leading module docs")
    result = "".join(lines[:at]) + block + "".join(lines[at:])
    if result.count(block) != 1 or result.replace(block, "", 1) != source:
        raise SystemExit("assemble-session-unit: inserted block does not strip to source")
    return result


def write(relative: str, contents: str) -> None:
    destination = temporary / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(contents)


try:
    if not check and temporary.exists():
        shutil.rmtree(temporary)
    temporary.mkdir(parents=True, exist_ok=True)

    write("Cargo.toml", """# GENERATED FILE -- DO NOT EDIT.
# Written by tacenta-proofs/scripts/assemble-session-unit.sh.

[package]
name = "tacenta-session-unit"
license = "Apache-2.0"
version = "0.0.0"
edition = "2024"
rust-version = "1.87"
description = "Eight Session leaves compiled as one crate for translation; generated and not shipped."
publish = false

[dependencies]
tacenta-boundary = { path = "../boundary" }
tacenta-kdf = { path = "../kdf" }
tacenta-kem = { path = "../kem" }
rand_core = "0.6"
zeroize = { version = "1", features = ["derive"] }

[features]
conformance = []

[lib]
test = false
doctest = false
""")

    lifecycle_root = (core / "lifecycle/src/lib.rs").read_text()
    assembled_root = after_module_docs(lifecycle_root, ROOT_BLOCK)
    anchor = "pub mod ratchet {\n    pub use tacenta_ratchet::*;\n}"
    replacement = "pub mod ratchet {\n" + RATCHET_IMPORT + "    pub use tacenta_ratchet::*;\n}"
    if assembled_root.count(anchor) != 1:
        raise SystemExit("assemble-session-unit: lifecycle ratchet re-export anchor changed")
    assembled_root = assembled_root.replace(anchor, replacement)
    stripped_root = assembled_root.replace(ROOT_BLOCK, "", 1).replace(RATCHET_IMPORT, "", 1)
    if stripped_root != lifecycle_root:
        raise SystemExit("assemble-session-unit: lifecycle root is not source plus insertions")
    write("src/lib.rs", NOTE + assembled_root)

    # These are the smaller assembly scripts' already byte-checked leaf copies.
    # Copying them locally gives rustfmt the same module layout as those units,
    # including the empty test stand-ins it resolves without reading cfg(test).
    generated_copies = [
        ("triple-unit/src/tacenta_triple.rs", "src/tacenta_triple.rs"),
        ("triple-unit/src/tacenta_triple/tests.rs", "src/tacenta_triple/tests.rs"),
        ("braid-unit/src/tacenta_braid.rs", "src/tacenta_braid.rs"),
        ("braid-unit/src/tacenta_braid/tests.rs", "src/tacenta_braid/tests.rs"),
    ]
    for source, destination in generated_copies:
        write(destination, (core / source).read_text())
    write("src/tests.rs", NOTE + "//! Empty rustfmt stand-in; the unit never builds with cfg(test).\n")

    copied = [
        ("lifecycle.rs", LIFECYCLE_IMPORT),
        ("serialization/mod.rs", WIRE_IMPORT),
        ("serialization/composite.rs", WIRE_IMPORT),
    ]
    for relative, block in copied:
        source = (core / "lifecycle/src" / relative).read_text()
        assembled = after_module_docs(source, block)
        if assembled.replace(block, "", 1) != source:
            raise SystemExit(f"assemble-session-unit: {relative} does not strip to source")
        write("src/" + relative, NOTE + assembled)

    if check:
        comparison = filecmp.dircmp(target, temporary)
        stack = [comparison]
        different = False
        while stack and not different:
            node = stack.pop()
            different = bool(node.left_only or node.right_only or node.diff_files or node.funny_files)
            stack.extend(node.subdirs.values())
        if different:
            subprocess.run(["diff", "-ru", str(target), str(temporary)], check=False)
            raise SystemExit("assemble-session-unit: generated unit is stale or hand-edited")
        print("assemble-session-unit: tacenta-core/session-unit matches all eight leaves")
    else:
        print("assemble-session-unit: wrote tacenta-core/session-unit")
finally:
    if check:
        shutil.rmtree(temporary, ignore_errors=True)
PY
