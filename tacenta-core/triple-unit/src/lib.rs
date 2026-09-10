// GENERATED FILE -- DO NOT EDIT.
//
// Written by tacenta-proofs/scripts/assemble-triple-unit.sh from the three
// leaf crates. Edit the leaves; run the script. An edit here is undone by
// the next run and refused by `assemble-triple-unit.sh --check`, which
// tooling/ci.sh runs, and by `attest.py --check`, which holds this crate
// to the hashes of the script and of all three leaf trees.

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
