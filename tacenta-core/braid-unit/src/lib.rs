// GENERATED FILE -- DO NOT EDIT.
//
// Written by tacenta-proofs/scripts/assemble-braid-unit.sh from the two
// leaf crates. Edit the leaves; run the script. An edit here is undone by
// the next run and refused by `assemble-braid-unit.sh --check`, which
// tooling/ci.sh runs, and by `attest.py --check`, which holds this crate
// to the hashes of the script and of both leaf trees.

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
