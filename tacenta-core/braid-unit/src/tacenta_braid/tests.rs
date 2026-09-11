// GENERATED FILE -- DO NOT EDIT.
//
// Written by tacenta-proofs/scripts/assemble-braid-unit.sh from the two
// leaf crates. Edit the leaves; run the script. An edit here is undone by
// the next run and refused by `assemble-braid-unit.sh --check`, which
// tooling/ci.sh runs, and by `attest.py --check`, which holds this crate
// to the hashes of the script and of both leaf trees.

//! Not the leaf's tests: an empty stand-in.
//!
//! `tacenta-core/braid/src/lib.rs` declares `#[cfg(test)] mod tests;`, and that
//! line is in the copy beside this file, verbatim, like every other line of it.
//! Nothing in this crate is ever compiled under `cfg(test)`, so this file exists
//! only so that tools which resolve modules without reading `cfg` -- `rustfmt`
//! -- find something.
//!
//! The Braid's tests live and run in `tacenta-core/braid`.
