//! tacenta-core: an implementation of selected published Signal Protocol
//! specifications.
//!
//! The implementation follows ../tacenta-spec and ../tacenta-model. This public
//! tree contains no libsignal source or compiled objects. Cryptography only,
//! with no product coupling.
//!
//! # Randomness
//!
//! Every public function that draws randomness is generic over `R: RngCore +
//! CryptoRng`, and those are the **`rand_core` 0.6** traits (CR-27). The dalek
//! and libcrux dependencies fix that version, so a caller on a newer `rand`
//! (0.8's re-export is 0.6; 0.9 and 1.0 moved the traits) passes an adapter
//! rather than its own generator directly. This is stated because the bound is
//! part of the public signature and a version mismatch surfaces as an opaque
//! trait-bound error at the call site rather than here.

// No `unsafe` in this library crate, enforced by the attribute rather than
// observed; every library crate in the workspace carries it. The one `unsafe`
// block in the workspace is in `tests/timing.rs`, which sets a CPU flag
// for measurement. The attribute bounds this crate only -- dependencies are
// the trusted boundary and are unaffected.
#![forbid(unsafe_code)]

/// The KDF inputs an external implementation's message layer would need,
/// held as a type with no constructor. Not wired into any output path:
/// message-layer byte compatibility with any other implementation is not
/// attempted.
pub mod interop;
pub mod primitives;
/// The Double Ratchet state machine, re-exported from the verified-zone leaf
/// crate `tacenta-ratchet` (isolated so the T1 translation covers it alone).
pub mod ratchet {
    pub use tacenta_ratchet::*;
}
pub mod serialization;
pub mod sessions;
