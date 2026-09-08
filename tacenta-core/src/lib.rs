//! tacenta-core: an implementation of selected published Signal Protocol
//! specifications.
//!
//! The implementation follows ../tacenta-spec and ../tacenta-model. This public
//! tree contains no libsignal source or compiled objects. Cryptography only,
//! with no product coupling.

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
