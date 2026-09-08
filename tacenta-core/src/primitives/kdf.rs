//! Key derivation: re-exported from the verified-zone leaf crate.
//!
//! HKDF-SHA256 and HMAC-SHA256 live in `tacenta-ratchet` because the ratchet
//! calls them and the T1 translation covers that crate alone; they are surfaced
//! here so the primitive set reads as one boundary.

pub use tacenta_kdf::*;
