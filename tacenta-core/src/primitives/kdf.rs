//! Key derivation: re-exported from `tacenta-kdf`.
//!
//! HKDF-SHA256 and HMAC-SHA256 live in their own crate, `tacenta-kdf`, which
//! every translation whose crate calls them includes; they are surfaced here so
//! the primitive set reads as one boundary.

pub use tacenta_kdf::*;
