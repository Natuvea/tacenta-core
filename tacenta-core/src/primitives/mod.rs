//! Cryptographic primitives.
//!
//! Thin wrappers over vetted, permissively licensed implementations (RustCrypto,
//! dalek). These are the trusted boundary of the library: the protocol logic
//! built on top of them is what tacenta specifies and verifies, while the
//! primitives themselves are assumed correct and are named in the proofs'
//! trusted computing base. Standard cryptography is not reimplemented here.

pub use tacenta_boundary::{aead, dh, kem, xeddsa};
pub mod kdf;
pub mod kem_incremental;
