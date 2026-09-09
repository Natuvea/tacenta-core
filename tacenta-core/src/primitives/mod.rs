//! Cryptographic primitives.
//!
//! Thin wrappers over vetted, permissively licensed implementations (RustCrypto,
//! dalek). These are the trusted boundary of the library: the protocol logic
//! built on top of them is what tacenta specifies and verifies, while the
//! primitives themselves are assumed correct and are named in the proofs'
//! trusted computing base. Standard cryptography is not reimplemented here.

pub mod aead;
pub mod dh;
pub mod kdf;
pub mod kem;
pub mod kem_incremental;
pub mod xeddsa;
