#![forbid(unsafe_code)]
//! The primitive boundary: X25519, the AEAD, ML-KEM-1024 and XEdDSA behind
//! the session lifecycle leaf. Charon translates the lifecycle with this crate
//! as a dependency, so every function here is an opaque declaration in the
//! generated Lean and the bodies below are trusted, not translated
//! (`tacenta-proofs/LIMITATIONS.md`, "Trusted, not verified"). The surface the
//! lifecycle reaches is the module API of `dh`, `aead`, `kem` and `xeddsa`;
//! `tooling/check-lifecycle-boundary-surface.py` pins that reachable set.

pub mod aead;
pub mod dh;
pub mod kem;
pub mod xeddsa;

pub mod kdf {
    pub use tacenta_kdf::*;
}
