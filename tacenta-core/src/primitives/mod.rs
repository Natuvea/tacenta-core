//! Cryptographic primitives.
//!
//! Mostly thin wrappers over vetted, permissively licensed implementations
//! (RustCrypto, dalek), assumed correct and named in the proofs' trusted
//! computing base. Two are written in this workspace instead: XEdDSA
//! (`tacenta-spec` ADR-0002) and the key derivation's SHA-256, HMAC and HKDF
//! (`tacenta-kdf`, ADR-0010, proposed), whose agreement with the model is proved.

pub mod aead {
    #[doc(inline)]
    pub use tacenta_boundary::aead::*;
}
pub mod dh {
    #[doc(inline)]
    pub use tacenta_boundary::dh::*;
}
pub mod kdf;
pub mod kem {
    #[doc(inline)]
    pub use tacenta_boundary::kem::*;
}
pub mod kem_incremental;
pub mod xeddsa {
    #[doc(inline)]
    pub use tacenta_boundary::xeddsa::*;
}
