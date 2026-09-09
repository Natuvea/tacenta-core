//! kem_incremental: ML-KEM-1024's incremental interface.
//!
//! The implementation is [`tacenta_kem`], a leaf crate, for the reason
//! [`super::kdf`]'s is: the ML-KEM Braid is built on this interface, and
//! a translation of the Braid must see the primitive as an opaque declaration
//! rather than as libcrux's const-generic internals.
//!
//! This module is the re-export, so the rest of `tacenta-core` names its
//! primitives in one place.

pub use tacenta_kem::{
    CT1_LEN, CT2_LEN, EK_VECTOR_LEN, EncapsState, HEADER_LEN, IncrementalKeyPair, encapsulate1,
    encapsulate2, validate_ek,
};
