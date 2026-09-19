//! Session establishment and lifecycle orchestration.
//!
//! The implementation lives in the translation-leaf `tacenta-lifecycle`
//! crate. Re-exporting it here preserves the public `tacenta_core::sessions`
//! API while keeping the code translated as one public call graph.

#[doc(inline)]
pub use tacenta_lifecycle::{
    ENCODE_EC_CURVE25519, ENCODE_EC_LEN, ENCODE_KEM_ML_KEM_1024, Identity, Key, LifecycleError,
    PreKeyBundle, PrekeyStore, PrekeyStoreDecodeError, PublicState, PublishedBundle, Session,
    SessionDecodeError, SessionError, associated_data, associated_data_with_kem, decode_ec,
    decode_kem, encode_ec, encode_kem, establish_initiator, establish_initiator_for,
    establish_responder, initiator_shared_secret, km, responder_shared_secret, shared_secret,
    verify_bundle, verify_under_identity,
};
