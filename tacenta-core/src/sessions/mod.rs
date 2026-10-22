//! Session establishment and lifecycle orchestration.
//!
//! The implementation lives in the translation-leaf `tacenta-lifecycle`
//! crate. Re-exporting it here preserves the public `tacenta_core::sessions`
//! API while keeping the code translated as one public call graph.
//!
//! [`identity`] is outside the translated surface: identity records, the
//! classification and the lookup, the identity pair digest, and initiator
//! establishment under an expectation, *known* or *first contact*
//! (`tacenta-spec/protocol/session-establishment.md`, Records, expectations
//! and attribution). Its establishment checks the expectation and then calls
//! the leaf's establishment unchanged.

pub mod identity;

#[doc(inline)]
pub use identity::{
    Attribution, ClassifyError, Expectation, InitiatorError, KeyClass, KeyEvidence, KeyRefusal,
    Lookup, PAIR_DIGEST_LABEL, PAIR_DIGEST_LEN, Record, Unattributed,
    VERIFICATION_NUMBER_GROUPED_LEN, VERIFICATION_NUMBER_LEN, classify,
    establish_responder_unattributed, identity_pair_digest, lookup, verification_number,
    verification_number_grouped,
};

#[doc(inline)]
pub use tacenta_lifecycle::{
    ENCODE_EC_CURVE25519, ENCODE_EC_LEN, ENCODE_KEM_ML_KEM_1024, Identity, Key, LifecycleError,
    PreKeyBundle, PrekeyStore, PrekeyStoreDecodeError, PublicState, PublishedBundle, Session,
    SessionDecodeError, SessionError, StoredSessionIdentities, associated_data,
    associated_data_with_kem, decode_ec, decode_kem, encode_ec, encode_kem, establish_initiator,
    establish_initiator_for, establish_responder, initiator_shared_secret, is_valid_identity_key,
    km, responder_shared_secret, scan_stored_prekey_identity, scan_stored_session_identities,
    shared_secret, verify_bundle, verify_under_identity,
};
