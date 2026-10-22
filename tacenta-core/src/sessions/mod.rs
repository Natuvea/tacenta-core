//! Session establishment and lifecycle orchestration.
//!
//! Most of the implementation lives in the translation-leaf
//! `tacenta-lifecycle` crate, and is re-exported here, so that the code is
//! translated as one public call graph.
//!
//! Initiator establishment is the exception. The specification has the
//! initiator establish only under an expectation, *known* or *first contact*
//! (`tacenta-spec/protocol/session-establishment.md`, Records, expectations
//! and attribution), and [`establish_initiator`] here is that entry point. It
//! lives in [`identity`], outside the translated surface, beside identity
//! records, the classification, the lookup and the identity pair digest. It
//! checks the expectation and then calls the leaf's establishment unchanged.
//! The leaf's own `establish_initiator` and `establish_initiator_for`, which
//! take no expectation, are not re-exported: they stay public in
//! `tacenta-lifecycle` for the translation and its tests.
//!
//! The responder's establishment is the leaf's, unchanged.
//! [`establish_responder_unattributed`] is the same establishment with the
//! first plaintext wrapped as [`Unattributed`].

pub mod identity;

#[doc(inline)]
pub use identity::{
    Attribution, ClassifyError, Expectation, InitiatorError, KeyClass, KeyEvidence, KeyRefusal,
    Lookup, PAIR_DIGEST_LABEL, PAIR_DIGEST_LEN, Record, Unattributed,
    VERIFICATION_NUMBER_GROUPED_LEN, VERIFICATION_NUMBER_LEN, classify, establish_initiator,
    establish_responder_unattributed, identity_pair_digest, lookup, verification_number,
    verification_number_grouped,
};

#[doc(inline)]
pub use tacenta_lifecycle::{
    ENCODE_EC_CURVE25519, ENCODE_EC_LEN, ENCODE_KEM_ML_KEM_1024, Identity, Key, LifecycleError,
    PreKeyBundle, PrekeyStore, PrekeyStoreDecodeError, PublicState, PublishedBundle, Session,
    SessionDecodeError, SessionError, StoredSessionIdentities, associated_data,
    associated_data_with_kem, decode_ec, decode_kem, encode_ec, encode_kem, establish_responder,
    initiator_shared_secret, is_valid_identity_key, km, responder_shared_secret,
    scan_stored_prekey_identity, scan_stored_session_identities, shared_secret, verify_bundle,
    verify_under_identity,
};
