//! Compile the API that moved behind the boundary and lifecycle leaf crates.
//!
//! This is an integration test, so every name is resolved exactly as it is for
//! an external consumer. Rustdoc records cross-crate reexports differently
//! from locally declared items; this fixture checks that the old import paths
//! and call signatures remain usable despite that metadata-only difference.

use rand_core::{CryptoRng, RngCore};
use tacenta_core::primitives::{aead, dh, kem, xeddsa};
use tacenta_core::sessions::{
    Identity, LifecycleError, PreKeyBundle, PrekeyStore, PrekeyStoreDecodeError, PublicState,
    PublishedBundle, Session, SessionDecodeError, SessionError,
};

#[allow(dead_code, clippy::too_many_arguments)]
fn moved_surface_still_type_checks<R: RngCore + CryptoRng>(
    rng: &mut R,
    identity: &Identity,
    peer_identity: &dh::PublicKeyBytes,
    private: &dh::PrivateKey,
    kem_pair: &kem::KeyPair,
    bundle: &PreKeyBundle,
    published: &PublishedBundle,
    store: &mut PrekeyStore,
    session: &mut Session,
    bytes: &[u8],
    signature: &[u8; 64],
) {
    let _: Option<aead::DecryptError> = None;
    let _ = aead::encrypt(&[0; 32], &[0; 32], &[0; 16], bytes, bytes);
    let _ = aead::decrypt(&[0; 32], &[0; 32], &[0; 16], bytes, bytes);

    let generated_private = dh::PrivateKey::generate(rng);
    let restored_private = dh::PrivateKey::from_bytes([0; 32]);
    let public = dh::PublicKeyBytes::from_bytes([0; 32]);
    let _ = generated_private.public_key();
    let _ = restored_private.to_bytes();
    let _ = private.agree(&public);
    let _ = public.as_bytes();

    let _: Option<kem::KemError> = None;
    let _ = kem::SHARED_SECRET_LEN;
    let _ = kem::public_key_len();
    let _ = kem::ciphertext_len();
    let generated_kem = kem::KeyPair::generate(rng);
    let _ = kem::KeyPair::from_bytes(bytes);
    let _ = generated_kem.public_key();
    let _ = kem_pair.to_bytes();
    let _ = kem::encapsulate(bytes, rng);
    let _ = kem::decapsulate(kem_pair, bytes);

    let _: Option<xeddsa::VerifyError> = None;
    let _ = xeddsa::sign(&[0; 32], bytes, rng);
    let _ = xeddsa::verify(peer_identity, bytes, signature);
    let _ = xeddsa::verifying_key(peer_identity, signature);

    let generated_identity = Identity::generate(rng);
    let _ = Identity::from_secret([0; 32]);
    let _ = generated_identity.public();
    let _ = identity.export();
    let _ = identity.sign_message(bytes, rng);
    let _ = identity.create_prekeys(1, rng);

    let _ = store.to_bytes();
    let _ = PrekeyStore::from_bytes(bytes);
    let _ = store.invariant();
    let _ = store.last_resort_record_remaining();
    let _ = store.last_resort_record_remaining_for(0);
    let _ = store.next_id();
    let _ = store.one_time_remaining();
    let _ = store.publish();
    let _ = store.publish_multi_use();
    let _ = store.publish_one_time_batch();
    store.replenish(identity, 1, rng);
    store.rotate_kem(identity, rng);
    store.rotate_signed_prekey(identity, rng);

    let _ = session.agreement_failed();
    let _ = session.encrypt(bytes, rng);
    let _ = session.decrypt(bytes, rng);
    let _ = session.export();
    let _ = Session::import(bytes);
    let _ = session.invariant();
    let _ = session.peer_identity();
    let _: PublicState = session.public_state();

    let _ = tacenta_core::sessions::encode_ec(peer_identity);
    let _ = tacenta_core::sessions::decode_ec(bytes);
    let _ = tacenta_core::sessions::encode_kem(bytes);
    let _ = tacenta_core::sessions::decode_kem(bytes);
    let _ = tacenta_core::sessions::verify_under_identity(peer_identity, bytes, signature);
    let _ = tacenta_core::sessions::verify_bundle(bundle);
    let _ = tacenta_core::sessions::initiator_shared_secret(private, private, bundle, &[0; 32]);
    let _ = tacenta_core::sessions::responder_shared_secret(
        private,
        private,
        Some(private),
        peer_identity,
        peer_identity,
        &[0; 32],
    );
    let _ = tacenta_core::sessions::establish_initiator(identity, published, rng);
    let _ =
        tacenta_core::sessions::establish_initiator_for(identity, published, peer_identity, rng);
    let _ = tacenta_core::sessions::establish_responder(identity, store, bytes, rng);

    let _ = bundle.identity_key;
    let _ = bundle.signed_prekey;
    let _ = bundle.signed_prekey_signature;
    let _ = &bundle.kem_prekey;
    let _ = bundle.kem_prekey_signature;
    let _ = bundle.one_time_prekey;
    let _ = published.signed_prekey_id;
    let _ = published.kem_prekey_id;
    let _ = published.one_time_prekey_id;
    let _ = &published.bundle;

    let _: Option<LifecycleError> = None;
    let _: Option<PrekeyStoreDecodeError> = None;
    let _: Option<SessionDecodeError> = None;
    let _: Option<SessionError> = None;
}

#[test]
fn moved_surface_is_importable_through_the_original_paths() {
    // The function above is deliberately not executed. Compiling this
    // integration target is the assertion: it resolves every moved public
    // item through the path consumers used before the carve-out.
}
