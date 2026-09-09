//! Session-layer refusals and bounds that the rest of the suite only exercised
//! from the leaf crates or not at all (CR-28).
//!
//! Three things are pinned here, each against `SECURITY.md`'s in-scope list:
//!
//! - **Non-contributory agreement is refused at the session layer**, on each of
//!   the three surfaces where an attacker chooses a public key -- a bundle key
//!   the initiator agrees with, a key in an unauthenticated initial message the
//!   responder agrees with, and the ratchet public in a received header -- and
//!   the refusal leaves the state it was handed unchanged.
//! - **The last-resort replay bound is a real limit**: past
//!   `MAX_LAST_RESORT_SEEN` distinct handshakes the oldest fingerprint is
//!   evicted and its replay is accepted again, while a fingerprint still inside
//!   the window is refused; and `from_bytes` refuses a stored count above the
//!   bound.
//!
//! The AEAD padding-versus-tag indistinguishability the same finding asks for
//! is a unit test in `src/primitives/aead.rs`, where the HMAC internals needed
//! to build the case are in scope.

use rand::SeedableRng;
use tacenta_core::primitives::dh::PublicKeyBytes;
use tacenta_core::primitives::kem;
use tacenta_core::serialization::composite::Composite;
use tacenta_core::serialization::{ABSENT_ID, decode_message, encode_initial, encode_message};
use tacenta_core::sessions::{
    Identity, LifecycleError, PreKeyBundle, PrekeyStore, PrekeyStoreDecodeError, PublishedBundle,
    Session, SessionError, encode_ec, encode_kem, establish_initiator, establish_responder,
};

fn rng(seed: u64) -> rand::rngs::StdRng {
    rand::rngs::StdRng::seed_from_u64(seed)
}

/// A low-order X25519 point: `u = 0` forces every agreement against it to zero,
/// so `dh::PrivateKey::agree` refuses it. This is the value an attacker sends to
/// try to make a shared secret they alone predict.
const LOW_ORDER: [u8; 32] = [0u8; 32];

// ---------------------------------------------------------------- initiator

/// A bundle whose signed prekey is a low-order point is refused by the
/// initiator, and the signature is *valid* -- the refusal is the agreement's,
/// not the verifier's.
#[test]
fn establish_initiator_refuses_a_low_order_bundle_key() {
    let mut r = rng(1);
    let alice = Identity::generate(&mut r);
    let bob = Identity::generate(&mut r);
    let bob_secret = bob.export();

    // A real KEM prekey, so verification and encapsulation pass and the DH
    // agreement is what fails.
    let kem_kp = kem::KeyPair::generate(&mut r);
    let low = PublicKeyBytes::from_bytes(LOW_ORDER);
    let bundle = PublishedBundle {
        bundle: PreKeyBundle {
            identity_key: bob.public(),
            signed_prekey: low,
            signed_prekey_signature: tacenta_core::primitives::xeddsa::sign(
                &bob_secret,
                &encode_ec(&low),
                &mut r,
            ),
            kem_prekey: kem_kp.public_key(),
            kem_prekey_signature: tacenta_core::primitives::xeddsa::sign(
                &bob_secret,
                &encode_kem(&kem_kp.public_key()),
                &mut r,
            ),
            one_time_prekey: None,
        },
        signed_prekey_id: 1,
        one_time_prekey_id: ABSENT_ID,
        kem_prekey_id: 2,
    };

    assert!(
        matches!(
            establish_initiator(&alice, &bundle, &mut r),
            Err(LifecycleError::Handshake(
                SessionError::NonContributoryAgreement
            ))
        ),
        "a low-order signed prekey must be refused as non-contributory"
    );
}

// ---------------------------------------------------------------- responder

/// A responder handed an initial message whose initiator ephemeral is a
/// low-order point refuses it, and -- because nothing durable moves until the
/// ciphertext authenticates -- the prekey store is byte-for-byte unchanged.
#[test]
fn establish_responder_refuses_a_low_order_initiator_key_and_changes_nothing() {
    let mut r = rng(2);
    let bob = Identity::generate(&mut r);
    // No one-time prekeys, so the message lands on the last-resort path and the
    // fields to control are minimal.
    let mut store = bob.create_prekeys(0, &mut r);
    let published = store.publish_multi_use();

    // A real ciphertext against the last-resort KEM prekey, so decapsulation
    // succeeds and the DH agreement is what fails.
    let (kem_ct, _ss) = kem::encapsulate(&published.bundle.kem_prekey, &mut r).unwrap();

    let alice = Identity::generate(&mut r);
    let identity_enc = encode_ec(&alice.public());
    let low_ephemeral_enc = encode_ec(&PublicKeyBytes::from_bytes(LOW_ORDER));
    let initial = encode_initial(
        &identity_enc,
        &low_ephemeral_enc,
        &kem_ct,
        published.signed_prekey_id,
        ABSENT_ID,
        published.kem_prekey_id,
        b"inner ratchet message, never reached",
    );

    let before = store.to_bytes().to_vec();
    assert!(
        matches!(
            establish_responder(&bob, &mut store, &initial, &mut r),
            Err(LifecycleError::Handshake(
                SessionError::NonContributoryAgreement
            ))
        ),
        "a low-order initiator ephemeral must be refused as non-contributory"
    );
    assert_eq!(
        store.to_bytes().to_vec(),
        before,
        "a refused handshake must not touch the prekey store"
    );
}

// ------------------------------------------------------------- ratchet header

fn established_pair(r: &mut rand::rngs::StdRng) -> (Session, Session) {
    let alice_id = Identity::generate(r);
    let bob_id = Identity::generate(r);
    let mut bob_prekeys = bob_id.create_prekeys(4, r);
    let bundle = bob_prekeys.publish();
    let mut alice = establish_initiator(&alice_id, &bundle, r).unwrap();
    let initial = alice.encrypt(b"hello", r).unwrap();
    let (mut bob, _) = establish_responder(&bob_id, &mut bob_prekeys, &initial, r).unwrap();
    // One reply so Alice stops prepending the initial message and her next
    // message is a plain ratchet message.
    let reply = bob.encrypt(b"ack", r).unwrap();
    alice.decrypt(&reply, r).unwrap();
    (alice, bob)
}

/// A received header whose ratchet public is a low-order point is refused, and
/// the session is unchanged: a genuine message that was in flight still
/// decrypts afterwards.
#[test]
fn decrypt_refuses_a_low_order_ratchet_header_and_changes_nothing() {
    let mut r = rng(3);
    let (mut alice, mut bob) = established_pair(&mut r);

    let genuine = alice.encrypt(b"the real message", &mut r).unwrap();
    let decoded = decode_message(&genuine).expect("a plain ratchet message");
    let forged_header = Composite {
        dh: LOW_ORDER,
        ..decoded.header
    };
    let forged = encode_message(&forged_header, &decoded.ciphertext);

    let before = bob.export().to_vec();
    assert!(
        matches!(
            bob.decrypt(&forged, &mut r),
            Err(LifecycleError::Handshake(
                SessionError::NonContributoryAgreement
            ))
        ),
        "a low-order ratchet public must be refused as non-contributory"
    );
    assert_eq!(
        bob.export().to_vec(),
        before,
        "a refused receive must not advance the session"
    );

    // The genuine message behind the forgery still decrypts.
    assert_eq!(
        bob.decrypt(&genuine, &mut r).unwrap(),
        b"the real message",
        "the refusal must not have consumed the genuine message's key"
    );
}

// --------------------------------------------------------- last-resort bound

/// The 1024-fingerprint bound is a real limit (CR-28). Past it the oldest
/// fingerprint is evicted, so the very first handshake can be replayed again,
/// while a handshake still inside the window is refused.
#[test]
fn the_last_resort_replay_bound_evicts_the_oldest() {
    const BOUND: usize = 1024;
    let mut r = rng(4);
    let bob = Identity::generate(&mut r);
    // No one-time KEM prekeys, so every first contact lands on the reusable
    // last-resort key and is fingerprinted.
    let mut store = bob.create_prekeys(0, &mut r);
    let bundle = store.publish_multi_use();
    let alice = Identity::generate(&mut r);

    let mut first = None;
    let mut inside_window = None;
    for i in 1..=BOUND + 1 {
        let mut a = establish_initiator(&alice, &bundle, &mut r).unwrap();
        let m = a.encrypt(b"first contact", &mut r).unwrap();
        establish_responder(&bob, &mut store, &m, &mut r)
            .unwrap_or_else(|e| panic!("handshake {i} was refused: {e:?}"));
        if i == 1 {
            first = Some(m);
        } else if i == BOUND {
            // The 1024th recorded, so still remembered after the 1025th arrives.
            inside_window = Some(m);
        }
    }

    // A fingerprint still inside the window is refused as a replay.
    assert!(
        matches!(
            establish_responder(&bob, &mut store, &inside_window.unwrap(), &mut r),
            Err(LifecycleError::ReplayedLastResort)
        ),
        "a handshake inside the window must be refused as a replay"
    );

    // The very first fingerprint was evicted when the 1025th was recorded, so
    // its replay is accepted again -- the bound is a real limit, not a
    // permanent record.
    assert!(
        establish_responder(&bob, &mut store, &first.unwrap(), &mut r).is_ok(),
        "the evicted first handshake must be accepted again"
    );
}

/// `from_bytes` refuses a stored last-resort count larger than the bound before
/// it trusts the count to size anything (CR-28).
#[test]
fn from_bytes_refuses_a_last_resort_count_above_the_bound() {
    let mut r = rng(5);
    let bob = Identity::generate(&mut r);
    // A fresh store with no one-time keys, no rotation, and no fingerprints: its
    // encoding ends with the four-byte seen-count (zero) followed by the two
    // retired-prekey presence bytes (both absent).
    let store = bob.create_prekeys(0, &mut r);
    let mut bytes = store.to_bytes().to_vec();
    let n = bytes.len();
    assert_eq!(
        &bytes[n - 6..],
        &[0, 0, 0, 0, 0, 0],
        "layout drift: expected a zero seen-count and two absent presence bytes at the tail"
    );

    // Overwrite the seen-count with one past the bound.
    bytes[n - 6..n - 2].copy_from_slice(&(1025u32).to_be_bytes());
    assert!(
        matches!(
            PrekeyStore::from_bytes(&bytes),
            Err(PrekeyStoreDecodeError::Malformed)
        ),
        "a seen-count above the bound must be refused"
    );
}
