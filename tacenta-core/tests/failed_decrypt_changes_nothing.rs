//! A message that does not authenticate must change nothing.
//!
//! Both halves of the session lifecycle derive state before they know whether
//! the message driving them is genuine: receiving advances the ratchet, and
//! establishing consumes one-time prekeys. Tests that ask only what happens
//! when a message *is* genuine cannot tell whether that mutation is
//! conditional on authentication.
//!
//! These are the negative tests. They assert that a forged message leaves the
//! receiver exactly as it was, which is what the Double Ratchet specification
//! requires of an exception (section 3.5) and what PQXDH requires of a failed
//! initial message (section 3.4). Each one fails against an implementation
//! that mutates unconditionally.
//!
//! The observable consequence is the point rather than the internal state: a
//! genuine message that was in flight when the forgery arrived must still
//! decrypt. That is the property an attacker would otherwise be able to break.

use rand::SeedableRng;
use tacenta_core::sessions::{self, Session, establish_initiator, establish_responder};

fn rng(seed: u64) -> rand::rngs::StdRng {
    rand::rngs::StdRng::seed_from_u64(seed)
}

fn establish(rng: &mut rand::rngs::StdRng) -> (Session, Session) {
    let alice_id = sessions::Identity::generate(rng);
    let bob_id = sessions::Identity::generate(rng);
    let mut bob_prekeys = bob_id.create_prekeys(4, rng);
    let bundle = bob_prekeys.publish();

    let mut alice = establish_initiator(&alice_id, &bundle, rng).unwrap();
    let initial = alice.encrypt(b"hello bob", rng).unwrap();
    let (bob, _) = establish_responder(&bob_id, &mut bob_prekeys, &initial, rng).unwrap();
    (alice, bob)
}

/// Alter the last byte, which is inside the authentication tag.
fn forge(message: &[u8]) -> Vec<u8> {
    let mut m = message.to_vec();
    let last = m.len() - 1;
    m[last] ^= 0x01;
    m
}

/// A forged message must not consume the key of a genuine one.
///
/// The attack this refuses needs no secret at all: capture a frame, flip a bit,
/// send it first. A receiver that advanced its ratchet deriving a key for the
/// forgery would then decrypt the genuine frame behind it against a chain that
/// had already moved.
#[test]
fn a_forged_message_does_not_consume_the_genuine_one() {
    let mut r = rng(11);
    let (mut alice, mut bob) = establish(&mut r);

    let genuine = alice.encrypt(b"the real message", &mut r).unwrap();
    let forged = forge(&genuine);

    assert!(
        bob.decrypt(&forged, &mut r).is_err(),
        "a message with an altered tag must not decrypt"
    );

    // The whole point: the genuine message is still delivered.
    assert_eq!(
        bob.decrypt(&genuine, &mut r).unwrap(),
        b"the real message",
        "a forgery must not consume the message key of a genuine message"
    );
}

/// The same, with several forgeries in a row: the state must not drift under
/// repeated failures either, so that an attacker cannot desynchronise a session
/// merely by sending enough of them.
#[test]
fn repeated_forgeries_do_not_desynchronise_the_session() {
    let mut r = rng(12);
    let (mut alice, mut bob) = establish(&mut r);

    let genuine = alice.encrypt(b"still here", &mut r).unwrap();
    for _ in 0..32 {
        assert!(bob.decrypt(&forge(&genuine), &mut r).is_err());
    }
    assert_eq!(bob.decrypt(&genuine, &mut r).unwrap(), b"still here");

    // And the conversation continues normally afterwards, in both directions.
    let m = alice.encrypt(b"next", &mut r).unwrap();
    assert_eq!(bob.decrypt(&m, &mut r).unwrap(), b"next");
    let reply = bob.encrypt(b"reply", &mut r).unwrap();
    assert_eq!(alice.decrypt(&reply, &mut r).unwrap(), b"reply");
}

/// A forgery must not consume a *skipped* key either.
///
/// Receiving out of order stores keys for the messages that have not arrived.
/// A forged header naming one of those must not make the receiver derive and
/// consume it, or the delayed genuine message could never be read.
#[test]
fn a_forgery_does_not_consume_a_skipped_key() {
    let mut r = rng(13);
    let (mut alice, mut bob) = establish(&mut r);

    // Alice sends three; Bob will read the third first, storing keys for the
    // first two.
    let first = alice.encrypt(b"one", &mut r).unwrap();
    let second = alice.encrypt(b"two", &mut r).unwrap();
    let third = alice.encrypt(b"three", &mut r).unwrap();

    assert_eq!(bob.decrypt(&third, &mut r).unwrap(), b"three");

    // Forgeries of the two still in flight.
    assert!(bob.decrypt(&forge(&first), &mut r).is_err());
    assert!(bob.decrypt(&forge(&second), &mut r).is_err());

    // Both must still arrive.
    assert_eq!(bob.decrypt(&first, &mut r).unwrap(), b"one");
    assert_eq!(bob.decrypt(&second, &mut r).unwrap(), b"two");
}

/// A failed initial message must not consume one-time prekeys.
///
/// Anyone can fetch a published bundle, and the identifiers in it must not be
/// enough to burn the matching private keys: otherwise an initial message that
/// names them and does not authenticate would delete them, and the store would
/// drain without a single session being established.
///
/// Checked through the published bundle, because that is what an attacker sees
/// and what a legitimate peer depends on: if the same one-time identifiers are
/// still on offer, the keys behind them still exist.
#[test]
fn a_failed_initial_message_does_not_burn_prekeys() {
    let mut r = rng(14);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(4, &mut r);

    let bundle = bob_prekeys.publish();
    let offered_curve = bundle.one_time_prekey_id;
    let offered_kem = bundle.kem_prekey_id;

    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let initial = alice.encrypt(b"hello bob", &mut r).unwrap();

    assert!(
        establish_responder(&bob_id, &mut bob_prekeys, &forge(&initial), &mut r).is_err(),
        "an initial message with an altered tag must not establish"
    );

    // The keys the forgery named are still there, so the genuine message that
    // names the same ones still works.
    let (_, plaintext) = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r)
        .expect("a forged initial message must not consume the prekeys a genuine one needs");
    assert_eq!(plaintext, b"hello bob");

    // And the identifiers the failed attempt named were the ones at risk.
    assert_ne!(offered_curve, 0);
    assert_ne!(offered_kem, 0);
}

/// Many failed initial messages must not drain the store.
///
/// One burnt prekey is a lost message; a drained store is every later peer
/// forced onto the reusable last-resort KEM key, which is the one that carries
/// no one-time forward secrecy. This is the version of the attack that matters.
#[test]
fn repeated_failed_initial_messages_do_not_drain_the_store() {
    let mut r = rng(15);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(4, &mut r);

    // What is on offer before the attack. `publish` reads the store without
    // consuming from it, so these identifiers change only if a key is deleted.
    let before = bob_prekeys.publish();
    let (curve_before, kem_before) = (before.one_time_prekey_id, before.kem_prekey_id);

    // Four one-time prekeys, so four bundles' worth. Attack with far more.
    for _ in 0..16 {
        let bundle = bob_prekeys.publish();
        let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
        let initial = alice.encrypt(b"burn", &mut r).unwrap();
        assert!(establish_responder(&bob_id, &mut bob_prekeys, &forge(&initial), &mut r).is_err());
    }

    // Every one-time prekey survived: the store offers exactly what it offered
    // before, so nothing behind those identifiers was deleted.
    let bundle = bob_prekeys.publish();
    assert_eq!(
        bundle.one_time_prekey_id, curve_before,
        "one-time curve prekeys were consumed by messages that never authenticated"
    );
    assert_eq!(
        bundle.kem_prekey_id, kem_before,
        "one-time KEM prekeys were consumed by messages that never authenticated"
    );

    // And a genuine establishment still works.
    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let initial = alice.encrypt(b"for real", &mut r).unwrap();
    let (_, plaintext) = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
    assert_eq!(plaintext, b"for real");
}

/// A successful establishment *must* consume them, which is the other half of
/// the contract. Deferring deletion is only correct if it still happens.
#[test]
fn a_successful_initial_message_does_consume_its_prekeys() {
    let mut r = rng(16);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(4, &mut r);

    let bundle = bob_prekeys.publish();
    let used_curve = bundle.one_time_prekey_id;
    let used_kem = bundle.kem_prekey_id;

    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let initial = alice.encrypt(b"hello", &mut r).unwrap();
    establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();

    // The next bundle offers different one-time keys, because the last ones
    // were spent.
    let next = bob_prekeys.publish();
    assert_ne!(next.one_time_prekey_id, used_curve);
    assert_ne!(next.kem_prekey_id, used_kem);

    // And replaying the same initial message cannot reuse them.
    assert!(
        establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).is_err(),
        "a one-time prekey must not serve a replayed initial message"
    );
}
