//! A full conversation through the session lifecycle, Tacenta to Tacenta: create
//! identities, publish a bundle, establish from an initial message, then exchange
//! messages both ways and out of order. This exercises the whole stack behind one
//! establish-and-message interface, which is the surface an interoperability
//! harness drives.

use rand::SeedableRng;
use tacenta_core::sessions::{self, Session, establish_initiator, establish_responder};

fn rng(seed: u64) -> rand::rngs::StdRng {
    rand::rngs::StdRng::seed_from_u64(seed)
}

/// Set up Alice (initiator) and Bob (responder) with a session established from
/// Alice's first message, and return both sessions and Bob's first plaintext.
fn establish(rng: &mut rand::rngs::StdRng) -> (Session, Session, Vec<u8>) {
    let alice_id = sessions::Identity::generate(rng);
    let bob_id = sessions::Identity::generate(rng);
    let mut bob_prekeys = bob_id.create_prekeys(4, rng);
    let bundle = bob_prekeys.publish();

    let mut alice = establish_initiator(&alice_id, &bundle, rng).unwrap();
    let initial = alice.encrypt(b"hello bob", rng).unwrap();
    let (bob, first) = establish_responder(&bob_id, &mut bob_prekeys, &initial, rng).unwrap();
    (alice, bob, first)
}

#[test]
fn the_first_message_is_delivered() {
    let mut r = rng(1);
    let (_alice, _bob, first) = establish(&mut r);
    assert_eq!(first, b"hello bob");
}

#[test]
fn a_bidirectional_conversation_flows() {
    let mut r = rng(2);
    let (mut alice, mut bob, first) = establish(&mut r);
    assert_eq!(first, b"hello bob");

    // Bob replies; his first send starts a new chain after the opening ratchet.
    let m = bob.encrypt(b"hi alice", &mut r).unwrap();
    assert_eq!(alice.decrypt(&m, &mut r).unwrap(), b"hi alice");

    // Several turns each way.
    for i in 0..5u8 {
        let a = alice.encrypt(&[b'a', i], &mut r).unwrap();
        assert_eq!(bob.decrypt(&a, &mut r).unwrap(), &[b'a', i]);
        let b = bob.encrypt(&[b'b', i], &mut r).unwrap();
        assert_eq!(alice.decrypt(&b, &mut r).unwrap(), &[b'b', i]);
    }
}

#[test]
fn out_of_order_delivery_still_decrypts() {
    let mut r = rng(3);
    let (mut alice, mut bob, _first) = establish(&mut r);

    // Alice sends three on one chain; Bob receives the third, then the first two.
    let m0 = alice.encrypt(b"zero", &mut r).unwrap();
    let m1 = alice.encrypt(b"one", &mut r).unwrap();
    let m2 = alice.encrypt(b"two", &mut r).unwrap();

    assert_eq!(bob.decrypt(&m2, &mut r).unwrap(), b"two");
    assert_eq!(bob.decrypt(&m0, &mut r).unwrap(), b"zero");
    assert_eq!(bob.decrypt(&m1, &mut r).unwrap(), b"one");
}

#[test]
fn a_bundle_without_a_one_time_prekey_still_establishes() {
    let mut r = rng(4);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    // No one-time prekeys, so the bundle uses only the signed and KEM prekeys.
    let mut bob_prekeys = bob_id.create_prekeys(0, &mut r);
    let bundle = bob_prekeys.publish();
    assert!(bundle.bundle.one_time_prekey.is_none());

    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let initial = alice.encrypt(b"no one-time prekey", &mut r).unwrap();
    let (_bob, first) = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
    assert_eq!(first, b"no one-time prekey");
}

#[test]
fn a_tampered_message_is_rejected() {
    let mut r = rng(5);
    let (mut alice, mut bob, _first) = establish(&mut r);
    let mut m = alice.encrypt(b"authentic", &mut r).unwrap();
    // Flip a byte in the ciphertext tail.
    let last = m.len() - 1;
    m[last] ^= 0x01;
    assert!(bob.decrypt(&m, &mut r).is_err());
}

/// One-time KEM prekeys are handed out in preference to the last-resort key,
/// and each is deleted as it is used. Establishing more sessions than there are
/// one-time keys must keep working: the bundle falls back to the last-resort
/// key, which is what it is for (session-establishment.md, Keys).
#[test]
fn kem_prekeys_are_used_once_then_fall_back_to_the_last_resort() {
    let mut r = rng(7);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(2, &mut r);

    // Two one-time KEM prekeys, so the third and fourth sessions must fall back.
    let mut seen_kem_ids = Vec::new();
    for round in 0..4u32 {
        let alice_id = sessions::Identity::generate(&mut r);
        let bundle = bob_prekeys.publish();
        seen_kem_ids.push(bundle.kem_prekey_id);

        let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
        let initial = alice.encrypt(b"hello", &mut r).unwrap();
        let (_bob, first) =
            establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
        assert_eq!(first, b"hello", "round {round} failed to decrypt");
    }

    // The first two rounds each consumed a distinct one-time key; the last two
    // shared the last-resort key, which is not consumed.
    assert_ne!(
        seen_kem_ids[0], seen_kem_ids[1],
        "a one-time key was reused"
    );
    assert_ne!(
        seen_kem_ids[1], seen_kem_ids[2],
        "the fallback never happened"
    );
    assert_eq!(
        seen_kem_ids[2], seen_kem_ids[3],
        "the last-resort key should be reusable"
    );
}

/// An initial message cannot be replayed once the one-time keys it named have
/// been consumed. Note this does not isolate the KEM key: the one-time *curve*
/// prekey is consumed by the same message and would reject the replay on its
/// own. Isolating it would need the two one-time sets sized independently,
/// which `create_prekeys` does not offer today.
#[test]
fn a_replayed_initial_message_is_rejected() {
    let mut r = rng(8);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(2, &mut r);
    let bundle = bob_prekeys.publish();

    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let initial = alice.encrypt(b"hello bob", &mut r).unwrap();

    establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
    let replay = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r);
    assert!(
        replay.is_err(),
        "a consumed one-time KEM prekey was accepted twice"
    );
}

/// **A responder can be reached by any of the initiator's first messages, not
/// only the earliest.**
///
/// The Double Ratchet specification recommends that an initiator repeat the
/// initial message on every message until the peer answers, precisely so that
/// losing or reordering the first one does not strand the session. An
/// initiator that consumed the initial payload on the first `encrypt` would
/// leave a responder who received message three first with no session and no
/// way to get one.
///
/// The conformance suite exercises the same property by asking a responder to
/// read the latest message first.
#[test]
fn a_later_message_can_establish_the_session_when_the_first_is_lost() {
    let mut r = rng(20);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(4, &mut r);
    let bundle = bob_prekeys.publish();

    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let one = alice.encrypt(b"first", &mut r).unwrap();
    let two = alice.encrypt(b"second", &mut r).unwrap();
    let three = alice.encrypt(b"third", &mut r).unwrap();

    // The first two never arrive. The third establishes the session by itself.
    let (mut bob, third) = establish_responder(&bob_id, &mut bob_prekeys, &three, &mut r).unwrap();
    assert_eq!(third, b"third");

    // And the earlier two, arriving late, are read inside that same session
    // rather than opening another one.
    assert_eq!(bob.decrypt(&one, &mut r).unwrap(), b"first");
    assert_eq!(bob.decrypt(&two, &mut r).unwrap(), b"second");
}

/// The repetition stops once the peer answers, so a conversation does not carry
/// the prekey payload forever.
#[test]
fn the_initial_message_stops_repeating_once_the_peer_replies() {
    let mut r = rng(21);
    let (mut alice, mut bob, _) = establish(&mut r);

    let still_initial = alice.encrypt(b"still no reply", &mut r).unwrap();
    assert_eq!(
        tacenta_core::serialization::message_type(&still_initial),
        Some(tacenta_core::serialization::MessageType::Initial),
        "the initiator stopped repeating before hearing back"
    );
    bob.decrypt(&still_initial, &mut r).unwrap();

    let reply = bob.encrypt(b"hi", &mut r).unwrap();
    alice.decrypt(&reply, &mut r).unwrap();

    let after = alice.encrypt(b"now plain", &mut r).unwrap();
    assert_eq!(
        tacenta_core::serialization::message_type(&after),
        Some(tacenta_core::serialization::MessageType::Ratchet),
        "the initiator kept repeating after hearing back"
    );
    assert_eq!(bob.decrypt(&after, &mut r).unwrap(), b"now plain");
}

/// An initial message from a *different* establishment is refused rather than
/// replacing the session in place.
#[test]
fn an_unrelated_initial_message_does_not_take_over_a_session() {
    let mut r = rng(22);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(4, &mut r);
    let bundle = bob_prekeys.publish();

    let alice_id = sessions::Identity::generate(&mut r);
    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let from_alice = alice.encrypt(b"hello", &mut r).unwrap();
    let (mut bob, _) = establish_responder(&bob_id, &mut bob_prekeys, &from_alice, &mut r).unwrap();

    let mallory_id = sessions::Identity::generate(&mut r);
    let mut mallory = establish_initiator(&mallory_id, &bundle, &mut r).unwrap();
    let from_mallory = mallory.encrypt(b"me instead", &mut r).unwrap();

    assert!(
        bob.decrypt(&from_mallory, &mut r).is_err(),
        "a stranger's initial message was accepted into an established session"
    );
    // And the real session still works.
    let next = alice.encrypt(b"still here", &mut r).unwrap();
    assert_eq!(bob.decrypt(&next, &mut r).unwrap(), b"still here");
}

/// **A last-resort handshake cannot be replayed.** A one-time KEM prekey
/// defends itself by being deleted on use; the last-resort key is reusable by
/// design, so without a fingerprint record a captured initial message could be
/// replayed without limit, each replay opening a fresh duplicate session. No
/// content would leak -- but unbounded session creation from one captured
/// packet is a denial of service.
///
/// Exhaust the one-time keys so the handshake lands on the last-resort path,
/// then replay the exact bytes.
#[test]
fn a_last_resort_handshake_cannot_be_replayed() {
    let mut r = rng(31);
    let bob_id = sessions::Identity::generate(&mut r);
    // No one-time keys at all, so the very first contact is last-resort.
    let mut bob_prekeys = bob_id.create_prekeys(0, &mut r);

    let alice_id = sessions::Identity::generate(&mut r);
    let bundle = bob_prekeys.publish();
    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let initial = alice.encrypt(b"hello", &mut r).unwrap();

    let (_bob, first) = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
    assert_eq!(first, b"hello");

    // The same bytes again. A replay is refused.
    assert_eq!(
        establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r)
            .map(|_| ())
            .unwrap_err(),
        sessions::LifecycleError::ReplayedLastResort,
    );
    // And again, so the refusal is not a one-shot.
    assert_eq!(
        establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r)
            .map(|_| ())
            .unwrap_err(),
        sessions::LifecycleError::ReplayedLastResort,
    );
}

/// The refusal is specific to the replayed handshake, not to the last-resort
/// path in general: a *different* initiator using the same last-resort key
/// still gets a session. Without this the refusal would be a denial of service
/// of its own -- the last-resort key exists precisely to serve everyone once the
/// one-time keys run out.
#[test]
fn a_different_peer_on_the_last_resort_key_is_unaffected() {
    let mut r = rng(32);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(0, &mut r);

    let mut first_initial = None;
    for round in 0..4u32 {
        let alice_id = sessions::Identity::generate(&mut r);
        let bundle = bob_prekeys.publish();
        let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
        let initial = alice.encrypt(b"hello", &mut r).unwrap();
        let (_bob, plaintext) =
            establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
        assert_eq!(plaintext, b"hello", "round {round} was refused");
        if round == 0 {
            first_initial = Some(initial);
        }
    }

    // Three peers later, the first one's message is still refused.
    assert_eq!(
        establish_responder(&bob_id, &mut bob_prekeys, &first_initial.unwrap(), &mut r)
            .map(|_| ())
            .unwrap_err(),
        sessions::LifecycleError::ReplayedLastResort,
    );
}

/// Replenishment continues the identifier sequence. The trap it exists to
/// avoid is numbering a fresh batch from one: identifiers would collide, and
/// since a lookup finds the *first* match, removing one entry would expose
/// another under the same name -- a one-time prekey served twice.
#[test]
fn replenishment_continues_the_identifier_sequence() {
    let mut r = rng(33);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(2, &mut r);

    let before = bob_prekeys.next_id();
    assert_eq!(bob_prekeys.one_time_remaining(), (2, 2));

    bob_prekeys.replenish(&bob_id, 3, &mut r);
    assert_eq!(bob_prekeys.one_time_remaining(), (5, 5));
    assert!(
        bob_prekeys.next_id() >= before + 6,
        "replenishment restarted the sequence"
    );

    // Every identifier the store will hand out is distinct, which is the
    // property the sequence exists to provide. Five rounds drain the five
    // one-time KEM keys, and no identifier repeats.
    let mut seen = Vec::new();
    for _ in 0..5u32 {
        let alice_id = sessions::Identity::generate(&mut r);
        let bundle = bob_prekeys.publish();
        assert!(
            !seen.contains(&bundle.kem_prekey_id),
            "identifier {} handed out twice",
            bundle.kem_prekey_id
        );
        seen.push(bundle.kem_prekey_id);

        let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
        let initial = alice.encrypt(b"hi", &mut r).unwrap();
        let (_bob, plaintext) =
            establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
        assert_eq!(plaintext, b"hi");
    }
    assert_eq!(bob_prekeys.one_time_remaining(), (0, 0));
}

/// Replenishment keeps peers off the last-resort path, which is the point of
/// it: the last-resort key carries no one-time forward secrecy and is the one
/// needing a bounded replay record.
#[test]
fn replenishment_restores_one_time_key_use() {
    let mut r = rng(34);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(1, &mut r);

    let last_resort_id = {
        // Drain the single one-time key, then read the fallback's identifier.
        let alice_id = sessions::Identity::generate(&mut r);
        let bundle = bob_prekeys.publish();
        let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
        let initial = alice.encrypt(b"x", &mut r).unwrap();
        establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
        bob_prekeys.publish().kem_prekey_id
    };

    bob_prekeys.replenish(&bob_id, 4, &mut r);
    assert_ne!(
        bob_prekeys.publish().kem_prekey_id,
        last_resort_id,
        "still falling back after replenishment"
    );
}

/// A store persisted before the replay record reads back with none remembered,
/// which is the honest answer: it never recorded any. The version byte is what
/// distinguishes them, and a v2 store round-trips its fingerprints.
#[test]
fn the_replay_record_survives_persistence() {
    let mut r = rng(35);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(0, &mut r);

    let alice_id = sessions::Identity::generate(&mut r);
    let bundle = bob_prekeys.publish();
    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let initial = alice.encrypt(b"hello", &mut r).unwrap();
    establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();

    let bytes = bob_prekeys.to_bytes();
    let mut restored = sessions::PrekeyStore::from_bytes(&bytes).unwrap();

    // A restart must not forget what was already spent, or the replay window
    // reopens on every restart.
    assert_eq!(
        establish_responder(&bob_id, &mut restored, &initial, &mut r)
            .map(|_| ())
            .unwrap_err(),
        sessions::LifecycleError::ReplayedLastResort,
    );
}

/// A dispensed batch gives every peer a distinct one-time prekey, which is
/// what `publish` alone cannot do.
#[test]
fn a_published_batch_opens_a_distinct_session_per_peer() {
    let mut r = rng(41);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(3, &mut r);

    let batch = bob_prekeys.publish_one_time_batch();
    assert_eq!(batch.len(), 3, "one bundle per one-time pair");

    // No identifier appears twice, in either pool.
    let mut curve: Vec<u32> = batch.iter().map(|b| b.one_time_prekey_id).collect();
    let mut kem: Vec<u32> = batch.iter().map(|b| b.kem_prekey_id).collect();
    for ids in [&mut curve, &mut kem] {
        let before = ids.len();
        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids.len(), before, "an identifier was published twice");
    }

    // Every dispensed bundle actually opens a session, and each consumes its
    // own prekey rather than colliding with the others.
    for (round, bundle) in batch.into_iter().enumerate() {
        let alice_id = sessions::Identity::generate(&mut r);
        let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
        let initial = alice.encrypt(b"hello", &mut r).unwrap();
        let (_bob, plaintext) = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r)
            .unwrap_or_else(|e| panic!("dispensed bundle {round} failed: {e:?}"));
        assert_eq!(plaintext, b"hello");
    }
    assert_eq!(bob_prekeys.one_time_remaining(), (0, 0));
}

/// The exhausted-pool fallback carries no one-time curve prekey and the
/// reusable last-resort KEM key, and still opens a session.
#[test]
fn the_multi_use_bundle_serves_when_the_pool_is_empty() {
    let mut r = rng(42);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(0, &mut r);

    let fallback = bob_prekeys.publish_multi_use();
    assert!(fallback.bundle.one_time_prekey.is_none());
    assert!(bob_prekeys.publish_one_time_batch().is_empty());

    let alice_id = sessions::Identity::generate(&mut r);
    let mut alice = establish_initiator(&alice_id, &fallback, &mut r).unwrap();
    let initial = alice.encrypt(b"hello", &mut r).unwrap();
    let (_bob, plaintext) =
        establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
    assert_eq!(plaintext, b"hello");
}
