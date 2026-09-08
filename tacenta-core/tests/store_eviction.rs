//! A full skipped-key store makes room rather than wedging the session.
//!
//! Both ratchets cap their skipped-key stores at 2000 keys. Refusing with
//! `SkippedStoreFull` past that, with no way back, would wedge the session:
//! the classical store shrinks only by ageing on a *successful* receive, and
//! the sparse store only when an epoch retires, so once the store was full and
//! one more message was missing, every later message would need a slot, be
//! refused, and never advance the clock. A peer that dropped (not forged)
//! about two thousand messages, or a link losing two in three, would end the
//! receive direction for good.
//!
//! The session instead evicts the oldest keys from a *working copy* and
//! retries, committing the copy only after the tag verifies. These tests pin
//! both halves of that: recovery happens, and a forgery still evicts nothing.

use rand::SeedableRng;
use tacenta_core::ratchet::{MAX_SKIP, MAX_SKIPPED_STORE};
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
    let (bob, first) = establish_responder(&bob_id, &mut bob_prekeys, &initial, rng).unwrap();
    assert_eq!(first, b"hello bob");
    (alice, bob)
}

/// One round: Alice sends `MAX_SKIP + 1` messages on a fresh chain, Bob
/// receives only the last (storing `MAX_SKIP` keys), then replies so the next
/// round starts a new chain. Returns Alice's undelivered messages.
fn round(
    alice: &mut Session,
    bob: &mut Session,
    r: &mut rand::rngs::StdRng,
    label: &str,
) -> Vec<Vec<u8>> {
    let mut sent = Vec::new();
    for i in 0..=MAX_SKIP {
        let text = format!("{label} {i}");
        sent.push(alice.encrypt(text.as_bytes(), r).unwrap());
    }
    let last = sent.pop().unwrap();
    let got = bob
        .decrypt(&last, r)
        .unwrap_or_else(|e| panic!("{label}: the last message was refused: {e:?}"));
    assert_eq!(got, format!("{label} {MAX_SKIP}").as_bytes());
    let reply = bob.encrypt(b"ack", r).unwrap();
    assert_eq!(alice.decrypt(&reply, r).unwrap(), b"ack");
    sent
}

#[test]
fn a_full_store_makes_room_and_the_conversation_continues() {
    let mut r = rng(31);
    let (mut alice, mut bob) = establish(&mut r);

    // Two rounds fill the store to exactly its cap.
    let first = round(&mut alice, &mut bob, &mut r, "one");
    let second = round(&mut alice, &mut bob, &mut r, "two");
    assert_eq!(2 * MAX_SKIP as usize, MAX_SKIPPED_STORE);

    // The third round needs another `MAX_SKIP` slots. Without eviction this
    // `decrypt` would fail with `SkippedStoreFull`, and so would every message
    // after it, forever.
    let third = round(&mut alice, &mut bob, &mut r, "three");

    // The newest stored keys survived: the whole of round three, and most of
    // round two. Eviction is oldest-first, so what went was round one.
    assert_eq!(
        bob.decrypt(&third[MAX_SKIP as usize / 2], &mut r).unwrap(),
        b"three 500"
    );
    assert_eq!(
        bob.decrypt(&second[MAX_SKIP as usize - 1], &mut r).unwrap(),
        b"two 999"
    );
    assert!(
        bob.decrypt(&first[MAX_SKIP as usize / 2], &mut r).is_err(),
        "an evicted key still decrypted"
    );

    // And the direction is alive in both senses.
    let m = alice.encrypt(b"still here", &mut r).unwrap();
    assert_eq!(bob.decrypt(&m, &mut r).unwrap(), b"still here");
    let m = bob.encrypt(b"and back", &mut r).unwrap();
    assert_eq!(alice.decrypt(&m, &mut r).unwrap(), b"and back");
}

#[test]
fn a_forgery_against_a_full_store_evicts_nothing() {
    let mut r = rng(32);
    let (mut alice, mut bob) = establish(&mut r);

    let first = round(&mut alice, &mut bob, &mut r, "one");
    let _second = round(&mut alice, &mut bob, &mut r, "two");

    // A genuine third-round message that needs `MAX_SKIP` slots, torn so its
    // tag fails. Handling it evicts on the working copy; the copy must then
    // be dropped, evictions and all.
    let mut sent = Vec::new();
    for i in 0..=MAX_SKIP {
        sent.push(
            alice
                .encrypt(format!("three {i}").as_bytes(), &mut r)
                .unwrap(),
        );
    }
    let genuine = sent.pop().unwrap();
    let mut torn = genuine.clone();
    let last = torn.len() - 1;
    torn[last] ^= 0x01;
    assert!(
        bob.decrypt(&torn, &mut r).is_err(),
        "a torn message was accepted"
    );

    // The oldest keys -- the ones an eviction would have taken first -- are
    // still there.
    assert_eq!(bob.decrypt(&first[0], &mut r).unwrap(), b"one 0");
    assert_eq!(
        bob.decrypt(&first[MAX_SKIP as usize - 1], &mut r).unwrap(),
        b"one 999"
    );

    // The genuine message then goes through, and only now does the store
    // make room.
    assert_eq!(
        bob.decrypt(&genuine, &mut r).unwrap(),
        format!("three {MAX_SKIP}").as_bytes()
    );
}
