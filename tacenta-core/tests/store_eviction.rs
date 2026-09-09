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
//! that: recovery happens, the first batch is sized to what the message
//! actually displaces, and a forgery still evicts nothing -- including the
//! forgery that reaches the one sizing path honest traffic cannot, a header
//! naming the epoch a fold is about to open.

use rand::SeedableRng;
use tacenta_core::ratchet::{MAX_SKIP, MAX_SKIPPED_STORE};
use tacenta_core::serialization::{decode_message, encode_message};
use tacenta_core::sessions::{self, Session, establish_initiator, establish_responder};
use tacenta_spqr::MAX_SKIP as PQ_MAX_SKIP;

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

/// The first eviction is sized to the shortfall, which is the keys held plus
/// the keys the message skips on its chain, less the cap -- not the skip
/// count on its own, and not a geometric climb up to it. The store refuses
/// well before it holds the cap: 1500 keys and a message 599 ahead is 99
/// over, and 99 is what must go from each store. Sizing by the skip count
/// would take 599, five hundred keys the message never displaced (CR-19).
///
/// Both halves are pinned. The classical one has been sized from its own
/// figures since CR-19; the post-quantum one climbed 1, 2, 4, ... until the
/// sparse ratchet gained the two accessors that let a shortfall be computed
/// for the epoch a header names, and took 127 for a 99-key excess -- 28 keys
/// the message never displaced (external review, 2026-09). The two are
/// distinguishable through what still decrypts, because a message needs a key
/// from each store: the message whose classical key survives by one is the one
/// that says the post-quantum half stopped in the same place.
#[test]
fn the_first_eviction_is_sized_to_the_shortfall_not_the_skip_count() {
    let mut r = rng(33);
    let (mut alice, mut bob) = establish(&mut r);

    // A thousand keys from the first chain.
    let first = round(&mut alice, &mut bob, &mut r, "one");

    // Five hundred more from the second: Alice sends 501, Bob receives only
    // the last, so his receive count on this chain is 501 and the store holds
    // 1500.
    let mut second = Vec::new();
    for i in 0..=500u32 {
        second.push(
            alice
                .encrypt(format!("two {i}").as_bytes(), &mut r)
                .unwrap(),
        );
    }
    assert_eq!(bob.decrypt(&second[500], &mut r).unwrap(), b"two 500");

    // Message 1100 on the same chain skips 599 keys. 1500 + 599 passes the
    // 2000-key cap by 99, so the store refuses, and 99 is the room to make.
    let mut later = Vec::new();
    for i in 501..=1100u32 {
        later.push(
            alice
                .encrypt(format!("two {i}").as_bytes(), &mut r)
                .unwrap(),
        );
    }
    assert_eq!(bob.decrypt(&later[599], &mut r).unwrap(), b"two 1100");

    // Oldest first, and 99 of them from each store. Both halves hold a key
    // for every message of round one, so "one 98" is gone whichever half is
    // sized how, and its absence pins only that an eviction happened at all.
    assert!(
        bob.decrypt(&first[98], &mut r).is_err(),
        "the 99 keys the message displaced must have gone"
    );

    // "one 99" is the pin, and it pins both halves at once: it is the first
    // message whose classical key the 99-key eviction spared, so it decrypts
    // only if the post-quantum store stopped at 99 too. Sized by the skip
    // count the classical half would have taken 599; climbing 1, 2, 4, ... the
    // post-quantum half would have taken 127. Either mistake loses this
    // message.
    assert_eq!(bob.decrypt(&first[99], &mut r).unwrap(), b"one 99");

    // And nothing above it went either, in either store.
    assert_eq!(bob.decrypt(&first[127], &mut r).unwrap(), b"one 127");
    assert_eq!(
        bob.decrypt(&first[MAX_SKIP as usize - 1], &mut r).unwrap(),
        b"one 999"
    );
    assert_eq!(bob.decrypt(&second[0], &mut r).unwrap(), b"two 0");
    assert_eq!(bob.decrypt(&later[0], &mut r).unwrap(), b"two 501");
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

/// The post-quantum sizing has a fallback the arithmetic above cannot reach:
/// a header naming an epoch the state holds no receiving chain for. There is
/// no receive count to compute a shortfall from, so the batch starts at one
/// and climbs geometrically, which is the only place that ramp survives.
///
/// **Nothing a session sends produces that header.** The agreement reports the
/// epoch both parties are known to hold, which is one behind the sender's own,
/// so the message that carries the output opening epoch `e` is itself stamped
/// `e - 1` -- the assertion below pins that, and it is why the branch never
/// fires on honest traffic. A header naming an epoch already *retired* does
/// not reach the sizing either: the sparse ratchet answers `NoChain`, which is
/// not a store-full refusal, and the caller returns before any eviction is
/// considered.
///
/// What is left is a forged header, and that is what this builds: the epoch
/// raised to the one the fold is about to open, and a message number far
/// enough ahead that the store refuses once the fold has happened. The message
/// key never authenticates -- the associated data covers the whole header --
/// so the point is not that it decrypts. The point is the one the forgery test
/// above makes for the classical store: the ramp runs, climbing from one until
/// it has taken hundreds of keys off the working copy, and commits none of it.
#[test]
fn a_forged_header_naming_the_epoch_a_fold_opens_evicts_nothing() {
    let mut r = rng(34);
    let (mut alice, mut bob) = establish(&mut r);

    // Bob sends without hearing back, so his agreement cannot move and every
    // message stays on epoch 0.
    let mut fill = Vec::new();
    for i in 0..=(MAX_SKIP as usize + PQ_MAX_SKIP as usize / 2) {
        fill.push(bob.encrypt(format!("fill {i}").as_bytes(), &mut r).unwrap());
    }

    // Alice takes two of them, and each stores the keys it skipped past: the
    // first a full `MAX_SKIP`, the second the rest. Her post-quantum store is
    // then 1500 of its 2000, which is what makes the forged message's skip
    // overflow it.
    let first = MAX_SKIP as usize;
    let second = fill.len() - 1;
    assert_eq!(
        alice.decrypt(&fill[first], &mut r).unwrap(),
        format!("fill {first}").as_bytes()
    );
    assert_eq!(
        alice.decrypt(&fill[second], &mut r).unwrap(),
        format!("fill {second}").as_bytes()
    );

    // Now let the agreement run to the point where one of Bob's messages
    // carries the output that opens epoch 1 on Alice. Each candidate is tried
    // on a copy first, because the message that folds must not be delivered:
    // it is the one to forge.
    let folding = loop_until_fold(&mut alice, &mut bob, &mut r);

    // The fold-carrying message names the epoch *before* the one it opens.
    // This is the reason the branch below is unreachable without a forgery.
    let mut forged = decode_message(&folding).unwrap();
    assert_eq!(
        forged.header.pq_epoch, 0,
        "the message that opens epoch 1 must still name epoch 0"
    );

    // Forge it: name the epoch the fold is about to open, and a number that
    // skips a full `MAX_SKIP` on a chain that does not exist yet. Once the
    // fold has run, 1500 held plus 1000 skipped passes the 2000-key cap, so
    // the store refuses and the sizing has no receive count to work from.
    forged.header.pq_epoch = 1;
    forged.header.pq_n = PQ_MAX_SKIP + 1;
    let forged_bytes = encode_message(&forged.header, &forged.ciphertext);
    assert!(
        alice.decrypt(&forged_bytes, &mut r).is_err(),
        "a forged header must not authenticate"
    );

    // Nothing was committed. The oldest key Alice holds is the first one an
    // eviction takes, and it is still there.
    assert_eq!(
        alice.decrypt(&fill[0], &mut r).unwrap(),
        b"fill 0",
        "the ramp evicted from the committed state"
    );

    // And the genuine message still folds and decrypts, so the agreement was
    // not moved either.
    assert_eq!(alice.decrypt(&folding, &mut r).unwrap(), b"b");
}

/// Deliver messages both ways until one of Bob's carries the output that opens
/// epoch 1 on Alice, and return that message *undelivered*.
///
/// Nothing public reports the folded epoch, so this reads it off the wire: the
/// epoch a session stamps on its next message moves from 0 to 1 exactly when
/// it folds. `export`/`import` is what makes the question askable without
/// answering it -- the candidate is decrypted on a copy, and the copy is
/// thrown away.
fn loop_until_fold(alice: &mut Session, bob: &mut Session, r: &mut rand::rngs::StdRng) -> Vec<u8> {
    for _ in 0..400 {
        let m = alice.encrypt(b"a", r).unwrap();
        assert_eq!(bob.decrypt(&m, r).unwrap(), b"a");

        let m = bob.encrypt(b"b", r).unwrap();
        let mut probe = Session::import(&alice.export()).unwrap();
        assert_eq!(probe.decrypt(&m, r).unwrap(), b"b");
        if stamped_epoch(&probe, r) == 1 {
            return m;
        }
        assert_eq!(alice.decrypt(&m, r).unwrap(), b"b");
    }
    panic!("the agreement did not reach epoch 1");
}

/// The epoch a session would stamp on its next message, read without keeping
/// the send that reveals it.
fn stamped_epoch(s: &Session, r: &mut rand::rngs::StdRng) -> u64 {
    let mut probe = Session::import(&s.export()).unwrap();
    let m = probe.encrypt(b"probe", r).unwrap();
    decode_message(&m).unwrap().header.pq_epoch
}
