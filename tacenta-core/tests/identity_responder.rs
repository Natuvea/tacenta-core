//! The responder's side of identity records (session-establishment.md,
//! Records, expectations and attribution, The responder; REQ-AUTH-15).
//!
//! The responder's establishment does not consult records: whatever identity
//! key an initial message carries, once it passes the identity-key rule and
//! the message authenticates, the session is established and its prekeys are
//! consumed. Attribution is a lookup of the session's peer key against the
//! records as they stand. These tests drive `establish_responder_unattributed`
//! and release its first plaintext only through that lookup.

use rand::SeedableRng;
use tacenta_core::primitives::dh;
use tacenta_core::serialization::{decode_initial, encode_initial};
use tacenta_core::sessions::identity::{
    Attribution, Expectation, Record, establish_initiator, establish_responder_unattributed, lookup,
};
use tacenta_core::sessions::{Identity, LifecycleError, PrekeyStore, SessionError, encode_ec};

fn rng(seed: u64) -> rand::rngs::StdRng {
    rand::rngs::StdRng::seed_from_u64(seed)
}

fn key(text: &str) -> dh::PublicKeyBytes {
    let bytes: [u8; 32] = hex::decode(text).unwrap().try_into().unwrap();
    dh::PublicKeyBytes::from_bytes(bytes)
}

const RFC7748_ALICE_SECRET: &str =
    "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a";
const RFC7748_ALICE_PLUS_TORSION: &str =
    "ec06a18b2851717cbad4dda975daa176baef2f520371e51e5383029272448859";
const U0: &str = "0000000000000000000000000000000000000000000000000000000000000000";
const U2: &str = "0200000000000000000000000000000000000000000000000000000000000000";
const U_P: &str = "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f";

/// `sender` initiates to the owner of `store` under first contact with no
/// records, and the initial message carrying `text` is returned.
fn initial_from(sender: &Identity, store: &PrekeyStore, text: &[u8], seed: u64) -> Vec<u8> {
    let mut r = rng(seed);
    let mut session = establish_initiator(
        sender,
        &store.publish(),
        &Expectation::first_contact(&[]),
        &mut r,
    )
    .unwrap();
    session.encrypt(text, &mut r).unwrap()
}

/// A peer in no record: the session establishes, the prekeys it names are
/// consumed, and the first plaintext and the session are unattributed.
#[test]
fn a_key_in_no_record_gives_an_unattributed_session() {
    let mut r = rng(1);
    let bob = Identity::generate(&mut r);
    let stranger = Identity::generate(&mut r);
    let carol = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(2, &mut r);
    let before = store.one_time_remaining();
    let initial = initial_from(&stranger, &store, b"hello", 2);
    let (mut session, first) =
        establish_responder_unattributed(&bob, &mut store, &initial, &mut r).unwrap();
    assert_eq!(first.peer_identity(), stranger.public());
    assert_eq!(session.peer_identity(), stranger.public());
    assert_eq!(store.one_time_remaining().0, before.0 - 1);
    assert_eq!(store.one_time_remaining().1, before.1 - 1);
    let records = [Record::new(vec![carol.public()], Vec::new())];
    let (found, plaintext) = first.attribute(&records).unwrap();
    assert_eq!(plaintext, b"hello");
    assert_eq!(found.attribution, Attribution::Unattributed);

    // A later plaintext is attributed as the session is: by a lookup of its
    // peer key.
    let reply = session.encrypt(b"who is this", &mut r).unwrap();
    assert!(!reply.is_empty());
    assert_eq!(
        lookup(&session.peer_identity(), &records)
            .unwrap()
            .attribution,
        Attribution::Unattributed
    );
}

/// The same initial message again is refused, and no second session forms;
/// so is its delivery after the session is discarded. The one-time prekeys it
/// named are gone, so the message names a prekey the store no longer holds.
#[test]
fn a_repeat_establishes_nothing_whether_or_not_the_session_is_kept() {
    let mut r = rng(3);
    let bob = Identity::generate(&mut r);
    let stranger = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(2, &mut r);
    let initial = initial_from(&stranger, &store, b"once", 4);
    let (session, _) =
        establish_responder_unattributed(&bob, &mut store, &initial, &mut r).unwrap();
    let after_first = store.to_bytes().to_vec();
    assert_eq!(
        establish_responder_unattributed(&bob, &mut store, &initial, &mut r).err(),
        Some(LifecycleError::UnknownPrekeyId),
        "a replay while the session is kept"
    );
    drop(session);
    assert_eq!(
        establish_responder_unattributed(&bob, &mut store, &initial, &mut r).err(),
        Some(LifecycleError::UnknownPrekeyId),
        "a repeat after the session is discarded"
    );
    assert_eq!(store.to_bytes().to_vec(), after_first);
}

/// On the last-resort path the replay record refuses the repeat instead.
#[test]
fn a_last_resort_repeat_is_refused_by_the_replay_record() {
    let mut r = rng(5);
    let bob = Identity::generate(&mut r);
    let stranger = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(0, &mut r);
    let initial = initial_from(&stranger, &store, b"last resort", 6);
    let (session, _) =
        establish_responder_unattributed(&bob, &mut store, &initial, &mut r).unwrap();
    drop(session);
    assert_eq!(
        establish_responder_unattributed(&bob, &mut store, &initial, &mut r).err(),
        Some(LifecycleError::ReplayedLastResort)
    );
}

/// A key a record holds as retired gives a session that is a retired key of
/// that contact, attributed to nobody.
#[test]
fn a_retired_key_gives_a_session_attributed_to_nobody() {
    let mut r = rng(7);
    let bob = Identity::generate(&mut r);
    let carol_old = Identity::generate(&mut r);
    let carol_new = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(2, &mut r);
    let initial = initial_from(&carol_old, &store, b"old key", 8);
    let (_, first) = establish_responder_unattributed(&bob, &mut store, &initial, &mut r).unwrap();
    let records = [Record::new(
        vec![carol_new.public()],
        vec![carol_old.public()],
    )];
    let (found, _) = first.attribute(&records).unwrap();
    assert_eq!(found.attribution, Attribution::RetiredKey);
    assert_eq!(found.retired_for, vec![0]);
}

/// An initial message whose identity is not an identity key is refused as
/// an invalid identity key before anything changes: no session, the store as
/// it was, and so nothing to look up.
#[test]
fn an_identity_that_is_not_an_identity_key_is_refused_and_changes_nothing() {
    let mut r = rng(9);
    let bob = Identity::generate(&mut r);
    let secret: [u8; 32] = hex::decode(RFC7748_ALICE_SECRET)
        .unwrap()
        .try_into()
        .unwrap();
    let sender = Identity::from_secret(secret);
    let mut store = bob.create_prekeys(2, &mut r);
    let initial = initial_from(&sender, &store, b"twin", 10);
    let message = decode_initial(&initial).unwrap();
    let before = store.to_bytes().to_vec();
    for (id, value) in [
        ("torsion twin", RFC7748_ALICE_PLUS_TORSION),
        ("u = 0", U0),
        (
            "u = 1",
            "0100000000000000000000000000000000000000000000000000000000000000",
        ),
        (
            "u = p - 1",
            "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        ),
        (
            "order 8, a",
            "e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800",
        ),
        (
            "order 8, b",
            "5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157",
        ),
    ] {
        let named = encode_initial(
            &encode_ec(&key(value)),
            &message.ephemeral,
            &message.kem_ciphertext,
            message.signed_prekey_id,
            message.one_time_prekey_id,
            message.kem_prekey_id,
            &message.message,
        );
        assert_eq!(
            establish_responder_unattributed(&bob, &mut store, &named, &mut r).err(),
            Some(LifecycleError::Handshake(SessionError::InvalidIdentityKey)),
            "{id}"
        );
        assert_eq!(store.to_bytes().to_vec(), before, "{id}: the store changed");
    }
}

/// A malformed record is skipped and reported by the lookup; establishment
/// does not consult it and is unchanged.
#[test]
fn a_malformed_record_is_skipped_and_reported() {
    let mut r = rng(11);
    let bob = Identity::generate(&mut r);
    let carol = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(2, &mut r);
    let initial = initial_from(&carol, &store, b"from carol", 12);
    let (_, first) = establish_responder_unattributed(&bob, &mut store, &initial, &mut r).unwrap();
    let records = [
        Record::new(vec![carol.public(), key(U_P)], Vec::new()),
        Record::new(vec![carol.public()], Vec::new()),
    ];
    let (found, plaintext) = first.attribute(&records).unwrap();
    assert_eq!(plaintext, b"from carol");
    assert_eq!(found.attribution, Attribution::Contact(1));
    assert_eq!(found.malformed, vec![0]);
}

/// Attribution follows the records as they stand: a session found to be a
/// contact's is a retired key once the party retires that key.
#[test]
fn retiring_a_key_withdraws_attribution() {
    let mut r = rng(13);
    let bob = Identity::generate(&mut r);
    let carol = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(2, &mut r);
    let initial = initial_from(&carol, &store, b"hi", 14);
    let (session, first) =
        establish_responder_unattributed(&bob, &mut store, &initial, &mut r).unwrap();
    let mut records = vec![Record::new(vec![carol.public()], Vec::new())];
    let (found, _) = first.attribute(&records).unwrap();
    assert_eq!(found.attribution, Attribution::Contact(0));
    records[0].retired.push(carol.public());
    let now = lookup(&session.peer_identity(), &records).unwrap();
    assert_eq!(now.attribution, Attribution::RetiredKey);
    assert_eq!(now.retired_for, vec![0]);
}

/// A key *same* for two records is ambiguous: no contact's.
#[test]
fn a_key_same_for_two_records_is_ambiguous() {
    let mut r = rng(15);
    let bob = Identity::generate(&mut r);
    let carol = Identity::generate(&mut r);
    let dave = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(2, &mut r);
    let initial = initial_from(&carol, &store, b"hi", 16);
    let (_, first) = establish_responder_unattributed(&bob, &mut store, &initial, &mut r).unwrap();
    let records = [
        Record::new(vec![carol.public()], Vec::new()),
        Record::new(vec![dave.public(), carol.public()], Vec::new()),
    ];
    let (found, _) = first.attribute(&records).unwrap();
    assert_eq!(found.attribution, Attribution::Ambiguous);
    assert_eq!(found.same_for, vec![0, 1]);
}

/// A record holding canonical members that are not identity keys is not
/// malformed, and an honest message still establishes.
#[test]
fn a_canonical_non_identity_member_does_not_make_a_record_malformed() {
    let mut r = rng(17);
    let bob = Identity::generate(&mut r);
    let carol = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(2, &mut r);
    let initial = initial_from(&carol, &store, b"hi", 18);
    let (_, first) = establish_responder_unattributed(&bob, &mut store, &initial, &mut r).unwrap();
    let records = [
        Record::new(vec![key(U0), key(U2)], Vec::new()),
        Record::new(vec![carol.public()], vec![key(U0)]),
    ];
    let (found, _) = first.attribute(&records).unwrap();
    assert_eq!(found.attribution, Attribution::Contact(1));
    assert!(found.malformed.is_empty());
}
