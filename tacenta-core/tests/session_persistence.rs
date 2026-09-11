//! `Session::export`/`import`: a session survives being serialized to bytes
//! and restored, resuming exactly where it left off -- the point of session persistence.
//! `export`ing mid-conversation and continuing from the imported copy is the
//! shape a real storage layer needs, not just a static round trip.

use rand::SeedableRng;
use tacenta_core::sessions::{
    self, Session, SessionDecodeError, establish_initiator, establish_responder,
};

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

/// A session exported and re-imported mid-conversation keeps encrypting and
/// decrypting exactly as the original would have, across a simulated process
/// restart rather than just as a static blob.
#[test]
fn a_session_survives_export_and_import() {
    let mut r = rng(100);
    let (mut alice, mut bob, _first) = establish(&mut r);

    // A few turns each way before the "restart", so both ratchets and the
    // Braid have advanced past their initial state.
    for i in 0..5u8 {
        let a = alice.encrypt(&[b'a', i], &mut r).unwrap();
        assert_eq!(bob.decrypt(&a, &mut r).unwrap(), &[b'a', i]);
        let b = bob.encrypt(&[b'b', i], &mut r).unwrap();
        assert_eq!(alice.decrypt(&b, &mut r).unwrap(), &[b'b', i]);
    }

    // "Restart": export Alice's session, drop it, and import the bytes back.
    let bytes = alice.export();
    drop(alice);
    let mut alice = Session::import(&bytes).unwrap();

    // The conversation keeps going from the restored session, both directions.
    for i in 5..10u8 {
        let a = alice.encrypt(&[b'a', i], &mut r).unwrap();
        assert_eq!(bob.decrypt(&a, &mut r).unwrap(), &[b'a', i]);
        let b = bob.encrypt(&[b'b', i], &mut r).unwrap();
        assert_eq!(alice.decrypt(&b, &mut r).unwrap(), &[b'b', i]);
    }
}

/// Out-of-order delivery still recovers after a restart: the skipped-key
/// stores in both ratchets have to have round-tripped, not just the counters.
#[test]
fn a_restored_session_still_recovers_out_of_order_messages() {
    let mut r = rng(101);
    let (mut alice, bob, _first) = establish(&mut r);

    // Warm up a bit so there is real ratchet state to carry across.
    let mut bob = bob;
    for i in 0..3u8 {
        let a = alice.encrypt(&[b'a', i], &mut r).unwrap();
        assert_eq!(bob.decrypt(&a, &mut r).unwrap(), &[b'a', i]);
    }

    let bytes = bob.export();
    drop(bob);
    let mut bob = Session::import(&bytes).unwrap();

    let m0 = alice.encrypt(b"zero", &mut r).unwrap();
    let m1 = alice.encrypt(b"one", &mut r).unwrap();
    let m2 = alice.encrypt(b"two", &mut r).unwrap();
    assert_eq!(bob.decrypt(&m2, &mut r).unwrap(), b"two");
    assert_eq!(bob.decrypt(&m0, &mut r).unwrap(), b"zero");
    assert_eq!(bob.decrypt(&m1, &mut r).unwrap(), b"one");
}

/// A session exported right after establishment -- before either side has
/// sent a reply, an initiator's `pending_initial` still set -- round-trips
/// too, and the restored initiator still repeats its initial message
/// correctly.
#[test]
fn a_freshly_established_session_survives_export_and_import() {
    let mut r = rng(102);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(4, &mut r);
    let bundle = bob_prekeys.publish();

    let alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let bytes = alice.export();
    let mut restored = Session::import(&bytes).unwrap();

    let initial = restored.encrypt(b"hello bob", &mut r).unwrap();
    let (_bob, first) = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
    assert_eq!(first, b"hello bob");
}

/// Corrupt or foreign-version bytes are refused rather than silently misread.
#[test]
fn import_rejects_a_foreign_version() {
    let mut r = rng(103);
    let (alice, _bob, _first) = establish(&mut r);
    let mut bytes = alice.export();
    bytes[0] = 0xff;
    assert!(matches!(
        Session::import(&bytes),
        Err(SessionDecodeError::UnknownVersion)
    ));
}

#[test]
fn import_rejects_a_truncated_buffer() {
    let mut r = rng(104);
    let (alice, _bob, _first) = establish(&mut r);
    let bytes = alice.export();
    assert!(Session::import(&bytes[..bytes.len() - 1]).is_err());
}

#[test]
fn import_rejects_trailing_bytes() {
    let mut r = rng(105);
    let (alice, _bob, _first) = establish(&mut r);
    let mut bytes = alice.export().to_vec();
    bytes.push(0x00);
    assert!(matches!(
        Session::import(&bytes),
        Err(SessionDecodeError::Malformed)
    ));
}

/// A session whose Braid holds a key pair with a wrong header hash is refused
/// as malformed. The Braid's own reader refuses the key pair
/// (session-persistence.md, Braid; register item J-4), and the session reader
/// reports a half its own reader refuses as malformed, before the re-encode
/// check.
#[test]
fn import_rejects_a_braid_key_pair_whose_hash_is_not_its_own() {
    let mut r = rng(106);
    let (alice, _bob, _first) = establish(&mut r);
    let mut bytes = alice.export().to_vec();
    assert!(Session::import(&bytes).is_ok(), "the honest export imports");

    // session = version(1) || len(4) || triple_state || len(4) || braid || ...
    let triple_len = u32::from_be_bytes(bytes[1..5].try_into().unwrap()) as usize;
    let braid = 1 + 4 + triple_len + 4;
    // The Braid's version and tag, then its epoch and authenticator. In tags
    // 1 to 4 the key pair comes next, behind its own length prefix.
    let tag = bytes[braid + 1];
    assert!(
        (1..=4).contains(&tag),
        "an initiator that has sent holds a key pair; tag {tag}"
    );
    let key_pair = braid + 2 + 8 + 64 + 4;
    // The header's hash is bytes 32 to 63 of the key pair; the braid crate's
    // tests read that offset from the library rather than assume it.
    bytes[key_pair + 32] ^= 0x01;
    assert!(matches!(
        Session::import(&bytes),
        Err(SessionDecodeError::Malformed)
    ));
}
