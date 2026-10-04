//! The comparison `Session::decrypt` makes before it accepts a repeated initial message
//! (session-establishment.md, Receiving the initial message): the message's ephemeral must be in the
//! X25519 agreement class of the stored `established_ephemeral` under the session's
//! `ratchet_private`, with both agreements contributory and their outputs equal.
//!
//! Each test refuses one wrong form of that comparison, and together they hold all of it:
//!
//! - a comparison that accepts any two contributory agreements, whatever their outputs, accepts a
//!   repeat that carries another initiator's ephemeral (`another_contributory_ephemeral_is_refused`);
//! - one that compares the two keys' bytes instead of their agreements refuses a torsion-equivalent
//!   spelling of the stored key (`a_torsion_equivalent_ephemeral_is_accepted`);
//! - one that accepts when the incoming agreement is refused accepts a low-order incoming ephemeral
//!   (`a_low_order_incoming_ephemeral_is_refused`);
//! - one that accepts when the stored agreement is refused, alone or with the incoming one, accepts
//!   a repeat against a session whose stored ephemeral is low order
//!   (`a_low_order_stored_ephemeral_matches_nothing`). Establishment never stores such a key, but
//!   `Session::import` accepts one, because its shape rule asks only for a canonical encoding.
//!
//! The comparison is private, so each test drives it through `Session::decrypt`, and each refusal
//! is also shown to leave the session unchanged.

use curve25519_dalek::edwards::{CompressedEdwardsY, EdwardsPoint};
use curve25519_dalek::montgomery::MontgomeryPoint;
use curve25519_dalek::traits::IsIdentity;
use rand::SeedableRng;
use rand::rngs::StdRng;
use tacenta_core::sessions::{
    Identity, LifecycleError, Session, establish_initiator, establish_responder,
};

/// The thirty-two key bytes of an initial message's `ephemeral` field: after the version and type
/// bytes, the 33-byte `identity` and the curve byte of `ephemeral`.
const EPHEMERAL: core::ops::Range<usize> = 36..68;

fn ephemeral(message: &[u8]) -> [u8; 32] {
    let mut key = [0u8; 32];
    key.copy_from_slice(&message[EPHEMERAL]);
    key
}

fn with_ephemeral(message: &[u8], key: [u8; 32]) -> Vec<u8> {
    let mut out = message.to_vec();
    out[EPHEMERAL].copy_from_slice(&key);
    out
}

/// A responder session established from an initiator's first initial message, the initiator's
/// second initial message (a repeat of the first around another ratchet message), and the first
/// initial message of a second initiator to the same bundle, whose ephemeral is another
/// contributory key.
struct Setting {
    responder: Session,
    first: Vec<u8>,
    repeat: Vec<u8>,
    other: Vec<u8>,
    rng: StdRng,
}

fn setting(seed: u64) -> Setting {
    let mut rng = StdRng::seed_from_u64(seed);
    let alice = Identity::generate(&mut rng);
    let bob = Identity::generate(&mut rng);
    let mut store = bob.create_prekeys(0, &mut rng);
    let bundle = store.publish_multi_use();
    let mut initiator = establish_initiator(&alice, &bundle, &mut rng).unwrap();
    let first = initiator.encrypt(b"first", &mut rng).unwrap();
    let repeat = initiator.encrypt(b"second", &mut rng).unwrap();
    let mut second_initiator = establish_initiator(&alice, &bundle, &mut rng).unwrap();
    let other = second_initiator.encrypt(b"other", &mut rng).unwrap();
    assert_ne!(ephemeral(&other), ephemeral(&first));
    let (responder, plaintext) = establish_responder(&bob, &mut store, &first, &mut rng).unwrap();
    assert_eq!(plaintext, b"first");
    Setting {
        responder,
        first,
        repeat,
        other,
        rng,
    }
}

/// `decrypt` refuses `message` as not a repeat and leaves the session as it was.
fn refused_as_not_a_repeat(session: &mut Session, message: &[u8], rng: &mut StdRng) {
    let before = session.export().to_vec();
    assert!(matches!(
        session.decrypt(message, rng),
        Err(LifecycleError::NotARepeatedInitial)
    ));
    assert_eq!(session.export().to_vec(), before);
}

#[test]
fn another_contributory_ephemeral_is_refused() {
    for seed in [1u64, 2, 3] {
        let mut s = setting(0x5245_5045_4154 + seed);
        // The repeat's wrapper with the second initiator's ephemeral: a contributory key whose
        // agreement with the session's ratchet key differs from the stored one's.
        let wrapped = with_ephemeral(&s.repeat, ephemeral(&s.other));
        refused_as_not_a_repeat(&mut s.responder, &wrapped, &mut s.rng);
        // The second initiator's own initial message is not a repeat of this session either.
        refused_as_not_a_repeat(&mut s.responder, &s.other, &mut s.rng);
        // The genuine repeat is still accepted, so the refusals were about the ephemeral.
        assert_eq!(
            s.responder.decrypt(&s.repeat, &mut s.rng).unwrap(),
            b"second"
        );
    }
}

fn order8() -> EdwardsPoint {
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(
        &hex::decode("c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a").unwrap(),
    );
    let point = CompressedEdwardsY(bytes).decompress().unwrap();
    assert!(point.is_small_order());
    assert!(!(point + point + point + point).is_identity());
    point
}

/// A canonical u-coordinate other than `key` in the same X25519 agreement class: `key`'s point
/// plus a point of order 8.
fn torsion_spelling(key: [u8; 32]) -> [u8; 32] {
    let point = MontgomeryPoint(key).to_edwards(0).unwrap();
    let spelling = (point + order8()).to_montgomery().to_bytes();
    assert_ne!(spelling, key);
    assert!(spelling[31] < 0x80);
    spelling
}

#[test]
fn a_torsion_equivalent_ephemeral_is_accepted() {
    let mut s = setting(0x544f_5253);
    let spelling = torsion_spelling(ephemeral(&s.first));
    let wrapped = with_ephemeral(&s.repeat, spelling);
    assert_eq!(
        s.responder.decrypt(&wrapped, &mut s.rng).unwrap(),
        b"second"
    );
}

#[test]
fn a_low_order_incoming_ephemeral_is_refused() {
    let mut s = setting(0x4c4f_5749);
    for key in [[0u8; 32], {
        let mut one = [0u8; 32];
        one[0] = 1;
        one
    }] {
        let wrapped = with_ephemeral(&s.repeat, key);
        refused_as_not_a_repeat(&mut s.responder, &wrapped, &mut s.rng);
    }
    assert_eq!(
        s.responder.decrypt(&s.repeat, &mut s.rng).unwrap(),
        b"second"
    );
}

#[test]
fn a_low_order_stored_ephemeral_matches_nothing() {
    let mut s = setting(0x4c4f_5753);
    // The stored ephemeral is the last field of the exported session: its curve byte, then its key.
    let mut bytes = s.responder.export().to_vec();
    let at = bytes.len() - 32;
    assert_eq!(bytes[at - 1], 0x05);
    assert_eq!(bytes[at..], ephemeral(&s.first));
    bytes[at..].fill(0);
    let mut patched = Session::import(&bytes).expect("a canonical stored ephemeral is accepted");
    // A repeat with the genuine ephemeral (stored agreement refused, incoming contributory) and one
    // with a low-order ephemeral (both refused) are each refused.
    refused_as_not_a_repeat(&mut patched, &s.repeat, &mut s.rng);
    let low = with_ephemeral(&s.repeat, [0u8; 32]);
    refused_as_not_a_repeat(&mut patched, &low, &mut s.rng);
}
