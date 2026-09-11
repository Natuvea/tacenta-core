//! A curve key has one encoding (message-format.md, Curve public keys;
//! session-establishment.md, `DecodeEC`).
//!
//! An initial message, a prekey bundle or a ratchet message carrying a
//! re-spelled curve key does not decode at all. So an initial message whose
//! identity or ephemeral key is spelled any other way cannot pass for a
//! handshake the responder has not seen, nor for a repeat of one it has.

use rand::SeedableRng;
use tacenta_core::serialization::{
    DecodeError, WireBundle, decode_bundle, decode_initial, decode_message, encode_bundle,
};
use tacenta_core::sessions::{
    Identity, LifecycleError, encode_ec, establish_initiator, establish_responder,
};

/// Where the identity's thirty-two key bytes start in an initial message:
/// after the version and type bytes and the identity's curve byte.
const IDENTITY_KEY: usize = 2 + 1;

/// Where the ephemeral's thirty-two key bytes start: after the 33-byte identity
/// encoding and the ephemeral's curve byte.
const EPHEMERAL_KEY: usize = 2 + 33 + 1;

/// Offset of the last byte of the ephemeral key in an initial message: version
/// and type, the 33-byte identity encoding, then the ephemeral's curve byte at
/// 35 and its 32 key bytes.
const EPHEMERAL_LAST_BYTE: usize = EPHEMERAL_KEY + 31;

/// p = 2^255 - 19, little-endian.
fn p() -> [u8; 32] {
    let mut p = [0xffu8; 32];
    p[0] = 0xed;
    p[31] = 0x7f;
    p
}

/// The two other spellings of an honest key `k`: bit 255 set, and `k + p`.
/// Both name the key `k` does, because X25519 ignores bit 255 and reduces
/// modulo p.
fn respellings(k: &[u8; 32]) -> [[u8; 32]; 2] {
    let mut high = *k;
    high[31] |= 0x80;
    let mut plus_p = [0u8; 32];
    let mut carry = 0u16;
    for ((out, a), b) in plus_p.iter_mut().zip(k).zip(p()) {
        let sum = u16::from(*a) + u16::from(b) + carry;
        *out = sum.to_le_bytes()[0];
        carry = sum >> 8;
    }
    assert_eq!(carry, 0, "an honest key is below p, so adding p fits");
    [high, plus_p]
}

#[test]
fn a_last_resort_first_contact_with_a_respelled_ephemeral_is_refused() {
    let mut r = rand::rngs::StdRng::seed_from_u64(7);
    let bob = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(0, &mut r);
    let bundle = store.publish_multi_use();
    let alice = Identity::generate(&mut r);
    let mut session = establish_initiator(&alice, &bundle, &mut r).unwrap();
    let captured = session.encrypt(b"first", &mut r).unwrap();
    assert_eq!(captured[35], 0x05, "the ephemeral's curve byte");
    assert_eq!(
        captured[EPHEMERAL_LAST_BYTE] & 0x80,
        0,
        "an honest key is canonical"
    );

    assert!(establish_responder(&bob, &mut store, &captured, &mut r).is_ok());
    assert!(matches!(
        establish_responder(&bob, &mut store, &captured, &mut r),
        Err(LifecycleError::ReplayedLastResort)
    ));

    // The same key with bit 255 set names the same point, and does not decode.
    let mut respelled = captured.clone();
    respelled[EPHEMERAL_LAST_BYTE] |= 0x80;
    assert!(matches!(
        establish_responder(&bob, &mut store, &respelled, &mut r),
        Err(LifecycleError::Decode(DecodeError::WrongType))
    ));
    // And refusing it changed nothing: the original is still a replay.
    assert!(matches!(
        establish_responder(&bob, &mut store, &captured, &mut r),
        Err(LifecycleError::ReplayedLastResort)
    ));
}

/// The initial message a real session sends, with its identity or its
/// ephemeral key re-spelled both ways in place, does not decode, and a
/// responder refuses it as a decode failure without touching its store.
#[test]
fn an_initial_message_with_a_respelled_key_is_refused_at_decode() {
    let mut r = rand::rngs::StdRng::seed_from_u64(17);
    let bob = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(1, &mut r);
    let bundle = store.publish();
    let alice = Identity::generate(&mut r);
    let mut session = establish_initiator(&alice, &bundle, &mut r).unwrap();
    let initial = session.encrypt(b"first", &mut r).unwrap();
    decode_initial(&initial).expect("the honest initial message decodes");

    for (at, position) in [(IDENTITY_KEY, "identity"), (EPHEMERAL_KEY, "ephemeral")] {
        let mut honest = [0u8; 32];
        honest.copy_from_slice(&initial[at..at + 32]);
        for key in respellings(&honest) {
            let mut respelled = initial.clone();
            respelled[at..at + 32].copy_from_slice(&key);
            assert_eq!(
                decode_initial(&respelled),
                Err(DecodeError::WrongType),
                "a re-spelled {position}"
            );
            let before = store.to_bytes().to_vec();
            assert!(
                matches!(
                    establish_responder(&bob, &mut store, &respelled, &mut r),
                    Err(LifecycleError::Decode(DecodeError::WrongType))
                ),
                "a re-spelled {position} reached establishment"
            );
            assert_eq!(store.to_bytes().to_vec(), before, "{position}");
        }
    }
    // The honest message still establishes.
    assert!(establish_responder(&bob, &mut store, &initial, &mut r).is_ok());
}

/// A repeated initial message is matched on its identity as well as its
/// ephemeral (session-establishment.md, Receiving the initial message).
///
/// The repeat an initiator sends is read. The same repeat carrying another
/// identity, a real key in its canonical encoding, is not a repeat; carrying
/// the session's own peer identity re-spelled, it does not decode. Before the
/// identity was compared, the first of those was accepted and its ratchet
/// message decrypted. Neither refusal changes the session: the unaltered
/// repeat is still read afterwards, which the ratchet would refuse had either
/// consumed it.
#[test]
fn a_repeated_initial_message_must_carry_the_sessions_peer_identity() {
    let mut r = rand::rngs::StdRng::seed_from_u64(19);
    let bob = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(1, &mut r);
    let bundle = store.publish();
    let alice = Identity::generate(&mut r);
    let mut session = establish_initiator(&alice, &bundle, &mut r).unwrap();
    let first = session.encrypt(b"first", &mut r).unwrap();
    let (mut responder, plaintext) = establish_responder(&bob, &mut store, &first, &mut r).unwrap();
    assert_eq!(plaintext, b"first");

    // Alice has not heard back, so her next message repeats the initial one.
    let repeat = session.encrypt(b"second", &mut r).unwrap();
    assert_eq!(
        repeat[..EPHEMERAL_KEY + 32],
        first[..EPHEMERAL_KEY + 32],
        "the repeat carries the establishing message's keys"
    );
    assert_eq!(&repeat[2..2 + 33], encode_ec(&alice.public()).as_slice());

    let carol = Identity::generate(&mut r);
    let mut other = repeat.clone();
    other[2..2 + 33].copy_from_slice(&encode_ec(&carol.public()));
    assert!(
        matches!(
            responder.decrypt(&other, &mut r),
            Err(LifecycleError::NotARepeatedInitial)
        ),
        "a repeat carrying another identity was accepted"
    );

    let mut honest = [0u8; 32];
    honest.copy_from_slice(&repeat[IDENTITY_KEY..IDENTITY_KEY + 32]);
    for key in respellings(&honest) {
        let mut respelled = repeat.clone();
        respelled[IDENTITY_KEY..IDENTITY_KEY + 32].copy_from_slice(&key);
        assert!(
            matches!(
                responder.decrypt(&respelled, &mut r),
                Err(LifecycleError::Decode(DecodeError::WrongType))
            ),
            "a repeat carrying a re-spelled identity decoded"
        );
    }

    assert_eq!(responder.decrypt(&repeat, &mut r).unwrap(), b"second");
}

/// A published bundle's three curve keys, each re-spelled both ways, and the
/// bundle carrying any one of them does not decode.
#[test]
fn a_bundle_with_a_respelled_curve_key_is_refused_at_decode() {
    let mut r = rand::rngs::StdRng::seed_from_u64(11);
    let bob = Identity::generate(&mut r);
    let store = bob.create_prekeys(1, &mut r);
    let published = store.publish();
    let b = &published.bundle;
    let one_time = b
        .one_time_prekey
        .as_ref()
        .expect("the store holds a one-time prekey");
    let honest = WireBundle {
        identity_key: *b.identity_key.as_bytes(),
        signed_prekey: *b.signed_prekey.as_bytes(),
        signed_prekey_signature: b.signed_prekey_signature,
        kem_prekey: b.kem_prekey.clone(),
        kem_prekey_signature: b.kem_prekey_signature,
        one_time_prekey: Some(*one_time.as_bytes()),
        signed_prekey_id: published.signed_prekey_id,
        one_time_prekey_id: published.one_time_prekey_id,
        kem_prekey_id: published.kem_prekey_id,
    };
    assert_eq!(
        decode_bundle(&encode_bundle(&honest)),
        Ok(honest.clone()),
        "the honest bundle decodes"
    );

    for key in respellings(&honest.identity_key) {
        let bundle = WireBundle {
            identity_key: key,
            ..honest.clone()
        };
        assert_eq!(
            decode_bundle(&encode_bundle(&bundle)),
            Err(DecodeError::WrongType),
            "a re-spelled identity key"
        );
    }
    for key in respellings(&honest.signed_prekey) {
        let bundle = WireBundle {
            signed_prekey: key,
            ..honest.clone()
        };
        assert_eq!(
            decode_bundle(&encode_bundle(&bundle)),
            Err(DecodeError::WrongType),
            "a re-spelled signed prekey"
        );
    }
    for key in respellings(one_time.as_bytes()) {
        let bundle = WireBundle {
            one_time_prekey: Some(key),
            ..honest.clone()
        };
        assert_eq!(
            decode_bundle(&encode_bundle(&bundle)),
            Err(DecodeError::WrongType),
            "a re-spelled one-time prekey"
        );
    }
}

/// The ratchet message a real session sends, with its header's `dh` re-spelled
/// both ways in place, does not decode.
#[test]
fn a_ratchet_message_with_a_respelled_ratchet_key_is_refused_at_decode() {
    let mut r = rand::rngs::StdRng::seed_from_u64(13);
    let bob = Identity::generate(&mut r);
    let store = bob.create_prekeys(0, &mut r);
    let bundle = store.publish_multi_use();
    let alice = Identity::generate(&mut r);
    let mut session = establish_initiator(&alice, &bundle, &mut r).unwrap();
    let initial = session.encrypt(b"first", &mut r).unwrap();
    let message = decode_initial(&initial)
        .expect("the initial message decodes")
        .message;
    let honest = decode_message(&message).expect("its ratchet message decodes");

    for key in respellings(&honest.header.dh) {
        let mut respelled = message.clone();
        // The header's `dh` follows the version and type bytes.
        respelled[2..34].copy_from_slice(&key);
        assert_eq!(decode_message(&respelled), Err(DecodeError::WrongType));
    }
}
