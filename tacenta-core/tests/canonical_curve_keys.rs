//! A curve key has one encoding (message-format.md, Curve public keys;
//! session-establishment.md, `DecodeEC`).
//!
//! An initial message whose ephemeral key is spelled any other way is refused
//! as a bad encoding, so it cannot pass for a handshake the responder has not
//! seen. A prekey bundle or a ratchet message carrying a re-spelled curve key
//! does not decode at all.

use rand::SeedableRng;
use tacenta_core::serialization::{
    DecodeError, WireBundle, decode_bundle, decode_initial, decode_message, encode_bundle,
};
use tacenta_core::sessions::{Identity, LifecycleError, establish_initiator, establish_responder};

/// Offset of the last byte of the ephemeral key in an initial message: version
/// and type, the 33-byte identity encoding, then the ephemeral's curve byte at
/// 35 and its 32 key bytes.
const EPHEMERAL_LAST_BYTE: usize = 2 + 33 + 1 + 31;

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

    // The same key with bit 255 set names the same point, and is refused.
    let mut respelled = captured.clone();
    respelled[EPHEMERAL_LAST_BYTE] |= 0x80;
    assert!(matches!(
        establish_responder(&bob, &mut store, &respelled, &mut r),
        Err(LifecycleError::BadEncoding)
    ));
    // And refusing it changed nothing: the original is still a replay.
    assert!(matches!(
        establish_responder(&bob, &mut store, &captured, &mut r),
        Err(LifecycleError::ReplayedLastResort)
    ));
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
