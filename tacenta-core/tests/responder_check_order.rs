//! The responder resolves every identifier an initial message names before it
//! spends a decapsulation on the message, and refuses an unknown identifier as
//! `UnknownPrekeyId` rather than as `Kem` (session-establishment.md, Receiving
//! the initial message; the Session L4 translatability decision requires the
//! carve-out to keep this order and these refusal kinds).
//!
//! The discriminating message names a live KEM prekey, carries a KEM
//! ciphertext of the wrong length, and names a one-time curve prekey the store
//! does not hold. Decapsulating first would refuse it as `Kem`; looking the
//! identifiers up first refuses it as `UnknownPrekeyId`. Either way the store
//! is untouched.

use rand::SeedableRng;
use tacenta_core::serialization::{decode_initial, encode_initial};
use tacenta_core::sessions::{
    Identity, LifecycleError as Error, establish_initiator, establish_responder,
};

fn rng(seed: u64) -> rand::rngs::StdRng {
    rand::rngs::StdRng::seed_from_u64(seed)
}

fn reencode(
    decoded: &tacenta_core::serialization::DecodedInitial,
    kem_ciphertext: &[u8],
    one_time_prekey_id: u32,
) -> Vec<u8> {
    encode_initial(
        &decoded.identity,
        &decoded.ephemeral,
        kem_ciphertext,
        decoded.signed_prekey_id,
        one_time_prekey_id,
        decoded.kem_prekey_id,
        &decoded.message,
    )
}

#[test]
fn an_unknown_identifier_is_refused_before_decapsulation() {
    let mut r = rng(7);
    let alice_id = Identity::generate(&mut r);
    let bob_id = Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(4, &mut r);
    let bundle = bob_prekeys.publish();
    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let initial = alice.encrypt(b"hello", &mut r).unwrap();
    let decoded = decode_initial(&initial).unwrap();
    let store_before = bob_prekeys.to_bytes();

    let short_ct = &decoded.kem_ciphertext[..decoded.kem_ciphertext.len() - 1];
    let unknown_one_time_id = u32::MAX - 1;

    // Wrong-length ciphertext alone: the decapsulation is what refuses it.
    let wrong_ct_only = reencode(&decoded, short_ct, decoded.one_time_prekey_id);
    assert!(matches!(
        establish_responder(&bob_id, &mut bob_prekeys, &wrong_ct_only, &mut r),
        Err(Error::Kem)
    ));

    // Unknown one-time identifier alone: the lookup refuses it.
    let unknown_id_only = reencode(&decoded, &decoded.kem_ciphertext, unknown_one_time_id);
    assert!(matches!(
        establish_responder(&bob_id, &mut bob_prekeys, &unknown_id_only, &mut r),
        Err(Error::UnknownPrekeyId)
    ));

    // Both: the identifier lookup runs first, so its refusal is the one seen.
    let both = reencode(&decoded, short_ct, unknown_one_time_id);
    assert!(matches!(
        establish_responder(&bob_id, &mut bob_prekeys, &both, &mut r),
        Err(Error::UnknownPrekeyId)
    ));

    assert_eq!(
        &*bob_prekeys.to_bytes(),
        &*store_before,
        "every refusal left the store as it was"
    );

    // The genuine message still establishes.
    let (_, plaintext) = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
    assert_eq!(plaintext, b"hello");
}
