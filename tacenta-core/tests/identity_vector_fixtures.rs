//! Writes `vectors/identity/initial-message-admission.json`.
//!
//! Not part of the suite: it is ignored, and run by hand when the file has to be
//! regenerated,
//!
//! ```text
//! IDENTITY_VECTORS_OUT=tacenta-test-vectors/vectors/identity/initial-message-admission.json \
//!   cargo test -p tacenta-core --test identity_vector_fixtures -- --ignored
//! ```
//!
//! The honest row is a real initial message and the prekey store it was sent to,
//! made from fixed secrets and a fixed byte stream (splitmix64, written out here
//! so the bytes are not hostage to a dependency's generator). The refused rows are
//! that message with its `identity` field replaced by a key the identity-key rule
//! refuses (identities-and-devices.md, Identity keys), so the check has to come
//! before the message is authenticated to give the refusal the row names.

use rand_core::{CryptoRng, RngCore};
use tacenta_core::serialization::{decode_initial, encode_initial};
use tacenta_core::sessions::{
    Identity, PrekeyStore, encode_ec, establish_initiator, establish_responder,
};

const ALICE_SECRET: [u8; 32] = [1u8; 32];
const BOB_SECRET: [u8; 32] = [0xa5u8; 32];

/// `(id, identity key, what it is)`.
const REFUSED: &[(&str, &str, &str)] = &[
    (
        "identity-mixed-order-8",
        "037faa3bbfc676b26f87fb1449a152bcb3eb7cfeeedbaa3604deca93ac75304b",
        "the sender's identity point plus a torsion point of order 8: canonical, on the curve, not of prime order",
    ),
    (
        "identity-mixed-order-4",
        "6722174dbc997c555d35183ae1f5b54d718517e2012641580dc06bf48b5cc67b",
        "the sender's identity point plus a torsion point of order 4: canonical, on the curve, not of prime order",
    ),
    (
        "identity-mixed-order-2",
        "cc80c67924df11225baa5ff7838b65ef4747fc514b11a810fb951106ab3d620a",
        "the sender's identity point plus a torsion point of order 2: canonical, on the curve, not of prime order",
    ),
    (
        "identity-low-order-u0",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "u = 0, a point of order 2",
    ),
    (
        "identity-low-order-u1",
        "0100000000000000000000000000000000000000000000000000000000000000",
        "u = 1, a point of order 4",
    ),
    (
        "identity-low-order-p-minus-1",
        "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        "u = p - 1: canonical, and no point of the curve has this u",
    ),
    (
        "identity-low-order-order8-a",
        "e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800",
        "one of the two u-coordinates of order eight",
    ),
    (
        "identity-off-curve-u2",
        "0200000000000000000000000000000000000000000000000000000000000000",
        "u = 2: canonical, and no point of the curve has this u",
    ),
];

struct Stream {
    at: u64,
}

impl RngCore for Stream {
    fn next_u32(&mut self) -> u32 {
        let mut b = [0u8; 4];
        self.fill_bytes(&mut b);
        u32::from_le_bytes(b)
    }
    fn next_u64(&mut self) -> u64 {
        let mut b = [0u8; 8];
        self.fill_bytes(&mut b);
        u64::from_le_bytes(b)
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        for d in dest.iter_mut() {
            let mut x = self
                .at
                .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .wrapping_add(0x1d);
            x ^= x >> 30;
            x = x.wrapping_mul(0xBF58_476D_1CE4_E5B9);
            x ^= x >> 27;
            x = x.wrapping_mul(0x94D0_49BB_1331_11EB);
            x ^= x >> 31;
            *d = (x & 0xff) as u8;
            self.at = self.at.wrapping_add(1);
        }
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl CryptoRng for Stream {}

fn hex_of(bytes: &[u8]) -> String {
    hex::encode(bytes)
}

#[test]
#[ignore = "writes a vector file; run by hand with IDENTITY_VECTORS_OUT"]
fn write_initial_message_admission_vectors() {
    let out = std::env::var("IDENTITY_VECTORS_OUT").expect("set IDENTITY_VECTORS_OUT");
    let mut rng = Stream { at: 0 };
    let alice = Identity::from_secret(ALICE_SECRET);
    let bob = Identity::from_secret(BOB_SECRET);
    let store = bob.create_prekeys(1, &mut rng);
    let stored = store.to_bytes();
    let bundle = store.publish();
    let mut session = establish_initiator(&alice, &bundle, &mut rng).unwrap();
    let plaintext = b"identity boundary";
    let initial = session.encrypt(plaintext, &mut rng).unwrap();

    // The honest row must establish, on a copy of the store.
    let mut copy = PrekeyStore::from_bytes(&stored).unwrap();
    let (_, recovered) = establish_responder(&bob, &mut copy, &initial, &mut rng).unwrap();
    assert_eq!(recovered, plaintext);

    let message = decode_initial(&initial).unwrap();
    let rows: Vec<String> = {
        let mut rows = vec![row(
            "honest-initial-message",
            "a real initial message and the prekey store it was sent to: the identity key is an identity key, the ratchet message authenticates, and the plaintext is recovered",
            &stored,
            &initial,
            Outcome::Recovered(plaintext),
            &BOB_SECRET,
        )];
        for (id, key, what) in REFUSED {
            let key: [u8; 32] = hex::decode(key).unwrap().try_into().unwrap();
            let named = encode_initial(
                &encode_ec(&tacenta_core::primitives::dh::PublicKeyBytes::from_bytes(
                    key,
                )),
                &message.ephemeral,
                &message.kem_ciphertext,
                message.signed_prekey_id,
                message.one_time_prekey_id,
                message.kem_prekey_id,
                &message.message,
            );
            rows.push(row(
                id,
                &format!("the honest initial message with its identity replaced: {what}. Refused as an invalid identity key, before the message is authenticated and before any private key is used on it"),
                &stored,
                &named,
                Outcome::Refused,
                &BOB_SECRET,
            ));
        }
        // The order of the checks: the identity is refused before an unknown
        // one-time identifier or a ciphertext of the wrong length is.
        let (_, key, _) = REFUSED[0];
        let key: [u8; 32] = hex::decode(key).unwrap().try_into().unwrap();
        let identity = encode_ec(&tacenta_core::primitives::dh::PublicKeyBytes::from_bytes(
            key,
        ));
        let unknown = encode_initial(
            &identity,
            &message.ephemeral,
            &message.kem_ciphertext,
            message.signed_prekey_id,
            u32::MAX - 1,
            message.kem_prekey_id,
            &message.message,
        );
        rows.push(row(
            "identity-mixed-order-8-before-unknown-one-time-identifier",
            "the mixed-order identity of identity-mixed-order-8 on a message that also names a one-time prekey the store does not hold: refused as an invalid identity key, not as an unknown identifier",
            &stored,
            &unknown,
            Outcome::Refused,
            &BOB_SECRET,
        ));
        let short = &message.kem_ciphertext[..message.kem_ciphertext.len() - 1];
        let wrong_length = encode_initial(
            &identity,
            &message.ephemeral,
            short,
            message.signed_prekey_id,
            message.one_time_prekey_id,
            message.kem_prekey_id,
            &message.message,
        );
        rows.push(row(
            "identity-mixed-order-8-before-wrong-length-ciphertext",
            "the mixed-order identity of identity-mixed-order-8 on a message whose KEM ciphertext has the wrong length: refused as an invalid identity key, not by the decapsulation",
            &stored,
            &wrong_length,
            Outcome::Refused,
            &BOB_SECRET,
        ));
        rows
    };
    let text = format!(
        "{{\n  \"schema_version\": 1,\n  \"algorithm\": \"initial-message-admission\",\n  \"source\": \"Generated by tacenta-core (tests/identity_vector_fixtures.rs, run by hand): the honest row is a real initial message and the prekey store it was sent to, made from fixed secrets and a fixed byte stream; each refused row is that message with its identity field replaced. The expected refusal is the specification's: identities-and-devices.md, Identity keys, and session-establishment.md, Receiving the initial message. inputs.bob_identity_secret is the responder's identity secret, inputs.prekey_store the responder's stored prekey store (PrekeyStore::to_bytes) and inputs.initial_message the whole message; a valid vector's output is the plaintext recovered, and a refused vector leaves the prekey store as it was.\",\n  \"vectors\": [\n{}\n  ]\n}}\n",
        rows.join(",\n")
    );
    std::fs::write(&out, text).unwrap();
}

enum Outcome<'a> {
    Recovered(&'a [u8]),
    Refused,
}

fn row(
    id: &str,
    comment: &str,
    store: &[u8],
    message: &[u8],
    outcome: Outcome<'_>,
    bob: &[u8; 32],
) -> String {
    let mut text = format!(
        "    {{\n      \"id\": \"{id}\",\n      \"comment\": \"{comment}\",\n      \"result\": \"{}\",\n      \"inputs\": {{\n        \"bob_identity_secret\": \"{}\",\n        \"prekey_store\": \"{}\",\n        \"initial_message\": \"{}\"\n      }}",
        match outcome {
            Outcome::Recovered(_) => "valid",
            Outcome::Refused => "invalid",
        },
        hex_of(bob),
        hex_of(store),
        hex_of(message),
    );
    match outcome {
        Outcome::Recovered(plaintext) => {
            text.push_str(&format!(",\n      \"output\": \"{}\"", hex_of(plaintext)))
        }
        Outcome::Refused => text.push_str(",\n      \"refusal\": \"invalid-identity-key\""),
    }
    text.push_str("\n    }");
    text
}
