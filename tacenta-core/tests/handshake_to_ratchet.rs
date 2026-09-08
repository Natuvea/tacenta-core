//! The whole stack composing: a PQXDH handshake produces the shared secret, the
//! Double Ratchet starts from it, and a message survives the round trip through
//! the AEAD the ratchet's message key drives.
//!
//! This is the composition the specifications call for. PQXDH says any protocol
//! built on it must randomise the encryption key before the responder replies,
//! because a replayed initial message would otherwise reproduce the same secret;
//! the Double Ratchet's first Diffie-Hellman step is what does that. The
//! responder's signed prekey doubles as its initial ratchet key, which is what
//! lets the ratchet start without another round trip.

use rand::SeedableRng;
use tacenta_core::primitives::{aead, dh, kem, xeddsa};
use tacenta_core::{ratchet, sessions};

#[test]
fn pqxdh_secret_seeds_the_ratchet_and_a_message_round_trips() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);

    // Bob publishes a bundle. His signed prekey is also his initial ratchet key.
    let ik_b_bytes = [0x0bu8; 32];
    let spk_b_bytes = [0x0cu8; 32];
    let ik_b = dh::PrivateKey::from_bytes(ik_b_bytes);
    let spk_b = dh::PrivateKey::from_bytes(spk_b_bytes);
    let opk_b = dh::PrivateKey::from_bytes([0x0du8; 32]);
    let kem_kp = kem::KeyPair::generate(&mut rng);

    let bundle = sessions::PreKeyBundle {
        identity_key: ik_b.public_key(),
        signed_prekey: spk_b.public_key(),
        signed_prekey_signature: xeddsa::sign(
            &ik_b_bytes,
            &sessions::encode_ec(&spk_b.public_key()),
            &mut rng,
        ),
        kem_prekey: kem_kp.public_key(),
        kem_prekey_signature: xeddsa::sign(
            &ik_b_bytes,
            &sessions::encode_kem(&kem_kp.public_key()),
            &mut rng,
        ),
        one_time_prekey: Some(opk_b.public_key()),
    };

    // Alice runs the handshake.
    let ik_a = dh::PrivateKey::from_bytes([0x0au8; 32]);
    let ek_a = dh::PrivateKey::from_bytes([0x0eu8; 32]);
    let (kem_ciphertext, ss_alice) = kem::encapsulate(&bundle.kem_prekey, &mut rng).unwrap();
    let sk_alice = sessions::initiator_shared_secret(&ik_a, &ek_a, &bundle, &ss_alice).unwrap();

    // Bob repeats it from his side.
    let ss_bob = kem::decapsulate(&kem_kp, &kem_ciphertext).unwrap();
    let sk_bob = sessions::responder_shared_secret(
        &ik_b,
        &spk_b,
        Some(&opk_b),
        &ik_a.public_key(),
        &ek_a.public_key(),
        &ss_bob,
    )
    .expect("test keys are not low-order");
    assert_eq!(
        sk_alice, sk_bob,
        "the handshake must agree before the ratchet"
    );

    // The ratchet starts from that secret. Alice's first ratchet key pair agrees
    // with Bob's signed prekey, which is the value both sides feed the ratchet.
    let ratchet_a = dh::PrivateKey::from_bytes([0xa1u8; 32]);
    let dh_a_to_b = ratchet_a
        .agree(&spk_b.public_key())
        .expect("test keys are not low-order");

    let mut alice = ratchet::init_sender(
        &sk_alice,
        *ratchet_a.public_key().as_bytes(),
        *spk_b.public_key().as_bytes(),
        &dh_a_to_b,
        ratchet::LabelSet::Tacenta,
    );
    let mut bob = ratchet::init_receiver(
        &sk_bob,
        *spk_b.public_key().as_bytes(),
        ratchet::LabelSet::Tacenta,
    );

    // Alice sends; the message key drives the AEAD.
    let (header, mk_send) = ratchet::send(&mut alice).unwrap();
    let (enc, mac, iv) = ratchet::message_keys(&mk_send, ratchet::LabelSet::Tacenta);
    let associated = sessions::associated_data(
        &sessions::encode_ec(&ik_a.public_key()),
        &sessions::encode_ec(&ik_b.public_key()),
    );
    let ciphertext = aead::encrypt(&enc, &mac, &iv, b"the whole stack composes", &associated);

    // Bob receives. His ratchet step uses DH(his signed prekey, her ratchet key),
    // which is the same agreement Alice computed, by DH symmetry.
    let dh_b_to_a = spk_b
        .agree(&ratchet_a.public_key())
        .expect("test keys are not low-order");
    let bob_next_ratchet = dh::PrivateKey::from_bytes([0xb1u8; 32]);
    let dh_b_new = bob_next_ratchet
        .agree(&ratchet_a.public_key())
        .expect("test keys are not low-order");
    let mk_recv = ratchet::receive(
        &mut bob,
        &header,
        &dh_b_to_a,
        &dh_b_new,
        *bob_next_ratchet.public_key().as_bytes(),
    )
    .unwrap();
    assert_eq!(
        mk_send, mk_recv,
        "the ratchet must agree on the message key"
    );

    let (enc_r, mac_r, iv_r) = ratchet::message_keys(&mk_recv, ratchet::LabelSet::Tacenta);
    let plaintext = aead::decrypt(&enc_r, &mac_r, &iv_r, &ciphertext, &associated).unwrap();
    assert_eq!(plaintext, b"the whole stack composes");
}
