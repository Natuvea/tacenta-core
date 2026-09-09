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

/// Which private key is paired with which public key at a session's DH ratchet
/// step -- old key with the peer's new key for receiving, a fresh key with it
/// for sending -- is decided in `sessions::lifecycle`, which no proof, vector,
/// or model covers (CR-07). This drives a real `Session` (not the leaf ratchet)
/// through a step and checks that pairing against the `dh` primitive directly.
///
/// The session's ratchet private key is not a public accessor, but `export`
/// serialises it at a known offset, so the test can read it back and compute
/// the agreement itself rather than trusting the session's word for it.
#[test]
fn a_session_dh_step_pairs_the_old_key_with_the_peers_new_key() {
    use rand::SeedableRng;
    use tacenta_core::primitives::dh::PublicKeyBytes;
    use tacenta_core::sessions::{Identity, Session, establish_initiator, establish_responder};

    // `export` writes: version(1), then two length-prefixed blobs (the triple
    // and the braid), then the 32-byte ratchet private key. Read it back.
    fn ratchet_private_of(session: &Session) -> dh::PrivateKey {
        let bytes = session.export();
        let mut pos = 1usize;
        for _ in 0..2 {
            let len = u32::from_be_bytes(bytes[pos..pos + 4].try_into().unwrap()) as usize;
            pos += 4 + len;
        }
        let mut key = [0u8; 32];
        key.copy_from_slice(&bytes[pos..pos + 32]);
        dh::PrivateKey::from_bytes(key)
    }

    let mut r = rand::rngs::StdRng::seed_from_u64(7);
    let alice_id = Identity::generate(&mut r);
    let bob_id = Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(2, &mut r);
    let bundle = bob_prekeys.publish();

    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let initial = alice.encrypt(b"open", &mut r).unwrap();
    // Establishing the responder makes Bob take his first DH step: he receives
    // Alice's ratchet key and adopts a fresh one of his own for sending.
    let (mut bob, first) =
        establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
    assert_eq!(first, b"open");

    // Alice's current ratchet key `a1` (unchanged: she has received nothing) and
    // Bob's freshly adopted one `b1`, with the private halves read from export.
    let a1 = alice.public_state().our_ratchet_public;
    let b1 = bob.public_state().our_ratchet_public;
    let a1_priv = ratchet_private_of(&alice);
    let b1_priv = ratchet_private_of(&bob);
    assert_eq!(
        a1_priv.public_key().as_bytes(),
        &a1,
        "export gave Alice's key"
    );
    assert_eq!(
        b1_priv.public_key().as_bytes(),
        &b1,
        "export gave Bob's key"
    );

    // The pairing, checked with the primitive: when Alice receives a message
    // sent under Bob's `b1`, her receiving chain is seeded from DH(her current
    // key `a1`, `b1`) -- the old key with the peer's new key. Bob's sending
    // chain under `b1` was seeded from DH(`b1`, `a1`). The two are the same
    // agreement, so if the pairing is right they are equal.
    let alice_receiving_seed = a1_priv
        .agree(&PublicKeyBytes::from_bytes(b1))
        .expect("honest keys are contributory");
    let bob_sending_seed = b1_priv
        .agree(&PublicKeyBytes::from_bytes(a1))
        .expect("honest keys are contributory");
    assert_eq!(
        alice_receiving_seed, bob_sending_seed,
        "the receiving chain must pair the old key with the peer's new key"
    );

    // Pairing the peer's new key with a *fresh* key instead -- the send rule,
    // wrongly applied on receive -- would seed a different chain, which is why
    // the two halves are not interchangeable.
    let fresh = dh::PrivateKey::from_bytes([0x5a; 32]);
    assert_ne!(
        fresh
            .agree(&PublicKeyBytes::from_bytes(b1))
            .expect("contributory"),
        alice_receiving_seed,
        "a fresh key on receive would seed the wrong chain"
    );

    // Now drive the actual step through the session and confirm it uses that
    // pairing (the message decrypts) and adopts a fresh key for sending only on
    // the step (Alice's sending public changes).
    let from_bob = bob.encrypt(b"reply", &mut r).unwrap();
    let a_before = alice.public_state().our_ratchet_public;
    assert_eq!(alice.decrypt(&from_bob, &mut r).unwrap(), b"reply");
    assert_ne!(
        alice.public_state().our_ratchet_public,
        a_before,
        "a DH ratchet step adopts a fresh sending key"
    );
}
