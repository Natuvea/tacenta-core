//! Regression tests for canonical X25519 keys that share one agreement class.
//!
//! The wire decoder accepts canonical u-coordinates, and X25519 can have more
//! than one such coordinate for the same clamped agreement when a torsion
//! component is added. A repeat of an initial message must therefore use the
//! agreement class, while the identity field remains byte-bound by the AEAD.

use curve25519_dalek::edwards::{CompressedEdwardsY, EdwardsPoint};
use curve25519_dalek::montgomery::MontgomeryPoint;
use curve25519_dalek::traits::IsIdentity;
use rand::SeedableRng;
use tacenta_core::sessions::{Identity, LifecycleError, establish_initiator, establish_responder};

const EPHEMERAL: core::ops::Range<usize> = 36..68;

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

/// Return the seven other canonical u-coordinates in the initiator's
/// agreement class.
fn torsion_spellings(ephemeral: [u8; 32]) -> Vec<[u8; 32]> {
    let point = MontgomeryPoint(ephemeral).to_edwards(0).unwrap();
    let torsion = order8();
    let mut out = Vec::new();
    let mut multiple = torsion;
    for _ in 1..8 {
        let spelling = (point + multiple).to_montgomery().to_bytes();
        assert_ne!(spelling, ephemeral);
        assert!(spelling[31] < 0x80);
        out.push(spelling);
        multiple += torsion;
    }
    out.sort();
    out.dedup();
    assert_eq!(out.len(), 7);
    out
}

fn replace_ephemeral(message: &[u8], spelling: [u8; 32]) -> Vec<u8> {
    let mut message = message.to_vec();
    message[EPHEMERAL].copy_from_slice(&spelling);
    message
}

fn ephemeral(message: &[u8]) -> [u8; 32] {
    let mut ephemeral = [0u8; 32];
    ephemeral.copy_from_slice(&message[EPHEMERAL]);
    ephemeral
}

#[test]
fn torsion_equivalent_initial_repeat_stays_in_the_established_session() {
    for one_time_count in [0, 2] {
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x544f5253494f4e + one_time_count as u64);
        let alice = Identity::generate(&mut rng);
        let bob = Identity::generate(&mut rng);
        let mut store = bob.create_prekeys(one_time_count, &mut rng);
        let bundle = if one_time_count == 0 {
            store.publish_multi_use()
        } else {
            store.publish()
        };
        let mut initiator = establish_initiator(&alice, &bundle, &mut rng).unwrap();
        let first = initiator.encrypt(b"first", &mut rng).unwrap();
        let repeat = initiator.encrypt(b"second", &mut rng).unwrap();
        let spelling = torsion_spellings(ephemeral(&first))[0];

        // The attacker changes only the first wrapper's canonical ephemeral.
        // It remains an authenticated initial message because the ephemeral
        // is not in the initial ciphertext's associated data.
        let (mut responder, plaintext) = establish_responder(
            &bob,
            &mut store,
            &replace_ephemeral(&first, spelling),
            &mut rng,
        )
        .unwrap();
        assert_eq!(plaintext, b"first");

        // The genuine repeat belongs to the same X25519 agreement class and
        // must be accepted rather than rejected as a different establishment.
        assert_eq!(responder.decrypt(&repeat, &mut rng).unwrap(), b"second");
    }
}

#[test]
fn spent_last_resort_rejects_every_torsion_equivalent_replay() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(0x52504c4159);
    let alice = Identity::generate(&mut rng);
    let bob = Identity::generate(&mut rng);
    let mut store = bob.create_prekeys(0, &mut rng);
    let bundle = store.publish_multi_use();
    let mut initiator = establish_initiator(&alice, &bundle, &mut rng).unwrap();
    let first = initiator.encrypt(b"first", &mut rng).unwrap();
    establish_responder(&bob, &mut store, &first, &mut rng).unwrap();
    let before = store.to_bytes().to_vec();

    for spelling in torsion_spellings(ephemeral(&first)) {
        assert!(matches!(
            establish_responder(
                &bob,
                &mut store,
                &replace_ephemeral(&first, spelling),
                &mut rng,
            ),
            Err(LifecycleError::ReplayedLastResort)
        ));
        assert_eq!(store.to_bytes().to_vec(), before);
    }
}

#[test]
fn a_non_contributory_ephemeral_is_not_a_repeat() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(0x4e4f4e43);
    let alice = Identity::generate(&mut rng);
    let bob = Identity::generate(&mut rng);
    let mut store = bob.create_prekeys(0, &mut rng);
    let bundle = store.publish_multi_use();
    let mut initiator = establish_initiator(&alice, &bundle, &mut rng).unwrap();
    let first = initiator.encrypt(b"first", &mut rng).unwrap();
    let (mut responder, _) = establish_responder(&bob, &mut store, &first, &mut rng).unwrap();
    let mut low_order = first.clone();
    low_order[EPHEMERAL].fill(0);
    assert!(matches!(
        responder.decrypt(&low_order, &mut rng),
        Err(LifecycleError::NotARepeatedInitial)
    ));
}
