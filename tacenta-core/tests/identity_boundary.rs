//! Identity admission is stricter than ephemeral X25519 agreement.
//!
//! These tests keep the identity/revocation byte boundary separate from the
//! agreement-class tests: a torsion-equivalent spelling may be a valid
//! ephemeral agreement input, but it must not become a second long-lived
//! identity spelling.

use curve25519_dalek::edwards::{CompressedEdwardsY, EdwardsPoint};
use curve25519_dalek::montgomery::MontgomeryPoint;
use rand::SeedableRng;
use tacenta_core::sessions::{Identity, Session, establish_initiator, establish_responder};

const IDENTITY: core::ops::Range<usize> = 3..35;

fn order8() -> EdwardsPoint {
    let bytes =
        hex::decode("c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a").unwrap();
    CompressedEdwardsY(bytes.try_into().unwrap())
        .decompress()
        .unwrap()
}

fn respellings(u: [u8; 32]) -> Vec<[u8; 32]> {
    let p = MontgomeryPoint(u).to_edwards(0).unwrap();
    let torsion = order8();
    let mut out = Vec::new();
    let mut add = torsion;
    for _ in 1..8 {
        out.push((p + add).to_montgomery().to_bytes());
        add += torsion;
    }
    out
}

fn get(bytes: &[u8], range: core::ops::Range<usize>) -> [u8; 32] {
    bytes[range].try_into().unwrap()
}

fn replace(bytes: &[u8], range: core::ops::Range<usize>, key: [u8; 32]) -> Vec<u8> {
    let mut changed = bytes.to_vec();
    changed[range].copy_from_slice(&key);
    changed
}

#[test]
fn responder_refuses_a_torsion_spelled_identity_before_authentication() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(7001);
    let alice = Identity::generate(&mut rng);
    let bob = Identity::generate(&mut rng);
    let mut store = bob.create_prekeys(0, &mut rng);
    let bundle = store.publish_multi_use();
    let mut initiator = establish_initiator(&alice, &bundle, &mut rng).unwrap();
    let initial = initiator.encrypt(b"identity boundary", &mut rng).unwrap();
    let before = store.to_bytes();

    for key in respellings(get(&initial, IDENTITY)) {
        assert!(
            establish_responder(
                &bob,
                &mut store,
                &replace(&initial, IDENTITY, key),
                &mut rng
            )
            .is_err()
        );
        assert_eq!(store.to_bytes(), before);
    }
}

#[test]
fn imported_state_cannot_change_a_long_lived_identity_spelling() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(7002);
    let alice = Identity::generate(&mut rng);
    let bob = Identity::generate(&mut rng);
    let store = bob.create_prekeys(0, &mut rng);
    let bundle = store.publish_multi_use();
    let initiator = establish_initiator(&alice, &bundle, &mut rng).unwrap();
    let exported = initiator.export().to_vec();
    let public = *alice.public().as_bytes();

    let mut replaced = exported.clone();
    let mut occurrences = 0;
    for at in 0..=replaced.len() - public.len() {
        if replaced[at..at + public.len()] == public {
            replaced[at..at + public.len()].copy_from_slice(&respellings(public)[2]);
            occurrences += 1;
        }
    }
    assert!(occurrences >= 1, "the export carries the identity boundary");
    assert!(Session::import(&replaced).is_err());
    assert!(Session::import(&exported).is_ok());
}
