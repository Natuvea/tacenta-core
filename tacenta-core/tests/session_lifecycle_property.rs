//! Concrete witness for the bounded `SESSION-LIFECYCLE-01` model property.
//!
//! This is a deterministic, deliberately small trace: it establishes through
//! fresh session objects, restores both sides at committed checkpoints,
//! exercises skipped-message recovery, and proves that authentication failure
//! and replay do not consume the genuine message or accept it twice. It does
//! not claim database atomicity, a general Rust-to-Lean refinement, or complete
//! schedule coverage.

use rand::{SeedableRng, rngs::StdRng};
use tacenta_core::sessions::{self, Session, establish_initiator, establish_responder};

fn rng(seed: u64) -> StdRng {
    StdRng::seed_from_u64(seed)
}

#[test]
fn session_lifecycle_01_establishes_restores_continues_and_refuses_replays() {
    let mut random = rng(0x5e55_10ce);
    let alice_id = sessions::Identity::generate(&mut random);
    let bob_id = sessions::Identity::generate(&mut random);
    let mut bob_prekeys = bob_id.create_prekeys(3, &mut random);
    let bundle = bob_prekeys.publish();

    // Pending initiator checkpoint: the fresh object must retain enough state
    // to generate an initial wrapper and establish the peer.
    let alice = establish_initiator(&alice_id, &bundle, &mut random).unwrap();
    let mut alice = Session::import(&alice.export()).unwrap();
    let initial = alice.encrypt(b"initial", &mut random).unwrap();
    let (bob, plaintext) =
        establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut random).unwrap();
    assert_eq!(plaintext, b"initial");

    // Established responder checkpoint, then the authenticated reply clears
    // the pending initial state held by Alice.
    let mut bob = Session::import(&bob.export()).unwrap();
    let reply = bob.encrypt(b"reply", &mut random).unwrap();
    assert_eq!(alice.decrypt(&reply, &mut random).unwrap(), b"reply");
    alice = Session::import(&alice.export()).unwrap();

    // Queue three messages, deliver the last first, and restart the receiver
    // before it uses its persisted skipped-message keys for the earlier two.
    let first = alice.encrypt(b"one", &mut random).unwrap();
    let second = alice.encrypt(b"two", &mut random).unwrap();
    let third = alice.encrypt(b"three", &mut random).unwrap();
    assert_eq!(bob.decrypt(&third, &mut random).unwrap(), b"three");
    bob = Session::import(&bob.export()).unwrap();
    assert_eq!(bob.decrypt(&first, &mut random).unwrap(), b"one");
    assert_eq!(bob.decrypt(&second, &mut random).unwrap(), b"two");

    // A replay is refused and has no durable effect. The next authentic message
    // still reaches the restored receiver, showing the refusal did not consume
    // a future key or otherwise corrupt the committed observation.
    let before_replay = bob.export();
    assert!(bob.decrypt(&second, &mut random).is_err());
    assert_eq!(bob.export(), before_replay);

    let genuine = alice.encrypt(b"after replay", &mut random).unwrap();
    let mut forged = genuine.clone();
    *forged.last_mut().unwrap() ^= 1;
    let before_forgery = bob.export();
    assert!(bob.decrypt(&forged, &mut random).is_err());
    assert_eq!(bob.export(), before_forgery);
    assert_eq!(bob.decrypt(&genuine, &mut random).unwrap(), b"after replay");
}
