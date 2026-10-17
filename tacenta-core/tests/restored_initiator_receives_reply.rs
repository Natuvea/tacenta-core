//! A copy of the session `establish_initiator` returned, exported before the initiator's first
//! `encrypt` and restored after the responder replied, decrypts that reply.
//!
//! The Lean theorems about `Session::decrypt` at an established initiator session cover the state
//! `establish_initiator` returns. A single session value leaves that state at its first `encrypt`,
//! which an honest responder needs before it can reply; a persisted copy does not. This test shows
//! the success arm reached by an honest run through such a copy, on the seeds it tries. It is a test,
//! not a proof, and says nothing about whether restoring an older snapshot is safe for an
//! application; that is the caller's concern (`tacenta-spec`, session persistence).

use rand::SeedableRng;
use tacenta_core::sessions::{self, Session, establish_initiator, establish_responder};

/// The type byte of a ratchet frame, as `serialization::message_type` reads it.
const RATCHET_TYPE: u8 = 1;

#[test]
fn restored_initiator_receives_reply() {
    for seed in 0..20u64 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let alice_id = sessions::Identity::generate(&mut rng);
        let bob_id = sessions::Identity::generate(&mut rng);
        let mut bob_prekeys = bob_id.create_prekeys(4, &mut rng);
        let bundle = bob_prekeys.publish();

        let mut alice = establish_initiator(&alice_id, &bundle, &mut rng).unwrap();
        let saved = alice.export();

        let initial = alice.encrypt(b"hello bob", &mut rng).unwrap();
        let (mut bob, first) =
            establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut rng).unwrap();
        assert_eq!(
            first, b"hello bob",
            "seed {seed}: the responder reads the initial message"
        );
        let reply = bob.encrypt(b"reply", &mut rng).unwrap();
        assert_eq!(
            reply.first(),
            Some(&RATCHET_TYPE),
            "seed {seed}: the reply is a ratchet frame"
        );

        let mut restored = Session::import(&saved).unwrap();
        assert_eq!(
            &restored.export()[..],
            &saved[..],
            "seed {seed}: the copy round-trips exactly"
        );
        let plaintext = restored
            .decrypt(&reply, &mut rng)
            .unwrap_or_else(|e| panic!("seed {seed}: the restored copy refused the reply: {e:?}"));
        assert_eq!(
            plaintext, b"reply",
            "seed {seed}: the restored copy reads the reply"
        );
    }
}
