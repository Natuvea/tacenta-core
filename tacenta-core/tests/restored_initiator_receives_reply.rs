//! A copy of the session `establish_initiator` returned, exported before the initiator's first
//! `encrypt` and restored after the responder replied, decrypts that reply.
//!
//! The Lean theorems about `Session::decrypt` at an established initiator session cover the state
//! `establish_initiator` returns. A single session value leaves that state at its first `encrypt`,
//! which an honest responder needs before it can reply; a persisted copy does not. This test shows
//! the success arm reached by an honest run through such a copy, on the seeds it tries. It is a test,
//! not a proof, and says nothing about whether restoring an older snapshot is safe for an
//! application; that is the caller's concern (`tacenta-spec`, session persistence).
//!
//! What it exercises is what `restored_established_initiator_decrypt_refines`
//! (`tacenta-proofs/translation/Translation/UnitLifecycleRestoredSession.lean`) states of the
//! translated session unit under nine assumed laws: `import` of the bytes `export` writes returns
//! the established session unchanged, and, given the caller's boundary records, chunk relation and
//! draw, `decrypt` of the restored copy on a ratchet-type frame refines the model's step. The theorem
//! does not say what an honest responder sends; this test runs one.

use rand::SeedableRng;
use tacenta_core::sessions::{
    self, Expectation, Session, establish_initiator, establish_responder,
};

/// Byte 0 of a frame is the wire version; byte 1 is the type, which
/// `serialization::message_type` reads (`tacenta_wire::VERSION`, `TYPE_RATCHET`).
const VERSION: u8 = tacenta_wire::VERSION;
const RATCHET_TYPE: u8 = tacenta_wire::TYPE_RATCHET;

#[test]
fn restored_initiator_receives_reply() {
    for seed in 0..20u64 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let alice_id = sessions::Identity::generate(&mut rng);
        let bob_id = sessions::Identity::generate(&mut rng);
        let mut bob_prekeys = bob_id.create_prekeys(4, &mut rng);
        let bundle = bob_prekeys.publish();

        let mut alice = establish_initiator(
            &alice_id,
            &bundle,
            &Expectation::first_contact(&[]),
            &mut rng,
        )
        .unwrap();
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
            Some(&VERSION),
            "seed {seed}: the reply carries the wire version"
        );
        assert_eq!(
            reply.get(1),
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
