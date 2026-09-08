//! The session, fed attacker-chosen messages on both of its receive paths.
//!
//! This is the composed state machine: `Session::decrypt` drives the classical
//! ratchet, the sparse post-quantum ratchet, and the Braid beneath them as one
//! transaction, and `establish_responder` builds a session out of a message
//! that has not been authenticated yet. Together they are the whole of what a
//! hostile peer can reach without holding a key.
//!
//! Two entry points, and the second is the more interesting one.
//! `establish_responder` reads prekey identifiers out of an unauthenticated
//! message and looks them up in a store it holds mutably, which is the shape
//! where the authenticate-then-delete ordering it enforces matters;
//! `AUTHENTICATION-BOUNDARY.md` carries the argument for it.
//!
//! Both parties are set up honestly, then the fuzzer supplies the message. The
//! attacker cannot choose the victim's keys, only what arrives.

#![no_main]

use libfuzzer_sys::fuzz_target;
use rand::SeedableRng;
use tacenta_core::sessions::{Identity, establish_initiator, establish_responder};

fuzz_target!(|data: &[u8]| {
    // Fixed seed: the budget belongs to the message bytes, and a crash has to
    // minimise to something reproducible.
    let mut rng = rand::rngs::StdRng::seed_from_u64(0);

    let bob = Identity::generate(&mut rng);
    let mut bob_prekeys = bob.create_prekeys(4, &mut rng);

    // Path one: an unauthenticated initial message against a live prekey store.
    // Whatever it does, it must not panic and it must not consume a one-time
    // prekey for a message that fails to authenticate -- the second is not
    // asserted here (a fuzz target has no oracle for it) but the first is what
    // a crash would show.
    let _ = establish_responder(&bob, &mut bob_prekeys, data, &mut rng);

    // Path two: a message arriving on a session that is already established.
    // Alice opens one against Bob's real bundle so the ratchet state is
    // genuine, and then the fuzzer's bytes arrive instead of Bob's reply.
    let alice = Identity::generate(&mut rng);
    let bundle = bob_prekeys.publish();
    if let Ok(mut session) = establish_initiator(&alice, &bundle, &mut rng) {
        // One real send first, so the session is past its opening state and the
        // receive path has an actual chain to fail against rather than an empty
        // one. Reaching the interesting branches needs a session that has run.
        let _ = session.encrypt(b"fuzz", &mut rng);
        let _ = session.decrypt(data, &mut rng);
    }
});
