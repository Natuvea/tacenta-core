//! Seeds for the persisted-state fuzz target, in the shape it reads.
//!
//! `fuzz/fuzz_targets/persisted_state.rs` restores a session from the first
//! part of its input and drives it with the rest, and the split is a two-byte
//! big-endian length at the front. libFuzzer cannot discover a canonical
//! session export by mutation, so the corpus has to be seeded with real ones:
//! a responder just after establishment with the initiator's next message
//! aimed at it, and an initiator after its first send (which holds the ML-KEM
//! key pair, the largest a session gets) with the responder's reply.
//!
//! Ignored by default because it writes into the corpus; run it deliberately
//! when the persisted format changes:
//!
//! ```sh
//! cargo test --test fuzz_seeds -- --ignored
//! ```

use std::path::PathBuf;

use rand::SeedableRng;
use tacenta_core::sessions::{self, Session, establish_initiator, establish_responder};

fn seed(name: &str, session: &Session, wire: &[u8]) {
    let export = session.export();
    let len = u16::try_from(export.len()).expect("an export fits sixteen bits of length");
    let mut out = Vec::with_capacity(2 + export.len() + wire.len());
    out.extend_from_slice(&len.to_be_bytes());
    out.extend_from_slice(&export);
    out.extend_from_slice(wire);
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fuzz/corpus/persisted_state");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("seed-{name}.bin"));
    std::fs::write(&path, &out).unwrap();
    println!("wrote {} ({} bytes)", path.display(), out.len());
}

#[test]
#[ignore]
fn write_persisted_state_seeds() {
    let mut r = rand::rngs::StdRng::seed_from_u64(20260903);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(4, &mut r);
    let bundle = bob_prekeys.publish();

    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let initial = alice.encrypt(b"hello bob", &mut r).unwrap();
    let (mut bob, _) = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();

    // Responder right after establishment, with the initiator's next message.
    let next = alice.encrypt(b"second", &mut r).unwrap();
    seed("responder-with-message", &bob, &next);

    // Initiator after its first sends, with the responder's reply.
    let reply = bob.encrypt(b"reply", &mut r).unwrap();
    seed("initiator-with-reply", &alice, &reply);
}
