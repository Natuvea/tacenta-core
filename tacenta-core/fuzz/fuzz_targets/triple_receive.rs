//! The Triple Ratchet, fed attacker-chosen headers.
//!
//! The session parses a composite header and hands each half to the Triple
//! Ratchet, which drives the classical ratchet and the sparse post-quantum one
//! from it. `wire_decoders` covers the parse; this covers what a *sequence* of
//! well-formed headers does to the two state machines and their skipped-key
//! stores: ratchet steps on every message, skips at the bound, stores at the
//! bound, epochs that arrive out of order, and message numbers a peer would
//! never send. The same shape as `braid_receive`, one level up.
//!
//! The Diffie-Hellman outputs are fixed stand-ins, as in the crate's own
//! tests: what a hostile peer controls is the header, and the agreement's
//! output is supplied by the fuzzer too, since a peer controls when an epoch
//! completes. Every candidate the ratchets accept is committed, because the
//! property is that no accepted sequence panics, not that hostile headers are
//! refused; refusal is the AEAD's job, above this layer.
//!
//! The first byte picks the side driven: Bob after one genuine message from
//! Alice, or Alice after her first send. The corpus is seeded with a few
//! honest headers for each by `write_triple_receive_seeds` in
//! `triple/src/tests.rs`, which mirrors this layout.

#![no_main]

use libfuzzer_sys::fuzz_target;
use tacenta_triple::{DrHeader, Header, Key, LabelSet, Output, State};

const SK: &[u8] = &[0x01; 32];
const A_PUB: Key = [0x0a; 32];
const B_PUB: Key = [0x0b; 32];
const NEW_PUB: Key = [0xb2; 32];
const DH_AB: Key = [0xab; 32];
const DH_B2A: Key = [0xba; 32];

/// After the role byte, one message per 97 input bytes: 32 ratchet key, 4
/// previous-chain length, 4 message number, 8 epoch, 8 post-quantum number,
/// 1 output presence, 8 output epoch, 32 output key. A fixed stride, for the
/// reason `braid_receive` gives.
const STRIDE: usize = 32 + 4 + 4 + 8 + 8 + 1 + 8 + 32;

fn header_at(bytes: &[u8]) -> (Header, Option<Output>) {
    let mut dh = [0u8; 32];
    dh.copy_from_slice(&bytes[..32]);
    let pn = u32::from_be_bytes([bytes[32], bytes[33], bytes[34], bytes[35]]);
    let n = u32::from_be_bytes([bytes[36], bytes[37], bytes[38], bytes[39]]);
    let mut epoch = [0u8; 8];
    epoch.copy_from_slice(&bytes[40..48]);
    let mut pq_n = [0u8; 8];
    pq_n.copy_from_slice(&bytes[48..56]);
    let output = if bytes[56] & 1 == 1 {
        let mut key_epoch = [0u8; 8];
        key_epoch.copy_from_slice(&bytes[57..65]);
        let mut key = [0u8; 32];
        key.copy_from_slice(&bytes[65..97]);
        Some(Output::new(u64::from_be_bytes(key_epoch), key))
    } else {
        None
    };
    (
        Header {
            dr: DrHeader { dh, pn, n },
            epoch: u64::from_be_bytes(epoch),
            pq_n: u64::from_be_bytes(pq_n),
        },
        output,
    )
}

fuzz_target!(|data: &[u8]| {
    let Some(role) = data.first() else {
        return;
    };
    let mut alice = State::init_sender(SK, A_PUB, B_PUB, &DH_AB, LabelSet::Tacenta);
    let mut bob = State::init_receiver(SK, B_PUB, LabelSet::Tacenta);
    // One genuine message so Bob has a receiving chain; Alice keeps only her
    // first send, which is the state an initiator waits in.
    let Ok((h, _)) = alice.send(0, None) else {
        return;
    };
    if let Ok((next, _)) = bob.receive(&h, &DH_AB, &DH_B2A, NEW_PUB, None) {
        bob.commit(next);
    }
    let mut state = if role & 1 == 0 { bob } else { alice };

    let mut pos = 1usize;
    while pos + STRIDE <= data.len() {
        let (header, output) = header_at(&data[pos..pos + STRIDE]);
        pos += STRIDE;

        if let Ok((next, _key)) = state.receive(&header, &DH_AB, &DH_B2A, NEW_PUB, output.as_ref())
        {
            state.commit(next);
        }
        // The send side must stay usable from whatever a refused header left
        // behind; a sequence that wedges it is a denial of service.
        let _ = state.send(state.epoch(), None);
        // Once `tacenta_triple::State` exposes an `invariant`, assert it here
        // after the commit and after the send, as `braid_receive` does for
        // the Braid: the two ratchets' own predicates are then checked as
        // inductive invariants through the composition that drives them.
    }
});
