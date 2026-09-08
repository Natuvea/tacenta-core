//! The ML-KEM Braid's state machine, fed attacker-chosen messages.
//!
//! A decoder target asks whether parsing a message panics. This asks the harder
//! question: whether *driving a state machine* with a sequence of
//! parsed-but-hostile messages panics. They are different failures. The Braid
//! has eleven live states and a terminal one, each accepting a different
//! message type, and the transitions between them are where an epoch or a chunk
//! index read out of one message meets state built from another.
//!
//! `Braid::receive` takes a structured `Msg`, not bytes -- the composite header
//! decoder parses the wire form, and `wire_decoders` covers that. So the input
//! here is decoded into `Msg` values directly. That is the right shape: it
//! reaches states a byte-level fuzzer would need a valid encoder to reach, and
//! it models an attacker who can emit any *well-formed* message rather than
//! only malformed bytes. The two targets meet in the middle.
//!
//! The agreement is set up honestly first, from a fixed preshared secret, and
//! the fuzzer drives one side. That is the real attacker's position: they
//! cannot choose the victim's starting state, only what arrives next.

#![no_main]

use libfuzzer_sys::fuzz_target;
use rand::SeedableRng;
use tacenta_braid::{Braid, Msg, MsgType, CHUNK_SIZE};
use tacenta_erasure::Chunk;

/// One message per 43 input bytes: 8 epoch, 1 type, 1 presence, 2 index, 32
/// chunk. Reading a fixed stride rather than a length prefix keeps the mapping
/// from input to message stable, which is what lets libFuzzer minimise a crash
/// to something a human can read.
const STRIDE: usize = 8 + 1 + 1 + 2 + CHUNK_SIZE;

fn message_at(bytes: &[u8]) -> Msg {
    let mut epoch = [0u8; 8];
    epoch.copy_from_slice(&bytes[..8]);
    let ty = match bytes[8] % 6 {
        0 => MsgType::None,
        1 => MsgType::Hdr,
        2 => MsgType::Ek,
        3 => MsgType::EkCt1Ack,
        4 => MsgType::Ct1,
        _ => MsgType::Ct2,
    };
    // The presence byte is taken from the input rather than always set, so the
    // "a type that expects a chunk arrives without one" case is reachable. That
    // pairing is exactly what a hostile peer controls.
    let data = if bytes[9] & 1 == 1 {
        let mut chunk = [0u8; CHUNK_SIZE];
        chunk.copy_from_slice(&bytes[12..12 + CHUNK_SIZE]);
        Some(Chunk {
            index: u16::from_be_bytes([bytes[10], bytes[11]]),
            data: chunk,
        })
    } else {
        None
    };
    Msg {
        epoch: u64::from_be_bytes(epoch),
        ty,
        data,
    }
}

fuzz_target!(|data: &[u8]| {
    // Fixed seed and fixed secret: the fuzzer's budget should go to the
    // messages, and a target whose setup varies per input cannot minimise a
    // crash to a reproducible case.
    let mut rng = rand::rngs::StdRng::seed_from_u64(0);
    let secret = [0x2au8; 32];
    let mut braid = Braid::initiator(&secret);

    let mut pos = 0usize;
    while pos + STRIDE <= data.len() {
        let msg = message_at(&data[pos..pos + STRIDE]);
        pos += STRIDE;

        // `receive` returns a candidate and commits nothing. For fuzzer-chosen
        // messages the candidate is essentially never one a genuine peer would
        // have produced, so it is deliberately dropped: a forged message must
        // be able to advance nothing, and adopting it here would test the
        // opposite of the property.
        let (_epoch, _out, candidate) = braid.receive(&msg);
        let _ = candidate.failed();

        // Sending must stay possible from whatever state a rejected message
        // left behind. A forged message that wedges the send side is a denial
        // of service even though it decrypts nothing.
        let (_msg, _epoch, _out, next) = braid.send(&mut rng);
        braid = next;
    }
});
