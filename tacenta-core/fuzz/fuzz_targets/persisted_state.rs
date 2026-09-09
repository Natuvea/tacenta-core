//! The storage decoders, driven with attacker-chosen bytes -- and then the
//! state they restore, driven too.
//!
//! These arrived with the session-persistence format. Round-trip tests by
//! construction never see a malformed buffer; this target is where malformed
//! ones are tried.
//!
//! **The threat model here is corruption, not a hostile peer**, and
//! session-persistence.md says so: these bytes are written and read back by the
//! same code, never sent to anyone. That makes the panic-freedom property more
//! important rather than less. A wire decoder that panics takes down a session;
//! a storage decoder that panics takes down every start-up until the file is
//! deleted, and the file is the user's identity and their live conversations.
//! A truncated write, a bit flip, or a downgrade to an older build all produce
//! exactly the inputs below.
//!
//! **Parsing is half of it.** A decoder restored with a `size` no honest run
//! could have produced can parse, re-encode to itself, and still fail on the
//! *next chunk*. A restored state is only known good once something has
//! driven it, so the second half of the input is spent as a wire message
//! against the restored session, which reaches every state machine the file
//! composes, and one `encrypt` follows for the send side.
//!
//! Each format is given the whole buffer. The formats are independently
//! versioned and length-checked, so handing all of them the same bytes
//! exercises each one's own framing rather than only the shape its own encoder
//! emits.

#![no_main]

use libfuzzer_sys::fuzz_target;
use rand::SeedableRng;
use tacenta_core::sessions::{PrekeyStore, Session};

fuzz_target!(|data: &[u8]| {
    // The four ratchet-layer formats, bottom to top. The last composes the
    // first two, so a length prefix that lies about an inner format's size is
    // reachable only through it. Each accepted state must re-encode to the
    // bytes it came from.
    if let Ok(s) = tacenta_ratchet::State::from_bytes(data) {
        assert_eq!(s.to_bytes().as_slice(), data, "ratchet state is not canonical");
    }
    if let Ok(s) = tacenta_spqr::State::from_bytes(data) {
        assert_eq!(s.to_bytes().as_slice(), data, "spqr state is not canonical");
    }
    if let Ok(b) = tacenta_braid::Braid::from_bytes(data) {
        assert_eq!(b.to_bytes().as_slice(), data, "braid state is not canonical");
    }
    if let Ok(s) = tacenta_triple::State::from_bytes(data) {
        assert_eq!(s.to_bytes().as_slice(), data, "triple state is not canonical");
    }

    // The erasure coders, which the Braid's format nests inside its own.
    if let Some(e) = tacenta_erasure::Encoder::from_bytes(data) {
        assert_eq!(e.to_bytes().as_slice(), data, "erasure encoder is not canonical");
    }
    if let Some(d) = tacenta_erasure::Decoder::from_bytes(data) {
        assert_eq!(d.to_bytes().as_slice(), data, "erasure decoder is not canonical");
        // A restored decoder must be drivable: `message()` reserves `size`
        // bytes, which is where an unvalidated `size` would show.
        let _ = d.message();
    }

    // The session layer, which composes everything above plus the identity and
    // pending-handshake fields.
    //
    // The prekey store still reads its earlier formats (versions 0x01
    // through 0x03: no replay record; then an untagged record without the
    // retired prekeys; then the same with them) and always writes the
    // current one, on purpose, so
    // byte-identical re-encoding is the rule only for a current store. For an
    // older one the oracle is idempotence: what it writes back must itself
    // read and re-emit unchanged.
    if let Ok(p) = PrekeyStore::from_bytes(data) {
        let re = p.to_bytes();
        if data.first() == re.first() {
            assert_eq!(re.as_slice(), data, "prekey store is not canonical");
        } else {
            let again = PrekeyStore::from_bytes(&re).expect("an upgraded store must read back");
            assert_eq!(again.to_bytes().as_slice(), re.as_slice(), "upgrade is not idempotent");
        }
    }

    // Restore, then drive. The input names its own split: a two-byte
    // big-endian length, then that many bytes of persisted session, then the
    // rest as a message from the wire aimed at it. A fixed split at the
    // midpoint could only ever import a session whose export happened to be
    // exactly half the input, which no mutation preserves, so the split is
    // self-describing. The corpus carries seeds in this shape
    // (`tests/fuzz_seeds.rs` writes them).
    // Whatever the split, nothing here may panic.
    if data.len() < 2 {
        return;
    }
    let cut = u16::from_be_bytes([data[0], data[1]]) as usize;
    let rest = &data[2..];
    if cut > rest.len() {
        return;
    }
    let (stored, wire) = rest.split_at(cut);
    if let Ok(mut s) = Session::import(stored) {
        assert_eq!(s.export().as_slice(), stored, "session import is not canonical");
        let mut rng = rand::rngs::StdRng::seed_from_u64(0);
        let _ = s.decrypt(wire, &mut rng);
        let _ = s.encrypt(wire, &mut rng);
    }
});
