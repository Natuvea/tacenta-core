//! Every decoder that reads bytes a peer chose, driven with bytes an attacker
//! chose.
//!
//! These are the functions on the far side of the network from us: a message
//! arrives, and one of them is the first thing to look at it. Each returns
//! `Result` or `Option`, so the first property under test is that it *returns*
//! -- that no input reaches a panic, an index out of bounds, or an arithmetic
//! overflow, whatever the bytes say their lengths are.
//!
//! **The second property is canonicality, and it is asserted rather than left
//! to a separate suite.** Every accepted input must re-encode to exactly the
//! bytes it was decoded from: a presence byte or padding that a decoder
//! tolerates and its encoder does not emit falls out of this oracle in
//! seconds, where "did not panic" alone would never see it.
//!
//! `tests/fuzz.rs` covers three of these with proptest already. This is not
//! that: proptest generates from a declared shape and cannot see which branches
//! it reached, so it cannot search toward the ones it has not.

#![no_main]

use libfuzzer_sys::fuzz_target;
use tacenta_core::serialization::composite::{decode_composite, encode_composite};
use tacenta_core::serialization::{
    decode_bundle, decode_initial, decode_message, encode_bundle, encode_message, message_type,
};

fuzz_target!(|data: &[u8]| {
    // Each is given the whole input rather than a slice of it. A decoder that
    // only ever sees well-framed input is a decoder whose framing checks are
    // untested, and the framing checks are the ones an attacker reaches first.
    let _ = message_type(data);

    if let Ok(m) = decode_message(data) {
        assert_eq!(
            encode_message(&m.header, &m.ciphertext).as_slice(),
            data,
            "decode_message accepted bytes it does not re-emit"
        );
    }

    // `decode_initial` has no single-call inverse (the encoder takes the
    // parts the session layer holds separately), so it is checked for
    // returning only; `tests/canonicality.rs` covers its round trip.
    let _ = decode_initial(data);

    if let Ok(b) = decode_bundle(data) {
        assert_eq!(
            encode_bundle(&b).as_slice(),
            data,
            "decode_bundle accepted bytes it does not re-emit"
        );
    }

    if let Ok((c, rest)) = decode_composite(data) {
        let consumed = data.len() - rest.len();
        assert_eq!(
            encode_composite(&c).as_slice(),
            &data[..consumed],
            "decode_composite accepted bytes it does not re-emit"
        );
    }
});
