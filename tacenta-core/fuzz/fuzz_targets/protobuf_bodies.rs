//! The protobuf profile, driven with attacker-chosen bytes.
//!
//! `tacenta-protobuf` is a bounded reader written for this repository rather
//! than a general protobuf library: it enforces its own limits on message
//! length, field number, field count, and varint width. Those limits are the
//! interesting surface. A varint that claims ten continuation bytes, a field
//! number past the profile's ceiling, a length prefix that overruns the buffer
//! -- each has to be refused rather than trusted, and the refusal has to happen
//! without arithmetic that overflows on the way.
//!
//! Both entry points take `Vec<u8>` by value, so the input is cloned per call
//! rather than shared: giving the second parser a buffer the first had already
//! consumed would test something neither of them does in production.

#![no_main]

use libfuzzer_sys::fuzz_target;
use tacenta_protobuf::{decode_tag, parse_prekey_body, parse_ratchet_body};

fuzz_target!(|data: &[u8]| {
    let _ = parse_prekey_body(data.to_vec());
    let _ = parse_ratchet_body(data.to_vec());

    // The tag decoder takes an already-parsed `u32`, so it is not reachable
    // from the byte stream alone at full width. Feeding it the first four bytes
    // covers it directly rather than hoping the parsers above happen to.
    if data.len() >= 4 {
        let raw = u32::from_be_bytes([data[0], data[1], data[2], data[3]]);
        let _ = decode_tag(raw);
    }
});
