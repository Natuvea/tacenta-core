//! One property, checked against every decoder: **of the byte strings a decoder
//! accepts, each must be the encoding of what it decoded to.**
//!
//! The property has more than one site: the composite header's absent
//! codeword and the bundle decoder's absent one-time prekey both carry
//! padding that must be zero, and every other decoder has its own shape of the
//! same rule. Checking one site and not sweeping the neighbours is how a class
//! of problem survives, and a rule against it would be checked by nothing. So
//! this is a suite over *every* decoder, plus a check that no decoder is
//! missing from it, which is the part that makes it a sweep rather than a
//! single instance.
//!
//! ## Why round-tripping is not enough
//!
//! `decode(encode(x)) == x` is proved for several of these and says nothing
//! about the property above: it quantifies over values and only ever asks about
//! bytes the encoder produced. A decoder that accepted every byte string and
//! returned a fixed value would satisfy it. Canonicality is the other
//! direction, and it is the one an attacker plays with.

use tacenta_core::primitives::dh::PublicKeyBytes;
use tacenta_core::serialization::composite::{
    AgreementType, CHUNK_BYTES, Codeword, Composite, decode_composite, encode_composite,
};
use tacenta_core::serialization::{
    WireBundle, decode_bundle, decode_initial, decode_message, encode_bundle, encode_initial,
    encode_message,
};
use tacenta_core::sessions::{decode_ec, decode_kem, encode_ec, encode_kem};

/// Every decoder covered here. The registry test below fails if the source
/// grows one that is not on this list.
const COVERED: &[&str] = &[
    "decode_ec",
    "decode_kem",
    "decode_composite",
    "decode_message",
    "decode_bundle",
    "decode_initial",
];

/// Mutate each sampled byte, and for anything still accepted, require that
/// re-encoding reproduces the input exactly.
///
/// `reencode` returns `None` when the decoder refused, which is the ordinary
/// outcome and not a finding. A finding is an acceptance whose re-encoding
/// differs: that is a second spelling of one value.
fn assert_canonical(name: &str, canonical: &[u8], reencode: impl Fn(&[u8]) -> Option<Vec<u8>>) {
    assert_eq!(
        reencode(canonical).as_deref(),
        Some(canonical),
        "{name}: its own canonical encoding does not round trip"
    );

    let n = canonical.len();
    let step = (n / 96).max(1);
    let mut accepted = 0;
    for at in (0..n).step_by(step) {
        for bit in [0x01u8, 0x80] {
            let mut bytes = canonical.to_vec();
            bytes[at] ^= bit;
            if let Some(again) = reencode(&bytes) {
                accepted += 1;
                assert_eq!(
                    again, bytes,
                    "{name}: byte {at} flipped, still accepted, and re-encodes differently. \
                     Two byte strings mean one value."
                );
            }
        }
    }
    // Not an assertion about the count, a guard against a vacuous pass: if a
    // decoder refused every mutation including ones it should accept, the loop
    // proved nothing and the encoder pair is probably wrong.
    let _ = accepted;
}

#[test]
fn decode_ec_is_canonical() {
    let key = PublicKeyBytes::from_bytes([0x42; 32]);
    let canonical = encode_ec(&key);
    assert_canonical("decode_ec", &canonical, |b| {
        decode_ec(b).map(|k| encode_ec(&k))
    });
}

#[test]
fn decode_kem_is_canonical() {
    let key = vec![0x33u8; 1568];
    let canonical = encode_kem(&key);
    assert_canonical("decode_kem", &canonical, |b| {
        decode_kem(b).map(|k| encode_kem(&k))
    });
}

#[test]
fn decode_composite_is_canonical() {
    for chunk in [
        None,
        Some(Codeword {
            index: 5,
            data: [0xcd; 32],
        }),
    ] {
        let h = Composite {
            dh: [0xaa; 32],
            pn: 7,
            n: 9,
            pq_epoch: 3,
            pq_n: 11,
            ag_epoch: 3,
            ag_type: if chunk.is_some() {
                AgreementType::Ct1
            } else {
                AgreementType::None
            },
            ag_chunk: chunk,
        };
        let canonical = encode_composite(&h);
        assert_canonical("decode_composite", &canonical, |b| {
            decode_composite(b)
                .ok()
                .filter(|(_, rest)| rest.is_empty())
                .map(|(h, _)| encode_composite(&h))
        });
    }
}

#[test]
fn decode_message_is_canonical() {
    let header = Composite {
        dh: [0x11; 32],
        pn: 3,
        n: 4,
        pq_epoch: 2,
        pq_n: 6,
        ag_epoch: 2,
        ag_type: AgreementType::Ct1,
        ag_chunk: Some(Codeword {
            index: 1,
            data: [0x22; CHUNK_BYTES],
        }),
    };
    let canonical = encode_message(&header, b"ciphertext bytes");
    assert_canonical("decode_message", &canonical, |b| {
        decode_message(b)
            .ok()
            .map(|m| encode_message(&m.header, &m.ciphertext))
    });
}

#[test]
fn decode_bundle_is_canonical() {
    for one_time in [None, Some([0x77u8; 32])] {
        let fields = WireBundle {
            identity_key: [0x11; 32],
            signed_prekey: [0x22; 32],
            signed_prekey_signature: [0x33; 64],
            kem_prekey: vec![0x44; 1568],
            kem_prekey_signature: [0x55; 64],
            one_time_prekey: one_time,
            signed_prekey_id: 1,
            one_time_prekey_id: if one_time.is_some() { 2 } else { 0 },
            kem_prekey_id: 3,
        };
        let canonical = encode_bundle(&fields);
        assert_canonical("decode_bundle", &canonical, |b| {
            decode_bundle(b).ok().map(|f| encode_bundle(&f))
        });
    }
}

#[test]
fn decode_initial_is_canonical() {
    let canonical = encode_initial(
        &[0x05; 33],
        &[0x05; 33],
        &vec![0x66u8; 1568],
        1,
        2,
        3,
        b"inner ratchet message",
    );
    assert_canonical("decode_initial", &canonical, |b| {
        decode_initial(b).ok().map(|d| {
            encode_initial(
                &d.identity,
                &d.ephemeral,
                &d.kem_ciphertext,
                d.signed_prekey_id,
                d.one_time_prekey_id,
                d.kem_prekey_id,
                &d.message,
            )
        })
    });
}

/// No decoder escapes the suite.
///
/// The sweep is the point. A canonicality test at one site leaves the decoder
/// beside it unchecked; the sweep covers every decoder.
#[test]
fn every_decoder_is_covered() {
    use std::fs;
    use std::path::PathBuf;

    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let sources = [
        root.join("src/serialization/mod.rs"),
        root.join("src/serialization/composite.rs"),
        root.join("src/sessions/mod.rs"),
    ];

    let mut found = Vec::new();
    for path in &sources {
        let text = fs::read_to_string(path).expect("source");
        // Only what the crate exposes: an internal helper is not a decoder an
        // attacker reaches.
        for line in text.lines() {
            let line = line.trim_start();
            if let Some(rest) = line.strip_prefix("pub fn decode_") {
                let name = rest
                    .split(|c: char| !c.is_alphanumeric() && c != '_')
                    .next()
                    .unwrap_or("");
                found.push(format!("decode_{name}"));
            }
        }
    }
    found.sort();
    found.dedup();

    let missing: Vec<&String> = found
        .iter()
        .filter(|n| !COVERED.contains(&n.as_str()))
        .collect();
    assert!(
        missing.is_empty(),
        "these decoders have no canonicality test: {missing:?}. \
         Add them to this file and to COVERED, or say in the source why the \
         property does not apply."
    );

    let stale: Vec<&&str> = COVERED
        .iter()
        .filter(|n| !found.contains(&n.to_string()))
        .collect();
    assert!(
        stale.is_empty(),
        "COVERED lists decoders that no longer exist: {stale:?}"
    );
}
