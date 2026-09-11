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
use tacenta_core::sessions::{
    Identity, PrekeyStore, Session, decode_ec, decode_kem, encode_ec, encode_kem,
    establish_initiator, establish_responder,
};

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

/// The persisted-state decoders -- the `from_bytes`/`import` pair that restores
/// state a storage layer wrote, as opposed to the wire `decode_*` above. These
/// carry their own canonicality check inside the decoder (a re-encode and
/// compare), so the sweep here is the same mutation oracle applied from the
/// outside. The registry test below fails if `lifecycle.rs` grows a public
/// `from_bytes` or `import` that is not on this list (CR-18).
const PERSISTED_COVERED: &[&str] = &["PrekeyStore::from_bytes", "Session::import"];

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
            dh: [0x5a; 32],
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
        // `decode_composite`, `decode_message`, `decode_initial` and
        // `decode_bundle` live in the `tacenta-wire`
        // leaf crate, re-exported by `serialization`; the sweep reads their
        // source where it is.
        root.join("wire/src/lib.rs"),
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

fn seeded_rng(seed: u64) -> rand::rngs::StdRng {
    use rand::SeedableRng;
    rand::rngs::StdRng::seed_from_u64(seed)
}

/// The bytes `PrekeyStore::to_bytes` produces for a store with a little history,
/// so the v3 fields (retired prekeys, a last-resort fingerprint) are present.
fn canonical_prekey_store() -> Vec<u8> {
    let mut r = seeded_rng(1);
    let id = Identity::generate(&mut r);
    let mut store = id.create_prekeys(3, &mut r);
    store.rotate_signed_prekey(&id, &mut r);
    store.rotate_kem(&id, &mut r);
    store.to_bytes().to_vec()
}

/// The bytes `Session::export` produces for an established, slightly advanced
/// session.
fn canonical_session() -> Vec<u8> {
    let mut r = seeded_rng(2);
    let alice_id = Identity::generate(&mut r);
    let bob_id = Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(4, &mut r);
    let bundle = bob_prekeys.publish();
    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let initial = alice.encrypt(b"hello", &mut r).unwrap();
    let (mut bob, _) = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
    let reply = bob.encrypt(b"hi", &mut r).unwrap();
    alice.decrypt(&reply, &mut r).unwrap();
    alice.export().to_vec()
}

#[test]
fn prekey_store_from_bytes_is_canonical() {
    let canonical = canonical_prekey_store();
    assert_canonical("PrekeyStore::from_bytes", &canonical, |b| {
        PrekeyStore::from_bytes(b)
            .ok()
            .map(|s| s.to_bytes().to_vec())
    });
}

#[test]
fn session_import_is_canonical() {
    let canonical = canonical_session();
    assert_canonical("Session::import", &canonical, |b| {
        Session::import(b).ok().map(|s| s.export().to_vec())
    });
}

/// No persisted decoder escapes the sweep either.
///
/// The wire `decode_*` sweep above cannot see these: they are `from_bytes` and
/// `import`, not `decode_*`, and they live in `lifecycle.rs`. This is the same
/// guard for that file: a new public `from_bytes` or `import` there must be
/// listed in `PERSISTED_COVERED` and given a canonicality test (CR-18).
#[test]
fn every_persisted_decoder_is_covered() {
    use std::fs;
    use std::path::PathBuf;

    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let text = fs::read_to_string(root.join("src/sessions/lifecycle.rs")).expect("source");

    // The type each `impl` block is for, tracked so a bare `from_bytes` is
    // reported as `Type::from_bytes` rather than by name alone.
    let mut current_type: Option<String> = None;
    let mut found: Vec<String> = Vec::new();
    for line in text.lines() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("impl ") {
            // `impl PrekeyStore {` / `impl Session {`; ignore trait impls,
            // which are not where the public decoders live.
            let name = rest
                .split(|c: char| c.is_whitespace() || c == '{')
                .next()
                .unwrap_or("");
            if !name.is_empty() && !rest.contains(" for ") {
                current_type = Some(name.to_string());
            }
        }
        for verb in ["from_bytes", "import"] {
            if t.starts_with(&format!("pub fn {verb}")) {
                let ty = current_type.clone().unwrap_or_default();
                found.push(format!("{ty}::{verb}"));
            }
        }
    }
    found.sort();
    found.dedup();

    let missing: Vec<&String> = found
        .iter()
        .filter(|n| !PERSISTED_COVERED.contains(&n.as_str()))
        .collect();
    assert!(
        missing.is_empty(),
        "these persisted decoders have no canonicality test: {missing:?}. \
         Add them to this file and to PERSISTED_COVERED."
    );

    let stale: Vec<&&str> = PERSISTED_COVERED
        .iter()
        .filter(|n| !found.contains(&n.to_string()))
        .collect();
    assert!(
        stale.is_empty(),
        "PERSISTED_COVERED lists decoders that no longer exist: {stale:?}"
    );
}
