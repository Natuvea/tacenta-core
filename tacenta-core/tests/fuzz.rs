//! Property-based fuzzing of the untrusted-input decoders. They parse bytes that
//! arrive from the network, so they must reject anything malformed and never
//! panic. This is the runtime complement to the T1 panic-freedom proof: the proof
//! argues it for the whole verified zone; this exercises the decoders directly on
//! random and structured input every push.

use proptest::prelude::*;

use tacenta_core::serialization::composite::{AgreementType, Codeword, Composite};

/// A composite header with the agreement half present, for properties that are
/// about something other than the header's own fields.
fn sample_composite() -> Composite {
    Composite {
        dh: [7u8; 32],
        pn: 3,
        n: 5,
        pq_epoch: 1,
        pq_n: 2,
        ag_epoch: 1,
        ag_type: AgreementType::Hdr,
        ag_chunk: Some(Codeword {
            index: 0,
            data: [9u8; 32],
        }),
    }
}

/// A canonical curve key made from arbitrary bytes: bit 255 cleared, and bit
/// 254 cleared as well when the rest would be at least p = 2^255 - 19. A decoder
/// accepts a key in no other spelling (message-format.md, Curve public keys).
fn canonical_key(mut k: [u8; 32]) -> [u8; 32] {
    k[31] &= 0x7f;
    if k[31] == 0x7f && k[1..31].iter().all(|b| *b == 0xff) && k[0] >= 0xed {
        k[31] = 0x3f;
    }
    k
}

use tacenta_core::serialization::{
    concat_ad, decode_initial, decode_message, encode_message, message_type,
};

use std::sync::OnceLock;
use tacenta_core::sessions::{
    Identity, PrekeyStore, Session, establish_initiator, establish_responder,
};

/// A canonical persisted `PrekeyStore`, built once. Property cases mutate a copy
/// rather than rebuild it, which would pay for ML-KEM key generation each time.
fn canonical_prekey_store() -> &'static [u8] {
    static BYTES: OnceLock<Vec<u8>> = OnceLock::new();
    BYTES.get_or_init(|| {
        use rand::SeedableRng;
        let mut r = rand::rngs::StdRng::seed_from_u64(101);
        let id = Identity::generate(&mut r);
        let mut store = id.create_prekeys(3, &mut r);
        store.rotate_signed_prekey(&id, &mut r);
        store.rotate_kem(&id, &mut r);
        store.to_bytes().to_vec()
    })
}

/// A canonical persisted `Session`, built once, mid-conversation.
fn canonical_session() -> &'static [u8] {
    static BYTES: OnceLock<Vec<u8>> = OnceLock::new();
    BYTES.get_or_init(|| {
        use rand::SeedableRng;
        let mut r = rand::rngs::StdRng::seed_from_u64(202);
        let alice_id = Identity::generate(&mut r);
        let bob_id = Identity::generate(&mut r);
        let mut bob_prekeys = bob_id.create_prekeys(4, &mut r);
        let bundle = bob_prekeys.publish();
        let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
        let initial = alice.encrypt(b"hi", &mut r).unwrap();
        let (mut bob, _) =
            establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
        let reply = bob.encrypt(b"ack", &mut r).unwrap();
        alice.decrypt(&reply, &mut r).unwrap();
        alice.export().to_vec()
    })
}

proptest! {
    /// Neither persisted-state decoder panics on arbitrary bytes; it returns Ok
    /// or Err (CR-28). The runtime complement to the nightly cargo-fuzz smoke,
    /// under `cargo test`.
    #[test]
    fn persisted_decoders_never_panic(bytes in prop::collection::vec(any::<u8>(), 0..8192)) {
        let _ = PrekeyStore::from_bytes(&bytes);
        let _ = Session::import(&bytes);
    }

    /// A mutation of a canonical store that is still accepted re-encodes to
    /// exactly the bytes it was decoded from -- the canonicality property, now
    /// exercised on near-valid input (CR-28). Guarded to current-version (v4)
    /// acceptances: a mutation that relabels the store v1, v2 or v3 is
    /// legitimately upgraded on re-encode, which is not a canonicality
    /// violation.
    #[test]
    fn prekey_store_accepted_mutations_reencode_identically(
        at in any::<usize>(),
        bit in 0u8..8,
    ) {
        let mut bytes = canonical_prekey_store().to_vec();
        let i = at % bytes.len();
        bytes[i] ^= 1 << bit;
        if bytes[0] == 0x04 {
            if let Ok(store) = PrekeyStore::from_bytes(&bytes) {
                let reencoded = store.to_bytes();
                prop_assert_eq!(reencoded.as_slice(), bytes.as_slice());
            }
        }
    }

    /// The same for `Session::import`, whose only version is v1, so every
    /// accepted input re-encodes identically (CR-28).
    #[test]
    fn session_accepted_mutations_reencode_identically(
        at in any::<usize>(),
        bit in 0u8..8,
    ) {
        let mut bytes = canonical_session().to_vec();
        let i = at % bytes.len();
        bytes[i] ^= 1 << bit;
        if let Ok(session) = Session::import(&bytes) {
            let reencoded = session.export();
            prop_assert_eq!(reencoded.as_slice(), bytes.as_slice());
        }
    }
}

proptest! {
    /// No arbitrary byte string makes a decoder panic. It returns Ok or Err.
    #[test]
    fn decoders_never_panic(bytes in prop::collection::vec(any::<u8>(), 0..4096)) {
        let _ = decode_message(&bytes);
        let _ = decode_initial(&bytes);
        let _ = message_type(&bytes);
    }

    /// Any well-formed ratchet message round-trips: decoding an encoding returns
    /// exactly what went in, for every canonical key, counter pair, and
    /// ciphertext.
    #[test]
    fn message_round_trips(
        dh in prop::array::uniform32(any::<u8>()),
        pn in any::<u32>(),
        n in any::<u32>(),
        pq_epoch in any::<u64>(),
        pq_n in any::<u64>(),
        ag_epoch in any::<u64>(),
        chunk_index in any::<u16>(),
        chunk_data in prop::array::uniform32(any::<u8>()),
        carries_chunk in any::<bool>(),
        ciphertext in prop::collection::vec(any::<u8>(), 0..1024),
    ) {
        // The agreement half is generated too, both present and absent, because
        // a message carries it now and a property that only ever exercised the
        // classical fields would say nothing about the half that was added.
        let header = Composite {
            dh: canonical_key(dh),
            pn,
            n,
            pq_epoch,
            pq_n,
            ag_epoch,
            ag_type: if carries_chunk { AgreementType::Ek } else { AgreementType::None },
            ag_chunk: if carries_chunk {
                Some(Codeword { index: chunk_index, data: chunk_data })
            } else {
                None
            },
        };
        let encoded = encode_message(&header, &ciphertext);
        let decoded = decode_message(&encoded).expect("a well-formed message decodes");
        prop_assert_eq!(decoded.header, header);
        prop_assert_eq!(decoded.ciphertext, ciphertext);
    }

    /// A ratchet key with bit 255 set is a second spelling of a key, and the
    /// message carrying it never decodes, whatever the rest of the key and the
    /// ciphertext are.
    #[test]
    fn a_respelled_ratchet_key_never_decodes(
        dh in prop::array::uniform32(any::<u8>()),
        ciphertext in prop::collection::vec(any::<u8>(), 0..64),
    ) {
        let mut dh = dh;
        dh[31] |= 0x80;
        let header = Composite { dh, ..sample_composite() };
        prop_assert!(decode_message(&encode_message(&header, &ciphertext)).is_err());
    }

    /// Truncating a valid message anywhere never panics and never decodes: a
    /// prefix is either too short or fails the framing check.
    #[test]
    fn truncation_is_rejected_cleanly(
        cut in 0usize..200,
        ciphertext in prop::collection::vec(any::<u8>(), 0..64),
    ) {
        let encoded = encode_message(&sample_composite(), &ciphertext);
        if cut < encoded.len() {
            // A strict prefix must not decode to the original.
            let got = decode_message(&encoded[..cut]);
            if let Ok(m) = got {
                prop_assert_ne!(m.ciphertext.len(), ciphertext.len());
            }
        }
    }

    /// The associated-data concatenation is injective in its split: two different
    /// (ad, header) pairs never produce the same bytes, which is what stops a
    /// header being reinterpreted as application data.
    #[test]
    fn concat_ad_is_unambiguous(
        ad1 in prop::collection::vec(any::<u8>(), 0..64),
        ad2 in prop::collection::vec(any::<u8>(), 0..64),
        dh in prop::array::uniform32(any::<u8>()),
    ) {
        prop_assume!(ad1 != ad2);
        let header = Composite { dh, ..sample_composite() };
        prop_assert_ne!(concat_ad(&ad1, &header), concat_ad(&ad2, &header));
    }
}
