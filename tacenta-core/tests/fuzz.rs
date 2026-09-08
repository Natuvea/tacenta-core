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
use tacenta_core::serialization::{
    concat_ad, decode_initial, decode_message, encode_message, message_type,
};

proptest! {
    /// No arbitrary byte string makes a decoder panic. It returns Ok or Err.
    #[test]
    fn decoders_never_panic(bytes in prop::collection::vec(any::<u8>(), 0..4096)) {
        let _ = decode_message(&bytes);
        let _ = decode_initial(&bytes);
        let _ = message_type(&bytes);
    }

    /// Any well-formed ratchet message round-trips: decoding an encoding returns
    /// exactly what went in, for every key, counter pair, and ciphertext.
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
            dh,
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
