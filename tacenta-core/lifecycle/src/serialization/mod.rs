//! serialization: the wire encoding.
//!
//! This module follows tacenta-spec/protocol/message-format.md and the model in
//! tacenta-model (`Model.Messages`, `Model.CompositeHeader`). The header's round
//! trip is proved in tacenta-proofs (`Proofs.Serialization.decode_encode_composite`)
//! rather than only sampled here.
//!
//! Encodings are canonical: exactly one valid spelling of a message, and a
//! decoder that rejects anything else rather than repairing it. Fixed-width
//! counters rather than variable-length integers keep the decoder loop-free and
//! inside the subset the Charon and Aeneas translation models.

use crate::ratchet::Header;

pub mod composite;

use composite::encode_composite;

// The version and type bytes, the decode error, the decoders for both kinds of
// message, and the prekey bundle's encoding live in `tacenta-wire`, so the
// translation covers them; see `composite`. Re-exported here under their old
// paths.
pub use tacenta_wire::{
    DecodeError, DecodedInitial, DecodedMessage, TYPE_BUNDLE, TYPE_INITIAL, TYPE_RATCHET, VERSION,
    WireBundle, decode_bundle, decode_initial, decode_message, encode_bundle,
};

/// The identifier meaning "no prekey was used". **Wire-sensitive.**
pub const ABSENT_ID: u32 = 0;

/// Bytes of a serialized header: the ratchet key and two counters.
pub const HEADER_LEN: usize = 32 + 4 + 4;

/// What kind of message a byte string is, read from its framing without
/// decoding the rest. A receiver dispatches on this so it can recognise an
/// initial message even when it already has a session (a reset or a changed
/// identity), rather than trying to decrypt it as a ratchet message.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MessageType {
    Ratchet,
    Initial,
}

/// Peek at a message's type. Returns `None` for an empty input, an unrecognised
/// version, or an unknown type byte.
pub fn message_type(bytes: &[u8]) -> Option<MessageType> {
    if bytes.len() < 2 || bytes[0] != VERSION {
        return None;
    }
    if bytes[1] == TYPE_RATCHET {
        Some(MessageType::Ratchet)
    } else if bytes[1] == TYPE_INITIAL {
        Some(MessageType::Initial)
    } else {
        None
    }
}

/// `MAX_PLAINTEXT_LEN` (message-format.md, Message size; CONSTANTS.md,
/// Bounds): the longest plaintext a session encrypts, 2^20 - 1 bytes. One
/// protocol constant, the same on every platform; not negotiated and not
/// configurable. `Session::encrypt` refuses a longer plaintext as
/// `Error::PlaintextTooLong` before anything else.
pub const MAX_PLAINTEXT_LEN: usize = 1_048_575;

/// `MAX_RATCHET_FRAME_LEN`: the longest ratchet message a receiver accepts,
/// standalone or inside an initial message. Derived, not chosen:
/// `150 + 16 * (MAX_PLAINTEXT_LEN / 16)`, the 102-byte composite header, the
/// padded AES-CBC ciphertext and the 32-byte tag.
pub const MAX_RATCHET_FRAME_LEN: usize = 1_048_710;

/// `MAX_INITIAL_FRAME_LEN`: the longest frame any receiving operation accepts.
/// Derived: `MAX_RATCHET_FRAME_LEN` plus the 1,652-byte initial wrapper.
pub const MAX_INITIAL_FRAME_LEN: usize = 1_050_362;

/// The initial wrapper with ML-KEM-1024's 1,568-byte ciphertext:
/// `2 + 33 + 33 + 4 + 1,568 + 4 + 4 + 4`.
const INITIAL_WRAPPER_LEN: usize = 1_652;

/// Where an initial frame's `kem_ciphertext_len` starts: the version and type
/// bytes and the two 33-byte `EncodeEC` keys.
const INITIAL_KEM_LEN_AT: usize = 68;

/// Where it ends. An initial frame shorter than this does not hold it.
const INITIAL_KEM_LEN_END: usize = 72;

/// Every byte of the initial wrapper except `kem_ciphertext`: version, type,
/// both keys, `kem_ciphertext_len` and the three identifiers. The ratchet
/// message starts this many bytes plus `kem_ciphertext_len` into the frame.
const INITIAL_FIXED_LEN: usize = 84;

// The literals above are what the translation reads; these tie them to the
// expressions they stand for, so a wrong literal fails the build.
#[allow(
    dead_code,
    reason = "a compile-time check, named because the translation cannot take an anonymous constant"
)]
const MAX_RATCHET_FRAME_LEN_IS_DERIVED: () =
    assert!(MAX_RATCHET_FRAME_LEN == 150 + 16 * (MAX_PLAINTEXT_LEN / 16));
#[allow(
    dead_code,
    reason = "a compile-time check, named because the translation cannot take an anonymous constant"
)]
const MAX_INITIAL_FRAME_LEN_IS_DERIVED: () =
    assert!(MAX_INITIAL_FRAME_LEN == MAX_RATCHET_FRAME_LEN + INITIAL_WRAPPER_LEN);
#[allow(
    dead_code,
    reason = "a compile-time check, named because the translation cannot take an anonymous constant"
)]
const INITIAL_WRAPPER_LEN_IS_ITS_FIELDS: () =
    assert!(INITIAL_WRAPPER_LEN == 2 + 33 + 33 + 4 + 1568 + 4 + 4 + 4);
#[allow(
    dead_code,
    reason = "a compile-time check, named because the translation cannot take an anonymous constant"
)]
const INITIAL_FIXED_LEN_IS_ITS_FIELDS: () = assert!(
    INITIAL_FIXED_LEN == INITIAL_WRAPPER_LEN - 1568
        && INITIAL_KEM_LEN_END == INITIAL_KEM_LEN_AT + 4
);
#[allow(
    dead_code,
    reason = "a compile-time check, named because the translation cannot take an anonymous constant"
)]
const MAX_PLAINTEXT_LEN_FIXES_THE_RECEIVED_MAXIMUM: () =
    assert!(MAX_PLAINTEXT_LEN % 16 == 15 && MAX_PLAINTEXT_LEN == (1 << 20) - 1);

/// The length of the ratchet message inside an initial frame of `frame_len`
/// bytes whose `kem_ciphertext_len` is `kem_len`, or `None` when that field
/// runs past the end of the frame (the initial-message decoder refuses such a
/// frame, so no ratchet message is ever taken from it).
///
/// **Checked arithmetic is the point**, as in the wire crate's `span_end`: on a
/// 32-bit target `84 + kem_len` can exceed `usize::MAX`, and a sum that does
/// not fit is treated as running past the end, never wrapped.
// A `match` rather than `checked_add(..).filter(..)`: the translation does not
// model closures.
#[allow(clippy::manual_filter)]
pub fn nested_ratchet_len(frame_len: usize, kem_len: u32) -> Option<usize> {
    match INITIAL_FIXED_LEN.checked_add(kem_len as usize) {
        Some(start) => {
            if start <= frame_len {
                Some(frame_len - start)
            } else {
                None
            }
        }
        None => None,
    }
}

/// The length of the ratchet message a received frame carries, from the values
/// the size rule reads: the frame's length, whether it is an initial frame,
/// and, for an initial frame that holds it, its `kem_ciphertext_len`. Every
/// frame that is not an initial frame is its own ratchet message. `None` for
/// an initial frame whose ratchet message cannot be located.
pub fn ratchet_span_of(frame_len: usize, initial: bool, kem_len: Option<u32>) -> Option<usize> {
    if initial {
        match kem_len {
            Some(k) => nested_ratchet_len(frame_len, k),
            None => None,
        }
    } else {
        Some(frame_len)
    }
}

/// The size rule on the values it reads (message-format.md, Message size):
/// refused when the frame is longer than `MAX_INITIAL_FRAME_LEN` (rule 1), or
/// when the ratchet message it carries is longer than `MAX_RATCHET_FRAME_LEN`
/// (rules 2 and 3). A frame whose ratchet message cannot be located is refused
/// only by rule 1, and goes on to the decoder otherwise.
pub fn frame_too_long(frame_len: usize, initial: bool, kem_len: Option<u32>) -> bool {
    if frame_len > MAX_INITIAL_FRAME_LEN {
        return true;
    }
    match ratchet_span_of(frame_len, initial, kem_len) {
        Some(span) => span > MAX_RATCHET_FRAME_LEN,
        None => false,
    }
}

/// An initial frame's `kem_ciphertext_len`, read from bytes 68 to 71, if the
/// frame holds them. Reads four bytes and allocates nothing.
fn initial_kem_len(bytes: &[u8]) -> Option<u32> {
    if bytes.len() < INITIAL_KEM_LEN_END {
        return None;
    }
    // Bytes `INITIAL_KEM_LEN_AT` to `INITIAL_KEM_LEN_END - 1`, written as
    // literals so the translation sees no index arithmetic.
    Some(u32::from_be_bytes([
        bytes[68], bytes[69], bytes[70], bytes[71],
    ]))
}

/// The length of the ratchet message a received frame carries, read from its
/// framing alone: the whole frame unless it is an initial frame, and for an
/// initial frame the span its own `kem_ciphertext_len` locates, whatever value
/// that declares. Reads at most six bytes and allocates nothing.
pub fn ratchet_span(bytes: &[u8]) -> Option<usize> {
    match message_type(bytes) {
        Some(MessageType::Initial) => ratchet_span_of(bytes.len(), true, initial_kem_len(bytes)),
        _ => ratchet_span_of(bytes.len(), false, None),
    }
}

/// The size rule, applied to a received frame before anything else reads it
/// (message-format.md, Message size). `Err(DecodeError::TooLong)` when it
/// refuses. It reads the frame's length, its first two bytes and, for an
/// initial frame, the four bytes of `kem_ciphertext_len`; it copies and
/// allocates nothing, so it can run before every copy, decode, cryptographic
/// operation and random draw.
pub fn check_frame_size(bytes: &[u8]) -> Result<(), DecodeError> {
    let refused = match message_type(bytes) {
        Some(MessageType::Initial) => frame_too_long(bytes.len(), true, initial_kem_len(bytes)),
        _ => frame_too_long(bytes.len(), false, None),
    };
    if refused {
        Err(DecodeError::TooLong)
    } else {
        Ok(())
    }
}

/// Serialize a header: the ratchet public key, then the previous chain length
/// and the message number, each four bytes big-endian.
pub fn encode_header(header: &Header) -> Vec<u8> {
    let mut out = Vec::with_capacity(HEADER_LEN);
    out.extend_from_slice(&header.dh);
    out.extend_from_slice(&header.pn.to_be_bytes());
    out.extend_from_slice(&header.n.to_be_bytes());
    out
}

/// Serialize a ratchet message: version, type, header, then the AEAD output.
pub fn encode_message(header: &composite::Composite, ciphertext: &[u8]) -> Vec<u8> {
    let mut out = encode_composite(header);
    out.extend_from_slice(ciphertext);
    out
}

/// `CONCAT(ad, header)`: the length of the application's associated data, then
/// that data, then the serialized header.
///
/// The length prefix is what the Double Ratchet specification requires when the
/// application's part is not self-delimiting: without it a different split of
/// the same bytes would be equally valid, and a header could be reinterpreted.
/// **The composite header, not the classical one.** The associated data covers
/// the agreement's message as well as the Double Ratchet's header. If it
/// covered only the latter, an intermediary could strip the agreement's
/// message -- set the presence byte and the codeword to absent -- and the
/// payload would still authenticate: the post-quantum half could be removed
/// from a conversation in flight without either party noticing.
pub fn concat_ad(ad: &[u8], header: &composite::Composite) -> Vec<u8> {
    let encoded = encode_composite(header);
    let mut out = Vec::with_capacity(4 + ad.len() + encoded.len());
    out.extend_from_slice(&(ad.len() as u32).to_be_bytes());
    out.extend_from_slice(ad);
    out.extend_from_slice(&encoded);
    out
}

/// Serialize an initial (prekey) message. `identity` and `ephemeral` are
/// `EncodeEC` forms, so they carry their own type byte.
pub fn encode_initial(
    identity: &[u8],
    ephemeral: &[u8],
    kem_ciphertext: &[u8],
    signed_prekey_id: u32,
    one_time_prekey_id: u32,
    kem_prekey_id: u32,
    message: &[u8],
) -> Vec<u8> {
    let mut out = Vec::new();
    out.push(VERSION);
    out.push(TYPE_INITIAL);
    out.extend_from_slice(identity);
    out.extend_from_slice(ephemeral);
    out.extend_from_slice(&(kem_ciphertext.len() as u32).to_be_bytes());
    out.extend_from_slice(kem_ciphertext);
    out.extend_from_slice(&signed_prekey_id.to_be_bytes());
    out.extend_from_slice(&one_time_prekey_id.to_be_bytes());
    out.extend_from_slice(&kem_prekey_id.to_be_bytes());
    out.extend_from_slice(message);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The associated data encoding is self-delimiting: the length prefix and
    /// fixed-width composite header make the split recoverable from the bytes.
    #[test]
    fn concat_ad_is_self_delimiting() {
        let header = composite::Composite {
            dh: [0xaa; 32],
            pn: 1,
            n: 2,
            pq_epoch: 3,
            pq_n: 4,
            ag_epoch: 3,
            ag_type: composite::AgreementType::None,
            ag_chunk: None,
        };

        let short = concat_ad(b"ab", &header);
        let long = concat_ad(b"abcd", &header);
        assert_eq!(&short[..4], &(2u32).to_be_bytes());
        assert_eq!(&long[..4], &(4u32).to_be_bytes());
        assert_eq!(long.len(), short.len() + 2);
        assert_ne!(concat_ad(b"ab", &header), concat_ad(b"a", &header));
    }

    /// The composite a message actually carries now. The agreement half is
    /// present rather than absent, so these tests exercise the shape a real
    /// message has instead of the degenerate one.
    fn message_header() -> composite::Composite {
        composite::Composite {
            dh: [0x0a; 32],
            pn: 7,
            n: 9,
            pq_epoch: 3,
            pq_n: 5,
            ag_epoch: 3,
            ag_type: composite::AgreementType::Ek,
            ag_chunk: Some(composite::Codeword {
                index: 2,
                data: [0x5c; composite::CHUNK_BYTES],
            }),
        }
    }

    #[test]
    fn a_message_round_trips() {
        let encoded = encode_message(&message_header(), b"ciphertext");
        let decoded = decode_message(&encoded).unwrap();
        assert_eq!(decoded.header, message_header());
        assert_eq!(decoded.ciphertext, b"ciphertext");
    }

    #[test]
    fn an_empty_ciphertext_round_trips() {
        let encoded = encode_message(&message_header(), b"");
        let decoded = decode_message(&encoded).unwrap();
        assert_eq!(decoded.header, message_header());
        assert!(decoded.ciphertext.is_empty());
    }

    #[test]
    fn an_unknown_version_is_rejected() {
        let mut encoded = encode_message(&message_header(), b"ciphertext");
        encoded[0] = 0x00;
        assert_eq!(decode_message(&encoded), Err(DecodeError::UnknownVersion));
    }

    #[test]
    fn an_initial_message_is_not_decoded_as_a_ratchet_message() {
        // The type byte is what lets a receiver tell the two apart on the wire,
        // which is what the session-reset and identity-change cases rely on.
        // Two paths, because the length check runs before the type check.
        // Both must refuse.
        //
        // A short initial message never reaches the type byte.
        let short = encode_initial(&[0x01; 33], &[0x02; 33], b"kem", 1, 2, 3, b"");
        assert_eq!(decode_message(&short), Err(DecodeError::TooShort));
        assert_eq!(message_type(&short), Some(MessageType::Initial));

        // One long enough to reach it is refused *by* it, which is the check
        // that actually distinguishes the two message kinds.
        let inner = encode_message(&message_header(), b"ciphertext");
        let initial = encode_initial(&[0x01; 33], &[0x02; 33], b"kem", 1, 2, 3, &inner);
        assert!(initial.len() > composite::COMPOSITE_LEN);
        assert_eq!(decode_message(&initial), Err(DecodeError::WrongType));
        assert_eq!(message_type(&initial), Some(MessageType::Initial));

        let ratchet = encode_message(&message_header(), b"ct");
        assert_eq!(message_type(&ratchet), Some(MessageType::Ratchet));

        assert_eq!(message_type(b"\x00\x01"), None);
        assert_eq!(message_type(b""), None);
    }

    #[test]
    fn a_truncated_message_is_rejected() {
        let encoded = encode_message(&message_header(), b"ciphertext");
        for cut in 0..2 + HEADER_LEN {
            assert!(
                decode_message(&encoded[..cut]).is_err(),
                "a {cut}-byte message must not decode"
            );
        }
    }

    #[test]
    fn the_associated_data_pair_is_unambiguous() {
        // Without the length prefix these two splits would concatenate to the
        // same bytes, and a header could be reinterpreted as application data.
        assert_ne!(
            concat_ad(b"ab", &message_header()),
            concat_ad(b"a", &message_header())
        );
    }

    #[test]
    fn associated_data_records_the_length() {
        let ad = b"alicebob";
        let out = concat_ad(ad, &message_header());
        assert_eq!(&out[0..4], &(ad.len() as u32).to_be_bytes());
        assert_eq!(&out[4..4 + ad.len()], ad);
        assert_eq!(
            &out[4 + ad.len()..],
            &encode_composite(&message_header())[..]
        );
    }

    /// A 33-byte `EncodeEC` key: the curve byte, then 32 copies of `fill`.
    /// `decode_initial` refuses a key without the curve byte.
    fn ec_key(fill: u8) -> [u8; 33] {
        let mut k = [fill; 33];
        k[0] = 0x05;
        k
    }

    #[test]
    fn an_initial_message_round_trips() {
        let inner = encode_message(&message_header(), b"ciphertext");
        let encoded = encode_initial(
            &ec_key(0x01),
            &ec_key(0x02),
            b"kem-ciphertext",
            11,
            ABSENT_ID,
            13,
            &inner,
        );
        let decoded = decode_initial(&encoded).unwrap();
        assert_eq!(decoded.identity, ec_key(0x01).to_vec());
        assert_eq!(decoded.ephemeral, ec_key(0x02).to_vec());
        assert_eq!(decoded.kem_ciphertext, b"kem-ciphertext");
        assert_eq!(decoded.signed_prekey_id, 11);
        assert_eq!(decoded.one_time_prekey_id, ABSENT_ID);
        assert_eq!(decoded.kem_prekey_id, 13);
        assert_eq!(decoded.message, inner);

        // The inner message still decodes on its own.
        let inner_decoded = decode_message(&decoded.message).unwrap();
        assert_eq!(inner_decoded.header, message_header());
    }

    #[test]
    fn a_kem_length_that_overruns_is_rejected() {
        let mut encoded = encode_initial(&ec_key(0x01), &ec_key(0x02), b"kem", 1, 2, 3, b"");
        // The KEM length sits after the version, the type, and the two curve keys.
        let at = 2 + 33 + 33;
        encoded[at..at + 4].copy_from_slice(&0xffff_u32.to_be_bytes());
        assert_eq!(decode_initial(&encoded), Err(DecodeError::LengthOverrun));
    }

    /// The bundle decoder rejects the largest length the wire can carry, which
    /// is the reachable form of the case above.
    #[test]
    fn a_bundle_kem_length_of_u32_max_is_rejected() {
        let mut encoded = encode_bundle(&sample_fields(None));
        let at = 2 + 32 + 32 + 64;
        encoded[at..at + 4].copy_from_slice(&u32::MAX.to_be_bytes());
        assert_eq!(decode_bundle(&encoded), Err(DecodeError::LengthOverrun));
    }

    /// And so does the initial-message decoder, with the same value.
    #[test]
    fn an_initial_kem_length_of_u32_max_is_rejected() {
        let mut encoded = encode_initial(&ec_key(0x01), &ec_key(0x02), b"kem", 1, 2, 3, b"");
        let at = 2 + 33 + 33;
        encoded[at..at + 4].copy_from_slice(&u32::MAX.to_be_bytes());
        assert_eq!(decode_initial(&encoded), Err(DecodeError::LengthOverrun));
    }

    /// An absent one-time prekey must have zero padding, like the composite
    /// header's. Same rule, same file, pinned at both sites.
    #[test]
    fn a_bundle_with_an_absent_prekey_requires_zero_padding() {
        let canonical = encode_bundle(&sample_fields(None));
        assert!(decode_bundle(&canonical).is_ok());

        // The presence byte sits after the KEM signature; the thirty-two bytes
        // after it are the padding under test.
        let at = canonical.len() - 12 - 32;
        for offset in [0usize, 1, 31] {
            let mut bytes = canonical.clone();
            bytes[at + offset] = 0x01;
            assert_eq!(
                decode_bundle(&bytes),
                Err(DecodeError::LengthOverrun),
                "byte {offset} of the absent prekey's padding was ignored"
            );
        }
    }

    /// And a present one still round trips, so the check did not overcorrect
    /// into refusing real keys.
    #[test]
    fn a_bundle_with_a_present_prekey_still_round_trips() {
        let fields = sample_fields(Some([0x77; 32]));
        let encoded = encode_bundle(&fields);
        assert_eq!(decode_bundle(&encoded), Ok(fields));
    }

    fn sample_fields(one_time: Option<[u8; 32]>) -> WireBundle {
        WireBundle {
            identity_key: [0x11; 32],
            signed_prekey: [0x22; 32],
            signed_prekey_signature: [0x33; 64],
            kem_prekey: vec![0x44; 1568],
            kem_prekey_signature: [0x55; 64],
            one_time_prekey: one_time,
            signed_prekey_id: 7,
            one_time_prekey_id: if one_time.is_some() { 8 } else { ABSENT_ID },
            kem_prekey_id: 9,
        }
    }

    fn sample_bundle() -> Vec<u8> {
        encode_bundle(&sample_fields(Some([0x66; 32])))
    }

    /// Decoding an encoded bundle gives back exactly what was encoded, in both
    /// shapes. Stated on the one type, so this is the whole property rather than
    /// a field-by-field spot check.
    #[test]
    fn a_bundle_round_trips() {
        for one_time in [Some([0x66; 32]), None] {
            let fields = sample_fields(one_time);
            assert_eq!(decode_bundle(&encode_bundle(&fields)), Ok(fields));
        }
    }

    /// Both shapes are the same length, and the presence byte alone tells them
    /// apart.
    ///
    /// The layout is fixed deliberately: a variable-length optional field forces
    /// a branch on both sides, which is what stopped the round trip being proved
    /// (see `Proofs.Serialization`). The property to hold onto is not that the
    /// lengths differ but that the *encodings* do.
    #[test]
    fn the_two_bundle_shapes_are_the_same_length_and_still_differ() {
        let with = sample_bundle();
        let without = encode_bundle(&sample_fields(None));
        assert_eq!(with.len(), without.len(), "fixed layout");
        assert_ne!(with, without, "the presence byte distinguishes them");
        assert_ne!(
            decode_bundle(&with).unwrap().one_time_prekey,
            decode_bundle(&without).unwrap().one_time_prekey
        );
    }

    #[test]
    fn a_truncated_bundle_is_rejected() {
        let bytes = sample_bundle();
        for cut in [0, 1, 2, 40, 100, bytes.len() - 1] {
            assert!(
                decode_bundle(&bytes[..cut]).is_err(),
                "a bundle truncated to {cut} bytes was accepted"
            );
        }
    }

    /// Trailing bytes are rejected. A bundle is a whole object, so a decoder
    /// that ignored what followed would accept two different byte strings as
    /// the same bundle.
    #[test]
    fn a_bundle_with_trailing_bytes_is_rejected() {
        let mut bytes = sample_bundle();
        bytes.push(0x00);
        assert!(decode_bundle(&bytes).is_err());
    }

    #[test]
    fn a_bundle_is_not_a_message() {
        let bundle = sample_bundle();
        assert!(decode_message(&bundle).is_err());
        assert!(decode_initial(&bundle).is_err());
        let msg = encode_message(&message_header(), b"ciphertext");
        assert!(decode_bundle(&msg).is_err());
    }

    /// The length prefix is what stops a bundle carrying one parameter set's
    /// KEM key from being read as another's.
    #[test]
    fn a_bundle_with_a_lying_length_is_rejected() {
        let mut bytes = sample_bundle();
        // The KEM length sits after version, type, and three fixed fields.
        let at = 2 + 32 + 32 + 64;
        bytes[at..at + 4].copy_from_slice(&u32::MAX.to_be_bytes());
        assert!(decode_bundle(&bytes).is_err());
    }
}
