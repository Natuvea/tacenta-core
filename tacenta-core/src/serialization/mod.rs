//! serialization: the wire encoding.
//!
//! This module follows tacenta-spec/protocol/message-format.md and the model in
//! tacenta-model (`Model.Messages`). The round-trip
//! property is proved in tacenta-proofs (`Proofs.Serialization.decode_encode`)
//! rather than only sampled here.
//!
//! Encodings are canonical: exactly one valid spelling of a message, and a
//! decoder that rejects anything else rather than repairing it. Fixed-width
//! counters rather than variable-length integers keep the decoder loop-free and
//! inside the subset the Charon and Aeneas translation models.

use crate::ratchet::Header;

/// The message version byte. **Wire-sensitive** (message-format.md).
pub mod composite;

use composite::{decode_composite, encode_composite};

pub const VERSION: u8 = 0x01;

/// Message type: a ratchet message. **Wire-sensitive.**
pub const TYPE_RATCHET: u8 = 0x01;

/// Message type: an initial (prekey) message. **Wire-sensitive.**
pub const TYPE_INITIAL: u8 = 0x02;

/// Type byte for a published prekey bundle.
///
/// A bundle is not a message and never travels as one, but it shares this
/// module's version and type framing so that a decoder given the wrong bytes
/// says so rather than misreading them. That is the same reason the two message
/// types are distinguished, and the reason costs one byte.
pub const TYPE_BUNDLE: u8 = 0x03;

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
    match bytes {
        [VERSION, TYPE_RATCHET, ..] => Some(MessageType::Ratchet),
        [VERSION, TYPE_INITIAL, ..] => Some(MessageType::Initial),
        _ => None,
    }
}

/// Why a decode failed. Distinct from an authentication failure, and no more
/// informative than "not acceptable".
///
/// `#[non_exhaustive]`: pre-1.0, so new decode-failure reasons are not a
/// breaking change and a consumer must carry a wildcard arm (CR-27).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum DecodeError {
    /// The version byte is not one this implementation accepts.
    UnknownVersion,
    /// The type byte is not the one expected for this decoder.
    WrongType,
    /// The input is shorter than its fixed fields require.
    TooShort,
    /// A length prefix runs past the end of the input.
    LengthOverrun,
}

/// A decoded ratchet message.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DecodedMessage {
    pub header: composite::Composite,
    pub ciphertext: Vec<u8>,
}

/// A decoded initial (prekey) message.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DecodedInitial {
    pub identity: Vec<u8>,
    pub ephemeral: Vec<u8>,
    pub kem_ciphertext: Vec<u8>,
    pub signed_prekey_id: u32,
    pub one_time_prekey_id: u32,
    pub kem_prekey_id: u32,
    pub message: Vec<u8>,
}

/// Take `n` bytes from `at`, advancing `at`, and refuse anything that does not
/// fit rather than computing an offset that cannot exist.
///
/// **The checked addition is the point of this function.** A decoder reads a
/// four-byte length off the wire and casts it to `usize`. On a 64-bit target
/// `at + n` cannot overflow, because `u32::MAX` plus a small offset is nowhere
/// near the top of the range, and the length check catches it. On a 32-bit
/// target it can: `u32::MAX as usize` plus any nonzero offset wraps, a debug
/// build panics on the addition, and a release build wraps to a small number,
/// passes the length check, and panics on the slice instead. The crate builds
/// for `armv7-linux-androideabi`, so that target is not hypothetical.
///
/// Every length that came off the wire goes through here. Two decoders need
/// the same check, which is the argument for one function over two
/// expressions.
/// The two cases report differently, and the difference is worth keeping: a
/// fixed field that does not fit means the input is `TooShort`, while a length
/// read off the wire that does not fit is a `LengthOverrun`. Overflow is
/// reported as whatever the caller's case is, because a length too large to add
/// is the same failure as one too large to fit.
fn take_at<'a>(
    bytes: &'a [u8],
    at: &mut usize,
    n: usize,
    err: DecodeError,
) -> Result<&'a [u8], DecodeError> {
    let end = at.checked_add(n).ok_or(err)?;
    if bytes.len() < end {
        return Err(err);
    }
    let s = &bytes[*at..end];
    *at = end;
    Ok(s)
}

/// A field whose width the format fixes.
fn take_fixed<'a>(bytes: &'a [u8], at: &mut usize, n: usize) -> Result<&'a [u8], DecodeError> {
    take_at(bytes, at, n, DecodeError::TooShort)
}

/// A field whose width came off the wire, and is therefore an attacker's to
/// choose.
fn take_wire<'a>(bytes: &'a [u8], at: &mut usize, n: usize) -> Result<&'a [u8], DecodeError> {
    take_at(bytes, at, n, DecodeError::LengthOverrun)
}

fn read_be32(bytes: &[u8], at: usize) -> Result<u32, DecodeError> {
    let mut cursor = at;
    let s = take_fixed(bytes, &mut cursor, 4)?;
    let mut buf = [0u8; 4];
    buf.copy_from_slice(s);
    Ok(u32::from_be_bytes(buf))
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

/// Parse a ratchet message, rejecting anything that is not canonical.
///
/// The header is a composite one: both ratchets' state and the agreement's
/// message, in one structure. `decode_composite` returns the bytes that
/// followed it, which are the ciphertext.
pub fn decode_message(bytes: &[u8]) -> Result<DecodedMessage, DecodeError> {
    let (header, rest) = decode_composite(bytes)?;
    Ok(DecodedMessage {
        header,
        ciphertext: rest.to_vec(),
    })
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

/// A prekey bundle's fields on the wire: public key material and the identifiers
/// a recipient echoes back, all of it public.
///
/// Both the encoder's input and the decoder's output, so the round trip is
/// stated on one type rather than between two. Clippy asked for this by
/// objecting to a nine-argument encoder, and it was right for a better reason
/// than argument count.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct WireBundle {
    pub identity_key: [u8; 32],
    pub signed_prekey: [u8; 32],
    pub signed_prekey_signature: [u8; 64],
    pub kem_prekey: Vec<u8>,
    pub kem_prekey_signature: [u8; 64],
    pub one_time_prekey: Option<[u8; 32]>,
    pub signed_prekey_id: u32,
    pub one_time_prekey_id: u32,
    pub kem_prekey_id: u32,
}

/// Serialize a published prekey bundle.
///
/// Every field is public key material or an identifier, so nothing here is
/// secret and the encoding needs no protection beyond being unambiguous. It is
/// unambiguous the same way the rest of this module is: fixed-width fields at
/// fixed offsets, one length prefix for the only variable field, and a presence
/// byte for the only optional one.
///
/// The KEM prekey is the sole variable-length field because its size depends on
/// the parameter set. It is length-prefixed rather than assumed, so a bundle
/// produced under one parameter set fails to decode under another instead of
/// being read as a shorter key followed by rubbish.
pub fn encode_bundle(b: &WireBundle) -> Vec<u8> {
    let mut out = Vec::new();
    out.push(VERSION);
    out.push(TYPE_BUNDLE);
    out.extend_from_slice(&b.identity_key);
    out.extend_from_slice(&b.signed_prekey);
    out.extend_from_slice(&b.signed_prekey_signature);
    out.extend_from_slice(&(b.kem_prekey.len() as u32).to_be_bytes());
    out.extend_from_slice(&b.kem_prekey);
    out.extend_from_slice(&b.kem_prekey_signature);
    // Fixed width either way: a presence byte and thirty-two bytes. Emitting
    // the key only when present would save thirty-two bytes on a bundle of
    // about seventeen hundred and make the encoding variable-length, which
    // forces both sides to branch. The zeros are never read; the presence byte
    // alone decides. This is what lets the round trip be *proved* in the model
    // rather than sampled.
    match &b.one_time_prekey {
        None => {
            out.push(0);
            out.extend_from_slice(&[0u8; 32]);
        }
        Some(k) => {
            out.push(1);
            out.extend_from_slice(k);
        }
    }
    out.extend_from_slice(&b.signed_prekey_id.to_be_bytes());
    out.extend_from_slice(&b.one_time_prekey_id.to_be_bytes());
    out.extend_from_slice(&b.kem_prekey_id.to_be_bytes());
    out
}

/// Parse a published prekey bundle. The inverse of [`encode_bundle`].
///
/// Trailing bytes are rejected. A bundle is a whole object rather than a prefix
/// of a stream, so anything after the last field means these are not the bytes
/// they claim to be.
pub fn decode_bundle(bytes: &[u8]) -> Result<WireBundle, DecodeError> {
    if bytes.len() < 2 {
        return Err(DecodeError::TooShort);
    }
    if bytes[0] != VERSION {
        return Err(DecodeError::UnknownVersion);
    }
    if bytes[1] != TYPE_BUNDLE {
        return Err(DecodeError::WrongType);
    }
    let mut at = 2;

    let take = |at: &mut usize, n: usize| take_fixed(bytes, at, n);

    let mut identity_key = [0u8; 32];
    identity_key.copy_from_slice(take(&mut at, 32)?);
    let mut signed_prekey = [0u8; 32];
    signed_prekey.copy_from_slice(take(&mut at, 32)?);
    let mut signed_prekey_signature = [0u8; 64];
    signed_prekey_signature.copy_from_slice(take(&mut at, 64)?);

    let kem_len = read_be32(bytes, at)? as usize;
    at += 4;
    let kem_prekey = take_wire(bytes, &mut at, kem_len)?.to_vec();

    let mut kem_prekey_signature = [0u8; 64];
    kem_prekey_signature.copy_from_slice(take(&mut at, 64)?);

    // Absent means the whole field is zero, not merely that the flag is.
    //
    // Accepting any thirty-two bytes when the flag says absent would give one
    // bundle 2^256 other accepted spellings. The composite header applies the
    // same rule to its absent codeword; this is its sibling.
    //
    // It matters wherever a bundle is hashed, signed, cached or deduplicated:
    // two byte strings that mean one bundle are two entries, two digests, and
    // two chances for a cache to disagree with a verifier.
    let present = take(&mut at, 1)?[0];
    let mut key_bytes = [0u8; 32];
    key_bytes.copy_from_slice(take(&mut at, 32)?);
    let one_time_prekey = match present {
        0 => {
            if key_bytes != [0u8; 32] {
                return Err(DecodeError::LengthOverrun);
            }
            None
        }
        1 => Some(key_bytes),
        _ => return Err(DecodeError::WrongType),
    };

    let signed_prekey_id = read_be32(bytes, at)?;
    at += 4;
    let one_time_prekey_id = read_be32(bytes, at)?;
    at += 4;
    let kem_prekey_id = read_be32(bytes, at)?;
    at += 4;

    if at != bytes.len() {
        return Err(DecodeError::LengthOverrun);
    }

    Ok(WireBundle {
        identity_key,
        signed_prekey,
        signed_prekey_signature,
        kem_prekey,
        kem_prekey_signature,
        one_time_prekey,
        signed_prekey_id,
        one_time_prekey_id,
        kem_prekey_id,
    })
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

/// Parse an initial (prekey) message. `identity` and `ephemeral` are 33 bytes
/// each (a type byte and a curve public key).
pub fn decode_initial(bytes: &[u8]) -> Result<DecodedInitial, DecodeError> {
    const EC_LEN: usize = 33;
    if bytes.len() < 2 {
        return Err(DecodeError::TooShort);
    }
    if bytes[0] != VERSION {
        return Err(DecodeError::UnknownVersion);
    }
    if bytes[1] != TYPE_INITIAL {
        return Err(DecodeError::WrongType);
    }
    let mut at = 2;
    let identity = take_fixed(bytes, &mut at, EC_LEN)?.to_vec();
    let ephemeral = take_fixed(bytes, &mut at, EC_LEN)?.to_vec();

    let kem_len = read_be32(bytes, at)? as usize;
    at += 4;
    let kem_ciphertext = take_wire(bytes, &mut at, kem_len)?.to_vec();

    let signed_prekey_id = read_be32(bytes, at)?;
    at += 4;
    let one_time_prekey_id = read_be32(bytes, at)?;
    at += 4;
    let kem_prekey_id = read_be32(bytes, at)?;
    at += 4;

    Ok(DecodedInitial {
        identity,
        ephemeral,
        kem_ciphertext,
        signed_prekey_id,
        one_time_prekey_id,
        kem_prekey_id,
        message: bytes[at..].to_vec(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn an_initial_message_round_trips() {
        let inner = encode_message(&message_header(), b"ciphertext");
        let encoded = encode_initial(
            &[0x01; 33],
            &[0x02; 33],
            b"kem-ciphertext",
            11,
            ABSENT_ID,
            13,
            &inner,
        );
        let decoded = decode_initial(&encoded).unwrap();
        assert_eq!(decoded.identity, vec![0x01; 33]);
        assert_eq!(decoded.ephemeral, vec![0x02; 33]);
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
        let mut encoded = encode_initial(&[0x01; 33], &[0x02; 33], b"kem", 1, 2, 3, b"");
        // The KEM length sits after the version, the type, and the two curve keys.
        let at = 2 + 33 + 33;
        encoded[at..at + 4].copy_from_slice(&0xffff_u32.to_be_bytes());
        assert_eq!(decode_initial(&encoded), Err(DecodeError::LengthOverrun));
    }

    /// A length that cannot even be *added* to the cursor is refused, rather
    /// than wrapping into a small number that passes the bounds check.
    ///
    /// The decoder tests above cannot reach this. They pass `u32::MAX`, which is
    /// what an attacker can actually write on the wire, and on a 64-bit host
    /// `u32::MAX + 66` is ordinary arithmetic caught by the length check. On a
    /// 32-bit target the same input wraps: a debug build panics on the addition
    /// and a release build wraps to a small number, passes the check, and panics
    /// on the slice. This crate builds for `armv7-linux-androideabi`.
    ///
    /// So this test goes at the helper directly with a value that overflows on
    /// every target, because the alternative is a test that only fails on
    /// hardware the suite does not run on.
    #[test]
    fn a_length_that_cannot_be_added_is_refused_rather_than_wrapping() {
        let bytes = [0u8; 8];

        let mut at = 2;
        assert_eq!(
            take_wire(&bytes, &mut at, usize::MAX),
            Err(DecodeError::LengthOverrun)
        );
        assert_eq!(at, 2, "a refused take must not advance the cursor");

        let mut at = 2;
        assert_eq!(
            take_fixed(&bytes, &mut at, usize::MAX),
            Err(DecodeError::TooShort)
        );
        assert_eq!(at, 2);

        // The boundary itself: exactly enough to overflow by one.
        let mut at = 1;
        assert_eq!(
            take_wire(&bytes, &mut at, usize::MAX),
            Err(DecodeError::LengthOverrun)
        );
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
        let mut encoded = encode_initial(&[0x01; 33], &[0x02; 33], b"kem", 1, 2, 3, b"");
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
