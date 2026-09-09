//! The Triple Ratchet's composite header on the wire.
//!
//! Written from tacenta-spec/protocol/triple-ratchet.md and the model in
//! `Model.CompositeHeader`, whose round-trip is proved in
//! `Proofs.Serialization.decode_encode_composite`.
//!
//! One message of the composition carries three things besides its ciphertext:
//! the Diffie-Hellman ratchet's header, the sparse ratchet's epoch and message
//! number, and the agreement's own message. This encodes all three.
//!
//! ## Why every field is fixed width
//!
//! The specification's one obligation on this encoding is that it parse
//! unambiguously, and fixed width is how that is bought rather than argued: no
//! field's position depends on a value the decoder has already read, so there is
//! no case analysis to get wrong.
//!
//! The agreement's codeword is the one genuinely optional field, and it is
//! encoded the way an absent prekey is in a bundle: a presence byte, then the
//! field's full width regardless, zeroed when absent. It costs thirty-four bytes
//! on a message carrying no codeword.
//!
//! ## What it costs
//!
//! [`COMPOSITE_LEN`](crate::serialization::composite::COMPOSITE_LEN) bytes of header on every message, against the Double
//! Ratchet's forty-one. The specification says the composition costs bandwidth
//! and that the sparse agreement exists to keep it affordable; this is the
//! number.

use super::{DecodeError, TYPE_RATCHET, VERSION};

/// The codeword size, matching `tacenta_erasure::CHUNK_BYTES`. Repeated rather
/// than imported: this module is an encoding and should not acquire a dependency
/// on the codec to name a width.
pub const CHUNK_BYTES: usize = 32;

/// A composite header's width, the same for every message.
pub const COMPOSITE_LEN: usize = 2 + 32 + 4 + 4 + 8 + 8 + 8 + 1 + 1 + 2 + CHUNK_BYTES;

/// What the agreement's message carries.
///
/// `Ct1Ack`, a member of the specification's set, is never produced here and
/// has no byte: the acknowledgement always rides on an `ek_vector` chunk. A
/// peer emitting one therefore fails to parse rather than being ignored
/// without notice; the Braid's page records the same reasoning.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AgreementType {
    None,
    Hdr,
    Ek,
    EkCt1Ack,
    Ct1,
    Ct2,
}

impl AgreementType {
    fn to_byte(self) -> u8 {
        match self {
            AgreementType::None => 0x00,
            AgreementType::Hdr => 0x01,
            AgreementType::Ek => 0x02,
            AgreementType::EkCt1Ack => 0x03,
            AgreementType::Ct1 => 0x04,
            AgreementType::Ct2 => 0x05,
        }
    }

    fn from_byte(b: u8) -> Option<AgreementType> {
        match b {
            0x00 => Some(AgreementType::None),
            0x01 => Some(AgreementType::Hdr),
            0x02 => Some(AgreementType::Ek),
            0x03 => Some(AgreementType::EkCt1Ack),
            0x04 => Some(AgreementType::Ct1),
            0x05 => Some(AgreementType::Ct2),
            _ => None,
        }
    }
}

/// One codeword of an erasure-coded stream.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Codeword {
    pub index: u16,
    pub data: [u8; CHUNK_BYTES],
}

/// Everything a message carries besides its ciphertext.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Composite {
    /// The Diffie-Hellman ratchet's public key.
    pub dh: [u8; 32],
    /// The previous sending chain's length.
    pub pn: u32,
    /// The message number on the classical chain.
    pub n: u32,
    /// The agreement epoch the post-quantum key came from.
    pub pq_epoch: u64,
    /// The message number on that epoch's chain.
    pub pq_n: u64,
    /// The epoch the agreement's own message belongs to.
    pub ag_epoch: u64,
    /// What the agreement's message carries.
    pub ag_type: AgreementType,
    /// Its codeword, when it has one.
    pub ag_chunk: Option<Codeword>,
}

/// Encode a composite header. Always [`COMPOSITE_LEN`] bytes.
pub fn encode_composite(h: &Composite) -> Vec<u8> {
    let mut out = Vec::with_capacity(COMPOSITE_LEN);
    out.push(VERSION);
    out.push(TYPE_RATCHET);
    out.extend_from_slice(&h.dh);
    out.extend_from_slice(&h.pn.to_be_bytes());
    out.extend_from_slice(&h.n.to_be_bytes());
    out.extend_from_slice(&h.pq_epoch.to_be_bytes());
    out.extend_from_slice(&h.pq_n.to_be_bytes());
    out.extend_from_slice(&h.ag_epoch.to_be_bytes());
    out.push(h.ag_type.to_byte());
    match &h.ag_chunk {
        None => {
            out.push(0x00);
            out.extend_from_slice(&[0u8; 2 + CHUNK_BYTES]);
        }
        Some(c) => {
            out.push(0x01);
            out.extend_from_slice(&c.index.to_be_bytes());
            out.extend_from_slice(&c.data);
        }
    }
    out
}

/// Decode a composite header, returning it and the bytes that followed.
///
/// Trailing bytes are returned rather than rejected, because a message is a
/// header followed by its ciphertext.
pub fn decode_composite(bytes: &[u8]) -> Result<(Composite, &[u8]), DecodeError> {
    if bytes.len() < COMPOSITE_LEN {
        return Err(DecodeError::TooShort);
    }
    if bytes[0] != VERSION {
        return Err(DecodeError::UnknownVersion);
    }
    if bytes[1] != TYPE_RATCHET {
        return Err(DecodeError::WrongType);
    }
    let mut dh = [0u8; 32];
    dh.copy_from_slice(&bytes[2..34]);
    let pn = u32::from_be_bytes([bytes[34], bytes[35], bytes[36], bytes[37]]);
    let n = u32::from_be_bytes([bytes[38], bytes[39], bytes[40], bytes[41]]);
    let pq_epoch = be64_at(bytes, 42);
    let pq_n = be64_at(bytes, 50);
    let ag_epoch = be64_at(bytes, 58);
    let ag_type = match AgreementType::from_byte(bytes[66]) {
        Some(t) => t,
        None => return Err(DecodeError::WrongType),
    };
    // **Exactly one spelling, and the decoder is what makes that true.**
    //
    // The presence byte is `0x00` or `0x01` and nothing else, and when the
    // chunk is absent the index and chunk bytes must be zero. A decoder that
    // read any other byte as absent and ignored the index and chunk bytes
    // would accept 2^(8 + 16 + 8*CHUNK_BYTES) - 1 other spellings of one
    // header, against a module that opens by saying there is one. A canonical
    // encoder does not supply that on its own, and a round-trip theorem cannot
    // see the difference, because it only ever asks about bytes the encoder
    // produced.
    //
    // It matters at integration rather than today. Once this header is
    // authenticated as associated data, a decoder that accepts many spellings
    // of one header is a decoder whose output does not determine the bytes that
    // were signed.
    let present = bytes[67];
    if present != 0x00 && present != 0x01 {
        return Err(DecodeError::WrongType);
    }
    let index = u16::from_be_bytes([bytes[68], bytes[69]]);
    let ag_chunk = if present == 0x01 {
        let mut data = [0u8; CHUNK_BYTES];
        data.copy_from_slice(&bytes[70..70 + CHUNK_BYTES]);
        Some(Codeword { index, data })
    } else {
        // Absent means absent: the fields the chunk would have occupied must be
        // zero, or these bytes are not the encoding of any header.
        if index != 0 || bytes[70..70 + CHUNK_BYTES].iter().any(|b| *b != 0) {
            return Err(DecodeError::LengthOverrun);
        }
        None
    };
    Ok((
        Composite {
            dh,
            pn,
            n,
            pq_epoch,
            pq_n,
            ag_epoch,
            ag_type,
            ag_chunk,
        },
        &bytes[COMPOSITE_LEN..],
    ))
}

fn be64_at(bytes: &[u8], at: usize) -> u64 {
    let mut a = [0u8; 8];
    a.copy_from_slice(&bytes[at..at + 8]);
    u64::from_be_bytes(a)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> Composite {
        Composite {
            dh: [0xaa; 32],
            pn: 7,
            n: 9,
            pq_epoch: 3,
            pq_n: 11,
            ag_epoch: 3,
            ag_type: AgreementType::Ct1,
            ag_chunk: Some(Codeword {
                index: 5,
                data: [0xcd; CHUNK_BYTES],
            }),
        }
    }

    fn sample_no_chunk() -> Composite {
        Composite {
            ag_type: AgreementType::None,
            ag_chunk: None,
            ..sample()
        }
    }

    #[test]
    fn every_header_is_the_same_width() {
        assert_eq!(encode_composite(&sample()).len(), COMPOSITE_LEN);
        assert_eq!(encode_composite(&sample_no_chunk()).len(), COMPOSITE_LEN);
    }

    #[test]
    fn it_round_trips() {
        for h in [sample(), sample_no_chunk()] {
            let bytes = encode_composite(&h);
            let (back, rest) = decode_composite(&bytes).unwrap();
            assert_eq!(back, h);
            assert!(rest.is_empty());
        }
    }

    #[test]
    fn trailing_bytes_are_returned_rather_than_consumed() {
        let mut bytes = encode_composite(&sample());
        bytes.extend_from_slice(b"ciphertext");
        let (back, rest) = decode_composite(&bytes).unwrap();
        assert_eq!(back, sample());
        assert_eq!(rest, b"ciphertext");
    }

    #[test]
    fn a_wrong_version_or_type_is_refused() {
        let mut bytes = encode_composite(&sample());
        bytes[0] = 0x02;
        assert_eq!(decode_composite(&bytes), Err(DecodeError::UnknownVersion));
        let mut bytes = encode_composite(&sample());
        bytes[1] = 0x02;
        assert_eq!(decode_composite(&bytes), Err(DecodeError::WrongType));
    }

    #[test]
    fn a_truncated_header_is_refused_rather_than_read_short() {
        let bytes = encode_composite(&sample());
        for cut in 0..COMPOSITE_LEN {
            assert_eq!(
                decode_composite(&bytes[..cut]),
                Err(DecodeError::TooShort),
                "cut at {cut}"
            );
        }
    }

    #[test]
    fn an_unknown_agreement_type_is_refused() {
        // 0x06 would be Ct1Ack in the published enumeration. No state produces
        // it, so a peer sending one is a fault rather than a no-op.
        let mut bytes = encode_composite(&sample());
        bytes[66] = 0x06;
        assert_eq!(decode_composite(&bytes), Err(DecodeError::WrongType));
    }

    /// The width does not depend on whether a codeword is there.
    ///
    /// This is what the presence byte buys and it is worth keeping: a header is
    /// always `COMPOSITE_LEN` bytes, so nothing downstream has to parse to know
    /// how far the ciphertext starts.
    #[test]
    fn the_width_is_the_same_with_and_without_a_codeword() {
        let with = encode_composite(&sample());
        let mut without = sample();
        without.ag_chunk = None;
        assert_eq!(encode_composite(&without).len(), with.len());
        assert_eq!(with.len(), COMPOSITE_LEN);
    }

    /// Clearing the presence byte without clearing the codeword is refused.
    ///
    /// The width is independent of the value; accepting two spellings of one
    /// header is a separate thing and is not wanted. The module opens by saying
    /// there
    /// is exactly one valid spelling of a message, and this is the decoder
    /// making that true rather than the encoder merely happening to.
    #[test]
    fn a_cleared_presence_byte_over_a_live_codeword_is_refused() {
        let mut bytes = encode_composite(&sample());
        bytes[67] = 0x00;
        assert_eq!(decode_composite(&bytes), Err(DecodeError::LengthOverrun));
    }

    /// Absent means the whole field is zero, not merely that the flag is.
    #[test]
    fn absent_requires_canonical_padding() {
        let mut without = sample();
        without.ag_chunk = None;
        let canonical = encode_composite(&without);
        assert!(decode_composite(&canonical).is_ok());

        // A single set bit anywhere in the unused field is enough to refuse.
        for at in [68, 69, 70, 70 + CHUNK_BYTES - 1] {
            let mut bytes = canonical.clone();
            bytes[at] = 0x01;
            assert_eq!(
                decode_composite(&bytes),
                Err(DecodeError::LengthOverrun),
                "byte {at} was ignored"
            );
        }
    }

    /// The presence byte is a flag, so only its two values are a flag.
    #[test]
    fn a_presence_byte_that_is_neither_zero_nor_one_is_refused() {
        for present in [0x02u8, 0x7f, 0x80, 0xff] {
            let mut bytes = encode_composite(&sample());
            bytes[67] = present;
            assert_eq!(
                decode_composite(&bytes),
                Err(DecodeError::WrongType),
                "presence byte {present:#04x} was accepted"
            );
        }
    }

    /// Every accepted byte string re-encodes to itself.
    ///
    /// The direction the existing round-trip theorem does not cover. That one
    /// says `decode(encode(h)) = h`, which only ever asks about bytes the
    /// encoder produced. This asks the question canonicality actually turns on:
    /// of the byte strings the *decoder* accepts, is each one the encoding of
    /// what it decoded to?
    #[test]
    fn everything_accepted_re_encodes_to_itself() {
        let mut cases = vec![encode_composite(&sample())];
        let mut without = sample();
        without.ag_chunk = None;
        cases.push(encode_composite(&without));

        // Plus a spread of mutations, most of which are refused. The ones that
        // are accepted must be canonical.
        let base = encode_composite(&sample());
        for at in 0..base.len() {
            for bit in [0x01u8, 0x80] {
                let mut bytes = base.clone();
                bytes[at] ^= bit;
                cases.push(bytes);
            }
        }

        let mut accepted = 0usize;
        for bytes in cases {
            if let Ok((header, rest)) = decode_composite(&bytes) {
                assert!(rest.is_empty());
                assert_eq!(
                    encode_composite(&header),
                    bytes,
                    "an accepted byte string is not the encoding of what it decoded to"
                );
                accepted += 1;
            }
        }
        assert!(
            accepted > 2,
            "the mutations refused everything, so this proves nothing"
        );
    }
}
