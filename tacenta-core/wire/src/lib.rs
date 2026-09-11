//! The composite header on the wire, the decoders every message a peer sends
//! goes through first (`decode_message` for a ratchet message and
//! `decode_initial` for an initial (prekey) message), and the prekey bundle's
//! encoding (`decode_bundle`).
//!
//! Written from tacenta-spec/protocol/triple-ratchet.md and the model in
//! `Model.CompositeHeader`, whose round-trip is proved in
//! `Proofs.Serialization.decode_encode_composite`.
//!
//! ## Why this is a crate of its own
//!
//! These bytes are the most exposed input in the engine: `decode_message` runs on
//! every ratchet message before anything is authenticated, and what it returns
//! selects the ratchet keys the message is tried against. Until this crate
//! existed the decoder lived in the root crate's `serialization` module, which the
//! Charon/Aeneas translation does not cover, so nothing proved about the ratchets
//! began at the bytes a message arrived as. Isolated here, with no dependencies,
//! it is translated and proved like the other verified zones. The root crate
//! re-exports everything under `tacenta_core::serialization`, so no caller's path
//! changed and neither did a byte on the wire.
//!
//! A published prekey bundle is decoded here too. It is not a message, but a
//! sender decodes one fetched from a directory it does not control before any
//! session exists, so it is as exposed as the messages are.
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
//! [`COMPOSITE_LEN`] bytes of header on every message, against the Double
//! Ratchet's forty-two. The specification says the composition costs bandwidth
//! and that the sparse agreement exists to keep it affordable; this is the
//! number.

// Early returns here are spelled as `if`/`match` and `return`, not `?`: see
// tacenta-ratchet's module doc ("The `?` operator") for what is and is not known
// to translate.
#![allow(clippy::question_mark)]
#![forbid(unsafe_code)]

/// The message version byte. **Wire-sensitive** (message-format.md).
pub const VERSION: u8 = 0x01;

/// Message type: a ratchet message. **Wire-sensitive.**
pub const TYPE_RATCHET: u8 = 0x01;

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
        if index != 0 || or_bytes(bytes, 70, CHUNK_BYTES) != 0 {
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

/// Every byte of `bytes[from..from + len]` ORed together: zero exactly when the
/// whole range is zero.
///
/// A loop with no early exit rather than `iter().any(|b| *b != 0)`, because the
/// Charon/Aeneas translation does not model closures, and a loop whose body is
/// one assignment is the shape its proofs step through. The caller has already
/// checked that the range is inside `bytes`.
fn or_bytes(bytes: &[u8], from: usize, len: usize) -> u8 {
    let mut acc = 0u8;
    let mut i = 0;
    while i < len {
        acc |= bytes[from + i];
        i += 1;
    }
    acc
}

fn be64_at(bytes: &[u8], at: usize) -> u64 {
    let mut a = [0u8; 8];
    a.copy_from_slice(&bytes[at..at + 8]);
    u64::from_be_bytes(a)
}

/// A decoded ratchet message.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DecodedMessage {
    pub header: Composite,
    pub ciphertext: Vec<u8>,
}

/// Parse a ratchet message, rejecting anything that is not canonical.
///
/// The header is a composite one: both ratchets' state and the agreement's
/// message, in one structure. `decode_composite` returns the bytes that
/// followed it, which are the ciphertext.
pub fn decode_message(bytes: &[u8]) -> Result<DecodedMessage, DecodeError> {
    // A `match` rather than `?` and a tuple pattern: the translation of either
    // is a pure destructuring `let` that the proofs cannot step through.
    match decode_composite(bytes) {
        Ok(parsed) => Ok(DecodedMessage {
            header: parsed.0,
            ciphertext: parsed.1.to_vec(),
        }),
        Err(e) => Err(e),
    }
}

/// Message type: an initial (prekey) message. **Wire-sensitive.**
pub const TYPE_INITIAL: u8 = 0x02;

/// The width of an `EncodeEC` public key: a curve type byte and 32 bytes.
const EC_LEN: usize = 33;

/// The `EncodeEC` curve byte, the first byte of an initial message's `identity`
/// and `ephemeral`. **Wire-sensitive** (tacenta-spec/CONSTANTS.md, `EncodeEC`
/// type byte).
///
/// The same value as `tacenta_session::ENCODE_EC_CURVE25519`, repeated rather
/// than imported, as `CHUNK_BYTES` is, because this crate has no dependencies.
/// A key that does not begin with it is not an `EncodeEC` form, and
/// `decode_initial` refuses it (message-format.md, Initial message).
const ENCODE_EC_CURVE25519: u8 = 0x05;

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

/// Where the `n` bytes starting at `at` end, if they fit inside `bytes`, and
/// nothing otherwise.
///
/// **The checked addition is the point of this function.** A decoder reads a
/// four-byte length off the wire and casts it to `usize`. On a 64-bit target
/// `at + n` cannot overflow, because `u32::MAX` plus a small offset is nowhere
/// near the top of the range, and the length check catches it. On a 32-bit
/// target it can: `u32::MAX as usize` plus any nonzero offset wraps, a debug
/// build panics on the addition, and a release build wraps to a small number,
/// passes the length check, and panics on the slice instead. The crate builds
/// for `armv7-linux-androideabi`, so that target is not hypothetical. An
/// addition that overflows is refused the same way as a field that does not
/// fit, because a length too large to add is the same failure as one too large
/// to fit.
// Spelled as a `match` rather than `checked_add(n).filter(..)`, which is what
// clippy asks for: the translation does not model closures.
#[allow(clippy::manual_filter)]
fn span_end(bytes: &[u8], at: usize, n: usize) -> Option<usize> {
    match at.checked_add(n) {
        Some(end) => {
            if end <= bytes.len() {
                Some(end)
            } else {
                None
            }
        }
        None => None,
    }
}

/// Four big-endian bytes at `at`. The caller has already checked they fit.
fn be32_at(bytes: &[u8], at: usize) -> u32 {
    u32::from_be_bytes([bytes[at], bytes[at + 1], bytes[at + 2], bytes[at + 3]])
}

/// Parse an initial (prekey) message. `identity` and `ephemeral` are 33 bytes
/// each (a type byte and a curve public key); the KEM ciphertext is
/// length-prefixed; then three prekey identifiers; then the ratchet message.
///
/// A fixed-width field that does not fit is `TooShort`; the KEM ciphertext's
/// length came off the wire, so a ciphertext that does not fit is
/// `LengthOverrun`. An `identity` or `ephemeral` whose first byte is not
/// `ENCODE_EC_CURVE25519` is not an `EncodeEC` form and is `WrongType`,
/// checked once both keys are bounded (message-format.md, Initial message).
/// Each field's end is computed by `span_end` before anything is read, and
/// every read is at a position that check has already bounded.
pub fn decode_initial(bytes: &[u8]) -> Result<DecodedInitial, DecodeError> {
    if bytes.len() < 2 {
        return Err(DecodeError::TooShort);
    }
    if bytes[0] != VERSION {
        return Err(DecodeError::UnknownVersion);
    }
    if bytes[1] != TYPE_INITIAL {
        return Err(DecodeError::WrongType);
    }
    let identity_end = match span_end(bytes, 2, EC_LEN) {
        Some(end) => end,
        None => return Err(DecodeError::TooShort),
    };
    let ephemeral_end = match span_end(bytes, identity_end, EC_LEN) {
        Some(end) => end,
        None => return Err(DecodeError::TooShort),
    };
    // Both keys are bounded, so each first byte is inside the input. A key
    // without the curve byte is not an `EncodeEC` form, whatever follows it.
    if bytes[2] != ENCODE_EC_CURVE25519 {
        return Err(DecodeError::WrongType);
    }
    if bytes[identity_end] != ENCODE_EC_CURVE25519 {
        return Err(DecodeError::WrongType);
    }
    let kem_len_end = match span_end(bytes, ephemeral_end, 4) {
        Some(end) => end,
        None => return Err(DecodeError::TooShort),
    };
    let kem_len = be32_at(bytes, ephemeral_end) as usize;
    let kem_end = match span_end(bytes, kem_len_end, kem_len) {
        Some(end) => end,
        None => return Err(DecodeError::LengthOverrun),
    };
    let signed_prekey_end = match span_end(bytes, kem_end, 4) {
        Some(end) => end,
        None => return Err(DecodeError::TooShort),
    };
    let one_time_prekey_end = match span_end(bytes, signed_prekey_end, 4) {
        Some(end) => end,
        None => return Err(DecodeError::TooShort),
    };
    let kem_prekey_end = match span_end(bytes, one_time_prekey_end, 4) {
        Some(end) => end,
        None => return Err(DecodeError::TooShort),
    };
    Ok(DecodedInitial {
        identity: bytes[2..identity_end].to_vec(),
        ephemeral: bytes[identity_end..ephemeral_end].to_vec(),
        kem_ciphertext: bytes[kem_len_end..kem_end].to_vec(),
        signed_prekey_id: be32_at(bytes, kem_end),
        one_time_prekey_id: be32_at(bytes, signed_prekey_end),
        kem_prekey_id: be32_at(bytes, one_time_prekey_end),
        message: bytes[kem_prekey_end..].to_vec(),
    })
}

/// Type byte for a published prekey bundle. **Wire-sensitive.**
///
/// A bundle is not a message and never travels as one, but it shares the
/// version and type framing so that a decoder given the wrong bytes says so
/// rather than misreading them. That is the same reason the two message types
/// are distinguished, and the reason costs one byte.
pub const TYPE_BUNDLE: u8 = 0x03;

/// Where a bundle's KEM prekey starts: the version and type bytes, the identity
/// key (32), the signed prekey (32) and its signature (64), and the KEM prekey's
/// four-byte length.
const BUNDLE_KEM_AT: usize = 134;

/// The length a bundle's KEM prekey must have: the ML-KEM-1024
/// encapsulation-key length, fixed by the FIPS 203 parameter set
/// (tacenta-spec/CONSTANTS.md, Bundle KEM prekey length).
///
/// `decode_bundle` refuses any other length prefix as soon as it reads one,
/// whether or not that many bytes follow (message-format.md, Prekey bundle).
/// The prefix stays on the wire, so a bundle made under another parameter set
/// is refused at its length rather than read as this one's key.
const KEM_PREKEY_LEN: usize = 1568;

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

/// The one-time prekey's field at `at`: a presence byte, then thirty-two bytes
/// either way. The caller has already checked that all thirty-three fit.
///
/// A function of its own so that the decoder continues from one point. The
/// translation copies whatever follows a branch into every branch that does not
/// return early, so three outcomes decided inline would put the rest of the
/// decoder, and every proof about it, in twice.
fn one_time_prekey_at(bytes: &[u8], at: usize) -> Result<Option<[u8; 32]>, DecodeError> {
    let present = bytes[at];
    if present == 0x00 {
        // Absent means the whole field is zero, not merely that the flag is.
        //
        // Accepting any thirty-two bytes when the flag says absent would give
        // one bundle 2^256 other accepted spellings. The composite header
        // applies the same rule to its absent codeword; this is its sibling.
        //
        // It matters wherever a bundle is hashed, signed, cached or
        // deduplicated: two byte strings that mean one bundle are two entries,
        // two digests, and two chances for a cache to disagree with a verifier.
        if or_bytes(bytes, at + 1, 32) != 0 {
            return Err(DecodeError::LengthOverrun);
        }
        Ok(None)
    } else if present == 0x01 {
        let mut key = [0u8; 32];
        key.copy_from_slice(&bytes[at + 1..at + 33]);
        Ok(Some(key))
    } else {
        Err(DecodeError::WrongType)
    }
}

/// Parse a published prekey bundle. The inverse of [`encode_bundle`].
///
/// A sender runs this on bytes fetched from a directory it does not control,
/// before any session exists, so a bundle is as exposed as a message is.
///
/// Trailing bytes are rejected. A bundle is a whole object rather than a prefix
/// of a stream, so anything after the last field means these are not the bytes
/// they claim to be.
///
/// A fixed-width field that does not fit is `TooShort`; the KEM prekey's length
/// came off the wire, so a length other than `KEM_PREKEY_LEN`, or a key that
/// does not fit, is `LengthOverrun`. Every field is bounded by `span_end` or the
/// length check before anything is read.
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
    if bytes.len() < BUNDLE_KEM_AT {
        return Err(DecodeError::TooShort);
    }
    let kem_len = be32_at(bytes, 130) as usize;
    if kem_len != KEM_PREKEY_LEN {
        return Err(DecodeError::LengthOverrun);
    }
    let kem_end = match span_end(bytes, BUNDLE_KEM_AT, kem_len) {
        Some(end) => end,
        None => return Err(DecodeError::LengthOverrun),
    };
    let signature_end = match span_end(bytes, kem_end, 64) {
        Some(end) => end,
        None => return Err(DecodeError::TooShort),
    };
    // The presence byte and the thirty-two bytes after it.
    let key_end = match span_end(bytes, signature_end, 33) {
        Some(end) => end,
        None => return Err(DecodeError::TooShort),
    };
    let one_time_prekey = match one_time_prekey_at(bytes, signature_end) {
        Ok(key) => key,
        Err(e) => return Err(e),
    };
    let ids_end = match span_end(bytes, key_end, 12) {
        Some(end) => end,
        None => return Err(DecodeError::TooShort),
    };
    if ids_end != bytes.len() {
        return Err(DecodeError::LengthOverrun);
    }
    let mut identity_key = [0u8; 32];
    identity_key.copy_from_slice(&bytes[2..34]);
    let mut signed_prekey = [0u8; 32];
    signed_prekey.copy_from_slice(&bytes[34..66]);
    let mut signed_prekey_signature = [0u8; 64];
    signed_prekey_signature.copy_from_slice(&bytes[66..130]);
    let mut kem_prekey_signature = [0u8; 64];
    kem_prekey_signature.copy_from_slice(&bytes[kem_end..signature_end]);
    Ok(WireBundle {
        identity_key,
        signed_prekey,
        signed_prekey_signature,
        kem_prekey: bytes[BUNDLE_KEM_AT..kem_end].to_vec(),
        kem_prekey_signature,
        one_time_prekey,
        signed_prekey_id: be32_at(bytes, key_end),
        one_time_prekey_id: be32_at(bytes, key_end + 4),
        kem_prekey_id: be32_at(bytes, key_end + 8),
    })
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

    /// A span whose end cannot even be computed is refused, rather than wrapping
    /// into a small number that passes the bounds check.
    ///
    /// The decoder tests cannot reach this. They pass `u32::MAX`, which is what an
    /// attacker can actually write on the wire, and on a 64-bit host `u32::MAX`
    /// plus an offset is ordinary arithmetic the length check catches. On a
    /// 32-bit target the same input wraps: a debug build panics on the addition
    /// and a release build wraps to a small number, passes the check, and panics
    /// on the slice. So this goes at the helper directly, with a length that
    /// overflows on every target.
    #[test]
    fn a_span_that_cannot_be_added_is_refused_rather_than_wrapping() {
        let bytes = [0u8; 8];
        assert_eq!(span_end(&bytes, 2, usize::MAX), None);
        // The boundary itself: exactly enough to overflow by one.
        assert_eq!(span_end(&bytes, 1, usize::MAX), None);
        // And the ordinary cases either side of the end.
        assert_eq!(span_end(&bytes, 2, 6), Some(8));
        assert_eq!(span_end(&bytes, 2, 7), None);
    }

    /// An initial message with the given keys, an empty KEM ciphertext, three
    /// identifiers and no ratchet message. Built by hand: the encoder lives in
    /// the root crate.
    fn initial_with(identity: [u8; EC_LEN], ephemeral: [u8; EC_LEN]) -> Vec<u8> {
        let mut out = vec![VERSION, TYPE_INITIAL];
        out.extend_from_slice(&identity);
        out.extend_from_slice(&ephemeral);
        out.extend_from_slice(&0u32.to_be_bytes());
        out.extend_from_slice(&[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3]);
        out
    }

    fn ec_key(first: u8, fill: u8) -> [u8; EC_LEN] {
        let mut k = [fill; EC_LEN];
        k[0] = first;
        k
    }

    /// A key without the `EncodeEC` curve byte is refused at decode, in either
    /// position, although every length in the message is right.
    #[test]
    fn an_initial_key_without_the_curve_byte_is_refused() {
        let good = ec_key(ENCODE_EC_CURVE25519, 0x0a);
        let decoded = decode_initial(&initial_with(good, good)).unwrap();
        assert_eq!(decoded.identity, good.to_vec());
        assert_eq!(decoded.ephemeral, good.to_vec());

        for bad in [0x00u8, 0x04, 0x06, 0x08, 0xff] {
            let key = ec_key(bad, 0x0a);
            assert_eq!(
                decode_initial(&initial_with(key, good)),
                Err(DecodeError::WrongType),
                "an identity starting {bad:#04x} was accepted"
            );
            assert_eq!(
                decode_initial(&initial_with(good, key)),
                Err(DecodeError::WrongType),
                "an ephemeral starting {bad:#04x} was accepted"
            );
        }
    }

    fn bundle_with_kem(kem_prekey: Vec<u8>) -> WireBundle {
        WireBundle {
            identity_key: [0x11; 32],
            signed_prekey: [0x22; 32],
            signed_prekey_signature: [0x33; 64],
            kem_prekey,
            kem_prekey_signature: [0x55; 64],
            one_time_prekey: None,
            signed_prekey_id: 7,
            one_time_prekey_id: 0,
            kem_prekey_id: 9,
        }
    }

    /// A KEM prekey of any length but the encapsulation key's is refused,
    /// even when its length prefix is honest about the bytes that follow.
    #[test]
    fn a_bundle_kem_prekey_of_the_wrong_length_is_refused() {
        let good = bundle_with_kem(vec![0x44; KEM_PREKEY_LEN]);
        assert_eq!(decode_bundle(&encode_bundle(&good)), Ok(good));

        for len in [0, 1, KEM_PREKEY_LEN - 1, KEM_PREKEY_LEN + 1, 1184] {
            assert_eq!(
                decode_bundle(&encode_bundle(&bundle_with_kem(vec![0x44; len]))),
                Err(DecodeError::LengthOverrun),
                "a {len}-byte KEM prekey was accepted"
            );
        }
    }

    /// And a prefix that disagrees with a right-length key is refused on the
    /// prefix, before the bytes are looked at.
    #[test]
    fn a_bundle_kem_length_prefix_other_than_the_key_length_is_refused() {
        let canonical = encode_bundle(&bundle_with_kem(vec![0x44; KEM_PREKEY_LEN]));
        for len in [KEM_PREKEY_LEN as u32 - 1, KEM_PREKEY_LEN as u32 + 1] {
            let mut bytes = canonical.clone();
            bytes[130..134].copy_from_slice(&len.to_be_bytes());
            assert_eq!(decode_bundle(&bytes), Err(DecodeError::LengthOverrun));
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
