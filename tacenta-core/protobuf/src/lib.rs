//! A bounded protobuf reader for one named wire profile.
//!
//! **Not a general protobuf implementation.** It reads the bounded profile for
//! the two message types this engine supports, within declared limits, and
//! refuses everything else. A general implementation would be a
//! larger trusted surface than the protocol it serves.
//!
//! ## Why this is inside the verified core
//!
//! An attacker chooses these bytes. The fields parsed here select ratchet keys
//! and drive state transitions, the authenticator covers the exact serialized
//! header, and re-encoding can change what was authenticated. Leaving it outside
//! would cut refinement at the most exposed boundary in the engine.
//!
//! ## Shape rules this crate obeys
//!
//! Total functions, checked arithmetic, explicit errors, no panics, no `unsafe`,
//! no closures, no traits beyond what the translation models, and no unbounded
//! work. Owned bytes rather than a zero-copy lifetime design: the proof comes
//! first and the optimisation second, if ever.

// `?` appears here only on a `Result` whose error type is this function's own,
// the one shape known to translate; the remaining early returns are spelled as
// `match`, and the lint that asks to rewrite those as `?` stays off because
// what it asks for is not uniformly known to translate. See tacenta-ratchet's
// module doc ("The `?` operator") for what is and is not known.
#![allow(clippy::question_mark)]
#![forbid(unsafe_code)]

/// The largest message this profile accepts, in bytes.
///
/// An outer limit checked before anything else is read. Every bound below is
/// smaller, so no accepted input can drive work beyond this.
pub const MAX_MESSAGE_LEN: usize = 16384;

/// The largest field number this profile knows. Anything above is refused
/// rather than skipped: unknown fields are not part of the profile, and
/// accepting them would mean accepting bytes whose meaning we do not define.
pub const MAX_FIELD_NUMBER: u32 = 15;

/// The most fields a message may carry, so a stream of empty fields cannot make
/// a parser work indefinitely inside the length limit.
pub const MAX_FIELDS: usize = 32;

/// A varint is at most this many bytes in this profile. Ten would admit a full
/// `u64`; five admits `u32`, which is every varint the profile carries, and a
/// shorter bound is a smaller loop to reason about.
pub const MAX_VARINT_BYTES: usize = 5;

/// Why a byte string is not a message of this profile.
///
/// Coarse on purpose. A parser that reports precisely where it stopped tells an
/// attacker where it stopped.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ProtoError {
    /// Over `MAX_MESSAGE_LEN`, a length past the end, too many fields, or bytes left.
    TooLong,
    /// Ended inside a varint, or a required field never appeared.
    Truncated,
    /// A varint longer than `MAX_VARINT_BYTES`, not minimally encoded, or with a
    /// value that does not fit 32 bits.
    BadVarint,
    /// A wire type or field number outside the profile.
    NotInProfile,
    /// A field appeared twice where the profile allows one.
    Duplicate,
}

/// A protobuf wire type, restricted to the two this profile uses.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WireType {
    Varint,
    LengthDelimited,
}

/// A cursor over the input, carrying the checked position.
///
/// A struct rather than a pair of arguments because the translation models a
/// struct cleanly and every function here needs both halves.
/// A tag: which field, and how it is encoded.
///
/// A named pair rather than a tuple. A tuple reaches the translation as
/// `let (a, b) := p`
/// wherever it is used, and no stepping tactic will enter that; a struct
/// reaches it as projections, which they handle. The arithmetic was never the
/// obstacle, the form was.
#[derive(Debug, PartialEq, Eq)]
pub struct Tag {
    pub field: u32,
    pub wire: WireType,
}

pub struct Reader {
    /// The bytes, owned. See the module note on zero-copy.
    pub bytes: Vec<u8>,
    /// How far in. Only ever advanced through the checked helpers below.
    pub at: usize,
}

impl Reader {
    /// Start reading, refusing anything past the outer limit before a single
    /// byte is examined.
    pub fn new(bytes: Vec<u8>) -> Result<Reader, ProtoError> {
        if bytes.len() > MAX_MESSAGE_LEN {
            return Err(ProtoError::TooLong);
        }
        Ok(Reader { bytes, at: 0 })
    }

    /// Bytes left. Total: `at` never exceeds `bytes.len()`, which every
    /// advance below preserves.
    pub fn remaining(&self) -> usize {
        if self.at > self.bytes.len() {
            0
        } else {
            self.bytes.len() - self.at
        }
    }

    /// One byte, or `Truncated`.
    pub fn byte(&mut self) -> Result<u8, ProtoError> {
        if self.at >= self.bytes.len() {
            return Err(ProtoError::Truncated);
        }
        let b = self.bytes[self.at];
        match self.at.checked_add(1) {
            Some(next) => {
                self.at = next;
                Ok(b)
            }
            None => Err(ProtoError::TooLong),
        }
    }

    /// A varint, bounded and required to be minimally encoded.
    ///
    /// **The bounded loop is the hard shape**, and it is here deliberately: a
    /// fixed trip count with an early exit, no recursion, and checked shifts.
    /// Minimality is required because a non-minimal varint is a second spelling
    /// of one value, and this profile's authenticator covers exact bytes.
    /// **Multiplication rather than a shift, and that is a verification
    /// decision rather than a stylistic one.** `u32::checked_shl` reaches the
    /// translation as an axiom: Aeneas does not model it, so proving this
    /// function total through a shift would mean adding a trusted boundary at
    /// the most exposed parser in the engine, and asserting that the thing we
    /// most want proved returns.
    ///
    /// A varint is base-128 little-endian, so a running factor is the same
    /// arithmetic written in an operation the toolchain does model. The factor
    /// is itself checked, which is what bounds it without a separate guard on
    /// the exponent: once it would exceed the word, the multiply fails and the
    /// value was never one this profile can carry.
    pub fn varint(&mut self) -> Result<u32, ProtoError> {
        let mut value: u32 = 0;
        let mut factor: u32 = 1;
        let mut taken: usize = 0;

        while taken < MAX_VARINT_BYTES {
            let b = self.byte()?;
            // `% 128` rather than `& 0x7f`, and `< 128` rather than a mask test
            // below: a varint byte's low seven bits are its value modulo 128 and its
            // continuation bit is whether it reaches 128. Both are the definition
            // rather than a substitute, and both are arithmetic the verification
            // toolchain reasons about directly where a bit mask is not.
            let low = (b % 128) as u32;

            match low.checked_mul(factor) {
                Some(part) => match value.checked_add(part) {
                    Some(v) => value = v,
                    None => return Err(ProtoError::BadVarint),
                },
                None => return Err(ProtoError::BadVarint),
            }

            taken += 1;

            if b < 128 {
                // Minimal encoding: a trailing byte contributing nothing is
                // padding, and padding is a second spelling of one value, which
                // an authenticator over exact bytes cannot tolerate.
                //
                // The test is on `factor` rather than on `taken`, and the two
                // are the same test: the place value is one exactly on the first
                // byte. Saying it this way keeps `taken` as nothing but the loop
                // bound, which is what lets the verification relate this loop to
                // its specification without carrying `factor == 128^taken`
                // alongside.
                if factor > 1 && b == 0x00 {
                    return Err(ProtoError::BadVarint);
                }
                return Ok(value);
            }

            // The next byte is worth 128 times this one. When that would leave
            // the word, no further byte can contribute and the input is not a
            // varint of this profile.
            match factor.checked_mul(128) {
                Some(f) => factor = f,
                None => return Err(ProtoError::BadVarint),
            }
        }
        Err(ProtoError::BadVarint)
    }

    /// A tag: its field number and wire type, both inside the profile.
    ///
    /// Two functions rather than one, and the split is for the proofs. Reading
    /// and interpreting were together, and a totality proof then had to carry
    /// the varint loop through every branch of the interpretation, which
    /// exhausted the elaborator rather than being hard. Separated, each half is
    /// provable on its own and this one composes them.
    pub fn tag(&mut self) -> Result<Tag, ProtoError> {
        let raw = self.varint()?;
        decode_tag(raw)
    }

    /// A length-delimited field's bytes, copied out.
    ///
    /// The length is attacker-chosen, so the addition is checked and the result
    /// is compared against what is actually present before anything is
    /// allocated. That ordering is the whole of the boundedness property: the
    /// allocation below can never exceed what was already received.
    pub fn length_delimited(&mut self) -> Result<Vec<u8>, ProtoError> {
        let len = self.varint()? as usize;

        // Ask the question the specification asks -- is there that much left --
        // rather than whether the end falls outside the buffer. The two are the
        // same only while the cursor is inside the buffer, which is true, but is
        // a fact about every other method rather than about this one. Asking
        // the specification's question keeps the code and the model refusing
        // the same inputs whether or not that invariant holds.
        if len > self.remaining() {
            return Err(ProtoError::TooLong);
        }

        // Cannot overflow after the line above. Checked anyway: an addition that
        // is total only because of an earlier line is one refactor from not.
        let end = match self.at.checked_add(len) {
            Some(e) => e,
            None => return Err(ProtoError::TooLong),
        };
        let mut out: Vec<u8> = Vec::new();
        let mut i = self.at;
        while i < end {
            out.push(self.bytes[i]);
            i += 1;
        }
        self.at = end;
        Ok(out)
    }
}

/// The field numbers seen so far while parsing one message.
///
/// A message-level property rather than a field-level one, which is why it is
/// its own type rather than a counter inside `Reader`. `MAX_FIELDS` and
/// `ProtoError::Duplicate` are enforced here: `admit` reads the limit and
/// constructs the error, so the profile's own bounds are checked rather than
/// merely declared.
///
/// Why refuse a duplicate rather than take the last, which is what a tolerant
/// protobuf decoder does: two spellings of one message are two byte strings an
/// authenticator must agree about, and "take the last" makes the meaning depend
/// on decoder order rather than on the bytes.
pub struct FieldSet {
    seen: Vec<u32>,
}

impl Default for FieldSet {
    fn default() -> Self {
        Self::new()
    }
}

impl FieldSet {
    /// No fields seen.
    pub fn new() -> FieldSet {
        FieldSet { seen: Vec::new() }
    }

    /// Whether a field number has already been recorded.
    ///
    /// Split from `admit` for the reason `decode_tag` was split from `tag`: two
    /// short functions with a proof each, rather than one whose totality proof
    /// carries a loop through every branch of a decision.
    pub fn contains(&self, field: u32) -> bool {
        let mut i: usize = 0;
        while i < self.seen.len() {
            if self.seen[i] == field {
                return true;
            }
            i += 1;
        }
        false
    }

    /// Record a field number, refusing a repeat and refusing more fields than
    /// the profile carries.
    ///
    /// Returns the refusal rather than a `Result`, so the call is a two-wide
    /// direct bind in the translation. `&mut self` is not a problem for the
    /// translation: a call binds directly and the stepping tactic handles it.
    /// What the translation cannot handle is wide *joins* -- eight mutable
    /// locals would mean every branch of the parse loop returned a seven-wide
    /// tuple, and Charon binds those with a pure `let (a, b, ..) := x` that no
    /// tactic enters. That is answered by one state struct in the caller, not
    /// by this signature.
    ///
    /// Both refusals happen before anything is written, so **a refused set is
    /// unchanged**. That is the candidate-state property, proved
    /// rather than asserted: see `admit_refines`.
    pub fn admit(&mut self, field: u32) -> Option<ProtoError> {
        if self.contains(field) {
            return Some(ProtoError::Duplicate);
        }
        if self.seen.len() >= MAX_FIELDS {
            return Some(ProtoError::TooLong);
        }
        self.seen.push(field);
        None
    }
}

/// Interpret a tag value: a field number and a wire type, both inside the
/// profile.
///
/// Pure arithmetic on a value already read, which is what makes it provable
/// without the reader underneath it. Division and remainder rather than a shift
/// and a mask, for the reason given on `varint`: a tag *is* a field number times
/// eight plus a three-bit wire type, so this is the definition rather than a
/// substitute for it.
pub fn decode_tag(raw: u32) -> Result<Tag, ProtoError> {
    let field = raw / 8;
    let wire = raw % 8;
    if field == 0 || field > MAX_FIELD_NUMBER {
        return Err(ProtoError::NotInProfile);
    }
    // `if` rather than `match` on the scalar. A match on integer literals
    // translates to a form the elaborator case-splits expensively, and this
    // function is otherwise three comparisons. Same shape rule as the shift and
    // the tag split above: the arithmetic is not the difficulty, the form is.
    if wire == 0 {
        Ok(Tag {
            field,
            wire: WireType::Varint,
        })
    } else if wire == 2 {
        Ok(Tag {
            field,
            wire: WireType::LengthDelimited,
        })
    } else {
        Err(ProtoError::NotInProfile)
    }
}

/// A prekey envelope's protobuf region, parsed.
///
/// Eight fields, numbered as in the external interoperability profile
/// (`tacenta-spec/CONSTANTS.md`). Field names are this crate's own, chosen for
/// what each field carries; only the field numbers and wire types are the
/// profile's. Field 4 is a **nested ratchet message**, byte-identical in shape
/// to a standalone one. It is carried here as bytes and not parsed, because the
/// authenticator inside it covers those bytes and re-encoding them to check
/// would verify a different byte string.
///
/// An envelope has **no trailing authenticator**: the protobuf region runs to
/// the end. That is the one structural difference from a ratchet message and it
/// decides where a caller slices.
pub struct PrekeyBody {
    /// Field 1, and **the only optional field in either message type**. Absent
    /// means omitted entirely, not zero-filled: a bundle with no one-time
    /// prekey produces a message without the field, and it still establishes.
    pub prekey_id: Option<u32>,
    pub base_key: Vec<u8>,
    pub identity_key: Vec<u8>,
    pub message: Vec<u8>,
    pub registration_id: u32,
    pub signed_prekey_id: u32,
    pub pq_prekey_id: u32,
    pub kem: Vec<u8>,
}

pub const FIELD_PREKEY_ID: u32 = 1;
pub const FIELD_BASE_KEY: u32 = 2;
pub const FIELD_IDENTITY_KEY: u32 = 3;
pub const FIELD_MESSAGE: u32 = 4;
pub const FIELD_REGISTRATION_ID: u32 = 5;
pub const FIELD_SIGNED_PREKEY_ID: u32 = 6;
pub const FIELD_PQ_PREKEY_ID: u32 = 7;
pub const FIELD_KEM: u32 = 8;

/// One turn of the envelope parse.
pub struct EnvelopeParse {
    pub reader: Reader,
    pub seen: FieldSet,
    pub body: PrekeyBody,
    pub error: Option<ProtoError>,
}

/// Read one envelope field into the state.
pub fn one_envelope_field(mut st: EnvelopeParse) -> EnvelopeParse {
    let t = match st.reader.tag() {
        Ok(t) => t,
        Err(e) => {
            st.error = Some(e);
            return st;
        }
    };

    if let Some(e) = st.seen.admit(t.field) {
        st.error = Some(e);
        return st;
    }

    // A flat chain rather than `let want_bytes = a || b || c`. Aeneas translates
    // an `||` over comparisons into a *proposition* -- `t.field = FIELD_KEM`,
    // not a bool -- and the generated file then fails to typecheck for want of
    // a `Decidable` instance. The chain below says the same thing in a form
    // that translates, and it is the same shape `one_field` already uses.
    if t.field == FIELD_BASE_KEY {
        if !matches!(t.wire, WireType::LengthDelimited) {
            st.error = Some(ProtoError::NotInProfile);
            return st;
        }
        match st.reader.length_delimited() {
            Ok(v) => st.body.base_key = v,
            Err(e) => st.error = Some(e),
        }
    } else if t.field == FIELD_IDENTITY_KEY {
        if !matches!(t.wire, WireType::LengthDelimited) {
            st.error = Some(ProtoError::NotInProfile);
            return st;
        }
        match st.reader.length_delimited() {
            Ok(v) => st.body.identity_key = v,
            Err(e) => st.error = Some(e),
        }
    } else if t.field == FIELD_MESSAGE {
        if !matches!(t.wire, WireType::LengthDelimited) {
            st.error = Some(ProtoError::NotInProfile);
            return st;
        }
        match st.reader.length_delimited() {
            Ok(v) => st.body.message = v,
            Err(e) => st.error = Some(e),
        }
    } else if t.field == FIELD_KEM {
        if !matches!(t.wire, WireType::LengthDelimited) {
            st.error = Some(ProtoError::NotInProfile);
            return st;
        }
        match st.reader.length_delimited() {
            Ok(v) => st.body.kem = v,
            Err(e) => st.error = Some(e),
        }
    } else if t.field == FIELD_PREKEY_ID {
        if !matches!(t.wire, WireType::Varint) {
            st.error = Some(ProtoError::NotInProfile);
            return st;
        }
        match st.reader.varint() {
            Ok(v) => st.body.prekey_id = Some(v),
            Err(e) => st.error = Some(e),
        }
    } else if t.field == FIELD_REGISTRATION_ID {
        if !matches!(t.wire, WireType::Varint) {
            st.error = Some(ProtoError::NotInProfile);
            return st;
        }
        match st.reader.varint() {
            Ok(v) => st.body.registration_id = v,
            Err(e) => st.error = Some(e),
        }
    } else if t.field == FIELD_SIGNED_PREKEY_ID {
        if !matches!(t.wire, WireType::Varint) {
            st.error = Some(ProtoError::NotInProfile);
            return st;
        }
        match st.reader.varint() {
            Ok(v) => st.body.signed_prekey_id = v,
            Err(e) => st.error = Some(e),
        }
    } else if t.field == FIELD_PQ_PREKEY_ID {
        if !matches!(t.wire, WireType::Varint) {
            st.error = Some(ProtoError::NotInProfile);
            return st;
        }
        match st.reader.varint() {
            Ok(v) => st.body.pq_prekey_id = v,
            Err(e) => st.error = Some(e),
        }
    } else {
        st.error = Some(ProtoError::NotInProfile);
    }

    st
}

/// Parse the protobuf region of a prekey envelope.
pub fn parse_prekey_body(bytes: Vec<u8>) -> Result<PrekeyBody, ProtoError> {
    let reader = match Reader::new(bytes) {
        Ok(r) => r,
        Err(e) => return Err(e),
    };

    let mut st = EnvelopeParse {
        reader,
        seen: FieldSet::new(),
        body: PrekeyBody {
            prekey_id: None,
            base_key: Vec::new(),
            identity_key: Vec::new(),
            message: Vec::new(),
            registration_id: 0,
            signed_prekey_id: 0,
            pq_prekey_id: 0,
            kem: Vec::new(),
        },
        error: None,
    };

    let mut turns: usize = 0;
    while turns < MAX_FIELDS && st.error.is_none() && st.reader.remaining() > 0 {
        st = one_envelope_field(st);
        turns += 1;
    }

    if let Some(e) = st.error {
        return Err(e);
    }
    if st.reader.remaining() > 0 {
        return Err(ProtoError::TooLong);
    }

    // Field 1 is deliberately absent from this list: the external profile
    // omits it from well-formed messages, so requiring it would refuse
    // messages that are well formed under the profile.
    if !st.seen.contains(FIELD_BASE_KEY)
        || !st.seen.contains(FIELD_IDENTITY_KEY)
        || !st.seen.contains(FIELD_MESSAGE)
        || !st.seen.contains(FIELD_REGISTRATION_ID)
        || !st.seen.contains(FIELD_SIGNED_PREKEY_ID)
        || !st.seen.contains(FIELD_PQ_PREKEY_ID)
        || !st.seen.contains(FIELD_KEM)
    {
        return Err(ProtoError::Truncated);
    }

    Ok(st.body)
}

/// A varint being emitted: the bytes so far, what is left of the value, whether
/// the last byte has been written, and any refusal.
///
/// A state struct and a step function, for the reason the parser needed them:
/// Aeneas has no early return inside a loop, and a loop with several mutable
/// locals joins its branches into a tuple no stepping tactic will enter.
pub struct VarintOut {
    pub bytes: Vec<u8>,
    pub value: u32,
    pub done: bool,
    pub error: Option<ProtoError>,
}

/// Append one byte, refusing to grow past the profile's outer limit.
///
/// **The writer is bounded because the reader is.** A `Vec` push can fail at the
/// allocator, so an encoder that pushed unconditionally would be total only
/// because of a fact about its callers -- a shape this repository avoids.
/// Refusing at `MAX_MESSAGE_LEN` makes it total on its
/// own terms, and refuses exactly what the reader would refuse to read back.
pub fn push_bounded(mut bytes: Vec<u8>, b: u8) -> Result<Vec<u8>, ProtoError> {
    if bytes.len() >= MAX_MESSAGE_LEN {
        return Err(ProtoError::TooLong);
    }
    bytes.push(b);
    Ok(bytes)
}

/// Write one byte of a varint.
pub fn varint_step(mut st: VarintOut) -> VarintOut {
    let low = (st.value % 128) as u8;
    let rest = st.value / 128;
    // The continuation bit is `+ 128` rather than `| 0x80`: the byte is below
    // 128 already, so this is addition, and addition is what the verification
    // reasons about. Same rule as `% 128` in the reader.
    let b = if rest == 0 { low } else { low + 128 };
    match push_bounded(st.bytes, b) {
        Ok(next) => {
            st.bytes = next;
            if rest == 0 {
                st.done = true;
            } else {
                st.value = rest;
            }
        }
        Err(e) => {
            st.bytes = Vec::new();
            st.error = Some(e);
        }
    }
    st
}

/// Emit a varint, minimally, appending to `bytes`.
///
/// Minimal by construction: the loop stops as soon as nothing is left, so no
/// trailing zero byte is ever written. That is not a nicety. This profile's
/// authenticator covers exact bytes, so a second spelling of one value is a
/// second message that means the same thing, and the decoder refuses one.
pub fn encode_varint(bytes: Vec<u8>, value: u32) -> Result<Vec<u8>, ProtoError> {
    let mut st = VarintOut {
        bytes,
        value,
        done: false,
        error: None,
    };
    let mut turns: usize = 0;
    while turns < MAX_VARINT_BYTES && !st.done && st.error.is_none() {
        st = varint_step(st);
        turns += 1;
    }
    match st.error {
        Some(e) => Err(e),
        None => Ok(st.bytes),
    }
}

/// The wire type's three-bit code.
///
/// Its own function, and that is the whole reason it exists. Inline, the enum
/// test reaches the translation as a `match` inside a bind that the stepping
/// tactics will not enter and the case-splitters will not eliminate; as a call
/// it is an ordinary value. Splitting a function to make its proof one line is
/// a pattern this crate uses throughout.
pub fn wire_code(wire: WireType) -> u32 {
    if matches!(wire, WireType::Varint) {
        0
    } else {
        2
    }
}

/// Emit a tag: field times eight plus wire type. The field is not range-checked.
pub fn encode_tag(bytes: Vec<u8>, field: u32, wire: WireType) -> Result<Vec<u8>, ProtoError> {
    let w = wire_code(wire);
    match field.checked_mul(8) {
        Some(base) => match base.checked_add(w) {
            Some(raw) => encode_varint(bytes, raw),
            None => Err(ProtoError::NotInProfile),
        },
        None => Err(ProtoError::NotInProfile),
    }
}

/// A copy in progress, for the same reason `VarintOut` exists.
pub struct CopyOut {
    pub bytes: Vec<u8>,
    pub i: usize,
    pub error: Option<ProtoError>,
}

/// Copy one byte of a length-delimited field's value.
pub fn copy_step(mut st: CopyOut, value: &[u8]) -> CopyOut {
    if st.i >= value.len() {
        st.error = Some(ProtoError::Truncated);
        return st;
    }
    match push_bounded(st.bytes, value[st.i]) {
        Ok(next) => {
            st.bytes = next;
            st.i += 1;
        }
        Err(e) => {
            st.bytes = Vec::new();
            st.error = Some(e);
        }
    }
    st
}

/// Emit a length-delimited field: its length, then its bytes.
pub fn encode_length_delimited(bytes: Vec<u8>, value: &[u8]) -> Result<Vec<u8>, ProtoError> {
    if value.len() > MAX_MESSAGE_LEN {
        return Err(ProtoError::TooLong);
    }
    let with_len = match encode_varint(bytes, value.len() as u32) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let mut st = CopyOut {
        bytes: with_len,
        i: 0,
        error: None,
    };
    let mut turns: usize = 0;
    while turns < MAX_MESSAGE_LEN && st.i < value.len() && st.error.is_none() {
        st = copy_step(st, value);
        turns += 1;
    }
    match st.error {
        Some(e) => Err(e),
        None => Ok(st.bytes),
    }
}

/// Emit the protobuf region of a ratchet message.
///
/// Fields ascending, the order the external interoperability profile emits.
/// The profile's emitted order is a property of the encoder, not of the
/// format -- reordering is accepted -- so this is a choice about what we
/// produce and not a claim about what we must. Ours matches so that a
/// re-encoding of a message in the external profile is byte-identical to it.
/// The tests below cover the model and the code agreeing on synthetic input.
///
/// **That is not a canonicality property of the parser.** `parse_ratchet_body`
/// accepts fields in any order, and this emits them ascending, so for an
/// accepted input with its fields reordered `encode(parse(b)) != b`. Nothing
/// in the core checks an authenticator over re-encoded bytes today -- the
/// session layer's AEAD covers the composite header and the ciphertext it
/// received, not a re-emission -- and the day something does, the parser must
/// refuse non-ascending order first, or the two will disagree on exactly the
/// input an attacker would choose. `reordered_fields_parse_but_do_not_re_emit`
/// pins the current behaviour so the gap stays visible.
pub fn encode_ratchet_body(body: &RatchetBody) -> Result<Vec<u8>, ProtoError> {
    let out: Vec<u8> = Vec::new();
    let out = match encode_tag(out, FIELD_RATCHET_KEY, WireType::LengthDelimited) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_length_delimited(out, &body.ratchet_key) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_tag(out, FIELD_COUNTER, WireType::Varint) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_varint(out, body.counter) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_tag(out, FIELD_PREVIOUS_COUNTER, WireType::Varint) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_varint(out, body.previous_counter) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_tag(out, FIELD_CIPHERTEXT, WireType::LengthDelimited) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_length_delimited(out, &body.ciphertext) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_tag(out, FIELD_PQ, WireType::LengthDelimited) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    encode_length_delimited(out, &body.pq)
}

/// Emit the protobuf region of a prekey envelope.
///
/// Fields ascending, as the external profile emits them; re-encoding reproduces
/// only an ascending input, since a reader takes any order. Field 1 is emitted
/// **only when present**: a bundle with no one-time prekey produces a message
/// with the field omitted entirely rather than set to zero, as the external
/// profile does, and a zero would be a different byte string carrying a claim
/// nobody made.
pub fn encode_prekey_body(body: &PrekeyBody) -> Result<Vec<u8>, ProtoError> {
    let out: Vec<u8> = Vec::new();

    let out = match body.prekey_id {
        Some(id) => {
            let o = match encode_tag(out, FIELD_PREKEY_ID, WireType::Varint) {
                Ok(b) => b,
                Err(e) => return Err(e),
            };
            match encode_varint(o, id) {
                Ok(b) => b,
                Err(e) => return Err(e),
            }
        }
        None => out,
    };

    let out = match encode_tag(out, FIELD_BASE_KEY, WireType::LengthDelimited) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_length_delimited(out, &body.base_key) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_tag(out, FIELD_IDENTITY_KEY, WireType::LengthDelimited) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_length_delimited(out, &body.identity_key) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_tag(out, FIELD_MESSAGE, WireType::LengthDelimited) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_length_delimited(out, &body.message) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_tag(out, FIELD_REGISTRATION_ID, WireType::Varint) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_varint(out, body.registration_id) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_tag(out, FIELD_SIGNED_PREKEY_ID, WireType::Varint) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_varint(out, body.signed_prekey_id) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_tag(out, FIELD_PQ_PREKEY_ID, WireType::Varint) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_varint(out, body.pq_prekey_id) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    let out = match encode_tag(out, FIELD_KEM, WireType::LengthDelimited) {
        Ok(b) => b,
        Err(e) => return Err(e),
    };
    encode_length_delimited(out, &body.kem)
}

/// The exact bytes a field occupied, for a field whose authenticated form must
/// be the received one rather than a re-encoding.
///
/// **Raw-byte fidelity is a protocol requirement, not an optimisation.** The
/// authenticator covers what arrived; re-encoding and authenticating that would
/// verify a different byte string, and the two agree only while the encoder and
/// the sender agree, which is precisely what cannot be assumed of a peer.
pub struct Raw {
    pub start: usize,
    pub end: usize,
}

impl Raw {
    /// Copy the span out of the reader's buffer. Checked, and empty rather than
    /// panicking if the span is not inside the input.
    pub fn slice_of(&self, bytes: &[u8]) -> Result<Vec<u8>, ProtoError> {
        if self.start > self.end || self.end > bytes.len() {
            return Err(ProtoError::Truncated);
        }
        let mut out: Vec<u8> = Vec::new();
        let mut i = self.start;
        while i < self.end {
            out.push(bytes[i]);
            i += 1;
        }
        Ok(out)
    }
}

/// A ratchet message's protobuf region, parsed.
///
/// The five fields of the external interoperability profile
/// (`tacenta-spec/CONSTANTS.md`). Field names are this crate's own, chosen for
/// what each field carries; only the field numbers and wire types are the
/// profile's.
///
/// The version byte and the trailing authenticator are *not* handled here.
/// This parses the protobuf region a caller has already separated, because the
/// authenticator covers those bytes and deciding what a message means before
/// checking who wrote it is what the authentication boundary exists to
/// prevent.
pub struct RatchetBody {
    pub ratchet_key: Vec<u8>,
    pub counter: u32,
    pub previous_counter: u32,
    pub ciphertext: Vec<u8>,
    pub pq: Vec<u8>,
}

/// Field numbers of the ratchet message, as in the external interoperability
/// profile.
pub const FIELD_RATCHET_KEY: u32 = 1;
pub const FIELD_COUNTER: u32 = 2;
pub const FIELD_PREVIOUS_COUNTER: u32 = 3;
pub const FIELD_CIPHERTEXT: u32 = 4;
pub const FIELD_PQ: u32 = 5;

/// One turn of the parse: the reader, what it has produced, and any refusal.
///
/// A single struct rather than eight locals, and that is the whole reason the
/// parse is provable. Charon joins the branches of an `if`/`else` by returning
/// every local the branches may have written; with eight of them each join was
/// a seven-wide tuple bound by a pure `let (a, b, ..) := x`, which no stepping
/// tactic enters. With one struct each join is a single value.
pub struct Parse {
    pub reader: Reader,
    pub seen: FieldSet,
    pub ratchet_key: Vec<u8>,
    pub counter: u32,
    pub previous_counter: u32,
    pub ciphertext: Vec<u8>,
    pub pq: Vec<u8>,
    pub error: Option<ProtoError>,
}

/// Read one field into the state.
///
/// Its own function, not the loop's body, and that buys two things: the loop
/// body becomes a single call, and **early returns are legal again** -- Aeneas
/// forbids them inside a loop but not inside a function a loop calls. So the
/// refusals below read as refusals instead of as a nest of `else` branches.
pub fn one_field(mut st: Parse) -> Parse {
    let t = match st.reader.tag() {
        Ok(t) => t,
        Err(e) => {
            st.error = Some(e);
            return st;
        }
    };

    if let Some(e) = st.seen.admit(t.field) {
        st.error = Some(e);
        return st;
    }

    // A wire type that does not match the field's is refused rather than
    // skipped, for the same reason an unknown field number is: a byte string
    // whose meaning nobody has defined is not a message.
    if t.field == FIELD_RATCHET_KEY {
        if !matches!(t.wire, WireType::LengthDelimited) {
            st.error = Some(ProtoError::NotInProfile);
            return st;
        }
        match st.reader.length_delimited() {
            Ok(v) => st.ratchet_key = v,
            Err(e) => st.error = Some(e),
        }
    } else if t.field == FIELD_COUNTER {
        if !matches!(t.wire, WireType::Varint) {
            st.error = Some(ProtoError::NotInProfile);
            return st;
        }
        match st.reader.varint() {
            Ok(v) => st.counter = v,
            Err(e) => st.error = Some(e),
        }
    } else if t.field == FIELD_PREVIOUS_COUNTER {
        if !matches!(t.wire, WireType::Varint) {
            st.error = Some(ProtoError::NotInProfile);
            return st;
        }
        match st.reader.varint() {
            Ok(v) => st.previous_counter = v,
            Err(e) => st.error = Some(e),
        }
    } else if t.field == FIELD_CIPHERTEXT {
        if !matches!(t.wire, WireType::LengthDelimited) {
            st.error = Some(ProtoError::NotInProfile);
            return st;
        }
        match st.reader.length_delimited() {
            Ok(v) => st.ciphertext = v,
            Err(e) => st.error = Some(e),
        }
    } else if t.field == FIELD_PQ {
        if !matches!(t.wire, WireType::LengthDelimited) {
            st.error = Some(ProtoError::NotInProfile);
            return st;
        }
        match st.reader.length_delimited() {
            Ok(v) => st.pq = v,
            Err(e) => st.error = Some(e),
        }
    } else {
        st.error = Some(ProtoError::NotInProfile);
    }

    st
}

/// Parse the protobuf region of a ratchet message.
///
/// Field order is not required: the external profile's emitted order is a
/// property of the encoder, not of the format, so a parser that demanded it
/// would refuse messages that are well formed under the profile.
///
/// The loop is bounded by `MAX_FIELDS` rather than by the cursor. That makes it
/// terminate by construction instead of by an argument that reading a tag
/// always advances the cursor -- true, but a second thing to prove and a second
/// thing to keep true.
pub fn parse_ratchet_body(bytes: Vec<u8>) -> Result<RatchetBody, ProtoError> {
    let reader = match Reader::new(bytes) {
        Ok(r) => r,
        Err(e) => return Err(e),
    };

    let mut st = Parse {
        reader,
        seen: FieldSet::new(),
        ratchet_key: Vec::new(),
        counter: 0,
        previous_counter: 0,
        ciphertext: Vec::new(),
        pq: Vec::new(),
        error: None,
    };

    let mut turns: usize = 0;
    while turns < MAX_FIELDS && st.error.is_none() && st.reader.remaining() > 0 {
        st = one_field(st);
        turns += 1;
    }

    if let Some(e) = st.error {
        return Err(e);
    }

    // Unreachable once the loop ends without an error (a sixth field is refused
    // inside it), and kept so the format's rule is stated where it is enforced.
    if st.reader.remaining() > 0 {
        return Err(ProtoError::TooLong);
    }

    // No field of the ratchet message is omissible in the external profile;
    // only the prekey envelope's field 1 is optional. A
    // missing field here is refused rather than defaulted, because a default
    // is a value nobody sent.
    if !st.seen.contains(FIELD_RATCHET_KEY)
        || !st.seen.contains(FIELD_COUNTER)
        || !st.seen.contains(FIELD_PREVIOUS_COUNTER)
        || !st.seen.contains(FIELD_CIPHERTEXT)
        || !st.seen.contains(FIELD_PQ)
    {
        return Err(ProtoError::Truncated);
    }

    Ok(RatchetBody {
        ratchet_key: st.ratchet_key,
        counter: st.counter,
        previous_counter: st.previous_counter,
        ciphertext: st.ciphertext,
        pq: st.pq,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Read a varint from a fresh reader, for the cases below.
    fn v(bytes: &[u8]) -> Result<(u32, usize), ProtoError> {
        let mut r = Reader::new(bytes.to_vec())?;
        let value = r.varint()?;
        Ok((value, r.at))
    }

    /// **The same answers `Model.Protobuf` asserts.**
    ///
    /// Not a proof that the two agree, which is contract item 3 and needs a
    /// refinement theorem. This is the cheap half: if the model and the code
    /// disagree on a case either one states, one of them is wrong, and finding
    /// that out from a failing test costs minutes where finding it out from a
    /// failing refinement proof costs an afternoon of suspecting the proof.
    ///
    /// The model's examples are `native_decide`d, so they fail its build if
    /// wrong. These fail this crate's. A disagreement therefore cannot be
    /// green anywhere.
    #[test]
    fn the_model_and_the_code_agree_on_varints() {
        assert_eq!(v(&[0x05]), Ok((5, 1)));
        // 300, the canonical protobuf example.
        assert_eq!(v(&[0xAC, 0x02]), Ok((300, 2)));
        // Trailing bytes are left for the caller.
        assert_eq!(v(&[0x05, 0xFF]), Ok((5, 1)));
        // A non-minimal encoding of zero: two spellings of one value.
        assert_eq!(v(&[0x80, 0x00]), Err(ProtoError::BadVarint));
        // Longer than the profile allows.
        assert_eq!(
            v(&[0x80, 0x80, 0x80, 0x80, 0x80, 0x01]),
            Err(ProtoError::BadVarint)
        );
    }

    #[test]
    fn the_model_and_the_code_agree_on_tags() {
        assert_eq!(
            decode_tag(10),
            Ok(Tag {
                field: 1,
                wire: WireType::LengthDelimited
            })
        );
        // Field zero does not exist in protobuf.
        assert_eq!(decode_tag(2), Err(ProtoError::NotInProfile));
        // Above the profile: refused rather than skipped.
        assert_eq!(
            decode_tag((MAX_FIELD_NUMBER + 1) * 8 + 2),
            Err(ProtoError::NotInProfile)
        );
        // Wire type 5, which this profile does not carry.
        assert_eq!(decode_tag(13), Err(ProtoError::NotInProfile));
    }

    #[test]
    fn the_model_and_the_code_agree_on_length_delimited_fields() {
        let mut r = Reader::new(vec![0x03, 0xAA, 0xBB, 0xCC, 0xDD]).unwrap();
        assert_eq!(r.length_delimited(), Ok(vec![0xAA, 0xBB, 0xCC]));
        assert_eq!(r.remaining(), 1);

        // A length past the end takes nothing.
        let mut r = Reader::new(vec![0x08, 0xAA]).unwrap();
        assert_eq!(r.length_delimited(), Err(ProtoError::TooLong));
    }

    /// The outer limit is checked before a byte is read.
    #[test]
    fn an_oversized_input_is_refused_before_parsing() {
        let too_long = vec![0u8; MAX_MESSAGE_LEN + 1];
        assert_eq!(Reader::new(too_long).err(), Some(ProtoError::TooLong));
    }

    /// Every byte string this crate is given returns, which is what T1 proves
    /// for all inputs and this samples. Kept because a proof about the
    /// translated Rust is a proof about a translation, and a cheap check that
    /// the shipping build agrees costs nothing.
    #[test]
    fn a_field_number_cannot_be_admitted_twice() {
        let mut fs = FieldSet::new();
        assert!(fs.admit(3).is_none(), "first time");
        assert!(matches!(fs.admit(3), Some(ProtoError::Duplicate)));
    }

    #[test]
    fn a_different_field_number_still_can_be() {
        let mut fs = FieldSet::new();
        assert!(fs.admit(3).is_none(), "first");
        assert!(fs.admit(4).is_none());
    }

    #[test]
    fn the_profile_field_limit_is_enforced_and_not_merely_declared() {
        // The point of this test is the assertion at the end: `admit` reads
        // `MAX_FIELDS`, so the set stops admitting at the limit.
        let mut fs = FieldSet::new();
        for f in 0..MAX_FIELDS as u32 {
            assert!(fs.admit(f).is_none(), "within the limit");
        }
        assert!(matches!(fs.admit(9999), Some(ProtoError::TooLong)));
    }

    #[test]
    fn no_input_panics() {
        let mut seed = 0x2545_F491_4F6C_DD1Du64;
        let mut next = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..4096 {
            let n = (next() % 64) as usize;
            let bytes: Vec<u8> = (0..n).map(|_| (next() >> 33) as u8).collect();
            if let Ok(mut r) = Reader::new(bytes) {
                let _ = r.varint();
                let _ = r.tag();
                let _ = r.length_delimited();
            }
        }
    }

    /// The parser accepts fields in any order and the encoder emits them
    /// ascending, so `encode(parse(b))` is *not* `b` for a reordered `b`.
    /// Pinned so the gap stays visible: the day an authenticator is checked
    /// over re-encoded bytes, this test is the one that has to change, by
    /// making the parser refuse non-ascending order.
    #[test]
    fn reordered_fields_parse_but_do_not_re_emit() {
        let body = RatchetBody {
            ratchet_key: vec![0x05; 33],
            counter: 7,
            previous_counter: 3,
            ciphertext: vec![0x09; 48],
            pq: vec![0x01; 8],
        };
        let ascending = encode_ratchet_body(&body).unwrap();

        // The same five fields, counter first.
        let out = encode_tag(Vec::new(), FIELD_COUNTER, WireType::Varint).unwrap();
        let out = encode_varint(out, body.counter).unwrap();
        let out = encode_tag(out, FIELD_RATCHET_KEY, WireType::LengthDelimited).unwrap();
        let out = encode_length_delimited(out, &body.ratchet_key).unwrap();
        let out = encode_tag(out, FIELD_PREVIOUS_COUNTER, WireType::Varint).unwrap();
        let out = encode_varint(out, body.previous_counter).unwrap();
        let out = encode_tag(out, FIELD_CIPHERTEXT, WireType::LengthDelimited).unwrap();
        let out = encode_length_delimited(out, &body.ciphertext).unwrap();
        let out = encode_tag(out, FIELD_PQ, WireType::LengthDelimited).unwrap();
        let reordered = encode_length_delimited(out, &body.pq).unwrap();
        assert_ne!(reordered, ascending);

        let parsed = parse_ratchet_body(reordered.clone()).unwrap();
        assert_eq!(parsed.ratchet_key, body.ratchet_key);
        assert_eq!(parsed.counter, body.counter);
        assert_eq!(parsed.previous_counter, body.previous_counter);
        assert_eq!(parsed.ciphertext, body.ciphertext);
        assert_eq!(parsed.pq, body.pq);

        let re_emitted = encode_ratchet_body(&parsed).unwrap();
        assert_eq!(re_emitted, ascending, "re-emission is always ascending");
        assert_ne!(
            re_emitted, reordered,
            "so it is not byte-identical to a reordered input"
        );
    }
}
