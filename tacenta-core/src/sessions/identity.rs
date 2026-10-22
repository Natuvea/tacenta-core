//! Identity records, the identity pair digest, and the initiator's
//! expectation.
//!
//! This module implements three parts of the specification:
//!
//! - **The identity pair digest and the verification number**
//!   (`tacenta-spec/protocol/identities-and-devices.md`, The identity pair
//!   digest): [`identity_pair_digest`], [`verification_number`] and
//!   [`verification_number_grouped`].
//! - **Records, the classification and the lookup**
//!   (`tacenta-spec/protocol/session-establishment.md`, Records, expectations
//!   and attribution): [`Record`], [`classify`] and [`lookup`]. Their results
//!   are fixed by the specification; their names and signatures here are this
//!   implementation's.
//! - **Initiator establishment under an expectation** (the same section, and
//!   Sending the initial message): [`establish_initiator`] with an
//!   [`Expectation`], *known* or *first contact*.
//!
//! # Where this sits
//!
//! This module is outside the translated surface. Initiator establishment
//! here checks the expectation and then calls the translated lifecycle
//! leaf's `establish_initiator_for`, unchanged, with the bundle's own identity
//! key as the expected one, so the leaf's named-identity comparison can never
//! refuse. Nothing is drawn from the random generator before that call.
//! What is stated about the leaf's establishment holds for the session this
//! module returns only by reading this module, not by a proof about it.
//!
//! The functions are written in the subset the translated crates use (index
//! loops with flags, explicit `match`, no closures, no `?`, no early return
//! inside a loop), so that they can move into a translated crate later
//! without being rewritten. The digest's SHA-256 is the one call outside that
//! subset.
//!
//! # The order of checks
//!
//! [`establish_initiator`] refuses in this order, as session-establishment.md
//! fixes it:
//!
//! 1. a malformed expectation, as [`InitiatorError::MalformedRecord`], before
//!    any check of the bundle;
//! 2. the bundle's presence check (`LifecycleError::InconsistentBundle`) and
//!    canonical-key checks (`LifecycleError::BadEncoding`), the same
//!    predicates the leaf applies;
//! 3. the bundle's identity key against the expectation, which applies the
//!    identity-key rule first (`LifecycleError::Handshake(SessionError::InvalidIdentityKey)`),
//!    then refuses as [`InitiatorError::RetiredIdentity`] or
//!    [`InitiatorError::UnexpectedIdentity`];
//! 4. everything the leaf checks after that: the identity-key rule again
//!    (which cannot fire now), both signatures, the KEM prekey's input checks
//!    and the agreements, with the first random value drawn only after the
//!    signatures verify.
//!
//! So `RetiredIdentity` and `UnexpectedIdentity` are reported only for a
//! bundle that passed the presence and canonical-key checks and whose
//! identity key is an identity key.
//!
//! # Attribution
//!
//! A session is a contact's only when [`lookup`] of its peer identity key
//! ([`Session::peer_identity`]) finds it that contact's, against the records
//! as they stand when a plaintext is shown or the session is used. Every
//! plaintext and control payload a session yields is attributed exactly as
//! the session is. `Session::decrypt` returns plaintexts unwrapped; a caller
//! attributes them by a lookup of the session's peer key. For the responder's
//! first plaintext, [`establish_responder_unattributed`] returns it wrapped
//! in [`Unattributed`], which releases it only together with a lookup.

use rand_core::{CryptoRng, RngCore};
use sha2::{Digest, Sha256};
use tacenta_lifecycle::serialization::ABSENT_ID;
use tacenta_lifecycle::{
    Identity, LifecycleError, PrekeyStore, PublishedBundle, Session, SessionError,
    is_valid_identity_key,
};

use crate::primitives::dh::PublicKeyBytes;

/// The prefix of the identity pair digest's SHA-256 input:
/// `Tacenta:identity:pair-digest:v1` and the byte `0xFF`, 32 bytes
/// (`tacenta-spec/CONSTANTS.md`; registered in `tacenta-core/LABELS.md`).
pub const PAIR_DIGEST_LABEL: &[u8] = b"Tacenta:identity:pair-digest:v1\xff";

/// The length of the identity pair digest, in bytes.
pub const PAIR_DIGEST_LEN: usize = 32;

/// The length of the verification number, in ASCII decimal digits.
pub const VERIFICATION_NUMBER_LEN: usize = 60;

/// The length of the verification number laid out as twelve groups of five
/// digits separated by single spaces.
pub const VERIFICATION_NUMBER_GROUPED_LEN: usize = 71;

/// The label is the 32 bytes the specification fixes.
#[allow(dead_code, reason = "a compile-time assertion; nothing reads it")]
const PAIR_DIGEST_LABEL_IS_32_BYTES: () = assert!(PAIR_DIGEST_LABEL.len() == 32);

/// Why a presented key is refused: it is not an identity key
/// (`tacenta-spec/protocol/identities-and-devices.md`, Identity keys).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum KeyRefusal {
    /// The key is not the canonical encoding of a curve public key: bit 255 is
    /// set, or its value is at least p = 2^255 - 19. A decode failure, as
    /// `DecodeEC` refuses such a key.
    NotCanonical,
    /// The key is canonical but not an identity key: no point of the
    /// prime-order subgroup has it as its u-coordinate. An invalid identity
    /// key.
    InvalidIdentityKey,
}

/// The identity-key rule applied to a presented key, the canonical encoding
/// first: `None` when it is an identity key.
fn identity_key_refusal(key: &PublicKeyBytes) -> Option<KeyRefusal> {
    if !tacenta_session::is_canonical_x25519(key.as_bytes()) {
        Some(KeyRefusal::NotCanonical)
    } else if !is_valid_identity_key(key) {
        Some(KeyRefusal::InvalidIdentityKey)
    } else {
        None
    }
}

/// Whether `a <= b` as strings of unsigned bytes, byte 0 first: the first
/// byte that differs decides. Not the order of the keys' little-endian values.
fn unsigned_bytes_le(a: &[u8; 32], b: &[u8; 32]) -> bool {
    let mut decided = false;
    let mut result = true;
    let mut i = 0;
    while i < 32 {
        if !decided && a[i] != b[i] {
            decided = true;
            result = a[i] < b[i];
        }
        i += 1;
    }
    result
}

/// The identity pair digest of two identity keys
/// (`tacenta-spec/protocol/identities-and-devices.md`, The identity pair
/// digest): `SHA-256(PAIR_DIGEST_LABEL || lo || hi)`, where `lo` and `hi` are
/// the two keys sorted as strings of unsigned bytes. The same in either
/// argument order; equal keys are allowed.
///
/// Both keys are held to the identity-key rule. A key that is not canonical
/// is refused as [`KeyRefusal::NotCanonical`], and a canonical key that is not
/// an identity key as [`KeyRefusal::InvalidIdentityKey`]. When both keys
/// would be refused, `k1`'s refusal is reported; the specification lets
/// either conform.
///
/// The digest binds the two keys and nothing else. Equal digests mean the
/// two parties hold the same unordered pair of keys, not that the keys belong
/// to the people they mean to reach.
pub fn identity_pair_digest(
    k1: &PublicKeyBytes,
    k2: &PublicKeyBytes,
) -> Result<[u8; PAIR_DIGEST_LEN], KeyRefusal> {
    if let Some(refusal) = identity_key_refusal(k1) {
        return Err(refusal);
    }
    if let Some(refusal) = identity_key_refusal(k2) {
        return Err(refusal);
    }
    let (lo, hi) = if unsigned_bytes_le(k1.as_bytes(), k2.as_bytes()) {
        (k1, k2)
    } else {
        (k2, k1)
    };
    let mut hash = Sha256::new();
    hash.update(PAIR_DIGEST_LABEL);
    hash.update(lo.as_bytes());
    hash.update(hi.as_bytes());
    let mut out = [0u8; PAIR_DIGEST_LEN];
    out.copy_from_slice(&hash.finalize());
    Ok(out)
}

/// The verification number of a digest
/// (`tacenta-spec/protocol/identities-and-devices.md`, The verification
/// number): the digest read as an unsigned big-endian integer, reduced mod
/// 10^60, as 60 ASCII digits, most significant first, left-padded with `0`.
///
/// A comparison of fewer than 60 digits is not a comparison of the
/// verification number.
pub fn verification_number(digest: &[u8; PAIR_DIGEST_LEN]) -> [u8; VERIFICATION_NUMBER_LEN] {
    // Long division by ten, sixty times: each pass leaves the next decimal
    // digit, least significant first, as the remainder.
    let mut n = *digest;
    let mut out = [b'0'; VERIFICATION_NUMBER_LEN];
    let mut d = 0;
    while d < VERIFICATION_NUMBER_LEN {
        let mut rem: u32 = 0;
        let mut i = 0;
        while i < PAIR_DIGEST_LEN {
            let acc = rem * 256 + n[i] as u32;
            n[i] = (acc / 10) as u8;
            rem = acc % 10;
            i += 1;
        }
        out[VERIFICATION_NUMBER_LEN - 1 - d] = b'0' + rem as u8;
        d += 1;
    }
    out
}

/// A verification number laid out as twelve groups of five digits separated
/// by single spaces. The digits are unchanged.
pub fn verification_number_grouped(
    number: &[u8; VERIFICATION_NUMBER_LEN],
) -> [u8; VERIFICATION_NUMBER_GROUPED_LEN] {
    let mut out = [b' '; VERIFICATION_NUMBER_GROUPED_LEN];
    let mut i = 0;
    while i < VERIFICATION_NUMBER_LEN {
        out[i + i / 5] = number[i];
        i += 1;
    }
    out
}

/// A party's record for one contact
/// (`tacenta-spec/protocol/session-establishment.md`, Records, expectations
/// and attribution): the keys it accepts for the contact (`current`) and the
/// keys it no longer accepts for it (`retired`).
///
/// Each member must be the canonical encoding of a curve public key. A record
/// holding any other is malformed: [`classify`] refuses it, [`lookup`] skips
/// and reports it, and an [`Expectation`] holding it is refused. A canonical
/// member that is not an identity key is not malformed; it matches no
/// presented key. A key in both sets is retired. Duplicates are ignored.
/// How keys enter and leave a record is the party's own act.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Record {
    /// The keys the party accepts for the contact.
    pub current: Vec<PublicKeyBytes>,
    /// The keys the party no longer accepts for the contact.
    pub retired: Vec<PublicKeyBytes>,
}

impl Record {
    /// A record with the given current and retired keys.
    pub fn new(current: Vec<PublicKeyBytes>, retired: Vec<PublicKeyBytes>) -> Record {
        Record { current, retired }
    }

    /// Whether both sets are empty: a contact the party holds no record for.
    pub fn is_empty(&self) -> bool {
        self.current.is_empty() && self.retired.is_empty()
    }

    /// Whether any member of either set is not the canonical encoding of a
    /// curve public key.
    pub fn is_malformed(&self) -> bool {
        any_non_canonical(&self.current) || any_non_canonical(&self.retired)
    }
}

fn any_non_canonical(keys: &[PublicKeyBytes]) -> bool {
    let mut found = false;
    let mut i = 0;
    while i < keys.len() {
        if !tacenta_session::is_canonical_x25519(keys[i].as_bytes()) {
            found = true;
        }
        i += 1;
    }
    found
}

fn contains(keys: &[PublicKeyBytes], key: &PublicKeyBytes) -> bool {
    let mut found = false;
    let mut i = 0;
    while i < keys.len() {
        if keys[i] == *key {
            found = true;
        }
        i += 1;
    }
    found
}

/// How a presented key stands against one record.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum KeyClass {
    /// In the record's retired set (whether or not also current).
    Retired,
    /// In the current set and not in the retired set.
    Same,
    /// In neither set.
    New,
}

/// Why a classification is refused.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum ClassifyError {
    /// The presented key is not an identity key. Checked before the record.
    Key(KeyRefusal),
    /// A member of the record is not a canonical encoding. This reports the
    /// party's own record, never a peer's bytes.
    MalformedRecord,
}

/// The classification of an identity key already known to pass the rule.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Standing {
    Of(KeyClass),
    Malformed,
}

fn standing(key: &PublicKeyBytes, record: &Record) -> Standing {
    if record.is_malformed() {
        Standing::Malformed
    } else if contains(&record.retired, key) {
        Standing::Of(KeyClass::Retired)
    } else if contains(&record.current, key) {
        Standing::Of(KeyClass::Same)
    } else {
        Standing::Of(KeyClass::New)
    }
}

/// Classify a presented key against one record
/// (`tacenta-spec/protocol/session-establishment.md`, Records, expectations
/// and attribution, Classification).
///
/// The presented key is held to the identity-key rule before anything else:
/// a key that is not canonical, or canonical and not an identity key, is
/// refused as [`ClassifyError::Key`]. Then every member of both sets is
/// checked, and a non-canonical member refuses the classification as
/// [`ClassifyError::MalformedRecord`], even if the key matches another
/// member. Otherwise the key is [`KeyClass::Retired`] if it is in the retired
/// set, else [`KeyClass::Same`] if it is in the current set, else
/// [`KeyClass::New`]. Membership is equality of the 32 bytes.
///
/// A record with both sets empty classifies every identity key as `New`.
pub fn classify(key: &PublicKeyBytes, record: &Record) -> Result<KeyClass, ClassifyError> {
    if let Some(refusal) = identity_key_refusal(key) {
        return Err(ClassifyError::Key(refusal));
    }
    match standing(key, record) {
        Standing::Of(class) => Ok(class),
        Standing::Malformed => Err(ClassifyError::MalformedRecord),
    }
}

/// Whose a key is, by a lookup across all of a party's records.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Attribution {
    /// *Same* for exactly one record: the key is that contact's. The index is
    /// the record's position in the slice given to [`lookup`].
    Contact(usize),
    /// *Same* for more than one record: the key is no contact's.
    Ambiguous,
    /// *Same* for none and *retired* for one or more: a retired key of those
    /// contacts ([`Lookup::retired_for`]), and no contact's.
    RetiredKey,
    /// *Same* for none and *retired* for none: no contact's.
    Unattributed,
}

/// The result of a [`lookup`]. Contacts are named by their record's position
/// in the slice the lookup was given.
#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub struct Lookup {
    /// Whose the key is.
    pub attribution: Attribution,
    /// The records that classify the key as *same*, in slice order.
    pub same_for: Vec<usize>,
    /// The records that classify the key as *retired*, in slice order.
    /// Reported whatever the attribution.
    pub retired_for: Vec<usize>,
    /// The records skipped because they are malformed, in slice order. They
    /// attribute nothing.
    pub malformed: Vec<usize>,
}

/// Look a key up in all of a party's records
/// (`tacenta-spec/protocol/session-establishment.md`, Records, expectations
/// and attribution, Lookup).
///
/// A key that is not an identity key refuses the lookup with the
/// classification's [`KeyRefusal`], whether or not there are records, and no
/// record is reported. A malformed record is skipped and reported in
/// [`Lookup::malformed`]. The others decide the [`Attribution`].
///
/// Attribution comes only from the records: a label, handle or address that a
/// bundle, a message or the transport supplies never selects a record.
pub fn lookup(key: &PublicKeyBytes, records: &[Record]) -> Result<Lookup, KeyRefusal> {
    if let Some(refusal) = identity_key_refusal(key) {
        return Err(refusal);
    }
    let mut same_for = Vec::new();
    let mut retired_for = Vec::new();
    let mut malformed = Vec::new();
    let mut i = 0;
    while i < records.len() {
        match standing(key, &records[i]) {
            Standing::Of(KeyClass::Same) => same_for.push(i),
            Standing::Of(KeyClass::Retired) => retired_for.push(i),
            Standing::Of(KeyClass::New) => {}
            Standing::Malformed => malformed.push(i),
        }
        i += 1;
    }
    let attribution = if same_for.len() == 1 {
        Attribution::Contact(same_for[0])
    } else if same_for.len() > 1 {
        Attribution::Ambiguous
    } else if !retired_for.is_empty() {
        Attribution::RetiredKey
    } else {
        Attribution::Unattributed
    };
    Ok(Lookup {
        attribution,
        same_for,
        retired_for,
        malformed,
    })
}

/// What the initiator expects of the bundle's identity key
/// (`tacenta-spec/protocol/session-establishment.md`, Records, expectations
/// and attribution, The initiator). Built with [`Expectation::known`] or
/// [`Expectation::first_contact`].
///
/// Stating *first contact* for a contact the party holds a record for, or
/// leaving some of its records out of it, is the party's own failure, which
/// no implementation can see.
#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub enum Expectation<'a> {
    /// *Known*: the record of the contact she means to reach, which she
    /// selects herself. It must not be empty.
    #[non_exhaustive]
    Known {
        /// The contact's record.
        record: &'a Record,
    },
    /// *First contact*: for a peer she holds no record for. It carries all
    /// her records.
    #[non_exhaustive]
    FirstContact {
        /// Every record the party holds.
        records: &'a [Record],
    },
}

impl<'a> Expectation<'a> {
    /// *Known*, with the record of the contact she means to reach.
    pub fn known(record: &'a Record) -> Expectation<'a> {
        Expectation::Known { record }
    }

    /// *First contact*, with all of her records. An empty slice is a party
    /// that holds no records at all.
    pub fn first_contact(records: &'a [Record]) -> Expectation<'a> {
        Expectation::FirstContact { records }
    }

    /// Whether the expectation is malformed: it holds a non-canonical key, in
    /// the record under *known* or in any record under *first contact*, or it
    /// is *known* with a record whose two sets are both empty.
    pub fn is_malformed(&self) -> bool {
        match self {
            Expectation::Known { record } => record.is_empty() || record.is_malformed(),
            Expectation::FirstContact { records } => {
                let mut found = false;
                let mut i = 0;
                while i < records.len() {
                    if records[i].is_malformed() {
                        found = true;
                    }
                    i += 1;
                }
                found
            }
        }
    }
}

/// Reserved for evidence about a key from outside the party's records, such
/// as a key-transparency proof. It has no variants, so no value of it exists
/// and nothing constructs or consumes one.
///
/// It is not part of [`Expectation`] yet. Giving it a value adds a check and
/// a refusal to establishment, which is a change the specification has to
/// make first (`tacenta-spec/decisions/ADR-0006-specification-is-normative.md`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum KeyEvidence {}

/// Why initiator establishment under an expectation refused.
///
/// `#[non_exhaustive]`: pre-1.0, so a consumer carries a wildcard arm.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum InitiatorError {
    /// The expectation holds a non-canonical key, or is *known* with an empty
    /// record. Reported before any check of the bundle; it reports the
    /// party's own records, never a peer's bytes.
    MalformedRecord,
    /// The bundle's identity key is *new* in the record under *known*, or,
    /// under *first contact*, a recorded contact's key or an ambiguous one.
    UnexpectedIdentity,
    /// The bundle's identity key is *retired* in the record under *known*, or,
    /// under *first contact*, a retired key (*same* for no record).
    RetiredIdentity,
    /// A refusal the lifecycle leaf names, with its kind: a presence
    /// disagreement (`InconsistentBundle`), a non-canonical bundle key
    /// (`BadEncoding`), an identity key that is not an identity key
    /// (`Handshake(InvalidIdentityKey)`), a signature, the KEM prekey's input
    /// checks or a non-contributory agreement. Never `UnexpectedIdentity`:
    /// the leaf is always called with the bundle's own identity key.
    Establish(LifecycleError),
}

/// The bundle's identity key against the expectation, the identity-key rule
/// first. `None` lets establishment go on.
fn expectation_refusal(key: &PublicKeyBytes, expectation: &Expectation) -> Option<InitiatorError> {
    match identity_key_refusal(key) {
        Some(KeyRefusal::NotCanonical) => {
            return Some(InitiatorError::Establish(LifecycleError::BadEncoding));
        }
        Some(KeyRefusal::InvalidIdentityKey) => {
            return Some(InitiatorError::Establish(LifecycleError::Handshake(
                SessionError::InvalidIdentityKey,
            )));
        }
        None => {}
    }
    match expectation {
        Expectation::Known { record } => match standing(key, record) {
            Standing::Of(KeyClass::Same) => None,
            Standing::Of(KeyClass::Retired) => Some(InitiatorError::RetiredIdentity),
            Standing::Of(KeyClass::New) => Some(InitiatorError::UnexpectedIdentity),
            Standing::Malformed => Some(InitiatorError::MalformedRecord),
        },
        Expectation::FirstContact { records } => {
            let mut same = false;
            let mut retired = false;
            let mut i = 0;
            while i < records.len() {
                match standing(key, &records[i]) {
                    Standing::Of(KeyClass::Same) => same = true,
                    Standing::Of(KeyClass::Retired) => retired = true,
                    Standing::Of(KeyClass::New) => {}
                    Standing::Malformed => {}
                }
                i += 1;
            }
            if same {
                Some(InitiatorError::UnexpectedIdentity)
            } else if retired {
                Some(InitiatorError::RetiredIdentity)
            } else {
                None
            }
        }
    }
}

/// Establish a session as the initiator, from the peer's published bundle,
/// under an expectation (`tacenta-spec/protocol/session-establishment.md`,
/// Sending the initial message; Records, expectations and attribution). The
/// session is returned pending: the first `encrypt` produces the initial
/// message.
///
/// The checks run in the order the specification fixes (see the module
/// documentation): a malformed expectation first, then the bundle's presence
/// and canonical-key checks, then the bundle's identity key against the
/// expectation with the identity-key rule applied first, then the signatures,
/// the KEM prekey's input checks and the agreements. Every refusal before the
/// signatures draws nothing from `rng`.
///
/// A session established under *known* can still be ambiguous, if the key is
/// also current in another record, and one established under *first contact*
/// is unattributed. Attribute it by [`lookup`] of
/// [`Session::peer_identity`] against the records as they stand.
pub fn establish_initiator<R: RngCore + CryptoRng>(
    our_identity: &Identity,
    their_bundle: &PublishedBundle,
    expectation: &Expectation,
    rng: &mut R,
) -> Result<Session, InitiatorError> {
    if expectation.is_malformed() {
        return Err(InitiatorError::MalformedRecord);
    }
    let bundle = &their_bundle.bundle;
    // The presence and canonical-key checks, with the predicates the leaf
    // applies, so that a bundle refused here is refused as the leaf would.
    if bundle.one_time_prekey.is_some() != (their_bundle.one_time_prekey_id != ABSENT_ID) {
        return Err(InitiatorError::Establish(
            LifecycleError::InconsistentBundle,
        ));
    }
    let one_time_canonical = match &bundle.one_time_prekey {
        None => true,
        Some(key) => tacenta_session::is_canonical_x25519(key.as_bytes()),
    };
    if !tacenta_session::is_canonical_x25519(bundle.identity_key.as_bytes())
        || !tacenta_session::is_canonical_x25519(bundle.signed_prekey.as_bytes())
        || !one_time_canonical
    {
        return Err(InitiatorError::Establish(LifecycleError::BadEncoding));
    }
    if let Some(refusal) = expectation_refusal(&bundle.identity_key, expectation) {
        return Err(refusal);
    }
    // The leaf, unchanged, pinned to the key the expectation just accepted.
    match tacenta_lifecycle::establish_initiator_for(
        our_identity,
        their_bundle,
        &bundle.identity_key,
        rng,
    ) {
        Ok(session) => Ok(session),
        Err(error) => Err(InitiatorError::Establish(error)),
    }
}

/// A value from a session that no lookup has attributed yet. It gives the
/// session's peer identity key, and releases the value only together with a
/// [`lookup`] of that key.
#[derive(Debug)]
pub struct Unattributed<T> {
    peer_identity: PublicKeyBytes,
    value: T,
}

impl<T> Unattributed<T> {
    /// The peer identity key of the session the value came from.
    pub fn peer_identity(&self) -> PublicKeyBytes {
        self.peer_identity
    }

    /// Release the value with a lookup of the session's peer identity key in
    /// `records`. The value is attributed exactly as the lookup finds the key:
    /// a contact's, or no contact's (ambiguous, a retired key, or
    /// unattributed). A peer key that is not an identity key refuses, and
    /// keeps the value back; a session never holds one.
    pub fn attribute(self, records: &[Record]) -> Result<(Lookup, T), KeyRefusal> {
        match lookup(&self.peer_identity, records) {
            Ok(found) => Ok((found, self.value)),
            Err(refusal) => Err(refusal),
        }
    }
}

/// Establish a session as the responder, as `establish_responder` does,
/// returning the first plaintext as [`Unattributed`].
///
/// The establishment is unchanged: whatever identity key the initial message
/// carries, once it passes the identity-key rule and the message
/// authenticates, the session is returned and its prekeys are consumed. No
/// record is consulted, and no expectation refuses. The session and the
/// plaintext are attributed only by a lookup, which skips and reports a
/// malformed record rather than refusing.
pub fn establish_responder_unattributed<R: RngCore + CryptoRng>(
    our_identity: &Identity,
    our_prekeys: &mut PrekeyStore,
    initial_message: &[u8],
    rng: &mut R,
) -> Result<(Session, Unattributed<Vec<u8>>), LifecycleError> {
    match tacenta_lifecycle::establish_responder(our_identity, our_prekeys, initial_message, rng) {
        Ok((session, plaintext)) => {
            let peer_identity = session.peer_identity();
            Ok((
                session,
                Unattributed {
                    peer_identity,
                    value: plaintext,
                },
            ))
        }
        Err(error) => Err(error),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(text: &str) -> PublicKeyBytes {
        let bytes: [u8; 32] = hex::decode(text).unwrap().try_into().unwrap();
        PublicKeyBytes::from_bytes(bytes)
    }

    fn digest(text: &str) -> [u8; 32] {
        hex::decode(text).unwrap().try_into().unwrap()
    }

    fn digits(number: &[u8]) -> &str {
        core::str::from_utf8(number).unwrap()
    }

    // RFC 7748 section 6.1: Alice's and Bob's public keys. Both are identity
    // keys (the X25519 public keys of clamped secrets).
    const ALICE: &str = "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a";
    const BOB: &str = "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f";
    // Alice's key plus a point of order 8: the same X25519 agreement under a
    // clamped scalar, but of mixed order, so not an identity key.
    const ALICE_PLUS_TORSION: &str =
        "ec06a18b2851717cbad4dda975daa176baef2f520371e51e5383029272448859";
    // Two identity keys whose unsigned byte order disagrees with the order of
    // their little-endian values.
    const D3_A: &str = "9adcf8b0b668a3d1265ceaeca21842d68fbed9b24a955d77142b1ef112b49b09";
    const D3_B: &str = "4495ae279c3c3726cb968047eb431fc19a94b67c9649016ac7042617384bd930";
    // Two identity keys whose unsigned order disagrees with the signed-byte,
    // u64-limb and little-endian value orders.
    const D3B_A: &str = "024dfc7477b284dd11f4b6562500ce06aaa4d903e085182e76d6bec3a10bc01b";
    const D3B_B: &str = "b832ea22937fb9b62143d78e2ec1b582baabfc9686593c34e8d1ee72cae95819";

    const U0: &str = "0000000000000000000000000000000000000000000000000000000000000000";
    const U1: &str = "0100000000000000000000000000000000000000000000000000000000000000";
    const U2: &str = "0200000000000000000000000000000000000000000000000000000000000000";
    const P_MINUS_1: &str = "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f";
    const ORDER_8_A: &str = "e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800";
    const ORDER_8_B: &str = "5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157";
    const U_P: &str = "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f";
    const U_P_PLUS_18: &str = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f";
    const ALL_FF: &str = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    const NINE_BIT_255: &str = "0900000000000000000000000000000000000000000000000000000000000080";

    fn record(current: &[&str], retired: &[&str]) -> Record {
        let mut c = Vec::new();
        for k in current {
            c.push(key(k));
        }
        let mut r = Vec::new();
        for k in retired {
            r.push(key(k));
        }
        Record::new(c, r)
    }

    #[test]
    fn the_label_is_the_32_bytes_constants_md_gives() {
        assert_eq!(
            hex::encode(PAIR_DIGEST_LABEL),
            "546163656e74613a6964656e746974793a706169722d6469676573743a7631ff"
        );
    }

    /// The accepted digest cases, in both argument orders, with their
    /// verification numbers. The expected values were computed with Python's
    /// `hashlib` over `PAIR_DIGEST_LABEL || lo || hi`, independently of this
    /// code.
    #[test]
    fn digest_known_answers_in_both_orders() {
        let cases = [
            (
                "rfc7748-alice-bob",
                ALICE,
                BOB,
                "14008811078928fb1c0b1467a9abb2398f06cdbe384d30f1e1c2555aa6a4128d",
                "052232527622821359925098979431014658475034016576229087646349",
            ),
            (
                "equal-keys",
                ALICE,
                ALICE,
                "bd9ea428f322bc1156ba40bed0ce489c0c627f1c44457f6b8caf07a12d81583f",
                "342505388527416776856014407131757739973616090526712340764735",
            ),
            (
                "unsigned-against-little-endian-order",
                D3_A,
                D3_B,
                "0027825f48dd255fd917134fc155e774a0ca3349f447bea76c9ec01116c25b01",
                "326740346840144235862691584058853149216616459493057048500993",
            ),
            (
                "unsigned-against-signed-limb-and-value-orders",
                D3B_A,
                D3B_B,
                "8d4322bf83f49d728de0ff1b74146da602f44ecea4d2f68c9474a28fb703ca45",
                "810580752928734638613309288310412549030767074425684229343813",
            ),
        ];
        for (id, k1, k2, expected, number) in cases {
            let forward = identity_pair_digest(&key(k1), &key(k2)).unwrap();
            let backward = identity_pair_digest(&key(k2), &key(k1)).unwrap();
            assert_eq!(hex::encode(forward), expected, "{id}");
            assert_eq!(
                forward, backward,
                "{id}: the digest depends on argument order"
            );
            assert_eq!(digits(&verification_number(&forward)), number, "{id}");
        }
    }

    /// A digest that sorted by the keys' little-endian values, or by signed
    /// bytes, would give the other order's digest on these pairs. The values
    /// are SHA-256 over the label and the keys in the wrong order.
    #[test]
    fn the_digest_sorts_as_unsigned_bytes_and_not_otherwise() {
        let wrong = [
            (
                D3_A,
                D3_B,
                "608e2f4e4fc29c9158f3cf0c1b51cc2cd1c4dad1e1b5a8d87efaca9734bd8d76",
            ),
            (
                D3B_A,
                D3B_B,
                "016808aafca179f1e801befea73aef693f38866296a3cee77fce05e6f3e0bbec",
            ),
        ];
        for (k1, k2, reversed) in wrong {
            let got = identity_pair_digest(&key(k1), &key(k2)).unwrap();
            assert_ne!(hex::encode(got), reversed);
        }
        assert!(!unsigned_bytes_le(
            key(D3_A).as_bytes(),
            key(D3_B).as_bytes()
        ));
        assert!(unsigned_bytes_le(
            key(D3_B).as_bytes(),
            key(D3_A).as_bytes()
        ));
        assert!(unsigned_bytes_le(
            key(ALICE).as_bytes(),
            key(ALICE).as_bytes()
        ));
    }

    /// Canonical keys that are not identity keys are refused as invalid
    /// identity keys, in both orders: the torsion twin of an honest key, the
    /// pair (0, 0), the low-order values, u = 2 (on the twist), and u = p - 1.
    #[test]
    fn digest_refuses_keys_that_are_not_identity_keys() {
        let cases = [
            ("alice-plus-torsion", ALICE_PLUS_TORSION, ALICE),
            ("zero-zero", U0, U0),
            ("u0", U0, ALICE),
            ("u1", U1, ALICE),
            ("p-minus-1", P_MINUS_1, ALICE),
            ("order-8-a", ORDER_8_A, ALICE),
            ("order-8-b", ORDER_8_B, ALICE),
            ("u2-twist", U2, ALICE),
            ("p-minus-1-with-bob", P_MINUS_1, BOB),
        ];
        for (id, k1, k2) in cases {
            assert_eq!(
                identity_pair_digest(&key(k1), &key(k2)),
                Err(KeyRefusal::InvalidIdentityKey),
                "{id}"
            );
            assert_eq!(
                identity_pair_digest(&key(k2), &key(k1)),
                Err(KeyRefusal::InvalidIdentityKey),
                "{id} reversed"
            );
        }
    }

    /// Keys that are not canonical are refused as decode failures, in both
    /// orders.
    #[test]
    fn digest_refuses_non_canonical_keys_as_decode_failures() {
        for (id, k) in [
            ("u-p", U_P),
            ("u-p-plus-18", U_P_PLUS_18),
            ("all-ff", ALL_FF),
            ("nine-bit-255", NINE_BIT_255),
        ] {
            assert_eq!(
                identity_pair_digest(&key(k), &key(ALICE)),
                Err(KeyRefusal::NotCanonical),
                "{id}"
            );
            assert_eq!(
                identity_pair_digest(&key(ALICE), &key(k)),
                Err(KeyRefusal::NotCanonical),
                "{id} reversed"
            );
        }
    }

    /// Both keys refused, with different kinds: either refusal conforms.
    #[test]
    fn digest_with_two_refused_keys_reports_one_of_them() {
        let either = [KeyRefusal::NotCanonical, KeyRefusal::InvalidIdentityKey];
        let forward = identity_pair_digest(&key(U_P), &key(U0)).unwrap_err();
        let backward = identity_pair_digest(&key(U0), &key(U_P)).unwrap_err();
        assert!(either.contains(&forward));
        assert!(either.contains(&backward));
    }

    #[test]
    fn verification_number_known_answers() {
        let cases = [
            (
                "all-zero",
                "0000000000000000000000000000000000000000000000000000000000000000",
                "000000000000000000000000000000000000000000000000000000000000",
            ),
            (
                "all-ff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "423570985008687907853269984665640564039457584007913129639935",
            ),
            (
                "first-byte-high",
                "f30f87160c9c36b2645d92005f9555ee30ed00199f19bd6e1dde7c5bb2ec0bde",
                "615284566845113059934298192627384047078637029284611927837662",
            ),
            (
                "below-ten-to-the-thirty",
                "0000000000000000000000000000000000000000000000000000000000003039",
                "000000000000000000000000000000000000000000000000000000012345",
            ),
            (
                "big-endian",
                "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
                "700044960722568376592200742329637303199754547598369979440671",
            ),
        ];
        for (id, d, number) in cases {
            assert_eq!(digits(&verification_number(&digest(d))), number, "{id}");
        }
        // The little-endian reading of the last digest gives another number.
        assert_ne!(
            digits(&verification_number(&digest(
                "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
            ))),
            "155369551180448584754667373453244490859944217516317499064576"
        );
    }

    #[test]
    fn verification_number_in_twelve_groups_of_five() {
        let d = identity_pair_digest(&key(ALICE), &key(BOB)).unwrap();
        let grouped = verification_number_grouped(&verification_number(&d));
        assert_eq!(
            digits(&grouped),
            "05223 25276 22821 35992 50989 79431 01465 84750 34016 57622 90876 46349"
        );
    }

    #[test]
    fn classification_over_the_cases() {
        let k = ALICE;
        let k2 = BOB;
        let k3 = D3_A;
        let cases: [(&str, &str, Record, Result<KeyClass, ClassifyError>); 17] = [
            ("empty-record", k, record(&[], &[]), Ok(KeyClass::New)),
            ("same", k, record(&[k], &[]), Ok(KeyClass::Same)),
            ("new", k2, record(&[k], &[]), Ok(KeyClass::New)),
            ("retired", k, record(&[], &[k]), Ok(KeyClass::Retired)),
            (
                "retired-over-same",
                k,
                record(&[k], &[k]),
                Ok(KeyClass::Retired),
            ),
            ("retired-other", k, record(&[], &[k2]), Ok(KeyClass::New)),
            (
                "torsion-twin",
                ALICE_PLUS_TORSION,
                record(&[k], &[]),
                Err(ClassifyError::Key(KeyRefusal::InvalidIdentityKey)),
            ),
            (
                "middle-of-three",
                k2,
                record(&[k, k2, k3], &[]),
                Ok(KeyClass::Same),
            ),
            (
                "presented-bit-255",
                ALL_FF,
                record(&[k], &[]),
                Err(ClassifyError::Key(KeyRefusal::NotCanonical)),
            ),
            (
                "presented-u-p",
                U_P,
                record(&[k], &[]),
                Err(ClassifyError::Key(KeyRefusal::NotCanonical)),
            ),
            (
                "malformed-current",
                k,
                record(&[k, U_P], &[]),
                Err(ClassifyError::MalformedRecord),
            ),
            (
                "malformed-retired",
                k,
                record(&[k], &[ALL_FF]),
                Err(ClassifyError::MalformedRecord),
            ),
            (
                "malformed-before-retired-match",
                k,
                record(&[U_P], &[k]),
                Err(ClassifyError::MalformedRecord),
            ),
            (
                "canonical-non-identity-member",
                k,
                record(&[k], &[U0]),
                Ok(KeyClass::Same),
            ),
            (
                "presented-u0-member",
                U0,
                record(&[], &[U0]),
                Err(ClassifyError::Key(KeyRefusal::InvalidIdentityKey)),
            ),
            (
                "presented-key-before-members",
                ALICE_PLUS_TORSION,
                record(&[U_P], &[]),
                Err(ClassifyError::Key(KeyRefusal::InvalidIdentityKey)),
            ),
            (
                "canonical-first-of-all",
                U_P,
                record(&[ALL_FF], &[]),
                Err(ClassifyError::Key(KeyRefusal::NotCanonical)),
            ),
        ];
        for (id, presented, rec, expected) in cases {
            assert_eq!(classify(&key(presented), &rec), expected, "{id}");
        }
    }

    /// Duplicates in a list are ignored: the classification is that of the
    /// set of members.
    #[test]
    fn classification_ignores_duplicates() {
        let k = ALICE;
        let k2 = BOB;
        for presented in [k, k2, D3_A] {
            assert_eq!(
                classify(&key(presented), &record(&[k, k, k2], &[])),
                classify(&key(presented), &record(&[k, k2], &[])),
                "{presented}"
            );
        }
    }

    /// Members that are not identity keys never match a presented key.
    #[test]
    fn non_identity_members_never_match() {
        assert_eq!(
            classify(&key(ALICE), &record(&[U2, ALICE_PLUS_TORSION], &[])),
            Ok(KeyClass::New)
        );
    }

    #[test]
    fn lookup_over_the_cases() {
        let k = ALICE;
        let d = BOB;
        let other = D3_A;
        // (id, key, records, attribution, same_for, retired_for, malformed)
        type Row<'a> = (
            &'a str,
            &'a str,
            Vec<Record>,
            Attribution,
            Vec<usize>,
            Vec<usize>,
            Vec<usize>,
        );
        let rows: Vec<Row> = vec![
            (
                "same-for-one",
                k,
                vec![record(&[other], &[]), record(&[k], &[])],
                Attribution::Contact(1),
                vec![1],
                vec![],
                vec![],
            ),
            (
                "same-for-two",
                k,
                vec![record(&[k], &[]), record(&[k, d], &[])],
                Attribution::Ambiguous,
                vec![0, 1],
                vec![],
                vec![],
            ),
            (
                "retired-for-one",
                k,
                vec![record(&[], &[k]), record(&[other], &[])],
                Attribution::RetiredKey,
                vec![],
                vec![0],
                vec![],
            ),
            (
                "same-for-one-retired-for-another",
                k,
                vec![record(&[k], &[]), record(&[], &[k])],
                Attribution::Contact(0),
                vec![0],
                vec![1],
                vec![],
            ),
            (
                "in-no-record",
                k,
                vec![record(&[d], &[]), record(&[], &[other])],
                Attribution::Unattributed,
                vec![],
                vec![],
                vec![],
            ),
            (
                "malformed-and-same",
                k,
                vec![record(&[k, U_P], &[]), record(&[k], &[])],
                Attribution::Contact(1),
                vec![1],
                vec![],
                vec![0],
            ),
            (
                "only-malformed-holds-it",
                k,
                vec![record(&[k], &[ALL_FF])],
                Attribution::Unattributed,
                vec![],
                vec![],
                vec![0],
            ),
            (
                "same-for-two-retired-for-one",
                k,
                vec![
                    record(&[k], &[]),
                    record(&[], &[k]),
                    record(&[k, other], &[]),
                ],
                Attribution::Ambiguous,
                vec![0, 2],
                vec![1],
                vec![],
            ),
            (
                "retired-for-two",
                k,
                vec![record(&[d], &[k]), record(&[], &[k])],
                Attribution::RetiredKey,
                vec![],
                vec![0, 1],
                vec![],
            ),
            (
                "non-identity-members-only",
                k,
                vec![record(&[U0, U2], &[])],
                Attribution::Unattributed,
                vec![],
                vec![],
                vec![],
            ),
            (
                "no-records",
                k,
                vec![],
                Attribution::Unattributed,
                vec![],
                vec![],
                vec![],
            ),
        ];
        for (id, presented, records, attribution, same_for, retired_for, malformed) in rows {
            let found = lookup(&key(presented), &records).unwrap();
            assert_eq!(found.attribution, attribution, "{id}");
            assert_eq!(found.same_for, same_for, "{id}");
            assert_eq!(found.retired_for, retired_for, "{id}");
            assert_eq!(found.malformed, malformed, "{id}");
        }
    }

    /// A presented key that is not an identity key refuses the lookup, with
    /// records and without, and no record is reported.
    #[test]
    fn lookup_refuses_a_presented_key_that_is_not_an_identity_key() {
        let records = vec![record(&[ALICE], &[]), record(&[ALICE, U_P], &[])];
        for (id, presented, refusal) in [
            ("non-canonical", U_P, KeyRefusal::NotCanonical),
            ("bit-255", ALL_FF, KeyRefusal::NotCanonical),
            (
                "torsion-twin",
                ALICE_PLUS_TORSION,
                KeyRefusal::InvalidIdentityKey,
            ),
            ("u0", U0, KeyRefusal::InvalidIdentityKey),
        ] {
            assert_eq!(lookup(&key(presented), &records), Err(refusal), "{id}");
            assert_eq!(
                lookup(&key(presented), &[]),
                Err(refusal),
                "{id}, no records"
            );
        }
    }

    #[test]
    fn expectation_malformed_cases() {
        let good = record(&[ALICE], &[]);
        let empty = record(&[], &[]);
        let bad_current = record(&[ALICE, U_P], &[]);
        let bad_retired = record(&[ALICE], &[ALL_FF]);
        let non_identity = record(&[ALICE, U0], &[]);
        assert!(!Expectation::known(&good).is_malformed());
        assert!(!Expectation::known(&non_identity).is_malformed());
        assert!(Expectation::known(&empty).is_malformed());
        assert!(Expectation::known(&bad_current).is_malformed());
        assert!(Expectation::known(&bad_retired).is_malformed());
        assert!(!Expectation::first_contact(&[]).is_malformed());
        // An empty record under first contact is a contact with no record,
        // which is allowed.
        assert!(!Expectation::first_contact(&[empty.clone(), good.clone()]).is_malformed());
        assert!(Expectation::first_contact(&[good.clone(), bad_retired.clone()]).is_malformed());
        assert!(Expectation::first_contact(&[bad_current]).is_malformed());
    }
}
