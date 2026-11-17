//! Property tests for five of the identity-record functions of
//! `tacenta_core::sessions::identity`: `identity_pair_digest`, `verification_number`,
//! `verification_number_grouped`, `classify` and `lookup`.
//!
//! Each property names the sentence it tests, in
//! `tacenta-spec/protocol/identities-and-devices.md` (The identity pair digest; The
//! verification number) or `tacenta-spec/protocol/session-establishment.md` (Records,
//! expectations and attribution), and checks the function against an oracle written
//! here from that sentence: SHA-256 from the `sha2` crate over the label and the keys
//! sorted as the page orders them; the decimal digits computed by Horner's rule on a
//! decimal array (the function uses long division); the classification and the lookup
//! written out from the page's lists. The identity-key rule inside them is taken from
//! `is_valid_identity_key`, which these tests do not test (the inventory and identity
//! boundary tests and the vectors do).
//!
//! Keys are drawn from a small pool per case, so that the same key falls in several
//! records and both sets: honest identity keys (the X25519 public key of a 32-byte
//! secret, which the library clamps), arbitrary canonical bytes (most of them not
//! identity keys) and non-canonical spellings (bit 255 set).
//!
//! Not covered here: `establish_initiator`, `Unattributed::attribute` and
//! `establish_responder_unattributed`, whose generated-input coverage is the matter of
//! the register.
//!
//! Case count: `CASES` (512) per property when `PROPTEST_CASES` is unset. `PROPTEST_CASES`
//! overrides it (proptest reads the variable over the configuration given here), and the
//! hosted `rust` job and `tooling/ci.sh` set it to 2,048, so that is the count CI runs.
//! Replay: proptest shrinks a failing case and
//! prints the minimal input in the failure message, and its default failure
//! persistence writes the failing case's seed to
//! `identity_records_properties.proptest-regressions` beside this file, which the next
//! local run replays first. No regressions file is committed and the generator's seed
//! is not fixed, so a run that fails in CI is replayed from the minimal input its log
//! prints.

use proptest::prelude::*;
use sha2::{Digest, Sha256};
use tacenta_core::primitives::dh::PublicKeyBytes;
use tacenta_core::sessions::identity::{
    Attribution, ClassifyError, KeyClass, KeyRefusal, Record, classify, identity_pair_digest,
    lookup, verification_number, verification_number_grouped,
};
use tacenta_core::sessions::is_valid_identity_key;
use x25519_dalek::{PublicKey, StaticSecret};

/// The number of generated cases each property runs.
const CASES: u32 = 512;

/// The label as the page gives it: the ASCII string and one `0xFF` byte, 32 bytes.
const LABEL: &[u8] = b"Tacenta:identity:pair-digest:v1\xff";

fn config() -> ProptestConfig {
    ProptestConfig::with_cases(CASES)
}

/// The page's canonical rule on the bytes: bit 255 clear and the value below p.
fn canonical(k: &[u8; 32]) -> bool {
    if k[31] & 0x80 != 0 {
        return false;
    }
    let mut p = [0xffu8; 32];
    p[0] = 0xed;
    p[31] = 0x7f;
    for i in (0..32).rev() {
        if k[i] != p[i] {
            return k[i] < p[i];
        }
    }
    false
}

/// The identity-key rule as the page orders it: the canonical encoding first.
fn refusal(k: &[u8; 32]) -> Option<KeyRefusal> {
    if !canonical(k) {
        Some(KeyRefusal::NotCanonical)
    } else if !is_valid_identity_key(&PublicKeyBytes::from_bytes(*k)) {
        Some(KeyRefusal::InvalidIdentityKey)
    } else {
        None
    }
}

/// One key of the pool: an honest identity key, arbitrary canonical bytes, or a
/// spelling with bit 255 set.
fn pool_key() -> impl Strategy<Value = [u8; 32]> {
    prop_oneof![
        3 => prop::array::uniform32(any::<u8>())
            .prop_map(|s| PublicKey::from(&StaticSecret::from(s)).to_bytes()),
        1 => prop::array::uniform32(any::<u8>()).prop_map(|mut k| {
            k[31] &= 0x3f;
            k
        }),
        1 => prop::array::uniform32(any::<u8>()).prop_map(|mut k| {
            k[31] |= 0x80;
            k
        }),
    ]
}

fn honest_key() -> impl Strategy<Value = [u8; 32]> {
    prop::array::uniform32(any::<u8>())
        .prop_map(|s| PublicKey::from(&StaticSecret::from(s)).to_bytes())
}

/// A pool of keys, a presented key's index into it, and up to five records whose
/// sets are lists of indices into it (duplicates included).
type Case = (Vec<[u8; 32]>, usize, Vec<(Vec<usize>, Vec<usize>)>);

fn records_case() -> impl Strategy<Value = Case> {
    prop::collection::vec(pool_key(), 1..7).prop_flat_map(|pool| {
        let n = pool.len();
        let set = prop::collection::vec(0..n, 0..4);
        (
            Just(pool),
            0..n,
            prop::collection::vec((set.clone(), set), 0..6),
        )
    })
}

fn build(pool: &[[u8; 32]], sets: &[(Vec<usize>, Vec<usize>)]) -> Vec<Record> {
    let key = |i: &usize| PublicKeyBytes::from_bytes(pool[*i]);
    sets.iter()
        .map(|(c, r)| Record::new(c.iter().map(key).collect(), r.iter().map(key).collect()))
        .collect()
}

/// The page's classification, written from its list.
fn reference_classify(k: &[u8; 32], record: &Record) -> Result<KeyClass, ClassifyError> {
    if let Some(r) = refusal(k) {
        return Err(ClassifyError::Key(r));
    }
    let all = record.current.iter().chain(record.retired.iter());
    if all.clone().any(|m| !canonical(m.as_bytes())) {
        return Err(ClassifyError::MalformedRecord);
    }
    if record.retired.iter().any(|m| m.as_bytes() == k) {
        Ok(KeyClass::Retired)
    } else if record.current.iter().any(|m| m.as_bytes() == k) {
        Ok(KeyClass::Same)
    } else {
        Ok(KeyClass::New)
    }
}

/// `n mod 10^60` of a big-endian 32-byte number as 60 ASCII digits, by Horner's rule
/// on a little-endian array of decimal digits that keeps only the low 60 (reduction
/// mod 10^60 commutes with each multiply-and-add).
fn reference_number(digest: &[u8; 32]) -> [u8; 60] {
    let mut digits = [0u32; 60]; // least significant first
    for byte in digest {
        let mut carry = *byte as u32;
        for d in digits.iter_mut() {
            let v = *d * 256 + carry;
            *d = v % 10;
            carry = v / 10;
        }
    }
    let mut out = [0u8; 60];
    for (i, d) in digits.iter().enumerate() {
        out[59 - i] = b'0' + *d as u8;
    }
    out
}

proptest! {
    #![proptest_config(config())]

    /// For two identity keys, the digest is `SHA-256(PAIR_DIGEST_LABEL || lo || hi)`
    /// with the keys ordered as strings of unsigned bytes, byte 0 first; so it is the
    /// same in either argument order, and equal keys are allowed.
    ///
    /// Specification: identities-and-devices.md, The identity pair digest:
    /// "`(lo, hi) = (k1, k2) if k1 <= k2, else (k2, k1)`", "`return SHA-256(PAIR_DIGEST_LABEL
    /// || lo || hi)`", "`k1 <= k2` compares the keys as strings of unsigned bytes, byte 0
    /// first" and "**Equal keys** are allowed."
    #[test]
    fn the_digest_is_the_pages_hash_of_the_sorted_pair(
        a in honest_key(),
        b in honest_key(),
        same in any::<bool>(),
    ) {
        let b = if same { a } else { b };
        let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
        let mut h = Sha256::new();
        h.update(LABEL);
        h.update(lo);
        h.update(hi);
        let expected: [u8; 32] = h.finalize().into();
        let ka = PublicKeyBytes::from_bytes(a);
        let kb = PublicKeyBytes::from_bytes(b);
        prop_assert_eq!(identity_pair_digest(&ka, &kb), Ok(expected));
        prop_assert_eq!(identity_pair_digest(&kb, &ka), Ok(expected));
    }

    /// The digest refuses a pair exactly when one of its keys fails the identity-key
    /// rule, with a decode failure for a non-canonical key and an invalid identity key
    /// for a canonical key that is not one; when only one key is refused, the refusal
    /// is that key's; it refuses nothing else.
    ///
    /// Specification: identities-and-devices.md, The identity pair digest: "a key whose
    /// bit 255 is set, or whose value, read little-endian, is at least p = 2^255 - 19, is
    /// refused as `DecodeEC` refuses it", "a canonical key that is not an identity key
    /// is refused as an invalid identity key", and "It refuses nothing else. When both
    /// keys would be refused, either refusal conforms."
    #[test]
    fn the_digest_refuses_exactly_what_the_rule_refuses(a in pool_key(), b in pool_key()) {
        let got = identity_pair_digest(&PublicKeyBytes::from_bytes(a), &PublicKeyBytes::from_bytes(b));
        match (refusal(&a), refusal(&b)) {
            (None, None) => prop_assert!(got.is_ok()),
            (Some(r), None) | (None, Some(r)) => prop_assert_eq!(got, Err(r)),
            (Some(ra), Some(rb)) => {
                let e = got.expect_err("both keys are refused");
                prop_assert!(e == ra || e == rb);
            }
        }
    }

    /// The verification number of a 32-byte digest is the digest read as an unsigned
    /// big-endian integer, reduced mod 10^60, as 60 ASCII digits, most significant
    /// first, left-padded with '0'; the grouped form is those 60 digits unchanged in
    /// twelve groups of five.
    ///
    /// Specification: identities-and-devices.md, The verification number: "`n = digest
    /// read as an unsigned big-endian integer`", "`return n mod 10^60, as the ASCII
    /// digits 0 to 9, most significant first, left-padded with '0' to 60 digits`" and
    /// "For display they may be laid out in twelve groups of five". The page leaves the
    /// separator to the application; the single space checked here is this
    /// implementation's.
    #[test]
    fn the_number_is_the_digest_mod_ten_to_the_sixty(
        digest in prop_oneof![
            prop::array::uniform32(any::<u8>()),
            // Small values, so that the left padding is exercised.
            prop::array::uniform32(any::<u8>()).prop_map(|mut d| {
                for b in d.iter_mut().take(26) {
                    *b = 0;
                }
                d
            }),
        ],
    ) {
        let number = verification_number(&digest);
        prop_assert_eq!(number, reference_number(&digest));
        prop_assert!(number.iter().all(u8::is_ascii_digit));
        let grouped = verification_number_grouped(&number);
        let groups: Vec<&[u8]> = grouped.split(|b| *b == b' ').collect();
        prop_assert_eq!(groups.len(), 12);
        prop_assert!(groups.iter().all(|g| g.len() == 5));
        prop_assert_eq!(groups.concat(), number.to_vec(), "the digits are unchanged");
    }

    /// Classification against one record is the page's: the presented key is held to
    /// the identity-key rule first; then any non-canonical member refuses the record as
    /// malformed, even when the key matches another member; otherwise retired if in
    /// the retired set, else same if in the current set, else new, by byte equality.
    ///
    /// Specification: session-establishment.md, Records, expectations and attribution,
    /// Classification: "Before anything else, `k` must be an identity key", "If any of
    /// them is not a canonical encoding, it refuses the classification as a malformed
    /// record (`MalformedRecord`), even if `k` matches another member" and "*retired*,
    /// if it is in the retired set; otherwise *same*, if it is in the current set;
    /// otherwise *new*."
    #[test]
    fn classification_is_the_pages((pool, at, sets) in records_case()) {
        let records = build(&pool, &sets);
        let key = PublicKeyBytes::from_bytes(pool[at]);
        for record in &records {
            prop_assert_eq!(classify(&key, record), reference_classify(&pool[at], record));
        }
        prop_assert_eq!(
            classify(&key, &Record::default()),
            reference_classify(&pool[at], &Record::default())
        );
    }

    /// The lookup is the classification against every record: a key the rule refuses
    /// refuses the lookup the same way whatever the records; otherwise malformed
    /// records are skipped and reported, the records that classify the key as same and
    /// as retired are reported, and the attribution is the contact when same for
    /// exactly one, ambiguous when same for more than one, a retired key when same for
    /// none and retired for some, and unattributed otherwise.
    ///
    /// Specification: session-establishment.md, Records, expectations and attribution,
    /// Lookup: "A key is looked up by classifying it against every record the party
    /// holds", "A record whose classification is refused as a malformed record is
    /// skipped: it attributes nothing, and it is reported", and the four cases "*same*
    /// for exactly one contact" to "*same* for none and *retired* for none". The page
    /// makes the two lists sets; the order checked here (record order) is this
    /// implementation's.
    #[test]
    fn the_lookup_is_the_classification_against_every_record((pool, at, sets) in records_case()) {
        let records = build(&pool, &sets);
        let key = PublicKeyBytes::from_bytes(pool[at]);
        let got = lookup(&key, &records);
        if let Some(r) = refusal(&pool[at]) {
            prop_assert_eq!(got, Err(r));
            prop_assert_eq!(lookup(&key, &[]), Err(r));
            return Ok(());
        }
        let got = got.expect("an identity key is looked up");
        let (mut same, mut retired, mut malformed) = (vec![], vec![], vec![]);
        for (i, record) in records.iter().enumerate() {
            match reference_classify(&pool[at], record) {
                Ok(KeyClass::Same) => same.push(i),
                Ok(KeyClass::Retired) => retired.push(i),
                Ok(KeyClass::New) => {}
                Err(ClassifyError::MalformedRecord) => malformed.push(i),
                Err(e) => prop_assert!(false, "a refused key reached the records: {:?}", e),
            }
        }
        let attribution = match same.len() {
            1 => Attribution::Contact(same[0]),
            0 if !retired.is_empty() => Attribution::RetiredKey,
            0 => Attribution::Unattributed,
            _ => Attribution::Ambiguous,
        };
        prop_assert_eq!(got.attribution, attribution);
        prop_assert_eq!(got.same_for, same);
        prop_assert_eq!(got.retired_for, retired);
        prop_assert_eq!(got.malformed, malformed);
    }
}
