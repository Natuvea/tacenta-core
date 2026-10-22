//! Identity records, the identity pair digest and the initiator's
//! expectation, driven with attacker-chosen keys and records.
//!
//! A presented identity key comes from a peer's bundle or initial message, so
//! an attacker chooses it. The records are the party's own, but they are
//! decoded from storage an application keeps, so they are treated as
//! untrusted bytes here too. The input is read as a presented key, a second
//! key for the pair digest, and a list of records whose members are either
//! raw 32-byte keys or picks from a small pool (the presented key, the bundle
//! owner's real identity key, an RFC 7748 key, its torsion twin, u = 0 and two
//! non-canonical encodings), so that *same* and *retired* are reached and not
//! only *new*.
//!
//! Panic-freedom is one property; the others are oracles the functions'
//! documentation states:
//! - `lookup` agrees with `classify` record by record, and its attribution
//!   follows from how many records give *same* and *retired*;
//! - the pair digest is the same in either argument order, and its
//!   verification number is 60 ASCII digits whose grouped layout keeps them;
//! - `establish_initiator` refuses a malformed expectation as
//!   `MalformedRecord` and only then, never surfaces the leaf's
//!   `UnexpectedIdentity`, draws nothing before refusing on the expectation,
//!   and returns a session only for a key the expectation accepts.

#![no_main]

use libfuzzer_sys::fuzz_target;
use rand::SeedableRng;
use rand_core::{CryptoRng, RngCore};
use tacenta_core::primitives::dh::PublicKeyBytes;
use tacenta_core::sessions::identity::{
    Attribution, ClassifyError, Expectation, InitiatorError, KeyClass, Record, classify,
    establish_initiator, identity_pair_digest, lookup, verification_number,
    verification_number_grouped,
};
use tacenta_core::sessions::{Identity, LifecycleError};

/// A random generator that counts the bytes drawn from it.
struct Counting {
    inner: rand::rngs::StdRng,
    drawn: usize,
}

impl RngCore for Counting {
    fn next_u32(&mut self) -> u32 {
        self.drawn += 4;
        self.inner.next_u32()
    }
    fn next_u64(&mut self) -> u64 {
        self.drawn += 8;
        self.inner.next_u64()
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.drawn += dest.len();
        self.inner.fill_bytes(dest)
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.drawn += dest.len();
        self.inner.try_fill_bytes(dest)
    }
}

impl CryptoRng for Counting {}

/// RFC 7748 section 6.1, Alice's public key, and that key plus a point of
/// order 8 (canonical, not an identity key).
const RFC7748_ALICE: [u8; 32] = [
    0x85, 0x20, 0xf0, 0x09, 0x89, 0x30, 0xa7, 0x54, 0x74, 0x8b, 0x7d, 0xdc, 0xb4, 0x3e, 0xf7, 0x5a,
    0x0d, 0xbf, 0x3a, 0x0d, 0x26, 0x38, 0x1a, 0xf4, 0xeb, 0xa4, 0xa9, 0x8e, 0xaa, 0x9b, 0x4e, 0x6a,
];
const RFC7748_ALICE_PLUS_TORSION: [u8; 32] = [
    0xec, 0x06, 0xa1, 0x8b, 0x28, 0x51, 0x71, 0x7c, 0xba, 0xd4, 0xdd, 0xa9, 0x75, 0xda, 0xa1, 0x76,
    0xba, 0xef, 0x2f, 0x52, 0x03, 0x71, 0xe5, 0x1e, 0x53, 0x83, 0x02, 0x92, 0x72, 0x44, 0x88, 0x59,
];

/// Reads the input front to back; a read past the end gives zeros, so every
/// input parses.
struct Input<'a> {
    data: &'a [u8],
    at: usize,
}

impl Input<'_> {
    fn byte(&mut self) -> u8 {
        let b = self.data.get(self.at).copied().unwrap_or(0);
        self.at += 1;
        b
    }

    fn key(&mut self) -> PublicKeyBytes {
        let mut out = [0u8; 32];
        for b in out.iter_mut() {
            *b = self.byte();
        }
        PublicKeyBytes::from_bytes(out)
    }

    fn exhausted(&self) -> bool {
        self.at >= self.data.len()
    }
}

fuzz_target!(|data: &[u8]| {
    // Fixed seed: the budget belongs to the input, and a crash has to minimise
    // to something reproducible.
    let mut setup = rand::rngs::StdRng::seed_from_u64(0);
    let alice = Identity::generate(&mut setup);
    let bob = Identity::generate(&mut setup);

    let mut input = Input { data, at: 0 };
    let flags = input.byte();
    let presented = input.key();
    let other = input.key();

    let mut u_p = [0xffu8; 32];
    u_p[0] = 0xed;
    u_p[31] = 0x7f;
    let pool = [
        presented,
        bob.public(),
        PublicKeyBytes::from_bytes(RFC7748_ALICE),
        PublicKeyBytes::from_bytes(RFC7748_ALICE_PLUS_TORSION),
        PublicKeyBytes::from_bytes([0u8; 32]),
        PublicKeyBytes::from_bytes(u_p),
        PublicKeyBytes::from_bytes([0xffu8; 32]),
    ];

    // Up to eight records of up to four members in each set. A member is a
    // pool pick for a tag below 0x80, otherwise 32 raw bytes.
    let mut records: Vec<Record> = Vec::new();
    let count = (input.byte() % 9) as usize;
    while records.len() < count && !input.exhausted() {
        let sizes = input.byte();
        let mut sets = [Vec::new(), Vec::new()];
        for (n, set) in [(sizes & 0x0f) % 5, (sizes >> 4) % 5]
            .into_iter()
            .zip(sets.iter_mut())
        {
            for _ in 0..n {
                let tag = input.byte();
                if tag < 0x80 {
                    set.push(pool[tag as usize % pool.len()]);
                } else {
                    set.push(input.key());
                }
            }
        }
        let [current, retired] = sets;
        records.push(Record::new(current, retired));
    }

    // The pair digest, in both orders, and its number.
    let forward = identity_pair_digest(&presented, &other);
    let backward = identity_pair_digest(&other, &presented);
    assert_eq!(
        forward.is_ok(),
        backward.is_ok(),
        "the digest's verdict depends on order"
    );
    if let (Ok(a), Ok(b)) = (forward, backward) {
        assert_eq!(a, b, "the digest depends on argument order");
    }
    let raw: [u8; 32] = *other.as_bytes();
    for d in [forward.ok(), Some(raw)].into_iter().flatten() {
        let number = verification_number(&d);
        assert!(
            number.iter().all(u8::is_ascii_digit),
            "a verification number digit is not a digit"
        );
        let grouped = verification_number_grouped(&number);
        for (i, &c) in grouped.iter().enumerate() {
            if i % 6 == 5 {
                assert_eq!(c, b' ', "a group separator is not a space");
            } else {
                assert_eq!(c, number[i - i / 6], "grouping changed a digit");
            }
        }
    }

    // The classification of each record, and the lookup across them.
    let mut classes = Vec::with_capacity(records.len());
    for record in &records {
        classes.push(classify(&presented, record));
    }
    match lookup(&presented, &records) {
        Err(refusal) => {
            for class in &classes {
                assert_eq!(
                    *class,
                    Err(ClassifyError::Key(refusal)),
                    "lookup and classify disagree on the key"
                );
            }
        }
        Ok(found) => {
            let mut same = Vec::new();
            let mut retired = Vec::new();
            let mut malformed = Vec::new();
            for (i, class) in classes.iter().enumerate() {
                match class {
                    Ok(KeyClass::Same) => same.push(i),
                    Ok(KeyClass::Retired) => retired.push(i),
                    Ok(KeyClass::New) => {}
                    Err(ClassifyError::MalformedRecord) => malformed.push(i),
                    Err(refusal) => {
                        panic!("classify refused the key the lookup accepted: {refusal:?}")
                    }
                }
            }
            assert_eq!(found.same_for, same, "same_for");
            assert_eq!(found.retired_for, retired, "retired_for");
            assert_eq!(found.malformed, malformed, "malformed");
            let expected = match same.len() {
                1 => Attribution::Contact(same[0]),
                0 if !retired.is_empty() => Attribution::RetiredKey,
                0 => Attribution::Unattributed,
                _ => Attribution::Ambiguous,
            };
            assert_eq!(found.attribution, expected, "attribution");
        }
    }

    // The expectation wrapper, over Bob's honest bundle with its identity key
    // replaced by the presented key when the low flag bit is set.
    let mut bundle = bob.create_prekeys(1, &mut setup).publish();
    if flags & 1 == 1 {
        bundle.bundle.identity_key = presented;
    }
    let bundle_key = bundle.bundle.identity_key;
    let empty = Record::default();
    let expectation = if flags & 2 == 2 {
        Expectation::known(records.first().unwrap_or(&empty))
    } else {
        Expectation::first_contact(&records)
    };
    let mut rng = Counting {
        inner: rand::rngs::StdRng::seed_from_u64(1),
        drawn: 0,
    };
    let result = establish_initiator(&alice, &bundle, &expectation, &mut rng);
    assert_eq!(
        expectation.is_malformed(),
        result.as_ref().err() == Some(&InitiatorError::MalformedRecord),
        "a malformed expectation and the MalformedRecord refusal disagree"
    );
    match &result {
        Err(InitiatorError::MalformedRecord)
        | Err(InitiatorError::UnexpectedIdentity)
        | Err(InitiatorError::RetiredIdentity) => {
            assert_eq!(rng.drawn, 0, "a refusal on the expectation drew randomness");
        }
        Err(InitiatorError::Establish(LifecycleError::UnexpectedIdentity)) => {
            panic!("the leaf's named-identity refusal reached the caller");
        }
        Err(_) => {}
        Ok(session) => {
            assert_eq!(
                session.peer_identity(),
                bundle_key,
                "the session's peer is not the bundle's key"
            );
            assert!(
                session.invariant(),
                "an established session violates its invariant"
            );
            match expectation {
                Expectation::Known { record, .. } => {
                    assert_eq!(
                        classify(&bundle_key, record),
                        Ok(KeyClass::Same),
                        "known accepted a key that is not same"
                    );
                }
                Expectation::FirstContact { records, .. } => {
                    let found = lookup(&bundle_key, records)
                        .expect("an established peer key is an identity key");
                    assert!(
                        found.same_for.is_empty() && found.retired_for.is_empty(),
                        "first contact accepted a recorded or retired key"
                    );
                }
                _ => {}
            }
        }
    }
});
