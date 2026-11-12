//! Property tests for the three identity-record functions that establish or
//! attribute a session: `establish_initiator` under an expectation,
//! `establish_responder_unattributed` and `Unattributed::attribute`, against
//! `tacenta-spec/protocol/session-establishment.md`, Records, expectations and
//! attribution.
//!
//! Generator: for each of `RUNS` runs, `StdRng::seed_from_u64(SEED + run)` makes three
//! identities (the initiator, the responder, a third party), a prekey store for the
//! responder, and `RECORD_SETS` sets of up to four records whose members are drawn
//! from a pool of the three identity keys and a non-canonical spelling, so that the
//! responder's key falls *same*, *retired*, *new*, in several records, and in malformed
//! ones. The expected outcome is written here from the page's lists, with the
//! classification and the lookup also written out from the page (as in
//! `tests/identity_records_properties.rs`), not taken from the crate: both tests use
//! this file's `class` and `reference_lookup`.
//!
//! Replay: the seed is fixed in this file, and every assertion message names the run
//! and the record set. Case count: `RUNS` (24) runs of `RECORD_SETS` (40) record sets,
//! each under *first contact* and, when the set holds a record (about four times in
//! five), under *known* with one of its records; and `RESPONDER_RUNS` (96) responder
//! establishments, each attributed against one generated record set.

use rand::{Rng, SeedableRng, rngs::StdRng};
use rand_core::{CryptoRng, RngCore};
use tacenta_core::primitives::dh::PublicKeyBytes;
use tacenta_core::sessions::identity::{
    Attribution, Expectation, InitiatorError, Record, establish_initiator,
    establish_responder_unattributed,
};
use tacenta_core::sessions::{Identity, PrekeyStore, establish_responder};

const SEED: u64 = 0x1d_7e57;
const RUNS: u64 = 24;
const RECORD_SETS: usize = 40;
const RESPONDER_RUNS: u64 = 96;

/// A random generator that counts the bytes drawn from it.
struct Counting {
    inner: StdRng,
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

#[derive(Clone, Copy, PartialEq, Debug)]
enum Class {
    Retired,
    Same,
    New,
    Malformed,
}

fn canonical(k: &[u8; 32]) -> bool {
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

/// The page's classification of an identity key against one record.
fn class(k: &PublicKeyBytes, r: &Record) -> Class {
    if r.current
        .iter()
        .chain(&r.retired)
        .any(|m| !canonical(m.as_bytes()))
    {
        Class::Malformed
    } else if r.retired.contains(k) {
        Class::Retired
    } else if r.current.contains(k) {
        Class::Same
    } else {
        Class::New
    }
}

/// The page's expectation outcome for a bundle whose identity key `k` is an identity
/// key: `None` when establishment goes on.
fn expected_refusal(
    k: &PublicKeyBytes,
    known: Option<&Record>,
    all: &[Record],
) -> Option<InitiatorError> {
    match known {
        Some(r) => {
            if r.current.is_empty() && r.retired.is_empty() {
                return Some(InitiatorError::MalformedRecord);
            }
            match class(k, r) {
                Class::Malformed => Some(InitiatorError::MalformedRecord),
                Class::Retired => Some(InitiatorError::RetiredIdentity),
                Class::New => Some(InitiatorError::UnexpectedIdentity),
                Class::Same => None,
            }
        }
        None => {
            let classes: Vec<Class> = all.iter().map(|r| class(k, r)).collect();
            if classes.contains(&Class::Malformed) {
                Some(InitiatorError::MalformedRecord)
            } else if classes.contains(&Class::Same) {
                Some(InitiatorError::UnexpectedIdentity)
            } else if classes.contains(&Class::Retired) {
                Some(InitiatorError::RetiredIdentity)
            } else {
                None
            }
        }
    }
}

/// The page's lookup of an identity key, written from its list: the records that
/// classify the key as same, as retired, and the malformed ones skipped, in record
/// order, and the attribution they decide.
fn reference_lookup(
    k: &PublicKeyBytes,
    records: &[Record],
) -> (Attribution, Vec<usize>, Vec<usize>, Vec<usize>) {
    let (mut same, mut retired, mut malformed) = (vec![], vec![], vec![]);
    for (i, r) in records.iter().enumerate() {
        match class(k, r) {
            Class::Same => same.push(i),
            Class::Retired => retired.push(i),
            Class::New => {}
            Class::Malformed => malformed.push(i),
        }
    }
    let attribution = match same.len() {
        1 => Attribution::Contact(same[0]),
        0 if !retired.is_empty() => Attribution::RetiredKey,
        0 => Attribution::Unattributed,
        _ => Attribution::Ambiguous,
    };
    (attribution, same, retired, malformed)
}

fn record_set(r: &mut StdRng, pool: &[PublicKeyBytes]) -> Vec<Record> {
    let count = r.gen_range(0..5);
    (0..count)
        .map(|_| {
            let mut set = || {
                let n = r.gen_range(0..3);
                (0..n)
                    .map(|_| pool[r.gen_range(0..pool.len())])
                    .collect::<Vec<_>>()
            };
            let current = set();
            let retired = set();
            Record::new(current, retired)
        })
        .collect()
}

/// Under *known* and under *first contact*, `establish_initiator` refuses exactly as
/// the page's lists say, draws nothing from the generator when it refuses for the
/// expectation, and otherwise returns a session whose peer identity key is the
/// bundle's.
///
/// Specification: session-establishment.md, Records, expectations and attribution,
/// The initiator: "She refuses an expectation as a malformed record (`MalformedRecord`)
/// ... when it holds a non-canonical key ... or when it is *known* with a record whose
/// two sets are both empty"; "under *known*, by classifying it against that record.
/// *Retired* is refused as a retired identity (`RetiredIdentity`). *New* is refused as
/// an unexpected identity (`UnexpectedIdentity`). *Same* goes on"; "under *first
/// contact*, by looking it up in her records: a key the lookup finds a contact's, or
/// ambiguous, is refused as an unexpected identity ... a retired key (*same* for no
/// contact) is refused as a retired identity ... an unattributed key goes on"; and "A
/// bundle refused for its identity key is refused as such ... Nothing is verified,
/// drawn, computed or sent for it."
#[test]
fn the_initiator_refuses_exactly_as_the_expectation_says() {
    let (mut refused, mut established) = (0usize, 0usize);
    for run in 0..RUNS {
        let mut r = StdRng::seed_from_u64(SEED + run);
        let alice = Identity::generate(&mut r);
        let bob = Identity::generate(&mut r);
        let carol = Identity::generate(&mut r);
        let mut bad = *bob.public().as_bytes();
        bad[31] |= 0x80;
        let pool = [
            bob.public(),
            carol.public(),
            alice.public(),
            PublicKeyBytes::from_bytes(bad),
        ];
        let bundle = bob.create_prekeys(1, &mut r).publish();
        for set in 0..RECORD_SETS {
            let records = record_set(&mut r, &pool);
            let pick = if records.is_empty() {
                None
            } else {
                Some(r.gen_range(0..records.len()))
            };
            let mut cases: Vec<(Option<&Record>, Expectation)> =
                vec![(None, Expectation::first_contact(&records))];
            if let Some(i) = pick {
                cases.push((Some(&records[i]), Expectation::known(&records[i])));
            }
            for (known, expectation) in cases {
                let want = expected_refusal(&bob.public(), known, &records);
                let mut g = Counting {
                    inner: StdRng::seed_from_u64(r.r#gen()),
                    drawn: 0,
                };
                let got = establish_initiator(&alice, &bundle, &expectation, &mut g);
                match (want, got) {
                    (Some(w), Err(e)) => {
                        assert_eq!(e, w, "run {run} set {set}: refusal");
                        assert_eq!(g.drawn, 0, "run {run} set {set}: drew before refusing");
                        refused += 1;
                    }
                    (None, Ok(session)) => {
                        assert_eq!(session.peer_identity(), bob.public(), "run {run} set {set}");
                        established += 1;
                    }
                    (w, g) => panic!("run {run} set {set}: expected {w:?}, got {:?}", g.err()),
                }
            }
        }
    }
    assert!(
        refused > 100 && established > 100,
        "refused {refused}, established {established}"
    );
}

/// The responder's wrapper establishes exactly as the leaf `establish_responder` does
/// (the same session bytes and plaintext from the same generator and store), its
/// value carries the initiator's identity key, and `attribute` releases the first
/// plaintext beside a lookup of that key in whatever records it is given, with no
/// record consulted before. The expected lookup is this file's `reference_lookup`,
/// written from the page's list; across the runs all four attributions occur.
///
/// Specification: session-establishment.md, Records, expectations and attribution,
/// Attribution: "A session is a contact's only when a lookup of its peer identity key
/// finds it that contact's" and "Every plaintext and control payload a session yields
/// is attributed exactly as the session is, and no more."; Lookup (the four cases and
/// the reported lists).
#[test]
fn the_responders_first_plaintext_is_attributed_as_its_session() {
    let mut kinds = [0usize; 4];
    for run in 0..RESPONDER_RUNS {
        let mut r = StdRng::seed_from_u64(SEED ^ 0xa77 ^ run);
        let alice = Identity::generate(&mut r);
        let bob = Identity::generate(&mut r);
        let carol = Identity::generate(&mut r);
        let mut store = bob.create_prekeys(2, &mut r);
        let text: Vec<u8> = (0..r.gen_range(0..64)).map(|_| r.r#gen()).collect();
        let mut sender = establish_initiator(
            &alice,
            &store.publish(),
            &Expectation::first_contact(&[]),
            &mut r,
        )
        .unwrap();
        let initial = sender.encrypt(&text, &mut r).unwrap();
        let mut leaf_store = PrekeyStore::from_bytes(&store.to_bytes()).unwrap();
        let seed: u64 = r.r#gen();
        let (session, first) = establish_responder_unattributed(
            &bob,
            &mut store,
            &initial,
            &mut StdRng::seed_from_u64(seed),
        )
        .unwrap_or_else(|e| panic!("run {run}: {e:?}"));
        let (leaf_session, leaf_text) = establish_responder(
            &bob,
            &mut leaf_store,
            &initial,
            &mut StdRng::seed_from_u64(seed),
        )
        .unwrap();
        assert_eq!(
            &session.export()[..],
            &leaf_session.export()[..],
            "run {run}: session"
        );
        assert_eq!(
            store.to_bytes().to_vec(),
            leaf_store.to_bytes().to_vec(),
            "run {run}: store"
        );
        assert_eq!(first.peer_identity(), alice.public(), "run {run}");
        assert_eq!(session.peer_identity(), alice.public(), "run {run}");
        let mut bad = *alice.public().as_bytes();
        bad[31] |= 0x80;
        let pool = [
            alice.public(),
            carol.public(),
            bob.public(),
            PublicKeyBytes::from_bytes(bad),
        ];
        let records = record_set(&mut r, &pool);
        let (attribution, same, retired, malformed) = reference_lookup(&alice.public(), &records);
        let (found, plaintext) = first.attribute(&records).unwrap();
        assert_eq!(found.attribution, attribution, "run {run}: attribution");
        assert_eq!(found.same_for, same, "run {run}: same");
        assert_eq!(found.retired_for, retired, "run {run}: retired");
        assert_eq!(found.malformed, malformed, "run {run}: malformed");
        assert_eq!(plaintext, leaf_text, "run {run}: plaintext");
        assert_eq!(plaintext, text, "run {run}: plaintext");
        kinds[match found.attribution {
            Attribution::Contact(_) => 0,
            Attribution::Ambiguous => 1,
            Attribution::RetiredKey => 2,
            Attribution::Unattributed => 3,
        }] += 1;
    }
    assert!(
        kinds.iter().all(|k| *k > 0),
        "attributions reached: {kinds:?}"
    );
}
