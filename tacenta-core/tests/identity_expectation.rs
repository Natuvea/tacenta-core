//! The initiator's expectation (session-establishment.md, Records,
//! expectations and attribution; REQ-AUTH-02).
//!
//! The adversary is a directory that serves a bundle under an identity key
//! the initiator did not mean to reach: a substitute signed under its own
//! key, a contact's retired key, another contact's key, or a key that is not
//! an identity key at all, possibly with defects elsewhere in the bundle that
//! a later check would also refuse. Every case asserts the refusal kind the
//! page names, not only that something failed, and every refusal before the
//! signatures is asserted to draw nothing from the random generator.
//!
//! The order the page fixes is checked by bundles that fail two checks at
//! once: a malformed expectation wins over everything; the presence and
//! canonical-key checks win over the expectation; the identity-key rule,
//! applied by the expectation check, wins over a retired or unexpected
//! identity; and the expectation wins over the signatures, the KEM prekey's
//! input checks and the agreements.
//!
//! Finally, with no records, establishment under first contact is the
//! lifecycle leaf's establishment exactly: the same session bytes or the same
//! refusal, from the same random generator, over honest and refused bundles.

use rand::SeedableRng;
use rand_core::{CryptoRng, RngCore};
use tacenta_core::primitives::{dh, xeddsa};
use tacenta_core::sessions::identity::{
    Attribution, Expectation, InitiatorError, Record, establish_initiator, lookup,
};
use tacenta_core::sessions::{
    Identity, LifecycleError, PublishedBundle, SessionError, encode_ec, encode_kem,
    establish_responder,
};

/// A random generator that counts the bytes drawn from it.
struct Counting {
    inner: rand::rngs::StdRng,
    drawn: usize,
}

impl Counting {
    fn new(seed: u64) -> Counting {
        Counting {
            inner: rand::rngs::StdRng::seed_from_u64(seed),
            drawn: 0,
        }
    }
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

fn key(text: &str) -> dh::PublicKeyBytes {
    let bytes: [u8; 32] = hex::decode(text).unwrap().try_into().unwrap();
    dh::PublicKeyBytes::from_bytes(bytes)
}

/// RFC 7748 section 6.1, Alice's private key. Its public key is
/// `8520f009...4e6a`, so the torsion twin below is known.
const RFC7748_ALICE_SECRET: &str =
    "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a";
const RFC7748_ALICE_PUBLIC: &str =
    "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a";
/// That public key plus a point of order 8: canonical, the same X25519
/// agreement under a clamped scalar, and not an identity key.
const RFC7748_ALICE_PLUS_TORSION: &str =
    "ec06a18b2851717cbad4dda975daa176baef2f520371e51e5383029272448859";

/// Canonical keys that are not identity keys: u = 0, u = 1, u = p - 1, the
/// two points of order 8, and u = 2, which lies on the twist.
const NOT_IDENTITY_KEYS: &[(&str, &str)] = &[
    (
        "u-0",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ),
    (
        "u-1",
        "0100000000000000000000000000000000000000000000000000000000000000",
    ),
    (
        "u-p-minus-1",
        "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
    ),
    (
        "order-8-a",
        "e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800",
    ),
    (
        "order-8-b",
        "5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157",
    ),
    (
        "u-2",
        "0200000000000000000000000000000000000000000000000000000000000000",
    ),
];

const U0: &str = "0000000000000000000000000000000000000000000000000000000000000000";
/// u = p: not a canonical encoding.
const U_P: &str = "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f";

/// The parties. `bob` is K (the key Alice means to reach), `mallory` is K'
/// (a substitute), `old` is K_old (a key Bob replaced), `dave` is K_D
/// (another contact), `stranger` is K'' (a peer in no record).
struct World {
    alice: Identity,
    bob: Identity,
    mallory: Identity,
    old: Identity,
    dave: Identity,
    stranger: Identity,
}

fn world() -> World {
    let mut rng = rand::rngs::StdRng::seed_from_u64(0x1d);
    let secret: [u8; 32] = hex::decode(RFC7748_ALICE_SECRET)
        .unwrap()
        .try_into()
        .unwrap();
    let bob = Identity::from_secret(secret);
    assert_eq!(bob.public(), key(RFC7748_ALICE_PUBLIC));
    World {
        alice: Identity::generate(&mut rng),
        bob,
        mallory: Identity::generate(&mut rng),
        old: Identity::generate(&mut rng),
        dave: Identity::generate(&mut rng),
        stranger: Identity::generate(&mut rng),
    }
}

/// A bundle published by `owner`, with a one-time curve prekey.
fn bundle_of(owner: &Identity, seed: u64) -> PublishedBundle {
    let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
    owner.create_prekeys(2, &mut rng).publish()
}

fn current(keys: &[dh::PublicKeyBytes]) -> Record {
    Record::new(keys.to_vec(), Vec::new())
}

fn with_bad_signed_prekey_signature(mut b: PublishedBundle) -> PublishedBundle {
    b.bundle.signed_prekey_signature[0] ^= 1;
    b
}

fn with_bad_kem_prekey_signature(mut b: PublishedBundle) -> PublishedBundle {
    b.bundle.kem_prekey_signature[0] ^= 1;
    b
}

fn with_identity_key(mut b: PublishedBundle, identity: dh::PublicKeyBytes) -> PublishedBundle {
    b.bundle.identity_key = identity;
    b
}

/// The one-time curve prekey removed but its identifier kept: a bundle the
/// decoder would never return, whose presence check fails.
fn with_inconsistent_presence(mut b: PublishedBundle) -> PublishedBundle {
    assert_ne!(b.one_time_prekey_id, 0);
    b.bundle.one_time_prekey = None;
    b
}

/// A full-length KEM prekey whose first coefficient is 4095, which fails the
/// ByteEncode12 round trip, signed again under `signer` so that only the KEM
/// input check refuses it.
fn with_unencodable_kem_prekey(mut b: PublishedBundle, signer: &Identity) -> PublishedBundle {
    b.bundle.kem_prekey[0] = 0xff;
    b.bundle.kem_prekey[1] |= 0x0f;
    let mut rng = rand::rngs::StdRng::seed_from_u64(7);
    b.bundle.kem_prekey_signature = xeddsa::sign(
        &signer.export(),
        &encode_kem(&b.bundle.kem_prekey),
        &mut rng,
    );
    b
}

/// The low-order u = 0 as the one-time curve prekey (unsigned, so no
/// signature changes).
fn with_low_order_one_time_prekey(mut b: PublishedBundle) -> PublishedBundle {
    b.bundle.one_time_prekey = Some(key(U0));
    b
}

/// The low-order u = 0 as the signed prekey, signed again under `signer`.
fn with_low_order_signed_prekey(mut b: PublishedBundle, signer: &Identity) -> PublishedBundle {
    b.bundle.signed_prekey = key(U0);
    let mut rng = rand::rngs::StdRng::seed_from_u64(8);
    b.bundle.signed_prekey_signature = xeddsa::sign(
        &signer.export(),
        &encode_ec(&b.bundle.signed_prekey),
        &mut rng,
    );
    b
}

fn establish(
    w: &World,
    bundle: &PublishedBundle,
    expectation: &Expectation,
) -> (
    Result<tacenta_core::sessions::Session, InitiatorError>,
    usize,
) {
    let mut rng = Counting::new(99);
    let result = establish_initiator(&w.alice, bundle, expectation, &mut rng);
    (result, rng.drawn)
}

/// Asserts a refusal of the given kind that drew nothing.
fn refused_before_randomness(
    w: &World,
    bundle: &PublishedBundle,
    expectation: &Expectation,
    expected: InitiatorError,
    id: &str,
) {
    let (result, drawn) = establish(w, bundle, expectation);
    assert_eq!(result.err(), Some(expected), "{id}");
    assert_eq!(drawn, 0, "{id}: the refusal drew randomness");
}

fn invalid_identity_key() -> InitiatorError {
    InitiatorError::Establish(LifecycleError::Handshake(SessionError::InvalidIdentityKey))
}

/// Under *known*, the expected key establishes, and the session's peer is it.
#[test]
fn known_and_same_establishes() {
    let w = world();
    let rec = current(&[w.bob.public()]);
    let bundle = bundle_of(&w.bob, 1);
    let (result, _) = establish(&w, &bundle, &Expectation::known(&rec));
    let session = result.expect("the expected key establishes");
    assert_eq!(session.peer_identity(), w.bob.public());
}

/// A substitute bundle that verifies under its own key is refused as an
/// unexpected identity before any randomness is drawn, and it establishes
/// under first contact with no records, so only the expectation refuses it.
#[test]
fn known_and_new_is_an_unexpected_identity() {
    let w = world();
    let rec = current(&[w.bob.public()]);
    let substitute = bundle_of(&w.mallory, 2);
    assert!(
        establish(&w, &substitute, &Expectation::first_contact(&[]))
            .0
            .is_ok()
    );
    refused_before_randomness(
        &w,
        &substitute,
        &Expectation::known(&rec),
        InitiatorError::UnexpectedIdentity,
        "known, new",
    );
}

#[test]
fn known_and_retired_is_a_retired_identity() {
    let w = world();
    let rec = Record::new(vec![w.bob.public()], vec![w.old.public()]);
    refused_before_randomness(
        &w,
        &bundle_of(&w.old, 3),
        &Expectation::known(&rec),
        InitiatorError::RetiredIdentity,
        "known, retired",
    );
}

/// The expectation is checked before the signatures, the KEM prekey's input
/// checks and the agreements: a substitute with any of those defects is still
/// an unexpected identity. Under the expected key the same defects give their
/// own refusals, so the signatures and later checks still run.
#[test]
fn the_expectation_comes_before_the_signatures_and_the_kem_and_agreement_checks() {
    let w = world();
    let rec = current(&[w.bob.public()]);
    let known = Expectation::known(&rec);
    let substitutes = [
        (
            "bad signed-prekey signature",
            with_bad_signed_prekey_signature(bundle_of(&w.mallory, 4)),
        ),
        (
            "bad KEM-prekey signature",
            with_bad_kem_prekey_signature(bundle_of(&w.mallory, 4)),
        ),
        (
            "unencodable KEM prekey",
            with_unencodable_kem_prekey(bundle_of(&w.mallory, 4), &w.mallory),
        ),
        (
            "low-order one-time prekey",
            with_low_order_one_time_prekey(bundle_of(&w.mallory, 4)),
        ),
        (
            "low-order signed prekey",
            with_low_order_signed_prekey(bundle_of(&w.mallory, 4), &w.mallory),
        ),
    ];
    for (id, bundle) in &substitutes {
        refused_before_randomness(&w, bundle, &known, InitiatorError::UnexpectedIdentity, id);
    }

    // Under the expected key, each defect is reported as itself.
    let both_bad =
        with_bad_kem_prekey_signature(with_bad_signed_prekey_signature(bundle_of(&w.bob, 5)));
    refused_before_randomness(
        &w,
        &both_bad,
        &known,
        InitiatorError::Establish(LifecycleError::Handshake(
            SessionError::BadSignedPrekeySignature,
        )),
        "expected key, both signatures bad",
    );
    refused_before_randomness(
        &w,
        &with_bad_kem_prekey_signature(bundle_of(&w.bob, 5)),
        &known,
        InitiatorError::Establish(LifecycleError::Handshake(
            SessionError::BadKemPrekeySignature,
        )),
        "expected key, bad KEM-prekey signature",
    );
    let (kem, _) = establish(
        &w,
        &with_unencodable_kem_prekey(bundle_of(&w.bob, 5), &w.bob),
        &known,
    );
    assert_eq!(
        kem.err(),
        Some(InitiatorError::Establish(LifecycleError::Kem)),
        "expected key, unencodable KEM prekey"
    );
    for (id, bundle) in [
        (
            "expected key, low-order one-time prekey",
            with_low_order_one_time_prekey(bundle_of(&w.bob, 5)),
        ),
        (
            "expected key, low-order signed prekey",
            with_low_order_signed_prekey(bundle_of(&w.bob, 5), &w.bob),
        ),
    ] {
        let (result, _) = establish(&w, &bundle, &known);
        assert_eq!(
            result.err(),
            Some(InitiatorError::Establish(LifecycleError::Handshake(
                SessionError::NonContributoryAgreement
            ))),
            "{id}"
        );
    }
}

/// A malformed expectation is refused before any check of the bundle, so it
/// wins over a bad signature, a key that is not an identity key, a presence
/// disagreement and a non-canonical key, and it draws nothing.
#[test]
fn a_malformed_expectation_is_refused_first() {
    let w = world();
    let empty = Record::default();
    let bad_member = Record::new(vec![w.bob.public(), key(U_P)], Vec::new());
    let bad_retired = Record::new(vec![w.bob.public()], vec![key(U_P)]);
    let honest_other = current(&[w.dave.public()]);
    let first_contact_records = [honest_other.clone(), bad_member.clone()];
    let mut non_canonical_identity = bundle_of(&w.bob, 6);
    non_canonical_identity.bundle.identity_key = key(U_P);
    let bundles = [
        ("honest", bundle_of(&w.bob, 6)),
        (
            "bad signature",
            with_bad_signed_prekey_signature(bundle_of(&w.bob, 6)),
        ),
        (
            "identity u = 0",
            with_identity_key(bundle_of(&w.bob, 6), key(U0)),
        ),
        (
            "inconsistent presence",
            with_inconsistent_presence(bundle_of(&w.bob, 6)),
        ),
        ("non-canonical identity", non_canonical_identity),
    ];
    let expectations = [
        ("known, empty record", Expectation::known(&empty)),
        (
            "known, non-canonical current",
            Expectation::known(&bad_member),
        ),
        (
            "known, non-canonical retired",
            Expectation::known(&bad_retired),
        ),
        (
            "first contact, one non-canonical record",
            Expectation::first_contact(&first_contact_records),
        ),
    ];
    for (bundle_id, bundle) in &bundles {
        for (exp_id, expectation) in &expectations {
            refused_before_randomness(
                &w,
                bundle,
                expectation,
                InitiatorError::MalformedRecord,
                &format!("{exp_id}, {bundle_id}"),
            );
        }
    }
}

/// A canonical member that is not an identity key does not make a record
/// malformed, under either form.
#[test]
fn a_canonical_non_identity_member_is_not_malformed() {
    let w = world();
    let rec = current(&[w.bob.public(), key(U0)]);
    assert!(
        establish(&w, &bundle_of(&w.bob, 7), &Expectation::known(&rec))
            .0
            .is_ok(),
        "known with a u = 0 member"
    );
    let records = [current(&[key(U0)])];
    let (result, _) = establish(
        &w,
        &bundle_of(&w.stranger, 7),
        &Expectation::first_contact(&records),
    );
    let session = result.expect("first contact with a u = 0 member");
    let found = lookup(&session.peer_identity(), &records).unwrap();
    assert_eq!(found.attribution, Attribution::Unattributed);
    assert!(found.malformed.is_empty());
}

/// The bundle's identity key is held to the identity-key rule by the
/// expectation check, before it is compared: a key that is not an identity
/// key is an invalid identity key under *known* (even when it is a member of
/// the record, as a retired torsion twin) and under first contact, never a
/// retired or unexpected identity, and nothing is drawn. Signatures are left
/// as they are, so they would fail too.
#[test]
fn a_key_that_is_not_an_identity_key_is_refused_as_such_before_the_comparison() {
    let w = world();
    let twin = key(RFC7748_ALICE_PLUS_TORSION);
    let known = current(&[w.bob.public()]);
    let known_with_twin_retired = Record::new(vec![w.bob.public()], vec![twin]);
    let twin_bundle = with_identity_key(bundle_of(&w.bob, 8), twin);
    refused_before_randomness(
        &w,
        &twin_bundle,
        &Expectation::known(&known),
        invalid_identity_key(),
        "known, torsion twin",
    );
    refused_before_randomness(
        &w,
        &twin_bundle,
        &Expectation::known(&known_with_twin_retired),
        invalid_identity_key(),
        "known with the twin retired, torsion twin",
    );
    refused_before_randomness(
        &w,
        &twin_bundle,
        &Expectation::first_contact(&[]),
        invalid_identity_key(),
        "first contact, no records, torsion twin",
    );
    for (id, value) in NOT_IDENTITY_KEYS {
        let bundle =
            with_bad_signed_prekey_signature(with_identity_key(bundle_of(&w.bob, 8), key(value)));
        refused_before_randomness(
            &w,
            &bundle,
            &Expectation::known(&known),
            invalid_identity_key(),
            &format!("known, {id}"),
        );
        refused_before_randomness(
            &w,
            &bundle,
            &Expectation::first_contact(&[]),
            invalid_identity_key(),
            &format!("first contact, {id}"),
        );
        // A record holding the very bytes as a member does not change it.
        let holding = Record::new(vec![w.bob.public(), key(value)], vec![key(value)]);
        refused_before_randomness(
            &w,
            &bundle,
            &Expectation::first_contact(core::slice::from_ref(&holding)),
            invalid_identity_key(),
            &format!("first contact, {id} recorded"),
        );
    }
}

/// The presence and canonical-key checks come before the expectation, so a
/// bundle that fails one is reported as that, never as a retired or
/// unexpected identity, under every expectation that would refuse its key.
#[test]
fn retired_and_unexpected_are_never_reported_for_a_malformed_bundle() {
    let w = world();
    let known_bob = current(&[w.bob.public()]);
    let known_retired = Record::new(vec![w.bob.public()], vec![w.mallory.public()]);
    let records_same = [current(&[w.mallory.public()])];
    let records_retired = [Record::new(Vec::new(), vec![w.mallory.public()])];
    let expectations = [
        ("known, new", Expectation::known(&known_bob)),
        ("known, retired", Expectation::known(&known_retired)),
        (
            "first contact, recorded",
            Expectation::first_contact(&records_same),
        ),
        (
            "first contact, retired key",
            Expectation::first_contact(&records_retired),
        ),
    ];
    // Each would be refused as unexpected or retired on its key.
    for (id, expectation) in &expectations {
        let (result, _) = establish(&w, &bundle_of(&w.mallory, 9), expectation);
        assert!(
            matches!(
                result.err(),
                Some(InitiatorError::UnexpectedIdentity | InitiatorError::RetiredIdentity)
            ),
            "{id}: the control"
        );
    }
    let mut respelled_identity = bundle_of(&w.mallory, 9);
    let mut bytes = *respelled_identity.bundle.identity_key.as_bytes();
    bytes[31] |= 0x80;
    respelled_identity.bundle.identity_key = dh::PublicKeyBytes::from_bytes(bytes);
    let mut non_canonical_signed = bundle_of(&w.mallory, 9);
    non_canonical_signed.bundle.signed_prekey = key(U_P);
    let mut non_canonical_one_time = bundle_of(&w.mallory, 9);
    non_canonical_one_time.bundle.one_time_prekey = Some(key(U_P));
    let mut both = with_inconsistent_presence(bundle_of(&w.mallory, 9));
    both.bundle.signed_prekey = key(U_P);
    let malformed = [
        (
            "inconsistent presence",
            with_inconsistent_presence(bundle_of(&w.mallory, 9)),
            LifecycleError::InconsistentBundle,
        ),
        (
            "identity key with bit 255 set",
            respelled_identity,
            LifecycleError::BadEncoding,
        ),
        (
            "non-canonical signed prekey",
            non_canonical_signed,
            LifecycleError::BadEncoding,
        ),
        (
            "non-canonical one-time prekey",
            non_canonical_one_time,
            LifecycleError::BadEncoding,
        ),
        // The two together: presence first, as the leaf orders them.
        (
            "presence and canonical",
            both,
            LifecycleError::InconsistentBundle,
        ),
    ];
    for (bundle_id, bundle, kind) in &malformed {
        for (exp_id, expectation) in &expectations {
            refused_before_randomness(
                &w,
                bundle,
                expectation,
                InitiatorError::Establish(*kind),
                &format!("{exp_id}, {bundle_id}"),
            );
        }
    }
    // The expected key itself, re-spelled with bit 255 set: a canonical-key
    // refusal, not an identity refusal.
    let mut expected_respelled = bundle_of(&w.bob, 9);
    let mut bytes = *expected_respelled.bundle.identity_key.as_bytes();
    bytes[31] |= 0x80;
    expected_respelled.bundle.identity_key = dh::PublicKeyBytes::from_bytes(bytes);
    refused_before_randomness(
        &w,
        &expected_respelled,
        &Expectation::known(&known_bob),
        InitiatorError::Establish(LifecycleError::BadEncoding),
        "known, the expected key re-spelled",
    );
    // A presence disagreement on a bundle whose identity key is u = 0 is a
    // presence refusal, not an invalid identity key.
    let presence_u0 =
        with_inconsistent_presence(with_identity_key(bundle_of(&w.mallory, 9), key(U0)));
    for (exp_id, expectation) in &expectations {
        refused_before_randomness(
            &w,
            &presence_u0,
            expectation,
            InitiatorError::Establish(LifecycleError::InconsistentBundle),
            &format!("{exp_id}, presence with u = 0"),
        );
    }
}

/// First contact refuses a key her records hold, by what the lookup finds.
#[test]
fn first_contact_over_her_records() {
    let w = world();
    let carol_retired_old = Record::new(vec![w.bob.public()], vec![w.old.public()]);
    let dave = current(&[w.dave.public()]);
    let dave_also_old = current(&[w.old.public(), w.dave.public()]);
    let mallory_twice_a = current(&[w.mallory.public()]);
    let mallory_twice_b = current(&[w.mallory.public(), w.dave.public()]);
    let mallory_retired_by_carol = Record::new(Vec::new(), vec![w.mallory.public()]);

    // A retired key, *same* for no record.
    refused_before_randomness(
        &w,
        &bundle_of(&w.old, 10),
        &Expectation::first_contact(&[carol_retired_old.clone(), dave.clone()]),
        InitiatorError::RetiredIdentity,
        "retired for one, same for none",
    );
    // A recorded contact's key under another name.
    refused_before_randomness(
        &w,
        &bundle_of(&w.dave, 10),
        &Expectation::first_contact(&[carol_retired_old.clone(), dave.clone()]),
        InitiatorError::UnexpectedIdentity,
        "current for one",
    );
    // Current for one contact and retired for another: still unexpected.
    refused_before_randomness(
        &w,
        &bundle_of(&w.old, 10),
        &Expectation::first_contact(&[carol_retired_old.clone(), dave_also_old]),
        InitiatorError::UnexpectedIdentity,
        "current for one, retired for another",
    );
    // Ambiguous.
    refused_before_randomness(
        &w,
        &bundle_of(&w.mallory, 10),
        &Expectation::first_contact(&[mallory_twice_a, mallory_twice_b, mallory_retired_by_carol]),
        InitiatorError::UnexpectedIdentity,
        "same for two",
    );
    // A record with a non-canonical member refuses the whole expectation,
    // even over a bundle with a bad signature.
    let malformed = Record::new(vec![w.dave.public()], vec![key(U_P)]);
    refused_before_randomness(
        &w,
        &with_bad_signed_prekey_signature(bundle_of(&w.stranger, 10)),
        &Expectation::first_contact(&[dave.clone(), malformed]),
        InitiatorError::MalformedRecord,
        "one malformed record",
    );
    // Unattributed goes on, and the session is unattributed.
    let records = [carol_retired_old, dave];
    let (result, _) = establish(
        &w,
        &bundle_of(&w.stranger, 10),
        &Expectation::first_contact(&records),
    );
    let session = result.expect("a key in no record establishes under first contact");
    assert_eq!(
        lookup(&session.peer_identity(), &records)
            .unwrap()
            .attribution,
        Attribution::Unattributed
    );
}

/// Under *known*, a key that is also current in another contact's record
/// goes on, and the session is ambiguous.
#[test]
fn known_and_same_elsewhere_establishes_an_ambiguous_session() {
    let w = world();
    let records = [
        current(&[w.bob.public()]),
        current(&[w.bob.public(), w.dave.public()]),
    ];
    let (result, _) = establish(&w, &bundle_of(&w.bob, 11), &Expectation::known(&records[0]));
    let session = result.expect("same under known goes on");
    assert_eq!(
        lookup(&session.peer_identity(), &records)
            .unwrap()
            .attribution,
        Attribution::Ambiguous
    );
}

/// Under *known*, a key that is *same* in the selected record and *retired*
/// in another contact's record goes on: *known* reads the selected record
/// only. The lookup then finds the selected contact, and reports the other
/// record as retiring the key.
#[test]
fn known_and_same_but_retired_elsewhere_establishes_a_contacts_session() {
    let w = world();
    let records = [
        current(&[w.bob.public()]),
        Record::new(vec![w.dave.public()], vec![w.bob.public()]),
    ];
    let (result, _) = establish(&w, &bundle_of(&w.bob, 21), &Expectation::known(&records[0]));
    let session = result.expect("same in the selected record goes on");
    let found = lookup(&session.peer_identity(), &records).unwrap();
    assert_eq!(found.attribution, Attribution::Contact(0));
    assert_eq!(found.same_for, vec![0]);
    assert_eq!(found.retired_for, vec![1]);
    assert!(found.malformed.is_empty());
}

/// Under *first contact*, a record with both sets empty is a contact with no
/// record, not a malformed one: a key in no other record goes on, and the
/// session is unattributed. A key current in another record is still refused,
/// so the empty record changes nothing.
#[test]
fn first_contact_over_records_including_an_empty_one() {
    let w = world();
    let records = [Record::default(), current(&[w.dave.public()])];
    let first_contact = Expectation::first_contact(&records);
    assert!(!first_contact.is_malformed());
    let (result, _) = establish(&w, &bundle_of(&w.stranger, 22), &first_contact);
    let session = result.expect("an empty record does not refuse first contact");
    let found = lookup(&session.peer_identity(), &records).unwrap();
    assert_eq!(found.attribution, Attribution::Unattributed);
    assert!(found.malformed.is_empty());
    let only_empty = [Record::default()];
    assert!(
        establish(
            &w,
            &bundle_of(&w.stranger, 23),
            &Expectation::first_contact(&only_empty)
        )
        .0
        .is_ok()
    );
    refused_before_randomness(
        &w,
        &bundle_of(&w.dave, 24),
        &first_contact,
        InitiatorError::UnexpectedIdentity,
        "first contact, an empty record and a recorded contact's key",
    );
}

/// First contact with no records gives an unattributed session, and the
/// responder reads it.
#[test]
fn first_contact_with_no_records_establishes_end_to_end() {
    let w = world();
    let mut rng = rand::rngs::StdRng::seed_from_u64(12);
    let mut store = w.stranger.create_prekeys(2, &mut rng);
    let bundle = store.publish();
    let mut session = establish_initiator(
        &w.alice,
        &bundle,
        &Expectation::first_contact(&[]),
        &mut rng,
    )
    .expect("first contact establishes");
    assert_eq!(
        lookup(&session.peer_identity(), &[]).unwrap().attribution,
        Attribution::Unattributed
    );
    let initial = session.encrypt(b"hello", &mut rng).unwrap();
    let (_, plaintext) = establish_responder(&w.stranger, &mut store, &initial, &mut rng).unwrap();
    assert_eq!(plaintext, b"hello");
}

/// With no records, the expectation adds nothing: establishment under first
/// contact gives the lifecycle leaf's result exactly, from the same random
/// generator, and draws exactly what the leaf draws. Checked over honest
/// bundles from fresh identities and over a bundle failing each check the
/// leaf makes.
#[test]
fn with_no_records_first_contact_is_the_leafs_establishment() {
    let w = world();
    let mut bundles: Vec<(String, PublishedBundle)> = Vec::new();
    let mut seed_rng = rand::rngs::StdRng::seed_from_u64(13);
    for i in 0..8u64 {
        let owner = Identity::generate(&mut seed_rng);
        let one_time = if i % 2 == 0 { 2 } else { 0 };
        let b = owner.create_prekeys(one_time, &mut seed_rng).publish();
        bundles.push((format!("honest {i}"), b));
    }
    let base = || bundle_of(&w.bob, 14);
    let mut respelled = base();
    let mut bytes = *respelled.bundle.identity_key.as_bytes();
    bytes[31] |= 0x80;
    respelled.bundle.identity_key = dh::PublicKeyBytes::from_bytes(bytes);
    let mut non_canonical_signed = base();
    non_canonical_signed.bundle.signed_prekey = key(U_P);
    bundles.extend([
        (
            "bad signed".to_string(),
            with_bad_signed_prekey_signature(base()),
        ),
        ("bad kem".to_string(), with_bad_kem_prekey_signature(base())),
        (
            "unencodable kem".to_string(),
            with_unencodable_kem_prekey(base(), &w.bob),
        ),
        (
            "low-order one-time".to_string(),
            with_low_order_one_time_prekey(base()),
        ),
        (
            "low-order signed".to_string(),
            with_low_order_signed_prekey(base(), &w.bob),
        ),
        ("presence".to_string(), with_inconsistent_presence(base())),
        ("respelled identity".to_string(), respelled),
        ("non-canonical signed".to_string(), non_canonical_signed),
        (
            "torsion twin".to_string(),
            with_identity_key(base(), key(RFC7748_ALICE_PLUS_TORSION)),
        ),
    ]);
    for (id, value) in NOT_IDENTITY_KEYS {
        bundles.push((
            format!("identity {id}"),
            with_identity_key(base(), key(value)),
        ));
    }
    for (id, bundle) in &bundles {
        let mut ours = Counting::new(15);
        let mut leaf = Counting::new(15);
        let wrapped = establish_initiator(
            &w.alice,
            bundle,
            &Expectation::first_contact(&[]),
            &mut ours,
        );
        let direct = tacenta_lifecycle::establish_initiator(&w.alice, bundle, &mut leaf);
        assert_eq!(ours.drawn, leaf.drawn, "{id}: draws differ");
        match (wrapped, direct) {
            (Ok(a), Ok(b)) => assert_eq!(&*a.export(), &*b.export(), "{id}: sessions differ"),
            (Err(InitiatorError::Establish(a)), Err(b)) => assert_eq!(a, b, "{id}"),
            (a, b) => panic!(
                "{id}: first contact gave {:?}, the leaf gave {:?}",
                a.err(),
                b.err()
            ),
        }
    }
}

/// The leaf, pinned to the bundle's own key, never refuses as
/// `UnexpectedIdentity`, so that kind never reaches a caller through
/// [`InitiatorError::Establish`]: a substituted key is refused by the
/// expectation instead.
#[test]
fn the_leaf_pin_never_fires_through_the_expectation() {
    let w = world();
    let rec = current(&[w.bob.public()]);
    for seed in 0..4u64 {
        for owner in [&w.bob, &w.mallory, &w.dave] {
            let (result, _) =
                establish(&w, &bundle_of(owner, 16 + seed), &Expectation::known(&rec));
            assert_ne!(
                result.err(),
                Some(InitiatorError::Establish(
                    LifecycleError::UnexpectedIdentity
                ))
            );
        }
    }
}
