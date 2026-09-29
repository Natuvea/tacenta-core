//! Identity keys at every entry point that admits one.
//!
//! An identity key is the canonical encoding of a point of the prime-order
//! subgroup of Curve25519 (identities-and-devices.md, Accepting a signed
//! statement, check 6). One table of keys, classified by an independent
//! implementation of that rule when the table was written, is driven through
//! each entry point, and every row asserts the refusal kind the specification
//! and the model name for that boundary, not only that something failed.
//! Honest keys are driven through the same entry points and must be accepted.

use curve25519_dalek::montgomery::MontgomeryPoint;
use rand::SeedableRng;
use rand_core::{CryptoRng, RngCore};
use tacenta_core::primitives::{dh, xeddsa};
use tacenta_core::serialization::{decode_initial, encode_initial};
use tacenta_core::sessions::{
    Identity, LifecycleError as Error, PrekeyStore, PrekeyStoreDecodeError, Session,
    SessionDecodeError, SessionError, StoredSessionIdentities, encode_ec, establish_initiator,
    establish_initiator_for, establish_responder, is_valid_identity_key, responder_shared_secret,
    scan_stored_prekey_identity, scan_stored_session_identities, verify_bundle,
    verify_under_identity,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Class {
    /// The canonical encoding of a point of the prime-order subgroup.
    Prime,
    /// Canonical, on the curve, and not of prime order.
    Mixed,
    /// One of the five values of order dividing eight.
    LowOrder,
    /// Canonical, and no point of the curve has this u.
    OffCurve,
    /// Bit 255 set, or a value at or above p.
    NonCanonical,
}

/// `(id, key as hex, class)`. The classes come from an independent
/// implementation with its own field and curve arithmetic; the test
/// `the_table_agrees_with_curve_arithmetic` recomputes them here.
const TABLE: &[(&str, &str, Class)] = &[
    (
        "honest-h1",
        "a4e09292b651c278b9772c569f5fa9bb13d906b46ab68c9df9dc2b4409f8a209",
        Class::Prime,
    ),
    (
        "honest-h2",
        "ce8d3ad1ccb633ec7b70c17814a5c76ecd029685050d344745ba05870e587d59",
        Class::Prime,
    ),
    (
        "honest-h3",
        "5fef13fc76023a9ee6ded987b6aa93958cdc2097ef9fc845d5319c9ca100d35e",
        Class::Prime,
    ),
    (
        "rfc7748-alice",
        "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a",
        Class::Prime,
    ),
    (
        "rfc7748-bob",
        "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f",
        Class::Prime,
    ),
    (
        "base-point",
        "0900000000000000000000000000000000000000000000000000000000000000",
        Class::Prime,
    ),
    (
        "h1-plus-torsion-1",
        "037faa3bbfc676b26f87fb1449a152bcb3eb7cfeeedbaa3604deca93ac75304b",
        Class::Mixed,
    ),
    (
        "h1-plus-torsion-2",
        "6722174dbc997c555d35183ae1f5b54d718517e2012641580dc06bf48b5cc67b",
        Class::Mixed,
    ),
    (
        "h1-plus-torsion-3",
        "e8d38dcb16f648d07445eec3ca82323dba82357310085fbf9bb0345ce823e87e",
        Class::Mixed,
    ),
    (
        "h1-plus-torsion-4",
        "cc80c67924df11225baa5ff7838b65ef4747fc514b11a810fb951106ab3d620a",
        Class::Mixed,
    ),
    (
        "h1-plus-torsion-5",
        "9111bc7d044c267035bca4a9de062fe4f353e2ee88a3ef9ea32429678b585b7d",
        Class::Mixed,
    ),
    (
        "h1-plus-torsion-6",
        "a142bda181923458bf441949108fdcb0bc0765d479086b8f520a6592c8f92619",
        Class::Mixed,
    ),
    (
        "h1-plus-torsion-7",
        "17f500d43bb2ac86183a9b80e83d701445cfbd68042222600acb81b7096d0974",
        Class::Mixed,
    ),
    (
        "h3-plus-torsion-1",
        "bb1a166d952ff3ddaf21a8aece506e592b3b337738dd1dd17b38b71e10754101",
        Class::Mixed,
    ),
    (
        "h3-plus-torsion-2",
        "26f0928b418ae501439b9685f125b7ac6aa6b3da65632b57643af67f2e19572d",
        Class::Mixed,
    ),
    (
        "h3-plus-torsion-3",
        "f6a773dc913bc1f16e6f1e7111bf8567bff841c04817c1ae8adcaa5e3156096e",
        Class::Mixed,
    ),
    (
        "h3-plus-torsion-4",
        "076fb60f40bd1b27c418d7dd94868dabd42f849d121f2e2d7c2f9cddad99b728",
        Class::Mixed,
    ),
    (
        "h3-plus-torsion-5",
        "67dd9120e24772f893706db46d43e2708fea46212e6d924dc20882a91e6b355f",
        Class::Mixed,
    ),
    (
        "h3-plus-torsion-6",
        "6c4bd83c899973c3fa16823e445842703042da3c2f5abad90355d8f581ab9f23",
        Class::Mixed,
    ),
    (
        "h3-plus-torsion-7",
        "19840e3660bdc0267416296dd74d449c652813794b378e98ccc066202394cb37",
        Class::Mixed,
    ),
    (
        "base9-plus-torsion-1",
        "c5e259858ab3095bc0569034a6f3a88fbde0536e336dad4a9519584e920c0c7c",
        Class::Mixed,
    ),
    (
        "base9-plus-torsion-2",
        "1fe6ceff8b05ff49494ba9ab1eb4ff98f3d60573ebd1927b9a7f68509f252e02",
        Class::Mixed,
    ),
    (
        "base9-plus-torsion-4",
        "6a6367e4f97c6024bced038937b5b12b2f26c2e9915fe3a7bcbea07354504770",
        Class::Mixed,
    ),
    (
        "u-0",
        "0000000000000000000000000000000000000000000000000000000000000000",
        Class::LowOrder,
    ),
    (
        "u-1",
        "0100000000000000000000000000000000000000000000000000000000000000",
        Class::LowOrder,
    ),
    (
        "u-p-minus-1",
        "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        Class::OffCurve,
    ),
    (
        "u-order8-a",
        "e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800",
        Class::LowOrder,
    ),
    (
        "u-order8-b",
        "5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157",
        Class::LowOrder,
    ),
    (
        "twist-u-2",
        "0200000000000000000000000000000000000000000000000000000000000000",
        Class::OffCurve,
    ),
    (
        "twist-u-3",
        "0300000000000000000000000000000000000000000000000000000000000000",
        Class::OffCurve,
    ),
    (
        "twist-u-5",
        "0500000000000000000000000000000000000000000000000000000000000000",
        Class::OffCurve,
    ),
    (
        "twist-u-12",
        "0c00000000000000000000000000000000000000000000000000000000000000",
        Class::OffCurve,
    ),
    (
        "noncanonical-9-plus-p",
        "f6ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        Class::NonCanonical,
    ),
    (
        "noncanonical-9-bit255",
        "0900000000000000000000000000000000000000000000000000000000000080",
        Class::NonCanonical,
    ),
    (
        "noncanonical-p",
        "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        Class::NonCanonical,
    ),
    (
        "noncanonical-p-plus-1",
        "eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        Class::NonCanonical,
    ),
    (
        "noncanonical-max",
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        Class::NonCanonical,
    ),
    (
        "noncanonical-honest-h1-bit255",
        "a4e09292b651c278b9772c569f5fa9bb13d906b46ab68c9df9dc2b4409f8a289",
        Class::NonCanonical,
    ),
    (
        "noncanonical-torsion-bit255",
        "037faa3bbfc676b26f87fb1449a152bcb3eb7cfeeedbaa3604deca93ac7530cb",
        Class::NonCanonical,
    ),
];

/// `(id, key, signature over the application signing input of APP_MESSAGE, accepted)`.
/// Every signature verifies under the key of its row when the key is not
/// required to be of prime order (identities-and-devices.md, Verifying a
/// signature, steps 1 to 6); only the `true` rows are under an identity key.
const APP_SIGNATURES: &[(&str, &str, &str, bool)] = &[
    (
        "h1-honest",
        "a4e09292b651c278b9772c569f5fa9bb13d906b46ab68c9df9dc2b4409f8a209",
        "ff435d625f1fce88de561459721bed4fd61669f5b060fcc8f833129f65209df942700276727102b008d3c5d637d7fe8b2aad23af236819b5505dc9f93d36110f",
        true,
    ),
    (
        "h1-plus-torsion-1",
        "037faa3bbfc676b26f87fb1449a152bcb3eb7cfeeedbaa3604deca93ac75304b",
        "1b19c58fe625bae78b8507385c7588d0d03d66885c8f28b61f712b27c9a471b5f27ef2962df2c48387abb50f671757fdb1f32857a6c5bacdeecd99b7b5a20386",
        false,
    ),
    (
        "h1-plus-torsion-2",
        "6722174dbc997c555d35183ae1f5b54d718517e2012641580dc06bf48b5cc67b",
        "22ffc745bf9326adca6dee9e0c00d9777651896da83fc97224bcc799690d11ff93983e5ef065321dc0f879702999e85a021fe278b09e064e4bcd9c4584787501",
        false,
    ),
    (
        "h1-plus-torsion-4",
        "cc80c67924df11225baa5ff7838b65ef4747fc514b11a810fb951106ab3d620a",
        "ec6db775b733303e3ea4cf91bc0563f4282e53378674813814f4e0a00868580c36de193ae1169982162bd3cb82ad3c099cd48fe602cbcaeb76547cebd1755188",
        false,
    ),
    (
        "h3-honest",
        "5fef13fc76023a9ee6ded987b6aa93958cdc2097ef9fc845d5319c9ca100d35e",
        "e6aa17e236a72bdfeda4b57b3cb45d70a10919d3493458aeb12ba6c37e2b7df479702e182bcdc7c816acab4c3e67fda1e65d3476661ac35bde1c01e34844d40f",
        true,
    ),
    (
        "h3-plus-torsion-1",
        "bb1a166d952ff3ddaf21a8aece506e592b3b337738dd1dd17b38b71e10754101",
        "40425cee3d45b73703c10f0846d19a4b4ef3e553bdc82afb835b12ebe0914ca17651d822c801faedabbff5a3b3507c54fb4a93af0d615ee0348225d3c8a3f007",
        false,
    ),
];
const APP_MESSAGE: &[u8] = b"identity boundary";

const ALICE_SECRET: [u8; 32] = [1u8; 32];
const BOB_SECRET: [u8; 32] = [0xa5u8; 32];

fn unhex<const N: usize>(text: &str) -> [u8; N] {
    hex::decode(text).unwrap().try_into().unwrap()
}

fn key_of(id: &str) -> [u8; 32] {
    let row = TABLE.iter().find(|row| row.0 == id).unwrap();
    unhex(row.1)
}

fn public(bytes: [u8; 32]) -> dh::PublicKeyBytes {
    dh::PublicKeyBytes::from_bytes(bytes)
}

fn rows() -> impl Iterator<Item = (&'static str, [u8; 32], Class)> {
    TABLE.iter().map(|row| (row.0, unhex(row.1), row.2))
}

/// A random source that counts what is drawn from it.
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

/// Replace every occurrence of `from` in `bytes` by `to`, and say how many.
fn replace_all(bytes: &[u8], from: &[u8; 32], to: &[u8; 32]) -> (Vec<u8>, usize) {
    let mut out = bytes.to_vec();
    let mut count = 0;
    let mut at = 0;
    while at + 32 <= out.len() {
        if out[at..at + 32] == from[..] {
            out[at..at + 32].copy_from_slice(to);
            count += 1;
            at += 32;
        } else {
            at += 1;
        }
    }
    (out, count)
}

/// Alice (initiator), Bob (responder), Bob's store and the honest first
/// message, all from fixed secrets so the table's derived rows line up.
struct World {
    alice: Identity,
    bob: Identity,
    store: PrekeyStore,
    initial: Vec<u8>,
    initiator_export: Vec<u8>,
    responder_export: Vec<u8>,
}

fn world() -> World {
    let mut rng = rand::rngs::StdRng::seed_from_u64(20260929);
    let alice = Identity::from_secret(ALICE_SECRET);
    let bob = Identity::from_secret(BOB_SECRET);
    let mut store = bob.create_prekeys(1, &mut rng);
    let bundle = store.publish();
    let mut initiator = establish_initiator(&alice, &bundle, &mut rng).unwrap();
    let initial = initiator.encrypt(b"identity boundary", &mut rng).unwrap();
    let initiator_export = initiator.export().to_vec();
    let mut scratch = PrekeyStore::from_bytes(&store.to_bytes()).unwrap();
    let (responder, _) = establish_responder(&bob, &mut scratch, &initial, &mut rng).unwrap();
    let responder_export = responder.export().to_vec();
    // The store the tests offer messages to is the one before the first message.
    store = PrekeyStore::from_bytes(&store.to_bytes()).unwrap();
    World {
        alice,
        bob,
        store,
        initial,
        initiator_export,
        responder_export,
    }
}

#[test]
fn the_fixed_secrets_have_the_table_keys() {
    assert_eq!(
        *Identity::from_secret(ALICE_SECRET).public().as_bytes(),
        key_of("honest-h1")
    );
    assert_eq!(
        *Identity::from_secret(BOB_SECRET).public().as_bytes(),
        key_of("honest-h3")
    );
    // RFC 7748 section 6.1: the published public keys of the two example private keys.
    let alice = Identity::from_secret(unhex(
        "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a",
    ));
    let bob = Identity::from_secret(unhex(
        "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb",
    ));
    assert_eq!(*alice.public().as_bytes(), key_of("rfc7748-alice"));
    assert_eq!(*bob.public().as_bytes(), key_of("rfc7748-bob"));
}

#[test]
fn the_table_agrees_with_curve_arithmetic() {
    let mut counts = [0usize; 5];
    for (id, key, class) in rows() {
        let point = MontgomeryPoint(key).to_edwards(0);
        let canonical = key[31] & 0x80 == 0 && public(key) == public(key) && {
            // below p = 2^255 - 19
            let mut p = [0xffu8; 32];
            p[0] = 0xed;
            p[31] = 0x7f;
            key.iter().rev().cmp(p.iter().rev()) == core::cmp::Ordering::Less
        };
        let computed = match (canonical, point) {
            (false, _) => Class::NonCanonical,
            (true, None) => Class::OffCurve,
            (true, Some(p)) if p.is_small_order() => Class::LowOrder,
            (true, Some(p)) if p.is_torsion_free() => Class::Prime,
            (true, Some(_)) => Class::Mixed,
        };
        assert_eq!(computed, class, "{id}");
        counts[class as usize] += 1;
    }
    assert!(
        counts.iter().all(|n| *n > 0),
        "every class is represented: {counts:?}"
    );
}

#[test]
fn the_rule_over_the_table() {
    for (id, key, class) in rows() {
        let expected = class == Class::Prime;
        assert_eq!(is_valid_identity_key(&public(key)), expected, "{id}");
        assert_eq!(dh::is_prime_order_public(&public(key)), expected, "{id}");
    }
}

/// A bundle of Bob's with `identity` in place of his identity key.
fn bundle_naming(world: &World, identity: [u8; 32]) -> tacenta_core::sessions::PublishedBundle {
    let mut bundle = world.store.publish();
    bundle.bundle.identity_key = public(identity);
    bundle
}

/// The inventory profile's validator (Accepting a signed statement, check 6) and
/// the rule the session boundaries apply are one rule written twice. The same
/// keys pass, and the refusal classes line up, over the table and over keys of
/// no particular form, so the two cannot drift without this test saying so.
#[test]
fn the_inventory_validator_and_the_session_rule_agree() {
    use tacenta_core::groups::inventory::{Error as InventoryError, validate_identity_key};
    for (id, key, class) in rows() {
        let inventory = validate_identity_key(&key);
        assert_eq!(
            inventory.is_ok(),
            is_valid_identity_key(&public(key)),
            "{id}"
        );
        match class {
            Class::Prime => assert_eq!(inventory, Ok(()), "{id}"),
            Class::NonCanonical => assert_eq!(inventory, Err(InventoryError::NonCanonical), "{id}"),
            Class::LowOrder => assert_eq!(inventory, Err(InventoryError::NonContributory), "{id}"),
            Class::Mixed => assert_eq!(inventory, Err(InventoryError::NotPrimeOrder), "{id}"),
            Class::OffCurve => assert!(inventory.is_err(), "{id}"),
        }
    }
    let mut rng = rand::rngs::StdRng::seed_from_u64(0x1d);
    let mut accepted = 0;
    for _ in 0..3000 {
        let mut key = [0u8; 32];
        rng.fill_bytes(&mut key);
        if rng.next_u32() % 2 == 0 {
            key[31] &= 0x7f;
        }
        let both = (
            validate_identity_key(&key).is_ok(),
            is_valid_identity_key(&public(key)),
        );
        assert_eq!(both.0, both.1, "{key:02x?}");
        accepted += usize::from(both.0);
    }
    assert!(
        accepted > 20,
        "the sample reaches accepted keys: {accepted}"
    );
}

#[test]
fn verify_bundle_over_the_table() {
    let world = world();
    for (id, key, class) in rows() {
        let result = verify_bundle(&bundle_naming(&world, key).bundle);
        let expected = match class {
            // Bob's own key: his signatures verify. Any other identity key
            // passes the rule and fails the signature.
            Class::Prime if id == "honest-h3" => Ok(()),
            Class::Prime => Err(SessionError::BadSignedPrekeySignature),
            _ => Err(SessionError::InvalidIdentityKey),
        };
        assert_eq!(result, expected, "{id}");
    }
}

/// Bundles whose two prekey signatures verify under the unrestricted rule of
/// identities-and-devices.md, Verifying a signature, steps 1 to 6, under an
/// identity key that is not of prime order: `(id, identity, signed prekey
/// signature, KEM prekey signature)`. Only the identity rule refuses them.
const SIGNED_BUNDLES: &[(&str, &str, &str, &str)] = &[
    (
        "h3-plus-torsion-1",
        "bb1a166d952ff3ddaf21a8aece506e592b3b337738dd1dd17b38b71e10754101",
        "9f090dbeded8f6665e173797a0b6f2c40c194aa9a82c56b503dd8a708648a88bfc8f021398afac2eb365c57352073bebd61a724eff8c81913c2bcf46b478ac07",
        "ebbcfd9905444e530448f82b2c2161feaa4e738a0b2e004f55c7d141b9f821b6355fa67c7d7cb8a2b2d2a0e6d55329dd4532dede49441a172978ccac55a66507",
    ),
    (
        "h3-plus-torsion-2",
        "26f0928b418ae501439b9685f125b7ac6aa6b3da65632b57643af67f2e19572d",
        "74617b4981c1fcb07e8d9fc652e02fb499f31af0f44c37965dcd347c3ca830245d2fa675f1eb2d6510239e7dfe9c04a6ba3d13c585dfb9068cf7861c967e020a",
        "53203837f45f5e0d962d5f91883212a799b0b53f64fa2df4c876867f1cc3194bac42672bb88d9948e01c7348f19b18a2fa2c9bbe0f7ccb1f40e6699dac51d807",
    ),
    (
        "h3-plus-torsion-4",
        "076fb60f40bd1b27c418d7dd94868dabd42f849d121f2e2d7c2f9cddad99b728",
        "f24fb682f2213e0d607f7fef9154f1a9e929007bdd6f2b59eb2926099a9218e11a532af64c431c710ee5839d66ac7723f036bdfad85f17303e8c885cf1b58f8a",
        "0422f1d0e29048d1a99fab76aacd151d27a0d5d5078e68bb5298164a87b491df30c658f24488363eecfe09f8ca02d5f343937709d2db871dfadd189d2ac9ee8b",
    ),
];
const BUNDLE_SIGNED_PREKEY: &str =
    "ce8d3ad1ccb633ec7b70c17814a5c76ecd029685050d344745ba05870e587d59";
const BUNDLE_KEM_PREKEY: &str =
    "746163656e74612074657374206b656d207072656b65792028343020627974657321292e2e2e2e2e";

fn signed_bundle(row: &(&str, &str, &str, &str)) -> tacenta_core::sessions::PublishedBundle {
    tacenta_core::sessions::PublishedBundle {
        bundle: tacenta_core::sessions::PreKeyBundle {
            identity_key: public(unhex(row.1)),
            signed_prekey: public(unhex(BUNDLE_SIGNED_PREKEY)),
            signed_prekey_signature: unhex(row.2),
            kem_prekey: hex::decode(BUNDLE_KEM_PREKEY).unwrap(),
            kem_prekey_signature: unhex(row.3),
            one_time_prekey: None,
        },
        signed_prekey_id: 1,
        one_time_prekey_id: 0,
        kem_prekey_id: 2,
    }
}

#[test]
fn a_bundle_signed_under_a_refused_identity_is_refused() {
    let alice = Identity::from_secret(ALICE_SECRET);
    for row in SIGNED_BUNDLES {
        let bundle = signed_bundle(row);
        let id = row.0;
        assert_eq!(
            verify_bundle(&bundle.bundle),
            Err(SessionError::InvalidIdentityKey),
            "{id}"
        );
        let mut rng = Counting::new(6);
        let established =
            establish_initiator_for(&alice, &bundle, &bundle.bundle.identity_key, &mut rng);
        assert!(
            matches!(
                established,
                Err(Error::Handshake(SessionError::InvalidIdentityKey))
            ),
            "{id}"
        );
        assert!(
            matches!(
                establish_initiator(&alice, &bundle, &mut rng),
                Err(Error::Handshake(SessionError::InvalidIdentityKey))
            ),
            "{id}"
        );
        assert_eq!(rng.drawn, 0, "{id}: a refused bundle draws no randomness");
        let private = dh::PrivateKey::from_bytes([3u8; 32]);
        assert_eq!(
            tacenta_core::sessions::initiator_shared_secret(
                &private,
                &private,
                &bundle.bundle,
                &[0u8; 32]
            )
            .err(),
            Some(SessionError::InvalidIdentityKey),
            "{id}"
        );
    }
}

#[test]
fn the_initiator_over_the_table() {
    let world = world();
    for (id, key, class) in rows() {
        let mut rng = Counting::new(3);
        let bundle = bundle_naming(&world, key);
        let result = establish_initiator_for(&world.alice, &bundle, &public(key), &mut rng);
        let drawn = rng.drawn;
        match class {
            Class::NonCanonical => assert!(matches!(result, Err(Error::BadEncoding)), "{id}"),
            Class::Prime if id == "honest-h3" => {
                assert!(result.is_ok(), "{id}");
                continue;
            }
            Class::Prime => assert!(
                matches!(
                    result,
                    Err(Error::Handshake(SessionError::BadSignedPrekeySignature))
                ),
                "{id}"
            ),
            _ => assert!(
                matches!(
                    result,
                    Err(Error::Handshake(SessionError::InvalidIdentityKey))
                ),
                "{id}"
            ),
        }
        assert_eq!(drawn, 0, "{id}: a refused bundle draws no randomness");
        // The unpinned entry point pins to what the bundle carries: the same verdict.
        let unpinned = establish_initiator(&world.alice, &bundle, &mut Counting::new(3));
        assert!(unpinned.is_err(), "{id}");
    }
}

#[test]
fn responder_shared_secret_over_the_table() {
    let ours = dh::PrivateKey::from_bytes([9u8; 32]);
    let signed = dh::PrivateKey::from_bytes([10u8; 32]);
    let ephemeral = dh::PrivateKey::from_bytes([11u8; 32]).public_key();
    let secret = [7u8; 32];
    for (id, key, class) in rows() {
        let result =
            responder_shared_secret(&ours, &signed, None, &public(key), &ephemeral, &secret);
        if class == Class::Prime {
            assert!(result.is_ok(), "{id}");
        } else {
            // Reported before any agreement: a low-order key would otherwise
            // be a non-contributory agreement.
            assert_eq!(result.err(), Some(SessionError::InvalidIdentityKey), "{id}");
        }
    }
}

#[test]
fn the_responder_over_the_table() {
    let world = world();
    let message = decode_initial(&world.initial).unwrap();
    let honest = key_of("honest-h1");
    for (id, key, class) in rows() {
        let mut store = PrekeyStore::from_bytes(&world.store.to_bytes()).unwrap();
        let before = store.to_bytes();
        let named = encode_initial(
            &encode_ec(&public(key)),
            &message.ephemeral,
            &message.kem_ciphertext,
            message.signed_prekey_id,
            message.one_time_prekey_id,
            message.kem_prekey_id,
            &message.message,
        );
        let mut rng = Counting::new(4);
        let result = establish_responder(&world.bob, &mut store, &named, &mut rng);
        match class {
            Class::NonCanonical => assert!(matches!(result, Err(Error::Decode(_))), "{id}"),
            Class::Prime if key == honest => {
                assert!(result.is_ok(), "{id}");
                continue;
            }
            // An identity key, and not the one that built the message: the
            // associated data no longer matches.
            Class::Prime => assert!(matches!(result, Err(Error::Aead)), "{id}"),
            _ => assert!(
                matches!(
                    result,
                    Err(Error::Handshake(SessionError::InvalidIdentityKey))
                ),
                "{id}"
            ),
        }
        assert_eq!(
            &*store.to_bytes(),
            &*before,
            "{id}: a refusal leaves the store as it was"
        );
    }
}

/// The identity is refused after the identifiers that select keys are
/// resolved and before anything is spent on the message: an identity that is
/// not one wins over an unknown one-time identifier and over a ciphertext the
/// decapsulation would refuse.
#[test]
fn the_responder_refuses_the_identity_before_the_later_checks() {
    let world = world();
    let message = decode_initial(&world.initial).unwrap();
    let unknown_one_time_id = u32::MAX - 1;
    let short = &message.kem_ciphertext[..message.kem_ciphertext.len() - 1];
    for id in ["h1-plus-torsion-1", "h1-plus-torsion-4", "u-0", "twist-u-2"] {
        let identity = encode_ec(&public(key_of(id)));
        for (label, ciphertext, one_time) in [
            (
                "unknown one-time identifier",
                &message.kem_ciphertext[..],
                unknown_one_time_id,
            ),
            ("wrong-length ciphertext", short, message.one_time_prekey_id),
        ] {
            let mut store = PrekeyStore::from_bytes(&world.store.to_bytes()).unwrap();
            let named = encode_initial(
                &identity,
                &message.ephemeral,
                ciphertext,
                message.signed_prekey_id,
                one_time,
                message.kem_prekey_id,
                &message.message,
            );
            let result = establish_responder(&world.bob, &mut store, &named, &mut Counting::new(5));
            assert!(
                matches!(
                    result,
                    Err(Error::Handshake(SessionError::InvalidIdentityKey))
                ),
                "{id} with {label}"
            );
        }
    }
    // The controls: the same two defects on an honest identity keep the
    // refusals they had.
    let mut store = PrekeyStore::from_bytes(&world.store.to_bytes()).unwrap();
    let unknown = encode_initial(
        &message.identity,
        &message.ephemeral,
        &message.kem_ciphertext,
        message.signed_prekey_id,
        unknown_one_time_id,
        message.kem_prekey_id,
        &message.message,
    );
    assert!(matches!(
        establish_responder(&world.bob, &mut store, &unknown, &mut Counting::new(5)),
        Err(Error::UnknownPrekeyId)
    ));
    let wrong_length = encode_initial(
        &message.identity,
        &message.ephemeral,
        short,
        message.signed_prekey_id,
        message.one_time_prekey_id,
        message.kem_prekey_id,
        &message.message,
    );
    assert!(matches!(
        establish_responder(&world.bob, &mut store, &wrong_length, &mut Counting::new(5)),
        Err(Error::Kem)
    ));
}

#[test]
fn a_stored_session_over_the_table() {
    let world = world();
    let alice = key_of("honest-h1");
    let bob = key_of("honest-h3");
    // (export, the key to replace, whether the replaced key is ours)
    let cases = [
        (&world.initiator_export, alice, "initiator, our identity"),
        (&world.initiator_export, bob, "initiator, peer identity"),
        (&world.responder_export, bob, "responder, our identity"),
        (&world.responder_export, alice, "responder, peer identity"),
    ];
    for (export, replaced, position) in cases {
        for (id, key, class) in rows() {
            let (bytes, count) = replace_all(export, &replaced, &key);
            assert!(
                count >= 2,
                "{position}: the identity is stored twice at least"
            );
            let result = Session::import(&bytes);
            if class == Class::Prime {
                assert!(result.is_ok(), "{position}, {id}");
            } else {
                assert_eq!(
                    result.err(),
                    Some(SessionDecodeError::Inconsistent),
                    "{position}, {id}"
                );
            }
        }
    }
}

#[test]
fn a_stored_prekey_store_over_the_table() {
    let world = world();
    let bytes = world.store.to_bytes();
    let bob = key_of("honest-h3");
    for (id, key, class) in rows() {
        let (patched, count) = replace_all(&bytes, &bob, &key);
        assert_eq!(count, 1, "the store holds its identity key once");
        let result = PrekeyStore::from_bytes(&patched);
        match class {
            // Bob's own key: the store is the one he wrote.
            Class::Prime if id == "honest-h3" => assert!(result.is_ok(), "{id}"),
            // An identity key and not the one the signatures were made under.
            Class::Prime => assert_eq!(
                result.err(),
                Some(PrekeyStoreDecodeError::Incoherent),
                "{id}"
            ),
            _ => assert_eq!(
                result.err(),
                Some(PrekeyStoreDecodeError::Malformed),
                "{id}"
            ),
        }
    }
}

#[test]
fn application_signatures_over_the_fixtures() {
    for (id, key, signature, accepted) in APP_SIGNATURES {
        let key = public(unhex(key));
        let signature: [u8; 64] = unhex(signature);
        assert_eq!(
            verify_under_identity(&key, APP_MESSAGE, &signature),
            *accepted,
            "{id}"
        );
        // The verifier is where the rule is applied: a key outside the subgroup
        // verifies nothing, whichever function asks.
        let mut input = b"tacenta:application-signature:v1\xff".to_vec();
        input.extend_from_slice(APP_MESSAGE);
        assert_eq!(
            xeddsa::verify(&key, &input, &signature).is_ok(),
            *accepted,
            "{id}"
        );
    }
    // A key of the table verifies no signature that was made for another.
    let (_, _, signature, _) = APP_SIGNATURES[0];
    let signature: [u8; 64] = unhex(signature);
    for (id, key, _) in rows() {
        if id != "honest-h1" {
            assert!(
                !verify_under_identity(&public(key), APP_MESSAGE, &signature),
                "{id}"
            );
        }
    }
}

/// Over-refusal: honest keys from many secrets, and the standard's own, are
/// all identity keys, and sessions between them establish, export and import.
#[test]
fn honest_identities_are_accepted_everywhere() {
    let mut secrets: Vec<[u8; 32]> = Vec::new();
    for n in 0..=255u8 {
        secrets.push([n; 32]);
    }
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    for _ in 0..2048 {
        let mut secret = [0u8; 32];
        for chunk in secret.chunks_mut(8) {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            chunk.copy_from_slice(&(state ^ (state >> 29)).to_le_bytes());
        }
        secrets.push(secret);
    }
    for secret in &secrets {
        let identity = Identity::from_secret(*secret);
        assert!(is_valid_identity_key(&identity.public()), "{secret:02x?}");
    }
    let mut rng = rand::rngs::StdRng::seed_from_u64(77);
    for pair in secrets.chunks(2).take(24) {
        let alice = Identity::from_secret(pair[0]);
        let bob = Identity::from_secret(pair[1]);
        let mut store = bob.create_prekeys(1, &mut rng);
        let bundle = store.publish();
        assert_eq!(verify_bundle(&bundle.bundle), Ok(()));
        let mut initiator =
            establish_initiator_for(&alice, &bundle, &bob.public(), &mut rng).unwrap();
        let initial = initiator.encrypt(b"hello", &mut rng).unwrap();
        let (responder, plaintext) =
            establish_responder(&bob, &mut store, &initial, &mut rng).unwrap();
        assert_eq!(plaintext, b"hello");
        assert!(Session::import(&initiator.export()).is_ok());
        assert!(Session::import(&responder.export()).is_ok());
        assert!(PrekeyStore::from_bytes(&store.to_bytes()).is_ok());
        let signature = alice.sign_message(b"challenge", &mut rng);
        assert!(verify_under_identity(
            &alice.public(),
            b"challenge",
            &signature
        ));
    }
}

/// The pre-rollout scan says what `import` and `from_bytes` will say about the
/// identity keys, for the same bytes.
#[test]
fn the_scan_reports_what_import_refuses() {
    let world = world();
    let alice = key_of("honest-h1");
    let replacement = key_of("h1-plus-torsion-1");
    assert_eq!(
        scan_stored_session_identities(&world.initiator_export),
        Ok(StoredSessionIdentities {
            ours: true,
            peer: true
        })
    );
    let (ours, _) = replace_all(&world.initiator_export, &alice, &replacement);
    assert_eq!(
        scan_stored_session_identities(&ours),
        Ok(StoredSessionIdentities {
            ours: false,
            peer: true
        })
    );
    assert_eq!(
        Session::import(&ours).err(),
        Some(SessionDecodeError::Inconsistent)
    );
    let (peer, _) = replace_all(&world.responder_export, &alice, &replacement);
    assert_eq!(
        scan_stored_session_identities(&peer),
        Ok(StoredSessionIdentities {
            ours: true,
            peer: false
        })
    );
    assert_eq!(
        Session::import(&peer).err(),
        Some(SessionDecodeError::Inconsistent)
    );
    assert_eq!(
        scan_stored_session_identities(&world.responder_export[..10]),
        Err(SessionDecodeError::TooShort)
    );
    assert_eq!(
        scan_stored_session_identities(&[]),
        Err(SessionDecodeError::TooShort)
    );
    let mut foreign = world.responder_export.clone();
    foreign[0] = 0x7f;
    assert_eq!(
        scan_stored_session_identities(&foreign),
        Err(SessionDecodeError::UnknownVersion)
    );

    let store = world.store.to_bytes();
    assert_eq!(scan_stored_prekey_identity(&store), Ok(true));
    let (patched, _) = replace_all(&store, &key_of("honest-h3"), &replacement);
    assert_eq!(scan_stored_prekey_identity(&patched), Ok(false));
    assert_eq!(
        PrekeyStore::from_bytes(&patched).err(),
        Some(PrekeyStoreDecodeError::Malformed)
    );
    assert_eq!(
        scan_stored_prekey_identity(&[]),
        Err(PrekeyStoreDecodeError::TooShort)
    );
}
