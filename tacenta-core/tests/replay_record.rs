//! The last-resort replay record follows the keys it protects (external
//! review, 2026-09). An entry is tagged with the last-resort KEM key the
//! handshake was made against; it stays while that key can still decrypt,
//! leaves when a rotation wipes the key, and persists with its tag in the v4
//! store format, while the three earlier formats still read.
//!
//! The record itself is private, so the tests observe it through behaviour
//! (which error a replay draws) and through `to_bytes`, whose length moves by
//! exactly one 36-byte entry per record entry once the rest of the store is
//! held equal. The fail-closed bound is `agreement_and_bounds.rs`.

use rand::SeedableRng;
use tacenta_core::sessions::{
    Identity, LifecycleError, PrekeyStore, PrekeyStoreDecodeError, establish_initiator,
    establish_responder,
};

fn rng(seed: u64) -> rand::rngs::StdRng {
    rand::rngs::StdRng::seed_from_u64(seed)
}

/// One byte per version, as `PrekeyStore::to_bytes` writes it.
const V4: u8 = 0x04;
const V3: u8 = 0x03;

/// A record entry on the wire in v4: the key identifier, then the fingerprint.
const ENTRY: usize = 4 + 32;

/// A last-resort first contact from a fresh identity against `bundle`.
fn last_resort_initial(
    bundle: &tacenta_core::sessions::PublishedBundle,
    text: &[u8],
    r: &mut rand::rngs::StdRng,
) -> Vec<u8> {
    let peer = Identity::generate(r);
    let mut s = establish_initiator(&peer, bundle, r).unwrap();
    s.encrypt(text, r).unwrap()
}

/// Where the record's count sits in the encoding of a store that holds no
/// one-time keys of either kind, which is the only shape these tests build.
/// Everything before it is fixed-width except the KEM key pair, which is
/// length-prefixed, so the offset is read rather than assumed.
fn seen_count_offset(bytes: &[u8]) -> usize {
    // version, identity_public, signed secret + id + sig, then the one-time
    // curve count, which must be zero for the arithmetic below to hold.
    let mut pos = 1 + 32 + (32 + 4 + 64);
    assert_eq!(
        &bytes[pos..pos + 4],
        &[0, 0, 0, 0],
        "expected no one-time curve prekeys"
    );
    pos += 4;
    let kem_len = u32::from_be_bytes(bytes[pos..pos + 4].try_into().unwrap()) as usize;
    pos += 4 + kem_len + 4 + 64;
    assert_eq!(
        &bytes[pos..pos + 4],
        &[0, 0, 0, 0],
        "expected no one-time KEM prekeys"
    );
    pos += 4;
    // next_id, then the count.
    pos + 4
}

/// The v3 spelling of a v4 store: the same bytes with the four-byte tag
/// removed from every record entry and the version byte relabelled.
fn strip_to_v3(v4: &[u8]) -> Vec<u8> {
    assert_eq!(v4[0], V4);
    let count_at = seen_count_offset(v4);
    let count = u32::from_be_bytes(v4[count_at..count_at + 4].try_into().unwrap()) as usize;
    let mut out = v4[..count_at + 4].to_vec();
    out[0] = V3;
    let mut pos = count_at + 4;
    for _ in 0..count {
        out.extend_from_slice(&v4[pos + 4..pos + ENTRY]);
        pos += ENTRY;
    }
    out.extend_from_slice(&v4[pos..]);
    out
}

// ------------------------------------------------------------------ rotation

/// After one rotation the retired key still decrypts, so its entry still
/// refuses the replay; after the second the key is wiped, its entries go with
/// it, and the replay fails on the identifier rather than being accepted.
#[test]
fn the_record_follows_its_key_through_rotation_and_leaves_when_it_is_wiped() {
    let mut r = rng(1);
    let bob = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(0, &mut r);
    // A control store from the same identity, taken through the same
    // rotations but no handshakes, so that the two encodings differ only by
    // the record: the KEM encodings are fixed-width, so the difference is
    // exactly the entries.
    let mut control = bob.create_prekeys(0, &mut r);
    let bundle = store.publish_multi_use();

    let captured = last_resort_initial(&bundle, b"first", &mut r);
    establish_responder(&bob, &mut store, &captured, &mut r).unwrap();
    assert_eq!(store.to_bytes().len(), control.to_bytes().len() + ENTRY);

    // One rotation: the entry stays, because the key it was made against is
    // the retired one and still decrypts.
    store.rotate_kem(&bob, &mut r);
    control.rotate_kem(&bob, &mut r);
    assert_eq!(store.to_bytes().len(), control.to_bytes().len() + ENTRY);
    assert!(matches!(
        establish_responder(&bob, &mut store, &captured, &mut r),
        Err(LifecycleError::ReplayedLastResort)
    ));

    // Two rotations: the key is wiped and the entry is dropped. The replay is
    // not accepted; it fails on the identifier, before the record is
    // consulted, which is why the entry had nothing left to refuse.
    store.rotate_kem(&bob, &mut r);
    control.rotate_kem(&bob, &mut r);
    assert_eq!(
        store.to_bytes().len(),
        control.to_bytes().len(),
        "the wiped key's entries must leave the record with it"
    );
    assert!(matches!(
        establish_responder(&bob, &mut store, &captured, &mut r),
        Err(LifecycleError::UnknownPrekeyId)
    ));
}

/// Only the wiped key's entries go. Entries made under the key a rotation
/// retires stay through that rotation, and entries made under the new key are
/// untouched by the next one.
#[test]
fn rotation_drops_exactly_the_wiped_keys_entries() {
    let mut r = rng(2);
    let bob = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(0, &mut r);
    let mut control = bob.create_prekeys(0, &mut r);

    // Two under the first key.
    let first = store.publish_multi_use();
    let a = last_resort_initial(&first, b"a", &mut r);
    let b = last_resort_initial(&first, b"b", &mut r);
    establish_responder(&bob, &mut store, &a, &mut r).unwrap();
    establish_responder(&bob, &mut store, &b, &mut r).unwrap();

    // One under the second.
    store.rotate_kem(&bob, &mut r);
    control.rotate_kem(&bob, &mut r);
    let second = store.publish_multi_use();
    let c = last_resort_initial(&second, b"c", &mut r);
    establish_responder(&bob, &mut store, &c, &mut r).unwrap();
    assert_eq!(store.to_bytes().len(), control.to_bytes().len() + 3 * ENTRY);

    // The rotation that wipes the first key drops its two and keeps the one.
    store.rotate_kem(&bob, &mut r);
    control.rotate_kem(&bob, &mut r);
    assert_eq!(store.to_bytes().len(), control.to_bytes().len() + ENTRY);
    assert!(matches!(
        establish_responder(&bob, &mut store, &c, &mut r),
        Err(LifecycleError::ReplayedLastResort)
    ));
    assert!(matches!(
        establish_responder(&bob, &mut store, &a, &mut r),
        Err(LifecycleError::UnknownPrekeyId)
    ));
}

// --------------------------------------------------------------- persistence

/// A v4 round trip preserves the tags. The proof is behavioural: a restored
/// store still refuses the replay, and the rotation that wipes the entry's key
/// still drops it -- which it could not if the tag had been lost or replaced
/// by the current key's identifier on the way through.
#[test]
fn a_v4_round_trip_preserves_the_tags() {
    let mut r = rng(3);
    let bob = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(0, &mut r);
    let mut control = bob.create_prekeys(0, &mut r);
    let bundle = store.publish_multi_use();
    let captured = last_resort_initial(&bundle, b"first", &mut r);
    establish_responder(&bob, &mut store, &captured, &mut r).unwrap();
    store.rotate_kem(&bob, &mut r);
    control.rotate_kem(&bob, &mut r);

    let bytes = store.to_bytes();
    assert_eq!(bytes[0], V4);
    let mut restored = PrekeyStore::from_bytes(&bytes).unwrap();
    assert_eq!(restored.to_bytes().as_slice(), bytes.as_slice());
    assert!(matches!(
        establish_responder(&bob, &mut restored, &captured, &mut r),
        Err(LifecycleError::ReplayedLastResort)
    ));

    // The entry was made under the now-retired key. If the restore had tagged
    // it with the current key instead, this rotation would keep it.
    restored.rotate_kem(&bob, &mut r);
    control.rotate_kem(&bob, &mut r);
    assert_eq!(
        restored.to_bytes().len(),
        control.to_bytes().len(),
        "a restored entry must carry the tag it was written with"
    );
}

/// A v3 store's untagged entries read back tagged with the current key, so
/// a v3 file whose entries were all made under that key upgrades to exactly
/// the v4 bytes the same store writes.
#[test]
fn a_v3_store_upgrades_with_its_entries_tagged_with_the_current_key() {
    let mut r = rng(4);
    let bob = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(0, &mut r);
    let bundle = store.publish_multi_use();
    for text in [&b"one"[..], b"two", b"three"] {
        let m = last_resort_initial(&bundle, text, &mut r);
        establish_responder(&bob, &mut store, &m, &mut r).unwrap();
    }
    let v4 = store.to_bytes();
    let v3 = strip_to_v3(&v4);
    assert_eq!(v3.len(), v4.len() - 3 * 4);

    let upgraded = PrekeyStore::from_bytes(&v3).expect("a v3 store must still read");
    assert_eq!(
        upgraded.to_bytes().as_slice(),
        v4.as_slice(),
        "untagged entries must come back tagged with the current key"
    );
}

/// The conservative reading is safe even when it is wrong. A v3 entry made
/// under the key a rotation retired comes back tagged with the current key,
/// but the fingerprint alone decides whether a handshake is a repeat, so the
/// replay is still refused; the tag only decides when the entry is dropped.
#[test]
fn a_v3_entry_made_under_the_retired_key_still_refuses_its_replay() {
    let mut r = rng(5);
    let bob = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(0, &mut r);
    let bundle = store.publish_multi_use();
    let captured = last_resort_initial(&bundle, b"first", &mut r);
    establish_responder(&bob, &mut store, &captured, &mut r).unwrap();
    store.rotate_kem(&bob, &mut r);

    let v3 = strip_to_v3(&store.to_bytes());
    let mut upgraded = PrekeyStore::from_bytes(&v3).unwrap();
    assert!(matches!(
        establish_responder(&bob, &mut upgraded, &captured, &mut r),
        Err(LifecycleError::ReplayedLastResort)
    ));
}

/// A v4 entry tagged with an identifier that names neither the current
/// last-resort key nor the retired one is malformed: the store drops a key's
/// entries when it wipes the key, so the writer never emits such a tag.
#[test]
fn from_bytes_refuses_an_entry_tagged_with_an_unknown_key() {
    let mut r = rng(6);
    let bob = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(0, &mut r);
    let bundle = store.publish_multi_use();
    let m = last_resort_initial(&bundle, b"first", &mut r);
    establish_responder(&bob, &mut store, &m, &mut r).unwrap();

    let mut bytes = store.to_bytes().to_vec();
    let entry_at = seen_count_offset(&bytes) + 4;
    // An identifier no store has issued: `next_id` starts at one and this
    // store has issued a handful.
    bytes[entry_at..entry_at + 4].copy_from_slice(&u32::MAX.to_be_bytes());
    assert!(matches!(
        PrekeyStore::from_bytes(&bytes),
        Err(PrekeyStoreDecodeError::Malformed)
    ));
}

/// A repeated fingerprint is malformed: the responder refuses a repeat before
/// it could be recorded, so only something other than `to_bytes` writes one.
#[test]
fn from_bytes_refuses_a_repeated_fingerprint() {
    let mut r = rng(7);
    let bob = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(0, &mut r);
    let bundle = store.publish_multi_use();
    for text in [&b"one"[..], b"two"] {
        let m = last_resort_initial(&bundle, text, &mut r);
        establish_responder(&bob, &mut store, &m, &mut r).unwrap();
    }

    let mut bytes = store.to_bytes().to_vec();
    let first = seen_count_offset(&bytes) + 4;
    let (head, tail) = bytes.split_at_mut(first + ENTRY);
    tail[..ENTRY].copy_from_slice(&head[first..first + ENTRY]);
    assert!(matches!(
        PrekeyStore::from_bytes(&bytes),
        Err(PrekeyStoreDecodeError::Malformed)
    ));

    // The same rule reaches the untagged formats.
    let v3 = strip_to_v3(&store.to_bytes());
    let mut v3_dup = v3.clone();
    let first = seen_count_offset(&v3_dup) + 4;
    let (head, tail) = v3_dup.split_at_mut(first + 32);
    tail[..32].copy_from_slice(&head[first..first + 32]);
    assert!(matches!(
        PrekeyStore::from_bytes(&v3_dup),
        Err(PrekeyStoreDecodeError::Malformed)
    ));
}

/// A count above the bound is refused whatever the version claims, before
/// the count sizes anything.
#[test]
fn from_bytes_refuses_a_count_above_the_bound_in_v4_and_v3() {
    let mut r = rng(8);
    let bob = Identity::generate(&mut r);
    let store = bob.create_prekeys(0, &mut r);
    for version in [V4, V3] {
        let mut bytes = store.to_bytes().to_vec();
        bytes[0] = version;
        let count_at = seen_count_offset(&bytes);
        bytes[count_at..count_at + 4].copy_from_slice(&1025u32.to_be_bytes());
        assert!(
            matches!(
                PrekeyStore::from_bytes(&bytes),
                Err(PrekeyStoreDecodeError::Malformed)
            ),
            "version {version:#04x} must refuse a count above the bound"
        );
    }
}
