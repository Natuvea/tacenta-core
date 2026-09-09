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
//!
//! The identifier rules `from_bytes` enforces are here too: no identifier at
//! or past `next_id`, no retired identifier equal to the live one, no
//! repeated one-time identifier, and no one-time KEM prekey carrying a
//! last-resort key's identifier. Each is a store `to_bytes` never writes and
//! at least one is a store that, accepted, would let a replay through.

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

// ------------------------------------------------------------- identifiers

/// The big-endian `u32` at `at`.
fn u32_at(bytes: &[u8], at: usize) -> u32 {
    u32::from_be_bytes(bytes[at..at + 4].try_into().unwrap())
}

/// Where the signed prekey identifier sits: after the version byte, the
/// identity key, and the signed prekey secret, all fixed-width.
const SIGNED_PREKEY_ID_AT: usize = 1 + 32 + 32;

/// Where the current last-resort KEM key's identifier sits: after the
/// one-time curve vector, whose entries are fixed-width, and the KEM key
/// pair, which is length-prefixed. Unlike `seen_count_offset` this walks the
/// curve vector rather than requiring it to be empty.
fn kem_id_offset(bytes: &[u8]) -> usize {
    let mut pos = 1 + 32 + (32 + 4 + 64);
    let curve_count = u32_at(bytes, pos) as usize;
    pos += 4 + curve_count * 36;
    let kem_len = u32_at(bytes, pos) as usize;
    pos + 4 + kem_len
}

/// Where the first one-time KEM entry's identifier sits: past the current
/// KEM identifier, its signature, and the vector's count.
fn first_kem_one_time_at(bytes: &[u8]) -> usize {
    kem_id_offset(bytes) + 4 + 64 + 4
}

/// A retired identifier equal to the live one is malformed. Accepted, a
/// retired KEM identifier equal to the current one would have the next
/// rotation prune the record by the *live* key's identifier, dropping every
/// entry that key had recorded, after which a captured message naming it is
/// accepted a second time. The honest store after one rotation is the
/// starting point, so the only difference is the one identifier.
#[test]
fn from_bytes_refuses_a_retired_identifier_equal_to_the_current_one() {
    let mut r = rng(9);
    let bob = Identity::generate(&mut r);

    let mut store = bob.create_prekeys(0, &mut r);
    store.rotate_kem(&bob, &mut r);
    let honest = store.to_bytes().to_vec();
    assert!(PrekeyStore::from_bytes(&honest).is_ok());
    let kem_id = u32_at(&honest, kem_id_offset(&honest));
    // The retired KEM key is the tail of the encoding: a presence byte, the
    // length-prefixed pair, the identifier, then a 64-byte signature.
    let at = honest.len() - 64 - 4;
    assert_ne!(
        u32_at(&honest, at),
        kem_id,
        "an honest rotation retires a distinct key"
    );
    let mut bytes = honest.clone();
    bytes[at..at + 4].copy_from_slice(&kem_id.to_be_bytes());
    assert!(
        matches!(
            PrekeyStore::from_bytes(&bytes),
            Err(PrekeyStoreDecodeError::Malformed)
        ),
        "a retired KEM identifier equal to the live one must be refused"
    );

    // The same rule for the signed prekey. With no retired KEM key the tail
    // is the retired signed prekey -- presence byte, secret, identifier,
    // signature -- then the KEM key's absent-marker byte.
    let mut store = bob.create_prekeys(0, &mut r);
    store.rotate_signed_prekey(&bob, &mut r);
    let honest = store.to_bytes().to_vec();
    assert!(PrekeyStore::from_bytes(&honest).is_ok());
    let signed_id = u32_at(&honest, SIGNED_PREKEY_ID_AT);
    let at = honest.len() - 1 - 64 - 4;
    assert_ne!(u32_at(&honest, at), signed_id);
    let mut bytes = honest.clone();
    bytes[at..at + 4].copy_from_slice(&signed_id.to_be_bytes());
    assert!(matches!(
        PrekeyStore::from_bytes(&bytes),
        Err(PrekeyStoreDecodeError::Malformed)
    ));
}

/// Every identifier a store holds was handed out by `next_id`, so each is
/// below it. A counter wound back to a live identifier, or an identifier past
/// the counter, is refused: either way the next key handed out could collide
/// with one the store still holds.
#[test]
fn from_bytes_refuses_an_identifier_at_or_past_next_id() {
    let mut r = rng(10);
    let bob = Identity::generate(&mut r);
    let store = bob.create_prekeys(0, &mut r);
    let honest = store.to_bytes().to_vec();
    let kem_id = u32_at(&honest, kem_id_offset(&honest));
    let next_at = seen_count_offset(&honest) - 4;
    assert!(u32_at(&honest, next_at) > kem_id);

    // The counter wound back to the live key's identifier.
    let mut wound = honest.clone();
    wound[next_at..next_at + 4].copy_from_slice(&kem_id.to_be_bytes());
    assert!(
        matches!(
            PrekeyStore::from_bytes(&wound),
            Err(PrekeyStoreDecodeError::Malformed)
        ),
        "an identifier equal to next_id must be refused"
    );

    // An identifier past the counter, on the signed prekey.
    let mut past = honest.clone();
    past[SIGNED_PREKEY_ID_AT..SIGNED_PREKEY_ID_AT + 4].copy_from_slice(&u32::MAX.to_be_bytes());
    assert!(
        matches!(
            PrekeyStore::from_bytes(&past),
            Err(PrekeyStoreDecodeError::Malformed)
        ),
        "an identifier past next_id must be refused"
    );
}

/// Two one-time prekeys of one kind sharing an identifier is malformed: the
/// store consumes the first match, so the second would serve a replay of the
/// initial message that spent the first.
#[test]
fn from_bytes_refuses_a_repeated_one_time_identifier() {
    let mut r = rng(11);
    let bob = Identity::generate(&mut r);
    let store = bob.create_prekeys(2, &mut r);
    let honest = store.to_bytes().to_vec();
    assert!(PrekeyStore::from_bytes(&honest).is_ok());

    // Curve entries are 36 bytes each, straight after their count.
    let first = 1 + 32 + (32 + 4 + 64) + 4;
    let second = first + 36;
    let mut curve = honest.clone();
    let id = u32_at(&curve, first);
    curve[second..second + 4].copy_from_slice(&id.to_be_bytes());
    assert!(matches!(
        PrekeyStore::from_bytes(&curve),
        Err(PrekeyStoreDecodeError::Malformed)
    ));

    // A KEM entry is the identifier, the length-prefixed pair, then the
    // signature, so the second entry's position depends on the first's
    // length.
    let first = first_kem_one_time_at(&honest);
    let pair_len = u32_at(&honest, first + 4) as usize;
    let second = first + 4 + 4 + pair_len + 64;
    let mut kem = honest.clone();
    let id = u32_at(&kem, first);
    kem[second..second + 4].copy_from_slice(&id.to_be_bytes());
    assert!(matches!(
        PrekeyStore::from_bytes(&kem),
        Err(PrekeyStoreDecodeError::Malformed)
    ));
}

/// A one-time KEM prekey carrying a last-resort key's identifier, current or
/// retired, is malformed: an initial message naming that identifier would be
/// served from whichever the lookup reached first.
#[test]
fn from_bytes_refuses_a_one_time_kem_identifier_shared_with_a_last_resort_key() {
    let mut r = rng(12);
    let bob = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(1, &mut r);
    store.rotate_kem(&bob, &mut r);
    let honest = store.to_bytes().to_vec();
    assert!(PrekeyStore::from_bytes(&honest).is_ok());
    let one_time_at = first_kem_one_time_at(&honest);
    let current = u32_at(&honest, kem_id_offset(&honest));
    let retired = u32_at(&honest, honest.len() - 64 - 4);
    for shared in [current, retired] {
        let mut bytes = honest.clone();
        bytes[one_time_at..one_time_at + 4].copy_from_slice(&shared.to_be_bytes());
        assert!(
            matches!(
                PrekeyStore::from_bytes(&bytes),
                Err(PrekeyStoreDecodeError::Malformed)
            ),
            "a one-time KEM identifier equal to {shared} must be refused"
        );
    }
}

// --------------------------------------------------------------- occupancy

/// `last_resort_record_remaining` counts down as last-resort handshakes are
/// accepted, holds through a refusal and through the rotation that retires a
/// key, climbs back when the rotation after it wipes the key, and survives
/// persistence.
#[test]
fn the_record_reports_its_remaining_room() {
    let mut r = rng(13);
    let bob = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(0, &mut r);
    // `MAX_LAST_RESORT_SEEN`, which is private; the bound is also pinned in
    // `agreement_and_bounds.rs`.
    let full = 1024;
    assert_eq!(store.last_resort_record_remaining(), full);

    let first_bundle = store.publish_multi_use();
    let captured = last_resort_initial(&first_bundle, b"first", &mut r);
    establish_responder(&bob, &mut store, &captured, &mut r).unwrap();
    assert_eq!(store.last_resort_record_remaining(), full - 1);

    // A refused replay records nothing.
    assert!(matches!(
        establish_responder(&bob, &mut store, &captured, &mut r),
        Err(LifecycleError::ReplayedLastResort)
    ));
    assert_eq!(store.last_resort_record_remaining(), full - 1);

    // The rotation that retires the key keeps its entry; a handshake against
    // the new key adds one.
    store.rotate_kem(&bob, &mut r);
    assert_eq!(store.last_resort_record_remaining(), full - 1);
    let second = last_resort_initial(&store.publish_multi_use(), b"second", &mut r);
    establish_responder(&bob, &mut store, &second, &mut r).unwrap();
    assert_eq!(store.last_resort_record_remaining(), full - 2);

    // The rotation after it wipes the first key and frees its entry only.
    store.rotate_kem(&bob, &mut r);
    assert_eq!(store.last_resort_record_remaining(), full - 1);

    let restored = PrekeyStore::from_bytes(&store.to_bytes()).unwrap();
    assert_eq!(restored.last_resort_record_remaining(), full - 1);
}
