//! A last-resort handshake that also names a one-time curve prekey.
//!
//! `session-establishment.md` (Receiving the initial message) gives two store
//! effects on success and one rule on refusal. A last-resort handshake that
//! also named a one-time curve prekey removes that prekey and appends the
//! handshake's replay identity; no other entry or store field changes; and a
//! message whose inner ratchet message does not authenticate leaves the whole
//! store as it was.
//!
//! The other tests that consume a curve prekey name a one-time KEM prekey, so
//! their handshake is not on the last-resort path
//! (`a_successful_initial_message_does_consume_its_prekeys`), and the
//! last-resort tests use stores that hold no curve prekey
//! (`a_failed_last_resort_message_does_not_record_a_replay_identity`,
//! `replay_record.rs`). This file builds the bundle between them: the
//! last-resort KEM key from `publish_multi_use` with a one-time curve prekey
//! from `publish_one_time_batch`. Nothing stops a directory serving it, and
//! `establish_responder` accepts it.
//!
//! The curve prekey named is the second from the end of the pool, not the last
//! one, so that "the named prekey was removed" cannot be read as "the last
//! entry was popped".

use rand::SeedableRng;
use tacenta_core::serialization::{ABSENT_ID, decode_initial};
use tacenta_core::sessions::{
    Identity, LifecycleError as Error, PreKeyBundle, PrekeyStore, PublishedBundle,
    establish_initiator, establish_responder,
};

fn rng(seed: u64) -> rand::rngs::StdRng {
    rand::rngs::StdRng::seed_from_u64(seed)
}

/// Alter the last byte, which is inside the inner ratchet message's tag.
fn forge(message: &[u8]) -> Vec<u8> {
    let mut m = message.to_vec();
    let last = m.len() - 1;
    m[last] ^= 0x01;
    m
}

/// The identifiers of the one-time prekeys a store still holds, read through
/// the public batch. The batch pairs the two pools from their ends and is as
/// long as the shorter one, so it lists every curve prekey of a store that
/// holds no more curve than KEM prekeys, and the last `batch.len()` KEM
/// prekeys, newest first. The curve identifiers come back sorted, because a
/// removal moves the last entry into the vacated slot.
fn pool_ids(store: &PrekeyStore) -> (Vec<u32>, Vec<u32>) {
    let batch = store.publish_one_time_batch();
    let mut curve: Vec<u32> = batch.iter().map(|b| b.one_time_prekey_id).collect();
    let kem: Vec<u32> = batch.iter().map(|b| b.kem_prekey_id).collect();
    curve.sort_unstable();
    (curve, kem)
}

/// What a test needs to know about the store it started from.
struct World {
    alice: Identity,
    bob: Identity,
    /// The one-time curve prekey the handshake will name.
    named_curve: u32,
    /// The current last-resort KEM key, which the handshake will name.
    last_resort: u32,
    bundle: PublishedBundle,
}

/// Four one-time prekeys of each kind, and a bundle that names the second
/// curve prekey from the end together with the last-resort KEM key.
fn world(seed: u64) -> (World, PrekeyStore) {
    let mut r = rng(seed);
    let alice = Identity::generate(&mut r);
    let bob = Identity::generate(&mut r);
    let store = bob.create_prekeys(4, &mut r);

    let mut batch = store.publish_one_time_batch();
    assert_eq!(batch.len(), 4, "four curve and four KEM one-time prekeys");
    let one_time = batch.remove(1);
    let PublishedBundle {
        bundle,
        signed_prekey_id,
        kem_prekey_id,
        ..
    } = store.publish_multi_use();
    assert_ne!(
        one_time.one_time_prekey_id, ABSENT_ID,
        "the curve prekey is one the store holds"
    );
    assert!(
        one_time.bundle.one_time_prekey.is_some(),
        "the batch entry carries the curve prekey's public key"
    );

    let (_, kem_ids) = pool_ids(&store);
    assert!(
        !kem_ids.contains(&kem_prekey_id),
        "the KEM key the bundle names is the last-resort key, not a one-time one"
    );

    let world = World {
        alice,
        bob,
        named_curve: one_time.one_time_prekey_id,
        last_resort: kem_prekey_id,
        bundle: PublishedBundle {
            bundle: PreKeyBundle {
                one_time_prekey: one_time.bundle.one_time_prekey,
                ..bundle
            },
            signed_prekey_id,
            one_time_prekey_id: one_time.one_time_prekey_id,
            kem_prekey_id,
        },
    };
    (world, store)
}

/// The first message of a session started against `world.bundle`, checked to be
/// the message these tests are about: it names the curve prekey and the
/// last-resort key and no other.
fn combined_initial(world: &World, text: &[u8], r: &mut rand::rngs::StdRng) -> Vec<u8> {
    let mut alice = establish_initiator(&world.alice, &world.bundle, r).unwrap();
    let initial = alice.encrypt(text, r).unwrap();
    let decoded = decode_initial(&initial).unwrap();
    assert_eq!(decoded.one_time_prekey_id, world.named_curve);
    assert_eq!(decoded.kem_prekey_id, world.last_resort);
    initial
}

/// Both effects, on success.
///
/// The handshake removes the curve prekey it names and only that one, leaves
/// every one-time KEM prekey where it was, and spends exactly one entry of the
/// last-resort key's replay budget. Each effect is read from a different public
/// surface, so a handshake that drops one of them and still does the other
/// fails here: the remaining pools (`one_time_remaining` and the batch
/// identifiers) for the removal, `last_resort_record_remaining` and its
/// per-key form for the replay identity.
#[test]
fn a_last_resort_handshake_naming_a_curve_prekey_removes_it_and_records_its_replay_identity() {
    let mut r = rng(131);
    let (world, mut store) = world(31);
    let (curve_before, kem_before) = pool_ids(&store);
    assert!(curve_before.contains(&world.named_curve));
    let budget_before = store.last_resort_record_remaining();
    assert_eq!(
        store.last_resort_record_remaining_for(world.last_resort),
        Some(budget_before)
    );
    assert_eq!(store.one_time_remaining(), (4, 4));

    let initial = combined_initial(&world, b"combined", &mut r);
    let (_session, plaintext) =
        establish_responder(&world.bob, &mut store, &initial, &mut r).unwrap();
    assert_eq!(plaintext, b"combined");

    // The curve prekey it named is gone, and no other one-time prekey is.
    assert_eq!(
        store.one_time_remaining(),
        (3, 4),
        "one curve prekey removed, no KEM prekey removed"
    );
    let (curve_after, kem_after) = pool_ids(&store);
    let expected_curve: Vec<u32> = curve_before
        .iter()
        .copied()
        .filter(|id| *id != world.named_curve)
        .collect();
    assert_eq!(
        curve_after, expected_curve,
        "the curve prekey the message named was not removed, or another one was"
    );
    assert_eq!(
        kem_after[..],
        kem_before[..kem_after.len()],
        "a last-resort handshake removes no one-time KEM prekey"
    );

    // Its replay identity is in the record, against the key it was made under.
    assert_eq!(
        store.last_resort_record_remaining(),
        budget_before - 1,
        "the replay identity of a last-resort handshake that named a curve prekey was not recorded"
    );
    assert_eq!(
        store.last_resort_record_remaining_for(world.last_resort),
        Some(budget_before - 1)
    );

    // The last-resort key itself stays on offer, and the repeat is refused.
    assert_eq!(store.publish_multi_use().kem_prekey_id, world.last_resort);
    let after = store.to_bytes();
    assert!(
        matches!(
            establish_responder(&world.bob, &mut store, &initial, &mut r),
            Err(Error::UnknownPrekeyId)
        ),
        "the repeat names a curve prekey the store no longer holds"
    );
    // `assert!` rather than `assert_eq!`: a failure must not print key material.
    assert!(
        *store.to_bytes() == *after,
        "a refused repeat leaves the store as it was"
    );
}

/// Neither effect, on refusal.
///
/// A copy of the message whose inner tag is altered reaches the authenticated
/// decrypt with the last-resort key, the replay budget and the curve prekey all
/// in place, and is refused there. The store is byte for byte what it was, the
/// two effects are named separately so that a failure says which one moved, and
/// the genuine message behind it, which names the same prekeys, still
/// establishes and has both effects. That last step is what shows the refusal
/// was the tag and not a prekey the first attempt could not find.
#[test]
fn a_last_resort_handshake_naming_a_curve_prekey_that_fails_to_authenticate_changes_nothing() {
    let mut r = rng(132);
    let (world, mut store) = world(32);
    let before = store.to_bytes();
    let budget_before = store.last_resort_record_remaining();
    let initial = combined_initial(&world, b"combined", &mut r);

    assert!(
        matches!(
            establish_responder(&world.bob, &mut store, &forge(&initial), &mut r),
            Err(Error::Aead)
        ),
        "an altered inner tag is refused by the authenticated decrypt"
    );
    assert_eq!(
        store.one_time_remaining(),
        (4, 4),
        "a message that did not authenticate removed a one-time prekey"
    );
    assert_eq!(
        store.last_resort_record_remaining(),
        budget_before,
        "a message that did not authenticate recorded a replay identity"
    );
    assert!(
        *store.to_bytes() == *before,
        "a refusal leaves the whole store as it was"
    );

    let (_session, plaintext) = establish_responder(&world.bob, &mut store, &initial, &mut r)
        .expect("the refused attempt must not spend what the genuine message needs");
    assert_eq!(plaintext, b"combined");
    assert_eq!(
        store.one_time_remaining(),
        (3, 4),
        "the genuine message must remove the curve prekey it names"
    );
    assert_eq!(
        store.last_resort_record_remaining(),
        budget_before - 1,
        "the genuine message must record its replay identity"
    );
}
