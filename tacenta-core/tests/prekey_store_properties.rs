//! Property tests for the prekey store's operations (`create_prekeys`, `replenish`,
//! `rotate_signed_prekey`, `rotate_kem`, `publish_one_time_batch`, `publish_multi_use`
//! and consumption by `establish_responder`), against
//! `tacenta-spec/protocol/key-deletion.md`, What this implementation does, and for the
//! stored list `legacy_blocked`, against `tacenta-spec/protocol/session-persistence.md`,
//! Legacy markers.
//!
//! Generators, each `StdRng::seed_from_u64` with a seed fixed in this file and varied
//! by case: the numbering property draws the store's size `n` from 0 to `MAX_N` for
//! each of `NUMBERING_CASES` (48) cases; the sequence property draws, for each of
//! `RUNS` (12) runs, the store's starting size and a sequence of `STEPS` (24)
//! operations (a replenishment of 0 to 3, a rotation of either kind, or an initial
//! message from a fresh initiator to one of the bundles the store publishes, delivered
//! first with its authentication tag altered, then as sent, then again); the rotation
//! property draws, for each of `ROTATION_RUNS` (24) runs, the starting size and a
//! schedule of `ROTATION_STEPS` (8) steps, each a rotation of a drawn kind or a
//! replenishment, publishing a bundle after each; the list property draws, for each
//! of `LIST_CASES` (256) cases, the store's size and a `legacy_blocked` list of zero to
//! three entries, each the store's last-resort KEM identifier or a drawn other
//! identifier. Replay: the seeds are fixed, and each assertion message names the case,
//! run or step.
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::collections::{BTreeMap, BTreeSet};
use tacenta_core::sessions::identity::{Expectation, establish_initiator};
use tacenta_core::sessions::{Identity, PrekeyStore, PublishedBundle, establish_responder};

const SEED: u64 = 0x9e_4e75;
const RUNS: u64 = 12;
const STEPS: usize = 24;
const NUMBERING_CASES: u64 = 48;
const MAX_N: u32 = 40;
const ROTATION_RUNS: u64 = 24;
const ROTATION_STEPS: usize = 8;
const LIST_CASES: u64 = 256;

/// `create_prekeys(n)` numbers the store in one pass: the signed prekey 1, the
/// one-time curve prekeys 2 to n + 1, the last-resort KEM prekey n + 2 and the
/// one-time KEM prekeys n + 3 to 2n + 2, leaving `next_id` at 2n + 3.
///
/// Specification: key-deletion.md, What this implementation does: "`create_prekeys`
/// with `n` one-time prekeys of each kind numbers the store in one pass: the signed
/// prekey `1`, the one-time curve prekeys `2` to `n + 1`, the last-resort KEM prekey
/// `n + 2`, and the one-time KEM prekeys `n + 3` to `2n + 2`, leaving `next_id` at
/// `2n + 3`."
#[test]
fn create_prekeys_numbers_the_store_as_the_page_says() {
    let mut sizes = BTreeSet::new();
    for case in 0..NUMBERING_CASES {
        let mut r = StdRng::seed_from_u64(SEED ^ 0x0d0d ^ case);
        let n = r.gen_range(0..=MAX_N);
        sizes.insert(n);
        let id = Identity::generate(&mut r);
        let store = id.create_prekeys(n as usize, &mut r);
        assert_eq!(store.next_id(), 2 * n + 3, "case {case}, n = {n}: next_id");
        assert_eq!(
            store.one_time_remaining(),
            (n as usize, n as usize),
            "case {case}, n = {n}"
        );
        let multi = store.publish_multi_use();
        assert_eq!(
            multi.signed_prekey_id, 1,
            "case {case}, n = {n}: signed prekey"
        );
        assert_eq!(
            multi.kem_prekey_id,
            n + 2,
            "case {case}, n = {n}: last-resort KEM prekey"
        );
        assert!(
            multi.bundle.one_time_prekey.is_none(),
            "case {case}, n = {n}"
        );
        let batch = store.publish_one_time_batch();
        let curve: BTreeSet<u32> = batch.iter().map(|b| b.one_time_prekey_id).collect();
        let kem: BTreeSet<u32> = batch.iter().map(|b| b.kem_prekey_id).collect();
        assert_eq!(
            curve,
            (2..n + 2).collect(),
            "case {case}, n = {n}: one-time curve prekeys"
        );
        assert_eq!(
            kem,
            (n + 3..2 * n + 3).collect(),
            "case {case}, n = {n}: one-time KEM prekeys"
        );
        assert!(
            batch.iter().all(|b| b.signed_prekey_id == 1),
            "case {case}, n = {n}"
        );
    }
    // Not vacuous: the draws cover more than a handful of sizes.
    assert!(sizes.len() >= 16, "only {} sizes drawn", sizes.len());
}

/// Every identifier a key was ever published under: curve prekeys and KEM prekeys.
#[derive(Default)]
struct Seen {
    by_id: BTreeMap<u32, Vec<u8>>,
}

impl Seen {
    fn record(&mut self, b: &PublishedBundle, run: u64, step: usize) {
        let mut put = |id: u32, key: Vec<u8>| {
            let old = self.by_id.insert(id, key.clone());
            assert!(
                old.is_none() || old == Some(key),
                "run {run} step {step}: identifier {id} names two keys"
            );
        };
        put(
            b.signed_prekey_id,
            b.bundle.signed_prekey.as_bytes().to_vec(),
        );
        put(b.kem_prekey_id, b.bundle.kem_prekey.clone());
        if let Some(k) = b.bundle.one_time_prekey {
            put(b.one_time_prekey_id, k.as_bytes().to_vec());
        }
    }
}

/// Over generated sequences of operations:
/// - an identifier, once handed out, never names a second key, of either kind;
/// - `replenish(count)` adds `count` one-time curve prekeys numbered `next_id` onward
///   and then `count` one-time KEM prekeys numbered after them, advancing `next_id` by
///   one for each;
/// - an initial message whose authentication tag was altered is refused and leaves the
///   store's bytes as they were, so no one-time prekey is deleted before a message
///   authenticates;
/// - a one-time pair, once an initial message naming it is accepted, is never
///   published again and is counted out of `one_time_remaining`; and
/// - the same initial message delivered again is refused and leaves the store's bytes
///   as they were, whether it named a one-time pair or the last-resort KEM prekey.
///
/// Specification: key-deletion.md, What this implementation does: "**One-time prekeys
/// are replenished, and identifiers never repeat.**", "`replenish` with `count` adds
/// `count` one-time curve prekeys and then `count` one-time KEM prekeys, each taking
/// `next_id` as its identifier and advancing it by one", "A one-time KEM prekey defends
/// itself by being deleted on use, so replaying a message that names one fails", and
/// "**A replayed last-resort handshake is refused**"; Establishing a session: "if the
/// initial message fails to decrypt, it aborts and deletes `SK`, leaving no session
/// behind; if it decrypts, it deletes the private half of every one-time prekey the
/// message named"; and session-establishment.md, Receiving the initial message: "**A
/// refused initial message changes nothing.**" Rotations are interleaved with these
/// operations so that the identifiers they take are checked too; the rotation rule
/// itself is the next test's.
#[test]
fn identifiers_never_repeat_and_used_prekeys_are_gone() {
    let mut accepted = (0usize, 0usize);
    for run in 0..RUNS {
        let mut r = StdRng::seed_from_u64(SEED + 1 + run);
        let bob = Identity::generate(&mut r);
        let mut store = bob.create_prekeys(r.gen_range(0..4), &mut r);
        let mut seen = Seen::default();
        let mut used: BTreeSet<u32> = BTreeSet::new();
        for step in 0..STEPS {
            let multi = store.publish_multi_use();
            seen.record(&multi, run, step);
            let batch = store.publish_one_time_batch();
            for b in &batch {
                seen.record(b, run, step);
                assert!(
                    !used.contains(&b.one_time_prekey_id) && !used.contains(&b.kem_prekey_id),
                    "run {run} step {step}: a used one-time prekey was published again"
                );
            }
            match r.gen_range(0..6u8) {
                0 | 1 => {
                    let count = r.gen_range(0..4usize);
                    let (next, (c, k)) = (store.next_id(), store.one_time_remaining());
                    store.replenish(&bob, count, &mut r);
                    assert_eq!(
                        store.next_id(),
                        next + 2 * count as u32,
                        "run {run} step {step}"
                    );
                    let after = store.publish_one_time_batch();
                    let ids = |b: &[PublishedBundle], kem: bool| -> BTreeSet<u32> {
                        b.iter()
                            .map(|x| {
                                if kem {
                                    x.kem_prekey_id
                                } else {
                                    x.one_time_prekey_id
                                }
                            })
                            .collect()
                    };
                    let added = count as u32;
                    assert_eq!(
                        ids(&after, false)
                            .difference(&ids(&batch, false))
                            .copied()
                            .collect::<BTreeSet<u32>>(),
                        (next..next + added).collect(),
                        "run {run} step {step}: the new curve prekeys' identifiers"
                    );
                    assert_eq!(
                        ids(&after, true)
                            .difference(&ids(&batch, true))
                            .copied()
                            .collect::<BTreeSet<u32>>(),
                        (next + added..next + 2 * added).collect(),
                        "run {run} step {step}: the new KEM prekeys' identifiers"
                    );
                    assert_eq!(
                        store.one_time_remaining(),
                        (c + count, k + count),
                        "run {run} step {step}: replenish"
                    );
                }
                2 => store.rotate_signed_prekey(&bob, &mut r),
                3 => store.rotate_kem(&bob, &mut r),
                _ => {
                    let one_time = !batch.is_empty() && r.gen_range(0..3u8) != 0;
                    let bundle: &PublishedBundle = if one_time {
                        &batch[r.gen_range(0..batch.len())]
                    } else {
                        &multi
                    };
                    let alice = Identity::generate(&mut r);
                    let mut sender = establish_initiator(
                        &alice,
                        bundle,
                        &Expectation::first_contact(&[]),
                        &mut r,
                    )
                    .unwrap_or_else(|e| panic!("run {run} step {step}: {e:?}"));
                    let initial = sender.encrypt(b"first", &mut r).unwrap();
                    // The same message with its last byte (inside the authentication
                    // tag) changed first: refused, and the store unchanged.
                    let mut tampered = initial.clone();
                    *tampered.last_mut().unwrap() ^= 1;
                    let bytes = store.to_bytes().to_vec();
                    assert!(
                        establish_responder(&bob, &mut store, &tampered, &mut r).is_err(),
                        "run {run} step {step}: a tampered initial message was accepted"
                    );
                    assert_eq!(
                        store.to_bytes().to_vec(),
                        bytes,
                        "run {run} step {step}: a refused initial message changed the store"
                    );
                    let before = store.one_time_remaining();
                    establish_responder(&bob, &mut store, &initial, &mut r)
                        .unwrap_or_else(|e| panic!("run {run} step {step}: {e:?}"));
                    if one_time {
                        used.insert(bundle.one_time_prekey_id);
                        used.insert(bundle.kem_prekey_id);
                        assert_eq!(
                            store.one_time_remaining(),
                            (before.0 - 1, before.1 - 1),
                            "run {run} step {step}: the pair was not consumed"
                        );
                        accepted.0 += 1;
                    } else {
                        accepted.1 += 1;
                    }
                    let bytes = store.to_bytes().to_vec();
                    assert!(
                        establish_responder(&bob, &mut store, &initial, &mut r).is_err(),
                        "run {run} step {step}: a repeated initial message was accepted"
                    );
                    assert_eq!(
                        store.to_bytes().to_vec(),
                        bytes,
                        "run {run} step {step}: a refused repeat changed the store"
                    );
                }
            }
            assert!(store.invariant(), "run {run} step {step}: invariant");
        }
    }
    assert!(
        accepted.0 >= 10 && accepted.1 >= 10,
        "establishments: {} one-time, {} last-resort",
        accepted.0,
        accepted.1
    );
}

/// A retired prekey is honoured for exactly one rotation, for the signed prekey and for
/// the last-resort KEM prekey alike. Over generated schedules of rotations of either
/// kind and replenishments, an initial message made from any multi-use bundle the store
/// published earlier is accepted exactly when neither of the keys it names has been
/// retired by more than one rotation of its kind since that bundle was published, and a
/// refused one leaves the store's bytes as they were.
///
/// Specification: key-deletion.md, What this implementation does: "**Signed prekeys
/// rotate, and the retired one is kept for exactly one rotation.**", "is honoured by
/// `establish_responder` for an initial message that still names it", "when a second
/// rotation moves another key into the previous slot, the one already there is zeroed
/// and dropped", and "`rotate_kem` does the same for the signed last-resort KEM
/// prekey".
#[test]
fn a_retired_prekey_is_honoured_for_exactly_one_rotation() {
    let (mut honoured, mut refused) = (0usize, 0usize);
    for run in 0..ROTATION_RUNS {
        let mut r = StdRng::seed_from_u64(SEED ^ 0x707 ^ run);
        let bob = Identity::generate(&mut r);
        let mut store = bob.create_prekeys(r.gen_range(0..3), &mut r);
        // Each published bundle with the rotation counts of both kinds at publication.
        let (mut signed_rotations, mut kem_rotations) = (0u32, 0u32);
        let mut published = vec![(store.publish_multi_use(), 0u32, 0u32)];
        for step in 0..ROTATION_STEPS {
            match r.gen_range(0..5u8) {
                0 | 1 => {
                    store.rotate_signed_prekey(&bob, &mut r);
                    signed_rotations += 1;
                }
                2 | 3 => {
                    store.rotate_kem(&bob, &mut r);
                    kem_rotations += 1;
                }
                _ => store.replenish(&bob, r.gen_range(0..3usize), &mut r),
            }
            let i = r.gen_range(0..published.len());
            let (bundle, s_at, k_at) = &published[i];
            let expect = signed_rotations - s_at <= 1 && kem_rotations - k_at <= 1;
            let alice = Identity::generate(&mut r);
            let mut sender =
                establish_initiator(&alice, bundle, &Expectation::first_contact(&[]), &mut r)
                    .unwrap_or_else(|e| panic!("run {run} step {step}: {e:?}"));
            let initial = sender.encrypt(b"first", &mut r).unwrap();
            let bytes = store.to_bytes().to_vec();
            let got = establish_responder(&bob, &mut store, &initial, &mut r).is_ok();
            assert_eq!(
                got,
                expect,
                "run {run} step {step}: bundle {i} after {} signed and {} KEM rotations",
                signed_rotations - s_at,
                kem_rotations - k_at
            );
            if got {
                honoured += 1;
            } else {
                refused += 1;
                assert_eq!(
                    store.to_bytes().to_vec(),
                    bytes,
                    "run {run} step {step}: the refusal changed the store"
                );
            }
            assert!(store.invariant(), "run {run} step {step}: invariant");
            published.push((store.publish_multi_use(), signed_rotations, kem_rotations));
        }
    }
    // Not vacuous: both outcomes occur.
    assert!(
        honoured >= 20 && refused >= 20,
        "{honoured} honoured, {refused} refused"
    );
}

/// The decoder accepts a stored `legacy_blocked` list exactly when it is the canonical
/// one, and reads it back to the same bytes; it refuses every other spelling.
/// Generated: fresh stores (written as v5, with no previous prekeys, so the last-resort
/// KEM identifier is the only one a list may name) whose empty list is replaced by a
/// list of zero to three entries, each that identifier or another drawn one. The
/// canonical lists are then the empty list and the list holding that identifier once.
///
/// Specification: session-persistence.md, Legacy markers: "`legacy_blocked` is in
/// strictly ascending order, holds at most two entries, and every entry is `kem_id` or
/// the identifier inside `previous_kem`", and "A list that is not strictly ascending,
/// whether out of order or naming an identifier twice, is a second spelling of a list
/// the writer would have sorted, and is refused"; Principles, "Canonical and
/// length-prefixed". A repeated identifier is refused only by the decoder's canonical
/// re-encoding check, so this property is what tests that check.
#[test]
fn a_stored_blocked_list_is_accepted_only_in_its_canonical_spelling() {
    let (mut accepted, mut refused_repeat) = (0usize, 0usize);
    for case in 0..LIST_CASES {
        let mut r = StdRng::seed_from_u64(SEED ^ 0xb10c ^ case);
        let bob = Identity::generate(&mut r);
        let store = bob.create_prekeys(r.gen_range(0..3), &mut r);
        let kem_id = store.publish_multi_use().kem_prekey_id;
        let bytes = store.to_bytes().to_vec();
        // The tail of a fresh v5 store: an empty `legacy_blocked` (count 0) and two
        // absent previous prekeys.
        let tail = bytes.len() - 6;
        assert_eq!(&bytes[tail..], &[0u8; 6], "case {case}: unexpected tail");
        let len = r.gen_range(0..=3usize);
        let list: Vec<u32> = (0..len)
            .map(|_| {
                if r.gen_range(0..3u8) == 0 {
                    loop {
                        let other: u32 = r.r#gen();
                        if other != kem_id {
                            break other;
                        }
                    }
                } else {
                    kem_id
                }
            })
            .collect();
        let mut spelled = bytes[..tail].to_vec();
        spelled.extend_from_slice(&(list.len() as u32).to_be_bytes());
        for id in &list {
            spelled.extend_from_slice(&id.to_be_bytes());
        }
        spelled.extend_from_slice(&[0, 0]);
        let canonical = list.is_empty() || list == [kem_id];
        match PrekeyStore::from_bytes(&spelled) {
            Ok(back) => {
                assert!(canonical, "case {case}: list {list:?} accepted");
                assert_eq!(
                    back.to_bytes().to_vec(),
                    spelled,
                    "case {case}: list {list:?} read back to other bytes"
                );
                accepted += 1;
            }
            Err(e) => {
                assert!(
                    !canonical,
                    "case {case}: canonical list {list:?} refused: {e:?}"
                );
                if list == [kem_id, kem_id] {
                    refused_repeat += 1;
                }
            }
        }
    }
    // Not vacuous: canonical lists are accepted, and the repeated identifier, which
    // only the re-encoding check refuses, is drawn.
    assert!(
        accepted >= 32 && refused_repeat >= 8,
        "{accepted} accepted, {refused_repeat} repeats refused"
    );
}
