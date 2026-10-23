//! The order of a sparse skip's two bounds, through the public API.
//!
//! `sparse-pq-ratchet.md`, The store also has a total bound, steps 1 to 4: a
//! skip that steps the receiving chain of an epoch from `c` to `upto` is
//! refused as `TooManySkipped` when `upto - c` is more than `MAX_SKIP`;
//! otherwise it deletes, on a working copy, the keys stored for that epoch
//! under a number `n` with `c < n <= upto`; it counts the keys that remain,
//! whatever their epoch, and is refused as `SkippedStoreFull` when that count
//! plus `upto - c` is more than `MAX_SKIPPED_STORE`; otherwise it stores the
//! derived keys. A refusal leaves the state as it was.
//!
//! These are the public-API counterparts of the unit tests in
//! `tacenta-core/spqr/src/tests.rs`, which build their stores through private
//! fields and call the private `skip_message_keys`. Here every start is stored
//! bytes in the layout of `session-persistence.md`, Sparse ratchet state, read
//! with `State::from_bytes`, driven by `receive`, and read back with
//! `to_bytes`. Most starts hold keys past a chain's counter, which the page
//! says the operations do not produce (proved of the model from
//! initialisation, not of the code); the decoder accepts them, so a restored
//! state can hold them.
//!
//! What they add over the unit tests: a request that breaks both bounds,
//! which the order decides (the kind is `TooManySkipped`; checking the store
//! first would answer `SkippedStoreFull`); keys stored under another epoch,
//! which count against the store and are not deleted by a skip of this one;
//! and the edge `1,997 + 3` accepted, `1,997 + 4` refused, through `receive`.
//!
//! The edge numbers are literals, with an assertion on each constant, so a
//! change of policy fails these tests rather than moving them. Each refusal
//! is checked to leave `to_bytes` byte-identical to the start.

use tacenta_spqr::{MAX_SKIP, MAX_SKIPPED_STORE, SpqrError, State};

const ROOT_KEY: [u8; 32] = [0x11; 32];
/// Bob (`B2a`) in the stored direction byte.
const BOB: u8 = 0x01;

/// A chain: its key and its counter.
type Chain = ([u8; 32], u64);
/// A `chains` entry: the epoch, the sending chain and the receiving chain.
type ChainsEntry = (u64, Option<Chain>, Option<Chain>);

/// The chains entry of epoch 0: chain keys `0x22` (send) and `0x33`
/// (receive), both counters at 0.
const EPOCH_0: ChainsEntry = (0, Some(([0x22; 32], 0)), Some(([0x33; 32], 0)));
/// The chains entry of epoch 1: chain keys `0x44` and `0x55`, both at 0.
const EPOCH_1: ChainsEntry = (1, Some(([0x44; 32], 0)), Some(([0x55; 32], 0)));

/// A stored key for number `n`: `0x32` bytes with `n` big-endian in the first
/// eight, so that no two stored keys are equal.
fn stored(n: u64) -> [u8; 32] {
    let mut key = [0x32; 32];
    key[..8].copy_from_slice(&n.to_be_bytes());
    key
}

/// Sparse ratchet state bytes (`session-persistence.md`, Sparse ratchet
/// state): version, root key, epoch, direction, the `chains` entries, then the
/// stored keys in the order given.
fn state_bytes(epoch: u64, chains: &[ChainsEntry], skipped: &[(u64, u64)]) -> Vec<u8> {
    fn chain(out: &mut Vec<u8>, c: Option<Chain>) {
        match c {
            None => {
                out.push(0x00);
                out.extend_from_slice(&[0u8; 40]);
            }
            Some((ck, n)) => {
                out.push(0x01);
                out.extend_from_slice(&ck);
                out.extend_from_slice(&n.to_be_bytes());
            }
        }
    }
    let mut out = vec![0x01];
    out.extend_from_slice(&ROOT_KEY);
    out.extend_from_slice(&epoch.to_be_bytes());
    out.push(BOB);
    out.extend_from_slice(&(chains.len() as u32).to_be_bytes());
    for &(e, send, receive) in chains {
        out.extend_from_slice(&e.to_be_bytes());
        chain(&mut out, send);
        chain(&mut out, receive);
    }
    out.extend_from_slice(&(skipped.len() as u32).to_be_bytes());
    for &(e, n) in skipped {
        out.extend_from_slice(&e.to_be_bytes());
        out.extend_from_slice(&n.to_be_bytes());
        out.extend_from_slice(&stored(n));
    }
    out
}

/// The stored keys of state bytes, as `(epoch, number, key)` in stored order.
fn store_of(bytes: &[u8]) -> Vec<(u64, u64, [u8; 32])> {
    const FIXED_PREFIX: usize = 1 + 32 + 8 + 1 + 4;
    const CHAINS_ENTRY: usize = 8 + 2 * (1 + 32 + 8);
    const ENTRY: usize = 8 + 8 + 32;
    let chains = u32::from_be_bytes(bytes[42..46].try_into().unwrap()) as usize;
    let at = FIXED_PREFIX + chains * CHAINS_ENTRY;
    let count = u32::from_be_bytes(bytes[at..at + 4].try_into().unwrap()) as usize;
    let entries = &bytes[at + 4..];
    assert_eq!(entries.len(), count * ENTRY, "the store runs to the end");
    entries
        .chunks(ENTRY)
        .map(|c| {
            (
                u64::from_be_bytes(c[0..8].try_into().unwrap()),
                u64::from_be_bytes(c[8..16].try_into().unwrap()),
                c[16..48].try_into().unwrap(),
            )
        })
        .collect()
}

/// The decoded state, after checking that the decoder accepts the bytes and
/// writes them back unchanged.
fn restore(bytes: &[u8]) -> State {
    let state = State::from_bytes(bytes).expect("the decoder accepts the start");
    assert_same_bytes(
        &state.to_bytes(),
        bytes,
        "the start re-encodes to the same bytes",
    );
    state
}

/// `after` equals `before`, or a panic that names `what` and the first
/// difference rather than printing a hundred kilobytes.
fn assert_same_bytes(after: &[u8], before: &[u8], what: &str) {
    if after != before {
        let at = after.iter().zip(before).position(|(a, b)| a != b);
        panic!(
            "{what}: the bytes differ (length {} against {}, first difference at offset {:?}; \
             store length {} against {})",
            after.len(),
            before.len(),
            at,
            store_of(after).len(),
            store_of(before).len(),
        );
    }
}

/// The policy constants these literals are written against.
fn assert_policy() {
    assert_eq!(MAX_SKIP, 1_000);
    assert_eq!(MAX_SKIPPED_STORE, 2_000);
}

/// `receive(epoch, None, n)` on the state `start` decodes to, which must be
/// refused as `want` and leave the bytes as they were.
fn assert_refused(start: &[u8], epoch: u64, n: u64, want: SpqrError) {
    let mut state = restore(start);
    assert_eq!(state.receive(epoch, None, n), Err(want));
    assert_same_bytes(
        &state.to_bytes(),
        start,
        "a refused skip leaves the state as it was",
    );
}

/// Numbers `from..to` under `epoch`.
fn run(epoch: u64, from: u64, to: u64) -> impl Iterator<Item = (u64, u64)> {
    (from..to).map(move |n| (epoch, n))
}

#[test]
fn a_request_past_both_bounds_is_refused_as_too_many_skipped() {
    assert_policy();
    // Epoch 0, receiving chain at 0, a full store of 2,000 keys at numbers
    // 5,000..6,999. Message 1,002 asks for a skip to 1,001: 1,001 keys, past
    // `MAX_SKIP`, and 2,000 + 1,001 past the store. Step 1 comes first.
    let full: Vec<_> = run(0, 5_000, 7_000).collect();
    assert_eq!(full.len(), 2_000);
    let start = state_bytes(0, &[EPOCH_0], &full);
    assert_refused(&start, 0, 1_002, SpqrError::TooManySkipped);

    // The same with two of the 2,000 keys, (0, 1) and (0, 2), in the range of
    // the skip. Step 1 refuses before step 2 would delete them, on a copy or
    // otherwise: both are still there, with their keys.
    let mut in_range = vec![(0, 1), (0, 2)];
    in_range.extend(run(0, 5_000, 6_998));
    assert_eq!(in_range.len(), 2_000);
    let start = state_bytes(0, &[EPOCH_0], &in_range);
    assert_refused(&start, 0, 1_002, SpqrError::TooManySkipped);
    let mut state = restore(&start);
    let _ = state.receive(0, None, 1_002);
    let after = store_of(&state.to_bytes());
    assert!(after.contains(&(0, 1, stored(1))));
    assert!(after.contains(&(0, 2, stored(2))));
}

#[test]
fn the_store_bound_alone_is_refused_as_skipped_store_full() {
    assert_policy();
    // The control for the test above: the same full store, message 1,001, a
    // skip of exactly `MAX_SKIP` keys. Only the store bound is broken.
    let full: Vec<_> = run(0, 5_000, 7_000).collect();
    let start = state_bytes(0, &[EPOCH_0], &full);
    assert_refused(&start, 0, 1_001, SpqrError::SkippedStoreFull);
}

#[test]
fn keys_under_another_epoch_count_against_the_store() {
    assert_policy();
    // Epoch 1 is current, with chains for 0 and 1 (both receiving at 0), and
    // 1,999 keys stored under epoch 0 at 5,000..6,998. A skip on epoch 1
    // counts them: two keys more is 2,001, refused.
    let other: Vec<_> = run(0, 5_000, 6_999).collect();
    assert_eq!(other.len(), 1_999);
    let start = state_bytes(1, &[EPOCH_0, EPOCH_1], &other);
    assert_refused(&start, 1, 3, SpqrError::SkippedStoreFull);

    // One key more is 2,000, the edge, accepted.
    let mut state = restore(&start);
    assert!(state.receive(1, None, 2).is_ok());
    assert_eq!(state.skipped_len(), 2_000);
    assert_eq!(state.receive_count(1), Some(2));
}

#[test]
fn another_epochs_keys_in_the_range_are_neither_purged_nor_free() {
    assert_policy();
    // Epoch 1 current, chains for 0 and 1, 1,999 keys under epoch 0: (0, 1),
    // (0, 2) and 5,000..6,996. A skip on epoch 1 from 0 to 2 has (0, 1) and
    // (0, 2) in its numeric range, but they are another epoch's: step 2 does
    // not delete them, so 1,999 + 2 is counted and refused.
    let mut other = vec![(0, 1), (0, 2)];
    other.extend(run(0, 5_000, 6_997));
    assert_eq!(other.len(), 1_999);
    let start = state_bytes(1, &[EPOCH_0, EPOCH_1], &other);
    assert_refused(&start, 1, 3, SpqrError::SkippedStoreFull);
}

#[test]
fn a_replacement_at_the_cap_through_the_public_api() {
    assert_policy();
    // Epoch 0, receiving chain at 0, 1,999 keys: (0, 1), (0, 2) and
    // 5,000..6,996. Message 4 asks for a skip to 3: it deletes (0, 1) and
    // (0, 2) from the copy, and 1,997 + 3 is exactly 2,000, accepted.
    let mut keys = vec![(0, 1), (0, 2)];
    keys.extend(run(0, 5_000, 6_997));
    assert_eq!(keys.len(), 1_999);
    let start = state_bytes(0, &[EPOCH_0], &keys);

    let mut state = restore(&start);
    assert!(state.receive(0, None, 4).is_ok());
    assert_eq!(state.skipped_len(), 2_000);
    assert_eq!(state.receive_count(0), Some(4));
    let after = store_of(&state.to_bytes());
    assert_eq!(after.len(), 2_000);
    for n in 1..=3 {
        let held: Vec<_> = after.iter().filter(|s| s.0 == 0 && s.1 == n).collect();
        assert_eq!(held.len(), 1, "one key stored for (0, {n})");
        assert_ne!(held[0].2, stored(n), "(0, {n}) holds a derived key");
    }
    // The survivors keep their order, and the derived keys follow them.
    let survivors: Vec<_> = run(0, 5_000, 6_997).collect();
    let kept: Vec<_> = after[..1_997].iter().map(|s| (s.0, s.1)).collect();
    assert_eq!(kept, survivors);
    let derived: Vec<_> = after[1_997..].iter().map(|s| (s.0, s.1)).collect();
    assert_eq!(derived, vec![(0, 1), (0, 2), (0, 3)]);

    // On a fresh copy, message 5 asks for a skip to 4: 1,997 + 4 is 2,001,
    // refused, and the two held keys are not deleted.
    assert_refused(&start, 0, 5, SpqrError::SkippedStoreFull);
}
