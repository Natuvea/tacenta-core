//! A property test of the ML-KEM Braid's state machine (`tacenta-braid`, `Braid::send`,
//! `receive`, `commit`, `invariant`, `epoch`, `failed`) over generated delivery
//! schedules, against `tacenta-spec/protocol/mlkem-braid.md`.
//!
//! The scripted walk in `braid/src/tests.rs` drives one fixed send/receive pattern
//! with random key material. Here the schedule itself is generated: which party sends,
//! which queued message is delivered next, in any order, and whether a delivered
//! message is dropped from its queue or stays to be delivered again. Every message is
//! one an honest peer sent; no message is forged or altered.
//!
//! Generator: `StdRng::seed_from_u64(SEED + run)` for each of `RUNS` runs of `STEPS`
//! steps; the ML-KEM randomness comes from the same generator. Replay: the seed is
//! fixed in this file, so every run is the same run, and each assertion message names
//! the run and the step. Case count: `RUNS` (16) schedules of `STEPS` (2,000) steps;
//! at this seed each run ends at epoch 4 or 5.

use rand::{Rng, SeedableRng, rngs::StdRng};
use std::collections::BTreeMap;
use tacenta_braid::{Braid, Msg};

const SEED: u64 = 0x0b4a_1d00;
const RUNS: u64 = 16;
const STEPS: usize = 2000;
/// `Braid::state_tag` of `Ct2Sampled`, the one state that acts on the next epoch's
/// messages.
const CT2_SAMPLED: u8 = 10;

/// Under every generated schedule of honest messages, on both sides and after every
/// step:
/// - the Braid never fails;
/// - `invariant` holds;
/// - a send never raises the epoch;
/// - each epoch's key is output at most once on each side, labelled with an epoch the
///   side has reached; and
/// - when both sides have output a key for an epoch, the two keys are equal; and
/// - a received message stamped with an epoch other than the state's own (in
///   `Ct2Sampled`, the next) outputs nothing and leaves the state's persisted bytes
///   unchanged.
///
/// Across all runs, at least `2 * RUNS` epochs complete on both sides (55 at this seed
/// when written; each run ends at epoch 4 or 5, so a run covers three or four complete
/// epochs, not more), and at least `RUNS` messages are ignored for their epoch, so
/// neither clause is vacuous. The message type is not varied apart from the epoch, so
/// the page's other ignoring rules (a type the state is not waiting for, a message
/// with no codeword) are reached only as the schedule happens to reach them and are
/// not asserted.
///
/// Specification: mlkem-braid.md, The shape, in one paragraph: "Each completed
/// exchange is an epoch, each epoch yields one shared secret"; Parameters and
/// derivations, The epoch key: "The epoch's key is `KDF_OK(K, e)` for that epoch `e`"
/// (one secret and one derivation, so both sides' keys for an epoch are equal); When an
/// epoch completes: "Each epoch's key is output once on each side, labelled with that
/// epoch. 1. The encapsulating party's send outputs it at (7). 2. The other party's
/// receive outputs it later, at (5)";
/// What a send and a receive return: "A send never raises the epoch"; Failure: "A MAC
/// that does not verify moves the Braid to `Failed` ... So does each of the following,
/// and nothing else", none of which an honest schedule reaches (the KEM failures are
/// "defensive for an honest store", and "No honest run reaches either epoch" at the
/// ceiling); What a receive ignores: "A state acts only on a message stamped with its
/// own epoch (in `Ct2Sampled`, the next) and of a type it is waiting for; every other
/// message leaves it unchanged" (the epoch half).
#[test]
fn honest_schedules_agree_on_every_epoch_key() {
    let (mut agreed_total, mut ignored) = (0usize, 0usize);
    for run in 0..RUNS {
        let mut r = StdRng::seed_from_u64(SEED + run);
        let secret = b"a preshared secret from the handshake";
        let mut side = [Braid::initiator(secret), Braid::responder(secret)];
        // queue[i] holds messages sent by side i, not yet dropped.
        let mut queue: [Vec<Msg>; 2] = [Vec::new(), Vec::new()];
        let mut keys: [BTreeMap<u64, [u8; 32]>; 2] = [BTreeMap::new(), BTreeMap::new()];
        for step in 0..STEPS {
            let who = r.gen_range(0..2usize);
            let action = r.gen_range(0..10u8);
            let output = if action < 5 || queue[1 - who].is_empty() {
                let before = side[who].epoch();
                let (m, _, out, next) = side[who].send(&mut r);
                assert!(
                    next.epoch() <= before,
                    "run {run} step {step}: a send raised the epoch"
                );
                side[who] = next;
                queue[who].push(m);
                out
            } else {
                let q = &mut queue[1 - who];
                let at = r.gen_range(0..q.len());
                // Delivered out of order; kept for a later repeat 1 time in 4.
                let m = if r.gen_range(0..4u8) == 0 {
                    q[at]
                } else {
                    q.remove(at)
                };
                let epoch = side[who].epoch();
                let awaited = if side[who].state_tag() == CT2_SAMPLED {
                    epoch.checked_add(1)
                } else {
                    Some(epoch)
                };
                let before = side[who].to_bytes();
                let (_, out, next) = side[who].receive(&m);
                side[who].commit(next);
                if Some(m.epoch) != awaited {
                    ignored += 1;
                    assert!(
                        out.is_none() && side[who].to_bytes()[..] == before[..],
                        "run {run} step {step}: a message stamped {} changed a state at epoch {epoch}",
                        m.epoch
                    );
                }
                out
            };
            if action == 9 && !queue[who].is_empty() {
                // A message lost in transit.
                let at = r.gen_range(0..queue[who].len());
                queue[who].remove(at);
            }
            assert!(
                !side[who].failed(),
                "run {run} step {step}: an honest schedule failed"
            );
            assert!(side[who].invariant(), "run {run} step {step}: invariant");
            if let Some(o) = output {
                assert!(
                    o.key_epoch <= side[who].epoch(),
                    "run {run} step {step}: a key labelled with an epoch not reached"
                );
                assert!(
                    keys[who].insert(o.key_epoch, o.key).is_none(),
                    "run {run} step {step}: epoch {} output twice on one side",
                    o.key_epoch
                );
                if let Some(other) = keys[1 - who].get(&o.key_epoch) {
                    assert_eq!(
                        *other, o.key,
                        "run {run} step {step}: the two sides' keys for epoch {} differ",
                        o.key_epoch
                    );
                }
            }
        }
        agreed_total += keys[0].keys().filter(|e| keys[1].contains_key(e)).count();
    }
    assert!(
        ignored >= RUNS as usize,
        "only {ignored} messages were ignored for their epoch"
    );
    assert!(
        agreed_total >= 2 * RUNS as usize,
        "only {agreed_total} epochs completed on both sides across {RUNS} runs"
    );
}
