//! Operational benchmarks: what the paths a deployment depends on actually
//! cost.
//!
//! These are operational benchmarks for the paths a deployment depends on --
//! not microbenchmarks of primitives, which would measure dalek and
//! libcrux, but the costs an operator sizing a relay or a mobile client has to
//! plan around.
//!
//! **No criterion, deliberately.** It is the standard tool and it would give
//! better statistics than the medians below. It also pulls about fifty crates
//! into the dev tree of a cryptographic core whose whole argument is a small,
//! auditable dependency surface, and `tests/timing.rs` already established a
//! measurement idiom here that costs nothing. When these numbers start driving
//! optimisation decisions rather than sizing ones, that trade is worth
//! revisiting; today they are sizing ones.
//!
//! Reported as medians of cropped samples, same as `tests/timing.rs`. Run:
//!
//! ```text
//! cargo test --release -p tacenta-core --test benchmarks -- --ignored --nocapture
//! ```
//!
//! **Read them from a release build only.** A debug build is roughly an order
//! of magnitude slower here and the ratios between rows shift, so a debug
//! number is not a slow version of the truth, it is a different measurement.

use rand::SeedableRng;
use std::time::Instant;
use tacenta_core::sessions::{self, Session, establish_initiator, establish_responder};

fn rng(seed: u64) -> rand::rngs::StdRng {
    rand::rngs::StdRng::seed_from_u64(seed)
}

fn crop_slowest(mut xs: Vec<f64>, frac: f64) -> Vec<f64> {
    xs.sort_by(|p, q| p.partial_cmp(q).unwrap());
    let keep = ((xs.len() as f64) * (1.0 - frac)) as usize;
    xs.truncate(keep.max(2));
    xs
}

fn median(xs: &[f64]) -> f64 {
    let mut v = xs.to_vec();
    v.sort_by(|p, q| p.partial_cmp(q).unwrap());
    v[v.len() / 2]
}

/// Run `f` `n` times, returning the median in microseconds.
fn bench<F: FnMut()>(n: usize, mut f: F) -> f64 {
    // Warm up: the first call through a path pays for page faults and cold
    // branch predictors, and reporting that as the cost would overstate every
    // row by a constant nobody could see.
    for _ in 0..3 {
        f();
    }
    let mut times = Vec::with_capacity(n);
    for _ in 0..n {
        let s = Instant::now();
        f();
        times.push(s.elapsed().as_nanos() as f64);
    }
    median(&crop_slowest(times, 0.10)) / 1000.0
}

fn row(label: &str, micros: f64) {
    println!("  {label:<46} {micros:>9.1} us");
}

#[test]
#[ignore = "measurement, not a pass/fail gate; run with --ignored --release"]
fn operational_costs() {
    let mut r = rng(11);

    println!();
    println!("Operational costs (median of 100, slowest tenth cropped)");
    println!();
    println!("First contact");

    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);

    // Registration. Paid once per device, but it is the cost of coming online
    // for the first time and of every replenishment once that exists.
    row(
        "create_prekeys(32), a device registering",
        bench(20, || {
            let _ = bob_id.create_prekeys(32, &mut rng(1));
        }),
    );

    let mut bob_prekeys = bob_id.create_prekeys(32, &mut r);
    let bundle = bob_prekeys.publish();

    row(
        "publish(), handing out one bundle",
        bench(100, || {
            let _ = bob_prekeys.publish();
        }),
    );

    // PQXDH plus the first ratchet step, both sides. This is what a first
    // message to a new peer costs, and it is where the ML-KEM work lands.
    row(
        "establish_initiator, PQXDH + first ratchet",
        bench(20, || {
            let _ = establish_initiator(&alice_id, &bundle, &mut rng(2)).unwrap();
        }),
    );

    println!();
    println!("Steady state, per message");

    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let initial = alice.encrypt(b"hello", &mut r).unwrap();
    let (mut bob, _) = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();

    // A short message and a realistic one. The post-quantum stack adds a fixed
    // per-message cost that does not scale with the payload, so the gap between
    // these two rows is the part that does.
    row(
        "encrypt, 16-byte payload",
        bench(100, || {
            let _ = alice.encrypt(&[0u8; 16], &mut rng(3)).unwrap();
        }),
    );
    row(
        "encrypt, 4 KiB payload",
        bench(100, || {
            let _ = alice.encrypt(&[0u8; 4096], &mut rng(4)).unwrap();
        }),
    );

    // Decrypt has to be measured on messages nobody has consumed yet, so a
    // batch is prepared outside the timed region and drained inside it.
    let mut queued: Vec<Vec<u8>> = (0..120)
        .map(|_| alice.encrypt(&[0u8; 16], &mut r).unwrap())
        .collect();
    queued.reverse();
    let mut drained = 0usize;
    row(
        "decrypt, 16-byte payload, in order",
        bench(100, || {
            if let Some(m) = queued.pop() {
                let _ = bob.decrypt(&m, &mut rng(5)).unwrap();
                drained += 1;
            }
        }),
    );
    assert!(drained > 50, "the decrypt bench ran out of queued messages");

    println!();
    println!("Persistence, paid on every mutating call by a durable store");

    // A durable-storage caller exports and rewrites its whole state after
    // every encrypt and every decrypt, so this is not a
    // once-per-restart cost -- it is per message, for anyone using durable
    // storage. Worth having next to the encrypt row above rather than
    // discovered against it.
    let snapshot = alice.export();
    println!(
        "  (a single session serializes to {} bytes)",
        snapshot.len()
    );
    row(
        "Session::export",
        bench(100, || {
            let _ = alice.export();
        }),
    );
    row(
        "Session::import",
        bench(100, || {
            let _ = Session::import(&snapshot).unwrap();
        }),
    );

    println!();
    println!("Recovery from loss");

    // Out-of-order delivery: the receiver derives and stores the keys it
    // skipped. This is the cost of a gap in the network, and the same
    // mechanism `tests/timing.rs` measures from the attacker's side.
    for gap in [1u32, 50, 500] {
        // A fresh bundle per gap: `establish_responder` consumes the one-time
        // prekey the bundle names, so reusing one is `UnknownPrekeyId` on the
        // second pass -- which is the one-time guarantee working, not a bug.
        let fresh_bundle = bob_prekeys.publish();
        let mut a2 = establish_initiator(&alice_id, &fresh_bundle, &mut r).unwrap();
        let first = a2.encrypt(b"open", &mut r).unwrap();
        let (mut b2, _) = establish_responder(&bob_id, &mut bob_prekeys, &first, &mut r).unwrap();
        for _ in 0..gap {
            let _ = a2.encrypt(b"lost", &mut r).unwrap();
        }
        let arrived = a2.encrypt(b"found", &mut r).unwrap();
        let snap = b2.export();
        row(
            &format!("decrypt after {gap} lost messages"),
            bench(20, || {
                let mut fresh = Session::import(&snap).unwrap();
                let _ = fresh.decrypt(&arrived, &mut rng(6)).unwrap();
            }),
        );
        let _ = b2.decrypt(&arrived, &mut r);
    }

    println!();
}

/// What a forged header aimed at a **full** skipped-key store costs the
/// receiver (CR-19).
///
/// `Triple::receive` reports `SkippedStoreFull` before it checks the tag, so a
/// forged far-future header on a full store drives the eviction-and-retry loop
/// -- cloning the 2000-entry store and deriving up to `MAX_SKIP` keys per
/// attempt -- and commits nothing, so it can be repeated. This row is the cost
/// of one such attempt, next to the ordinary forged-message cost in
/// `tests/timing.rs`, which measures against an *empty* store. It is a sizing
/// number, not a pass/fail gate, and is `#[ignore]` like the row set above.
#[test]
#[ignore = "measurement, not a pass/fail gate; run with --ignored --release"]
fn forged_header_against_a_full_store() {
    use tacenta_core::ratchet::{MAX_SKIP, MAX_SKIPPED_STORE};

    let mut r = rng(41);

    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(4, &mut r);
    let bundle = bob_prekeys.publish();
    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let initial = alice.encrypt(b"hello", &mut r).unwrap();
    let (mut bob, _) = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();

    // One round: Alice sends MAX_SKIP + 1 on a fresh chain, Bob reads only the
    // last (storing MAX_SKIP keys), then Bob replies so the next round starts a
    // new chain. Two rounds fill the store to exactly its cap.
    let round = |alice: &mut Session, bob: &mut Session, r: &mut rand::rngs::StdRng| {
        for i in 0..MAX_SKIP {
            let _ = alice.encrypt(format!("m{i}").as_bytes(), r).unwrap();
        }
        let last = alice.encrypt(b"last", r).unwrap();
        bob.decrypt(&last, r).unwrap();
        let reply = bob.encrypt(b"ack", r).unwrap();
        alice.decrypt(&reply, r).unwrap();
    };
    round(&mut alice, &mut bob, &mut r);
    round(&mut alice, &mut bob, &mut r);
    assert_eq!(
        2 * MAX_SKIP as usize,
        MAX_SKIPPED_STORE,
        "store filled to cap"
    );

    // A genuine third-round message that needs another MAX_SKIP slots, torn so
    // its tag fails: this is the forged far-future header against the full
    // store.
    for i in 0..MAX_SKIP {
        let _ = alice.encrypt(format!("t{i}").as_bytes(), &mut r).unwrap();
    }
    let mut forged = alice.encrypt(b"forge", &mut r).unwrap();
    let last = forged.len() - 1;
    forged[last] ^= 0x01;

    // Fresh receiver per sample from the full-store snapshot, via export/import
    // -- `Session` is deliberately not `Clone` -- so every attempt sees the
    // full store rather than one an earlier attempt already drained.
    let snapshot = bob.export();
    row(
        "forged header against a full store",
        bench(20, || {
            let mut fresh = Session::import(&snapshot).unwrap();
            let outcome = fresh.decrypt(&forged, &mut rng(9));
            assert!(outcome.is_err(), "the forged header must be rejected");
        }),
    );

    println!();
}
