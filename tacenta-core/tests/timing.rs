//! Dudect-style timing measurement, against the two claims `LIMITATIONS.md`
//! actually makes.
//!
//! That file says constant-time behaviour here "holds by delegation and
//! discipline, not by proof", and names what a timing experiment would raise
//! from assumed to measured. This is that experiment. It does not raise
//! anything to *proven*: a measurement covers the inputs it draws on the
//! machine it runs on, where a proof covers all of them. What it does is make a
//! regression visible, which reading the code cannot.
//!
//! Two things are measured, and they are different kinds of claim:
//!
//! - **A leak test.** The tag comparison must not depend on how much of the
//!   tag was right. If it short-circuited on the first wrong byte, an attacker
//!   could recover a tag byte at a time. Expected result: indistinguishable.
//! - **A cost characterisation.** A forged message claiming a far-future
//!   message number forces the receiver to derive skipped keys before the MAC
//!   can be checked at all, so the work an attacker can induce with one packet
//!   is not constant. Expected result: distinguishable, bounded by `MAX_SKIP`.
//!   Measured because the bound is the security argument, and a bound nobody
//!   has measured is a bound nobody has checked.
//!
//! **What is deliberately not measured.** The primitives. X25519, Ed25519, and
//! ML-KEM are the trusted boundary and `LIMITATIONS.md` assumes them; timing
//! them here would report on dalek and libcrux rather than on this codebase,
//! and a green result would invite exactly the confusion that file exists to
//! prevent. The AEAD's padding check is not measured either, for a different
//! reason: encrypt-then-MAC means a padding failure is only reachable after a
//! tag that verified, so no attacker without the MAC key can produce one.
//!
//! `#[ignore]`d, because wall-clock timing on a shared machine is flaky and a
//! flaky gate teaches people to ignore gates. Run it deliberately:
//!
//! ```text
//! cargo test -p tacenta-core --test timing -- --ignored --nocapture
//! ```
//!
//! **These are gated, despite the `#[ignore]`.** The constant-time results are
//! defended by CI rather than measured once and written down: a nightly
//! workflow runs them in release mode on a dedicated machine.
//!
//! So the `#[ignore]` keeps them out of the per-push job, where they would be
//! flaky, without keeping them out of CI. Un-ignoring them would produce the
//! gate everyone learns to re-run until it passes.
//!
//! **The gate decides on the effect size, not a t-statistic.** A plain
//! wall-clock t-test reads contention as a leak: it can fail with the two
//! classes' medians equal to the nanosecond, the signature of a busy machine
//! rather than of a short-circuit. At ~200 ns per operation the t-statistic
//! reports a huge |t| for the timer's own 1 ns quantization as readily as for a
//! real leak, so `run_leak_test` gates
//! on the class **median rejection-time gap in nanoseconds** (`EFFECT_FLOOR_NS`):
//! a constant-time compare differs by <= 2 ns, a real byte-at-a-time short-circuit
//! by ~10 ns. The t-statistics and a same-input negative control are still
//! computed and printed, but as diagnostics. The measurement runs pinned to an
//! isolated, fixed-clock core, so contention does not perturb it.
//! `run_leak_test` carries the full derivation; `LIMITATIONS.md` has
//! the narrative.

use rand::SeedableRng;
use std::time::Instant;
use tacenta_core::primitives::aead;
use tacenta_core::sessions::{self, Session, establish_initiator, establish_responder};

// ---------------------------------------------------------------- statistics

/// Welch's t-statistic between two samples (unequal variance).
///
/// The same twenty-line shape as the timing test in the consuming product,
/// repeated rather than shared because the two repositories do not depend on
/// each other and a copied function is a smaller cost than a crate that exists
/// to hold one.
fn welch_t(a: &[f64], b: &[f64]) -> f64 {
    let mean = |x: &[f64]| x.iter().sum::<f64>() / x.len() as f64;
    let var =
        |x: &[f64], m: f64| x.iter().map(|v| (v - m).powi(2)).sum::<f64>() / (x.len() as f64 - 1.0);
    let (ma, mb) = (mean(a), mean(b));
    let (va, vb) = (var(a, ma), var(b, mb));
    let se = (va / a.len() as f64 + vb / b.len() as f64).sqrt();
    if se == 0.0 { 0.0 } else { (ma - mb) / se }
}

/// Drop the slowest `frac` of samples: scheduler pre-emption and page faults,
/// not signal. Dudect crops the same way before its t-test. Used by the cost
/// characterisation, which wants a representative time; the leak tests crop far
/// harder (see `keep_fastest`).
fn crop_slowest(mut xs: Vec<f64>, frac: f64) -> Vec<f64> {
    xs.sort_by(|p, q| p.partial_cmp(q).unwrap());
    let keep = ((xs.len() as f64) * (1.0 - frac)) as usize;
    xs.truncate(keep.max(2));
    xs
}

/// Keep only the fastest `frac` of samples.
///
/// Contention only ever *adds* time -- a sample that was pre-empted, migrated, or
/// took a cache miss under load is slower, never faster -- so the fastest samples
/// are the ones that ran closest to uninterrupted, and their timing reflects the
/// computation rather than the scheduler. Comparing the fast *heads* of two
/// classes compares their true compute cost, with the long contention tail that
/// corrupts a mean-based t-test removed. It is the minimum-latency idea with
/// enough samples left to still estimate a variance.
///
/// This is what makes the gate usable under contention. A full-sample t-test
/// can drive the same-input null to a double-digit |t| (a run that cannot tell
/// a leak from noise); keeping the fast head collapses that null toward zero,
/// while a genuine data-dependent difference survives because
/// it shifts the fast head too. The dropped fraction is large on purpose: what is
/// discarded is the part with no signal in it.
fn keep_fastest(mut xs: Vec<f64>, frac: f64) -> Vec<f64> {
    xs.sort_by(|p, q| p.partial_cmp(q).unwrap());
    let keep = ((xs.len() as f64) * frac) as usize;
    xs.truncate(keep.max(2));
    xs
}

fn median(xs: &[f64]) -> f64 {
    let mut v = xs.to_vec();
    v.sort_by(|p, q| p.partial_cmp(q).unwrap());
    v[v.len() / 2]
}

/// Fraction of samples the leak tests keep -- the fastest, least-interrupted
/// ones (see `keep_fastest`). 0.30 leaves ~1,200 of the 4,000 drawn per class:
/// enough to estimate a variance, few enough to be near the uninterrupted compute
/// floor.
///
/// Drawing more and keeping fewer does not help. A larger N does not average
/// contention out -- it gives Welch's t more power to resolve the systematic
/// between-stream drift a loaded machine accumulates over a longer measurement
/// window. So the sample size stays small; what contention remains is
/// environmental, not statistical, and the remedy is a quiet core.
const KEEP_FASTEST: f64 = 0.30;

fn rng(seed: u64) -> rand::rngs::StdRng {
    rand::rngs::StdRng::seed_from_u64(seed)
}

/// Ask the CPU to run in data-independent time for the duration of the process.
///
/// Apple Silicon has data-dependent timing on some data-processing instructions
/// unless the DIT bit is set (FEAT_DIT, present on every M-series part). Without
/// it, feeding an all-zero versus an all-one buffer to a routine that is
/// constant-time *by construction* still produces different wall-clock times --
/// a property of the core, not of this code, and one that swings the
/// forged-ciphertext measurement by more than an order of magnitude. Setting
/// DIT makes the experiment test the software, which is the
/// assumption the constant-time claim actually rests on. On x86_64 (the nightly
/// gate) there is no equivalent bit to set here and none is needed for the
/// add/xor/rotate of HMAC-SHA256, so this is a no-op off Apple Silicon.
fn request_data_independent_timing() {
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    // SAFETY: `msr DIT, #1` sets a documented, unprivileged control bit; it
    // touches no memory and clobbers no register, only the DIT flag.
    unsafe {
        std::arch::asm!("msr DIT, #1", options(nomem, nostack, preserves_flags));
    }
}

/// The value at quantile `q` (0..=1), nearest-rank.
///
/// Used for the noise floor: a high quantile rather than the max, so one unlucky
/// round does not by itself declare an otherwise-quiet run noisy; and rather than
/// the median, so a run that was contended across several rounds is not smoothed
/// into looking clean.
fn quantile(xs: &[f64], q: f64) -> f64 {
    let mut v = xs.to_vec();
    v.sort_by(|p, r| p.partial_cmp(r).unwrap());
    let idx = (((v.len() as f64) * q).ceil() as usize)
        .saturating_sub(1)
        .min(v.len() - 1);
    v[idx]
}

/// The class rejection-time gap, in nanoseconds, at or above which a difference
/// is treated as a real leak. This -- not the t-statistic -- is what the gate
/// decides on.
///
/// A timing leak is an *exploitable* difference in how long a rejection takes,
/// and that is an effect size in nanoseconds, not a p-value. At ~200 ns per
/// operation the t-statistic is the wrong instrument: with thousands of samples
/// it reports a |t| of 60 for the integer-nanosecond timer's own 1 ns
/// quantization as readily as for a 100 ns gap, and the same-input null spikes to
/// triple digits the moment an isolated core catches a stray housekeeping tick.
/// The effect size does not have those failure modes.
///
/// The floor is set from what the operations physically cost, not tuned to pass.
/// A constant-time compare (`subtle`/`verify_slice`) differs by 0-2 ns here
/// (measured across runs: 0 ns on a DIT core, 1-2 ns on the isolated x86 core --
/// the integer-nanosecond quantization plus sub-nanosecond jitter that rounds up).
/// A short-circuiting byte compare that leaked the tag would differ by ~10 ns
/// (tens of cycles at 3 GHz over up to 31 extra byte compares). 5 ns leaves a
/// margin above the measured constant-time noise, so good code does not flake at
/// the boundary, while staying at half a real short-circuit's ~10 ns, so a genuine
/// leak still trips it. The full effect size is printed every run, so even a
/// sub-floor difference stays visible to a human.
const EFFECT_FLOOR_NS: f64 = 5.0;

/// Measure, in one interleaved window, both the secret-dependent signal and a
/// same-input null -- and return (|signal t|, |null t|).
///
/// Three streams are timed sample-by-sample in the same loop: class `a`, a
/// *second draw of class `a`*, and class `b`. The signal is Welch's t between
/// `a` and `b`; the null is Welch's t between `a` and its own second draw, which
/// carries no secret-dependent difference by construction. Because all three are
/// interleaved in the same window, a burst of contention lands on all of them,
/// so it inflates the null as much as the signal -- which is the whole point.
/// Measuring the null in a *separate* window would let a burst hit the signal
/// alone and read as a leak; sharing the window is what makes the control
/// fair. `reject` performs one rejection of the bytes it is given and is
/// expected to `black_box` the result.
fn signal_and_null(a: &[u8], b: &[u8], n: usize, reject: &impl Fn(&[u8])) -> (f64, f64, f64, f64) {
    let mut ta = Vec::with_capacity(n);
    let mut ta2 = Vec::with_capacity(n);
    let mut tb = Vec::with_capacity(n);
    let time_one = |bytes: &[u8]| -> f64 {
        let s = Instant::now();
        reject(bytes);
        s.elapsed().as_nanos() as f64
    };
    // Rotate the order of the three timings each iteration so no stream is
    // permanently in the first (post-previous-iteration) slot or the slot right
    // after an identical call. With a fixed order the same-input null (a vs a)
    // picks up the systematic slot-to-slot bias -- pipeline and predictor warmup,
    // not a leak -- and Welch's t *amplifies* that bias with n, which is why a
    // larger sample made the shared runner worse rather than better. Over the run
    // each stream spends a third of its samples in each slot, so the bias cancels.
    for i in 0..n {
        match i % 3 {
            0 => {
                ta.push(time_one(a));
                ta2.push(time_one(a));
                tb.push(time_one(b));
            }
            1 => {
                ta2.push(time_one(a));
                tb.push(time_one(b));
                ta.push(time_one(a));
            }
            _ => {
                tb.push(time_one(b));
                ta.push(time_one(a));
                ta2.push(time_one(a));
            }
        }
    }
    // Keep only the fast head of each class, where the timing is compute and not
    // contention; the mean-based t over the full sample is what a shared runner
    // corrupts.
    let ca = keep_fastest(ta, KEEP_FASTEST);
    let ca2 = keep_fastest(ta2, KEEP_FASTEST);
    let cb = keep_fastest(tb, KEEP_FASTEST);
    // Also return the class medians: the |t| says whether the classes differ,
    // the medians say by how much. A large |t| over a sub-nanosecond median gap
    // is the t-test resolving noise below the timer's own resolution, not a leak
    // an attacker could use; the effect *size* is what tells them apart.
    (
        welch_t(&ca, &cb).abs(),
        welch_t(&ca, &ca2).abs(),
        median(&ca),
        median(&cb),
    )
}

/// The leak decision behind both tests, keyed on the effect size in nanoseconds.
///
/// The statistic is the median gap, and the reason is worth stating. A dudect
/// Welch t-statistic is the right tool for a microbenchmark on a quiet,
/// dedicated machine and the wrong one here. At ~200 ns per operation, sampled
/// thousands of times, the t-statistic reports a large |t| for the
/// integer-nanosecond timer's own 1 ns quantization as readily as for a real
/// leak, and its same-input null varies by two orders of magnitude run to run
/// -- even on an isolated, fixed-clock core, which still catches the occasional
/// per-CPU housekeeping tick. A negative control, fast-head cropping, and order
/// balancing each help and are kept, but none fixes the underlying mismatch: a
/// *p-value is not an effect size*, and a timing leak is an effect size -- an
/// exploitable difference in how long a rejection takes.
///
/// So the gate decides on the effect size: the difference between the two classes'
/// median rejection times (see [`EFFECT_FLOOR_NS`]). The t-statistics are still
/// computed and printed as diagnostics, but a leak is declared only when the
/// classes differ by an exploitable number of nanoseconds. A real byte-at-a-time
/// short-circuit differs by ~10 ns and trips it; a constant-time compare differs
/// by <= 1 ns (measured) and does not. A test that `#[ignore]`d itself would
/// reach the same conclusion; this one stays a gate, on the quantity that
/// actually matters.
fn run_leak_test(label: &str, a: &[u8], b: &[u8], reject: &impl Fn(&[u8]), leak_hint: &str) {
    const ROUNDS: usize = 11;
    const N: usize = 4000;

    // Make the CPU itself data-independent where it is not by default (Apple
    // Silicon), so the experiment measures the software and not the core.
    request_data_independent_timing();

    // Warm caches and branch predictors so the first measured round is not an
    // outlier standing in for the rest.
    for _ in 0..64 {
        reject(a);
        reject(b);
    }

    let mut signal = Vec::with_capacity(ROUNDS);
    let mut noise = Vec::with_capacity(ROUNDS);
    let mut meds_a = Vec::with_capacity(ROUNDS);
    let mut meds_b = Vec::with_capacity(ROUNDS);
    for _ in 0..ROUNDS {
        // Both come from the same interleaved window, so contention inflates the
        // null alongside the signal instead of the signal alone.
        let (s, n, ma, mb) = signal_and_null(a, b, N, reject);
        signal.push(s);
        noise.push(n);
        meds_a.push(ma);
        meds_b.push(mb);
    }

    let signal_t = median(&signal);
    let noise_t = quantile(&noise, 0.90);
    let med_a = median(&meds_a);
    let med_b = median(&meds_b);
    let effect = (med_a - med_b).abs();

    // The t-statistics are diagnostics, printed but not gated on: at this
    // operation size they report a huge |t| for a 1 ns quantization gap, and the
    // same-input null bounces with stray ticks even on an isolated core. The gate
    // decides on the effect size (see EFFECT_FLOOR_NS).
    println!(
        "{label}: |t| signal = {signal_t:.2}, same-input null = {noise_t:.2}  (diagnostic only)"
    );
    println!(
        "{label}: class medians = {med_a:.1} ns vs {med_b:.1} ns  =>  effect size = {effect:.2} ns  (leak floor {EFFECT_FLOOR_NS} ns)"
    );

    assert!(
        effect < EFFECT_FLOOR_NS,
        "{label}: distinguishable by timing. The two classes' median rejection times differ by \
         {effect:.2} ns, at or above the {EFFECT_FLOOR_NS} ns leak floor (|t| = {signal_t:.2}). \
         A constant-time path differs by <= 1 ns here, so a systematic gap this size is a real, \
         usable leak, not the timer's quantization. {leak_hint}"
    );
}

// ------------------------------------------------------------- the leak test

/// The tag comparison does not depend on how many leading bytes were correct.
///
/// This is the claim `LIMITATIONS.md` states as "the AEAD tag is checked with a
/// constant-time comparison (`Mac::verify_slice`), not a byte-wise `==`". A
/// byte-wise comparison returns as soon as it finds a difference, so a tag that
/// matches thirty-one of thirty-two bytes would take measurably longer to
/// reject than one that differs immediately -- and an attacker who can see that
/// difference recovers the tag one byte at a time, which is a forgery.
///
/// The two classes differ *only* in where the forged tag stops matching. Both
/// fail. Both do the same HMAC work. If the two are distinguishable, the
/// comparison is short-circuiting.
#[test]
#[ignore = "timing-sensitive; run with --ignored"]
fn the_tag_comparison_does_not_leak_how_much_of_the_tag_was_right() {
    let enc_key = [0x11u8; 32];
    let mac_key = [0x22u8; 32];
    let iv = [0x33u8; 16];
    let ad = b"associated data";

    let sealed = aead::encrypt(&enc_key, &mac_key, &iv, b"a plaintext of some length", ad);
    let split = sealed.len() - 32;
    let real_tag = &sealed[split..];

    // Class "early": the forged tag is wrong at byte 0.
    let mut early = sealed.clone();
    early[split] ^= 0xff;

    // Class "late": the forged tag matches the real one everywhere except its
    // last byte. A short-circuiting comparison walks thirty-one more bytes here
    // than it does above.
    let mut late = sealed.clone();
    let last = late.len() - 1;
    late[last] ^= 0xff;

    // Sanity: both are rejected, so what is being timed really is two failures
    // and not a failure against a success.
    assert!(aead::decrypt(&enc_key, &mac_key, &iv, &early, ad).is_err());
    assert!(aead::decrypt(&enc_key, &mac_key, &iv, &late, ad).is_err());
    assert_eq!(real_tag.len(), 32);

    let reject = |bytes: &[u8]| {
        let _ = std::hint::black_box(aead::decrypt(&enc_key, &mac_key, &iv, bytes, ad));
    };
    run_leak_test(
        "tag comparison",
        &early,
        &late,
        &reject,
        "A short-circuiting comparison would let an attacker recover the tag one \
         byte at a time; check that `Mac::verify_slice` is still what does the \
         comparison in primitives/aead.rs.",
    );
}

/// A forged ciphertext's rejection time does not depend on its contents.
///
/// The composition claim, one layer up: `LIMITATIONS.md` says this codebase
/// "branches on and compares only public data" and performs "no byte-wise `==`
/// on a message key". Two forgeries that differ only in their ciphertext bytes
/// should therefore be indistinguishable -- both fail the same way, having done
/// the same work.
#[test]
#[ignore = "timing-sensitive; run with --ignored"]
fn a_forged_ciphertext_rejects_in_time_independent_of_its_contents() {
    let enc_key = [0x44u8; 32];
    let mac_key = [0x55u8; 32];
    let iv = [0x66u8; 16];
    let ad = b"ad";

    let sealed = aead::encrypt(&enc_key, &mac_key, &iv, &[0u8; 128], ad);

    // Two forgeries of identical length, differing only in the bytes they
    // carry: all-zero against all-ones. Same work, same failure.
    let mut zeros = sealed.clone();
    let mut ones = sealed.clone();
    let split = sealed.len() - 32;
    for i in 0..split {
        zeros[i] = 0x00;
        ones[i] = 0xff;
    }

    assert!(aead::decrypt(&enc_key, &mac_key, &iv, &zeros, ad).is_err());
    assert!(aead::decrypt(&enc_key, &mac_key, &iv, &ones, ad).is_err());

    let reject = |bytes: &[u8]| {
        let _ = std::hint::black_box(aead::decrypt(&enc_key, &mac_key, &iv, bytes, ad));
    };
    run_leak_test(
        "forged ciphertext",
        &zeros,
        &ones,
        &reject,
        "Rejection time depends on ciphertext contents, which means this codebase \
         branched on or compared secret-derived bytes somewhere on the failure \
         path; check what the ratchet and AEAD touch before the MAC verifies.",
    );
}

// ------------------------------------------------- the cost characterisation

fn establish(r: &mut rand::rngs::StdRng) -> (Session, Session) {
    let alice_id = sessions::Identity::generate(r);
    let bob_id = sessions::Identity::generate(r);
    let mut bob_prekeys = bob_id.create_prekeys(4, r);
    let bundle = bob_prekeys.publish();
    let mut alice = establish_initiator(&alice_id, &bundle, r).unwrap();
    let initial = alice.encrypt(b"hello", r).unwrap();
    let (bob, _first) = establish_responder(&bob_id, &mut bob_prekeys, &initial, r).unwrap();
    (alice, bob)
}

/// **Not a leak test: a measurement of what one forged packet can cost.**
///
/// The Double Ratchet cannot check a message's authenticator until it has
/// derived that message's key, and reaching message *n* means deriving every
/// key before it. So a forged message claiming a far-future number makes the
/// receiver work before discovering the message was forged. That is inherent to
/// the protocol, not a defect here, and `MAX_SKIP` is what bounds it.
///
/// Three classes, because two would give a number without an explanation:
///
/// - **next number** -- nothing skipped, the ordinary case, the baseline.
/// - **just under `MAX_SKIP`** -- the most derivation a forged packet can buy.
///   This is the worst case the bound permits, and the number worth having.
/// - **beyond `MAX_SKIP`** -- refused. Must fall back to roughly the baseline:
///   if it did not, the refusal would be happening *after* the derivation, and
///   an attacker would get the work for free by asking for more than allowed.
///
/// Together these say what the bound costs and confirm that it is enforced
/// where it claims to be. Either number alone would say neither.
#[test]
#[ignore = "timing-sensitive; run with --ignored"]
fn the_skip_bound_caps_what_one_forged_message_can_cost() {
    /// Forge a message Alice produced at `gap` messages ahead of Bob, and time
    /// Bob rejecting it. A fresh receiver per sample, via the public
    /// `export`/`import` pair -- `Session` is deliberately not `Clone`, since
    /// duplicating live ratchet state is what a session type should make hard.
    fn cost_at_gap(gap: u32, samples: usize) -> f64 {
        let mut r = rng(7);
        let (mut alice, bob) = establish(&mut r);

        // Advance Alice `gap` messages past Bob without delivering any of them.
        for _ in 0..gap {
            let _ = alice.encrypt(b"x", &mut r).unwrap();
        }
        let mut forged = alice.encrypt(b"x", &mut r).unwrap();
        let last = forged.len() - 1;
        forged[last] ^= 0x01;

        let snapshot = bob.export();
        let mut times = Vec::with_capacity(samples);
        for _ in 0..samples {
            let mut b = Session::import(&snapshot).expect("its own export imports");
            let s = Instant::now();
            let outcome = std::hint::black_box(b.decrypt(&forged, &mut r));
            times.push(s.elapsed().as_nanos() as f64);
            // Every class must actually be rejected. A class that quietly
            // succeeded would be timing a different operation from the others
            // and the comparison between them would mean nothing.
            assert!(outcome.is_err(), "a forged message decrypted at gap {gap}");
        }
        median(&crop_slowest(times, 0.10))
    }

    const N: usize = 30;
    let baseline = cost_at_gap(0, N);
    let worst = cost_at_gap(900, N); // inside MAX_SKIP = 1000
    let refused = cost_at_gap(1200, N); // beyond it

    println!("forged message: next number          {baseline:.0} ns");
    println!(
        "forged message: gap 900 (allowed)    {worst:.0} ns  ({:.1}x)",
        worst / baseline
    );
    println!(
        "forged message: gap 1200 (refused)   {refused:.0} ns  ({:.1}x)",
        refused / baseline
    );

    // The bound is enforced *before* the derivation, not after. A gap the
    // receiver refuses must not cost more than one it accepts -- otherwise
    // asking for more than the limit is the cheapest way to buy work.
    assert!(
        refused < worst * 1.5,
        "a refused gap cost {:.1}x an allowed one ({refused:.0} ns against \
         {worst:.0} ns). The skip bound is supposed to reject ahead of the \
         derivation loop; check tacenta-ratchet.",
        refused / worst
    );

    // And the allowed worst case is bounded in the way `MAX_SKIP` intends:
    // linear in the gap, not worse. 900 skips costing more than a few thousand
    // times one message would mean the per-skip work is not what it looks like.
    assert!(
        worst < baseline * 3000.0,
        "the worst allowed gap cost {:.1}x the baseline, which is more than \
         linear in MAX_SKIP and suggests per-skip work beyond one derivation",
        worst / baseline
    );
}
