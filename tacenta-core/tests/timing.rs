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
//! workflow runs them in release mode on a dedicated machine -- an isolated,
//! fixed-clock linux x64 core. That workflow lives in
//! `tacenta-core-private-backup`, this repository's private predecessor: not
//! here, and not in the deployment repository either.
//!
//! **And it checks out its own tree, not this one.** Its `actions/checkout`
//! names no `repository:`, so what it runs is that repository's copy of this
//! file, which is not this copy. Until a change here is mirrored there, no
//! scheduled job anywhere runs it -- these controls included. That is a gap in
//! the arrangement rather than a detail of it, and `LIMITATIONS.md` says so.
//!
//! **The harness proves it can still see.** Every assertion above is a negative
//! result -- "these two are indistinguishable" -- and a negative result is
//! evidence only from an instrument that would have reported the positive.
//! Three calibration controls at the foot of this file run the same measurement, the
//! same floors and the same statistics over deliberately leaky stand-ins, and
//! fail if the leak is *not* detected. They are not optional colour: the first
//! of them found that this harness could not resolve a byte-at-a-time
//! short-circuit at all on a host whose timer quantum is 41.67 ns, which is why
//! `Floor::batch` now measures the quantum instead of assuming it.
//!
//! So the `#[ignore]` keeps them out of the per-push job, where they would be
//! flaky, without keeping them out of CI. Un-ignoring them would produce the
//! gate everyone learns to re-run until it passes.
//!
//! **The gate decides on the effect size, not a t-statistic.** A plain
//! wall-clock t-test reads contention as a leak: it can fail with the two
//! classes' medians equal to the nanosecond, the signature of a busy machine
//! rather than of a short-circuit. At a few hundred nanoseconds per operation
//! the t-statistic reports a huge |t| for the timer's own quantization -- which
//! is a property of the host, 41.67 ns here and a nanosecond or less on the
//! nightly's linux core -- as readily as for a
//! real leak, so `run_leak_test` gates
//! on the class **median rejection-time gap in nanoseconds** (`EFFECT_FLOOR_NS`):
//! a constant-time compare differs by <= 2 ns, a real byte-at-a-time short-circuit
//! by ~10 ns -- both figures now measured rather than estimated, by the
//! calibration controls, and both resolvable only once `Floor::batch` has taken
//! the host's timer quantum into account. The t-statistics and a same-input negative control are still
//! computed and printed, but as diagnostics. The measurement runs pinned to an
//! isolated, fixed-clock core, so contention does not perturb it.
//! `EFFECT_FLOOR_NS` and `LeakMeasurement` carry the full derivation;
//! `LIMITATIONS.md` has
//! the narrative.

use rand::SeedableRng;
use std::cell::RefCell;
use std::time::Instant;
use tacenta_braid::Braid;
use tacenta_core::primitives::aead;
use tacenta_core::sessions::{self, Session, establish_initiator, establish_responder};

// ------------------------------------------------------------------ the stamp

/// Rounds per leak test, and **rejections** per class per round.
///
/// Not samples: `Floor::batch` may group several rejections into one timed
/// sample on a coarse-timer host, in which case the sample count falls by the
/// same factor and this total stays put.
///
/// Module-level rather than local to `run_leak_test` so the stamp can report
/// the plan the numbers came from.
const LEAK_ROUNDS: usize = 11;
const LEAK_SAMPLES: usize = 4000;

/// Print where a run came from, so its numbers can be pasted into
/// `LIMITATIONS.md` with their provenance: the commit, the date, the `rustc`
/// version, the command line, and the sample plan. Every field degrades to
/// `unknown` rather than failing, since a stamp is not a gate. The fields the
/// nightly job adds (CPU model and fixed frequency, the isolated core, a run
/// id) are the machine's to know, not the test's.
fn print_stamp(plan: &str) {
    fn run(cmd: &str, args: &[&str]) -> String {
        std::process::Command::new(cmd)
            .args(args)
            .output()
            .ok()
            .filter(|o| o.status.success())
            .and_then(|o| String::from_utf8(o.stdout).ok())
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| "unknown".to_string())
    }
    let commit = run("git", &["rev-parse", "HEAD"]);
    let date = match run("date", &["-u", "+%Y-%m-%dT%H:%M:%SZ"]).as_str() {
        "unknown" => std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|t| format!("unix:{}", t.as_secs()))
            .unwrap_or_else(|_| "unknown".to_string()),
        d => d.to_string(),
    };
    let rustc = run("rustc", &["-V"]);
    let command = std::env::args().collect::<Vec<_>>().join(" ");
    println!("stamp: commit   {commit}");
    println!("stamp: date     {date}");
    println!("stamp: rustc    {rustc}");
    println!("stamp: command  {command}");
    println!("stamp: plan     {plan}");
}

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
/// ones (see `keep_fastest`). 0.30 leaves the fastest three in ten of whatever
/// the round drew -- which is `LEAK_SAMPLES` unbatched and fewer when batched:
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

/// The floor for the microsecond-scale paths -- the Braid's header MAC and the
/// full session rejection -- as a fraction of the faster class's median, and
/// a second, separately documented floor rather than a loosening of the first.
///
/// `EFFECT_FLOOR_NS` was derived for a ~200 ns operation whose two classes
/// differ by the timer's quantization and nothing else. A 3 µs path is not
/// that: it allocates (the candidate state, the reassembled header), walks
/// kilobytes of state, and runs an HMAC, and the fast head of such a path
/// drifts between two interleaved classes by tens of nanoseconds from
/// allocator and cache state alone. On Apple Silicon the timer's own quantum
/// is 41.67 ns (a 24 MHz timebase), so two medians of an identical operation
/// can sit one quantum apart. A 5 ns gate on such a path fails on a quiet
/// machine for reasons that are not leaks, which is the gate everyone learns
/// to re-run.
///
/// So these paths are gated at 2 % of their own cost, or `EFFECT_FLOOR_NS`
/// if that is larger: 60 ns on the ~3 µs Braid header path, and about 2.5 µs
/// on the ~127 µs session path (measured on an M5 Pro: 3000 vs 3000 ns, both
/// medians on the same quantum, and 127,250 vs 127,292 ns, one quantum
/// apart). The honest statement of what each floor resolves is this, and
/// the two are not the same. The Braid floor, ~60 ns, resolves a rejection
/// path that does *different work* by class at the scale of one primitive:
/// an HMAC-SHA256 skipped on one side (hundreds of nanoseconds), an early
/// return before the comparison, the reassembled header not built. The
/// session floor, ~2.5 µs, does not: an HMAC or an HKDF derivation skipped
/// inside `Session::decrypt` is a sub-microsecond change on a ~127 µs path
/// (the whole AEAD rejection it contains is about a microsecond) and sits
/// under the floor. What that floor resolves is an omitted *agreement-scale*
/// step -- a Diffie-Hellman, a KEM operation, a clone of the session state
/// -- each tens of microseconds, and nothing finer. Neither floor resolves a
/// ~10 ns byte-at-a-time short-circuit inside the comparison itself, which
/// is below what a wall-clock median can see at either scale. The
/// short-circuit question is answered where it can be: the ~200 ns tag test
/// above for the AEAD, and `tooling/check-constant-time-asm.sh` for
/// `mac_eq`, which reads the compiled comparison and fails on a conditional
/// branch. The measured gap is printed either way, so a sub-floor
/// difference stays visible to a human.
const EFFECT_FLOOR_FRACTION: f64 = 0.02;

/// Which floor a measurement is gated on. See the two constants.
#[derive(Clone, Copy)]
enum Floor {
    /// `EFFECT_FLOOR_NS`: for operations of a few hundred nanoseconds.
    Absolute,
    /// The larger of `EFFECT_FLOOR_NS` and `EFFECT_FLOOR_FRACTION` of the
    /// faster class's median: for microsecond-scale paths.
    Relative,
}

/// The smallest non-zero interval this machine's `Instant` can report, in
/// nanoseconds.
///
/// Measured rather than assumed, because it is the property that decides
/// whether a floor is real: see [`Floor::batch`]. Sampled from back-to-back
/// `Instant::now()` calls, whose true separation is far below any timer's
/// resolution, so every non-zero delta observed is one quantum or a multiple of
/// one. The smallest is the quantum.
fn measured_timer_quantum() -> f64 {
    let mut smallest = f64::INFINITY;
    let mut last = Instant::now();
    for _ in 0..200_000 {
        let now = Instant::now();
        let d = now.duration_since(last).as_nanos() as f64;
        if d > 0.0 && d < smallest {
            smallest = d;
        }
        last = now;
    }
    // A timer that reported nothing but zeros would leave this infinite; treat
    // that as "finer than we can measure", which needs no batching.
    if smallest.is_finite() { smallest } else { 1.0 }
}

impl Floor {
    fn nanoseconds(self, med_a: f64, med_b: f64) -> f64 {
        match self {
            Floor::Absolute => EFFECT_FLOOR_NS,
            Floor::Relative => EFFECT_FLOOR_NS.max(EFFECT_FLOOR_FRACTION * med_a.min(med_b)),
        }
    }

    /// How many rejections one timed sample covers, on this machine.
    ///
    /// **A floor below the timer's own quantum is not a floor.** `Instant`'s
    /// resolution is a property of the host, and on Apple Silicon it is 41.67 ns
    /// (a 24 MHz timebase). A median gap measured one rejection at a time can
    /// then only ever read 0 or >= 41.67 ns -- so `EFFECT_FLOOR_NS`, at 5 ns,
    /// was not a 5 ns floor there. It was a 41.67 ns floor wearing a 5 ns label,
    /// and the ~10 ns byte-at-a-time short-circuit this file exists to catch fell
    /// underneath it and read as exactly 0.00 ns.
    ///
    /// **The calibration control at the foot of this file is what found that**,
    /// which is the argument for having it. The nightly job runs on an isolated
    /// linux x64 core where the quantum is far finer, so the gate was sound
    /// where it gates; what was unsound was every run anywhere else, including
    /// a reviewer's, silently reporting a green it could not have distinguished
    /// from a leak.
    ///
    /// So the batch is **measured, not assumed**: enough rejections per sample
    /// that `quantum / batch` sits at half the floor or better. On a host whose
    /// timer already resolves a nanosecond this is 1 and nothing changes; on
    /// Apple Silicon it is 17. [`measure_leak`] divides the sample count by the
    /// same factor, so the total number of rejections is the same to within one
    /// batch and only their grouping differs.
    ///
    /// **The microsecond paths take 1 for cost, not because their floors are
    /// safe.** Batching a microsecond path seventeen times over eleven rounds
    /// costs minutes. The Braid header floor is only a small multiple of the
    /// quantum on a coarse-timer host -- close enough that the gate resolves
    /// differences in whole ticks rather than in nanoseconds, and a difference
    /// of one tick passes it. The session floor, being a fraction of a far
    /// longer path, is comfortably above the quantum. No figures are quoted for
    /// either: they move with the host and with the machine's load, and every
    /// number this file has quoted for them has since failed to reproduce. Run
    /// the suite with `--nocapture` and read the floor it prints.
    ///
    /// **What batching changes about the question.** A batched sample measures
    /// steady-state repeated rejection, with caches and predictors warm, rather
    /// than one rejection arriving cold. Both classes are batched identically,
    /// so the comparison stays fair, but the absolute numbers are steady-state
    /// numbers and should be read as such.
    fn batch(self) -> usize {
        match self {
            Floor::Absolute => {
                let quantum = measured_timer_quantum();
                ((quantum / (EFFECT_FLOOR_NS / 2.0)).ceil() as usize).clamp(1, 64)
            }
            Floor::Relative => 1,
        }
    }
}

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
fn signal_and_null(
    a: &[u8],
    b: &[u8],
    n: usize,
    batch: usize,
    reject: &impl Fn(&[u8]),
) -> (f64, f64, f64, f64) {
    let mut ta = Vec::with_capacity(n);
    let mut ta2 = Vec::with_capacity(n);
    let mut tb = Vec::with_capacity(n);
    // One sample covers `batch` rejections, so the quantized clock reading is
    // divided across them: see `Floor::batch` for why a floor below the timer's
    // quantum is not a floor at all.
    let time_one = |bytes: &[u8]| -> f64 {
        let s = Instant::now();
        for _ in 0..batch {
            reject(bytes);
        }
        s.elapsed().as_nanos() as f64 / batch as f64
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
/// dedicated machine and the wrong one here. At a few hundred nanoseconds per
/// operation, sampled
/// thousands of times, the t-statistic reports a large |t| for the
/// timer's own quantization -- a property of the host, not a nanosecond
/// everywhere -- as readily as for a real
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
/// One measurement: the class median gap, the floor it is judged against, and
/// the signal t-statistic.
///
/// Split out from [`run_leak_test`] so that the calibration controls at the
/// foot of this file run **the same measurement code** the real leak tests run.
/// A control that measured a leak its own way would certify only itself; the
/// whole point of it is to exercise this function and this floor.
struct LeakMeasurement {
    effect: f64,
    floor_ns: f64,
    signal_t: f64,
}

fn measure_leak(
    label: &str,
    a: &[u8],
    b: &[u8],
    reject: &impl Fn(&[u8]),
    floor: Floor,
    batch: usize,
) -> LeakMeasurement {
    // Make the CPU itself data-independent where it is not by default (Apple
    // Silicon), so the experiment measures the software and not the core.
    request_data_independent_timing();

    // Warm caches and branch predictors so the first measured round is not an
    // outlier standing in for the rest.
    for _ in 0..64 {
        reject(a);
        reject(b);
    }

    // The batch is the caller's, because a path has to be measured at more
    // than one: see `run_leak_test`. Rejections per round are held constant to
    // within one batch -- integer division, so `LEAK_SAMPLES / batch * batch`
    // falls short of `LEAK_SAMPLES` by up to `batch - 1`, and the run prints
    // both numbers. An earlier `.max(250)` floor made it wrong in the other
    // direction and by more, and made `LEAK_SAMPLES` inert below `250 * batch`,
    // which the control's own failure message told a reader to check first.
    let samples = (LEAK_SAMPLES / batch).max(1);

    let mut signal = Vec::with_capacity(LEAK_ROUNDS);
    let mut noise = Vec::with_capacity(LEAK_ROUNDS);
    let mut meds_a = Vec::with_capacity(LEAK_ROUNDS);
    let mut meds_b = Vec::with_capacity(LEAK_ROUNDS);
    for _ in 0..LEAK_ROUNDS {
        // Both come from the same interleaved window, so contention inflates the
        // null alongside the signal instead of the signal alone.
        let (s, n, ma, mb) = signal_and_null(a, b, samples, batch, reject);
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
    let floor_ns = floor.nanoseconds(med_a, med_b);

    // The t-statistics are diagnostics, printed but not gated on: at this
    // operation size they report a huge |t| for a 1 ns quantization gap, and the
    // same-input null bounces with stray ticks even on an isolated core. The gate
    // decides on the effect size (see EFFECT_FLOOR_NS and EFFECT_FLOOR_FRACTION).
    println!(
        "{label}: |t| signal = {signal_t:.2}, same-input null = {noise_t:.2}  (diagnostic only)"
    );
    println!(
        "{label}: class medians = {med_a:.1} ns vs {med_b:.1} ns  =>  effect size = {effect:.2} ns  (leak floor {floor_ns:.1} ns)"
    );
    println!("{label}: {samples} samples per class per round × {batch} rejections per sample");

    LeakMeasurement {
        effect,
        floor_ns,
        signal_t,
    }
}

/// The verdict the ordinary direction reaches: `Err` naming the factor at which
/// the two classes were distinguishable, `Ok` if they were indistinguishable at
/// every factor measured.
///
/// Split out from [`run_leak_test`] so a control can assert the *other* answer
/// over a stand-in that really leaks. Without that, the loop below -- the thing
/// that keeps this harness from being blind to cold leaks -- is pinned by
/// nothing, and removing it passes every test.
fn leak_verdict(
    label: &str,
    a: &[u8],
    b: &[u8],
    reject: &impl Fn(&[u8]),
    floor: Floor,
) -> Result<(), String> {
    // **Measured at both batch factors, and both must pass.** Batching buys
    // resolution on a coarse-timer host and pays for it by averaging: a leak
    // that appears only on the first rejection after the class changes -- a
    // cold cache, a cold predictor -- is attenuated, and one this harness
    // caught at 42 ns unbatched read 7.3 ns at seventeen per sample, close
    // enough to the floor that a smaller one would vanish. Choosing a single
    // factor chooses which class of leak to be blind to. Measuring at both
    // costs one more pass and chooses neither.
    let batched = floor.batch();
    for batch in if batched == 1 {
        vec![1]
    } else {
        vec![1, batched]
    } {
        let LeakMeasurement {
            effect,
            floor_ns,
            signal_t,
        } = measure_leak(label, a, b, reject, floor, batch);
        if effect >= floor_ns {
            return Err(format!(
                "{label}: distinguishable by timing. The two classes' median rejection times \
                 differ by {effect:.2} ns, at or above the {floor_ns:.1} ns leak floor \
                 (|t| = {signal_t:.2}), measured at {batch} rejections per sample. A \
                 constant-time path differs by less than that here, so a systematic gap this \
                 size is a real, usable leak, not the timer's quantization. A path must be \
                 indistinguishable at every factor it is measured at."
            ));
        }
    }
    Ok(())
}

/// Assert that two classes are **indistinguishable**: the ordinary direction.
fn run_leak_test(
    label: &str,
    a: &[u8],
    b: &[u8],
    reject: &impl Fn(&[u8]),
    leak_hint: &str,
    floor: Floor,
) {
    if let Err(why) = leak_verdict(label, a, b, reject, floor) {
        panic!("{why} {leak_hint}");
    }
}

/// Assert that `leak_verdict` reports a stand-in as distinguishable, **at the
/// batch factor named**.
///
/// Used only by the controls, over stand-ins written to leak. Naming the factor
/// is what makes each control pin its own leg of the loop: a steady-state leak
/// is resolvable only batched, a cold one only unbatched, so a control that
/// merely asserted "some factor caught it" would leave the other leg free. That
/// is not hypothetical -- with a plain `is_err()` assertion, deleting the
/// batched leg went undetected in ten runs out of ten.
///
/// A failure here does not mean `tacenta-core` leaks. The stand-in is not
/// `tacenta-core`; it is written to leak. It means **this harness can no longer
/// see a leak it is supposed to see**, and therefore that the four tests above
/// have stopped being evidence. That is the more dangerous failure of the two,
/// because a blind harness reports green.
fn expect_verdict_at(
    label: &str,
    a: &[u8],
    b: &[u8],
    reject: &impl Fn(&[u8]),
    what: &str,
    floor: Floor,
    batch: usize,
) {
    println!("{label}: CONTROL -- expected to be caught at {batch} per sample.");
    match leak_verdict(label, a, b, reject, floor) {
        Ok(()) => panic!(
            "{label}: THE HARNESS HAS GONE BLIND. {what} was not reported as distinguishable \
             at any factor measured. Likely causes, in order: a floor raised past the effect it \
             is meant to catch; a batch factor that no longer resolves this scale; a compiler or \
             hardware change that altered the cost of the stand-in; or a measurement taken on a \
             contended or frequency-scaling core rather than an isolated fixed-clock one. The \
             sampling plan is a weaker suspect than it looks: no control pins it, and thinning \
             it shows up first as a false red on honest code, not as a miss here."
        ),
        Err(why) => assert!(
            why.contains(&format!("at {batch} rejections per sample")),
            "{label}: caught, but not at the factor this control exists to pin. Expected the \
             verdict to name {batch} rejections per sample; it said: {why}"
        ),
    }
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
    print_stamp(&format!(
        "{LEAK_ROUNDS} rounds × {LEAK_SAMPLES} rejections per class per round"
    ));
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
        Floor::Absolute,
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
    print_stamp(&format!(
        "{LEAK_ROUNDS} rounds × {LEAK_SAMPLES} rejections per class per round"
    ));
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
        Floor::Absolute,
    );
}

/// The Braid's header MAC comparison does not depend on how many leading
/// bytes were correct.
///
/// `mac_eq` in `tacenta-braid` is a hand-written loop rather than a library
/// call, because every dependency that crate has is a translation boundary
/// (`LIMITATIONS.md`, "The Braid's MAC comparison is a hand-written loop").
/// This is the measurement that goes with the inspection: a responder that
/// has received two of the three chunks of the header (`HEADER_LEN + MAC_LEN`
/// is 96 bytes, three systematic chunks of 32; the third chunk is the MAC
/// itself) is timed receiving the third with the MAC wrong at byte 0 against
/// wrong at byte 31. Both reassemble the header, both recompute the MAC, both
/// fail; if the two are distinguishable the comparison stopped early.
///
/// `Braid::receive` is pure -- it hands back a candidate state and leaves the
/// receiver untouched -- so one responder serves every sample. The path is
/// about 3 µs (a state clone, the erasure decoder's reassembly, an HMAC),
/// which is why it is gated on the relative floor; what that resolves and
/// does not is stated at `EFFECT_FLOOR_FRACTION`.
#[test]
#[ignore = "timing-sensitive; run with --ignored"]
fn the_braid_header_mac_does_not_leak_how_much_of_the_mac_was_right() {
    print_stamp(&format!(
        "{LEAK_ROUNDS} rounds × {LEAK_SAMPLES} rejections per class per round"
    ));
    let mut r = rng(11);
    let secret = [0x77u8; 32];
    let initiator = Braid::initiator(&secret);
    let responder = Braid::responder(&secret);

    // The initiator streams its header as three systematic chunks; the
    // responder takes the first two, and the third is what gets timed.
    let (chunk0, _, _, initiator) = initiator.send(&mut r);
    let (chunk1, _, _, initiator) = initiator.send(&mut r);
    let (chunk2, _, _, _) = initiator.send(&mut r);
    let (_, _, responder) = responder.receive(&chunk0);
    let (_, _, responder) = responder.receive(&chunk1);
    let mac_chunk = chunk2.data.expect("the third header chunk carries data");
    assert_eq!(
        mac_chunk.index, 2,
        "the third chunk is systematic chunk 2, the MAC"
    );

    // Sanity: the untouched chunk completes the header (the responder moves
    // on), and each forgery fails it (the responder is Failed).
    let deliver = |bytes: &[u8]| {
        let mut msg = chunk2;
        msg.data.as_mut().expect("data").data.copy_from_slice(bytes);
        responder.receive(&msg).2
    };
    assert_ne!(
        deliver(&mac_chunk.data).state_tag(),
        responder.state_tag(),
        "the genuine third chunk must complete the header"
    );
    let mut early = mac_chunk.data;
    early[0] ^= 0xff;
    let mut late = mac_chunk.data;
    late[31] ^= 0xff;
    assert!(
        deliver(&early).failed(),
        "a MAC wrong at byte 0 must fail the header"
    );
    assert!(
        deliver(&late).failed(),
        "a MAC wrong at byte 31 must fail the header"
    );

    let reject = |bytes: &[u8]| {
        let _ = std::hint::black_box(deliver(bytes));
    };
    run_leak_test(
        "braid header mac",
        &early,
        &late,
        &reject,
        "The header MAC's rejection time depends on where the MAC stops matching. \
         `mac_eq` in braid/src/lib.rs must accumulate every byte; check that it still \
         does, and that nothing on the header path returns before it runs.",
        Floor::Relative,
    );
}

/// The full session rejection path does not depend on how many leading bytes
/// of the tag were correct.
///
/// The AEAD tag test above measures `aead::decrypt` alone. This is the same
/// question asked of everything a peer can actually time: `Session::decrypt`
/// on a ratchet message, through header decoding, the agreement's receive,
/// the ratchet step on a copy of the state, the message-key derivation and the
/// tag check, with the tag wrong at byte 0 against wrong at byte 31. A failed
/// decrypt discards every provisional change (`decrypt_ratchet`'s comment on
/// candidate state), so one receiver serves every sample and each sample sees
/// the same state.
///
/// Several microseconds of work, gated on the relative floor: what that
/// resolves is a path that does different work by class, which is the
/// composition claim `LIMITATIONS.md` makes ("branches on and compares only
/// public data"); the comparison itself is the AEAD test's question.
#[test]
#[ignore = "timing-sensitive; run with --ignored"]
fn the_session_rejection_path_does_not_leak_how_much_of_the_tag_was_right() {
    print_stamp(&format!(
        "{LEAK_ROUNDS} rounds × {LEAK_SAMPLES} rejections per class per round"
    ));
    let mut r = rng(13);
    let (mut alice, bob) = establish(&mut r);
    let genuine = alice
        .encrypt(b"a message whose tag is about to be wrong", &mut r)
        .expect("encrypt");
    let tag_at = genuine.len() - 32;

    let mut early = genuine.clone();
    early[tag_at] ^= 0xff;
    let mut late = genuine.clone();
    late[tag_at + 31] ^= 0xff;

    let bob = RefCell::new(bob);
    let r = RefCell::new(r);
    let reject = |bytes: &[u8]| {
        let outcome = bob.borrow_mut().decrypt(bytes, &mut *r.borrow_mut());
        let _ = std::hint::black_box(outcome);
    };

    // Sanity: both forgeries are refused, and refused without moving the
    // receiver -- the genuine message still decrypts afterwards, so every
    // timed sample ran against the same state.
    assert!(
        bob.borrow_mut()
            .decrypt(&early, &mut *r.borrow_mut())
            .is_err()
    );
    assert!(
        bob.borrow_mut()
            .decrypt(&late, &mut *r.borrow_mut())
            .is_err()
    );

    run_leak_test(
        "session rejection",
        &early,
        &late,
        &reject,
        "Rejection time depends on where the tag stops matching, somewhere on the \
         path from Session::decrypt to aead::decrypt; check what runs after the \
         tag check fails, and that the AEAD still compares with Mac::verify_slice.",
        Floor::Relative,
    );

    assert!(
        bob.borrow_mut()
            .decrypt(&genuine, &mut *r.borrow_mut())
            .is_ok(),
        "the genuine message must still decrypt after every forgery was refused"
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
    print_stamp(&format!("{N} samples per gap, three gaps"));
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

// ------------------------------------------- calibration: can this harness see?

// The four tests above assert that a path does not leak. Each one is evidence
// only while the harness that runs it can still detect a leak that is there --
// and nothing above establishes that. A harness whose sampling plan stopped
// resolving its scale, or whose floor drifted above the effect it exists to
// catch, reports exactly the same green as a codebase with no leak in it.
//
// So these three run the same measurement, the same floors and the same
// statistics over **deliberately leaky stand-ins**, and fail if the leak is
// not detected. They are the positive controls for the negative results above.
//
// **What these stand-ins are not.** Neither is `tacenta-core` code, and a
// failure in one is not a finding about the library. They are written to leak.
// Their only job is to make the harness demonstrate, on the machine and
// toolchain of the day, that it can still tell a leak from a non-leak.
//
// **What they do not establish.** Four things, named because a list of controls
// reads as coverage.
//
// *The sampling plan is pinned by nothing.* `LEAK_ROUNDS` and `LEAK_SAMPLES`
// can be cut a hundredfold with every test here still green: on a quiet host
// these effects resolve with far fewer samples than the plan draws. The plan is
// sized for a contended one, and no control demonstrates that -- so the failure
// message below lists the plan first among likely causes on reasoning, not on
// evidence.
//
// *An unbatched reading is bimodal, and a non-zero one is not an effect size.*
// Where the quantum is 41.67 ns a 12 ns difference reads as either 0 or one
// whole tick, so the same quantization that erases an effect can also overstate
// it three-and-a-half times. Read a single unbatched number as "same tick" or
// "different tick", not as nanoseconds.
//
// *That the harness resolves every weakening at every scale.*
// `EFFECT_FLOOR_FRACTION`'s derivation above is explicit that the session floor
// does not resolve a skipped HMAC or HKDF, and no control here claims
// otherwise. The three calibrate the two floors and the cost of batching: a
// byte-at-a-time comparison against `Floor::Absolute`, a few per cent of a
// microsecond path against `Floor::Relative`, and a leak confined to the first
// rejection after the class changes against the batching itself.
//
// *That any of this runs anywhere but by hand.* See the module header: the
// nightly job runs another repository's copy of this file.
//
// The gap between what a floor resolves and what an attacker could use is
// stated with the floors, not closed by these.

/// The harness detects a byte-at-a-time tag comparison.
///
/// The stand-in does exactly the work `aead::decrypt` does -- it calls it, so
/// the HMAC and the constant-time verify both happen -- and then performs the
/// short-circuiting comparison a careless implementer writes instead of
/// `Mac::verify_slice`. The two classes differ only in where that comparison
/// stops: byte 0 against byte 31.
///
/// `black_box` on each byte read is deliberate and is the honest choice to
/// document: without it the optimiser is free to turn the loop into a vector
/// compare, which would erase the very effect the control exists to produce and
/// leave the control passing for the wrong reason. A real short-circuiting
/// comparison in shipped code could of course be vectorised the same way -- that
/// is a reason the *absolute* floor is not the whole constant-time story, and it
/// is why the assembly gate exists alongside this file.
#[test]
#[ignore = "timing-sensitive; run with --ignored"]
fn control_the_harness_detects_a_short_circuiting_tag_comparison() {
    print_stamp(&format!(
        "CONTROL {LEAK_ROUNDS} rounds × {LEAK_SAMPLES} rejections per class per round"
    ));
    let enc_key = [0x11u8; 32];
    let mac_key = [0x22u8; 32];
    let iv = [0x33u8; 16];
    let ad = b"associated data";

    let sealed = aead::encrypt(&enc_key, &mac_key, &iv, b"a plaintext of some length", ad);
    let split = sealed.len() - 32;
    let real_tag: [u8; 32] = sealed[split..].try_into().expect("the tag is 32 bytes");

    let mut early = sealed.clone();
    early[split] ^= 0xff;
    let mut late = sealed.clone();
    let last = late.len() - 1;
    late[last] ^= 0xff;

    // Both are still rejected by the real path, so the stand-in is a leak added
    // to a genuine rejection rather than a rejection replaced by something else.
    assert!(aead::decrypt(&enc_key, &mac_key, &iv, &early, ad).is_err());
    assert!(aead::decrypt(&enc_key, &mac_key, &iv, &late, ad).is_err());

    let leaky_reject = |bytes: &[u8]| {
        let _ = std::hint::black_box(aead::decrypt(&enc_key, &mac_key, &iv, bytes, ad));
        // The deliberate defect: stop at the first wrong byte.
        let tag = &bytes[bytes.len() - 32..];
        let mut equal = true;
        for i in 0..32 {
            if std::hint::black_box(tag[i]) != std::hint::black_box(real_tag[i]) {
                equal = false;
                break;
            }
        }
        let _ = std::hint::black_box(equal);
    };
    // Pinned to the batched factor: a ~12 ns steady-state difference is below
    // one timer quantum on a coarse-timer host, so only the batched leg
    // resolves it, which is what makes this control that leg's pin.
    expect_verdict_at(
        "control: short-circuiting tag comparison",
        &early,
        &late,
        &leaky_reject,
        "A tag comparison that stops at the first wrong byte",
        Floor::Absolute,
        Floor::Absolute.batch(),
    );
}

/// The harness still sees a leak confined to the first rejection after the
/// class changes.
///
/// **This is the control for the cost of batching**, and it is why
/// `run_leak_test` measures at more than one factor. A batched sample averages
/// `batch` rejections, so a leak present only in the first of them is
/// attenuated by exactly that factor: this stand-in is caught at one rejection
/// per sample and attenuated to near the floor at seventeen -- close enough
/// that a smaller one would vanish. A harness that chose
/// the batched factor alone would be blind to every cold-cache leak below
/// `floor * batch`, and would say nothing about it.
///
/// Pinned to one rejection per sample deliberately. The tag-comparison control
/// is pinned to the batched factor, because a difference that small is below a
/// coarse timer's quantum and only batching resolves it; between the two, both
/// legs of `leak_verdict`'s loop are held, and deleting either is caught. The
/// third control runs on a microsecond path, where `Floor::Relative` takes no
/// batching at all.
#[test]
#[ignore = "timing-sensitive; run with --ignored"]
fn control_the_harness_detects_a_leak_only_on_the_first_rejection() {
    print_stamp(&format!(
        "CONTROL {LEAK_ROUNDS} rounds × {LEAK_SAMPLES} rejections per class per round"
    ));
    let enc_key = [0x77u8; 32];
    let mac_key = [0x88u8; 32];
    let iv = [0x99u8; 16];
    let ad = b"associated data";

    let sealed = aead::encrypt(&enc_key, &mac_key, &iv, b"a plaintext of some length", ad);
    let split = sealed.len() - 32;
    let mut early = sealed.clone();
    early[split] ^= 0xff;
    let mut late = sealed.clone();
    let last = late.len() - 1;
    late[last] ^= 0xff;

    // The deliberate defect: one class pays extra, and only on its first
    // rejection after the other class ran. Steady-state repetition hides it,
    // which is the whole point of the control.
    let cold_class = late.clone();
    let previous = RefCell::new(Vec::<u8>::new());
    let leaky_reject = |bytes: &[u8]| {
        let _ = std::hint::black_box(aead::decrypt(&enc_key, &mac_key, &iv, bytes, ad));
        let mut prev = previous.borrow_mut();
        let cold = bytes == cold_class.as_slice() && prev.as_slice() != cold_class.as_slice();
        prev.clear();
        prev.extend_from_slice(bytes);
        drop(prev);
        if cold {
            let mut acc = 0u64;
            for i in 0..COLD_PENALTY {
                acc = acc.wrapping_add(std::hint::black_box(i));
            }
            let _ = std::hint::black_box(acc);
        }
    };
    // Through `leak_verdict`, the same path the four real tests take, so this
    // pins the loop over batch factors and not merely the stand-in: measure at
    // the batched factor alone and this is the test that goes red.
    // Pinned to one rejection per sample: this leak is confined to the first
    // rejection after the class changes, so batching averages it away and only
    // the unbatched leg resolves it, which is what makes this control that
    // leg's pin.
    expect_verdict_at(
        "control: a leak only on the first rejection",
        &early,
        &late,
        &leaky_reject,
        "A rejection path that pays extra only on its first call after the class changed",
        Floor::Absolute,
        1,
    );
}

/// The extra work the relative-floor stand-in pays on one class, sized to a few
/// per cent of the ~1.8 microsecond Braid header path -- just above
/// `EFFECT_FLOOR_FRACTION` of it, so the control is judged by that constant and
/// fails if it is raised.
const RELATIVE_PENALTY: u64 = 520;

/// The work the cold-only stand-in pays, sized to about one DRAM miss -- the
/// scale of a real cold-cache leak, not a large one. Tuned so the effect sits
/// well above one timer quantum at a single rejection per sample.
const COLD_PENALTY: u64 = 120;

/// The harness detects a few per cent of difference on a microsecond path.
///
/// Both classes run the Braid's real header path, and one pays a few per cent
/// more. `Floor::Relative` is a fraction of the *faster* class's own cost, so
/// both classes must do the microsecond work or the floor is not the one being
/// calibrated -- an earlier version returned outright on one class, whose median
/// then measured zero, collapsing the relative floor to the absolute one.
///
/// What this pins is coarse, and the limits are worth stating. The floor can
/// still be loosened by a factor of about two and a half, or inflated at the
/// session scale alone, with this control green: it runs at the Braid scale
/// only, and its own margin is a handful of timer ticks rather than a
/// calibrated effect size.
#[test]
#[ignore = "timing-sensitive; run with --ignored"]
fn control_the_harness_detects_a_few_per_cent_on_a_microsecond_path() {
    print_stamp(&format!(
        "CONTROL {LEAK_ROUNDS} rounds × {LEAK_SAMPLES} rejections per class per round"
    ));
    let mut r = rng(11);
    let secret = [0x77u8; 32];
    let initiator = Braid::initiator(&secret);
    let responder = Braid::responder(&secret);

    let (chunk0, _, _, initiator) = initiator.send(&mut r);
    let (chunk1, _, _, initiator) = initiator.send(&mut r);
    let (chunk2, _, _, _) = initiator.send(&mut r);
    let (_, _, responder) = responder.receive(&chunk0);
    let (_, _, responder) = responder.receive(&chunk1);
    let mac_chunk = chunk2.data.expect("the third header chunk carries data");

    let deliver = |bytes: &[u8]| {
        let mut msg = chunk2;
        msg.data.as_mut().expect("data").data.copy_from_slice(bytes);
        responder.receive(&msg).2
    };
    let mut early = mac_chunk.data;
    early[0] ^= 0xff;
    let mut late = mac_chunk.data;
    late[31] ^= 0xff;
    assert!(deliver(&early).failed(), "the early forgery must fail");
    assert!(deliver(&late).failed(), "the late forgery must fail");

    let genuine = mac_chunk.data;
    let leaky_reject = |bytes: &[u8]| {
        // The deliberate defect: one class pays a little more than the other,
        // both having done the same microsecond-scale work.
        //
        // **Both classes must do that work**, or this control does not
        // calibrate the floor it names. An earlier version returned outright on
        // one class, whose median then measured 0.0 ns; `Floor::Relative` is
        // `EFFECT_FLOOR_FRACTION` of the *faster* class, so a zero median
        // collapses it to `EFFECT_FLOOR_NS` and the control silently exercised
        // the absolute floor instead. `EFFECT_FLOOR_FRACTION` could then be
        // raised to 100.0 -- enough for both microsecond gates to accept a leak
        // a hundred times the whole path cost -- with every test still green.
        let _ = std::hint::black_box(deliver(bytes));
        if std::hint::black_box(bytes[0]) == std::hint::black_box(genuine[0]) {
            let mut acc = 0u64;
            for i in 0..RELATIVE_PENALTY {
                acc = acc.wrapping_add(std::hint::black_box(i));
            }
            let _ = std::hint::black_box(acc);
        }
    };
    expect_verdict_at(
        "control: a few per cent on a microsecond path",
        &early,
        &late,
        &leaky_reject,
        "A rejection path that costs a few per cent more on one class than the other",
        Floor::Relative,
        Floor::Relative.batch(),
    );
}
