//! Malformed stored-state check for the ML-KEM boundary.
//!
//! `EncapsState::from_bytes` and `IncrementalKeyPair::from_bytes` accept any
//! byte string of the right length. The bytes hold raw `i16` ring-element
//! coefficients that libcrux never range-checks on read. This test feeds
//! length-valid states with out-of-range coefficients into `encapsulate2` and
//! `decapsulate` and records whether each call returns a `Result` or panics
//! inside the dependency.
//!
//! The expectation under test is the one the proofs assume (`BraidT1.lean`,
//! `Encapsulate2Total` and the decapsulation clause of `KemAgreesFor`): every
//! call on an accepted state returns. `from_bytes` checks the length alone, as
//! the persistence page says a reader does; `encapsulate2` refuses a state with
//! a coefficient outside the bound libcrux states for its arithmetic
//! (`|c| <= 3328`) instead of handing the library an input its annotations do
//! not cover. The first two tests FAIL when any probe panics, when
//! `encapsulate2` returns a ciphertext from an out-of-bound state, or when it
//! refuses an in-bound one; they print the panic location so a failing case is
//! preserved in the log. The last two tests are informational and never fail.
//!
//! Before the range check in `encapsulate2`, the first test failed on the
//! libcrux portable backend (`LIBCRUX_DISABLE_SIMD128=1` on aarch64, in a fresh
//! `CARGO_TARGET_DIR`; libcrux's build script reads the variable at build time)
//! with `i16` overflow panics inside libcrux for the `error2` patterns of large
//! magnitude and for random bytes, while the `r_as_ntt` patterns and the
//! smaller `error2` values returned a ciphertext; on NEON every pattern
//! returned a ciphertext.
//!
//! Run with `-- --nocapture` to see the table. Compare the dev and release
//! profiles: `tacenta-core/Cargo.toml` turns `overflow-checks` on for release.

use std::panic::{self, AssertUnwindSafe};
use std::sync::Mutex;

use rand::SeedableRng;
use rand::rngs::StdRng;
use tacenta_kem::{
    CT1_LEN, CT2_LEN, EK_VECTOR_LEN, EncapsState, HEADER_LEN, IncrementalKeyPair, KemError,
    SHARED_SECRET_LEN, encapsulate1, encapsulate2, validate_ek,
};

/// libcrux `EncapsState` layout (ind_cca/incremental/types.rs): `r_as_ntt`
/// (K = 4 polynomials of 256 little-endian i16), then `error2` (one
/// polynomial), then 32 bytes of randomness.
const STATE_LEN: usize = 2592;
const R_AS_NTT: std::ops::Range<usize> = 0..2048;
const ERROR2: std::ops::Range<usize> = 2048..2560;
const RANDOMNESS: std::ops::Range<usize> = 2560..2592;
const KEY_PAIR_LEN: usize = 11872;
/// The bound libcrux states for a coefficient it computes with, which
/// `encapsulate2` keeps on the state side.
const COEFFICIENT_BOUND: i16 = 3328;

/// Whether `encapsulate2` must refuse these state bytes: some coefficient in the
/// five polynomials has magnitude above the bound.
fn must_refuse(state: &[u8]) -> bool {
    state[..ERROR2.end]
        .chunks_exact(2)
        .any(|c| i16::from_le_bytes([c[0], c[1]]).unsigned_abs() > COEFFICIENT_BOUND as u16)
}

static PANICS: Mutex<Vec<String>> = Mutex::new(Vec::new());

fn install_hook() {
    panic::set_hook(Box::new(|info| {
        let location = info
            .location()
            .map(|l| format!("{}:{}", l.file(), l.line()))
            .unwrap_or_else(|| "<unknown>".to_string());
        let message = info
            .payload()
            .downcast_ref::<&str>()
            .map(|s| s.to_string())
            .or_else(|| info.payload().downcast_ref::<String>().cloned())
            .unwrap_or_default();
        PANICS
            .lock()
            .unwrap()
            .push(format!("{message} @ {location}"));
    }));
}

#[derive(Debug)]
enum Outcome {
    Returned(String),
    Panicked(String),
}

fn probe<T: std::fmt::Debug>(f: impl FnOnce() -> T) -> Outcome {
    PANICS.lock().unwrap().clear();
    match panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(v) => Outcome::Returned(format!("{v:?}")),
        Err(_) => {
            let recorded = PANICS.lock().unwrap().join(" | ");
            Outcome::Panicked(recorded)
        }
    }
}

fn fill_i16(bytes: &mut [u8], range: std::ops::Range<usize>, value: i16) {
    for chunk in bytes[range].chunks_exact_mut(2) {
        chunk.copy_from_slice(&value.to_le_bytes());
    }
}

fn xorshift_fill(bytes: &mut [u8], mut word: u64) {
    for b in bytes.iter_mut() {
        word ^= word << 13;
        word ^= word >> 7;
        word ^= word << 17;
        *b = (word & 0xff) as u8;
    }
}

struct Fixture {
    key_pair: IncrementalKeyPair,
    ek_vector: Vec<u8>,
    valid_state: Vec<u8>,
    ct1: Vec<u8>,
    ct2: Vec<u8>,
    secret: [u8; SHARED_SECRET_LEN],
}

fn fixture() -> Fixture {
    let mut rng = StdRng::seed_from_u64(0x7ac3_17a5);
    let key_pair = IncrementalKeyPair::generate(&mut rng).unwrap();
    let header = key_pair.header();
    let ek_vector = key_pair.ek_vector();
    assert_eq!(header.len(), HEADER_LEN);
    assert_eq!(ek_vector.len(), EK_VECTOR_LEN);
    assert!(validate_ek(&header, &ek_vector));
    let (state, ct1, secret) = encapsulate1(&header, &mut rng).unwrap();
    let ct2 = encapsulate2(&state, &ek_vector).unwrap();
    assert_eq!(ct1.len(), CT1_LEN);
    assert_eq!(ct2.len(), CT2_LEN);
    assert_eq!(key_pair.decapsulate(&ct1, &ct2), Ok(secret));
    let valid_state = state.to_bytes().to_vec();
    assert_eq!(valid_state.len(), STATE_LEN);
    assert_eq!(key_pair.to_bytes().len(), KEY_PAIR_LEN);
    Fixture {
        key_pair,
        ek_vector,
        valid_state,
        ct1,
        ct2,
        secret,
    }
}

fn state_cases(valid: &[u8]) -> Vec<(&'static str, Vec<u8>)> {
    let mut cases = Vec::new();
    let mut push = |name: &'static str, edit: &dyn Fn(&mut Vec<u8>)| {
        let mut bytes = valid.to_vec();
        edit(&mut bytes);
        assert_eq!(bytes.len(), STATE_LEN);
        cases.push((name, bytes));
    };
    push("valid (baseline)", &|_| {});
    push("randomness all 0xFF (coefficients untouched)", &|b| {
        b[RANDOMNESS].fill(0xff)
    });
    push("error2 = 32767, rest valid", &|b| {
        fill_i16(b, ERROR2, i16::MAX)
    });
    push("error2 = -32768, rest valid", &|b| {
        fill_i16(b, ERROR2, i16::MIN)
    });
    push("error2 = 3329 (q), rest valid", &|b| {
        fill_i16(b, ERROR2, 3329)
    });
    push("error2 = 28297 (one past Barrett bound)", &|b| {
        fill_i16(b, ERROR2, 28297)
    });
    push("error2 = 28296 (at Barrett bound)", &|b| {
        fill_i16(b, ERROR2, 28296)
    });
    push("r_as_ntt = 32767, rest valid", &|b| {
        fill_i16(b, R_AS_NTT, i16::MAX)
    });
    push("r_as_ntt = -32768, rest valid", &|b| {
        fill_i16(b, R_AS_NTT, i16::MIN)
    });
    push("r_as_ntt = 3329 (q), rest valid", &|b| {
        fill_i16(b, R_AS_NTT, 3329)
    });
    push(
        "r_as_ntt = 0, error2 = 32767 (error2 only at i16::MAX)",
        &|b| {
            fill_i16(b, R_AS_NTT, 0);
            fill_i16(b, ERROR2, i16::MAX);
        },
    );
    push("r_as_ntt = 3328 and error2 = 3328 (at the bound)", &|b| {
        fill_i16(b, R_AS_NTT, 3328);
        fill_i16(b, ERROR2, 3328);
    });
    push("r_as_ntt = -3328 and error2 = -3328 (at the bound)", &|b| {
        fill_i16(b, R_AS_NTT, -3328);
        fill_i16(b, ERROR2, -3328);
    });
    push(
        "one r_as_ntt coefficient = 3329 (one past the bound)",
        &|b| b[1000..1002].copy_from_slice(&3329i16.to_le_bytes()),
    );
    push(
        "one error2 coefficient = -3329 (one past the bound)",
        &|b| b[2300..2302].copy_from_slice(&(-3329i16).to_le_bytes()),
    );
    push("all bytes 0xFF (every coefficient -1)", &|b| b.fill(0xff));
    push("all bytes 0x00", &|b| b.fill(0x00));
    push("all coefficients 0x7FFF, randomness 0xFF", &|b| {
        fill_i16(b, R_AS_NTT, i16::MAX);
        fill_i16(b, ERROR2, i16::MAX);
        b[RANDOMNESS].fill(0xff);
    });
    push("xorshift random bytes (seed 1)", &|b| {
        xorshift_fill(b, 0x9e37_79b9_7f4a_7c15)
    });
    push("xorshift random bytes (seed 2)", &|b| {
        xorshift_fill(b, 0x2545_f491_4f6c_dd1d)
    });
    cases
}

fn key_pair_cases(valid: &[u8]) -> Vec<(&'static str, Vec<u8>)> {
    let mut cases = Vec::new();
    let mut push = |name: &'static str, edit: &dyn Fn(&mut Vec<u8>)| {
        let mut bytes = valid.to_vec();
        edit(&mut bytes);
        assert_eq!(bytes.len(), KEY_PAIR_LEN);
        cases.push((name, bytes));
    };
    push("valid (baseline)", &|_| {});
    push("all bytes 0xFF", &|b| b.fill(0xff));
    push("all bytes 0x00", &|b| b.fill(0x00));
    push("all i16 = 32767", &|b| {
        let len = b.len();
        fill_i16(b, 0..len, i16::MAX)
    });
    push("all i16 = -32768", &|b| {
        let len = b.len();
        fill_i16(b, 0..len, i16::MIN)
    });
    push("xorshift random bytes (seed 3)", &|b| {
        xorshift_fill(b, 0xd1b5_4a32_d192_ed03)
    });
    push(
        "secret polynomials i16 = 32767, public halves valid",
        &|b| {
            // libcrux's `KeyPair::to_bytes` writes pk1 (64 bytes), pk2 (1,536),
            // then the four secret polynomials (2,048 bytes at 1600..3648), then
            // the implicit-rejection value and the matrix. Only the secret
            // polynomials are set here; the layout is read from the library and
            // not asserted by this crate.
            fill_i16(b, 1600..3648, i16::MAX)
        },
    );
    cases
}

#[test]
fn accepted_stored_states_return_a_result_instead_of_panicking() {
    install_hook();
    let fx = fixture();
    let mut failures = Vec::new();

    println!();
    println!(
        "backend selectors: LIBCRUX_DISABLE_SIMD128={:?} LIBCRUX_DISABLE_SIMD256={:?}",
        std::env::var("LIBCRUX_DISABLE_SIMD128").ok(),
        std::env::var("LIBCRUX_DISABLE_SIMD256").ok()
    );
    println!(
        "profile: debug_assertions={} overflow_checks={}",
        cfg!(debug_assertions),
        {
            // Detect overflow checks in THIS crate's profile at run time.
            let x: u8 = std::hint::black_box(255);
            panic::catch_unwind(|| x + std::hint::black_box(1)).is_err()
        }
    );
    println!();
    println!("== EncapsState -> encapsulate2(state, valid ek_vector) ==");
    for (name, bytes) in state_cases(&fx.valid_state) {
        let refuse = must_refuse(&bytes);
        let state = match EncapsState::from_bytes(&bytes) {
            Ok(s) => s,
            Err(KemError) => {
                println!("{name:60} from_bytes: REFUSED length-valid bytes");
                failures.push(format!("from_bytes refused / {name}"));
                continue;
            }
        };
        let ek = fx.ek_vector.clone();
        let outcome = probe(move || encapsulate2(&state, &ek).map(|ct2| ct2.len()));
        match (&outcome, refuse) {
            (Outcome::Returned(v), false) if v.starts_with("Ok(") => {
                println!("{name:60} encapsulate2: returned {v}")
            }
            (Outcome::Returned(v), true) if v.starts_with("Err(") => {
                println!(
                    "{name:60} encapsulate2: refused {v} (coefficient above {COEFFICIENT_BOUND})"
                )
            }
            (Outcome::Returned(v), true) => {
                println!("{name:60} encapsulate2: ACCEPTED an out-of-bound state: {v}");
                failures.push(format!("encapsulate2 accepted out-of-bound / {name}"));
            }
            (Outcome::Returned(v), false) => {
                println!("{name:60} encapsulate2: REFUSED an in-bound state: {v}");
                failures.push(format!("encapsulate2 refused in-bound / {name}"));
            }
            (Outcome::Panicked(p), _) => {
                println!("{name:60} encapsulate2: PANIC {p}");
                failures.push(format!("encapsulate2 / {name}: {p}"));
            }
        }
    }

    println!();
    println!(
        "== IncrementalKeyPair -> header / ek_vector / validate_ek / decapsulate(valid ct) =="
    );
    for (name, bytes) in key_pair_cases(&fx.key_pair.to_bytes()) {
        let kp = match IncrementalKeyPair::from_bytes(&bytes) {
            Ok(k) => k,
            Err(KemError) => {
                println!("{name:60} from_bytes: Err(KemError)  [length-valid bytes refused?]");
                continue;
            }
        };
        let k1 = kp.clone();
        let header = probe(move || k1.header().len());
        let k2 = kp.clone();
        let ek = probe(move || k2.ek_vector().len());
        let k3 = kp.clone();
        let valid = probe(move || validate_ek(&k3.header(), &k3.ek_vector()));
        let (ct1, ct2) = (fx.ct1.clone(), fx.ct2.clone());
        let k4 = kp.clone();
        let decaps = probe(move || k4.decapsulate(&ct1, &ct2).map(|s| s == fx.secret));
        for (op, outcome) in [
            ("header", &header),
            ("ek_vector", &ek),
            ("validate_ek", &valid),
            ("decapsulate", &decaps),
        ] {
            match outcome {
                Outcome::Returned(v) => println!("{name:60} {op:12}: returned {v}"),
                Outcome::Panicked(p) => {
                    println!("{name:60} {op:12}: PANIC {p}");
                    failures.push(format!("{op} / {name}: {p}"));
                }
            }
        }
    }

    // Restore the default hook so later failures print normally.
    let _ = panic::take_hook();
    assert!(
        failures.is_empty(),
        "{} accepted stored state(s) panicked inside the KEM boundary:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}

/// Every one of the 1,280 coefficient positions is checked on its own: a value
/// one past the bound at that position alone must be refused, and the bound
/// itself there must be accepted, for both signs. This is what catches a guard
/// that skips the first or the last coefficient or checks every other one.
#[test]
fn every_coefficient_position_is_checked_against_the_bound() {
    install_hook();
    let fx = fixture();
    let mut failures = Vec::new();
    for index in 0..(ERROR2.end / 2) {
        for (value, accept) in [
            (COEFFICIENT_BOUND + 1, false),
            (-(COEFFICIENT_BOUND + 1), false),
            (COEFFICIENT_BOUND, true),
            (-COEFFICIENT_BOUND, true),
        ] {
            let mut bytes = fx.valid_state.clone();
            bytes[2 * index..2 * index + 2].copy_from_slice(&value.to_le_bytes());
            let state = EncapsState::from_bytes(&bytes).expect("length-valid bytes");
            let ek = fx.ek_vector.clone();
            let outcome = probe(move || encapsulate2(&state, &ek).map(|c| c.len()));
            let ok = match &outcome {
                Outcome::Returned(v) => v.starts_with("Ok(") == accept,
                Outcome::Panicked(_) => false,
            };
            if !ok {
                failures.push(format!("coefficient {index} = {value}: {outcome:?}"));
            }
        }
    }
    let _ = panic::take_hook();
    assert!(
        failures.is_empty(),
        "{} position(s) wrong:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}

/// Observed coefficient ranges of genuine states and key pairs, as evidence
/// for what a range validator in `from_bytes` could require. Informational.
#[test]
fn genuine_state_coefficient_ranges() {
    let mut rng = StdRng::seed_from_u64(99);
    let (mut r_min, mut r_max, mut e_min, mut e_max) = (i16::MAX, i16::MIN, i16::MAX, i16::MIN);
    for _ in 0..256 {
        let pair = IncrementalKeyPair::generate(&mut rng).unwrap();
        let (state, _, _) = encapsulate1(&pair.header(), &mut rng).unwrap();
        let bytes = state.to_bytes();
        for c in bytes[R_AS_NTT].chunks_exact(2) {
            let v = i16::from_le_bytes([c[0], c[1]]);
            r_min = r_min.min(v);
            r_max = r_max.max(v);
        }
        for c in bytes[ERROR2].chunks_exact(2) {
            let v = i16::from_le_bytes([c[0], c[1]]);
            e_min = e_min.min(v);
            e_max = e_max.max(v);
        }
    }
    println!();
    println!("genuine states (256): r_as_ntt in [{r_min}, {r_max}], error2 in [{e_min}, {e_max}]");
}

/// Panic rate over uniformly random length-valid states and key pairs on this
/// build. Informational: never fails.
#[test]
fn random_length_valid_inputs_panic_rate() {
    install_hook();
    let mut rng = StdRng::seed_from_u64(5);
    let pair = IncrementalKeyPair::generate(&mut rng).unwrap();
    let vector = pair.ek_vector();
    let (_, ct1, _) = encapsulate1(&pair.header(), &mut rng).unwrap();
    let ct2 = vec![0u8; CT2_LEN];
    let (mut state_panics, mut state_refusals, mut kp_panics) = (0, 0, 0);
    let n = 64;
    for i in 0..n as u64 {
        let mut bytes = vec![0u8; STATE_LEN];
        xorshift_fill(
            &mut bytes,
            0x1234_5678_9abc_def1 ^ (i.wrapping_mul(0x9e37_79b9_7f4a_7c15)),
        );
        let state = EncapsState::from_bytes(&bytes).unwrap();
        let v = vector.clone();
        match probe(move || encapsulate2(&state, &v).map(|c| c.len())) {
            Outcome::Panicked(_) => state_panics += 1,
            Outcome::Returned(r) if r.starts_with("Err(") => state_refusals += 1,
            Outcome::Returned(_) => {}
        }
        let mut kbytes = vec![0u8; KEY_PAIR_LEN];
        xorshift_fill(
            &mut kbytes,
            0x0fed_cba9_8765_4321 ^ (i.wrapping_mul(0x2545_f491_4f6c_dd1d)),
        );
        let kp = IncrementalKeyPair::from_bytes(&kbytes).unwrap();
        let (c1, c2) = (ct1.clone(), ct2.clone());
        if let Outcome::Panicked(_) = probe(move || kp.decapsulate(&c1, &c2).map(|_| ())) {
            kp_panics += 1;
        }
    }
    println!();
    println!(
        "random length-valid inputs: encapsulate2 refused {state_refusals}/{n}, encapsulate2 panicked {state_panics}/{n}, decapsulate panicked {kp_panics}/{n}"
    );
    let _ = panic::take_hook();
}

/// Scan the `error2` coefficient value (all 256 coefficients equal, `r_as_ntt`
/// zero, randomness zero) and report the smallest magnitude that panics on this
/// build. Informational: never fails.
#[test]
fn error2_magnitude_threshold_scan() {
    install_hook();
    let mut rng = StdRng::seed_from_u64(17);
    let pair = IncrementalKeyPair::generate(&mut rng).unwrap();
    let vector = pair.ek_vector();
    let mut first_panic_pos: Option<i16> = None;
    let mut first_panic_neg: Option<i16> = None;
    println!();
    println!("== error2 scan (r_as_ntt = 0, randomness = 0) ==");
    for magnitude in [
        0i16, 1, 2, 3, 1664, 1665, 3328, 3329, 3330, 6658, 10000, 20000, 26000, 27000, 27500,
        27800, 28000, 28296, 28297, 29000, 29961, 29962, 30000, 31000, 31625, 31626, 32000, 32767,
    ] {
        for (sign, slot) in [(1i16, &mut first_panic_pos), (-1i16, &mut first_panic_neg)] {
            let value = magnitude.saturating_mul(sign);
            let mut bytes = vec![0u8; STATE_LEN];
            fill_i16(&mut bytes, ERROR2, value);
            let state = EncapsState::from_bytes(&bytes).unwrap();
            let v = vector.clone();
            let outcome = probe(move || encapsulate2(&state, &v).map(|c| c.len()));
            let label = match &outcome {
                Outcome::Returned(r) if r.starts_with("Err(") => {
                    "refused by encapsulate2".to_string()
                }
                Outcome::Returned(_) => "returned".to_string(),
                Outcome::Panicked(p) => {
                    if slot.is_none() {
                        *slot = Some(value);
                    }
                    format!("PANIC {p}")
                }
            };
            println!("error2 = {value:>7}: {label}");
        }
    }
    println!(
        "first panicking error2 value: positive {first_panic_pos:?}, negative {first_panic_neg:?}"
    );
    let _ = panic::take_hook();
}
