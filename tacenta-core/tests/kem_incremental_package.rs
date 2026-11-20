//! The KEM wrapper (`tacenta-kem`) against libcrux's standard ML-KEM-1024 API.
//!
//! The wrapper's own tests (`kem/src/lib.rs`) check that the incremental path
//! agrees with itself: what `encapsulate1` and `encapsulate2` produce,
//! `decapsulate` recovers. A wrapper that fed the library the wrong
//! randomness, the wrong half of a key, or a mis-sized slice would still pass
//! them, because it would be wrong consistently. The tests here put a second
//! path on the other side of the comparison.
//!
//! # What the oracle is, and is not
//!
//! No FIPS 203 known-answer vectors are in this repository or in the offline
//! dependency sources (searched: `tacenta-test-vectors/`, the crate tests, the
//! vendored `libcrux-ml-kem` 0.0.10 source, which ships no `tests/`
//! directory). So **nothing here is an independent known answer**. There are
//! two kinds of expected value, and each test says which it uses:
//!
//! * The *standard-API oracle*: libcrux's non-incremental
//!   `mlkem1024::{generate_key_pair, encapsulate, decapsulate}` run on the
//!   same bytes. It is the same library, so a defect that sits in code both
//!   paths share (the arithmetic, the hash functions) is invisible to it. What
//!   it does check is the wrapper and the incremental interface: the
//!   randomness plumbing, the split of the key and the ciphertext, the
//!   lengths, the order of the halves.
//! * The *committed expected file* (`kem_incremental_expected.txt`): outputs of
//!   this wrapper at fixed inputs, written once from a build with libcrux's
//!   portable backend forced and checked on every build. It pins the output
//!   against changes of library version, build and wrapper code. It is a
//!   regression anchor, not a known answer: it was produced by the code it
//!   checks.
//!
//! # Fixed randomness
//!
//! Every random byte in this file comes from [`TestOnlyFixedRng`], which
//! replays bytes a test supplies. It is not a random source and must not be
//! copied into library or application code. A test that supplies the bytes
//! also learns exactly how many the wrapper drew, and fails if that is not the
//! 64 (key generation) or 32 (encapsulation) the library takes.
//!
//! # Backends
//!
//! libcrux chooses between portable, NEON and AVX2 arithmetic by CPU at run
//! time, among those its build script compiled in. The CI step that runs this
//! file a second time compiles only the portable one (see the `rust` job's
//! `rust_portable_kem` step). In-process, `portable_instantiation_*` compares
//! the wrapper (whatever the CPU dispatches to) with libcrux's explicit
//! `mlkem1024::portable` module.

use libcrux_ml_kem::mlkem1024::{
    self, MlKem1024Ciphertext, MlKem1024PrivateKey, MlKem1024PublicKey,
};
use rand_core::{CryptoRng, RngCore};
use tacenta_kem::{
    CT1_LEN, CT2_LEN, EK_VECTOR_LEN, ENCAPS_STATE_LEN, EncapsState, HEADER_LEN, IncrementalKeyPair,
    SHARED_SECRET_LEN, encapsulate1, encapsulate2, validate_ek,
};

/// The committed expected outputs; see the module documentation.
const EXPECTED: &str = include_str!("kem_incremental_expected.txt");

/// Length of the seed `IncrementalKeyPair::generate` draws.
const KEYGEN_SEED_LEN: usize = 64;

/// A source of "random" bytes for tests only: it replays a fixed byte string.
///
/// Not a random source. Reading past the end panics, so a wrapper that draws
/// more than the test supplied is a failure, and [`Self::undrawn`] lets a test
/// require that it drew no fewer.
struct TestOnlyFixedRng {
    bytes: Vec<u8>,
    position: usize,
}

impl TestOnlyFixedRng {
    fn new(bytes: Vec<u8>) -> Self {
        TestOnlyFixedRng { bytes, position: 0 }
    }
    fn undrawn(&self) -> usize {
        self.bytes.len() - self.position
    }
}

impl RngCore for TestOnlyFixedRng {
    fn next_u32(&mut self) -> u32 {
        let mut b = [0u8; 4];
        self.fill_bytes(&mut b);
        u32::from_le_bytes(b)
    }
    fn next_u64(&mut self) -> u64 {
        let mut b = [0u8; 8];
        self.fill_bytes(&mut b);
        u64::from_le_bytes(b)
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let end = self.position + dest.len();
        assert!(
            end <= self.bytes.len(),
            "the wrapper drew more bytes than the test supplied"
        );
        dest.copy_from_slice(&self.bytes[self.position..end]);
        self.position = end;
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

// Marker only: lets the test source satisfy the wrapper's bound.
impl CryptoRng for TestOnlyFixedRng {}

/// One SplitMix64 output step.
fn test_only_mix(x: u64) -> u64 {
    let mut z = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Deterministic bytes for case `case` and purpose `purpose`. Test-only. The
/// starting state is mixed from both arguments, so no two (case, purpose)
/// streams are shifted copies of one another.
fn test_only_bytes(case: u64, purpose: u64, len: usize) -> Vec<u8> {
    let mut state = test_only_mix(test_only_mix(case) ^ purpose.rotate_left(32));
    let mut out = Vec::with_capacity(len + 8);
    while out.len() < len {
        state = test_only_mix(state);
        out.extend_from_slice(&state.to_le_bytes());
    }
    out.truncate(len);
    out
}

fn keygen_seed(case: u64) -> [u8; KEYGEN_SEED_LEN] {
    test_only_bytes(case, 1, KEYGEN_SEED_LEN)
        .try_into()
        .unwrap()
}

fn encaps_randomness(case: u64) -> [u8; SHARED_SECRET_LEN] {
    test_only_bytes(case, 2, SHARED_SECRET_LEN)
        .try_into()
        .unwrap()
}

/// Generate through the wrapper from the fixed seed, requiring exactly the
/// 64 bytes the library takes to be drawn.
fn wrapper_key_pair(case: u64) -> IncrementalKeyPair {
    let mut rng = TestOnlyFixedRng::new(keygen_seed(case).to_vec());
    let kp = IncrementalKeyPair::generate(&mut rng).expect("generate");
    assert_eq!(
        rng.undrawn(),
        0,
        "generate must draw exactly the 64-byte seed"
    );
    kp
}

/// `encapsulate1` through the wrapper from the fixed randomness, requiring
/// exactly the 32 bytes the library takes to be drawn.
fn wrapper_encapsulate1(
    case: u64,
    header: &[u8],
) -> (EncapsState, Vec<u8>, [u8; SHARED_SECRET_LEN]) {
    let mut rng = TestOnlyFixedRng::new(encaps_randomness(case).to_vec());
    let out = encapsulate1(header, &mut rng).expect("encapsulate1");
    assert_eq!(rng.undrawn(), 0, "encapsulate1 must draw exactly 32 bytes");
    out
}

/// The standard encapsulation key of the key pair generated from `case`'s
/// seed: `ek_vector || rho`, 1,568 bytes.
fn standard_key_pair(case: u64) -> libcrux_ml_kem::MlKemKeyPair<3168, 1568> {
    mlkem1024::generate_key_pair(keygen_seed(case))
}

const CASES: std::ops::Range<u64> = 0..16;

// ---------------------------------------------------------------------------
// Committed expected outputs
// ---------------------------------------------------------------------------

/// One case's outputs through the wrapper, as the expected file spells them.
fn render_case(case: u64) -> String {
    let kp = wrapper_key_pair(case);
    let header = kp.header();
    let (state, ct1, ss) = wrapper_encapsulate1(case, &header);
    let ct2 = encapsulate2(&state, &kp.ek_vector()).expect("encapsulate2");
    let mut s = String::new();
    s.push_str(&format!("case {case}\n"));
    s.push_str(&format!("keygen_seed {}\n", hex::encode(keygen_seed(case))));
    s.push_str(&format!(
        "encaps_randomness {}\n",
        hex::encode(encaps_randomness(case))
    ));
    s.push_str(&format!("header {}\n", hex::encode(&header)));
    s.push_str(&format!("ek_vector {}\n", hex::encode(kp.ek_vector())));
    s.push_str(&format!("ct1 {}\n", hex::encode(&ct1)));
    s.push_str(&format!("ct2 {}\n", hex::encode(&ct2)));
    s.push_str(&format!("shared_secret {}\n", hex::encode(ss)));
    s
}

const EXPECTED_CASES: [u64; 2] = [0, 1];

/// Prints the expected file. Run with `--ignored --nocapture` under the
/// portable backend to regenerate it; the output is only ever reviewed and
/// committed by hand, and nothing reads it back except the test below.
#[test]
#[ignore = "prints the expected file; see its documentation"]
fn print_expected_file() {
    for case in EXPECTED_CASES {
        print!("{}", render_case(case));
        println!();
    }
}

/// The wrapper's outputs at fixed seeds equal the committed expected file.
///
/// Establishes: the incremental path's public parts, both ciphertext halves
/// and the shared secret are byte-for-byte what they were when the file was
/// written from a portable-only build. Run on the default build it compares
/// that build's output with the portable bytes; which arithmetic that build
/// executed is not recorded here.
///
/// Does not establish: that the file is right. It was produced by this
/// wrapper over this library; it is not a FIPS 203 known answer.
#[test]
fn incremental_outputs_equal_the_committed_expected_file() {
    let mut rendered = String::new();
    for case in EXPECTED_CASES {
        rendered.push_str(&render_case(case));
        rendered.push('\n');
    }
    // Same text, line by line, so a failure names the field.
    let want: Vec<&str> = EXPECTED.lines().collect();
    let got: Vec<&str> = rendered.lines().collect();
    assert_eq!(
        want.len(),
        got.len(),
        "expected file and run differ in length"
    );
    for (i, (w, g)) in want.iter().zip(got.iter()).enumerate() {
        let field = w.split(' ').next().unwrap_or("");
        assert_eq!(
            w,
            g,
            "line {}: field `{}` differs from the committed file",
            i + 1,
            field
        );
    }
}

// ---------------------------------------------------------------------------
// The incremental path against the standard API
// ---------------------------------------------------------------------------

/// The key pair the wrapper generates from a seed has the public parts of the
/// standard key pair generated from the same seed.
///
/// The standard encapsulation key is `ek_vector || rho`; the wrapper's header
/// is `rho || hek` and its `ek_vector` is the first part. So `ek_vector`
/// equals the first 1,536 bytes, `header[..32]` the last 32, and
/// `header[32..]` is `H(ek)` (checked through `validate_ek`, which compares
/// it with the hash libcrux computes, and against the standard
/// `validate_public_key`).
///
/// Oracle: the same library's standard key generation. Does not establish:
/// that either key is a valid FIPS 203 key for the seed (no KAT); the
/// private halves are compared through decapsulation below, not directly,
/// since the two private formats differ.
#[test]
fn incremental_public_parts_equal_the_standard_public_key() {
    for case in CASES {
        let kp = wrapper_key_pair(case);
        let std = standard_key_pair(case);
        let ek = std.pk();
        assert_eq!(
            &ek[..EK_VECTOR_LEN],
            kp.ek_vector().as_slice(),
            "case {case}: ek_vector"
        );
        assert_eq!(&ek[EK_VECTOR_LEN..], &kp.header()[..32], "case {case}: rho");
        assert!(
            mlkem1024::validate_public_key(std.public_key()),
            "case {case}: standard key"
        );
        assert!(
            validate_ek(&kp.header(), &kp.ek_vector()),
            "case {case}: header hash"
        );
    }
}

/// For the same key and the same randomness, `encapsulate1` followed by
/// `encapsulate2` gives exactly the standard encapsulation: ciphertext
/// `ct1 || ct2` (1,408 then 160 bytes, the standard's 1,568) and the same
/// shared secret.
///
/// Oracle: the standard `mlkem1024::encapsulate` of the same library, given
/// the same 32 bytes and the standard key assembled from the wrapper's own
/// public parts (`ek_vector || rho`), so the key is not taken from the
/// oracle's keygen. Establishes: the wrapper hands the library the
/// randomness unaltered, the split is at byte 1,408, the halves are returned
/// in the order the standard concatenates them, and the secret is the
/// standard's. Does not establish: agreement with FIPS 203 beyond the
/// library's own standard path.
#[test]
fn split_encapsulation_equals_the_standard_encapsulation_for_the_same_randomness() {
    for case in CASES {
        let kp = wrapper_key_pair(case);
        let header = kp.header();
        let (state, ct1, ss) = wrapper_encapsulate1(case, &header);
        let ct2 = encapsulate2(&state, &kp.ek_vector()).expect("encapsulate2");
        assert_eq!((ct1.len(), ct2.len()), (CT1_LEN, CT2_LEN));

        let mut ek = [0u8; 1568];
        ek[..EK_VECTOR_LEN].copy_from_slice(&kp.ek_vector());
        ek[EK_VECTOR_LEN..].copy_from_slice(&header[..32]);
        let (std_ct, std_ss) =
            mlkem1024::encapsulate(&MlKem1024PublicKey::from(ek), encaps_randomness(case));

        let mut joined = ct1.clone();
        joined.extend_from_slice(&ct2);
        assert_eq!(
            std_ct.as_slice(),
            joined.as_slice(),
            "case {case}: ct1 || ct2"
        );
        assert_eq!(std_ss, ss, "case {case}: shared secret");
    }
}

/// The standard decapsulation and the wrapper's decapsulation agree, on both
/// a genuine ciphertext and a corrupted one.
///
/// For a genuine `ct1 || ct2` both return the secret `encapsulate1` gave. For
/// a ciphertext with one flipped bit in each half, both return the same
/// implicit-rejection secret, which differs from the genuine one: the check
/// that the wrapper's path rejects as the standard path does, not merely that
/// it accepts.
///
/// Oracle: the standard `mlkem1024::decapsulate` with the private key from
/// the standard key generation at the same seed (the two private formats
/// differ, so the same seed is what ties the keys together). Does not
/// establish agreement with FIPS 203 beyond this library.
#[test]
fn standard_and_incremental_decapsulate_agree_on_genuine_and_corrupted_ciphertexts() {
    for case in CASES {
        let kp = wrapper_key_pair(case);
        let (state, ct1, ss) = wrapper_encapsulate1(case, &kp.header());
        let ct2 = encapsulate2(&state, &kp.ek_vector()).expect("encapsulate2");
        let std = standard_key_pair(case);
        let sk: &MlKem1024PrivateKey = std.private_key();

        let mut joined = ct1.clone();
        joined.extend_from_slice(&ct2);
        let std_ct = MlKem1024Ciphertext::try_from(joined.as_slice()).expect("ct length");
        assert_eq!(
            mlkem1024::decapsulate(sk, &std_ct),
            ss,
            "case {case}: standard decapsulate"
        );
        assert_eq!(
            kp.decapsulate(&ct1, &ct2).unwrap(),
            ss,
            "case {case}: wrapper decapsulate"
        );

        // A corrupted ciphertext: both sides implicitly reject, identically.
        let (mut bad1, mut bad2) = (ct1.clone(), ct2.clone());
        bad1[0] ^= 1;
        bad2[CT2_LEN - 1] ^= 0x80;
        let mut bad_joined = bad1.clone();
        bad_joined.extend_from_slice(&bad2);
        let bad_std = MlKem1024Ciphertext::try_from(bad_joined.as_slice()).expect("ct length");
        let rejected_std = mlkem1024::decapsulate(sk, &bad_std);
        let rejected_wrapper = kp.decapsulate(&bad1, &bad2).unwrap();
        assert_eq!(
            rejected_std, rejected_wrapper,
            "case {case}: implicit rejection"
        );
        assert_ne!(
            rejected_wrapper, ss,
            "case {case}: a corrupted ciphertext must not yield the secret"
        );
    }
}

/// A ciphertext made by the standard `encapsulate`, cut at byte 1,408, is
/// decapsulated by the wrapper to the standard's shared secret.
///
/// The reverse direction of the split test: it needs no wrapper
/// encapsulation, so it checks the wrapper's decapsulation and its
/// ciphertext-half lengths against ciphertext the incremental path never
/// produced. Same oracle and same limits.
#[test]
fn a_standard_ciphertext_split_at_1408_is_decapsulated_by_the_wrapper() {
    for case in CASES {
        let kp = wrapper_key_pair(case);
        let mut ek = [0u8; 1568];
        ek[..EK_VECTOR_LEN].copy_from_slice(&kp.ek_vector());
        ek[EK_VECTOR_LEN..].copy_from_slice(&kp.header()[..32]);
        let (std_ct, std_ss) = mlkem1024::encapsulate(
            &MlKem1024PublicKey::from(ek),
            encaps_randomness(case ^ 0x55),
        );
        let (c1, c2) = std_ct.as_slice().split_at(CT1_LEN);
        assert_eq!(c2.len(), CT2_LEN);
        assert_eq!(kp.decapsulate(c1, c2).unwrap(), std_ss, "case {case}");
    }
}

// ---------------------------------------------------------------------------
// The explicit portable instantiation, in the same process
// ---------------------------------------------------------------------------

/// The wrapper's outputs equal those of libcrux's explicit
/// `mlkem1024::portable` standard instantiation.
///
/// On a build and CPU where libcrux dispatches to NEON or AVX2 this compares
/// that backend (through the incremental interface) with portable arithmetic
/// (through the standard one) in one process; where only portable is compiled
/// in or available it compares portable with portable and still checks the
/// wrapper against the standard interface. It does not by itself show which
/// backend ran: the CI step that forces the portable build, and the committed
/// expected file, are what compare a portable-only build with the default one.
#[test]
fn portable_instantiation_agrees_with_the_wrapper_whatever_the_cpu_dispatches_to() {
    for case in CASES {
        let kp = wrapper_key_pair(case);
        let pstd = mlkem1024::portable::generate_key_pair(keygen_seed(case));
        assert_eq!(
            &pstd.pk()[..EK_VECTOR_LEN],
            kp.ek_vector().as_slice(),
            "case {case}: ek_vector"
        );
        assert_eq!(
            &pstd.pk()[EK_VECTOR_LEN..],
            &kp.header()[..32],
            "case {case}: rho"
        );

        let (state, ct1, ss) = wrapper_encapsulate1(case, &kp.header());
        let ct2 = encapsulate2(&state, &kp.ek_vector()).expect("encapsulate2");
        let (pct, pss) =
            mlkem1024::portable::encapsulate(pstd.public_key(), encaps_randomness(case));
        let mut joined = ct1.clone();
        joined.extend_from_slice(&ct2);
        assert_eq!(pct.as_slice(), joined.as_slice(), "case {case}: ciphertext");
        assert_eq!(pss, ss, "case {case}: shared secret");
        assert_eq!(
            mlkem1024::portable::decapsulate(pstd.private_key(), &pct),
            kp.decapsulate(&ct1, &ct2).unwrap(),
            "case {case}: decapsulate"
        );
    }
}

// ---------------------------------------------------------------------------
// Individual checks of the wrapper's lengths and success cases, one test each
// ---------------------------------------------------------------------------

/// `encapsulate1` succeeds on a header produced by `header` of a freshly
/// generated key pair, and returns the ciphertext half and secret sizes.
#[test]
fn encapsulate1_succeeds_on_a_header_from_header_of_generate() {
    for case in 0..4 {
        let kp = wrapper_key_pair(case);
        let header = kp.header();
        assert_eq!(header.len(), HEADER_LEN);
        let mut rng = TestOnlyFixedRng::new(encaps_randomness(case).to_vec());
        let (_state, ct1, ss) = encapsulate1(&header, &mut rng).expect("encapsulate1 must succeed");
        assert_eq!(ct1.len(), CT1_LEN);
        assert_ne!(ss, [0u8; SHARED_SECRET_LEN]);
    }
}

/// `encapsulate2` succeeds on the matching `ek_vector` with the state
/// `encapsulate1` returned, and returns a 160-byte second half.
#[test]
fn encapsulate2_succeeds_on_the_matching_ek_vector_with_the_state_from_encapsulate1() {
    for case in 0..4 {
        let kp = wrapper_key_pair(case);
        let (state, _ct1, _ss) = wrapper_encapsulate1(case, &kp.header());
        let ct2 = encapsulate2(&state, &kp.ek_vector()).expect("encapsulate2 must succeed");
        assert_eq!(ct2.len(), CT2_LEN);
    }
}

/// The encapsulation state `encapsulate1` leaves behind serialises to exactly
/// 2,592 bytes, and `ENCAPS_STATE_LEN` says so.
#[test]
fn the_state_after_encapsulate1_serialises_to_exactly_2592_bytes() {
    assert_eq!(ENCAPS_STATE_LEN, 2592);
    for case in 0..4 {
        let kp = wrapper_key_pair(case);
        let (state, _ct1, _ss) = wrapper_encapsulate1(case, &kp.header());
        assert_eq!(state.to_bytes().len(), 2592);
    }
}

/// `decapsulate` of the two halves returns the shared secret `encapsulate1`
/// returned.
#[test]
fn decapsulate_returns_the_shared_secret_encapsulate1_returned() {
    for case in 0..4 {
        let kp = wrapper_key_pair(case);
        let (state, ct1, ss) = wrapper_encapsulate1(case, &kp.header());
        let ct2 = encapsulate2(&state, &kp.ek_vector()).expect("encapsulate2");
        assert_eq!(kp.decapsulate(&ct1, &ct2).expect("decapsulate"), ss);
    }
}
