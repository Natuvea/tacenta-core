//! ML-KEM-1024 against NIST ACVP sample vectors: tested agreement with the
//! expected answers in upstream's published sample files.
//!
//! # What the data is
//!
//! `tests/data/acvp-ml-kem/` vendors the sample vector sets for ML-KEM from
//! the `usnistgov/ACVP-Server` repository at the commit recorded in its
//! `PROVENANCE.md`, in both test revisions upstream publishes for the
//! standard (`FIPS203` and `FIPS203-tr1`), byte for byte. The tests read the
//! ML-KEM-1024 cases from `mlkem1024-acvp-fixture.json`, a re-arrangement of
//! those files written by the vendored `extract.py` and reproduced by
//! `kem_acvp_provenance.rs`. Every expected value here is upstream's. None
//! was produced, adjusted or selected using this repository's code or
//! libcrux, there is no mode that rewrites one, and an empty or missing
//! group, a changed case count or an altered expected value fails a test.
//!
//! # What this establishes, and what it does not
//!
//! Passing establishes tested agreement, on these cases, between the
//! implementations named below and the sample expected answers. It is not
//! FIPS 203 certification or validation, not conformance testing by an
//! accredited laboratory, not independent human review, and not a
//! correctness theorem. The samples are a small selection (see the case
//! counts asserted below).
//!
//! # Which paths are checked against external answers directly
//!
//! * Standard API (libcrux `mlkem1024::{generate_key_pair, encapsulate,
//!   decapsulate}`): key generation, encapsulation and decapsulation, each
//!   compared with upstream's expected `ek`/`dk`, `c`/`k` and `k`. Direct.
//! * Incremental path (`tacenta-kem`):
//!   - key generation: the wrapper's `generate`, given the ACVP seed, has the
//!     public parts of the expected `ek` (`ek_vector` and `rho`) and the hash
//!     `H(ek)` that sits in the expected `dk`. Direct for the public parts.
//!     Its private half is exercised only through decapsulation below.
//!   - encapsulation: `encapsulate1` then `encapsulate2` from the expected
//!     `ek` and `m` give the expected `c` and `k`. Direct. The wrapper only
//!     encapsulates to a header (`rho || H(ek)`) and an `ek_vector`, so the
//!     header is derived from the ACVP `ek` here with a test-only SHA3-256
//!     (checked first against FIPS 202 known answers and against the `H(ek)`
//!     stored in the ACVP decapsulation keys).
//!   - decapsulation: only the `FIPS203-tr1` seed-format group carries the
//!     seeds `d`, `z` that the wrapper can be given; its `decapsulate` of the
//!     expected `c` (split at 1,408 bytes), on cases upstream labels valid and modified, gives the
//!     expected `k`. Direct. The expanded-format `dk` of the other
//!     decapsulation groups cannot be loaded into the wrapper:
//!     `IncrementalKeyPair` is made by `generate` from a random source or
//!     restored by `from_bytes` from its own serialisation (a different
//!     layout), and has no constructor from a FIPS 203 decapsulation key. Those
//!     groups are therefore checked against the standard API only.
//!   - the wrapper's `validate_ek` is run on the key-check cases that carry an
//!     encapsulation key (header derived as above).
//!
//! Which path was run through the standard API versus the wrapper is stated in
//! each test's comment. The existing `kem_incremental_package.rs` compares the
//! two paths with each other on generated inputs; that comparison is
//! same-library and is not external.
//!
//! # Seed order
//!
//! ACVP's key-generation inputs are `d` and `z` (32 bytes each), the inputs of
//! FIPS 203 Algorithm 16 `ML-KEM.KeyGen_internal(d, z)` (Algorithm 19
//! `ML-KEM.KeyGen` draws `d` then `z`). libcrux's `generate_key_pair` takes a
//! 64-byte array and, in `src/ind_cca.rs` of `libcrux-ml-kem` 0.0.10, uses
//! bytes `0..32` as the K-PKE key-generation seed (`d`) and `32..64` as the
//! implicit-rejection value (`z`); `IncrementalKeyPair::generate` draws those
//! 64 bytes in one fill and passes them unchanged. So the seed is `d || z`.
//! That reading is also checked by the data: with `d || z` the expected `ek`
//! and `dk` are produced for all 25 cases, and `dk` ends with `z`.
//!
//! # Key checks
//!
//! `encapsulationKeyCheck` is run through libcrux's `validate_public_key` and
//! the wrapper's `validate_ek`; `decapsulationKeyCheck` through libcrux's
//! `validate_private_key_only` (the hash check). The "valid" or "modified"
//! label of each case is UPSTREAM'S, carried in the fixture as `reason` (from
//! upstream's internal projection file), and
//! the expected `testPassed` is upstream's. Not exercised: the checks of FIPS
//! 203 section 7.3 steps other than that hash check are not separate public
//! entry points here, so the `decapsulationKeyCheck` cases show only that
//! the hash check agrees with upstream's expected result.
//!
//! # Upstream's labels
//!
//! Wherever this file says a decapsulation case is "valid" or has a "modified
//! ciphertext", or a key check is "valid", "modified H" or "noisy linear
//! system values too large", that is UPSTREAM'S label, read from the `reason`
//! field of upstream's internal projection file and carried in the fixture. The
//! tests do not establish it independently. What a decapsulation test
//! establishes is that the implementation returns the expected `k` for the
//! `dk` and `c` given, whichever label upstream put on the case; it does not
//! establish why or how upstream modified a ciphertext, or that the
//! ciphertext differs from a valid one. What a key-check test establishes is
//! that the implementation's answer equals upstream's expected `testPassed`.
//! The only classifications the tests check themselves are the counts per
//! label, so that a changed fixture is noticed.
//!
//! # Revisions
//!
//! `FIPS203` and `FIPS203-tr1` are upstream's two test revisions. The ACVP
//! specification says "FIPS203-tr1 indicates a new test revision against the
//! same standard, FIPS 203": a newer test revision of the same standard, not a
//! different algorithm edition. The two are labelled separately throughout
//! (directory names, fixture keys, test names, assertion messages).
//!
//! # Fixed randomness
//!
//! [`TestOnlyFixedRng`] replays supplied bytes. It is not a random source and
//! must not be copied into library or application code.

use libcrux_ml_kem::mlkem1024::{
    self, MlKem1024Ciphertext, MlKem1024PrivateKey, MlKem1024PublicKey,
};
use rand_core::{CryptoRng, RngCore};
use serde_json::Value;
use tacenta_kem::{
    CT1_LEN, CT2_LEN, EK_VECTOR_LEN, HEADER_LEN, IncrementalKeyPair, SHARED_SECRET_LEN,
    encapsulate1, encapsulate2, validate_ek,
};

const FIXTURE: &str = include_str!("data/acvp-ml-kem/mlkem1024-acvp-fixture.json");

const FIPS203: &str = "ML-KEM-encapDecap-FIPS203";
const FIPS203_TR1: &str = "ML-KEM-encapDecap-FIPS203-tr1";
const KEYGEN: &str = "ML-KEM-keyGen-FIPS203";

/// The groups the fixture must hold, and nothing else: directory (revision),
/// function (`keyGen` for the key-generation set), key format, `tgId`, number
/// of cases, and the number of cases carrying each `reason` (empty where
/// upstream gives none). Written out here so that a missing group, a deleted
/// case or an added one fails the first test.
struct Expect {
    revision: &'static str,
    function: &'static str,
    key_format: Option<&'static str>,
    tg_id: u64,
    cases: usize,
    reasons: &'static [(&'static str, usize)],
}

const EXPECTED_GROUPS: [Expect; 10] = [
    Expect {
        revision: KEYGEN,
        function: "keyGen",
        key_format: None,
        tg_id: 3,
        cases: 25,
        reasons: &[],
    },
    Expect {
        revision: FIPS203,
        function: "encapsulation",
        key_format: None,
        tg_id: 3,
        cases: 25,
        reasons: &[],
    },
    Expect {
        revision: FIPS203,
        function: "decapsulation",
        key_format: None,
        tg_id: 6,
        cases: 10,
        reasons: &[("valid decapsulation", 5), ("modified ciphertext", 5)],
    },
    Expect {
        revision: FIPS203,
        function: "decapsulationKeyCheck",
        key_format: None,
        tg_id: 11,
        cases: 10,
        reasons: &[("valid decapsulation key", 5), ("modified H", 5)],
    },
    Expect {
        revision: FIPS203,
        function: "encapsulationKeyCheck",
        key_format: None,
        tg_id: 12,
        cases: 10,
        reasons: &[
            ("valid encapsulation key", 5),
            ("noisy linear system values too large", 5),
        ],
    },
    Expect {
        revision: FIPS203_TR1,
        function: "encapsulation",
        key_format: None,
        tg_id: 3,
        cases: 25,
        reasons: &[],
    },
    Expect {
        revision: FIPS203_TR1,
        function: "decapsulation",
        key_format: Some("seed"),
        tg_id: 8,
        cases: 10,
        reasons: &[("valid decapsulation", 5), ("modified ciphertext", 5)],
    },
    Expect {
        revision: FIPS203_TR1,
        function: "decapsulation",
        key_format: Some("expanded"),
        tg_id: 9,
        cases: 10,
        reasons: &[("valid decapsulation", 5), ("modified ciphertext", 5)],
    },
    Expect {
        revision: FIPS203_TR1,
        function: "decapsulationKeyCheck",
        key_format: Some("expanded"),
        tg_id: 14,
        cases: 10,
        reasons: &[("valid decapsulation key", 5), ("modified H", 5)],
    },
    Expect {
        revision: FIPS203_TR1,
        function: "encapsulationKeyCheck",
        key_format: None,
        tg_id: 15,
        cases: 10,
        reasons: &[
            ("valid encapsulation key", 5),
            ("noisy linear system values too large", 5),
        ],
    },
];

// ---------------------------------------------------------------------------
// Fixture access
// ---------------------------------------------------------------------------

fn fixture() -> Value {
    serde_json::from_str(FIXTURE).expect("the vendored fixture parses")
}

/// The cases of the one group of `revision` with this function and key
/// format, after checking its `tgId`, its count and its `reason` counts
/// against [`EXPECTED_GROUPS`]. Panics if the group is absent, duplicated,
/// empty, or differs.
fn group_cases(fx: &Value, revision: &str, function: &str, key_format: Option<&str>) -> Vec<Value> {
    let exp = EXPECTED_GROUPS
        .iter()
        .find(|e| e.revision == revision && e.function == function && e.key_format == key_format)
        .unwrap_or_else(|| panic!("no expectation for {revision}/{function}/{key_format:?}"));
    let groups = fx["revisions"][revision]["groups"]
        .as_array()
        .unwrap_or_else(|| panic!("revision {revision} missing from the fixture"));
    let wanted_fn = if function == "keyGen" {
        None
    } else {
        Some(function)
    };
    let hits: Vec<&Value> = groups
        .iter()
        .filter(|g| g["function"].as_str() == wanted_fn && g["keyFormat"].as_str() == key_format)
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "{revision}/{function}/{key_format:?}: expected exactly one group"
    );
    let g = hits[0];
    assert_eq!(
        g["tgId"].as_u64(),
        Some(exp.tg_id),
        "{revision}/{function}: tgId"
    );
    assert_eq!(g["parameterSet"], "ML-KEM-1024");
    let cases = g["cases"].as_array().expect("cases").clone();
    assert!(
        !cases.is_empty(),
        "{revision}/{function} tg{}: empty group",
        exp.tg_id
    );
    assert_eq!(
        cases.len(),
        exp.cases,
        "{revision}/{function} tg{}: case count",
        exp.tg_id
    );
    for (reason, n) in exp.reasons {
        let got = cases
            .iter()
            .filter(|c| c["reason"].as_str() == Some(reason))
            .count();
        assert_eq!(
            got, *n,
            "{revision}/{function} tg{}: cases with reason {reason:?}",
            exp.tg_id
        );
    }
    let labelled: usize = exp.reasons.iter().map(|(_, n)| n).sum();
    let with_reason = cases.iter().filter(|c| c.get("reason").is_some()).count();
    assert_eq!(
        with_reason, labelled,
        "{revision}/{function} tg{}: unexpected reasons",
        exp.tg_id
    );
    cases
}

fn hexval(section: &Value, key: &str) -> Vec<u8> {
    hex::decode(
        section[key]
            .as_str()
            .unwrap_or_else(|| panic!("missing {key}")),
    )
    .unwrap_or_else(|e| panic!("{key} is not hex: {e}"))
}

fn input(case: &Value, key: &str) -> Vec<u8> {
    hexval(&case["inputs"], key)
}

fn expected(case: &Value, key: &str) -> Vec<u8> {
    hexval(&case["expected"], key)
}

fn tc(case: &Value) -> u64 {
    case["tcId"].as_u64().expect("tcId")
}

fn arr<const N: usize>(v: &[u8]) -> [u8; N] {
    v.try_into()
        .unwrap_or_else(|_| panic!("expected {N} bytes, got {}", v.len()))
}

/// `d || z`: see "Seed order" in the module documentation.
fn seed_d_z(case: &Value) -> [u8; 64] {
    let mut s = [0u8; 64];
    s[..32].copy_from_slice(&input(case, "d"));
    s[32..].copy_from_slice(&input(case, "z"));
    s
}

// ---------------------------------------------------------------------------
// Test-only helpers
// ---------------------------------------------------------------------------

/// A source of "random" bytes for tests only: it replays a fixed byte string.
/// Not a random source. Reading past the end panics.
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

/// SHA3-256 (FIPS 202), test-only. The wrapper takes an encapsulation key as a
/// header `rho || H(ek)` and `ek_vector`, so building a header from an ACVP
/// `ek` needs `H(ek) = SHA3-256(ek)`; the root package has no SHA3 dependency
/// and adding one would change the lockfile. Written from FIPS 202, and
/// checked below before any use against two published known answers and
/// against the 25 `H(ek)` values stored in the ACVP keys.
fn test_only_sha3_256(msg: &[u8]) -> [u8; 32] {
    const RC: [u64; 24] = [
        0x0000_0000_0000_0001,
        0x0000_0000_0000_8082,
        0x8000_0000_0000_808a,
        0x8000_0000_8000_8000,
        0x0000_0000_0000_808b,
        0x0000_0000_8000_0001,
        0x8000_0000_8000_8081,
        0x8000_0000_0000_8009,
        0x0000_0000_0000_008a,
        0x0000_0000_0000_0088,
        0x0000_0000_8000_8009,
        0x0000_0000_8000_000a,
        0x0000_0000_8000_808b,
        0x8000_0000_0000_008b,
        0x8000_0000_0000_8089,
        0x8000_0000_0000_8003,
        0x8000_0000_0000_8002,
        0x8000_0000_0000_0080,
        0x0000_0000_0000_800a,
        0x8000_0000_8000_000a,
        0x8000_0000_8000_8081,
        0x8000_0000_0000_8080,
        0x0000_0000_8000_0001,
        0x8000_0000_8000_8008,
    ];
    const ROT: [u32; 24] = [
        1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
    ];
    const PI: [usize; 24] = [
        10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
    ];
    const RATE: usize = 136;

    fn permute(a: &mut [u64; 25], rc: &[u64; 24], rot: &[u32; 24], pi: &[usize; 24]) {
        for round_constant in rc {
            let mut c = [0u64; 5];
            for x in 0..5 {
                c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
            }
            for x in 0..5 {
                let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
                for y in 0..5 {
                    a[x + 5 * y] ^= d;
                }
            }
            let mut t = a[1];
            for i in 0..24 {
                let j = pi[i];
                let b = a[j];
                a[j] = t.rotate_left(rot[i]);
                t = b;
            }
            for y in 0..5 {
                let row = [
                    a[5 * y],
                    a[5 * y + 1],
                    a[5 * y + 2],
                    a[5 * y + 3],
                    a[5 * y + 4],
                ];
                for x in 0..5 {
                    a[5 * y + x] = row[x] ^ (!row[(x + 1) % 5] & row[(x + 2) % 5]);
                }
            }
            a[0] ^= round_constant;
        }
    }

    let mut padded = msg.to_vec();
    padded.push(0x06);
    padded.resize((msg.len() / RATE + 1) * RATE, 0);
    let last = padded.len() - 1;
    padded[last] |= 0x80;
    let mut state = [0u64; 25];
    for block in padded.chunks(RATE) {
        for (i, lane) in block.chunks(8).enumerate() {
            state[i] ^= u64::from_le_bytes(lane.try_into().expect("8 bytes"));
        }
        permute(&mut state, &RC, &ROT, &PI);
    }
    let mut out = [0u8; 32];
    for (i, chunk) in out.chunks_mut(8).enumerate() {
        chunk.copy_from_slice(&state[i].to_le_bytes());
    }
    out
}

/// The wrapper's header for an encapsulation key: `rho || H(ek)`, where `rho`
/// is the last 32 bytes of `ek` and `ek_vector` is the first 1,536. The same
/// relation the wrapper's own documentation states (`header` is `ek_seed ||
/// hek`).
fn header_and_vector(ek: &[u8]) -> (Vec<u8>, Vec<u8>) {
    assert_eq!(ek.len(), 1568);
    let mut header = ek[EK_VECTOR_LEN..].to_vec();
    header.extend_from_slice(&test_only_sha3_256(ek));
    assert_eq!(header.len(), HEADER_LEN);
    (header, ek[..EK_VECTOR_LEN].to_vec())
}

// ---------------------------------------------------------------------------
// The data itself
// ---------------------------------------------------------------------------

/// Every group is present with its `tgId`, case count and labelled cases, and
/// no group is missing or empty. Both revisions, every selected function.
#[test]
fn the_fixture_holds_exactly_the_expected_groups_and_case_counts() {
    let fx = fixture();
    let mut total = 0;
    for e in &EXPECTED_GROUPS {
        total += group_cases(&fx, e.revision, e.function, e.key_format).len();
    }
    assert_eq!(total, 25 + 25 + 10 + 10 + 10 + 25 + 10 + 10 + 10 + 10);
    // No group beyond the expected ones.
    let mut listed = 0;
    for rev in [FIPS203, FIPS203_TR1, KEYGEN] {
        listed += fx["revisions"][rev]["groups"]
            .as_array()
            .expect("groups")
            .len();
    }
    assert_eq!(
        listed, 10,
        "the fixture holds a group this file does not name"
    );
    assert_eq!(fx["revisions"].as_object().expect("revisions").len(), 3);
}

/// The test-only SHA3-256 against FIPS 202 known answers and against `H(ek)`
/// as stored in the ACVP decapsulation keys (`dk = dkPKE || ek || H(ek) || z`,
/// so `H(ek)` is `dk[3104..3136]` and `z` is `dk[3136..]`) for the 25 key-generation cases.
#[test]
fn the_test_only_sha3_is_correct_on_published_values() {
    assert_eq!(
        hex::encode(test_only_sha3_256(b"")),
        "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
    );
    assert_eq!(
        hex::encode(test_only_sha3_256(b"abc")),
        "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
    );
    // A message longer than one block.
    assert_eq!(
        hex::encode(test_only_sha3_256(&[0xa3u8; 200])),
        "79f38adec5c20307a98ef76e8324afbfd46cfd81b22e3973c65fa1bd9de31787"
    );
    let fx = fixture();
    let mut checked = 0;
    for case in group_cases(&fx, KEYGEN, "keyGen", None) {
        let (ek, dk) = (expected(&case, "ek"), expected(&case, "dk"));
        assert_eq!(
            &dk[1536..1536 + 1568][..],
            &ek[..],
            "tc{}: dk carries ek",
            tc(&case)
        );
        assert_eq!(
            &test_only_sha3_256(&ek)[..],
            &dk[3104..3136],
            "tc{}: H(ek)",
            tc(&case)
        );
        assert_eq!(
            &dk[3136..],
            input(&case, "z").as_slice(),
            "tc{}: dk ends with z",
            tc(&case)
        );
        checked += 1;
    }
    assert_eq!(checked, 25);
}

// ---------------------------------------------------------------------------
// Key generation
// ---------------------------------------------------------------------------

/// Standard key generation from `d || z` gives the expected `ek` and `dk`.
/// Direct comparison with external answers (libcrux standard API).
#[test]
fn standard_key_generation_gives_the_expected_keys() {
    let fx = fixture();
    for case in group_cases(&fx, KEYGEN, "keyGen", None) {
        let kp = mlkem1024::generate_key_pair(seed_d_z(&case));
        assert_eq!(
            kp.pk().as_slice(),
            expected(&case, "ek").as_slice(),
            "tc{}: ek",
            tc(&case)
        );
        assert_eq!(
            kp.sk().as_slice(),
            expected(&case, "dk").as_slice(),
            "tc{}: dk",
            tc(&case)
        );
    }
}

/// The wrapper's `generate`, fed `d || z` through a fixed test-only source,
/// draws exactly those 64 bytes and has the expected public key: `ek_vector`
/// the first 1,536 bytes of `ek`, the header's first half `rho` the last 32,
/// and its second half `H(ek)` the value stored in the expected `dk`.
/// Direct for the public parts; the private half is not compared here
/// (formats differ) and is exercised through decapsulation.
#[test]
fn wrapper_key_generation_gives_the_expected_public_parts() {
    let fx = fixture();
    for case in group_cases(&fx, KEYGEN, "keyGen", None) {
        let (ek, dk) = (expected(&case, "ek"), expected(&case, "dk"));
        let mut rng = TestOnlyFixedRng::new(seed_d_z(&case).to_vec());
        let kp = IncrementalKeyPair::generate(&mut rng).expect("generate");
        assert_eq!(
            rng.undrawn(),
            0,
            "tc{}: generate must draw exactly 64 bytes",
            tc(&case)
        );
        assert_eq!(
            kp.ek_vector().as_slice(),
            &ek[..EK_VECTOR_LEN],
            "tc{}: ek_vector",
            tc(&case)
        );
        let header = kp.header();
        assert_eq!(&header[..32], &ek[EK_VECTOR_LEN..], "tc{}: rho", tc(&case));
        assert_eq!(&header[32..], &dk[3104..3136], "tc{}: H(ek)", tc(&case));
        assert!(
            validate_ek(&header, &kp.ek_vector()),
            "tc{}: header checks the vector",
            tc(&case)
        );
    }
}

// ---------------------------------------------------------------------------
// Encapsulation
// ---------------------------------------------------------------------------

/// Standard encapsulation of `m` to the expected `ek` gives the expected `c`
/// and `k`. Direct, standard API; one test per revision.
fn check_standard_encapsulation_gives_the_expected_ciphertext_and_secret(rev: &str) {
    let fx = fixture();
    for case in group_cases(&fx, rev, "encapsulation", None) {
        let pk = MlKem1024PublicKey::from(arr::<1568>(&input(&case, "ek")));
        let (c, k) = mlkem1024::encapsulate(&pk, arr::<32>(&input(&case, "m")));
        assert_eq!(
            c.as_slice(),
            expected(&case, "c").as_slice(),
            "{rev} tc{}: c",
            tc(&case)
        );
        assert_eq!(
            k.as_slice(),
            expected(&case, "k").as_slice(),
            "{rev} tc{}: k",
            tc(&case)
        );
    }
}

#[test]
fn fips203_standard_encapsulation_gives_the_expected_ciphertext_and_secret() {
    check_standard_encapsulation_gives_the_expected_ciphertext_and_secret(FIPS203);
}

#[test]
fn fips203_tr1_standard_encapsulation_gives_the_expected_ciphertext_and_secret() {
    check_standard_encapsulation_gives_the_expected_ciphertext_and_secret(FIPS203_TR1);
}

/// The incremental path, `encapsulate1` then `encapsulate2`, from the header
/// and `ek_vector` derived from the expected `ek` (see
/// [`header_and_vector`]) and `m` through a fixed test-only source, gives
/// `ct1 || ct2` equal to the expected `c` and the expected `k`. Direct; both
/// revisions. `encapsulate1` must draw exactly 32 bytes.
fn check_incremental_encapsulation_gives_the_expected_ciphertext_and_secret(rev: &str) {
    let fx = fixture();
    for case in group_cases(&fx, rev, "encapsulation", None) {
        let ek = input(&case, "ek");
        let (header, ek_vector) = header_and_vector(&ek);
        assert!(
            validate_ek(&header, &ek_vector),
            "{rev} tc{}: derived header",
            tc(&case)
        );
        let mut rng = TestOnlyFixedRng::new(input(&case, "m"));
        let (state, ct1, k) = encapsulate1(&header, &mut rng).expect("encapsulate1");
        assert_eq!(
            rng.undrawn(),
            0,
            "{rev} tc{}: encapsulate1 must draw exactly 32 bytes",
            tc(&case)
        );
        let ct2 = encapsulate2(&state, &ek_vector).expect("encapsulate2");
        assert_eq!((ct1.len(), ct2.len()), (CT1_LEN, CT2_LEN));
        let mut joined = ct1;
        joined.extend_from_slice(&ct2);
        assert_eq!(
            joined,
            expected(&case, "c"),
            "{rev} tc{}: ct1 || ct2",
            tc(&case)
        );
        assert_eq!(k.len(), SHARED_SECRET_LEN);
        assert_eq!(
            k.as_slice(),
            expected(&case, "k").as_slice(),
            "{rev} tc{}: k",
            tc(&case)
        );
    }
}

#[test]
fn fips203_incremental_encapsulation_gives_the_expected_ciphertext_and_secret() {
    check_incremental_encapsulation_gives_the_expected_ciphertext_and_secret(FIPS203);
}

#[test]
fn fips203_tr1_incremental_encapsulation_gives_the_expected_ciphertext_and_secret() {
    check_incremental_encapsulation_gives_the_expected_ciphertext_and_secret(FIPS203_TR1);
}

// ---------------------------------------------------------------------------
// Decapsulation
// ---------------------------------------------------------------------------

fn standard_decapsulate(dk: &[u8], c: &[u8]) -> [u8; 32] {
    let sk = MlKem1024PrivateKey::from(arr::<3168>(dk));
    let ct = MlKem1024Ciphertext::from(arr::<1568>(c));
    mlkem1024::decapsulate(&sk, &ct)
}

/// Standard decapsulation of the expected `c` with the expected `dk` gives the
/// expected `k`, for the cases upstream labels "valid decapsulation" and those
/// it labels "modified ciphertext" (upstream's labels; for the latter its
/// expected `k` is what an implicit-rejection path returns, and the test
/// establishes only that this implementation returns that `k`). Direct,
/// standard API; the `FIPS203` group and the `FIPS203-tr1` expanded group.
fn check_standard_decapsulation_gives_the_expected_secret_including_implicit_rejection(
    rev: &str,
    kf: Option<&str>,
) {
    let fx = fixture();
    for case in group_cases(&fx, rev, "decapsulation", kf) {
        let got = standard_decapsulate(&input(&case, "dk"), &input(&case, "c"));
        assert_eq!(
            got.as_slice(),
            expected(&case, "k").as_slice(),
            "{rev} tc{} ({}): k",
            tc(&case),
            case["reason"].as_str().unwrap_or("")
        );
    }
}

#[test]
fn fips203_standard_decapsulation_gives_the_expected_secret() {
    check_standard_decapsulation_gives_the_expected_secret_including_implicit_rejection(
        FIPS203, None,
    );
}

#[test]
fn fips203_tr1_expanded_standard_decapsulation_gives_the_expected_secret() {
    check_standard_decapsulation_gives_the_expected_secret_including_implicit_rejection(
        FIPS203_TR1,
        Some("expanded"),
    );
}

/// The `FIPS203-tr1` seed-format group, through both paths from the seeds
/// `d`, `z`: the standard API's key and the wrapper's key pair, each
/// decapsulating the expected `c` to the expected `k`, on the cases upstream
/// labels valid and those it labels modified ciphertext (upstream's labels). The wrapper takes the ciphertext as two halves cut at
/// byte 1,408. Direct, for both the standard and the incremental decapsulation.
#[test]
fn seed_format_decapsulation_gives_the_expected_secret_on_both_paths() {
    let fx = fixture();
    let cases = group_cases(&fx, FIPS203_TR1, "decapsulation", Some("seed"));
    let (mut valid, mut modified) = (0, 0);
    for case in cases {
        let seed = seed_d_z(&case);
        let c = input(&case, "c");
        let want = expected(&case, "k");
        let label = case["reason"].as_str().unwrap_or("").to_string();

        let std_kp = mlkem1024::generate_key_pair(seed);
        assert_eq!(
            standard_decapsulate(std_kp.sk(), &c).as_slice(),
            want.as_slice(),
            "tc{} ({label}): standard",
            tc(&case)
        );

        let mut rng = TestOnlyFixedRng::new(seed.to_vec());
        let kp = IncrementalKeyPair::generate(&mut rng).expect("generate");
        assert_eq!(rng.undrawn(), 0);
        let (c1, c2) = c.split_at(CT1_LEN);
        assert_eq!(c2.len(), CT2_LEN);
        let got = kp.decapsulate(c1, c2).expect("decapsulate");
        assert_eq!(
            got.as_slice(),
            want.as_slice(),
            "tc{} ({label}): incremental",
            tc(&case)
        );

        match label.as_str() {
            "valid decapsulation" => valid += 1,
            "modified ciphertext" => modified += 1,
            other => panic!("tc{}: unexpected reason {other:?}", tc(&case)),
        }
    }
    assert_eq!((valid, modified), (5, 5));
}

// ---------------------------------------------------------------------------
// Key checks
// ---------------------------------------------------------------------------

/// `encapsulationKeyCheck`: libcrux's `validate_public_key` and the wrapper's
/// `validate_ek` (header derived from the key) each agree with upstream's
/// expected `testPassed`, on the keys upstream labels valid and those it
/// labels "noisy linear system values too large" (upstream's labels).
fn check_encapsulation_key_checks_agree_with_the_expected_results(rev: &str) {
    let fx = fixture();
    let (mut pass, mut fail) = (0, 0);
    for case in group_cases(&fx, rev, "encapsulationKeyCheck", None) {
        let ek = input(&case, "ek");
        let want = case["expected"]["testPassed"]
            .as_bool()
            .expect("testPassed");
        let std = mlkem1024::validate_public_key(&MlKem1024PublicKey::from(arr::<1568>(&ek)));
        assert_eq!(std, want, "{rev} tc{}: validate_public_key", tc(&case));
        let (header, ek_vector) = header_and_vector(&ek);
        assert_eq!(
            validate_ek(&header, &ek_vector),
            want,
            "{rev} tc{}: validate_ek",
            tc(&case)
        );
        if want {
            pass += 1;
        } else {
            fail += 1;
        }
    }
    assert_eq!((pass, fail), (5, 5), "{rev}: valid and invalid keys");
}

#[test]
fn fips203_encapsulation_key_checks_agree_with_the_expected_results() {
    check_encapsulation_key_checks_agree_with_the_expected_results(FIPS203);
}

#[test]
fn fips203_tr1_encapsulation_key_checks_agree_with_the_expected_results() {
    check_encapsulation_key_checks_agree_with_the_expected_results(FIPS203_TR1);
}

/// `decapsulationKeyCheck`: libcrux's `validate_private_key_only` (the check
/// that the stored hash of the encapsulation key is right) agrees with
/// upstream's expected `testPassed`, on the keys upstream labels valid and those it
/// labels "modified H" (upstream's labels).
fn check_decapsulation_key_checks_agree_with_the_expected_results(rev: &str, kf: Option<&str>) {
    let fx = fixture();
    let (mut pass, mut fail) = (0, 0);
    for case in group_cases(&fx, rev, "decapsulationKeyCheck", kf) {
        let dk = input(&case, "dk");
        let want = case["expected"]["testPassed"]
            .as_bool()
            .expect("testPassed");
        let got = mlkem1024::portable::validate_private_key_only(&MlKem1024PrivateKey::from(
            arr::<3168>(&dk),
        ));
        assert_eq!(
            got,
            want,
            "{rev} tc{}: validate_private_key_only",
            tc(&case)
        );
        if want {
            pass += 1;
        } else {
            fail += 1;
        }
    }
    assert_eq!((pass, fail), (5, 5), "{rev}: valid and invalid keys");
}

#[test]
fn fips203_decapsulation_key_checks_agree_with_the_expected_results() {
    check_decapsulation_key_checks_agree_with_the_expected_results(FIPS203, None);
}

#[test]
fn fips203_tr1_expanded_decapsulation_key_checks_agree_with_the_expected_results() {
    check_decapsulation_key_checks_agree_with_the_expected_results(FIPS203_TR1, Some("expanded"));
}
