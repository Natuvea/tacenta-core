//! How the primitives the proofs' random-source laws name read the random source.
//!
//! The lifecycle proofs read randomness as an ordered trace of 32-byte draws and
//! assume three laws about the shipped functions (`tacenta-proofs/LIMITATIONS.md`,
//! "The clauses of `OracleOf`" and the integration screen's paragraph):
//!
//! * `SignFillsOnce64`: `xeddsa::sign` fills one 64-byte buffer and touches the
//!   random source nowhere else, and its signature is a function of the secret,
//!   the message and those 64 bytes;
//! * `KemShape`: `kem::encapsulate` refuses an invalid key before it reads the
//!   random source, and otherwise fills one 32-byte buffer, its result a function
//!   of the key and those 32 bytes;
//! * `GenerateFillsOnce64`: `IncrementalKeyPair::generate` fills one 64-byte seed
//!   and touches the random source nowhere else.
//!
//! The proofs cannot read these bodies (the functions are opaque to the
//! translation), so these tests hold the laws on the shipped source: a counting
//! random source records every call, and a second random source type that yields
//! the same bytes shows that the result depends on the bytes and not on the
//! source. They also drive the primitives the seven totality laws name over edge
//! and sampled inputs, and check the AEAD's length bound. They test the laws on
//! the inputs they try; they do not prove them. Every input is fixed, so the tests
//! are deterministic, and nothing depends on the width of `usize`.

use rand_core::{CryptoRng, RngCore};
use std::cell::RefCell;
use std::rc::Rc;
use tacenta_core::primitives::{aead, dh, kem, xeddsa};
use tacenta_kem::IncrementalKeyPair;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Call {
    Fill(usize),
    TryFill(usize),
    NextU32,
    NextU64,
}

/// A random source that records every call and yields a fixed byte stream.
struct Counting {
    log: Rc<RefCell<Vec<Call>>>,
    state: u8,
}

impl Counting {
    fn new(seed: u8) -> (Counting, Rc<RefCell<Vec<Call>>>) {
        let log = Rc::new(RefCell::new(Vec::new()));
        (
            Counting {
                log: log.clone(),
                state: seed,
            },
            log,
        )
    }
}

fn next_byte(state: &mut u8) -> u8 {
    *state = state.wrapping_mul(31).wrapping_add(7);
    *state
}

impl RngCore for Counting {
    fn next_u32(&mut self) -> u32 {
        self.log.borrow_mut().push(Call::NextU32);
        0
    }
    fn next_u64(&mut self) -> u64 {
        self.log.borrow_mut().push(Call::NextU64);
        0
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.log.borrow_mut().push(Call::Fill(dest.len()));
        for d in dest.iter_mut() {
            *d = next_byte(&mut self.state);
        }
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.log.borrow_mut().push(Call::TryFill(dest.len()));
        for d in dest.iter_mut() {
            *d = next_byte(&mut self.state);
        }
        Ok(())
    }
}
impl CryptoRng for Counting {}

/// A second random source type with the same byte stream through `fill_bytes`
/// and no other method.
struct SameBytes {
    state: u8,
}

impl RngCore for SameBytes {
    fn next_u32(&mut self) -> u32 {
        panic!("next_u32 called")
    }
    fn next_u64(&mut self) -> u64 {
        panic!("next_u64 called")
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        for d in dest.iter_mut() {
            *d = next_byte(&mut self.state);
        }
    }
    fn try_fill_bytes(&mut self, _dest: &mut [u8]) -> Result<(), rand_core::Error> {
        panic!("try_fill_bytes called")
    }
}
impl CryptoRng for SameBytes {}

/// Fixed pseudo-random bytes for inputs.
fn bytes(state: &mut u64, n: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        *state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        out.push((*state >> 33) as u8);
    }
    out
}

fn bytes32(state: &mut u64) -> [u8; 32] {
    let mut b = [0u8; 32];
    b.copy_from_slice(&bytes(state, 32));
    b
}

#[test]
fn xeddsa_sign_fills_one_64_byte_buffer() {
    let mut s = 1u64;
    let secrets = [[11u8; 32], [0u8; 32], [0xffu8; 32], bytes32(&mut s)];
    for secret in secrets {
        for len in [0usize, 1, 31, 32, 33, 64, 1000] {
            let message = bytes(&mut s, len);
            let (mut rng, log) = Counting::new(3);
            let signature = xeddsa::sign(&secret, &message, &mut rng);
            assert_eq!(
                *log.borrow(),
                vec![Call::Fill(64)],
                "one 64-byte fill and no other call (message length {len})"
            );
            let mut same = SameBytes { state: 3 };
            assert_eq!(
                signature,
                xeddsa::sign(&secret, &message, &mut same),
                "the signature depends on the secret, the message and the 64 bytes only"
            );
            let public = dh::PrivateKey::from_bytes(secret).public_key();
            assert!(xeddsa::verify(&public, &message, &signature).is_ok());
        }
    }
}

#[test]
fn kem_encapsulate_refuses_before_reading_and_otherwise_fills_32_bytes() {
    let (mut keygen, _) = Counting::new(1);
    let pair = kem::KeyPair::generate(&mut keygen);
    let public = pair.public_key();
    assert_eq!(public.len(), kem::public_key_len());

    for seed in [9u8, 10, 200] {
        let (mut rng, log) = Counting::new(seed);
        let out = kem::encapsulate(&public, &mut rng).expect("a valid key encapsulates");
        assert_eq!(
            *log.borrow(),
            vec![Call::Fill(32)],
            "one 32-byte fill and no other call"
        );
        let mut same = SameBytes { state: seed };
        assert_eq!(
            out,
            kem::encapsulate(&public, &mut same).expect("a valid key encapsulates"),
            "the result depends on the key and the 32 bytes only"
        );
        assert_eq!(
            kem::decapsulate(&pair, &out.0).expect("decapsulates"),
            out.1
        );
    }

    for len in [0usize, 1, 31, 32, 1567, 1569, 3000] {
        let (mut rng, log) = Counting::new(1);
        assert!(kem::encapsulate(&vec![7u8; len], &mut rng).is_err());
        assert!(
            log.borrow().is_empty(),
            "no call before refusing a key of length {len}"
        );
    }
    let mut s = 2u64;
    let mut refused = 0;
    for _ in 0..50 {
        let candidate = bytes(&mut s, public.len());
        let (mut rng, log) = Counting::new(1);
        if kem::encapsulate(&candidate, &mut rng).is_err() {
            refused += 1;
            assert!(
                log.borrow().is_empty(),
                "no call before refusing a malformed key"
            );
        } else {
            assert_eq!(*log.borrow(), vec![Call::Fill(32)]);
        }
    }
    assert!(refused > 0, "some random 1568-byte strings are refused");
}

#[test]
fn incremental_key_generation_fills_one_64_byte_seed() {
    for seed in [1u8, 2, 77] {
        let (mut rng, log) = Counting::new(seed);
        let pair = IncrementalKeyPair::generate(&mut rng).expect("generates");
        assert_eq!(
            *log.borrow(),
            vec![Call::Fill(64)],
            "one 64-byte fill and no other call"
        );
        let mut same = SameBytes { state: seed };
        let again = IncrementalKeyPair::generate(&mut same).expect("generates");
        assert_eq!(
            pair.header(),
            again.header(),
            "the pair depends on the 64 bytes only"
        );
        assert_eq!(pair.ek_vector(), again.ek_vector());
    }
}

#[test]
fn the_totality_laws_hold_on_sampled_inputs() {
    let mut s = 3u64;
    // DhCodecTotal, DhAgreeTotal, DhIdentityTotal: every call returns, and the
    // codec round trips, also for bytes a clamp would change.
    let mut keys = vec![[0u8; 32], [0xffu8; 32], [1u8; 32], [5u8; 32], [0x80u8; 32]];
    for _ in 0..200 {
        keys.push(bytes32(&mut s));
    }
    let own = dh::PrivateKey::from_bytes([9u8; 32]);
    for k in &keys {
        let private = dh::PrivateKey::from_bytes(*k);
        assert_eq!(*private.to_bytes(), *k);
        let public = dh::PublicKeyBytes::from_bytes(*k);
        assert_eq!(*public.as_bytes(), *k);
        let _ = private.public_key();
        let _ = own.agree(&public);
        let _ = dh::is_prime_order_public(&public);
        assert!(public == dh::PublicKeyBytes::from_bytes(*k));
    }

    // AeadSealBounded and AeadOpenTotal: sealing returns at most 48 bytes more
    // than the plaintext and opens back to it; opening returns on any bytes.
    let enc = [1u8; 32];
    let mac = [2u8; 32];
    let iv = [3u8; 16];
    for n in 0..300usize {
        let plaintext = bytes(&mut s, n);
        let ad = bytes(&mut s, n % 7);
        let ciphertext = aead::encrypt(&enc, &mac, &iv, &plaintext, &ad);
        assert!(
            ciphertext.len() <= n + 48,
            "{} > {} + 48",
            ciphertext.len(),
            n
        );
        assert_eq!(
            aead::decrypt(&enc, &mac, &iv, &ciphertext, &ad).expect("opens"),
            plaintext
        );
        let junk = bytes(&mut s, n);
        let _ = aead::decrypt(&enc, &mac, &iv, &junk, &ad);
    }

    // KemDecapsulateTotal: returns for every ciphertext length up to 2000.
    let (mut keygen, _) = Counting::new(4);
    let pair = kem::KeyPair::generate(&mut keygen);
    for n in 0..=2000usize {
        let ciphertext = vec![n as u8; n];
        let result = kem::decapsulate(&pair, &ciphertext);
        if n != kem::ciphertext_len() {
            assert!(result.is_err(), "a ciphertext of length {n} is refused");
        }
    }

    // XeddsaVerifyTotal: returns for edge and sampled keys and signatures.
    let messages: [&[u8]; 3] = [b"", b"m", &[0u8; 300]];
    for k in keys.iter().take(60) {
        let public = dh::PublicKeyBytes::from_bytes(*k);
        for m in messages {
            for signature in [[0u8; 64], [0xffu8; 64], [0x80u8; 64]] {
                let _ = xeddsa::verify(&public, m, &signature);
            }
            let mut signature = [0u8; 64];
            signature.copy_from_slice(&bytes(&mut s, 64));
            let _ = xeddsa::verify(&public, m, &signature);
        }
    }
}
