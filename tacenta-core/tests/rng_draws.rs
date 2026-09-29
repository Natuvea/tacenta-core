//! How much randomness the shipped code asks for, in what shape, and when it
//! declines to ask: pinned from the outside with a recording generator.
//!
//! What is pinned, and what the specification says about it:
//!
//! - **ML-KEM encapsulation refuses a malformed key before it touches the
//!   random source.** The refusal set is FIPS 203 section 7.2's: a key that is
//!   not 1,568 bytes, or whose first 1,536 bytes do not survive
//!   `ByteEncode12(ByteDecode12(..))` (some 12-bit coefficient is not below
//!   3,329). `tacenta-spec/protocol/session-establishment.md` (ML-KEM-1024)
//!   orders those checks before the encapsulation, and the encapsulation is
//!   what "draws 32 random bytes `m`"; it does not itself say that a refusal
//!   leaves the random source untouched. The shipped code does, and these tests
//!   hold it to that, so a change is a decision and not an accident. A valid
//!   key is never refused and costs exactly one 32-byte request.
//! - **XEdDSA signing takes its nonce input `Z` as one 64-byte request**
//!   (`tacenta-spec/protocol/identities-and-devices.md`, "Z = 64 fresh random
//!   bytes"; `tacenta-spec/threat-model/assumptions.md`, ASM-01, "the 64 bytes
//!   `Z` of each XEdDSA signature"), and the signature depends on exactly the
//!   first 64 bytes of the stream, in whatever call shape they arrive.
//! - **The session draws what the specification lists**
//!   (`tacenta-spec/threat-model/assumptions.md`, ASM-01): at establishment,
//!   the initiator's ephemeral key, the 32 bytes of the encapsulation and its
//!   first ratchet key pair; the Braid's key generation, 64 bytes `d || z`
//!   (`tacenta-spec/protocol/mlkem-braid.md`, "Key generation draws 64 random
//!   bytes"), on the initiator's first send; and the Braid's 32-byte
//!   encapsulation randomness `m` (same page) on the sends where the other side
//!   encapsulates. The specification does not say when a receive draws its
//!   candidate ratchet key; the shipped code draws one 32-byte X25519 private
//!   key on every successful receive and adopts it only when the receive takes a
//!   Diffie-Hellman step, and the conversation test below records that as a
//!   characterisation of the shipped behaviour.
//!
//! The order in which an establishment draws its three 32-byte values is not
//! a specification sentence either. It is pinned from the values themselves
//! (ephemeral, then encapsulation, then ratchet key), as a characterisation
//! of the shipped behaviour; `establishInitiator` in
//! `tacenta-model/Model/Lifecycle.lean` takes them in the same order.
//!
//! These tests live in the root package rather than in `tacenta-boundary`
//! because `tacenta-core/boundary` and `tacenta-core/kem` are translation
//! inputs: their bytes are hashed into every recorded translation
//! (`tacenta-proofs/scripts/attest.py`), so a test-only edit there would make
//! all of them stale.

use rand_core::{CryptoRng, Error as RngError, RngCore};
use tacenta_core::primitives::{dh, kem, xeddsa};
use tacenta_core::serialization::{decode_initial, decode_message};
use tacenta_core::sessions::{
    Identity, LifecycleError, PreKeyBundle, PublishedBundle, Session, encode_ec, encode_kem,
    establish_initiator, establish_responder,
};

// ---------------------------------------------------------------------------
// A generator that says what it was asked for.
// ---------------------------------------------------------------------------

/// One step of SplitMix64: a well-mixed 64-bit value from a counter.
fn mix(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    x = (x ^ (x >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    x ^ (x >> 31)
}

/// Byte `index` of the deterministic stream named by `seed`.
fn stream_byte(seed: u64, index: u64) -> u8 {
    mix(mix(seed) ^ index) as u8
}

/// `len` bytes of the stream `seed`, starting at `from`.
fn stream(seed: u64, from: u64, len: usize) -> Vec<u8> {
    (0..len as u64)
        .map(|i| stream_byte(seed, from + i))
        .collect()
}

/// A deterministic byte stream that records the length of every request.
///
/// `calls` is the sequence of `fill_bytes` lengths (`next_u32` and `next_u64`
/// are routed through `fill_bytes`, so they show up as 4 and 8), and `pos`
/// counts the bytes handed out, so a request that is made and then ignored
/// still moves it.
struct Recording {
    seed: u64,
    start: u64,
    pos: u64,
    calls: Vec<usize>,
}

impl Recording {
    fn new(seed: u64) -> Self {
        Self::from_offset(seed, 0)
    }

    /// The same stream as `new(seed)`, joined at byte `offset`.
    fn from_offset(seed: u64, offset: u64) -> Self {
        Recording {
            seed,
            start: offset,
            pos: offset,
            calls: Vec::new(),
        }
    }

    fn consumed(&self) -> u64 {
        self.pos - self.start
    }

    /// The requests made since the last call to this, oldest first.
    fn take_calls(&mut self) -> Vec<usize> {
        std::mem::take(&mut self.calls)
    }
}

impl RngCore for Recording {
    fn next_u32(&mut self) -> u32 {
        let mut bytes = [0u8; 4];
        self.fill_bytes(&mut bytes);
        u32::from_le_bytes(bytes)
    }
    fn next_u64(&mut self) -> u64 {
        let mut bytes = [0u8; 8];
        self.fill_bytes(&mut bytes);
        u64::from_le_bytes(bytes)
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.calls.push(dest.len());
        for byte in dest.iter_mut() {
            *byte = stream_byte(self.seed, self.pos);
            self.pos += 1;
        }
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), RngError> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl CryptoRng for Recording {}

/// Serves a fixed byte string and records the requests. Asking for more than
/// it holds is a test failure, not a wrap-around.
struct Scripted {
    bytes: Vec<u8>,
    at: usize,
    calls: Vec<usize>,
}

impl Scripted {
    fn new(bytes: Vec<u8>) -> Self {
        Scripted {
            bytes,
            at: 0,
            calls: Vec::new(),
        }
    }
}

impl RngCore for Scripted {
    fn next_u32(&mut self) -> u32 {
        let mut bytes = [0u8; 4];
        self.fill_bytes(&mut bytes);
        u32::from_le_bytes(bytes)
    }
    fn next_u64(&mut self) -> u64 {
        let mut bytes = [0u8; 8];
        self.fill_bytes(&mut bytes);
        u64::from_le_bytes(bytes)
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.calls.push(dest.len());
        let end = self.at + dest.len();
        assert!(
            end <= self.bytes.len(),
            "asked for {} bytes at offset {} of a {}-byte script",
            dest.len(),
            self.at,
            self.bytes.len()
        );
        dest.copy_from_slice(&self.bytes[self.at..end]);
        self.at = end;
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), RngError> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl CryptoRng for Scripted {}

/// Serves every request in 32-byte pieces, in order, from the generator
/// underneath: the "two consecutive 32-byte stream entries" view of a longer
/// request.
struct InPiecesOf32<R>(R);

impl<R: RngCore> RngCore for InPiecesOf32<R> {
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }
    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        for piece in dest.chunks_mut(32) {
            self.0.fill_bytes(piece);
        }
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), RngError> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl<R: RngCore> CryptoRng for InPiecesOf32<R> {}

// ---------------------------------------------------------------------------
// ML-KEM-1024 keys, built and judged independently of the code under test.
// ---------------------------------------------------------------------------

/// FIPS 203's modulus.
const Q: u16 = 3329;
/// An ML-KEM-1024 encapsulation key: `ByteEncode12(t_hat)` (1,536 bytes) then
/// `rho` (32 bytes).
const EK_LEN: usize = 1568;
const T_HAT_LEN: usize = 1536;
const COEFFICIENTS: usize = 1024;

/// Twelve-bit values, two to every three bytes, low bits first: FIPS 203
/// Algorithm 5 with d = 12, without the reduction that makes a value canonical.
fn pack12(values: &[u16]) -> Vec<u8> {
    let mut out = Vec::with_capacity(values.len() / 2 * 3);
    for pair in values.chunks(2) {
        let (low, high) = (pair[0], pair[1]);
        assert!(low < 4096 && high < 4096);
        out.push((low & 0xff) as u8);
        out.push(((low >> 8) as u8) | (((high & 0x0f) as u8) << 4));
        out.push((high >> 4) as u8);
    }
    out
}

/// The inverse of `pack12`: FIPS 203 Algorithm 6 with d = 12, *before* the
/// reduction modulo q.
fn unpack12(bytes: &[u8]) -> Vec<u16> {
    let mut out = Vec::with_capacity(bytes.len() / 3 * 2);
    for triple in bytes.chunks(3) {
        let (b0, b1, b2) = (triple[0] as u16, triple[1] as u16, triple[2] as u16);
        out.push(b0 | ((b1 & 0x0f) << 8));
        out.push((b1 >> 4) | (b2 << 4));
    }
    out
}

/// FIPS 203 section 7.2, read from the text: the key is 1,568 bytes, and
/// `ByteEncode12(ByteDecode12(ek[0:1536]))` equals `ek[0:1536]`, where
/// `ByteDecode12` reduces each value modulo q. `rho` is not checked.
fn fips_203_accepts(ek: &[u8]) -> bool {
    if ek.len() != EK_LEN {
        return false;
    }
    let t_hat = &ek[..T_HAT_LEN];
    let reduced: Vec<u16> = unpack12(t_hat).iter().map(|c| c % Q).collect();
    pack12(&reduced) == t_hat
}

/// An honest key from the shipped generator, and the stream that made it.
fn honest_key(seed: u64) -> Vec<u8> {
    let mut rng = Recording::new(seed);
    let pair = kem::KeyPair::generate(&mut rng);
    assert_eq!(
        rng.take_calls(),
        [64],
        "key generation is one 64-byte request"
    );
    pair.public_key()
}

/// `honest` with coefficient `index` replaced by `value` and `rho` kept.
fn with_coefficient(honest: &[u8], index: usize, value: u16) -> Vec<u8> {
    let mut coefficients = unpack12(&honest[..T_HAT_LEN]);
    coefficients[index] = value;
    let mut key = pack12(&coefficients);
    key.extend_from_slice(&honest[T_HAT_LEN..]);
    key
}

/// A key with the given coefficients and `rho`.
fn key_of(coefficients: &[u16], rho: &[u8]) -> Vec<u8> {
    assert_eq!(coefficients.len(), COEFFICIENTS);
    let mut key = pack12(coefficients);
    key.extend_from_slice(rho);
    key
}

const SEED: u64 = 0x5eed;

/// The refusal is an `Err`, and the source was neither asked for a byte nor
/// moved.
fn assert_refused_before_the_rng(label: &str, key: &[u8]) {
    let mut rng = Recording::new(SEED);
    assert!(
        kem::encapsulate(key, &mut rng).is_err(),
        "{label}: a malformed key must be refused"
    );
    assert!(
        rng.calls.is_empty(),
        "{label}: refused, but the source was asked for {:?}",
        rng.calls
    );
    assert_eq!(rng.consumed(), 0, "{label}: refused, but the source moved");
}

// ---------------------------------------------------------------------------
// ML-KEM encapsulation
// ---------------------------------------------------------------------------

#[test]
fn a_malformed_key_is_refused_before_the_rng_is_touched() {
    let honest = honest_key(1);
    assert_eq!(honest.len(), EK_LEN);
    assert!(fips_203_accepts(&honest));

    // Length.
    assert_refused_before_the_rng("empty", &[]);
    assert_refused_before_the_rng("one byte", &[0]);
    assert_refused_before_the_rng("1567 bytes", &honest[..EK_LEN - 1]);
    let mut longer = honest.clone();
    longer.push(0);
    assert_refused_before_the_rng("1569 bytes", &longer);
    assert_refused_before_the_rng("two keys", &[honest.clone(), honest.clone()].concat());
    assert_refused_before_the_rng("all 0x00, 1567 bytes", &[0u8; EK_LEN - 1]);
    assert_refused_before_the_rng("all 0x00, 1569 bytes", &[0u8; EK_LEN + 1]);

    // A 12-bit value that is not below q, in any of the 1,024 positions (the
    // even and the odd positions pack differently) and at every such value.
    for index in 0..COEFFICIENTS {
        assert_refused_before_the_rng(
            &format!("coefficient {index} = q"),
            &with_coefficient(&honest, index, Q),
        );
    }
    for index in [0, 1, 510, 511, 1022, 1023] {
        for value in Q..4096 {
            assert_refused_before_the_rng(
                &format!("coefficient {index} = {value}"),
                &with_coefficient(&honest, index, value),
            );
        }
    }
    assert_refused_before_the_rng("all 0xFF", &[0xff; EK_LEN]);
}

#[test]
fn a_refusal_leaves_the_stream_where_it_was() {
    // The recorder's own count could be the thing that is wrong, so this also
    // reads the effect: after a refusal, the next use of the same generator
    // gets the bytes a fresh generator would have given it.
    let honest = honest_key(2);
    let mut fresh = Recording::new(SEED);
    let expected = kem::encapsulate(&honest, &mut fresh).unwrap();
    assert_eq!(fresh.take_calls(), [32]);

    let refused: Vec<(&str, Vec<u8>)> = vec![
        ("empty", Vec::new()),
        ("1567 bytes", honest[..EK_LEN - 1].to_vec()),
        ("coefficient 0 = q", with_coefficient(&honest, 0, Q)),
        (
            "coefficient 1023 = 4095",
            with_coefficient(&honest, 1023, 4095),
        ),
        ("all 0xFF", vec![0xff; EK_LEN]),
    ];
    for (label, key) in refused {
        let mut rng = Recording::new(SEED);
        assert!(kem::encapsulate(&key, &mut rng).is_err(), "{label}");
        let after = kem::encapsulate(&honest, &mut rng).unwrap();
        assert_eq!(after, expected, "{label}: the refusal moved the stream");
        assert_eq!(rng.take_calls(), [32], "{label}");
    }
}

#[test]
fn a_valid_key_is_never_refused_and_costs_one_32_byte_request() {
    for seed in 0..64u64 {
        let mut generator = Recording::new(seed);
        let pair = kem::KeyPair::generate(&mut generator);
        let key = pair.public_key();
        assert!(fips_203_accepts(&key), "seed {seed}");

        let mut rng = Recording::from_offset(seed ^ 0xa5a5, 1 << 20);
        let (ciphertext, sent) = kem::encapsulate(&key, &mut rng)
            .unwrap_or_else(|_| panic!("seed {seed}: a valid key was refused"));
        assert_eq!(rng.calls, [32], "seed {seed}");
        assert_eq!(rng.consumed(), 32, "seed {seed}");
        assert_eq!(ciphertext.len(), kem::ciphertext_len());
        assert_eq!(sent.len(), kem::SHARED_SECRET_LEN);
        assert_eq!(
            kem::decapsulate(&pair, &ciphertext),
            Ok(sent),
            "seed {seed}"
        );
    }
}

#[test]
fn keys_at_the_edge_of_the_valid_set_are_accepted() {
    // Section 7.2 checks the coefficients and nothing else. These are all in
    // the valid set, whatever else might be said of them: a stricter refusal
    // set than the specification's would lock out a key an honest peer can
    // publish.
    let honest = honest_key(3);
    let rho = &honest[T_HAT_LEN..];
    let top = vec![Q - 1; COEFFICIENTS];
    let mut alternating = vec![0u16; COEFFICIENTS];
    for (i, c) in alternating.iter_mut().enumerate() {
        *c = if i % 2 == 0 { Q - 1 } else { 0 };
    }
    let cases: Vec<(&str, Vec<u8>)> = vec![
        ("all bytes 0x00", vec![0u8; EK_LEN]),
        ("every coefficient q - 1", key_of(&top, rho)),
        ("alternating q - 1 and 0", key_of(&alternating, rho)),
        ("coefficient 0 = q - 1", with_coefficient(&honest, 0, Q - 1)),
        (
            "coefficient 1023 = q - 1",
            with_coefficient(&honest, 1023, Q - 1),
        ),
        (
            "rho all 0x00",
            key_of(&unpack12(&honest[..T_HAT_LEN]), &[0u8; 32]),
        ),
        (
            "rho all 0xFF",
            key_of(&unpack12(&honest[..T_HAT_LEN]), &[0xff; 32]),
        ),
        ("rho flipped", {
            let mut key = honest.clone();
            for byte in &mut key[T_HAT_LEN..] {
                *byte ^= 0xff;
            }
            key
        }),
    ];
    for (label, key) in cases {
        assert!(
            fips_203_accepts(&key),
            "{label}: the fixture is not in the valid set"
        );
        let mut rng = Recording::new(SEED);
        let result = kem::encapsulate(&key, &mut rng);
        assert!(result.is_ok(), "{label}: a valid key was refused");
        assert_eq!(rng.calls, [32], "{label}");
    }
}

/// A small xorshift, so the differential below is the same on every run.
struct Xorshift(u64);

impl Xorshift {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

#[test]
fn the_refusal_set_is_exactly_fips_203_section_7_2() {
    let mut random = Xorshift(0x1234_5678_9abc_def1);
    let (mut accepted, mut refused) = (0u32, 0u32);
    for round in 0..3000u32 {
        let mut coefficients: Vec<u16> = (0..COEFFICIENTS)
            .map(|_| (random.next() % Q as u64) as u16)
            .collect();
        // Zero, one or two coefficients pushed just below, onto or above q.
        for _ in 0..round % 3 {
            let index = (random.next() % COEFFICIENTS as u64) as usize;
            coefficients[index] = (Q - 2) + (random.next() % (4096 - (Q as u64 - 2))) as u16;
        }
        let rho: Vec<u8> = (0..32).map(|_| random.next() as u8).collect();
        let key = key_of(&coefficients, &rho);

        let mut rng = Recording::new(u64::from(round));
        let result = kem::encapsulate(&key, &mut rng);
        let expected = fips_203_accepts(&key);
        assert_eq!(result.is_ok(), expected, "round {round}");
        if expected {
            assert_eq!(rng.calls, [32], "round {round}");
            accepted += 1;
        } else {
            assert!(rng.calls.is_empty(), "round {round}: {:?}", rng.calls);
            refused += 1;
        }
    }
    // Both arms were exercised.
    assert!(accepted > 500, "only {accepted} accepted keys were tried");
    assert!(refused > 500, "only {refused} refused keys were tried");
}

#[test]
fn key_generation_is_one_64_byte_request() {
    // `tacenta-spec/protocol/session-establishment.md`: "A KEM prekey pair is
    // generated from 64 random bytes `d || z`".
    let mut rng = Recording::new(9);
    let _ = kem::KeyPair::generate(&mut rng);
    assert_eq!(rng.calls, [64]);
    assert_eq!(rng.consumed(), 64);
}

// ---------------------------------------------------------------------------
// XEdDSA signing
// ---------------------------------------------------------------------------

const SIGNING_SECRET: [u8; 32] = [7u8; 32];

#[test]
fn signing_is_one_64_byte_request_whatever_the_message() {
    for length in [0usize, 1, 32, 33, 1000] {
        let message = vec![0x42u8; length];
        let mut rng = Recording::new(SEED);
        let signature = xeddsa::sign(&SIGNING_SECRET, &message, &mut rng);
        assert_eq!(rng.calls, [64], "message of {length} bytes");
        assert_eq!(rng.consumed(), 64, "message of {length} bytes");
        let public = dh::PrivateKey::from_bytes(SIGNING_SECRET).public_key();
        assert!(xeddsa::verify(&public, &message, &signature).is_ok());
    }
}

#[test]
fn the_signature_depends_on_the_first_64_stream_bytes_and_no_others() {
    let message = b"message";
    let script = stream(SEED, 0, 96);
    let sign_with = |bytes: Vec<u8>| {
        let mut rng = Scripted::new(bytes);
        let signature = xeddsa::sign(&SIGNING_SECRET, message, &mut rng);
        (signature, rng.calls, rng.at)
    };
    let (baseline, calls, at) = sign_with(script.clone());
    assert_eq!(calls, [64]);
    assert_eq!(at, 64);

    for index in 0..64 {
        let mut changed = script.clone();
        changed[index] ^= 0x01;
        let (signature, _, _) = sign_with(changed);
        assert_ne!(signature, baseline, "stream byte {index} does not reach Z");
    }
    for index in 64..96 {
        let mut changed = script.clone();
        changed[index] ^= 0x01;
        let (signature, calls, at) = sign_with(changed);
        assert_eq!(
            signature, baseline,
            "stream byte {index} reached the signature"
        );
        assert_eq!((calls, at), (vec![64], 64));
    }
}

#[test]
fn a_64_byte_request_is_two_consecutive_32_byte_stream_entries() {
    // The same signature whether the source is asked once for 64 bytes or twice
    // for 32: `Z` is "the next 64 bytes of the stream", and how a generator
    // slices its output cannot change the value.
    let message = b"message";
    let mut whole = Recording::new(SEED);
    let from_whole = xeddsa::sign(&SIGNING_SECRET, message, &mut whole);
    assert_eq!(whole.calls, [64]);

    let mut pieces = InPiecesOf32(Recording::new(SEED));
    let from_pieces = xeddsa::sign(&SIGNING_SECRET, message, &mut pieces);
    assert_eq!(pieces.0.calls, [32, 32]);
    assert_eq!(from_whole, from_pieces);
}

// ---------------------------------------------------------------------------
// Sessions
// ---------------------------------------------------------------------------

struct Parties {
    alice: Identity,
    bob: Identity,
    alice_rng: Recording,
    bob_rng: Recording,
}

fn parties() -> Parties {
    let mut alice_rng = Recording::new(0xa11ce);
    let mut bob_rng = Recording::new(0xb0b);
    let alice = Identity::generate(&mut alice_rng);
    let bob = Identity::generate(&mut bob_rng);
    Parties {
        alice,
        bob,
        alice_rng,
        bob_rng,
    }
}

/// Every request an initiator makes to establish, in order and by value: the
/// ephemeral key, the encapsulation's `m`, the first ratchet key pair.
#[test]
fn establishing_as_initiator_draws_ephemeral_then_encapsulation_then_ratchet_key() {
    let mut p = parties();
    let store = p.bob.create_prekeys(1, &mut p.bob_rng);
    let published = store.publish();
    let seed = p.alice_rng.seed;
    let first = p.alice_rng.pos; // After the identity: everything below starts here.
    p.alice_rng.take_calls();

    let mut alice = establish_initiator(&p.alice, &published, &mut p.alice_rng).unwrap();
    assert_eq!(p.alice_rng.take_calls(), [32, 32, 32]);
    assert_eq!(p.alice_rng.pos - first, 96);

    // The values, to pin the order: they surface in the first message.
    let initial = alice.encrypt(b"hello", &mut p.alice_rng).unwrap();
    let decoded = decode_initial(&initial).unwrap();

    let ephemeral = dh::PrivateKey::from_bytes(stream(seed, first, 32).try_into().unwrap());
    assert_eq!(
        decoded.ephemeral,
        encode_ec(&ephemeral.public_key()),
        "the first request is the ephemeral key"
    );

    let mut m = Recording::from_offset(seed, first + 32);
    let (ciphertext, _) = kem::encapsulate(&published.bundle.kem_prekey, &mut m).unwrap();
    assert_eq!(m.calls, [32]);
    assert_eq!(
        decoded.kem_ciphertext, ciphertext,
        "the second request is the encapsulation's m"
    );

    let ratchet = dh::PrivateKey::from_bytes(stream(seed, first + 64, 32).try_into().unwrap());
    let message = decode_message(&decoded.message).unwrap();
    assert_eq!(
        &message.header.dh,
        ratchet.public_key().as_bytes(),
        "the third request is the first ratchet key"
    );
}

#[test]
fn the_initiators_first_send_is_one_64_byte_request_and_the_next_send_is_none() {
    // The Braid's key generation, `d || z`
    // (`tacenta-spec/protocol/mlkem-braid.md`, "Key generation draws 64 random
    // bytes"): the initiator's Braid starts by generating a key pair, so its
    // first send makes that request and nothing else.
    let mut p = parties();
    let store = p.bob.create_prekeys(1, &mut p.bob_rng);
    let published = store.publish();
    let mut alice = establish_initiator(&p.alice, &published, &mut p.alice_rng).unwrap();
    p.alice_rng.take_calls();
    let before = p.alice_rng.pos;

    alice.encrypt(b"one", &mut p.alice_rng).unwrap();
    assert_eq!(p.alice_rng.take_calls(), [64]);
    assert_eq!(p.alice_rng.pos - before, 64);

    // Until the peer answers there is nothing further to generate.
    alice.encrypt(b"two", &mut p.alice_rng).unwrap();
    assert_eq!(p.alice_rng.take_calls(), Vec::<usize>::new());
    alice.encrypt(b"three", &mut p.alice_rng).unwrap();
    assert_eq!(p.alice_rng.take_calls(), Vec::<usize>::new());
    assert_eq!(p.alice_rng.pos - before, 64);
}

/// A bundle that verifies (both signatures are the identity's own) and whose
/// KEM prekey is `kem_prekey`.
fn bundle_signing_kem_prekey(
    identity: &Identity,
    rng: &mut Recording,
    honest: &PublishedBundle,
    kem_prekey: Vec<u8>,
) -> PublishedBundle {
    let secret = identity.export();
    let signature = xeddsa::sign(&secret, &encode_kem(&kem_prekey), rng);
    PublishedBundle {
        bundle: PreKeyBundle {
            identity_key: honest.bundle.identity_key,
            signed_prekey: honest.bundle.signed_prekey,
            signed_prekey_signature: honest.bundle.signed_prekey_signature,
            kem_prekey,
            kem_prekey_signature: signature,
            one_time_prekey: honest.bundle.one_time_prekey,
        },
        signed_prekey_id: honest.signed_prekey_id,
        one_time_prekey_id: honest.one_time_prekey_id,
        kem_prekey_id: honest.kem_prekey_id,
    }
}

#[test]
fn a_signed_malformed_kem_prekey_is_refused_after_the_ephemeral_and_before_any_other_request() {
    // A key its owner signed is still refused if it is malformed, and the
    // refusal costs the one request that precedes it (the ephemeral key).
    let mut p = parties();
    let store = p.bob.create_prekeys(1, &mut p.bob_rng);
    let honest = store.publish();

    let malformed: Vec<(&str, Vec<u8>)> = vec![
        (
            "coefficient 0 = 4095",
            with_coefficient(&honest.bundle.kem_prekey, 0, 4095),
        ),
        (
            "coefficient 1023 = q",
            with_coefficient(&honest.bundle.kem_prekey, 1023, Q),
        ),
        (
            "1567 bytes",
            honest.bundle.kem_prekey[..EK_LEN - 1].to_vec(),
        ),
    ];
    for (label, kem_prekey) in malformed {
        let bad = bundle_signing_kem_prekey(&p.bob, &mut p.bob_rng, &honest, kem_prekey);
        p.alice_rng.take_calls();
        let before = p.alice_rng.pos;
        let refused = establish_initiator(&p.alice, &bad, &mut p.alice_rng);
        assert!(
            matches!(refused, Err(LifecycleError::Kem)),
            "{label}: expected the KEM refusal"
        );
        assert_eq!(p.alice_rng.take_calls(), [32], "{label}");
        assert_eq!(p.alice_rng.pos - before, 32, "{label}");
    }

    // And the honest bundle still establishes, on the same generator.
    assert!(establish_initiator(&p.alice, &honest, &mut p.alice_rng).is_ok());
}

/// What one operation asked of the generator.
type Footprint = Vec<usize>;

fn encrypt_footprint(session: &mut Session, rng: &mut Recording) -> (Vec<u8>, Footprint) {
    rng.take_calls();
    let message = session.encrypt(b"payload", rng).unwrap();
    (message, rng.take_calls())
}

fn decrypt_footprint(session: &mut Session, rng: &mut Recording, message: &[u8]) -> Footprint {
    rng.take_calls();
    session.decrypt(message, rng).unwrap();
    rng.take_calls()
}

#[test]
fn a_long_conversation_draws_only_the_specified_amounts_at_the_specified_moments() {
    let mut p = parties();
    let mut store = p.bob.create_prekeys(1, &mut p.bob_rng);
    let published = store.publish();
    let mut alice = establish_initiator(&p.alice, &published, &mut p.alice_rng).unwrap();

    let mut alice_sends: Vec<Footprint> = Vec::new();
    let mut bob_sends: Vec<Footprint> = Vec::new();
    let mut receives: Vec<Footprint> = Vec::new();

    let (first, footprint) = encrypt_footprint(&mut alice, &mut p.alice_rng);
    alice_sends.push(footprint);
    p.bob_rng.take_calls();
    let (mut bob, opened) =
        establish_responder(&p.bob, &mut store, &first, &mut p.bob_rng).unwrap();
    assert_eq!(opened, b"payload");
    // The responder's establishment decrypts the first message: one ratchet key.
    assert_eq!(p.bob_rng.take_calls(), [32]);

    // Sixty rounds: Bob sends twice and Alice replies once, so both sides send
    // and receive across several agreement epochs.
    for _ in 0..60 {
        for _ in 0..2 {
            let (message, footprint) = encrypt_footprint(&mut bob, &mut p.bob_rng);
            bob_sends.push(footprint);
            receives.push(decrypt_footprint(&mut alice, &mut p.alice_rng, &message));
        }
        let (message, footprint) = encrypt_footprint(&mut alice, &mut p.alice_rng);
        alice_sends.push(footprint);
        receives.push(decrypt_footprint(&mut bob, &mut p.bob_rng, &message));
    }

    // Every successful receive makes one request: the next ratchet key pair.
    assert!(
        receives.iter().all(|f| f == &[32]),
        "a receive asked for something other than one 32-byte key pair"
    );

    // A send asks for nothing, except where the Braid needs randomness: 64 bytes
    // to generate a key pair, 32 for the first half of an encapsulation.
    let non_empty = |sends: &[Footprint]| -> Vec<Footprint> {
        sends.iter().filter(|f| !f.is_empty()).cloned().collect()
    };
    // The initiator generates first and encapsulates when the roles turn; the
    // responder encapsulates first and generates when they turn back.
    assert_eq!(non_empty(&alice_sends), vec![vec![64], vec![32]]);
    assert_eq!(non_empty(&bob_sends), vec![vec![32], vec![64]]);
    // The first send is the key generation.
    assert_eq!(alice_sends[0], [64]);
    assert_eq!(alice_sends.len(), 61);
    assert_eq!(bob_sends.len(), 120);
}
