//! Differential tests of this crate against the RustCrypto implementation it
//! replaced: `hmac` 0.12.1 and `hkdf` 0.12.4 over `sha2` 0.10.9, the versions
//! the workspace lockfile pins, called the way the previous `src/lib.rs` called
//! them (`Hkdf::new(Some(salt), ikm).expand(info, out)` and
//! `Hmac::new_from_slice(key)`, `update`, `finalize`).
//!
//! Lengths are chosen to cross every boundary the copied code branches on:
//! SHA-256's 64-byte block and 56-byte padding threshold (reached here through
//! HMAC's inner and outer hashes and through a key longer than a block, which
//! HMAC hashes), HMAC's 64-byte key threshold, and HKDF's 32-byte output
//! blocks up to its 8160-byte bound, then the refusal one byte past it.
//!
//! What this is: agreement on a finite, seeded set of inputs. It is a test,
//! not a proof that the two implementations agree everywhere.

use hmac::{Hmac, Mac};
use sha2::Sha256;
use tacenta_kdf::{hkdf_sha256, hkdf_sha256_into, hmac_sha256};

/// xorshift64*, for reproducible inputs.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
}

fn ref_hmac(key: &[u8], data: &[u8]) -> [u8; 32] {
    let mut m = Hmac::<Sha256>::new_from_slice(key).unwrap();
    m.update(data);
    m.finalize().into_bytes().into()
}

fn ref_hkdf(salt: &[u8], ikm: &[u8], info: &[u8], out: &mut [u8]) {
    hkdf::Hkdf::<Sha256>::new(Some(salt), ikm)
        .expand(info, out)
        .unwrap();
}

/// Lengths `0..=max`, plus every multiple of `block` up to `far` and one
/// either side of it.
fn lengths(max: usize, block: usize, far: usize) -> Vec<usize> {
    let mut v: Vec<usize> = (0..=max).collect();
    let mut m = block;
    while m <= far {
        v.extend([m - 1, m, m + 1]);
        m += block;
    }
    v.sort();
    v.dedup();
    v
}

#[test]
fn hmac_agrees_across_key_and_data_lengths() {
    let mut rng = Rng(2);
    for key_len in lengths(200, 64, 512) {
        for data_len in [0, 1, 55, 56, 63, 64, 65, 119, 120, 128, rng.below(300)] {
            let (key, data) = (rng.bytes(key_len), rng.bytes(data_len));
            assert_eq!(
                hmac_sha256(&key, &data),
                ref_hmac(&key, &data),
                "key length {key_len}, data length {data_len}"
            );
        }
    }
}

#[test]
fn hkdf_agrees_up_to_the_bound() {
    let mut rng = Rng(3);
    let mut out_lens = lengths(300, 32, 8160);
    out_lens.retain(|&l| l <= 8160);
    for len in out_lens {
        let (sl, il, fl) = (rng.below(100), rng.below(100), rng.below(100));
        let (salt, ikm, info) = (rng.bytes(sl), rng.bytes(il), rng.bytes(fl));
        let mut ours = vec![0u8; len];
        hkdf_sha256_into(&salt, &ikm, &info, &mut ours);
        let mut theirs = vec![0u8; len];
        ref_hkdf(&salt, &ikm, &info, &mut theirs);
        assert_eq!(ours, theirs, "length {len}");
    }
}

#[test]
fn hkdf_fixed_width_agrees() {
    let mut rng = Rng(4);
    for _ in 0..200 {
        let (sl, il, fl) = (rng.below(80), rng.below(80), rng.below(80));
        let (salt, ikm, info) = (rng.bytes(sl), rng.bytes(il), rng.bytes(fl));
        let ours32: [u8; 32] = hkdf_sha256(&salt, &ikm, &info);
        let ours64: [u8; 64] = hkdf_sha256(&salt, &ikm, &info);
        let ours80: [u8; 80] = hkdf_sha256(&salt, &ikm, &info);
        let mut theirs = [0u8; 80];
        ref_hkdf(&salt, &ikm, &info, &mut theirs);
        assert_eq!(ours32[..], theirs[..32]);
        assert_eq!(ours64[..], theirs[..64]);
        assert_eq!(ours80[..], theirs[..]);
    }
}

/// One byte past RFC 5869's bound, both refuse, and this crate's panic carries
/// the text the previous `expect` produced (its message, then the `Debug` form
/// of RustCrypto's `InvalidLength`). The payload's type is not the same: the
/// previous `expect` panicked with a `String`, this crate's `assert!` with a
/// literal message panics with a `&'static str`, and the test holds the new
/// type so that a change of either is seen.
#[test]
fn hkdf_refuses_past_the_bound_with_the_same_message() {
    let mut theirs = vec![0u8; 8161];
    assert!(
        hkdf::Hkdf::<Sha256>::new(Some(b"s"), b"k")
            .expand(b"i", &mut theirs)
            .is_err()
    );
    let refused = std::panic::catch_unwind(|| {
        let mut ours = vec![0u8; 8161];
        hkdf_sha256_into(b"s", b"k", b"i", &mut ours);
    });
    let payload = refused.expect_err("8161 bytes must be refused");
    assert!(
        payload.downcast_ref::<String>().is_none(),
        "the payload is a String, as the previous expect's was"
    );
    let message = *payload
        .downcast_ref::<&'static str>()
        .expect("the payload is the assert's &'static str");
    let expected = format!(
        "HKDF output length is within the 255 * HashLen bound: {:?}",
        hkdf::InvalidLength
    );
    assert_eq!(message, expected);
}
