//! HKDF-SHA256 (RFC 5869 §2), and `tacenta-kdf`'s two wrappers over it.
//!
//! `PRK = HMAC(salt, IKM)` (§2.2), then `T(0)` empty,
//! `T(i) = HMAC(PRK, T(i-1) ‖ info ‖ i)` for `i = 1 … ⌈L/32⌉`, and the
//! output is the first `L` bytes of `T(1) ‖ T(2) ‖ …` (§2.3), for
//! `L ≤ 255 · 32`.
//!
//! The salt is always given. `tacenta-kdf` passes `Some(salt)` to
//! RustCrypto's `Hkdf::new`. An empty salt is then HMAC's empty key, which
//! pads to the same `K0` as §2.2's default of 32 zero bytes, so the two
//! agree.

use super::hmac::HmacSha256;

/// `HashLen` for SHA-256.
const HASH_LEN: usize = 32;

/// RFC 5869's bound on `L`, `255 · HashLen`.
pub const MAX_OUTPUT_LEN: usize = 255 * HASH_LEN;

/// HKDF-Extract (§2.2).
fn extract(salt: &[u8], ikm: &[u8]) -> [u8; HASH_LEN] {
    let mut m = HmacSha256::new(salt);
    m.update(ikm);
    m.finalize()
}

/// HKDF-Expand (§2.3), filling all of `out`. Requires
/// `out.len() <= MAX_OUTPUT_LEN`, so the counter fits in a byte.
fn expand(prk: &[u8; HASH_LEN], info: &[u8], out: &mut [u8]) {
    let mut t = [0u8; HASH_LEN];
    let mut pos = 0;
    let mut i: u8 = 1;
    while pos < out.len() {
        let mut m = HmacSha256::new(prk);
        if i > 1 {
            m.update(&t);
        }
        m.update(info);
        m.update(&[i]);
        t = m.finalize();
        let mut j = 0;
        while j < HASH_LEN && pos < out.len() {
            out[pos] = t[j];
            pos += 1;
            j += 1;
        }
        if pos < out.len() {
            i += 1;
        }
    }
}

/// HKDF-SHA256: fill `out` with key material derived from `ikm`, salted by
/// `salt`, bound to `info`. Panics if `out.len() > 255 * 32`, as
/// `tacenta-kdf`'s `hkdf_sha256_into` does.
pub fn hkdf_sha256_into(salt: &[u8], ikm: &[u8], info: &[u8], out: &mut [u8]) {
    // The message is `tacenta-kdf`'s `expect` message followed by the
    // `Debug` form of RustCrypto's `InvalidLength`, which `expect` appends, so
    // the panic is byte-identical.
    assert!(out.len() <= MAX_OUTPUT_LEN, "HKDF output length is within the 255 * HashLen bound: InvalidLength");
    let prk = extract(salt, ikm);
    expand(&prk, info, out);
}

/// HKDF-SHA256 returning `[u8; N]`, as `tacenta-kdf`'s `hkdf_sha256`.
pub fn hkdf_sha256<const N: usize>(salt: &[u8], ikm: &[u8], info: &[u8]) -> [u8; N] {
    let mut out = [0u8; N];
    hkdf_sha256_into(salt, ikm, info, &mut out);
    out
}
