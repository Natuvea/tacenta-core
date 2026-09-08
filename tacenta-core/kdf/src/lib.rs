//! Key derivation: HKDF-SHA256 and HMAC-SHA256, the two derivations the Double
//! Ratchet uses (the root key derivation and the symmetric-key chain step).
//! Backed by RustCrypto's hkdf and hmac.

// No `unsafe` in this library crate, enforced by the attribute rather than
// observed; every library crate in the workspace carries it. The one `unsafe`
// block in the workspace is in `tacenta-core/tests/timing.rs`, which sets a CPU flag
// for measurement. The attribute bounds this crate only -- dependencies are
// the trusted boundary and are unaffected.
#![forbid(unsafe_code)]

use hkdf::Hkdf;
use hmac::{Hmac, Mac};
use sha2::Sha256;

/// HKDF-SHA256: fill `out` with derived key material from input keying material
/// `ikm`, salted by `salt` and bound to a context `info`. `out` must be at most
/// 255 * 32 bytes.
pub fn hkdf_sha256_into(salt: &[u8], ikm: &[u8], info: &[u8], out: &mut [u8]) {
    Hkdf::<Sha256>::new(Some(salt), ikm)
        .expand(info, out)
        .expect("HKDF output length is within the 255 * HashLen bound");
}

/// HKDF-SHA256 returning a fixed-size `[u8; N]`, the shape the protocol uses for
/// its fixed-width keys.
pub fn hkdf_sha256<const N: usize>(salt: &[u8], ikm: &[u8], info: &[u8]) -> [u8; N] {
    let mut out = [0u8; N];
    hkdf_sha256_into(salt, ikm, info, &mut out);
    out
}

/// HMAC-SHA256 of `data` under `key`.
pub fn hmac_sha256(key: &[u8], data: &[u8]) -> [u8; 32] {
    let mut mac = Hmac::<Sha256>::new_from_slice(key).expect("HMAC accepts a key of any length");
    mac.update(data);
    mac.finalize().into_bytes().into()
}

#[cfg(test)]
mod tests {
    use super::*;

    // RFC 5869, appendix A.1: the HKDF-SHA256 basic test case.
    #[test]
    fn hkdf_matches_rfc5869_case_1() {
        let ikm = [0x0b; 22];
        let salt: [u8; 13] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
        let info: [u8; 10] = [0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9];
        let okm = hkdf_sha256::<42>(&salt, &ikm, &info);
        let expected = hex::decode(
            "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865",
        )
        .unwrap();
        assert_eq!(&okm[..], &expected[..]);
    }

    // RFC 4231, test case 2: HMAC-SHA256, key "Jefe".
    #[test]
    fn hmac_matches_rfc4231_case_2() {
        let mac = hmac_sha256(b"Jefe", b"what do ya want for nothing?");
        let expected =
            hex::decode("5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843")
                .unwrap();
        assert_eq!(&mac[..], &expected[..]);
    }
}
