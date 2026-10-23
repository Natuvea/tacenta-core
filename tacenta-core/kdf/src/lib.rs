//! Key derivation: HKDF-SHA256 and HMAC-SHA256, the two derivations the Double
//! Ratchet uses (the root key derivation and the symmetric-key chain step).
//!
//! # Where the bodies come from
//!
//! The three modules below are copied from an independent verified
//! implementation of SHA-256, HMAC-SHA256 and HKDF-SHA256, written from FIPS
//! 180-4, FIPS 198-1 and RFC 5869 in the subset Charon and Aeneas translate.
//! `sha256.rs` is byte-identical to its source; `hmac.rs` and `hkdf.rs` differ
//! from theirs in one line each, the `use` of the sibling module
//! (`crate::sha256` and `crate::hmac` there, `super::sha256` and
//! `super::hmac` here). Nothing else was edited, and `rustfmt` is told to
//! leave the three files alone so that they stay comparable with their source
//! byte for byte. Their doc comments are the source's own, so a reference
//! there to `PLAN.md`, to `tests/sha256.rs` or to a constant-time requirement
//! names a file of the source repository, not of this one. The source is
//! that repository's commit `646fcdadb943`, whose three files have the SHA-256
//! digests
//!
//! - `sha256.rs`: `57512dd5218b1fb9d80f69ca9613b9f1a7dfa3e1ba64d8873c0a31de70c9fd6e`
//! - `hmac.rs`: `de0076540c2636bbe8f373f2b0a137ced5e926d6c1f4ed907184ce6519d893c0`
//! - `hkdf.rs`: `1351a9a22bec00583c2e39cd6af313094a1c9763da1d2ecb75cfe45592cca2b7`
//!
//! The source crate is `#![no_std]`; these three files use nothing from `std`
//! or `alloc`, so they compile unchanged here.
//!
//! What that buys: the Session unit's translation includes these bodies
//! (Charon's `--include 'tacenta_kdf'`), and `tacenta-proofs` proves that the
//! translated `hmac_sha256` and `hkdf_sha256` return, and equal
//! tacenta-model's `Model.Kdf.hmac` and `Model.Kdf.hkdf` (HKDF for outputs of
//! at most 8160 bytes). `tacenta-proofs/CLAIMS.md` names the theorems and
//! what they rest on; `LIMITATIONS.md` says what they do not establish (the
//! model is checked against RFC 4231 and RFC 5869 by vectors, not proved to
//! be them, and nothing here is a PRF or side-channel property).
//!
//! What it costs: these bodies are about 1.5 to 2.1 times slower than the
//! RustCrypto crates they replace, measured on SHA-256, HMAC and HKDF by the
//! source repository and not re-measured here. Intermediate values are not
//! erased, as RustCrypto's were not either with the features this crate
//! enabled.
//!
//! Not every SHA-256 or HMAC in the workspace moved: the AEAD's tag check on
//! decryption (`boundary/src/aead.rs`) and the identity and group digests in
//! the root crate still call RustCrypto directly.

// No `unsafe` in this library crate, enforced by the attribute rather than
// observed; every library crate in the workspace carries it. The one `unsafe`
// block in the workspace is in `tacenta-core/tests/timing.rs`, which sets a CPU flag
// for measurement.
#![forbid(unsafe_code)]

#[rustfmt::skip]
mod hkdf;
#[rustfmt::skip]
mod hmac;
#[rustfmt::skip]
mod sha256;

/// HKDF-SHA256: fill `out` with derived key material from input keying material
/// `ikm`, salted by `salt` and bound to a context `info`. `out` must be at most
/// 255 * 32 bytes.
///
/// A wrapper rather than a re-export, so that the translation names it
/// `tacenta_kdf.hkdf_sha256_into` as before.
pub fn hkdf_sha256_into(salt: &[u8], ikm: &[u8], info: &[u8], out: &mut [u8]) {
    hkdf::hkdf_sha256_into(salt, ikm, info, out)
}

/// HKDF-SHA256 returning a fixed-size `[u8; N]`, the shape the protocol uses for
/// its fixed-width keys.
pub fn hkdf_sha256<const N: usize>(salt: &[u8], ikm: &[u8], info: &[u8]) -> [u8; N] {
    hkdf::hkdf_sha256::<N>(salt, ikm, info)
}

/// HMAC-SHA256 of `data` under `key`.
pub fn hmac_sha256(key: &[u8], data: &[u8]) -> [u8; 32] {
    hmac::hmac_sha256(key, data)
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
