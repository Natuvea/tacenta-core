//! HMAC-SHA256 (FIPS 198-1 §4; RFC 2104 §2), for keys of any length, with
//! the full 32-byte output.
//!
//! `HMAC(K, text) = H((K0 ⊕ opad) ‖ H((K0 ⊕ ipad) ‖ text))`, where `K0` is
//! `K` padded with zeros to the 64-byte block, or `H(K)` padded the same way
//! when `K` is longer than the block (FIPS 198-1 §4, steps 1–3).
//!
//! Incremental over `text`, like `sha256::Sha256`, so the AEAD's tag over
//! `ad ‖ ciphertext` and HKDF's `T(i-1) ‖ info ‖ i` are hashed without being
//! built. The only branch on the key is on its length.

use super::sha256::{sha256, Sha256};

/// The block size `B` of SHA-256, in bytes.
const BLOCK: usize = 64;

/// An incremental HMAC-SHA256 computation: the inner hash, already fed
/// `K0 ⊕ ipad`, and the outer block `K0 ⊕ opad`.
#[derive(Clone, Copy)]
pub(crate) struct HmacSha256 {
    inner: Sha256,
    outer_block: [u8; BLOCK],
}

impl HmacSha256 {
    /// Steps 1–5 of FIPS 198-1 §4: derive `K0`, and start the inner hash
    /// on `K0 ⊕ ipad`.
    pub(crate) fn new(key: &[u8]) -> HmacSha256 {
        let mut k0 = [0u8; BLOCK];
        if key.len() > BLOCK {
            let hashed = sha256(key);
            let mut i = 0;
            while i < 32 {
                k0[i] = hashed[i];
                i += 1;
            }
        } else {
            let mut i = 0;
            while i < key.len() {
                k0[i] = key[i];
                i += 1;
            }
        }
        let mut inner_block = [0u8; BLOCK];
        let mut outer_block = [0u8; BLOCK];
        let mut i = 0;
        while i < BLOCK {
            inner_block[i] = k0[i] ^ 0x36;
            outer_block[i] = k0[i] ^ 0x5c;
            i += 1;
        }
        let mut inner = Sha256::new();
        inner.update(&inner_block);
        HmacSha256 { inner, outer_block }
    }

    /// Append to `text` (step 6's input).
    pub(crate) fn update(&mut self, data: &[u8]) {
        self.inner.update(data);
    }

    /// Steps 6–9: finish the inner hash, then hash `(K0 ⊕ opad) ‖` it.
    pub(crate) fn finalize(&self) -> [u8; 32] {
        let inner_hash = self.inner.finalize();
        let mut outer = Sha256::new();
        outer.update(&self.outer_block);
        outer.update(&inner_hash);
        outer.finalize()
    }
}

/// HMAC-SHA256 of `data` under `key`: `tacenta-kdf`'s `hmac_sha256`.
pub fn hmac_sha256(key: &[u8], data: &[u8]) -> [u8; 32] {
    let mut m = HmacSha256::new(key);
    m.update(data);
    m.finalize()
}
