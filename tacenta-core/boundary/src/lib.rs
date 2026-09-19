#![forbid(unsafe_code)]

pub mod aead;
pub mod dh;
pub mod kem;
pub mod xeddsa;

pub mod kdf {
    pub use tacenta_kdf::*;
}

use rand_core::{CryptoRng, RngCore};

pub fn dh_public(private: &[u8; 32]) -> [u8; 32] {
    *dh::PrivateKey::from_bytes(*private).public_key().as_bytes()
}

pub fn dh_agree(private: &[u8; 32], peer: &[u8; 32]) -> Option<[u8; 32]> {
    dh::PrivateKey::from_bytes(*private).agree(&dh::PublicKeyBytes::from_bytes(*peer))
}

pub fn aead_seal(
    enc: &[u8; 32],
    mac: &[u8; 32],
    iv: &[u8; 16],
    plaintext: &[u8],
    ad: &[u8],
) -> Vec<u8> {
    aead::encrypt(enc, mac, iv, plaintext, ad)
}

pub fn aead_open(
    enc: &[u8; 32],
    mac: &[u8; 32],
    iv: &[u8; 16],
    ciphertext: &[u8],
    ad: &[u8],
) -> Option<Vec<u8>> {
    aead::decrypt(enc, mac, iv, ciphertext, ad).ok()
}

pub fn kem_encapsulate<R: RngCore + CryptoRng>(
    public_key: &[u8],
    rng: &mut R,
) -> Result<(Vec<u8>, [u8; 32]), kem::KemError> {
    kem::encapsulate(public_key, rng)
}

pub fn kem_decapsulate(pair: &kem::KeyPair, ciphertext: &[u8]) -> Result<[u8; 32], kem::KemError> {
    kem::decapsulate(pair, ciphertext)
}

pub fn xeddsa_verify(pk: &[u8; 32], message: &[u8], signature: &[u8; 64]) -> bool {
    xeddsa::verify(&dh::PublicKeyBytes::from_bytes(*pk), message, signature).is_ok()
}

pub fn xeddsa_sign<R: RngCore + CryptoRng>(
    secret: &[u8; 32],
    message: &[u8],
    rng: &mut R,
) -> [u8; 64] {
    xeddsa::sign(secret, message, rng)
}

pub fn random32<R: RngCore + CryptoRng>(rng: &mut R) -> [u8; 32] {
    let mut out = [0; 32];
    rng.fill_bytes(&mut out);
    out
}
