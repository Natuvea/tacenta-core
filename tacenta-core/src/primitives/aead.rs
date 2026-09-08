//! Authenticated encryption: AES-256-CBC with HMAC-SHA256, encrypt-then-MAC.
//! This is the composition the Double Ratchet specification recommends for its
//! ENCRYPT function; the key and IV derivation that feeds it is part of the
//! ratchet slice, so this module takes explicit keys. Backed by RustCrypto's
//! aes, cbc, and hmac.

use aes::Aes256;
use aes::cipher::{BlockDecryptMut, BlockEncryptMut, KeyIvInit, block_padding::Pkcs7};

use super::kdf::hmac_sha256;

type CbcEnc = cbc::Encryptor<Aes256>;
type CbcDec = cbc::Decryptor<Aes256>;

/// Decryption failed: the tag did not verify, or the padding was invalid. One
/// coarse error on purpose, so a caller cannot distinguish tag failures from
/// padding failures and turn the difference into an oracle.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DecryptError;

/// Encrypt `plaintext` under `enc_key`/`iv` with AES-256-CBC (PKCS7), then MAC
/// `associated_data || ciphertext` under `mac_key` with HMAC-SHA256. Returns
/// `ciphertext || tag` with the full 32-byte tag appended.
pub fn encrypt(
    enc_key: &[u8; 32],
    mac_key: &[u8; 32],
    iv: &[u8; 16],
    plaintext: &[u8],
    associated_data: &[u8],
) -> Vec<u8> {
    let mut out = CbcEnc::new(enc_key.into(), iv.into()).encrypt_padded_vec_mut::<Pkcs7>(plaintext);
    let tag = mac(mac_key, associated_data, &out);
    out.extend_from_slice(&tag);
    out
}

/// Verify the tag over `associated_data || ciphertext`, then decrypt. Returns
/// the plaintext, or [`DecryptError`] if the tag or the padding is wrong.
pub fn decrypt(
    enc_key: &[u8; 32],
    mac_key: &[u8; 32],
    iv: &[u8; 16],
    ciphertext_and_tag: &[u8],
    associated_data: &[u8],
) -> Result<Vec<u8>, DecryptError> {
    if ciphertext_and_tag.len() < 32 {
        return Err(DecryptError);
    }
    let (ciphertext, tag) = ciphertext_and_tag.split_at(ciphertext_and_tag.len() - 32);

    // Constant-time tag comparison, via the Mac verify machinery.
    use hmac::{Hmac, Mac};
    use sha2::Sha256;
    let mut m = Hmac::<Sha256>::new_from_slice(mac_key).expect("HMAC accepts any key length");
    m.update(associated_data);
    m.update(ciphertext);
    m.verify_slice(tag).map_err(|_| DecryptError)?;

    CbcDec::new(enc_key.into(), iv.into())
        .decrypt_padded_vec_mut::<Pkcs7>(ciphertext)
        .map_err(|_| DecryptError)
}

fn mac(mac_key: &[u8; 32], associated_data: &[u8], ciphertext: &[u8]) -> [u8; 32] {
    let mut data = Vec::with_capacity(associated_data.len() + ciphertext.len());
    data.extend_from_slice(associated_data);
    data.extend_from_slice(ciphertext);
    hmac_sha256(mac_key, &data)
}

#[cfg(test)]
mod tests {
    use super::*;

    const ENC: [u8; 32] = [1u8; 32];
    const MAC: [u8; 32] = [2u8; 32];
    const IV: [u8; 16] = [3u8; 16];

    // NIST SP 800-38A, F.2.5 (CBC-AES256.Encrypt), first block: with the NIST
    // key, IV, and plaintext block, the first ciphertext block must match. The
    // remainder of our output is PKCS7 padding, which NIST's unpadded vector
    // does not cover.
    #[test]
    fn cbc_core_matches_nist_sp800_38a() {
        let key: [u8; 32] =
            hex::decode("603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4")
                .unwrap()
                .try_into()
                .unwrap();
        let iv: [u8; 16] = hex::decode("000102030405060708090a0b0c0d0e0f")
            .unwrap()
            .try_into()
            .unwrap();
        let pt = hex::decode("6bc1bee22e409f96e93d7e117393172a").unwrap();
        let out = encrypt(&key, &MAC, &iv, &pt, b"");
        assert_eq!(
            hex::encode(&out[..16]),
            "f58c4c04d6e5f1ba779eabfb5f7bfbd6",
            "first CBC block matches the NIST vector"
        );
    }

    #[test]
    fn round_trips_with_associated_data() {
        let ct = encrypt(&ENC, &MAC, &IV, b"a secret message", b"header");
        let pt = decrypt(&ENC, &MAC, &IV, &ct, b"header").unwrap();
        assert_eq!(pt, b"a secret message");
    }

    #[test]
    fn a_tampered_ciphertext_is_rejected() {
        let mut ct = encrypt(&ENC, &MAC, &IV, b"a secret message", b"header");
        ct[0] ^= 1;
        assert_eq!(decrypt(&ENC, &MAC, &IV, &ct, b"header"), Err(DecryptError));
    }

    #[test]
    fn a_tampered_tag_is_rejected() {
        let mut ct = encrypt(&ENC, &MAC, &IV, b"a secret message", b"header");
        let last = ct.len() - 1;
        ct[last] ^= 1;
        assert_eq!(decrypt(&ENC, &MAC, &IV, &ct, b"header"), Err(DecryptError));
    }

    #[test]
    fn the_wrong_associated_data_is_rejected() {
        let ct = encrypt(&ENC, &MAC, &IV, b"a secret message", b"header");
        assert_eq!(decrypt(&ENC, &MAC, &IV, &ct, b"other"), Err(DecryptError));
    }

    #[test]
    fn a_truncated_input_is_rejected() {
        assert_eq!(decrypt(&ENC, &MAC, &IV, &[0u8; 31], b""), Err(DecryptError));
    }
}
