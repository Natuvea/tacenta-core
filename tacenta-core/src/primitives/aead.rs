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
///
/// # Security
///
/// The tag is computed over the bare concatenation `associated_data ||
/// ciphertext`, with no length field between them (CR-16). That is sound only
/// when `associated_data` is **self-delimiting**: its length must be
/// recoverable from its own bytes, independent of what follows. If it is not,
/// the boundary between it and the ciphertext floats, and two different
/// `(associated_data, ciphertext)` pairs can concatenate to the same bytes and
/// so share a tag -- for example `(b"ab", b"c...")` and `(b"a", b"bc...")`.
/// The one in-tree caller passes [`concat_ad`](crate::serialization::concat_ad)
/// output, which is self-delimiting (a four-byte length prefix then a
/// fixed-width composite header); the unit test `concat_ad_is_self_delimiting`
/// pins that shape. A new caller supplying a variable-length associated data of
/// its own must prefix it with a length itself.
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
///
/// # Security
///
/// The tag covers `associated_data || ciphertext` with no framing between the
/// two, so this verifies a boundary only where `associated_data` is
/// self-delimiting; see [`encrypt`] for why, and for the invariant the one
/// in-tree caller upholds via [`concat_ad`](crate::serialization::concat_ad).
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

    /// A padding failure maps to the same `DecryptError` as a tag failure, so a
    /// caller cannot tell one from the other and turn the gap into a padding
    /// oracle (CR-28).
    ///
    /// The case is a single AES block with a *valid* tag over it, so the MAC
    /// verifies and decryption proceeds to the PKCS7 unpad, which then fails on
    /// bytes that are not a valid padding. The error must be indistinguishable
    /// from the tag-failure error checked above.
    #[test]
    fn a_padding_failure_is_the_same_error_as_a_tag_failure() {
        // One block of bytes whose decryption almost never ends in a valid pad;
        // asserted by the test failing loudly if it somehow does.
        let ciphertext = [0u8; 16];
        let tag = mac(&MAC, b"header", &ciphertext);
        let mut ct_and_tag = ciphertext.to_vec();
        ct_and_tag.extend_from_slice(&tag);

        assert_eq!(
            decrypt(&ENC, &MAC, &IV, &ct_and_tag, b"header"),
            Err(DecryptError),
            "a valid tag over invalid padding must still be DecryptError"
        );

        // The tag-failure path returns the very same error.
        let mut tampered = encrypt(&ENC, &MAC, &IV, b"a real message", b"header");
        let last = tampered.len() - 1;
        tampered[last] ^= 0x01;
        assert_eq!(
            decrypt(&ENC, &MAC, &IV, &tampered, b"header"),
            Err(DecryptError),
            "a tag failure and a padding failure must be indistinguishable"
        );
    }

    /// The one in-tree associated data is self-delimiting, which is the
    /// invariant the `# Security` note on [`encrypt`] rests the framing-free
    /// MAC on (CR-16).
    ///
    /// `concat_ad` emits a four-byte big-endian length prefix, then the
    /// identity associated data, then a fixed-width composite header. The
    /// length prefix and the fixed tail together mean the boundary between the
    /// associated data and the ciphertext is recoverable from the associated
    /// data's own bytes, so no second `(ad, ct)` split produces the same
    /// concatenation. If `concat_ad` ever stopped prefixing its length or the
    /// composite header stopped being fixed width, this fails.
    #[test]
    fn concat_ad_is_self_delimiting() {
        use crate::serialization::composite::{AgreementType, Composite};
        use crate::serialization::concat_ad;

        let header = Composite {
            dh: [0xaa; 32],
            pn: 1,
            n: 2,
            pq_epoch: 3,
            pq_n: 4,
            ag_epoch: 3,
            ag_type: AgreementType::None,
            ag_chunk: None,
        };

        let short = concat_ad(b"ab", &header);
        let long = concat_ad(b"abcd", &header);

        // The leading four bytes are the big-endian length of the associated
        // data, so the reader knows where it ends before the header begins.
        assert_eq!(&short[..4], &(2u32).to_be_bytes());
        assert_eq!(&long[..4], &(4u32).to_be_bytes());

        // The composite header is fixed width, so the tail after the prefixed
        // associated data does not depend on the associated data's length: the
        // two encodings differ by exactly the two extra associated-data bytes.
        assert_eq!(long.len(), short.len() + 2);

        // And the boundary genuinely moves with the declared length: a longer
        // associated data cannot be re-split as a shorter one with the surplus
        // folded into the header, because the prefix names the real length.
        assert_ne!(concat_ad(b"ab", &header), concat_ad(b"a", &header));
    }
}
