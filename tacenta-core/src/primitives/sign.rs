//! Ed25519 signatures. Identity signatures are XEdDSA (ADR-0002, the xeddsa
//! module); this module is the plain Ed25519 primitive that backs XEdDSA's
//! verification and remains available as a general building block. Backed by
//! ed25519-dalek.

use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use rand_core::{CryptoRng, RngCore};

/// An Ed25519 signing (private) key. Zeroized on drop by the underlying
/// `SigningKey`.
pub struct SigningKeyPair(SigningKey);

/// An Ed25519 verifying (public) key: 32 bytes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct VerifyingKeyBytes([u8; 32]);

/// Signature verification failed, or the public key bytes do not encode a
/// valid key.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct VerifyError;

impl SigningKeyPair {
    /// Generate a fresh signing key from a cryptographic RNG.
    pub fn generate<R: RngCore + CryptoRng>(rng: &mut R) -> SigningKeyPair {
        SigningKeyPair(SigningKey::generate(rng))
    }

    /// Reconstruct a signing key from its 32 secret bytes.
    pub fn from_bytes(bytes: [u8; 32]) -> SigningKeyPair {
        SigningKeyPair(SigningKey::from_bytes(&bytes))
    }

    /// The matching public key.
    pub fn verifying_key(&self) -> VerifyingKeyBytes {
        VerifyingKeyBytes(self.0.verifying_key().to_bytes())
    }

    /// Sign a message: a 64-byte Ed25519 signature.
    pub fn sign(&self, message: &[u8]) -> [u8; 64] {
        self.0.sign(message).to_bytes()
    }
}

impl VerifyingKeyBytes {
    pub fn from_bytes(bytes: [u8; 32]) -> VerifyingKeyBytes {
        VerifyingKeyBytes(bytes)
    }

    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// Verify `signature` over `message` under this key.
    ///
    /// `verify_strict`, matching the XEdDSA path: it refuses a small-order
    /// public key or nonce point and a non-canonical encoding, which the
    /// plain cofactorless `verify` accepts. Nothing in the core calls this
    /// today; it is kept strict so that a future caller cannot pick up the
    /// weaker verifier by reaching for the shorter name.
    pub fn verify(&self, message: &[u8], signature: &[u8; 64]) -> Result<(), VerifyError> {
        let key = VerifyingKey::from_bytes(&self.0).map_err(|_| VerifyError)?;
        key.verify_strict(message, &Signature::from_bytes(signature))
            .map_err(|_| VerifyError)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // RFC 8032, section 7.1, test 1: empty message.
    #[test]
    fn matches_rfc8032_test_1() {
        let secret: [u8; 32] =
            hex::decode("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
                .unwrap()
                .try_into()
                .unwrap();
        let pair = SigningKeyPair::from_bytes(secret);
        assert_eq!(
            hex::encode(pair.verifying_key().as_bytes()),
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
        );
        let sig = pair.sign(b"");
        assert_eq!(
            hex::encode(sig),
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
        );
        assert!(pair.verifying_key().verify(b"", &sig).is_ok());
    }

    #[test]
    fn a_signature_verifies_and_a_forgery_does_not() {
        let pair = SigningKeyPair::from_bytes([5u8; 32]);
        let sig = pair.sign(b"bind this prekey");
        assert!(
            pair.verifying_key()
                .verify(b"bind this prekey", &sig)
                .is_ok()
        );
        assert_eq!(
            pair.verifying_key().verify(b"bind another prekey", &sig),
            Err(VerifyError),
        );
        let other = SigningKeyPair::from_bytes([6u8; 32]);
        assert_eq!(
            other.verifying_key().verify(b"bind this prekey", &sig),
            Err(VerifyError),
        );
    }
}
