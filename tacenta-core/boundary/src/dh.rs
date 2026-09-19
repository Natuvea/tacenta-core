//! X25519 Diffie-Hellman, the key-agreement primitive the Double Ratchet
//! composes. Backed by x25519-dalek.

use rand_core::{CryptoRng, RngCore};
use x25519_dalek::{PublicKey, StaticSecret};
use zeroize::Zeroizing;

/// An X25519 private key. Its bytes are zeroized on drop by the underlying
/// `StaticSecret`.
pub struct PrivateKey(StaticSecret);

/// An X25519 public key: 32 bytes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PublicKeyBytes([u8; 32]);

impl PrivateKey {
    /// Generate a fresh key pair from a cryptographic RNG.
    pub fn generate<R: RngCore + CryptoRng>(rng: &mut R) -> PrivateKey {
        PrivateKey(StaticSecret::random_from_rng(rng))
    }

    /// Reconstruct a private key from its 32 bytes, for a caller restoring a key
    /// it stored. X25519 clamps the scalar on use.
    pub fn from_bytes(bytes: [u8; 32]) -> PrivateKey {
        PrivateKey(StaticSecret::from(bytes))
    }

    /// The matching public key.
    pub fn public_key(&self) -> PublicKeyBytes {
        PublicKeyBytes(PublicKey::from(&self.0).to_bytes())
    }

    /// The Diffie-Hellman shared secret with a peer's public key: the `DH(...)`
    /// the ratchet feeds into the root key derivation.
    /// Agree with `peer`, or `None` if the peer's key is one that forces the
    /// result.
    ///
    /// **Why this is fallible.** X25519 has a small subgroup, and a peer who
    /// sends one of its low-order points makes the shared secret all-zero
    /// whatever our private key is. Returning those bytes means both sides
    /// "agree" on a value the peer chose alone, so every key derived from it
    /// is the peer's to predict. RFC 7748 §6.1 names the check and leaves
    /// taking it to the protocol.
    ///
    /// Rejecting here, rather than leaving it to callers, means no caller has
    /// to carry the argument that every current and future calling
    /// construction makes an all-zero secret harmless.
    ///
    /// `was_contributory` is x25519-dalek's name for it: an agreement is
    /// contributory when both parties' keys actually contributed to the
    /// result.
    pub fn agree(&self, peer: &PublicKeyBytes) -> Option<[u8; 32]> {
        let shared = self.0.diffie_hellman(&PublicKey::from(peer.0));
        if !shared.was_contributory() {
            return None;
        }
        Some(shared.to_bytes())
    }

    /// This key's raw 32 bytes, for a caller persisting a session. Mirrors
    /// `Identity::export`: the wrapped `StaticSecret` already zeroizes its own
    /// resident bytes on drop (per this crate's `zeroize` feature), and this
    /// wraps the returned copy the same way.
    pub fn to_bytes(&self) -> Zeroizing<[u8; 32]> {
        Zeroizing::new(self.0.to_bytes())
    }
}

impl PublicKeyBytes {
    pub fn from_bytes(bytes: [u8; 32]) -> PublicKeyBytes {
        PublicKeyBytes(bytes)
    }

    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Low-order peer keys are refused rather than agreed with.
    ///
    /// Each value below forces the shared secret to all-zero whatever our
    /// private key is, so accepting one means deriving every session key from
    /// a value the peer chose alone.
    ///
    /// The three large encodings are *derived*, not copied from a table: with
    /// p = 2^255 - 19, they are p-1, p and p+1 written little-endian, which is
    /// why the leading bytes run ec/ed/ee and the last is 0x7f. Deriving them
    /// is the point -- a memorised table of low-order points is a thing a test
    /// can get subtly wrong while still passing.
    #[test]
    fn low_order_peer_keys_are_rejected() {
        let mut rng = rand_core::OsRng;
        let ours = PrivateKey::generate(&mut rng);

        let mut p_minus_1 = [0xffu8; 32];
        p_minus_1[0] = 0xec;
        p_minus_1[31] = 0x7f;
        let mut p_bytes = [0xffu8; 32];
        p_bytes[0] = 0xed;
        p_bytes[31] = 0x7f;
        let mut p_plus_1 = [0xffu8; 32];
        p_plus_1[0] = 0xee;
        p_plus_1[31] = 0x7f;

        let mut u_one = [0u8; 32];
        u_one[0] = 1;

        for (name, bytes) in [
            ("u = 0", [0u8; 32]),
            ("u = 1", u_one),
            ("p - 1", p_minus_1),
            ("p", p_bytes),
            ("p + 1", p_plus_1),
        ] {
            assert!(
                ours.agree(&PublicKeyBytes::from_bytes(bytes)).is_none(),
                "{name} was accepted as a peer key"
            );
        }
    }

    #[test]
    fn two_parties_agree_on_the_same_shared_secret() {
        // Deterministic keys so the test is reproducible.
        let alice = PrivateKey::from_bytes([7u8; 32]);
        let bob = PrivateKey::from_bytes([9u8; 32]);

        let ab = alice
            .agree(&bob.public_key())
            .expect("test keys are not low-order");
        let ba = bob
            .agree(&alice.public_key())
            .expect("test keys are not low-order");
        assert_eq!(ab, ba, "DH is symmetric");
        assert_ne!(ab, [0u8; 32], "the shared secret is not trivially zero");
    }

    #[test]
    fn generated_keys_agree() {
        use rand::rngs::OsRng;
        let a = PrivateKey::generate(&mut OsRng);
        let b = PrivateKey::generate(&mut OsRng);
        assert_eq!(
            a.agree(&b.public_key())
                .expect("test keys are not low-order"),
            b.agree(&a.public_key())
                .expect("test keys are not low-order")
        );
    }

    #[test]
    fn a_public_key_round_trips_through_its_bytes() {
        let k = PrivateKey::from_bytes([3u8; 32]).public_key();
        assert_eq!(PublicKeyBytes::from_bytes(*k.as_bytes()), k);
    }

    #[test]
    fn a_private_key_round_trips_through_to_bytes() {
        let original = PrivateKey::from_bytes([5u8; 32]);
        let restored = PrivateKey::from_bytes(*original.to_bytes());
        assert_eq!(restored.public_key(), original.public_key());
        let peer = PrivateKey::from_bytes([6u8; 32]);
        assert_eq!(
            restored
                .agree(&peer.public_key())
                .expect("test keys are not low-order"),
            original
                .agree(&peer.public_key())
                .expect("test keys are not low-order")
        );
    }
}
