//! X25519 Diffie-Hellman, the key-agreement primitive the Double Ratchet
//! composes. Backed by x25519-dalek.

use curve25519_dalek::montgomery::MontgomeryPoint;
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

/// Whether `key` is the canonical encoding of a point of the prime-order
/// subgroup of Curve25519: bit 255 clear, the value below p = 2^255 - 19, a
/// u-coordinate some point of the curve has, and that point of order q, the
/// order of the base point (identities-and-devices.md, Accepting a signed
/// statement, check 6).
///
/// This is the identity-key rule of the boundaries that admit a long-lived
/// key. It is not a rule for the keys an agreement consumes: X25519 accepts
/// any 32 bytes, and the ephemeral and prekey inputs are held to the canonical
/// encoding and to a contributory result instead. The rule refuses the five
/// low-order values, the values that lie on the twist, and every canonical
/// value of mixed order, and it refuses every non-canonical spelling of an
/// accepted key, so exactly one spelling of a key passes.
pub fn is_prime_order_public(key: &PublicKeyBytes) -> bool {
    if !crate::xeddsa::is_canonical_field_element(key.as_bytes()) {
        return false;
    }
    match MontgomeryPoint(*key.as_bytes()).to_edwards(0) {
        Some(point) => point.is_torsion_free(),
        None => false,
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

    /// `(label, key, accepted)`: known answers for the identity-key rule from
    /// an implementation that shares no code with this one (own field and
    /// curve arithmetic, two methods that agree), with the two public keys of
    /// RFC 7748, section 6.1, and the base point.
    const IDENTITY_KEYS: &[(&str, &str, bool)] = &[
        (
            "base-point",
            "0900000000000000000000000000000000000000000000000000000000000000",
            true,
        ),
        (
            "rfc7748-alice",
            "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a",
            true,
        ),
        (
            "rfc7748-bob",
            "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f",
            true,
        ),
        (
            "honest-h1",
            "a4e09292b651c278b9772c569f5fa9bb13d906b46ab68c9df9dc2b4409f8a209",
            true,
        ),
        (
            "honest-h2",
            "ce8d3ad1ccb633ec7b70c17814a5c76ecd029685050d344745ba05870e587d59",
            true,
        ),
        (
            "honest-h3",
            "5fef13fc76023a9ee6ded987b6aa93958cdc2097ef9fc845d5319c9ca100d35e",
            true,
        ),
        (
            "h1-plus-torsion-1",
            "037faa3bbfc676b26f87fb1449a152bcb3eb7cfeeedbaa3604deca93ac75304b",
            false,
        ),
        (
            "h1-plus-torsion-2",
            "6722174dbc997c555d35183ae1f5b54d718517e2012641580dc06bf48b5cc67b",
            false,
        ),
        (
            "h1-plus-torsion-4",
            "cc80c67924df11225baa5ff7838b65ef4747fc514b11a810fb951106ab3d620a",
            false,
        ),
        (
            "h1-plus-torsion-7",
            "17f500d43bb2ac86183a9b80e83d701445cfbd68042222600acb81b7096d0974",
            false,
        ),
        (
            "base9-plus-torsion-1",
            "c5e259858ab3095bc0569034a6f3a88fbde0536e336dad4a9519584e920c0c7c",
            false,
        ),
        (
            "base9-plus-torsion-2",
            "1fe6ceff8b05ff49494ba9ab1eb4ff98f3d60573ebd1927b9a7f68509f252e02",
            false,
        ),
        (
            "base9-plus-torsion-4",
            "6a6367e4f97c6024bced038937b5b12b2f26c2e9915fe3a7bcbea07354504770",
            false,
        ),
        (
            "u-0",
            "0000000000000000000000000000000000000000000000000000000000000000",
            false,
        ),
        (
            "u-1",
            "0100000000000000000000000000000000000000000000000000000000000000",
            false,
        ),
        (
            "u-p-minus-1",
            "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
            false,
        ),
        (
            "u-order8-a",
            "e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800",
            false,
        ),
        (
            "u-order8-b",
            "5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157",
            false,
        ),
        (
            "twist-u-2",
            "0200000000000000000000000000000000000000000000000000000000000000",
            false,
        ),
        (
            "twist-u-3",
            "0300000000000000000000000000000000000000000000000000000000000000",
            false,
        ),
        (
            "noncanonical-9-plus-p",
            "f6ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
            false,
        ),
        (
            "noncanonical-9-bit255",
            "0900000000000000000000000000000000000000000000000000000000000080",
            false,
        ),
        (
            "noncanonical-p",
            "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
            false,
        ),
        (
            "noncanonical-honest-h1-bit255",
            "a4e09292b651c278b9772c569f5fa9bb13d906b46ab68c9df9dc2b4409f8a289",
            false,
        ),
        (
            "noncanonical-torsion-bit255",
            "037faa3bbfc676b26f87fb1449a152bcb3eb7cfeeedbaa3604deca93ac7530cb",
            false,
        ),
    ];

    fn public(text: &str) -> PublicKeyBytes {
        let bytes: [u8; 32] = hex::decode(text).unwrap().try_into().unwrap();
        PublicKeyBytes::from_bytes(bytes)
    }

    #[test]
    fn the_identity_rule_over_known_keys() {
        for (label, key, accepted) in IDENTITY_KEYS {
            assert_eq!(is_prime_order_public(&public(key)), *accepted, "{label}");
        }
    }

    /// Over-refusal: every key an honest generator produces is accepted. The
    /// keys are drawn from a fixed seed, so a run is reproducible.
    #[test]
    fn generated_public_keys_are_accepted() {
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x1d);
        for _ in 0..512 {
            assert!(is_prime_order_public(
                &PrivateKey::generate(&mut rng).public_key()
            ));
        }
    }

    /// Exactly one spelling of an accepted key is accepted: each accepted key
    /// of the table above, written with bit 255 set, or with p added where the
    /// sum still fits in 256 bits, is refused.
    #[test]
    fn only_the_canonical_spelling_of_a_key_is_accepted() {
        let mut p = [0xffu8; 32];
        p[0] = 0xed;
        p[31] = 0x7f;
        for (label, key, accepted) in IDENTITY_KEYS {
            if !accepted {
                continue;
            }
            let base = *public(key).as_bytes();
            let mut high = base;
            high[31] |= 0x80;
            assert!(
                !is_prime_order_public(&PublicKeyBytes::from_bytes(high)),
                "{label} with bit 255 set"
            );
            let mut sum = [0u8; 32];
            let mut carry = 0u16;
            for i in 0..32 {
                let total = u16::from(base[i]) + u16::from(p[i]) + carry;
                sum[i] = total.to_le_bytes()[0];
                carry = total >> 8;
            }
            if carry == 0 {
                assert!(
                    !is_prime_order_public(&PublicKeyBytes::from_bytes(sum)),
                    "{label} plus p"
                );
            }
        }
    }

    /// The rule over every row of the identity-key vectors, which the model
    /// generates (tacenta-test-vectors/README.md). Found relative to this
    /// crate, as the XEdDSA vectors are.
    #[test]
    fn the_identity_key_vectors_agree() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tacenta-test-vectors/vectors/identity/identity-key.json"
        );
        let text = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("the identity-key vectors at {path} must be readable: {e}"));
        let doc: serde_json::Value = serde_json::from_str(&text).expect("the vectors file is JSON");
        let vectors = doc["vectors"].as_array().expect("a vectors array");
        let (mut valid, mut invalid) = (0, 0);
        for v in vectors {
            let id = v["id"].as_str().expect("an id");
            let accepted = v["result"].as_str() == Some("valid");
            assert_eq!(
                is_prime_order_public(&public(v["inputs"]["key"].as_str().expect("a key"))),
                accepted,
                "{id}"
            );
            if accepted {
                valid += 1;
            } else {
                invalid += 1;
            }
        }
        assert!(
            valid >= 6 && invalid >= 30,
            "the file holds {valid} valid and {invalid} invalid rows"
        );
    }
}
