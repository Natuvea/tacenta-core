//! XEdDSA: Ed25519-compatible signatures made with an X25519 key, so a single
//! identity key both agrees (Diffie-Hellman) and signs, as the X3DH and PQXDH
//! specifications require and as libsignal-based peers verify (ADR-0002).
//!
//! Written from Signal's published specification "The XEdDSA and VXEdDSA
//! Signature Schemes", revision 1: `calculate_key_pair` converts the Montgomery
//! private key to an Edwards key pair with the sign bit forced to zero
//! (negating the scalar when the derived point's sign bit is one), signing is
//! Ed25519 with the nonce derived as `hash_1(a || M || Z)` for 64 random bytes
//! `Z`, and verification is the standard Ed25519 equation against the converted
//! public key. This module is the deliberate exception to the rule that
//! primitives come from vetted libraries; the curve arithmetic underneath is
//! still curve25519-dalek and ed25519-dalek.
//!
//! **There are no published known-answer vectors for XEdDSA**, and none can be
//! obtained: the specification does not carry any. So this primitive cannot be
//! validated against an authority the way HKDF and Ed25519 are against their
//! RFCs. What exists instead, in increasing order of how much it is worth:
//!
//! - Structural tests: round trips, the sign-side and verify-side key
//!   conversions agreeing, a tampered message or signature rejected.
//! - A pinned regression vector (`signing_is_a_fixed_function_of_key_and_nonce`)
//!   over a fixed key and nonce, so a change to the nonce derivation, the
//!   scalar negation or the sign-bit handling shows as a diff rather than as
//!   different-but-still-valid signatures.
//! - `verify` checking through `ed25519_dalek::verify_strict`, an independent
//!   implementation, so our signatures are Ed25519 signatures by a third
//!   party's reckoning and not merely by ours.
//! - The sign-bit convention `verify` reads follows the external
//!   interoperability profile (`tacenta-spec/CONSTANTS.md`, ADR-0002).

use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::montgomery::MontgomeryPoint;
use curve25519_dalek::scalar::{Scalar, clamp_integer};
use rand_core::{CryptoRng, RngCore};
use sha2::{Digest, Sha512};
use subtle::{Choice, ConditionallyNegatable};
use zeroize::Zeroizing;

use super::dh::PublicKeyBytes;

/// Signature verification failed: the signature does not verify, the public
/// key does not lie on the curve, or the scalar is out of range.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct VerifyError;

/// `hash_1`'s domain-separation prefix from the specification: 2^256 - 1 - 1
/// as 32 little-endian bytes, so the nonce hash cannot collide with a plain
/// SHA-512 of a message.
const HASH_1_PREFIX: [u8; 32] = [
    0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
];

/// The specification's `calculate_key_pair`: from the X25519 private key,
/// derive the Edwards public key `A` with its sign bit forced to zero and the
/// matching signing scalar `a` (negated when the derived point's sign bit was
/// one, so `a * B` always compresses to `A`).
///
/// The scalar comes back already wrapped: `Scalar` is `Copy`, so a bare return
/// value would leave the signing scalar in a stack slot nothing wipes, and the
/// wrapper has to be applied where the value is born rather than after it has
/// been moved once.
fn calculate_key_pair(secret: &[u8; 32]) -> ([u8; 32], Zeroizing<Scalar>) {
    // The clamped copy is wiped: it is the private scalar in another form.
    let clamped = Zeroizing::new(clamp_integer(*secret));
    let mut a = Zeroizing::new(Scalar::from_bytes_mod_order(*clamped));
    let mut public = EdwardsPoint::mul_base(&a).compress().to_bytes();
    let sign = public[31] >> 7;
    public[31] &= 0x7F;
    // A constant-time conditional negation, not a branch. The sign bit of the
    // un-normalised point is not derivable from the Montgomery public key --
    // that is the whole reason the sign convention exists -- so it is one bit
    // of the private key, and `if sign == 1 { -a } else { a }` was a
    // secret-dependent branch the timing gate cannot see, since it does not
    // time the primitives. One bit per key, constant across
    // signatures, is negligible; the pattern is still not one to keep.
    a.conditional_negate(Choice::from(sign));
    (public, a)
}

/// Whether `u` is the canonical little-endian encoding of a field element:
/// bit 255 clear and the value below `p = 2^255 - 19`.
///
/// The specification's `xeddsa_verify` begins `if u >= p: return false`.
/// curve25519-dalek's `MontgomeryPoint::to_edwards` masks the top bit and
/// reduces, so without this check `u`, `u + p` and `u | 2^255` would all
/// verify the same signatures and agree the same secrets -- three encodings
/// of one key, of which only one is the peer's identity as the peer publishes
/// it. The associated data and any fingerprint are computed over the bytes,
/// so a directory serving a non-canonical encoding would produce a session
/// that verifies, agrees, and mismatches the peer's fingerprint. Not a
/// forgery; a canonicality rule the specification states, enforced here.
fn is_canonical_field_element(u: &[u8; 32]) -> bool {
    if u[31] & 0x80 != 0 {
        return false;
    }
    // Compare against p - 1 = 0xec ff .. ff 7f (little-endian), from the most
    // significant byte down. Public data, so a plain comparison is fine.
    let mut i = 31;
    loop {
        let p_minus_one_byte = if i == 31 {
            0x7f
        } else if i == 0 {
            0xec
        } else {
            0xff
        };
        if u[i] < p_minus_one_byte {
            return true;
        }
        if u[i] > p_minus_one_byte {
            return false;
        }
        if i == 0 {
            return true;
        }
        i -= 1;
    }
}

/// Sign `message` with an X25519 private key. The signature is randomized (64
/// fresh bytes of `Z` per call, as the specification requires) and verifies as
/// a standard Ed25519 signature under the converted public key.
pub fn sign<R: RngCore + CryptoRng>(secret: &[u8; 32], message: &[u8], rng: &mut R) -> [u8; 64] {
    // Every secret intermediate is wiped on the way out: `Z` and the
    // signing scalar `a` are the private key's companions, and the nonce `r`
    // is the private key outright -- `s = r + h*a`, so whoever learns `r`
    // learns `a`. The session layer wraps every Diffie-Hellman output the same
    // way, both in the PQXDH helpers and at each ratchet step (sessions/mod.rs,
    // sessions/lifecycle.rs). The stack copies dalek and the hash make
    // internally are outside reach, which is the accepted boundary.
    //
    // Within reach, and kept small: the secrets are passed to the hash by
    // reference rather than deref-copied, `a` is born wrapped instead of
    // wrapped after a move, and the `h*a` product -- which yields `a` to
    // anyone who also holds `s` and `r` -- is wiped like `r`. Not closed
    // entirely: `clamp_integer`'s output is passed to `from_bytes_mod_order`
    // by value, the `Zeroizing<Scalar>` returned from `calculate_key_pair` is
    // itself moved out of a callee slot, and the 64-byte SHA-512 output that
    // becomes `r` is a temporary this function owns and does not wipe.
    let mut z = Zeroizing::new([0u8; 64]);
    rng.fill_bytes(z.as_mut());
    let (public, a) = calculate_key_pair(secret);
    let a_bytes = Zeroizing::new(a.to_bytes());

    // r = hash_1(a || M || Z) reduced mod the group order.
    let r = Zeroizing::new(Scalar::from_bytes_mod_order_wide(
        &Sha512::new()
            .chain_update(HASH_1_PREFIX)
            .chain_update(a_bytes.as_slice())
            .chain_update(message)
            .chain_update(z.as_slice())
            .finalize()
            .into(),
    ));
    let big_r = EdwardsPoint::mul_base(&r).compress().to_bytes();

    // h = SHA-512(R || A || M), the standard Ed25519 challenge.
    let h = Scalar::from_bytes_mod_order_wide(
        &Sha512::new()
            .chain_update(big_r)
            .chain_update(public)
            .chain_update(message)
            .finalize()
            .into(),
    );
    // `*a` and `*r` would copy the secret scalars into temporaries nothing
    // wipes; the by-reference operators exist for exactly this, so clippy's
    // preference for the by-value form is overruled here.
    #[allow(clippy::op_ref)]
    let ha = Zeroizing::new(&h * &*a);
    #[allow(clippy::op_ref)]
    let s = &*r + &*ha;

    let mut signature = [0u8; 64];
    signature[..32].copy_from_slice(&big_r);
    signature[32..].copy_from_slice(&s.to_bytes());
    signature
}

/// Verify an XEdDSA signature under an X25519 public key.
///
/// **The signature's top bit is the Edwards sign bit, not part of `s`.** A
/// Montgomery `u` coordinate names two Edwards points, `A` and `-A`, and cannot
/// distinguish them. A signer that normalises to sign zero, as [`sign`] does,
/// need not say which it used. A signer that does not normalise must, and the
/// convention is to carry it in the one spare bit: `s` is a reduced scalar
/// below 2^253, so the top bit of its last byte is always free.
///
/// A verifier that forces the sign bit to zero refuses every signer of the
/// second kind. That is half of all identities, by an unbiased coin per
/// identity: a peer's identity either has the sign bit set or it does not, and
/// nothing about a single conversation reveals which until a signature has to
/// verify. So the sign is read from `signature[63]`.
///
/// The external interoperability profile carries the Edwards sign in
/// `signature[63]` (`tacenta-spec/CONSTANTS.md`, ADR-0002).
///
/// **The accepted set differs from XEdDSA Revision 1's in both directions,
/// by design.** The specification's `xeddsa_verify` forces the Edwards sign
/// bit to 0, rejects `s ≥ 2^253` (the top three bits set), evaluates the
/// group equation for whatever `R` and `A` decode, and never carries a sign
/// in the signature. This verifier:
///
/// - is **wider on the sign bit**: it reads the Edwards sign from
///   `signature[63]`, following the external interoperability profile
///   (`tacenta-spec/CONSTANTS.md`, ADR-0002), so signatures from either
///   sign of identity verify where a literal Revision 1 verifier refuses
///   half of them;
/// - is **narrower on `s`**: `verify_strict` decodes `s` with
///   `Scalar::from_canonical_bytes`, so it requires `s < l` rather than
///   `s < 2^253`. For almost every message Revision 1 also accepts the
///   second signature `(R, s + l)`; this verifier refuses it;
/// - is **narrower on small-order points**: `verify_strict` refuses a
///   small-order `R` or `A` outright, where Revision 1 evaluates the
///   equation and accepts when it holds. Under Revision 1 the identity
///   `u = 0` (the Edwards point of order 2) verifies `R = I`, `s = 0` for
///   half of all messages; here it is refused;
/// - agrees on **non-canonical encodings and on the equation**: `u ≥ p` is
///   refused by the check above exactly as the specification's first line
///   refuses it, a non-canonical `R` fails both because each compares the
///   recomputed `R`'s canonical bytes with the bytes given, and neither
///   multiplies by the cofactor.
///
/// Everything this signer produces lies in both sets: `s` is reduced below
/// `l` by scalar arithmetic, `A = aB` for a clamped `a` is never a
/// small-order point since a clamped scalar is never `0 (mod l)`, and `R`
/// is small-order only if the nonce hashes to `0 (mod l)`, which is
/// negligible. `calculate_key_pair` and `sign` follow the specification
/// line for line; `verify` follows it on the equation and departs from it
/// on the three points above.
pub fn verify(
    public: &PublicKeyBytes,
    message: &[u8],
    signature: &[u8; 64],
) -> Result<(), VerifyError> {
    let sign = signature[63] >> 7;
    let mut cleared = *signature;
    cleared[63] &= 0x7F;

    // The specification's first check: `u >= p` is not a key. See
    // `is_canonical_field_element` for what accepting it would allow.
    if !is_canonical_field_element(public.as_bytes()) {
        return Err(VerifyError);
    }
    let edwards = MontgomeryPoint(*public.as_bytes())
        .to_edwards(sign)
        .ok_or(VerifyError)?;
    let key = ed25519_dalek::VerifyingKey::from_bytes(&edwards.compress().to_bytes())
        .map_err(|_| VerifyError)?;
    key.verify_strict(message, &ed25519_dalek::Signature::from_bytes(&cleared))
        .map_err(|_| VerifyError)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::primitives::dh::PrivateKey;
    use rand::rngs::OsRng;

    /// A deterministic byte source, so a vector is a property of *this code*
    /// rather than of whichever PRNG `rand` ships this month.
    ///
    /// Seeding `StdRng` would have been shorter and would have made the
    /// expected bytes hostage to a dependency's internals: `StdRng`'s algorithm
    /// is explicitly allowed to change between releases, and the vector would
    /// then fail for a reason that has nothing to do with XEdDSA.
    struct FixedRng {
        bytes: [u8; 64],
        at: usize,
    }

    impl rand_core::RngCore for FixedRng {
        fn next_u32(&mut self) -> u32 {
            let mut b = [0u8; 4];
            self.fill_bytes(&mut b);
            u32::from_le_bytes(b)
        }
        fn next_u64(&mut self) -> u64 {
            let mut b = [0u8; 8];
            self.fill_bytes(&mut b);
            u64::from_le_bytes(b)
        }
        fn fill_bytes(&mut self, dest: &mut [u8]) {
            for d in dest.iter_mut() {
                *d = self.bytes[self.at % self.bytes.len()];
                self.at += 1;
            }
        }
        fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
            self.fill_bytes(dest);
            Ok(())
        }
    }

    impl rand_core::CryptoRng for FixedRng {}

    /// Known-answer regression vectors, and an honest label for what they are.
    ///
    /// **There are no published known-answer vectors for XEdDSA.** The
    /// specification does not carry any, so this cannot be validation against
    /// an authority the way the RFC 5869 and RFC 8032 vectors are. That gap
    /// is known and is not closed by this test.
    ///
    /// What this *is*: a pin on the exact bytes this construction produces for
    /// a fixed key and a fixed nonce, so any change to the nonce derivation,
    /// the scalar negation, or the sign-bit handling shows up as a diff rather
    /// than as different signatures that still verify under our own verifier.
    ///
    /// The external validation lives elsewhere and is stronger than a
    /// self-generated vector: `verify` checks with `ed25519_dalek`'s
    /// `verify_strict`, an independent implementation. Observation-based
    /// interoperability checks are not part of this tree.
    #[test]
    fn signing_is_a_fixed_function_of_key_and_nonce() {
        let secret = [7u8; 32];
        let message = b"tacenta xeddsa regression vector";

        let sign_once = || {
            let mut rng = FixedRng {
                bytes: [0x5au8; 64],
                at: 0,
            };
            sign(&secret, message, &mut rng)
        };

        let first = sign_once();
        assert_eq!(first, sign_once(), "same key and nonce, same signature");

        // The public key this signs under, and the signature over the message.
        let public = PrivateKey::from_bytes(secret).public_key();
        assert!(
            verify(&public, message, &first).is_ok(),
            "the pinned signature must verify"
        );

        // The pin itself. If this fails, the construction changed; decide
        // whether that was intended before updating the constant.
        assert_eq!(
            hex_of(&first),
            KNOWN_SIGNATURE,
            "the XEdDSA construction changed"
        );

        // A different nonce gives a different signature that still verifies,
        // which is what distinguishes this from a deterministic scheme.
        let mut other = FixedRng {
            bytes: [0xa5u8; 64],
            at: 0,
        };
        let second = sign(&secret, message, &mut other);
        assert_ne!(first, second, "the nonce must reach the signature");
        assert!(verify(&public, message, &second).is_ok());
    }

    /// The signature `sign` produces for secret `[7; 32]`, nonce `[0x5a; 64]`
    /// and the message above. Recorded from the implementation, not from an
    /// authority; see the test's own docstring for why that distinction
    /// matters and where the external validation actually comes from.
    const KNOWN_SIGNATURE: &str = "bb7c0f9b0b8ac3eae0d53d1f6293030c8e83cc77c95a588bf4d354fe8773d023aa43b918aea1e850e6007778504d2140b1da30668453760fb72874038f230a09";

    fn hex_of(bytes: &[u8; 64]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    #[test]
    fn a_signature_by_the_x25519_key_verifies_under_its_public_key() {
        let secret = [7u8; 32];
        let key = PrivateKey::from_bytes(secret);
        let sig = sign(&secret, b"sign this prekey", &mut OsRng);
        assert!(verify(&key.public_key(), b"sign this prekey", &sig).is_ok());
    }

    #[test]
    fn sign_side_and_verify_side_key_conversions_agree() {
        // The scalar-multiplication route (signing) and the Montgomery-to-
        // Edwards route (verifying) must land on the same Edwards public key,
        // for many keys.
        //
        // The keys are also chosen to exercise *both* branches of
        // `calculate_key_pair`'s sign normalisation (CR-28): the raw derived
        // point's sign bit is 0 for some and 1 for others, and the scalar is
        // negated only in the latter. A loop that happened to hit only one
        // branch would leave the negation path untested while still passing, so
        // the two are counted and both are required to occur.
        let mut saw_sign_zero = false;
        let mut saw_sign_one = false;
        for i in 0..32u8 {
            let secret = [i.wrapping_mul(17).wrapping_add(3); 32];
            let (public_from_scalar, _) = calculate_key_pair(&secret);
            let u = PrivateKey::from_bytes(secret).public_key();
            let public_from_montgomery = MontgomeryPoint(*u.as_bytes())
                .to_edwards(0)
                .expect("a valid public key converts")
                .compress()
                .to_bytes();
            assert_eq!(public_from_scalar, public_from_montgomery);

            // The sign bit of the *un-normalised* point, which is the bit
            // `calculate_key_pair` reads to decide whether to negate.
            let raw = EdwardsPoint::mul_base(&Scalar::from_bytes_mod_order(clamp_integer(secret)))
                .compress()
                .to_bytes();
            match raw[31] >> 7 {
                0 => saw_sign_zero = true,
                _ => saw_sign_one = true,
            }
        }
        assert!(
            saw_sign_zero && saw_sign_one,
            "the key set must exercise both the negated and un-negated sign branches"
        );
    }

    #[test]
    fn a_tampered_message_or_wrong_key_is_rejected() {
        let secret = [11u8; 32];
        let key = PrivateKey::from_bytes(secret);
        let sig = sign(&secret, b"the message", &mut OsRng);
        assert_eq!(
            verify(&key.public_key(), b"another message", &sig),
            Err(VerifyError)
        );
        let other = PrivateKey::from_bytes([12u8; 32]);
        assert_eq!(
            verify(&other.public_key(), b"the message", &sig),
            Err(VerifyError)
        );
    }

    /// A signer that does not normalise the sign bit is still verified.
    ///
    /// No other test here can cover this case, because every signature these
    /// tests produce comes from [`sign`], which normalises. A suite that only
    /// signs with itself cannot discover that it rejects half the world.
    ///
    /// So the signature is built the other way on purpose: the same identity,
    /// the Edwards point that `to_edwards(1)` reconstructs, the scalar that
    /// matches it, and the sign bit carried in the spare top bit of `s`. That
    /// is what a peer following the other convention sends.
    #[test]
    fn a_signature_carrying_the_sign_bit_verifies() {
        use curve25519_dalek::edwards::EdwardsPoint;
        use curve25519_dalek::scalar::{Scalar, clamp_integer};
        use sha2::{Digest, Sha512};

        let secret = [9u8; 32];
        let key = PrivateKey::from_bytes(secret);
        let message = b"a prekey signed by the other convention";

        // The un-normalised pair: whichever sign the raw scalar lands on, take
        // the *opposite* representation of the same Montgomery point, so the
        // sign bit is the one `sign` would have cleared.
        let scalar = Scalar::from_bytes_mod_order(clamp_integer(secret));
        let raw = EdwardsPoint::mul_base(&scalar).compress().to_bytes();
        let raw_sign = raw[31] >> 7;
        let (a, big_a) = if raw_sign == 1 {
            (scalar, raw)
        } else {
            let neg = -scalar;
            (neg, EdwardsPoint::mul_base(&neg).compress().to_bytes())
        };
        assert_eq!(big_a[31] >> 7, 1, "this test needs the sign-one branch");

        // An ordinary Ed25519 signature under that point, then the sign bit
        // moved into the spare top bit of `s`.
        let r = Scalar::from_bytes_mod_order_wide(&[3u8; 64]);
        let big_r = EdwardsPoint::mul_base(&r).compress().to_bytes();
        let h = Scalar::from_bytes_mod_order_wide(
            &Sha512::new()
                .chain_update(big_r)
                .chain_update(big_a)
                .chain_update(message)
                .finalize()
                .into(),
        );
        let sig_s = (r + h * a).to_bytes();

        let mut signature = [0u8; 64];
        signature[..32].copy_from_slice(&big_r);
        signature[32..].copy_from_slice(&sig_s);
        assert_eq!(signature[63] >> 7, 0, "s must leave the top bit free");
        signature[63] |= 0x80;

        assert!(
            verify(&key.public_key(), message, &signature).is_ok(),
            "a signature carrying the sign bit was refused; the interoperability profile carries the sign there"
        );
    }

    #[test]
    fn a_tampered_signature_is_rejected() {
        let secret = [13u8; 32];
        let key = PrivateKey::from_bytes(secret);
        let mut sig = sign(&secret, b"the message", &mut OsRng);
        sig[0] ^= 1;
        assert_eq!(
            verify(&key.public_key(), b"the message", &sig),
            Err(VerifyError)
        );
    }

    /// The refusals a verifier owes, each pinned.
    ///
    /// The `s + l` case guards against a feature-unification hazard:
    /// `ed25519-dalek`'s `legacy_compatibility` feature relaxes the `s < l`
    /// check, and Cargo feature unification means *any* crate in the build
    /// enabling it would relax ours. Nothing enables it today, and this test
    /// is what fails if something does -- a second signature for every
    /// message is a malleability the prekey signatures must not have.
    #[test]
    fn malformed_signatures_and_keys_are_rejected() {
        let secret = [23u8; 32];
        let key = PrivateKey::from_bytes(secret);
        let message = b"the refusals a verifier owes";
        let good = sign(&secret, message, &mut OsRng);
        assert!(verify(&key.public_key(), message, &good).is_ok());

        // `s + l`: the same signature with a non-reduced scalar. `s < l < 2^253`,
        // so the sum fits in 254 bits and leaves the sign bit clear.
        const GROUP_ORDER_LE: [u8; 32] = [
            0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9,
            0xde, 0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x10,
        ];
        let mut s_plus_l = good;
        let mut carry = 0u16;
        for i in 0..32 {
            let sum = u16::from(s_plus_l[32 + i]) + u16::from(GROUP_ORDER_LE[i]) + carry;
            s_plus_l[32 + i] = (sum & 0xff) as u8;
            carry = sum >> 8;
        }
        assert_eq!(carry, 0);
        assert_eq!(s_plus_l[63] >> 7, 0, "the sum must not reach the sign bit");
        assert_eq!(
            verify(&key.public_key(), message, &s_plus_l),
            Err(VerifyError),
            "a non-reduced s verified: is ed25519-dalek's legacy_compatibility enabled somewhere?"
        );

        // The sign bit flipped on a normalising signer's signature names -A.
        let mut flipped = good;
        flipped[63] ^= 0x80;
        assert_eq!(
            verify(&key.public_key(), message, &flipped),
            Err(VerifyError)
        );

        // A small-order R: the identity's encoding.
        let mut small_r = good;
        small_r[..32].copy_from_slice(&[0u8; 32]);
        small_r[0] = 1;
        assert_eq!(
            verify(&key.public_key(), message, &small_r),
            Err(VerifyError)
        );

        // Degenerate and non-canonical public keys: u = 0, u = 1 and u = p - 1
        // name low-order or undefined Edwards points; u | 2^255 and u + p are
        // the two non-canonical encodings of a valid key.
        let mut p_minus_one = [0xffu8; 32];
        p_minus_one[0] = 0xec;
        p_minus_one[31] = 0x7f;
        let mut one = [0u8; 32];
        one[0] = 1;
        for u in [[0u8; 32], one, p_minus_one] {
            assert_eq!(
                verify(&PublicKeyBytes::from_bytes(u), message, &good),
                Err(VerifyError),
                "degenerate u accepted"
            );
        }
        let canonical = *key.public_key().as_bytes();
        let mut high_bit = canonical;
        high_bit[31] |= 0x80;
        assert_eq!(
            verify(&PublicKeyBytes::from_bytes(high_bit), message, &good),
            Err(VerifyError)
        );
        let mut plus_p = canonical;
        let mut carry = 0u16;
        let p_le = {
            let mut p = [0xffu8; 32];
            p[0] = 0xed;
            p[31] = 0x7f;
            p
        };
        for i in 0..32 {
            let sum = u16::from(plus_p[i]) + u16::from(p_le[i]) + carry;
            plus_p[i] = (sum & 0xff) as u8;
            carry = sum >> 8;
        }
        assert_eq!(carry, 0, "a canonical u plus p fits in 256 bits");
        assert_eq!(
            verify(&PublicKeyBytes::from_bytes(plus_p), message, &good),
            Err(VerifyError)
        );
    }

    /// A forgery-shaped input the plain Ed25519 equation *accepts* and only
    /// `verify_strict` refuses: a small-order public key (the point `u = 0`
    /// names), `R` the identity, `s = 0`. The negative tests above are all
    /// rejected by the equation itself, so they could not tell a regression
    /// from `verify_strict` to `verify` -- this one can. Non-strict
    /// verification accepts it for about half of all messages, so it is
    /// checked over many.
    #[test]
    fn a_small_order_forgery_is_refused() {
        let mut forged = [0u8; 64];
        forged[0] = 1; // `R` = the identity point's encoding; `s` = 0.
        let weak = PublicKeyBytes::from_bytes([0u8; 32]);
        for i in 0..64u8 {
            let message = [i; 16];
            assert_eq!(
                verify(&weak, &message, &forged),
                Err(VerifyError),
                "a small-order forgery verified; is verify_strict still in use?"
            );
        }
    }

    #[test]
    fn signatures_are_randomized_but_all_verify() {
        let secret = [21u8; 32];
        let key = PrivateKey::from_bytes(secret);
        let s1 = sign(&secret, b"m", &mut OsRng);
        let s2 = sign(&secret, b"m", &mut OsRng);
        assert_ne!(s1[..32], s2[..32], "fresh Z randomizes the nonce point R");
        assert!(verify(&key.public_key(), b"m", &s1).is_ok());
        assert!(verify(&key.public_key(), b"m", &s2).is_ok());
    }
}
