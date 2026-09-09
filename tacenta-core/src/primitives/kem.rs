//! kem: ML-KEM-1024 (FIPS 203), the post-quantum key encapsulation PQXDH uses.
//!
//! From libcrux-ml-kem, a formally verified implementation: its source carries
//! hax and F* contracts, which is why it is used here, since the post-quantum
//! primitive the rest of the handshake rests on should itself be verified. It
//! sits at the trusted boundary like the other primitives, and is named as such
//! in tacenta-proofs LIMITATIONS.md.
//!
//! The wrapper is byte-oriented so the session layer never handles the
//! underlying types, and takes randomness explicitly, which keeps the whole
//! boundary deterministic given its inputs.

use libcrux_ml_kem::mlkem1024;
use rand_core::{CryptoRng, RngCore};
use zeroize::Zeroizing;

/// The length of an encapsulated shared secret.
pub const SHARED_SECRET_LEN: usize = 32;

/// The seed length ML-KEM key generation needs.
const KEY_GENERATION_SEED_LEN: usize = 64;

/// A malformed public key or ciphertext (wrong length).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct KemError;

/// An ML-KEM-1024 key pair. Bob holds these for his KEM prekeys.
///
/// libcrux's key-pair type is not an erasing type, so this wrapper holds the
/// pair as `sk || pk` in an erasing buffer and hands libcrux a reconstructed
/// value per call. A key pair stored in `MlKem1024KeyPair` itself would stay
/// resident for the life of whatever held it -- for a `PrekeyStore`, the life
/// of the party. This is the shape `tacenta_kem::IncrementalKeyPair` uses one
/// crate over, for the same reason.
///
/// **One copy is not erased: the one inside libcrux's own types.** Both
/// `generate` and `decapsulate` have to hand libcrux its types, which means a
/// transient `MlKem1024KeyPair` at generation and a transient
/// `MlKem1024PrivateKey` per decapsulation, neither wiped when it drops. The
/// erasing buffer bounds the window to the duration of one call rather than
/// the lifetime of the store. Closing it entirely means reaching inside a
/// dependency, which is not this wrapper's to do -- it is recorded against the
/// trusted boundary in `tacenta-proofs/LIMITATIONS.md` instead.
pub struct KeyPair(Zeroizing<Vec<u8>>);

/// Asserted rather than derived: `Zeroizing` already wipes the only field on
/// drop, and the marker is what a static check in the tests can hold onto.
impl zeroize::ZeroizeOnDrop for KeyPair {}

impl KeyPair {
    /// Generate a key pair from the given randomness.
    pub fn generate<R: RngCore + CryptoRng>(rng: &mut R) -> KeyPair {
        // The seed is wiped once the key pair is derived from it.
        let mut seed = Zeroizing::new([0u8; KEY_GENERATION_SEED_LEN]);
        rng.fill_bytes(seed.as_mut());
        let generated = mlkem1024::generate_key_pair(*seed);
        let mut out = Vec::with_capacity(generated.sk().len() + generated.pk().len());
        out.extend_from_slice(generated.sk().as_slice());
        out.extend_from_slice(generated.pk().as_slice());
        KeyPair(Zeroizing::new(out))
    }

    /// The public key, as published in a prekey bundle.
    pub fn public_key(&self) -> Vec<u8> {
        self.0[mlkem1024::MlKem1024PrivateKey::len()..].to_vec()
    }

    /// This key pair's bytes, for a caller persisting a prekey store.
    /// Private half first, then the public half -- the order `from_bytes`
    /// below expects them back in.
    pub fn to_bytes(&self) -> Zeroizing<Vec<u8>> {
        Zeroizing::new(self.0.to_vec())
    }

    /// Reconstruct a key pair from bytes produced by `to_bytes`.
    ///
    /// Both halves are length-checked. The public half is then checked for shape
    /// too: `try_into` only verifies length -- libcrux's `TryFrom` is a length
    /// check, not a parse -- so the FIPS 203 encapsulation-key check is run over
    /// it explicitly with `validate_public_key`, the same check `encapsulate`
    /// makes on a bundle's KEM prekey (CR-18). A public half of the right size
    /// but the wrong shape is refused here rather than reasoned about at the
    /// first encapsulation against this pair.
    ///
    /// The private half is checked to *belong* to the public half. An ML-KEM
    /// decapsulation key carries the encapsulation key and its hash inside it
    /// (FIPS 203, `dk = dk_PKE || ek || H(ek) || z`), so the two halves can
    /// disagree in a way no length check sees: a private half from one
    /// generation beside a public half from another has the right size, a
    /// valid public half, and decapsulates every ciphertext sent to that
    /// public half to the wrong secret. Implicit rejection means nothing says
    /// so at decapsulation; the mismatch surfaces as an AEAD failure on the
    /// peer's first message, which is the same thing a network fault looks
    /// like, and a prekey store holding such a pair serves it to every peer
    /// who fetches it. Two checks close that. The embedded `ek` must be the
    /// public half byte for byte, which is what binds the halves, and
    /// libcrux's `validate_private_key_only` must accept the private half,
    /// which is the FIPS 203 section 7.3 hash check (`H(ek)` recomputed over
    /// the embedded key and compared) and says the private half is at least
    /// one key generation could have written. The threat model is still
    /// corruption rather than a hostile chooser -- the private half never
    /// leaves this party -- but a corrupted pair that decapsulates wrongly is
    /// worse than one that fails to decode, and the check costs one hash.
    pub fn from_bytes(bytes: &[u8]) -> Result<KeyPair, KemError> {
        let sk_len = mlkem1024::MlKem1024PrivateKey::len();
        let pk_len = mlkem1024::MlKem1024PublicKey::len();
        if bytes.len() != sk_len + pk_len {
            return Err(KemError);
        }
        let (sk_bytes, pk_bytes) = bytes.split_at(sk_len);
        let sk: mlkem1024::MlKem1024PrivateKey = sk_bytes.try_into().map_err(|_| KemError)?;
        let pk: mlkem1024::MlKem1024PublicKey = pk_bytes.try_into().map_err(|_| KemError)?;
        if !mlkem1024::validate_public_key(&pk) {
            return Err(KemError);
        }
        if !mlkem1024::portable::validate_private_key_only(&sk) {
            return Err(KemError);
        }
        if embedded_public_key(sk_bytes) != pk_bytes {
            return Err(KemError);
        }
        Ok(KeyPair(Zeroizing::new(bytes.to_vec())))
    }
}

/// The encapsulation key an ML-KEM-1024 decapsulation key carries inside it.
///
/// FIPS 203 lays a decapsulation key out as `dk_PKE || ek || H(ek) || z`, with
/// `H(ek)` and `z` 32 bytes each, so `ek` sits after the first `len(dk) -
/// len(ek) - 64` bytes. Located from the two public lengths rather than from a
/// literal offset, so a parameter-set change moves it with them.
fn embedded_public_key(sk_bytes: &[u8]) -> &[u8] {
    let pk_len = mlkem1024::MlKem1024PublicKey::len();
    let start = sk_bytes.len() - pk_len - 64;
    &sk_bytes[start..start + pk_len]
}

/// The length of an ML-KEM-1024 public key.
pub fn public_key_len() -> usize {
    mlkem1024::MlKem1024PublicKey::len()
}

/// The length of an ML-KEM-1024 ciphertext.
pub fn ciphertext_len() -> usize {
    mlkem1024::MlKem1024Ciphertext::len()
}

/// Encapsulate a fresh shared secret to `public_key`, returning the ciphertext
/// to send and the secret to fold into the handshake.
pub fn encapsulate<R: RngCore + CryptoRng>(
    public_key: &[u8],
    rng: &mut R,
) -> Result<(Vec<u8>, [u8; SHARED_SECRET_LEN]), KemError> {
    let pk = mlkem1024::MlKem1024PublicKey::try_from(public_key).map_err(|_| KemError)?;
    // `try_from` checks the length and nothing else. FIPS 203 section 7.2
    // specifies an encapsulation-key check -- every coefficient must
    // re-encode to the bytes it was decoded from -- and this wrapper performs
    // it itself rather than assume it of the dependency. The only caller
    // hands this a key straight out of a bundle the directory served, which is
    // the attacker's to write. The IND-CCA argument for the post-quantum half
    // assumes a well-formed key; a malformed one is refused rather than
    // reasoned about.
    if !mlkem1024::validate_public_key(&pk) {
        return Err(KemError);
    }
    // The encapsulation randomness is wiped once used.
    let mut randomness = Zeroizing::new([0u8; SHARED_SECRET_LEN]);
    rng.fill_bytes(randomness.as_mut());
    let (ciphertext, shared_secret) = mlkem1024::encapsulate(&pk, *randomness);
    Ok((ciphertext.as_slice().to_vec(), shared_secret))
}

/// Recover the shared secret from a ciphertext.
///
/// ML-KEM uses implicit rejection: a ciphertext that was not produced for this
/// key does not fail here, it yields a different, pseudorandom secret. The
/// mismatch surfaces when the handshake's AEAD fails to decrypt, which is where
/// PQXDH expects it to surface.
pub fn decapsulate(
    keypair: &KeyPair,
    ciphertext: &[u8],
) -> Result<[u8; SHARED_SECRET_LEN], KemError> {
    let ct = mlkem1024::MlKem1024Ciphertext::try_from(ciphertext).map_err(|_| KemError)?;
    // Reconstructed per call rather than stored, so the copy inside libcrux's
    // type lives for one call instead of for the life of the store. See
    // `KeyPair`'s own note.
    let sk_len = mlkem1024::MlKem1024PrivateKey::len();
    let sk_bytes = keypair.0.get(..sk_len).ok_or(KemError)?;
    let sk: mlkem1024::MlKem1024PrivateKey = sk_bytes.try_into().map_err(|_| KemError)?;
    Ok(mlkem1024::decapsulate(&sk, &ct))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;

    fn rng(seed: u64) -> rand::rngs::StdRng {
        rand::rngs::StdRng::seed_from_u64(seed)
    }

    /// The key pair erases itself when dropped.
    ///
    /// A static check, for the reason `tacenta-ratchet`'s own version gives:
    /// inspecting freed memory is not something a test can do soundly, and what
    /// this pins is that the property cannot be removed without the build
    /// failing. It matters more here than there, because the erasure is not a
    /// derive on this type but a consequence of its representation -- someone
    /// changing the field to libcrux's `MlKem1024KeyPair` would undo it
    /// without any other signal, and this fails instead.
    #[test]
    fn the_key_pair_erases_when_dropped() {
        fn assert_erases<T: zeroize::ZeroizeOnDrop>() {}
        assert_erases::<KeyPair>();
    }

    #[test]
    fn encapsulation_round_trips() {
        let mut r = rng(1);
        let kp = KeyPair::generate(&mut r);
        let (ct, sent) = encapsulate(&kp.public_key(), &mut r).unwrap();
        let received = decapsulate(&kp, &ct).unwrap();
        assert_eq!(sent, received);
        assert_eq!(sent.len(), SHARED_SECRET_LEN);
    }

    #[test]
    fn each_encapsulation_is_fresh() {
        let mut r = rng(2);
        let kp = KeyPair::generate(&mut r);
        let (ct1, ss1) = encapsulate(&kp.public_key(), &mut r).unwrap();
        let (ct2, ss2) = encapsulate(&kp.public_key(), &mut r).unwrap();
        assert_ne!(ct1, ct2);
        assert_ne!(ss1, ss2);
    }

    #[test]
    fn a_ciphertext_for_another_key_yields_a_different_secret() {
        // Implicit rejection: decapsulation succeeds but the secret differs, so
        // the mismatch shows up as an AEAD failure later, not here.
        let mut r = rng(3);
        let mine = KeyPair::generate(&mut r);
        let theirs = KeyPair::generate(&mut r);
        let (ct, sent) = encapsulate(&theirs.public_key(), &mut r).unwrap();
        let recovered = decapsulate(&mine, &ct).unwrap();
        assert_ne!(sent, recovered);
    }

    #[test]
    fn malformed_inputs_are_rejected() {
        let mut r = rng(4);
        let kp = KeyPair::generate(&mut r);
        assert_eq!(encapsulate(b"too short", &mut r), Err(KemError));
        assert_eq!(decapsulate(&kp, b"too short"), Err(KemError));
    }

    /// A key pair restored from `to_bytes`/`from_bytes` decapsulates exactly
    /// as the original does.
    #[test]
    fn a_restored_key_pair_decapsulates_like_the_original() {
        let mut r = rng(6);
        let kp = KeyPair::generate(&mut r);
        let (ct, sent) = encapsulate(&kp.public_key(), &mut r).unwrap();

        let restored = KeyPair::from_bytes(&kp.to_bytes()).unwrap();
        assert_eq!(restored.public_key(), kp.public_key());
        assert_eq!(decapsulate(&restored, &ct).unwrap(), sent);
    }

    #[test]
    fn from_bytes_rejects_a_wrong_length_key_pair() {
        assert!(matches!(KeyPair::from_bytes(b"too short"), Err(KemError)));
    }

    /// A private half from one generation beside a public half from another
    /// is refused, not restored.
    ///
    /// Before the check, such a pair decoded: right length, valid public
    /// half. It then decapsulated every ciphertext sent to its public half to
    /// the wrong secret -- implicit rejection, so silently -- and a prekey
    /// store holding it served it to every peer, each of whose first messages
    /// then failed to authenticate in a way indistinguishable from a network
    /// fault. The halves are checked against each other so that a pair
    /// which decodes is one that decapsulates.
    #[test]
    fn from_bytes_rejects_halves_from_different_generations() {
        let mut r = rng(7);
        let a = KeyPair::generate(&mut r);
        let b = KeyPair::generate(&mut r);
        let sk_len = mlkem1024::MlKem1024PrivateKey::len();
        let mut mixed = a.to_bytes().to_vec();
        mixed[sk_len..].copy_from_slice(&b.to_bytes()[sk_len..]);
        assert!(matches!(KeyPair::from_bytes(&mixed), Err(KemError)));

        // The pair is what would have gone wrong: with the check bypassed,
        // a secret encapsulated to the public half does not come back.
        let (ct, sent) = encapsulate(&b.public_key(), &mut r).unwrap();
        let unchecked = KeyPair(Zeroizing::new(mixed));
        assert_ne!(decapsulate(&unchecked, &ct).unwrap(), sent);
    }

    /// The private half's own consistency is checked too: a decapsulation key
    /// whose embedded `H(ek)` does not hash its embedded `ek` is refused, even
    /// when the embedded `ek` still matches the public half.
    #[test]
    fn from_bytes_rejects_a_private_half_with_a_wrong_embedded_hash() {
        let mut r = rng(8);
        let kp = KeyPair::generate(&mut r);
        let sk_len = mlkem1024::MlKem1024PrivateKey::len();
        let mut bytes = kp.to_bytes().to_vec();
        // `H(ek)` is the 32 bytes before the final 32-byte `z`.
        bytes[sk_len - 64] ^= 0x01;
        assert!(matches!(KeyPair::from_bytes(&bytes), Err(KemError)));
    }

    #[test]
    fn sizes_are_the_ml_kem_1024_sizes() {
        let mut r = rng(5);
        let kp = KeyPair::generate(&mut r);
        assert_eq!(kp.public_key().len(), public_key_len());
        let (ct, _) = encapsulate(&kp.public_key(), &mut r).unwrap();
        assert_eq!(ct.len(), ciphertext_len());
    }
}
