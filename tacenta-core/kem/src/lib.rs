//! tacenta-kem: ML-KEM-1024's incremental interface, which the ML-KEM Braid
//! is built on.
//!
//! Standard ML-KEM encapsulates in one step. The Braid needs it split, because
//! the compressed half of a ciphertext depends only on a 64-byte header and can
//! be computed and sent while the rest of the encapsulation key is still in
//! flight. That overlap is the whole point of the protocol, and without the
//! split there is nothing to overlap.
//!
//! This is the trusted boundary: libcrux-ml-kem, byte oriented, randomness
//! passed in. It is a leaf crate so that a translation of the Braid above it
//! sees opaque declarations rather than libcrux's const-generic internals.
//!
//! ## The mapping
//!
//! The specification and the library name the same things differently, and the
//! correspondence is exact rather than approximate. Every row here is asserted
//! by a test below rather than read off documentation.
//!
//! | Braid specification | libcrux | Size |
//! | --- | --- | --- |
//! | `ek_seed \|\| hek` (the header) | `pk1` | 64 |
//! | `ek_vector` | `pk2` | 1536 |
//! | `ct1` | `Ciphertext1` | 1408 |
//! | `ct2` | `Ciphertext2` | 160 |
//! | `SHA3-256(ek_vector \|\| ek_seed) == hek`, then the modulus check | `validate_pk_bytes` | |
//!
//! The last row is worth dwelling on. The Braid has the responder check the
//! `ek_vector` it eventually receives against the hash inside the header it
//! already authenticated, and that check is the only thing standing between an
//! authenticated header and a substituted key. libcrux performs it, so we do
//! not reimplement SHA3 to do it ourselves, and the test below confirms it
//! actually rejects a tampered `pk2` rather than merely being present.

// No `unsafe` in this library crate, enforced by the attribute rather than
// observed; every library crate in the workspace carries it. The one `unsafe`
// block in the workspace is in `tacenta-core/tests/timing.rs`, which sets a CPU flag
// for measurement. The attribute bounds this crate only -- dependencies are
// the trusted boundary and are unaffected.
#![forbid(unsafe_code)]

use libcrux_ml_kem::mlkem1024::incremental as inc;
use rand_core::{CryptoRng, RngCore};
use zeroize::Zeroizing;

/// The length of an encapsulated shared secret.
pub const SHARED_SECRET_LEN: usize = 32;

/// A malformed key, ciphertext, or state: the wrong length, or rejected by the
/// primitive. Deliberately opaque, and deliberately one variant: a caller that
/// could tell these apart would learn something about a value it failed to
/// parse.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct KemError;

/// The header: `ek_seed || hek`, 64 bytes. `HEADER_SIZE` in the specification.
pub const HEADER_LEN: usize = inc::pk1_len();

/// The rest of the encapsulation key, 1536 bytes. `EK_SIZE`.
pub const EK_VECTOR_LEN: usize = inc::pk2_len();

/// The compressed half of a ciphertext, 1408 bytes. `CT1_SIZE`.
pub const CT1_LEN: usize = 1408;

/// The remaining half, 160 bytes. `CT2_SIZE`.
pub const CT2_LEN: usize = 160;

/// The serialized encapsulation state's length, 2,592 bytes: the one length
/// `EncapsState::from_bytes` accepts (session-persistence.md, Braid).
pub const ENCAPS_STATE_LEN: usize = inc::encaps_state_len();

/// The seed length incremental key generation needs.
const KEY_GENERATION_SEED_LEN: usize = 64;

/// A key pair held by the party sending an encapsulation key.
///
/// Carries the private half, so it is zeroized on drop.
///
/// `Clone` so the agreement above can advance a copy and adopt it only once the
/// message driving it has authenticated. The copy is real: nearly twelve
/// kilobytes of secret duplicated per received message, and wiped when the loser
/// drops, because `Zeroizing` reaches through the `Box`. That is the price of
/// the transaction, and it is the same trade the ratchet states already make.
#[derive(Clone)]
pub struct IncrementalKeyPair(Box<Zeroizing<[u8; inc::key_pair_len()]>>);

impl IncrementalKeyPair {
    /// Generate a key pair.
    ///
    /// Boxed because the pair is nearly twelve kilobytes and this is not a
    /// stack's business, and fixed-size rather than a `Vec` so that reading the
    /// two public halves out needs no length check and can fail in no way.
    pub fn generate<R: RngCore + CryptoRng>(rng: &mut R) -> Result<IncrementalKeyPair, KemError> {
        let mut seed = Zeroizing::new([0u8; KEY_GENERATION_SEED_LEN]);
        rng.fill_bytes(seed.as_mut());
        let mut kp = Box::new(Zeroizing::new([0u8; inc::key_pair_len()]));
        // libcrux takes the seed by value, so `*seed` is a copy the wrapper
        // cannot avoid: the original is wiped when `seed` drops, the copy
        // lives on libcrux's stack for the duration of the call and is
        // outside what this crate can promise about (CR-15).
        match inc::generate_key_pair(*seed, kp.as_mut().as_mut()) {
            Ok(()) => Ok(IncrementalKeyPair(kp)),
            Err(_) => Err(KemError),
        }
    }

    /// The header to send first: `ek_seed || hek`.
    pub fn header(&self) -> Vec<u8> {
        inc::pk1(&self.0).to_vec()
    }

    /// The rest of the encapsulation key, sent while `ct1` comes back.
    pub fn ek_vector(&self) -> Vec<u8> {
        inc::pk2(&self.0).to_vec()
    }

    /// Recover the shared secret from a complete ciphertext.
    pub fn decapsulate(&self, ct1: &[u8], ct2: &[u8]) -> Result<[u8; SHARED_SECRET_LEN], KemError> {
        // The ciphertext halves are plain byte arrays behind a length-indexed
        // newtype, with no conversion from a slice, so the length check is ours
        // to make and this is where a wrong-sized ciphertext is rejected.
        let c1_bytes: [u8; CT1_LEN] = match ct1.try_into() {
            Ok(b) => b,
            Err(_) => return Err(KemError),
        };
        let c2_bytes: [u8; CT2_LEN] = match ct2.try_into() {
            Ok(b) => b,
            Err(_) => return Err(KemError),
        };
        let c1 = inc::Ciphertext1 { value: c1_bytes };
        let c2 = inc::Ciphertext2 { value: c2_bytes };
        match inc::decapsulate_incremental_key(self.0.as_slice(), &c1, &c2) {
            Ok(ss) => Ok(ss),
            Err(_) => Err(KemError),
        }
    }

    /// The full key pair as bytes, for persistence -- not a message on the
    /// wire, see the Braid and session layers for that. Already a fixed-size
    /// byte array underneath, so this is a copy, not an encoding: no version
    /// byte of its own, since the Braid's own `to_bytes` is what stamps a
    /// version on the whole persisted state this is one field of.
    pub fn to_bytes(&self) -> Zeroizing<Vec<u8>> {
        Zeroizing::new(self.0.as_slice().to_vec())
    }

    /// Reconstruct a key pair from bytes produced by `to_bytes`.
    pub fn from_bytes(bytes: &[u8]) -> Result<IncrementalKeyPair, KemError> {
        if bytes.len() != inc::key_pair_len() {
            return Err(KemError);
        }
        let mut kp = Box::new(Zeroizing::new([0u8; inc::key_pair_len()]));
        kp.as_mut().as_mut().copy_from_slice(bytes);
        Ok(IncrementalKeyPair(kp))
    }
}

/// What `encapsulate1` leaves behind for `encapsulate2` to finish with.
///
/// Held across several messages by the responder, which is why it is a value
/// rather than a borrow, and why it zeroizes: it determines the shared secret.
///
/// `Clone` for the same reason as [`IncrementalKeyPair`]: the agreement advances
/// a copy and adopts it only once the message has authenticated.
#[derive(Clone)]
pub struct EncapsState(Zeroizing<Vec<u8>>);

impl EncapsState {
    /// This state's bytes, for persistence. Same convention as
    /// `IncrementalKeyPair::to_bytes`: a copy of the underlying bytes, no
    /// version byte of its own.
    pub fn to_bytes(&self) -> Zeroizing<Vec<u8>> {
        Zeroizing::new(self.0.to_vec())
    }

    /// Reconstruct a state from bytes produced by `to_bytes`.
    ///
    /// Checks the length and nothing else, as session-persistence.md (Braid)
    /// says a reader does: the layout is the KEM library's and is delegated.
    /// The bytes are not trusted beyond that: [`encapsulate2`] checks the
    /// coefficients it is about to compute with against the bound the library
    /// states for them, and refuses rather than hands the library an input
    /// outside it.
    pub fn from_bytes(bytes: &[u8]) -> Result<EncapsState, KemError> {
        if bytes.len() != ENCAPS_STATE_LEN {
            return Err(KemError);
        }
        Ok(EncapsState(Zeroizing::new(bytes.to_vec())))
    }
}

/// The bytes of an encapsulation state that are `i16` coefficients: four
/// `r_as_ntt` polynomials and one `error2` polynomial, 256 coefficients each
/// (libcrux `ind_cca/incremental/types.rs`, `EncapsState::to_bytes`). The 32
/// bytes after them are the encapsulation randomness, which is not a
/// coefficient and is not checked.
const ENCAPS_STATE_COEFFICIENT_BYTES: usize = 5 * 256 * 2;
const _ENCAPS_STATE_LAYOUT_AGREES: () =
    assert!(ENCAPS_STATE_COEFFICIENT_BYTES + 32 == inc::encaps_state_len());

/// The bound libcrux states for a ring-element coefficient it computes with:
/// `q - 1`.
const COEFFICIENT_BOUND: i16 = 3328;

/// Whether every little-endian `i16` in `bytes` has magnitude at most `bound`.
///
/// No early return and, at the source level, no data-dependent branch: the two
/// sign bits are accumulated into one mask across the whole slice. No record
/// of a check of the compiled assembly for a data-dependent branch in the loop
/// is in this repository, and nothing gates one. `bytes.len()` must be even;
/// the one caller passes a
/// constant that is.
fn coefficients_bounded(bytes: &[u8], bound: i16) -> bool {
    let bound = bound as i32;
    let mut out_of_range: u32 = 0;
    let mut i = 0;
    while i + 1 < bytes.len() {
        let value = i16::from_le_bytes([bytes[i], bytes[i + 1]]) as i32;
        // Sign bit of `bound - value`: set iff value > bound.
        let above = ((bound - value) >> 31) as u32;
        // Sign bit of `value + bound`: set iff value < -bound.
        let below = ((value + bound) >> 31) as u32;
        out_of_range |= above | below;
        i += 2;
    }
    out_of_range == 0
}

/// The first half of an encapsulation, from the header alone.
///
/// Returns the state to finish with, the compressed ciphertext half, and the
/// shared secret. The responder has the secret from this moment, well before
/// the initiator does, which is what the Braid's `sending_epoch` exists to
/// report.
pub fn encapsulate1<R: RngCore + CryptoRng>(
    header: &[u8],
    rng: &mut R,
) -> Result<(EncapsState, Vec<u8>, [u8; SHARED_SECRET_LEN]), KemError> {
    if header.len() != HEADER_LEN {
        return Err(KemError);
    }
    let mut randomness = Zeroizing::new([0u8; SHARED_SECRET_LEN]);
    rng.fill_bytes(randomness.as_mut());
    let mut state = Zeroizing::new(vec![0u8; inc::encaps_state_len()]);
    let mut shared_secret = [0u8; SHARED_SECRET_LEN];
    // `*randomness` is a copy libcrux's by-value signature forces, as with the
    // key-generation seed above; the original is wiped on drop.
    let ct1 = match inc::encapsulate1(
        header,
        *randomness,
        state.as_mut_slice(),
        &mut shared_secret,
    ) {
        Ok(c) => c,
        Err(_) => return Err(KemError),
    };
    Ok((EncapsState(state), ct1.value.to_vec(), shared_secret))
}

/// The second half, once the rest of the encapsulation key has arrived.
///
/// `ek_vector` **must** have been checked against the header with
/// [`validate_ek`] first. This function does not check it, because the Braid
/// treats a mismatch as terminal for the session rather than as an error to
/// recover from, and the two live at different layers.
///
/// Refuses a state whose ring-element coefficients lie outside the bound the
/// KEM library states as a precondition of its arithmetic (the comment in the
/// body says which), so that a corrupted persisted state is a refusal and not
/// an input the library's annotations do not cover. The check reads secret
/// coefficients, so it accumulates a mask over every coefficient rather than
/// returning early.
pub fn encapsulate2(state: &EncapsState, ek_vector: &[u8]) -> Result<Vec<u8>, KemError> {
    let s: &[u8; inc::encaps_state_len()] = match state.0.as_slice().try_into() {
        Ok(s) => s,
        Err(_) => return Err(KemError),
    };
    // A state restored from persistence is any 2,592 bytes (`from_bytes`). Its
    // first 2,560 bytes are five polynomials of 256 little-endian `i16`
    // coefficients (`r_as_ntt`, four of them, then `error2`), which libcrux
    // reads back without a range check. libcrux states `is_bounded_poly 3328`
    // (magnitude at most `q - 1`) as the precondition of `ntt_multiply` and
    // `add_message_error_reduce` in version 0.0.10; this crate has not checked
    // that the library discharges it, and parts of the path are marked lax
    // (LIMITATIONS.md). Outside it the library's behaviour is undocumented: on
    // its portable backend an `error2` coefficient of magnitude about 31,626 or
    // more overflowed `i16` and panicked, since this workspace keeps overflow
    // checks on in release, and other out-of-bound values returned a
    // ciphertext. Refuse such a state here, the way a wrong-sized `ek_vector`
    // is refused, so that the Braid sees a KEM refusal and goes `Failed`
    // (`finish_encaps`). This is the state-side half of the precondition; the
    // `ek_vector` side rests on `validate_ek`, which the Braid runs before
    // this on a received vector. A state `encapsulate1` produced is inside the
    // bound: libcrux's own postconditions give `|c| <= 3328` for `r_as_ntt`
    // and `|c| <= 7` for `error2`, and over 256 generated states the observed
    // ranges were [-1664, 1664] and [-2, 2], so this refuses nothing the crate
    // wrote.
    if !coefficients_bounded(&s[..ENCAPS_STATE_COEFFICIENT_BYTES], COEFFICIENT_BOUND) {
        return Err(KemError);
    }
    let pk2: &[u8; EK_VECTOR_LEN] = match ek_vector.try_into() {
        Ok(p) => p,
        Err(_) => return Err(KemError),
    };
    Ok(inc::encapsulate2(s, pk2).value.to_vec())
}

/// Whether `ek_vector` is the one the header committed to.
///
/// FIPS 203 `H(ek)`, `SHA3-256(ek_vector || ek_seed) == hek`, then the section 7.2 modulus check.
pub fn validate_ek(header: &[u8], ek_vector: &[u8]) -> bool {
    inc::validate_pk_bytes(header, ek_vector).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand::rngs::StdRng;

    fn rng(seed: u64) -> StdRng {
        StdRng::seed_from_u64(seed)
    }

    /// Every row of the mapping table in this module's documentation.
    #[test]
    fn the_sizes_are_the_specifications_sizes() {
        let mut r = rng(1);
        let kp = IncrementalKeyPair::generate(&mut r).unwrap();
        assert_eq!(HEADER_LEN, 64, "HEADER_SIZE");
        assert_eq!(EK_VECTOR_LEN, 1536, "EK_SIZE");
        assert_eq!(kp.header().len(), HEADER_LEN);
        assert_eq!(kp.ek_vector().len(), EK_VECTOR_LEN);
        let (_, ct1, _) = encapsulate1(&kp.header(), &mut r).unwrap();
        assert_eq!(ct1.len(), CT1_LEN, "CT1_SIZE");
    }

    #[test]
    fn the_split_encapsulation_agrees_with_decapsulation() {
        let mut r = rng(2);
        let kp = IncrementalKeyPair::generate(&mut r).unwrap();
        let (state, ct1, sent) = encapsulate1(&kp.header(), &mut r).unwrap();
        let ct2 = encapsulate2(&state, &kp.ek_vector()).unwrap();
        assert_eq!(ct2.len(), CT2_LEN, "CT2_SIZE");
        let recovered = kp.decapsulate(&ct1, &ct2).unwrap();
        assert_eq!(sent, recovered);
    }

    #[test]
    fn the_secret_is_known_to_the_responder_before_ct2_exists() {
        // Not a property of the library so much as a property of the interface,
        // and it is the one the Braid is built to exploit: encapsulate1 yields
        // the shared secret without ek_vector having arrived at all.
        let mut r = rng(3);
        let kp = IncrementalKeyPair::generate(&mut r).unwrap();
        let (state, ct1, sent) = encapsulate1(&kp.header(), &mut r).unwrap();
        assert_ne!(sent, [0u8; SHARED_SECRET_LEN]);
        let ct2 = encapsulate2(&state, &kp.ek_vector()).unwrap();
        assert_eq!(kp.decapsulate(&ct1, &ct2).unwrap(), sent);
    }

    #[test]
    fn validate_ek_accepts_the_real_key_and_rejects_a_substitute() {
        let mut r = rng(4);
        let kp = IncrementalKeyPair::generate(&mut r).unwrap();
        let other = IncrementalKeyPair::generate(&mut r).unwrap();
        assert!(validate_ek(&kp.header(), &kp.ek_vector()));
        // A whole different key.
        assert!(!validate_ek(&kp.header(), &other.ek_vector()));
        // One flipped bit.
        let mut tampered = kp.ek_vector();
        tampered[0] ^= 1;
        assert!(!validate_ek(&kp.header(), &tampered));
        let mut tampered_end = kp.ek_vector();
        let last = tampered_end.len() - 1;
        tampered_end[last] ^= 0x80;
        assert!(!validate_ek(&kp.header(), &tampered_end));
    }

    #[test]
    fn two_key_pairs_do_not_share_a_secret() {
        let mut r = rng(5);
        let mine = IncrementalKeyPair::generate(&mut r).unwrap();
        let theirs = IncrementalKeyPair::generate(&mut r).unwrap();
        let (state, ct1, sent) = encapsulate1(&theirs.header(), &mut r).unwrap();
        let ct2 = encapsulate2(&state, &theirs.ek_vector()).unwrap();
        let wrong = mine.decapsulate(&ct1, &ct2).unwrap();
        assert_ne!(sent, wrong);
    }

    /// A key pair restored from `to_bytes`/`from_bytes` decapsulates exactly
    /// as the original does. Functional equivalence rather than a field
    /// comparison, since neither type derives `PartialEq` -- there is no
    /// legitimate reason to compare a key pair for equality outside a test
    /// like this one.
    #[test]
    fn a_restored_key_pair_decapsulates_like_the_original() {
        let mut r = rng(7);
        let kp = IncrementalKeyPair::generate(&mut r).unwrap();
        let (state, ct1, sent) = encapsulate1(&kp.header(), &mut r).unwrap();
        let ct2 = encapsulate2(&state, &kp.ek_vector()).unwrap();

        let restored = IncrementalKeyPair::from_bytes(&kp.to_bytes()).unwrap();
        assert_eq!(restored.header(), kp.header());
        assert_eq!(restored.ek_vector(), kp.ek_vector());
        assert_eq!(restored.decapsulate(&ct1, &ct2).unwrap(), sent);
    }

    #[test]
    fn from_bytes_rejects_a_wrong_length_key_pair() {
        assert_eq!(
            IncrementalKeyPair::from_bytes(b"too short").err(),
            Some(KemError)
        );
    }

    /// A restored `EncapsState` finishes an encapsulation exactly as the
    /// original would have.
    #[test]
    fn a_restored_encaps_state_encapsulates_like_the_original() {
        let mut r = rng(8);
        let kp = IncrementalKeyPair::generate(&mut r).unwrap();
        let (state, ct1, sent) = encapsulate1(&kp.header(), &mut r).unwrap();

        let restored = EncapsState::from_bytes(&state.to_bytes()).unwrap();
        let ct2 = encapsulate2(&restored, &kp.ek_vector()).unwrap();
        assert_eq!(kp.decapsulate(&ct1, &ct2).unwrap(), sent);
    }

    #[test]
    fn from_bytes_rejects_a_wrong_length_encaps_state() {
        assert_eq!(EncapsState::from_bytes(b"too short").err(), Some(KemError));
    }

    #[test]
    fn malformed_inputs_are_rejected() {
        let mut r = rng(6);
        let kp = IncrementalKeyPair::generate(&mut r).unwrap();
        assert_eq!(encapsulate1(b"too short", &mut r).err(), Some(KemError));
        let (state, ct1, _) = encapsulate1(&kp.header(), &mut r).unwrap();
        assert_eq!(encapsulate2(&state, b"too short").err(), Some(KemError));
        let ct2 = encapsulate2(&state, &kp.ek_vector()).unwrap();
        assert_eq!(kp.decapsulate(b"short", &ct2).err(), Some(KemError));
        assert_eq!(kp.decapsulate(&ct1, b"short").err(), Some(KemError));
    }
}
