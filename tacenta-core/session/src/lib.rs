//! The PQXDH derivation: the verified zone for session establishment.
//!
//! This crate follows tacenta-spec/protocol/session-establishment.md and the
//! model in tacenta-model (`Model.SessionEstablishment`).
//!
//! What lives here is the part of the agreement PQXDH itself contributes: the
//! order the Diffie-Hellman outputs and the encapsulated secret are assembled
//! in, the derivation that turns them into a shared secret, and the encodings
//! that bind the two identities. The agreements, the encapsulation, and the
//! signature check are trusted primitives and stay in `tacenta-core`, so they
//! reach the translation as axioms.
//!
//! This crate is a *leaf* for the same reason `tacenta-ratchet` is: T1 and T3
//! translate it, so nothing outside the derivation can drag constructs Aeneas
//! does not model into the translation.

// No `unsafe` in this library crate, enforced by the attribute rather than
// observed; every library crate in the workspace carries it. The one `unsafe`
// block in the workspace is in `tacenta-core/tests/timing.rs`, which sets a CPU flag
// for measurement. The attribute bounds this crate only -- dependencies are
// the trusted boundary and are unaffected.
#![forbid(unsafe_code)]
#![no_std]
// No `?`: `let`-`else` and `match` instead, for the reason recorded once in
// tacenta-ratchet's module doc ("The `?` operator"). The lint asks for `?`.
#![allow(clippy::question_mark)]

extern crate alloc;

use alloc::vec::Vec;
use zeroize::Zeroizing;

/// A 32-byte protocol key.
pub type Key = [u8; 32];

/// The domain-separation prefix on the KDF input: 32 bytes of `0xFF` for
/// curve25519. It ensures the leading bytes of the input keying material are
/// never a valid encoding of a scalar or a curve point, keeping this derivation
/// separate from XEdDSA's use of the same identity key.
const F_PREFIX: [u8; 32] = [0xFF; 32];

/// The KDF `info`: the application string, the curve, the hash, and the KEM
/// joined by underscores. The application string is wire-sensitive and pinned in
/// the conformance manifest; this matches the model's label.
const SK_INFO: &[u8] = b"Tacenta_CURVE25519_SHA-256_ML-KEM-1024";

/// Leading byte identifying curve25519 in `EncodeEC`.
///
/// The published specification leaves this byte to the implementer. The value
/// follows the external interoperability profile, which encodes a curve key as
/// `0x05 ‖ key` (`tacenta-spec/CONSTANTS.md`).
pub const ENCODE_EC_CURVE25519: u8 = 0x05;

/// Leading byte identifying ML-KEM-1024 in `EncodeKEM`. Distinct from the curve
/// byte, which is what keeps the two encodings' ranges disjoint so a byte
/// sequence can never be read as both a curve key and a KEM key.
///
/// Follows the same interoperability profile as the curve byte: a KEM prekey
/// signature verifies against `0x08 ‖ key`, not against the bare key.
///
/// The two bytes are a pair. A change to one alone would leave the other
/// encoding's signature failing to verify, and that refusal would be
/// indistinguishable from a bad key.
pub const ENCODE_KEM_ML_KEM_1024: u8 = 0x08;

/// The width of `EncodeEC`: the curve byte and a 32-byte key.
///
/// Load-bearing rather than incidental. `associated_data` is a bare
/// concatenation, so the two identities are recoverable from it only because
/// this width is known in advance (session-establishment.md).
pub const ENCODE_EC_LEN: usize = 33;

/// `KM`, the input keying material: the Diffie-Hellman outputs in order, then
/// the one-time curve output when the bundle carried a one-time prekey, then the
/// encapsulated post-quantum secret, which is always last.
///
/// The order and the optionality are the whole content of this step, which is
/// why it is named rather than folded into `shared_secret`. Every component is
/// a fixed 32 bytes, and that is what makes the concatenation unambiguous:
/// see `Proofs.SessionEstablishment`.
pub fn km(dh1: &Key, dh2: &Key, dh3: &Key, dh4: Option<&Key>, ss: &Key) -> Vec<u8> {
    // Sized for the widest case up front. Grown from empty, the vector would
    // reallocate as each output is appended and hand the allocator back the
    // 32-, 64- and 128-byte buffers holding the earlier outputs, unwiped; the
    // caller wraps only the final buffer. One allocation means there is only
    // the one to wipe (CR-15).
    let mut out = Vec::with_capacity(5 * 32);
    out.extend_from_slice(dh1);
    out.extend_from_slice(dh2);
    out.extend_from_slice(dh3);
    match dh4 {
        None => (),
        Some(d4) => out.extend_from_slice(d4),
    }
    out.extend_from_slice(ss);
    out
}

/// `KDF(KM)`: 32 bytes of HKDF output, with input keying material `F || KM`, an
/// all-zero salt the length of the hash output, and the parameter `info`.
///
/// The buffer is wiped on the way out: it holds the concatenated secret key
/// material, which the specification says to delete once the secret is derived.
pub fn kdf_sk(km_bytes: &[u8]) -> Key {
    // Sized for the prefix and the material together, so no intermediate
    // buffer holding the material is freed unwiped on the way to the one
    // that is (CR-15). Saturating: a capacity hint, and a slice length plus a
    // constant is an addition the panic-freedom proof would otherwise have to
    // discharge.
    let mut ikm = Zeroizing::new(Vec::with_capacity(
        F_PREFIX.len().saturating_add(km_bytes.len()),
    ));
    ikm.extend_from_slice(&F_PREFIX);
    ikm.extend_from_slice(km_bytes);
    tacenta_kdf::hkdf_sha256::<32>(&[0u8; 32], &ikm, SK_INFO)
}

/// The shared secret the Double Ratchet starts from.
///
/// `dh1`, `dh2`, `dh3` are always present. `dh4` is present exactly when the
/// prekey bundle carried a one-time curve prekey. `ss` is the encapsulated
/// post-quantum secret and is always last.
pub fn shared_secret(dh1: &Key, dh2: &Key, dh3: &Key, dh4: Option<&Key>, ss: &Key) -> Key {
    // Wiped on the way out: this buffer concentrates every Diffie-Hellman output
    // and the encapsulated secret, which the specification says to delete.
    let material = Zeroizing::new(km(dh1, dh2, dh3, dh4, ss));
    kdf_sk(&material)
}

/// The associated data binding both identities. The encoders are wire-sensitive
/// and pinned elsewhere, so this takes the encoded forms as given.
///
/// **The first encoding must be fixed-width.** This is a bare concatenation
/// with no separator and no length prefix, so the two identities are
/// recoverable only if the first one's width is known. With variable-width
/// encodings two different pairs of identities produce the same associated
/// data, and a binding two pairs satisfy binds neither. `encode_ec` is fixed at
/// `ENCODE_EC_LEN`, which is what makes this safe.
pub fn associated_data(encoded_ik_a: &[u8], encoded_ik_b: &[u8]) -> Vec<u8> {
    // Public data, so nothing here needs wiping; sized up front anyway, for
    // the same shape as `km` and one allocation rather than two.
    let mut ad = Vec::with_capacity(encoded_ik_a.len().saturating_add(encoded_ik_b.len()));
    ad.extend_from_slice(encoded_ik_a);
    ad.extend_from_slice(encoded_ik_b);
    ad
}

/// With a KEM that does not bind its public key into the ciphertext, the encoded
/// KEM prekey is appended to the associated data as well.
pub fn associated_data_with_kem(
    encoded_ik_a: &[u8],
    encoded_ik_b: &[u8],
    encoded_pq_pk: &[u8],
) -> Vec<u8> {
    let mut ad = associated_data(encoded_ik_a, encoded_ik_b);
    ad.extend_from_slice(encoded_pq_pk);
    ad
}

/// `EncodeEC`: the curve byte followed by the public key.
pub fn encode_ec(pk: &Key) -> Vec<u8> {
    let mut out = Vec::new();
    out.push(ENCODE_EC_CURVE25519);
    out.extend_from_slice(pk);
    out
}

/// `EncodeKEM`: the KEM byte followed by the public key.
pub fn encode_kem(pk: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    out.push(ENCODE_KEM_ML_KEM_1024);
    out.extend_from_slice(pk);
    out
}

/// `DecodeEC`: read a curve public key back from its `EncodeEC` form, or `None`
/// if the bytes are not one.
pub fn decode_ec(bytes: &[u8]) -> Option<Key> {
    if bytes.len() == ENCODE_EC_LEN && bytes[0] == ENCODE_EC_CURVE25519 {
        let mut k = [0u8; 32];
        let mut i = 0;
        // An index loop rather than `copy_from_slice` on a sub-slice: the
        // translation models the indexed write, and this keeps the bound the
        // proof needs visible rather than buried in a slice range.
        while i < 32 {
            k[i] = bytes[i + 1];
            i += 1;
        }
        Some(k)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_ec_is_fixed_width() {
        let a = encode_ec(&[0x11; 32]);
        let b = encode_ec(&[0x22; 32]);
        assert_eq!(a.len(), ENCODE_EC_LEN, "one curve byte and a 32-byte key");
        assert_eq!(a.len(), b.len(), "the width cannot depend on the key");
    }

    #[test]
    fn encode_ec_round_trips() {
        let k: Key = [0x5a; 32];
        assert_eq!(decode_ec(&encode_ec(&k)), Some(k));
    }

    #[test]
    fn decode_ec_rejects_the_other_encoding() {
        // A KEM encoding of the right length must not read back as a curve key.
        let mut bad = encode_kem(&[0x00; 32]);
        bad.truncate(ENCODE_EC_LEN);
        assert_eq!(decode_ec(&bad), None);
    }

    #[test]
    fn the_one_time_output_is_folded_in() {
        let a = shared_secret(&[0x11; 32], &[0x22; 32], &[0x33; 32], None, &[0x55; 32]);
        let b = shared_secret(
            &[0x11; 32],
            &[0x22; 32],
            &[0x33; 32],
            Some(&[0x44; 32]),
            &[0x55; 32],
        );
        assert_ne!(a, b, "the fourth agreement must reach the derivation");
    }

    #[test]
    fn km_orders_the_components() {
        let out = km(
            &[0x11; 32],
            &[0x22; 32],
            &[0x33; 32],
            Some(&[0x44; 32]),
            &[0x55; 32],
        );
        assert_eq!(out.len(), 5 * 32);
        assert_eq!(out[0], 0x11);
        assert_eq!(out[32], 0x22);
        assert_eq!(out[64], 0x33);
        assert_eq!(out[96], 0x44);
        assert_eq!(out[128], 0x55, "the encapsulated secret is always last");
    }
}
