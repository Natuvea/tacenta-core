//! Property tests for the PQXDH derivation crate, `tacenta-session`.
//!
//! Each property names the sentence of `tacenta-spec/protocol/session-establishment.md`
//! it tests, and each is checked against an oracle written from that sentence here, not
//! against the crate's own code: the derivation against the RustCrypto `hkdf` crate fed
//! the page's input keying material, salt and `info`; the encodings against the page's
//! byte layout; the canonical-key rule against a comparison with p = 2^255 - 19 done on
//! the bytes. A defect shared by the crate and the page is not found by these tests.
//!
//! Case count: `CASES` (1,024) per property when `PROPTEST_CASES` is unset. `PROPTEST_CASES`
//! overrides it (proptest reads the variable over the configuration given here), and the
//! hosted `rust` job and `tooling/ci.sh` set it to 2,048, so that is the count CI runs.
//! Replay: proptest shrinks a failing case and
//! prints the minimal input in the failure message, and its default failure
//! persistence writes the failing case's seed to `pqxdh_properties.proptest-regressions`
//! beside this file, which the next local run replays first. No regressions file is
//! committed and the generator's seed is not fixed, so a run that fails in CI is
//! replayed from the minimal input its log prints.

use hkdf::Hkdf;
use proptest::prelude::*;
use sha2::Sha256;
use tacenta_session::{
    ENCODE_EC_CURVE25519, ENCODE_EC_LEN, ENCODE_KEM_ML_KEM_1024, Key, associated_data,
    associated_data_with_kem, decode_ec, encode_ec, encode_kem, is_canonical_x25519, kdf_sk, km,
    shared_secret,
};
use x25519_dalek::{PublicKey, StaticSecret};

/// The number of generated cases each property runs.
const CASES: u32 = 1024;

/// The `info` string, as the page gives it ("used verbatim").
const INFO: &[u8] = b"Tacenta_CURVE25519_SHA-256_ML-KEM-1024";

/// The page's `KDF(KM)`, written from its sentence with the RustCrypto `hkdf` crate,
/// a second HKDF implementation beside the one in `tacenta-kdf`.
fn reference_kdf(km: &[u8]) -> [u8; 32] {
    let mut ikm = vec![0xFFu8; 32];
    ikm.extend_from_slice(km);
    let hk = Hkdf::<Sha256>::new(Some(&[0u8; 32]), &ikm);
    let mut out = [0u8; 32];
    hk.expand(INFO, &mut out)
        .expect("32 bytes is a valid HKDF length");
    out
}

/// p = 2^255 - 19, little-endian.
fn p_le() -> [u8; 32] {
    let mut p = [0xffu8; 32];
    p[0] = 0xed;
    p[31] = 0x7f;
    p
}

/// The page's canonical rule, written as a comparison of 256-bit little-endian
/// numbers: bit 255 clear, and the value below p.
fn reference_canonical(k: &Key) -> bool {
    if k[31] & 0x80 != 0 {
        return false;
    }
    let p = p_le();
    for i in (0..32).rev() {
        if k[i] != p[i] {
            return k[i] < p[i];
        }
    }
    false // equal to p
}

/// 32-byte strings that reach the boundary of the canonical rule often: uniform
/// bytes, bytes with bit 255 set, and values near p from either side (the last
/// byte `0x7f` or `0xff`, the thirty middle bytes `0xff`, the first byte half the
/// time in `0xe8..=0xf0` around p's `0xed` and otherwise any), with a middle byte
/// nudged off the pattern in a quarter of them.
fn curve_bytes() -> impl Strategy<Value = Key> {
    prop_oneof![
        prop::array::uniform32(any::<u8>()),
        prop::array::uniform32(any::<u8>()).prop_map(|mut k| {
            k[31] |= 0x80;
            k
        }),
        (
            prop_oneof![0xe8u8..=0xf0, any::<u8>()],
            any::<u8>(),
            0usize..31,
            0u8..4,
        )
            .prop_map(|(first, last_bit, at, nudge)| {
                let mut k = [0xffu8; 32];
                k[0] = first;
                k[31] = 0x7f | (last_bit & 0x80);
                if nudge == 0 && at > 0 {
                    k[at] = 0xfe;
                }
                k
            }),
    ]
}

fn config() -> ProptestConfig {
    ProptestConfig::with_cases(CASES)
}

proptest! {
    #![proptest_config(config())]

    /// `kdf_sk` is the page's `KDF(KM)` for every input keying material of up to
    /// 256 bytes: HKDF-SHA-256 over `F || KM` with `F` 32 bytes of `0xFF`, an all-zero
    /// 32-byte salt and the `info` string, 32 bytes out.
    ///
    /// Specification: session-establishment.md, Notation: "`KDF(KM)` is 32 bytes of
    /// HKDF output using `hash`, with input keying material `F || KM`, an all-zero salt
    /// the length of the hash output, and an `info` string"; the `info` string is the
    /// one the page gives "used verbatim".
    #[test]
    fn kdf_sk_is_the_pages_kdf(material in prop::collection::vec(any::<u8>(), 0..256)) {
        prop_assert_eq!(kdf_sk(&material), reference_kdf(&material));
    }

    /// `km` is `DH1 || DH2 || DH3 || SS` without a one-time curve prekey and
    /// `DH1 || DH2 || DH3 || DH4 || SS` with one, so its length is 128 or 160 bytes and
    /// each component is recovered at its 32-byte offset; and `shared_secret` is
    /// `KDF` of exactly that, for every choice of the five 32-byte inputs and of
    /// whether `DH4` is present.
    ///
    /// Specification: session-establishment.md, Sending the initial message:
    /// "SK = KDF(DH1 || DH2 || DH3 || SS) # without a one-time curve prekey" and
    /// "SK = KDF(DH1 || DH2 || DH3 || DH4 || SS) # with one".
    #[test]
    fn the_secret_is_kdf_of_the_outputs_in_the_pages_order(
        dh1 in prop::array::uniform32(any::<u8>()),
        dh2 in prop::array::uniform32(any::<u8>()),
        dh3 in prop::array::uniform32(any::<u8>()),
        dh4 in prop::option::of(prop::array::uniform32(any::<u8>())),
        ss in prop::array::uniform32(any::<u8>()),
    ) {
        let mut expected = Vec::new();
        expected.extend_from_slice(&dh1);
        expected.extend_from_slice(&dh2);
        expected.extend_from_slice(&dh3);
        if let Some(d4) = &dh4 {
            expected.extend_from_slice(d4);
        }
        expected.extend_from_slice(&ss);
        let material = km(&dh1, &dh2, &dh3, dh4.as_ref(), &ss);
        prop_assert_eq!(material.len(), if dh4.is_some() { 160 } else { 128 });
        prop_assert_eq!(&material, &expected, "the outputs in the page's order, SS last");
        prop_assert_eq!(
            shared_secret(&dh1, &dh2, &dh3, dh4.as_ref(), &ss),
            reference_kdf(&expected)
        );
    }

    /// `encode_ec` is the type byte `0x05` then the 32-byte key, 33 bytes for every
    /// key; `encode_kem` is the type byte `0x08` then the key, 1,569 bytes for a
    /// 1,568-byte key; the two type bytes differ, so no byte string is both.
    ///
    /// Specification: session-establishment.md, Parameters: "`EncodeEC` / `DecodeEC`
    /// ... type byte `0x05`, then the key: 33 bytes" and "`EncodeKEM` / `DecodeKEM` ...
    /// type byte `0x08`, then the key: 1,569 bytes".
    #[test]
    fn the_encodings_have_the_pages_layout(
        key in prop::array::uniform32(any::<u8>()),
        kem in prop::collection::vec(any::<u8>(), 1568),
    ) {
        let ec = encode_ec(&key);
        prop_assert_eq!(ec.len(), 33);
        prop_assert_eq!(ec.len(), ENCODE_EC_LEN);
        prop_assert_eq!(ec[0], 0x05);
        prop_assert_eq!(ENCODE_EC_CURVE25519, 0x05);
        prop_assert_eq!(&ec[1..], &key[..]);
        let k = encode_kem(&kem);
        prop_assert_eq!(k.len(), 1569);
        prop_assert_eq!(k[0], 0x08);
        prop_assert_eq!(ENCODE_KEM_ML_KEM_1024, 0x08);
        prop_assert_eq!(&k[1..], &kem[..]);
    }

    /// `AD = EncodeEC(IKA) || EncodeEC(IKB)`, and because `EncodeEC` is fixed-width
    /// the two identities are recovered from `AD` alone: splitting at 33 bytes gives
    /// back both keys, so two different pairs never give the same `AD`. The variant
    /// with the KEM prekey is that `AD` with `EncodeKEM(PQPKB)` appended.
    ///
    /// Specification: session-establishment.md, Sending the initial message: "AD =
    /// EncodeEC(IKA) || EncodeEC(IKB)", "the two identities are recoverable from it
    /// only if the first one's width is known in advance", and "`EncodeKEM(PQPKB)`
    /// must be appended to `AD` as well" (for a KEM that does not bind its key). The
    /// page says this implementation does not append it, so the last check tests an
    /// unused helper as written, not the associated data the session uses.
    #[test]
    fn the_associated_data_binds_both_identities(
        ika in prop::array::uniform32(any::<u8>()),
        ikb in prop::array::uniform32(any::<u8>()),
        other_a in prop::array::uniform32(any::<u8>()),
        other_b in prop::array::uniform32(any::<u8>()),
        pq in prop::collection::vec(any::<u8>(), 1568),
    ) {
        let ad = associated_data(&encode_ec(&ika), &encode_ec(&ikb));
        prop_assert_eq!(ad.len(), 66);
        let mut expected = encode_ec(&ika);
        expected.extend_from_slice(&encode_ec(&ikb));
        prop_assert_eq!(&ad, &expected);
        prop_assert_eq!(decode_any_ec(&ad[..33]), ika);
        prop_assert_eq!(decode_any_ec(&ad[33..]), ikb);
        let other = associated_data(&encode_ec(&other_a), &encode_ec(&other_b));
        prop_assert_eq!(ad == other, ika == other_a && ikb == other_b);
        let with_kem = associated_data_with_kem(&encode_ec(&ika), &encode_ec(&ikb), &encode_kem(&pq));
        let mut expected_kem = expected.clone();
        expected_kem.extend_from_slice(&encode_kem(&pq));
        prop_assert_eq!(with_kem, expected_kem);
    }

    /// `DecodeEC` accepts exactly one encoding of each key: over 32-byte strings
    /// concentrated at the boundary, `is_canonical_x25519` agrees with a comparison
    /// against p done on the bytes, `decode_ec(encode_ec(k))` is `Some(k)` exactly
    /// when `k` is canonical, and the accepted bytes are the encoding of the key
    /// returned.
    ///
    /// Specification: session-establishment.md, Sending the initial message:
    /// "`DecodeEC` accepts exactly one encoding of each key" and "`DecodeEC` refuses
    /// every one but the canonical encoding: a key whose top bit (bit 255) is set,
    /// and a key whose value is at least p."
    #[test]
    fn decode_ec_accepts_exactly_the_canonical_encoding(k in curve_bytes()) {
        let canonical = reference_canonical(&k);
        prop_assert_eq!(is_canonical_x25519(&k), canonical);
        let encoded = encode_ec(&k);
        match decode_ec(&encoded) {
            Some(back) => {
                prop_assert!(canonical, "accepted a non-canonical spelling");
                prop_assert_eq!(back, k);
                prop_assert_eq!(encode_ec(&back), encoded);
            }
            None => prop_assert!(!canonical, "refused a canonical key"),
        }
    }

    /// `DecodeEC` reads nothing but an `EncodeEC` form: for every byte string of up
    /// to 40 bytes, and for a curve byte with a key one to seven bytes too long or
    /// too short, it returns a key only when the string is 33 bytes, starts with
    /// `0x05` and carries a canonical key, and then re-encoding the key gives the
    /// string back.
    ///
    /// Specification: session-establishment.md, Parameters ("type byte `0x05`, then
    /// the key: 33 bytes") and Sending the initial message ("`DecodeEC` accepts
    /// exactly one encoding of each key").
    #[test]
    fn decode_ec_reads_only_encode_ec_forms(
        bytes in prop_oneof![
            prop::collection::vec(any::<u8>(), 0..40),
            (curve_bytes(), any::<u8>()).prop_map(|(k, t)| {
                let mut v = vec![if t < 192 { 0x05 } else { t }];
                v.extend_from_slice(&k);
                v
            }),
            (curve_bytes(), 1usize..8, any::<bool>(), any::<u8>()).prop_map(|(k, d, longer, x)| {
                let mut v = vec![0x05];
                if longer {
                    v.extend_from_slice(&k);
                    v.extend(std::iter::repeat_n(x, d));
                } else {
                    v.extend_from_slice(&k[..32 - d]);
                }
                v
            }),
        ],
    ) {
        match decode_ec(&bytes) {
            Some(k) => {
                prop_assert_eq!(bytes.len(), 33);
                prop_assert_eq!(bytes[0], 0x05);
                prop_assert!(reference_canonical(&k));
                prop_assert_eq!(encode_ec(&k), bytes);
            }
            None => {
                let well_formed = bytes.len() == 33
                    && bytes[0] == 0x05
                    && reference_canonical(&bytes[1..].try_into().unwrap());
                prop_assert!(!well_formed, "refused a well-formed encoding");
            }
        }
    }

    /// No honest key is refused: the X25519 public key of any 32-byte secret (the
    /// library clamps it) is canonical and decodes from its `EncodeEC` form.
    ///
    /// Specification: session-establishment.md, Sending the initial message: "An
    /// honest key generator never produces either, so no honest key is refused."
    #[test]
    fn no_honest_key_is_refused(secret in prop::array::uniform32(any::<u8>())) {
        let public = PublicKey::from(&StaticSecret::from(secret)).to_bytes();
        prop_assert!(is_canonical_x25519(&public));
        prop_assert_eq!(decode_ec(&encode_ec(&public)), Some(public));
    }
}

/// The key bytes of an `EncodeEC` form, without the canonical check, for the
/// recoverability property (which is about the split, not the decoder).
fn decode_any_ec(bytes: &[u8]) -> Key {
    assert_eq!(bytes.len(), 33);
    assert_eq!(bytes[0], 0x05);
    bytes[1..].try_into().unwrap()
}

/// The values either side of the canonical boundary, which the boundary strategy
/// can draw (the first byte `0xec` or `0xed` with the pattern of p) but a run does
/// not report drawing: checked here directly, so the two sides of the rule are
/// exercised on every run whatever proptest draws.
#[test]
fn the_boundary_values_are_on_the_sides_the_page_says() {
    let p = p_le();
    let mut below = p;
    below[0] = 0xec;
    assert!(
        reference_canonical(&below) && is_canonical_x25519(&below),
        "p - 1"
    );
    assert!(!reference_canonical(&p) && !is_canonical_x25519(&p), "p");
    let mut top = p;
    top[0] = 0xff;
    assert!(!is_canonical_x25519(&top), "2^255 - 1");
    assert!(is_canonical_x25519(&[0u8; 32]), "zero");
}
