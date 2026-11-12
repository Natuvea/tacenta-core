//! Property tests for the wire codecs the message properties in `tests/fuzz.rs` do
//! not reach: the composite header on its own (`encode_composite`,
//! `decode_composite`), the prekey bundle (`encode_bundle`, `decode_bundle`) and the
//! initial message (`encode_initial`, `decode_initial`), and the type a message's
//! framing names (`message_type`).
//!
//! Each property names the sentence of `tacenta-spec/protocol/message-format.md` it
//! tests. The oracles are written here from the page: the layouts from its diagrams
//! and stated lengths (102 and 1,811 bytes), the acceptance rule of the composite
//! header from its list of refusals, and the canonical rule on curve keys as a
//! comparison with p done on the bytes. The round trips use the crate's own encoder,
//! so a layout fault the encoder and decoder share is caught only where the layout is
//! also checked against the page's offsets, which the properties do for every field.
//!
//! Case count: `CASES` (512) per property when `PROPTEST_CASES` is unset. `PROPTEST_CASES`
//! overrides it (proptest reads the variable over the configuration given here), and the
//! hosted `rust` job and `tooling/ci.sh` set it to 2,048, so that is the count CI runs.
//! Replay: proptest shrinks a failing case and
//! prints the minimal input in the failure message, and its default failure
//! persistence writes the failing case's seed to
//! `wire_codec_properties.proptest-regressions` beside this file, which the next local
//! run replays first. No regressions file is committed and the generator's seed is not
//! fixed, so a run that fails in CI is replayed from the minimal input its log prints.

use proptest::prelude::*;
use tacenta_core::serialization::composite::{
    AgreementType, Codeword, Composite, decode_composite, encode_composite,
};
use tacenta_core::serialization::{
    MessageType, WireBundle, decode_bundle, decode_initial, encode_bundle, encode_initial,
    message_type,
};

/// The number of generated cases each property runs.
const CASES: u32 = 512;

fn config() -> ProptestConfig {
    ProptestConfig::with_cases(CASES)
}

/// The page's canonical rule: the 32 bytes read little-endian are below p.
fn canonical(k: &[u8]) -> bool {
    let mut p = [0xffu8; 32];
    p[0] = 0xed;
    p[31] = 0x7f;
    for i in (0..32).rev() {
        if k[i] != p[i] {
            return k[i] < p[i];
        }
    }
    false
}

/// A canonical curve key: arbitrary bytes, or the values just below p.
fn canonical_key() -> impl Strategy<Value = [u8; 32]> {
    prop_oneof![
        prop::array::uniform32(any::<u8>()).prop_map(|mut k| {
            k[31] &= 0x3f;
            k
        }),
        (0u8..=0xec).prop_map(|first| {
            let mut k = [0xffu8; 32];
            k[0] = first;
            k[31] = 0x7f;
            k
        }),
    ]
}

/// A curve key that is not canonical: bit 255 set, or a value from p up with bit 255
/// clear.
fn respelled_key() -> impl Strategy<Value = [u8; 32]> {
    prop_oneof![
        prop::array::uniform32(any::<u8>()).prop_map(|mut k| {
            k[31] |= 0x80;
            k
        }),
        (0xedu8..=0xff).prop_map(|first| {
            let mut k = [0xffu8; 32];
            k[0] = first;
            k[31] = 0x7f;
            k
        }),
    ]
}

fn ag_type() -> impl Strategy<Value = AgreementType> {
    prop_oneof![
        Just(AgreementType::None),
        Just(AgreementType::Hdr),
        Just(AgreementType::Ek),
        Just(AgreementType::EkCt1Ack),
        Just(AgreementType::Ct1),
        Just(AgreementType::Ct2),
    ]
}

fn composite() -> impl Strategy<Value = Composite> {
    (
        canonical_key(),
        any::<u32>(),
        any::<u32>(),
        any::<u64>(),
        any::<u64>(),
        any::<u64>(),
        ag_type(),
        prop::option::of((any::<u16>(), prop::array::uniform32(any::<u8>()))),
    )
        .prop_map(
            |(dh, pn, n, pq_epoch, pq_n, ag_epoch, ag_type, chunk)| Composite {
                dh,
                pn,
                n,
                pq_epoch,
                pq_n,
                ag_epoch,
                ag_type,
                ag_chunk: chunk.map(|(index, data)| Codeword { index, data }),
            },
        )
}

fn bundle() -> impl Strategy<Value = WireBundle> {
    (
        canonical_key(),
        canonical_key(),
        prop::collection::vec(any::<u8>(), 64),
        prop::collection::vec(any::<u8>(), 1568),
        prop::collection::vec(any::<u8>(), 64),
        prop::option::of(canonical_key()),
        any::<u32>(),
        any::<u32>(),
        any::<u32>(),
    )
        .prop_map(|(ik, spk, s1, kem, s2, otpk, a, b, c)| WireBundle {
            identity_key: ik,
            signed_prekey: spk,
            signed_prekey_signature: s1.try_into().unwrap(),
            kem_prekey: kem,
            kem_prekey_signature: s2.try_into().unwrap(),
            one_time_prekey: otpk,
            signed_prekey_id: a,
            one_time_prekey_id: b,
            kem_prekey_id: c,
        })
}

/// Whether 102 framed bytes are a composite header the page's decoder accepts,
/// written from the page's list of refusals.
fn reference_composite_valid(b: &[u8]) -> bool {
    b.len() >= 102
        && b[0] == 0x01
        && b[1] == 0x01
        && canonical(&b[2..34])
        && b[66] <= 0x05
        && match b[67] {
            0x00 => b[68..102].iter().all(|x| *x == 0),
            0x01 => true,
            _ => false,
        }
}

proptest! {
    #![proptest_config(config())]

    /// The composite header is the page's 102 bytes, field by field at the page's
    /// offsets with big-endian counters, a presence byte and the codeword's full width
    /// zeroed when absent; and it decodes back to itself, with whatever follows it
    /// returned untouched.
    ///
    /// Specification: message-format.md, Ratchet message: "composite = version ||
    /// type=0x01 || dh (32) || pn (4) || n (4) || pq_epoch (8) || pq_n (8) ||
    /// ag_epoch (8) || ag_type (1) || chunk_present (1) || chunk_index (2) || chunk
    /// (32)", "All counters are big-endian. The composite header is **102 bytes**",
    /// the `ag_type` table, and "a presence byte, then the field's full width
    /// regardless, zeroed when absent". (The page's standalone decoder refuses
    /// trailing bytes; `decode_composite` returns them to its caller, and that refusal
    /// is not tested here.)
    #[test]
    fn the_composite_header_has_the_pages_layout_and_round_trips(
        h in composite(),
        tail in prop::collection::vec(any::<u8>(), 0..40),
    ) {
        let e = encode_composite(&h);
        prop_assert_eq!(e.len(), 102);
        prop_assert_eq!(&e[..2], &[0x01, 0x01][..]);
        prop_assert_eq!(&e[2..34], &h.dh[..]);
        prop_assert_eq!(&e[34..38], &h.pn.to_be_bytes()[..]);
        prop_assert_eq!(&e[38..42], &h.n.to_be_bytes()[..]);
        prop_assert_eq!(&e[42..50], &h.pq_epoch.to_be_bytes()[..]);
        prop_assert_eq!(&e[50..58], &h.pq_n.to_be_bytes()[..]);
        prop_assert_eq!(&e[58..66], &h.ag_epoch.to_be_bytes()[..]);
        let type_byte = match h.ag_type {
            AgreementType::None => 0x00,
            AgreementType::Hdr => 0x01,
            AgreementType::Ek => 0x02,
            AgreementType::EkCt1Ack => 0x03,
            AgreementType::Ct1 => 0x04,
            AgreementType::Ct2 => 0x05,
        };
        prop_assert_eq!(e[66], type_byte);
        match &h.ag_chunk {
            None => {
                prop_assert_eq!(e[67], 0x00);
                prop_assert!(e[68..102].iter().all(|x| *x == 0));
            }
            Some(c) => {
                prop_assert_eq!(e[67], 0x01);
                prop_assert_eq!(&e[68..70], &c.index.to_be_bytes()[..]);
                prop_assert_eq!(&e[70..102], &c.data[..]);
            }
        }
        let mut with_tail = e.clone();
        with_tail.extend_from_slice(&tail);
        let (back, rest) = decode_composite(&with_tail).expect("a valid header decodes");
        prop_assert_eq!(back, h);
        prop_assert_eq!(rest, &tail[..]);
    }

    /// Over 102-byte strings made from a valid header with the version, type, `dh`,
    /// `ag_type`, presence byte and absent-codeword padding each corrupted at random
    /// (the bytes drawn half the time from just past the valid range),
    /// the decoder accepts exactly the strings the page's rules accept, and what it
    /// accepts re-encodes to the same bytes (one spelling), and anything shorter than
    /// 102 bytes is refused.
    ///
    /// Specification: message-format.md, Ratchet message: "A decoder rejects a message
    /// shorter than its framing and header, and rejects an unrecognised version or an
    /// unexpected type byte. It also rejects a `dh` that is not the canonical encoding
    /// of a curve public key ..., an `ag_type` outside the six values above, a presence
    /// byte other than `0x00` or `0x01`, and an absent codeword whose index or chunk
    /// bytes are not all zero"; and Principles: "**Canonical.** Exactly one valid
    /// encoding of a given message."
    #[test]
    fn the_composite_decoder_accepts_exactly_the_pages_headers(
        h in composite(),
        version in prop_oneof![3 => Just(0x01u8), 1 => 0u8..=3, 1 => any::<u8>()],
        kind in prop_oneof![3 => Just(0x01u8), 1 => 0u8..=3, 1 => any::<u8>()],
        dh in prop_oneof![2 => Just(None), 1 => respelled_key().prop_map(Some)],
        type_byte in prop_oneof![3 => Just(None), 1 => (0u8..=8).prop_map(Some), 1 => any::<u8>().prop_map(Some)],
        presence in prop_oneof![3 => Just(None), 1 => (0u8..=3).prop_map(Some), 1 => any::<u8>().prop_map(Some)],
        padding in prop_oneof![3 => Just(None), 1 => (0usize..34, 1u8..=255).prop_map(Some)],
        cut in 0usize..103,
    ) {
        let mut b = encode_composite(&h);
        b[0] = version;
        b[1] = kind;
        if let Some(k) = dh {
            b[2..34].copy_from_slice(&k);
        }
        if let Some(t) = type_byte {
            b[66] = t;
        }
        if let Some(p) = presence {
            b[67] = p;
        }
        if let Some((at, v)) = padding {
            b[68 + at] = v;
        }
        let expected = reference_composite_valid(&b);
        match decode_composite(&b) {
            Ok((back, rest)) => {
                prop_assert!(expected, "accepted a header the page refuses");
                prop_assert!(rest.is_empty());
                prop_assert_eq!(encode_composite(&back), b.clone(), "a second spelling");
            }
            Err(_) => prop_assert!(!expected, "refused a header the page accepts"),
        }
        if cut < 102 {
            prop_assert!(decode_composite(&b[..cut]).is_err(), "a short header decoded");
        }
    }

    /// The bundle is the page's 1,811 bytes with an ML-KEM-1024 prekey, field by field
    /// at the page's offsets, and it decodes back to itself.
    ///
    /// Specification: message-format.md, Prekey bundle: "bundle = version ||
    /// type=0x03 || identity_key (32) || signed_prekey (32) || signed_prekey_signature
    /// (64) || kem_prekey_len (4, big-endian) || kem_prekey || kem_prekey_signature
    /// (64) || one_time_prekey_present (1) || one_time_prekey (32) || signed_prekey_id
    /// (4, big-endian) || one_time_prekey_id (4, big-endian) || kem_prekey_id (4,
    /// big-endian)" and "A bundle is 1,811 bytes with that KEM."
    #[test]
    fn the_bundle_has_the_pages_layout_and_round_trips(b in bundle()) {
        let e = encode_bundle(&b);
        prop_assert_eq!(e.len(), 1811);
        prop_assert_eq!(&e[..2], &[0x01, 0x03][..]);
        prop_assert_eq!(&e[2..34], &b.identity_key[..]);
        prop_assert_eq!(&e[34..66], &b.signed_prekey[..]);
        prop_assert_eq!(&e[66..130], &b.signed_prekey_signature[..]);
        prop_assert_eq!(&e[130..134], &1568u32.to_be_bytes()[..]);
        prop_assert_eq!(&e[134..1702], &b.kem_prekey[..]);
        prop_assert_eq!(&e[1702..1766], &b.kem_prekey_signature[..]);
        match b.one_time_prekey {
            None => {
                prop_assert_eq!(e[1766], 0x00);
                prop_assert!(e[1767..1799].iter().all(|x| *x == 0));
            }
            Some(k) => {
                prop_assert_eq!(e[1766], 0x01);
                prop_assert_eq!(&e[1767..1799], &k[..]);
            }
        }
        prop_assert_eq!(&e[1799..1803], &b.signed_prekey_id.to_be_bytes()[..]);
        prop_assert_eq!(&e[1803..1807], &b.one_time_prekey_id.to_be_bytes()[..]);
        prop_assert_eq!(&e[1807..1811], &b.kem_prekey_id.to_be_bytes()[..]);
        prop_assert_eq!(decode_bundle(&e), Ok(b));
    }

    /// One flipped bit anywhere in a valid bundle: the result decodes only if it is
    /// the one spelling of what it decodes to; a flip inside a signature, the KEM
    /// prekey or an identifier always decodes (the decoder does not judge them); a
    /// flip in the framing, the length prefix or the padding behind an absent
    /// one-time prekey never does; and a key flipped to a non-canonical value is
    /// refused.
    ///
    /// Specification: message-format.md, Principles: "**Canonical.** Exactly one valid
    /// encoding of a given message"; Prekey bundle: "a decoder refuses a
    /// `kem_prekey_len` other than the encapsulation-key length", "When the presence
    /// byte is `0x00` the 32 bytes must be zero and a decoder refuses anything else",
    /// "a presence byte other than `0x00` or `0x01` is refused too" and "A decoder also
    /// refuses a bundle whose `identity_key`, `signed_prekey` or present
    /// `one_time_prekey` is not the canonical encoding of a curve public key"; Key
    /// identifiers are not read by the decoder ("Nor does the decoder look at the
    /// identifier values", Initial message, applied here to the bundle's identifiers).
    #[test]
    fn a_flipped_bundle_decodes_only_as_its_one_spelling(
        b in bundle(),
        at in 0usize..1811,
        bit in 0u8..8,
    ) {
        let mut e = encode_bundle(&b);
        e[at] ^= 1 << bit;
        let got = decode_bundle(&e);
        let free = (66..130).contains(&at) || (134..1766).contains(&at) || at >= 1799;
        let fixed = at < 2 || (130..134).contains(&at)
            || (b.one_time_prekey.is_none() && (1767..1799).contains(&at));
        let key = |r: std::ops::Range<usize>| r.contains(&at) && !canonical(&e[r.clone()]);
        let presence_bad = e[1766] > 1;
        let otpk_bad = e[1766] == 1 && !canonical(&e[1767..1799]);
        if free {
            prop_assert!(got.is_ok(), "a flip in an unjudged field was refused");
        }
        if fixed || key(2..34) || key(34..66) || presence_bad || otpk_bad {
            prop_assert!(got.is_err(), "a flip the page refuses decoded");
        }
        if let Ok(back) = got {
            prop_assert_eq!(encode_bundle(&back), e, "a second spelling");
        }
    }

    /// A bundle whose `identity_key`, `signed_prekey` or present `one_time_prekey` is
    /// re-spelled (bit 255 set, or a value from p up) is refused, and so is a bundle
    /// whose KEM prekey, with its length prefix written to match, is any length but
    /// 1,568 bytes.
    ///
    /// Specification: message-format.md, Prekey bundle: "A decoder also refuses a
    /// bundle whose `identity_key`, `signed_prekey` or present `one_time_prekey` is not
    /// the canonical encoding of a curve public key ..., as a decode failure" and "a
    /// decoder refuses a `kem_prekey_len` other than the encapsulation-key length of
    /// the KEM it expects, as a decode failure."
    #[test]
    fn a_respelled_key_or_another_kem_length_is_refused(
        b in bundle(),
        which in 0u8..3,
        k in respelled_key(),
        kem_len in (0usize..1700).prop_filter("not 1568", |n| *n != 1568),
    ) {
        let mut respelled = b.clone();
        match which {
            0 => respelled.identity_key = k,
            1 => respelled.signed_prekey = k,
            _ => respelled.one_time_prekey = Some(k),
        }
        prop_assert!(decode_bundle(&encode_bundle(&respelled)).is_err());
        let mut other = b;
        other.kem_prekey = vec![0x5a; kem_len];
        prop_assert!(decode_bundle(&encode_bundle(&other)).is_err());
    }

    /// Any bundle with bytes appended, or cut short, is refused.
    ///
    /// Specification: message-format.md, Prekey bundle: "Trailing bytes are rejected:
    /// a bundle is a whole object, not a prefix of a stream."
    #[test]
    fn a_bundle_with_trailing_or_missing_bytes_is_refused(
        b in bundle(),
        tail in prop::collection::vec(any::<u8>(), 1..40),
        cut in 0usize..1811,
    ) {
        let e = encode_bundle(&b);
        let mut longer = e.clone();
        longer.extend_from_slice(&tail);
        prop_assert!(decode_bundle(&longer).is_err());
        prop_assert!(decode_bundle(&e[..cut]).is_err());
    }

    /// An initial message is the page's layout, and it decodes back to its fields for
    /// every `EncodeEC` identity and ephemeral with canonical keys, every KEM
    /// ciphertext length (the decoder does not check it), every identifier and every
    /// trailing ratchet message, empty and not a ratchet message included; with an
    /// `identity` or `ephemeral` re-spelled, or carrying another first byte, it does
    /// not decode.
    ///
    /// Specification: message-format.md, Initial message: "initial = version ||
    /// type=0x02 || identity (33) || ephemeral (33) || kem_ciphertext_len (4,
    /// big-endian) || kem_ciphertext || signed_prekey_id (4, big-endian) ||
    /// one_time_prekey_id (4, big-endian) || kem_prekey_id (4, big-endian) ||
    /// ratchet_message", "Everything after `kem_prekey_id` is `ratchet_message`, and
    /// the initial-message decoder does not validate it", "The decoder does not check
    /// `kem_ciphertext`'s length either", and "It also refuses an `identity` or
    /// `ephemeral` whose first byte is not the `EncodeEC` curve byte ..., and an
    /// `identity` or `ephemeral` whose thirty-two key bytes are not the canonical
    /// encoding of a curve public key".
    #[test]
    fn the_initial_message_round_trips_and_refuses_respelled_keys(
        ik in canonical_key(),
        ek in canonical_key(),
        ct in prop::collection::vec(any::<u8>(), 0..1600),
        ids in (any::<u32>(), any::<u32>(), any::<u32>()),
        message in prop::collection::vec(any::<u8>(), 0..200),
        bad in prop_oneof![
            2 => Just(None),
            1 => (any::<bool>(), respelled_key(), Just(0x05u8)).prop_map(Some),
            1 => (any::<bool>(), canonical_key(), (0u8..=255).prop_filter("not 0x05", |b| *b != 0x05))
                .prop_map(Some),
        ],
    ) {
        let enc = |k: &[u8; 32], first: u8| {
            let mut v = vec![first];
            v.extend_from_slice(k);
            v
        };
        let (mut identity, mut ephemeral) = (enc(&ik, 0x05), enc(&ek, 0x05));
        if let Some((which, k, first)) = bad {
            if which { identity = enc(&k, first) } else { ephemeral = enc(&k, first) }
        }
        let e = encode_initial(&identity, &ephemeral, &ct, ids.0, ids.1, ids.2, &message);
        prop_assert_eq!(e.len(), 2 + 33 + 33 + 4 + ct.len() + 12 + message.len());
        prop_assert_eq!(&e[..2], &[0x01, 0x02][..]);
        prop_assert_eq!(&e[68..72], &(ct.len() as u32).to_be_bytes()[..]);
        let got = decode_initial(&e);
        if bad.is_some() {
            prop_assert!(got.is_err(), "a re-spelled or mistyped key decoded");
        } else {
            let d = got.expect("a well-formed initial message decodes");
            prop_assert_eq!(d.identity, identity);
            prop_assert_eq!(d.ephemeral, ephemeral);
            prop_assert_eq!(d.kem_ciphertext, ct);
            prop_assert_eq!(
                (d.signed_prekey_id, d.one_time_prekey_id, d.kem_prekey_id),
                ids
            );
            prop_assert_eq!(d.message, message);
        }
    }

    /// An initial message is refused when it is cut anywhere before the end of its last
    /// identifier, when its version is not `0x01`, when its type byte is not `0x02`, and
    /// when its `kem_ciphertext_len` runs past the end of the input.
    ///
    /// Specification: message-format.md, Initial message: "A decoder refuses an initial
    /// message shorter than its two framing bytes, an unrecognised version, a type byte
    /// other than `0x02`, input that ends inside `identity`, `ephemeral`,
    /// `kem_ciphertext_len` or any of the three identifiers, and a `kem_ciphertext_len`
    /// that runs past the end of the input."
    #[test]
    fn an_initial_message_is_refused_as_the_page_lists(
        ik in canonical_key(),
        ek in canonical_key(),
        ct in prop::collection::vec(any::<u8>(), 0..64),
        message in prop::collection::vec(any::<u8>(), 0..64),
        cut in any::<prop::sample::Index>(),
        version in prop_oneof![0u8..=4, any::<u8>()].prop_filter("not 0x01", |v| *v != 0x01),
        kind in prop_oneof![0u8..=4, any::<u8>()].prop_filter("not 0x02", |k| *k != 0x02),
        over in 1u32..100,
    ) {
        let enc = |k: &[u8; 32]| {
            let mut v = vec![0x05];
            v.extend_from_slice(k);
            v
        };
        let e = encode_initial(&enc(&ik), &enc(&ek), &ct, 1, 2, 3, &message);
        prop_assert!(decode_initial(&e).is_ok(), "the unaltered message decodes");
        let fixed = 2 + 33 + 33 + 4 + ct.len() + 12;
        prop_assert!(decode_initial(&e[..cut.index(fixed)]).is_err(), "a cut message decoded");
        let mut b = e.clone();
        b[0] = version;
        prop_assert!(decode_initial(&b).is_err(), "another version decoded");
        let mut b = e.clone();
        b[1] = kind;
        prop_assert!(decode_initial(&b).is_err(), "another type decoded");
        let mut b = e.clone();
        let past = (ct.len() + 12 + message.len()) as u32 + over;
        b[68..72].copy_from_slice(&past.to_be_bytes());
        prop_assert!(decode_initial(&b).is_err(), "a KEM ciphertext length past the end decoded");
    }

    /// A byte string's framing names its type: version `0x01` with type `0x01` is a
    /// ratchet message and with type `0x02` an initial message; anything else (an
    /// empty or one-byte string, another version, a bundle's `0x03`, any other type)
    /// is neither, whatever follows.
    ///
    /// Specification: message-format.md, Message type: "Every message begins with a
    /// version byte and a type byte, so a receiver can tell what it is holding without
    /// relying on the session state", the table "`type = 0x01` ratchet message, `type =
    /// 0x02` initial (prekey) message, `type = 0x03` prekey bundle", and "a decoder
    /// should reject a bundle handed to it as a message on the type byte".
    #[test]
    fn the_framing_names_the_message_type(
        version in prop_oneof![Just(0x01u8), any::<u8>()],
        kind in prop_oneof![0u8..=4, any::<u8>()],
        rest in prop::collection::vec(any::<u8>(), 0..8),
        short in 0usize..3,
    ) {
        let mut b = vec![version, kind];
        b.extend_from_slice(&rest);
        let expected = match (version, kind) {
            (0x01, 0x01) => Some(MessageType::Ratchet),
            (0x01, 0x02) => Some(MessageType::Initial),
            _ => None,
        };
        prop_assert_eq!(message_type(&b), expected);
        if short < 2 {
            prop_assert_eq!(message_type(&b[..short]), None);
        }
    }
}
