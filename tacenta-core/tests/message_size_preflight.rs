//! The size rule's arithmetic on length values, not allocations (tacenta-spec/protocol/message-format.md,
//! Message size). **Tested only; this is not a proof.**
//!
//! `nested_ratchet_len`, `ratchet_span_of` and `frame_too_long` take the values the rule reads (a frame length,
//! whether the frame is an initial one, its `kem_ciphertext_len`), so they can be driven at lengths no buffer
//! could have: up to `usize::MAX`, where `84 + kem_ciphertext_len` overflows a 32-bit `usize`. Each is compared
//! with a reference computed in `u128`, which cannot overflow for these operands on any target the crate
//! builds for. The same tests run on the 64-bit hosts and on the 32-bit i686 CI job, so the checked addition is
//! exercised at both widths.
//!
//! `check_frame_size` and `ratchet_span`, which read real bytes, are compared with the value functions on
//! small frames whose first bytes and length are generated.

use proptest::prelude::*;
use tacenta_core::serialization::{
    DecodeError, MAX_INITIAL_FRAME_LEN, MAX_RATCHET_FRAME_LEN, check_frame_size, decode_initial,
    frame_too_long, nested_ratchet_len, ratchet_span, ratchet_span_of,
};

/// The reference: `84 + k <= len` and `len - 84 - k`, in a width that cannot overflow.
fn reference_nested(len: usize, k: u32) -> Option<usize> {
    let start = 84u128 + u128::from(k);
    let len = len as u128;
    if start <= len {
        Some((len - start) as usize)
    } else {
        None
    }
}

fn reference_too_long(len: usize, initial: bool, k: Option<u32>) -> bool {
    if len as u128 > MAX_INITIAL_FRAME_LEN as u128 {
        return true;
    }
    let span = if initial {
        match k {
            Some(k) => reference_nested(len, k),
            None => None,
        }
    } else {
        Some(len)
    };
    match span {
        Some(s) => s as u128 > MAX_RATCHET_FRAME_LEN as u128,
        None => false,
    }
}

/// Lengths around every edge the rule has, and around the top of `usize`.
fn edge_lengths() -> Vec<usize> {
    let mut out = Vec::new();
    for base in [
        0usize,
        72,
        84,
        84 + 1568,
        MAX_RATCHET_FRAME_LEN,
        MAX_RATCHET_FRAME_LEN + 84,
        MAX_INITIAL_FRAME_LEN,
        u32::MAX as usize,
        usize::MAX,
    ] {
        for delta in 0..3usize {
            out.push(base.saturating_add(delta));
            out.push(base.saturating_sub(delta));
        }
    }
    out
}

fn edge_kem_lengths() -> Vec<u32> {
    vec![
        0,
        1,
        1567,
        1568,
        1569,
        (MAX_INITIAL_FRAME_LEN - 84 - MAX_RATCHET_FRAME_LEN) as u32,
        u32::MAX - 84,
        u32::MAX - 83,
        u32::MAX - 1,
        u32::MAX,
    ]
}

#[test]
fn the_value_functions_agree_with_the_reference_at_every_edge() {
    for &len in &edge_lengths() {
        for &k in &edge_kem_lengths() {
            assert_eq!(
                nested_ratchet_len(len, k),
                reference_nested(len, k),
                "len {len}, k {k}"
            );
            assert_eq!(
                frame_too_long(len, true, Some(k)),
                reference_too_long(len, true, Some(k)),
                "initial, len {len}, k {k}"
            );
        }
        assert_eq!(
            frame_too_long(len, true, None),
            reference_too_long(len, true, None)
        );
        assert_eq!(
            frame_too_long(len, false, None),
            reference_too_long(len, false, None)
        );
        assert_eq!(ratchet_span_of(len, false, None), Some(len));
        assert_eq!(ratchet_span_of(len, true, None), None);
    }
}

/// At the top of `usize` the addition must not wrap: on a 32-bit target `84 + u32::MAX` does not fit, and the
/// field is then taken as running past the end of any frame. On a 64-bit target it fits, and only a frame that
/// long could hold it.
#[test]
fn the_kem_length_addition_does_not_wrap_at_the_top_of_usize() {
    let fits = 84usize.checked_add(u32::MAX as usize);
    match fits {
        None => {
            // 32-bit: every frame length gives no span, never a wrapped small one.
            assert_eq!(nested_ratchet_len(usize::MAX, u32::MAX), None);
            assert_eq!(nested_ratchet_len(83, u32::MAX), None);
            assert_eq!(nested_ratchet_len(0, u32::MAX), None);
        }
        Some(start) => {
            assert_eq!(nested_ratchet_len(start, u32::MAX), Some(0));
            assert_eq!(nested_ratchet_len(start - 1, u32::MAX), None);
            assert_eq!(
                nested_ratchet_len(usize::MAX, u32::MAX),
                Some(usize::MAX - start)
            );
        }
    }
    // Whatever the width, a frame of `usize::MAX` bytes is refused by the outer bound.
    assert!(frame_too_long(usize::MAX, true, Some(u32::MAX)));
    assert!(frame_too_long(usize::MAX, true, None));
    assert!(frame_too_long(usize::MAX, false, None));
}

#[test]
fn the_three_rules_at_their_edges() {
    // Rule 1.
    assert!(!frame_too_long(MAX_INITIAL_FRAME_LEN, true, Some(1568)));
    assert!(frame_too_long(MAX_INITIAL_FRAME_LEN + 1, true, Some(1568)));
    assert!(frame_too_long(
        MAX_INITIAL_FRAME_LEN + 1,
        true,
        Some(u32::MAX)
    ));
    assert!(frame_too_long(MAX_INITIAL_FRAME_LEN + 1, true, None));
    // Rule 2: the ratchet message located through the frame's own length field.
    assert!(!frame_too_long(84 + MAX_RATCHET_FRAME_LEN, true, Some(0)));
    assert!(frame_too_long(
        84 + MAX_RATCHET_FRAME_LEN + 1,
        true,
        Some(0)
    ));
    assert!(frame_too_long(MAX_INITIAL_FRAME_LEN, true, Some(0)));
    assert!(frame_too_long(MAX_INITIAL_FRAME_LEN, true, Some(1567)));
    assert!(!frame_too_long(MAX_INITIAL_FRAME_LEN, true, Some(1568)));
    // A field that runs past the end locates nothing: only rule 1 applies.
    assert!(!frame_too_long(MAX_INITIAL_FRAME_LEN, true, Some(u32::MAX)));
    assert!(!frame_too_long(71, true, None));
    // Rule 3.
    assert!(!frame_too_long(MAX_RATCHET_FRAME_LEN, false, None));
    assert!(frame_too_long(MAX_RATCHET_FRAME_LEN + 1, false, None));
}

/// Declared KEM-ciphertext lengths other than ML-KEM-1024's 1,568, and that one for comparison. The nested
/// check locates the ratchet message through whatever the frame declares (message-format.md, Message size,
/// rule 2), so none of these may be treated as 1,568.
const DECLARED_KEM_LENGTHS: [u32; 7] = [0, 1, 1567, 1568, 1569, 70_000, u32::MAX];

/// The rule computed as a target with a 32-bit `usize` computes it: lengths are `u32`, and an `84 + k` that
/// `u32` cannot hold is taken as running past the end, so it locates nothing.
fn reference_32(len: u32, k: u32) -> bool {
    if u64::from(len) > MAX_INITIAL_FRAME_LEN as u64 {
        return true;
    }
    match 84u32.checked_add(k) {
        Some(start) if start <= len => u64::from(len - start) > MAX_RATCHET_FRAME_LEN as u64,
        _ => false,
    }
}

/// An initial frame of `len` bytes whose `kem_ciphertext_len` declares `k`: version, type, two well-formed
/// zero keys, the field, then zeros. Allocated, so `check_frame_size` and the decoder read real bytes.
fn initial_frame(len: usize, k: u32) -> Vec<u8> {
    let mut frame = vec![0u8; len];
    frame[0] = 0x01;
    frame[1] = 0x02;
    frame[2] = 0x05;
    frame[35] = 0x05;
    frame[68..72].copy_from_slice(&k.to_be_bytes());
    frame
}

/// The nested check does not assume a KEM length: for each declared length, the length-only call (made at
/// lengths a 32-bit target can hold, against that target's arithmetic) and the byte check agree with the rule,
/// and the bound that applies is the one the declared length gives. Acceptance of these lengths by the
/// initial-message decoder is unchanged here; whether a length other than 1,568 should be refused is a
/// separate decision, which the page leaves open.
#[test]
fn the_nested_check_does_not_assume_the_kem_length() {
    for &k in &DECLARED_KEM_LENGTHS {
        // The length at which the located ratchet message reaches MAX_RATCHET_FRAME_LEN, where it exists.
        let nested_edge = 84u64 + u64::from(k) + MAX_RATCHET_FRAME_LEN as u64;
        let mut lengths: Vec<u64> = vec![
            0,
            71,
            72,
            83 + u64::from(k),
            84 + u64::from(k),
            85 + u64::from(k),
            MAX_RATCHET_FRAME_LEN as u64,
            MAX_INITIAL_FRAME_LEN as u64 - 1,
            MAX_INITIAL_FRAME_LEN as u64,
            MAX_INITIAL_FRAME_LEN as u64 + 1,
            nested_edge - 1,
            nested_edge,
            nested_edge + 1,
            u64::from(u32::MAX),
        ];
        lengths.retain(|&l| l <= u64::from(u32::MAX));
        for &len in &lengths {
            let len32 = len as u32;
            assert_eq!(
                frame_too_long(len32 as usize, true, Some(k)),
                reference_32(len32, k),
                "k {k}, len {len}: the length-only call differs from 32-bit arithmetic"
            );
        }

        // The bound that binds: the nested one while 84 + k + MAX_RATCHET_FRAME_LEN fits within
        // MAX_INITIAL_FRAME_LEN, the outer one otherwise. Real frames at each edge.
        if nested_edge <= MAX_INITIAL_FRAME_LEN as u64 {
            let edge = nested_edge as usize;
            assert_eq!(check_frame_size(&initial_frame(edge, k)), Ok(()), "k {k}");
            assert_eq!(
                ratchet_span(&initial_frame(edge, k)),
                Some(MAX_RATCHET_FRAME_LEN),
                "k {k}"
            );
            assert_eq!(
                check_frame_size(&initial_frame(edge + 1, k)),
                Err(DecodeError::TooLong),
                "k {k}: one byte more inside is refused by the nested rule"
            );
        } else {
            let at = initial_frame(MAX_INITIAL_FRAME_LEN, k);
            assert_eq!(check_frame_size(&at), Ok(()), "k {k}");
            let span = (MAX_INITIAL_FRAME_LEN as u64).checked_sub(84 + u64::from(k));
            assert_eq!(
                ratchet_span(&at).map(|s| s as u64),
                span,
                "k {k}: the span is what the declared length locates, or none"
            );
            assert_eq!(
                check_frame_size(&initial_frame(MAX_INITIAL_FRAME_LEN + 1, k)),
                Err(DecodeError::TooLong),
                "k {k}: one byte over the outer bound"
            );
        }
    }
    // For the honest length the two rules meet at MAX_INITIAL_FRAME_LEN.
    assert_eq!(
        84 + 1568 + MAX_RATCHET_FRAME_LEN,
        MAX_INITIAL_FRAME_LEN,
        "the honest wrapper"
    );
}

/// What the decoder accepts is not changed by the size rule: an initial frame declaring any of these
/// lengths, with room for its fields, decodes with a `kem_ciphertext` of that length, and one whose length
/// runs past the end is refused as before. Pinned so that a change to KEM-length acceptance is a visible,
/// separate decision rather than a side effect of the size rule.
#[test]
fn the_size_rule_leaves_kem_length_acceptance_unchanged() {
    for &k in &[0u32, 1, 1567, 1568, 1569, 70_000] {
        let frame = initial_frame(84 + k as usize + 10, k);
        assert_eq!(check_frame_size(&frame), Ok(()), "k {k}");
        let decoded = decode_initial(&frame).expect("a declared KEM length with room decodes");
        assert_eq!(decoded.kem_ciphertext.len(), k as usize, "k {k}");
        assert_eq!(decoded.message.len(), 10, "k {k}");
    }
    let overrun = initial_frame(2000, u32::MAX);
    assert_eq!(check_frame_size(&overrun), Ok(()));
    assert_eq!(
        decode_initial(&overrun).err(),
        Some(DecodeError::LengthOverrun)
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4096))]

    #[test]
    fn nested_len_matches_the_reference(len in any::<usize>(), k in any::<u32>()) {
        prop_assert_eq!(nested_ratchet_len(len, k), reference_nested(len, k));
    }

    #[test]
    fn too_long_matches_the_reference(
        len in any::<usize>(),
        initial in any::<bool>(),
        k in proptest::option::of(any::<u32>()),
    ) {
        prop_assert_eq!(frame_too_long(len, initial, k), reference_too_long(len, initial, k));
    }

    #[test]
    fn too_long_matches_the_reference_near_the_bounds(
        len in (MAX_RATCHET_FRAME_LEN - 4000)..(MAX_INITIAL_FRAME_LEN + 4000),
        k in 0u32..4000,
    ) {
        prop_assert_eq!(frame_too_long(len, true, Some(k)), reference_too_long(len, true, Some(k)));
        prop_assert_eq!(frame_too_long(len, false, None), reference_too_long(len, false, None));
    }

    /// The byte functions read exactly what the value functions take: the length, the first two bytes and,
    /// for an initial frame of at least 72 bytes, bytes 68 to 71.
    #[test]
    fn the_byte_functions_read_what_the_value_functions_take(
        head in proptest::collection::vec(any::<u8>(), 0..120),
        version in prop_oneof![Just(0x01u8), any::<u8>()],
        kind in prop_oneof![Just(0x01u8), Just(0x02u8), any::<u8>()],
    ) {
        let mut frame = head;
        if frame.len() >= 2 {
            frame[0] = version;
            frame[1] = kind;
        }
        let initial = frame.len() >= 2 && frame[0] == 0x01 && frame[1] == 0x02;
        let k = if initial && frame.len() >= 72 {
            Some(u32::from_be_bytes([frame[68], frame[69], frame[70], frame[71]]))
        } else {
            None
        };
        prop_assert_eq!(ratchet_span(&frame), ratchet_span_of(frame.len(), initial, k));
        let expected = if frame_too_long(frame.len(), initial, k) {
            Err(DecodeError::TooLong)
        } else {
            Ok(())
        };
        prop_assert_eq!(check_frame_size(&frame), expected);
    }
}
