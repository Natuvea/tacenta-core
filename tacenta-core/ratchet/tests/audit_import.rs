//! Two decoder-level properties of `from_bytes`, pinned by executable tests
//! rather than by a paragraph.
//!
//! Both are about `from_bytes` accepting a byte string that `to_bytes` could
//! never have produced, and what happens next. They are tests of the decoder
//! alone: `Session::import`, the trust boundary above it, re-encodes and
//! compares, which refuses a non-canonical spelling, and adds no check of its
//! own beyond that. An earlier version of this file said the import enforced
//! a counter bound and kept both tests ignored on that basis; it did not, and
//! they are not (CR-28).
//!
//! **Padding is canonical, and the decoder enforces it.** An absent optional
//! key is a `0x00` tag and 32 zero bytes, and `read_optional_key` refuses
//! anything else behind the tag. The first test pins that.
//!
//! **Counters are not bounded at decode, and need not be.** `from_bytes`
//! takes `ns`, `nr` and `pn` from the buffer as they are. The T1 theorems for
//! the operations carry no precondition on them: every increment is
//! `checked_add` and reports `ChainExhausted` rather than wrapping, so a
//! state restored one step from the ceiling decodes, and then refuses. The
//! second test pins that shape -- decode, then refuse, never panic -- since
//! it is the reason no decoder-level bound is required.
//!
//! A caller that decodes with this crate directly rather than through
//! `Session::import` gets exactly this behaviour and no more.

use tacenta_ratchet::{LabelSet, RatchetError, State, init_receiver, init_sender, send};

fn a_receiver() -> State {
    init_receiver(&[7u8; 32], [9u8; 32], LabelSet::Tacenta)
}

fn a_sender() -> State {
    init_sender(
        &[7u8; 32],
        [8u8; 32],
        [9u8; 32],
        &[6u8; 32],
        LabelSet::Tacenta,
    )
}

/// **Absent-field padding must be canonical.**
///
/// An absent optional key encodes as a `0x00` tag followed by 32 zero bytes.
/// A decoder that returned `None` on the tag without reading the 32 bytes
/// would accept any padding as the same state: two distinct byte strings, one
/// value, in a format whose own comment says "a canonical encoding is
/// provable".
#[test]
fn absent_key_padding_must_be_rejected() {
    let clean = a_receiver().to_bytes().to_vec();

    // Byte 1 is dhs_pub's first byte; the first optional key follows the
    // 32-byte dhs_pub, so its tag is at 1 + 32 = 33.
    let tag = 1 + 32;
    assert_eq!(clean[tag], 0x00, "a fresh receiver has dhr_pub absent");

    let mut dirty = clean.clone();
    dirty[tag + 1] = 0xAA;
    assert_ne!(clean, dirty);

    assert!(
        State::from_bytes(&dirty).is_err(),
        "non-zero padding behind an absent tag must not decode"
    );
}

/// **A saturated counter decodes, and the next step refuses.**
///
/// `from_bytes` sets the counters from the buffer with no check, so an
/// imported state can start one increment from wrapping. That is safe only
/// because the increment is checked: the send on such a state must report
/// `ChainExhausted`, not wrap to zero and re-derive a key already used, and
/// not panic. This pins the property the absence of a decode-time bound
/// rests on.
#[test]
fn a_saturated_counter_decodes_and_then_refuses() {
    let clean = a_sender().to_bytes().to_vec();

    // ns is the first of three 4-byte counters after version + dhs_pub +
    // dhr_pub + rk + cks + ckr.
    let ns = 1 + 32 + 33 + 32 + 33 + 33;
    let mut dirty = clean.clone();
    dirty[ns..ns + 4].copy_from_slice(&u32::MAX.to_be_bytes());

    let mut state = State::from_bytes(&dirty).expect("the counter is not bounded at decode");
    assert_eq!(state.send_count(), u32::MAX);
    assert!(
        matches!(send(&mut state), Err(RatchetError::ChainExhausted)),
        "a saturated send counter must refuse rather than wrap"
    );
}
