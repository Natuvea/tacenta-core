//! Two canonicality properties of `from_bytes`, pinned by executable tests
//! rather than by a paragraph.
//!
//! Both are about `from_bytes` accepting a byte string that `to_bytes` could
//! never have produced.
//!
//! **They are `#[ignore]` because the decoder is not where the properties are
//! enforced.** `Session::import` is the trust boundary: it re-encodes and
//! compares, so a non-canonical spelling is refused before it becomes live
//! state. This decoder sits inside the verified zone, where a change re-runs
//! Charon and Aeneas and reopens the T1 and T3 theorems. The padding check is
//! enforced here as well; the counter check is not.
//!
//! What these two tests document is the decoder-level form of each property:
//! what `from_bytes` accepts on its own, as distinct from what
//! `Session::import` accepts. A caller that decodes with this crate directly
//! rather than through `Session::import` gets the decoder-level behaviour.
//!
//! Run them deliberately with:  cargo test -p tacenta-ratchet -- --ignored

use tacenta_ratchet::{LabelSet, State, init_receiver};

fn a_receiver() -> State {
    init_receiver(&[7u8; 32], [9u8; 32], LabelSet::Tacenta)
}

/// **Absent-field padding must be canonical.**
///
/// An absent optional key encodes as a `0x00` tag followed by 32 zero bytes.
/// A decoder that returned `None` on the tag without reading the 32 bytes
/// would accept any padding as the same state: two distinct byte strings, one
/// value, in a format whose own comment says "a canonical encoding is
/// provable".
#[test]
#[ignore = "the property is enforced at Session::import; this is the decoder-level form"]
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

/// **Import accepts counters the totality proofs assume cannot occur.**
///
/// T1 for the ratchet carries the precondition that the message counters stay
/// below their width. `from_bytes` sets them from the buffer with no check, so
/// an imported state can start one increment from wrapping -- which is a
/// precondition of the proof being established by an input rather than held.
#[test]
#[ignore = "the property is enforced at Session::import; this is the decoder-level form"]
fn saturated_counters_must_be_rejected_on_import() {
    let clean = a_receiver().to_bytes().to_vec();

    // ns, nr, pn are three 4-byte counters after version + dhs_pub + dhr_pub
    // + rk + cks + ckr.
    let ns = 1 + 32 + 33 + 32 + 33 + 33;
    let mut dirty = clean.clone();
    dirty[ns..ns + 4].copy_from_slice(&u32::MAX.to_be_bytes());

    assert!(
        State::from_bytes(&dirty).is_err(),
        "a saturated send counter must not decode"
    );
}
