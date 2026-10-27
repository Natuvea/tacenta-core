//! The size rule at its edges (tacenta-spec/protocol/message-format.md, Message size): frames around
//! `MAX_RATCHET_FRAME_LEN` and `MAX_INITIAL_FRAME_LEN`, and re-wrapped repeats whose declared KEM length moves
//! the nested ratchet message across its bound, given to `Session::decrypt` and `establish_responder`.
//!
//! The input is a short description of a frame of up to `MAX_INITIAL_FRAME_LEN + 64` bytes, expanded before it
//! is received (`../frame_size_entry.rs` says how), so this target reaches 1,050,363 bytes and beyond with the
//! default `-max_len`. Its oracle is the rule itself, computed independently in the harness: a frame the rule
//! refuses must be refused by both entries as `Decode(TooLong)` with no random draw and no change to the
//! session or the store, and a frame it admits must not be refused as too long by either.
//!
//! Kept separate from `session_receive`, whose fast small-input campaign is unchanged. The committed seeds
//! sit at, one below and one above both bounds, sixteen and fifteen bytes either side (one padding block), and
//! on the nested cases; `tacenta-core/tests/fuzz_frame_size_seeds.rs` runs them through the same entry and
//! requires every branch to be taken.

#![no_main]

use libfuzzer_sys::fuzz_target;

#[allow(
    dead_code,
    reason = "the seed-corpus test uses the rest of the entry module"
)]
#[path = "../frame_size_entry.rs"]
mod frame_size_entry;

fuzz_target!(|data: &[u8]| {
    let _ = frame_size_entry::run(data);
});
