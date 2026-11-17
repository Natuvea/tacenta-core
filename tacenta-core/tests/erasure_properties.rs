//! Property tests for the erasure code of `tacenta-erasure` against
//! `tacenta-spec/protocol/mlkem-braid.md`, The erasure code: the field operations
//! (`gf::add`, `gf::mul`, `gf::pow`, `gf::inv`), the codewords an `Encoder` issues
//! past the systematic ones, and a `Decoder` fed codewords at arbitrary distinct
//! indices up to 65,535, with repeats.
//!
//! The oracle is written here from the page's sentences: a carry-less product reduced
//! by `0x1100B` done bit by bit, division as multiplication by `a^(2^16 - 2)`, and the
//! page's Lagrange sums for a codeword and for a decoded chunk evaluated with that
//! reference field. It shares no code with the crate. The `tests` module of
//! `erasure/src/lib.rs` compares the crate's interpolation with its own barycentric
//! form and checks reconstruction from the encoder's own codewords; what is added here
//! is a check against the page's formulas, at indices those tests do not reach.
//!
//! Case count: `CASES` (256) per property when `PROPTEST_CASES` is unset. `PROPTEST_CASES`
//! overrides it (proptest reads the variable over the configuration given here), and the
//! hosted `rust` job and `tooling/ci.sh` set it to 2,048, so that is the count CI runs.
//! Replay: proptest shrinks a failing case and
//! prints the minimal input in the failure message, and its default failure
//! persistence writes the failing case's seed to `erasure_properties.proptest-regressions`
//! beside this file, which the next local run replays first. No regressions file is
//! committed and the generator's seed is not fixed, so a run that fails in CI is
//! replayed from the minimal input its log prints.

use proptest::prelude::*;
use tacenta_erasure::{Chunk, Decoder, Encoder, gf};

/// The number of generated cases each property runs.
const CASES: u32 = 256;

fn config() -> ProptestConfig {
    ProptestConfig::with_cases(CASES)
}

/// The page's multiplication: the carry-less product of the two polynomials reduced
/// modulo x^16 + x^12 + x^3 + x + 1, one bit at a time.
fn ref_mul(a: u16, b: u16) -> u16 {
    let mut product: u32 = 0;
    for bit in 0..16 {
        if b >> bit & 1 == 1 {
            product ^= (a as u32) << bit;
        }
    }
    for bit in (16..32).rev() {
        if product >> bit & 1 == 1 {
            product ^= 0x1100B << (bit - 16);
        }
    }
    product as u16
}

fn ref_pow(a: u16, mut n: u32) -> u16 {
    let (mut base, mut acc) = (a, 1u16);
    while n > 0 {
        if n & 1 == 1 {
            acc = ref_mul(acc, base);
        }
        base = ref_mul(base, base);
        n >>= 1;
    }
    acc
}

/// "Division by a nonzero `a` is multiplication by `a^(2^16 - 2)`."
fn ref_div(x: u16, a: u16) -> u16 {
    ref_mul(x, ref_pow(a, 65534))
}

fn element(data: &[u8; 32], j: usize) -> u16 {
    u16::from_be_bytes([data[2 * j], data[2 * j + 1]])
}

/// The page's codeword formula: element j at index i is the sum over t of
/// element_j(chunk_t) * product over s != t of (i + s) / (t + s).
fn ref_codeword(chunks: &[[u8; 32]], i: u16) -> [u8; 32] {
    let k = chunks.len();
    let mut out = [0u8; 32];
    for j in 0..16 {
        let mut sum = 0u16;
        for (t, chunk) in chunks.iter().enumerate() {
            let mut term = element(chunk, j);
            for s in 0..k {
                if s != t {
                    term = ref_mul(term, ref_div(i ^ s as u16, t as u16 ^ s as u16));
                }
            }
            sum ^= term;
        }
        out[2 * j..2 * j + 2].copy_from_slice(&sum.to_be_bytes());
    }
    out
}

fn chunks_of(message: &[u8]) -> Vec<[u8; 32]> {
    message
        .chunks(32)
        .map(|c| {
            let mut b = [0u8; 32];
            b[..c.len()].copy_from_slice(c);
            b
        })
        .collect()
}

proptest! {
    #![proptest_config(config())]

    /// Addition is exclusive or; multiplication is the carry-less product reduced by
    /// `0x1100B`; `pow` is repeated multiplication; and `inv(a)` is `a^(2^16 - 2)`,
    /// with `a * inv(a) = 1` for every nonzero `a`.
    ///
    /// Specification: mlkem-braid.md, The erasure code, The field: "Addition is
    /// exclusive or. Multiplication is the carry-less product of the two polynomials
    /// reduced modulo `x^16 + x^12 + x^3 + x + 1` (`0x1100B`...). Division by a
    /// nonzero `a` is multiplication by `a^(2^16 - 2)`."
    #[test]
    fn the_field_is_the_pages(a in any::<u16>(), b in any::<u16>(), n in 0u32..70000) {
        prop_assert_eq!(gf::add(a, b), a ^ b);
        prop_assert_eq!(gf::mul(a, b), ref_mul(a, b));
        prop_assert_eq!(gf::pow(a, n), ref_pow(a, n));
        if a != 0 {
            prop_assert_eq!(gf::inv(a), ref_pow(a, 65534));
            prop_assert_eq!(gf::mul(a, gf::inv(a)), 1);
        }
    }

    /// For a value of 1 to 6 chunks, the encoder issues the chunks themselves at
    /// indices below `k`, and past them the codeword the page's polynomial formula
    /// gives, computed with the reference field. Each case steps the encoder to a
    /// generated index between `k` and `k + 299` and compares only the last three
    /// indices it issues with the formula (the reference is cubic in `k`), so the
    /// indices compared vary from case to case rather than all being checked in one.
    ///
    /// Specification: mlkem-braid.md, The erasure code, Codewords: "For `i < k` the
    /// bytes are `chunk_i`. For `i >= k`, element `j` of the bytes is `P_j(i)`" and
    /// "`P_j(x) = sum over t of element_j(chunk_t) * product over s != t of (x + s) /
    /// (t + s)`"; Chunks: "element `j` being bytes `2j` and `2j + 1` read big-endian".
    #[test]
    fn the_encoder_issues_the_pages_codewords(
        message in prop::collection::vec(any::<u8>(), 1..=192),
        upto in 0u16..300,
    ) {
        let chunks = chunks_of(&message);
        let k = chunks.len();
        let mut encoder = Encoder::new(&message);
        for i in 0..=(k as u16 + upto) {
            let c = encoder.next_chunk().expect("an encoder issues index after index");
            prop_assert_eq!(c.index, i);
            if (i as usize) < k {
                prop_assert_eq!(c.data, chunks[i as usize]);
            } else if i >= k as u16 + upto.saturating_sub(3) {
                // The reference is cubic in k; checking the last few indices of each
                // run keeps the count of reference evaluations bounded.
                prop_assert_eq!(c.data, ref_codeword(&chunks, i));
            }
        }
    }

    /// A decoder for an `n`-byte value, fed codewords computed from the page's formula
    /// at distinct indices anywhere in 0 to 65,535 (with a repeat at a held index
    /// carrying other bytes, and extra codewords after the `k`-th), keeps the first at
    /// each index, ignores the rest, and returns the value: the `k` chunks in order,
    /// truncated to `n` bytes.
    ///
    /// Specification: mlkem-braid.md, The erasure code, Decoding: "It keeps the first
    /// codeword it receives at each index; a later one at an index it already holds is
    /// ignored, even when its bytes differ, and once it holds `k` codewords every
    /// further one is ignored" and "The value is the `k` chunks in order, truncated to
    /// `n` bytes."
    #[test]
    fn a_decoder_recovers_the_value_from_any_k_distinct_indices(
        message in prop::collection::vec(any::<u8>(), 1..=160),
        picks in prop::collection::vec(any::<u16>(), 12),
        repeat_at in 0usize..12,
        noise in prop::array::uniform32(any::<u8>()),
    ) {
        let chunks = chunks_of(&message);
        let k = chunks.len();
        let mut indices: Vec<u16> = Vec::new();
        for p in picks {
            if !indices.contains(&p) {
                indices.push(p);
            }
        }
        prop_assume!(indices.len() > k);
        let mut decoder = Decoder::new(message.len());
        let code = |i: u16| if (i as usize) < k { chunks[i as usize] } else { ref_codeword(&chunks, i) };
        for (n, i) in indices.iter().take(k).enumerate() {
            let first = Chunk { index: *i, data: code(*i) };
            prop_assert!(decoder.add_chunk(first), "a first codeword was refused");
            if n == repeat_at % k {
                let held = indices[repeat_at % k];
                let mut other = code(held);
                other[0] ^= 1;
                other[31] ^= noise[0] | 1;
                prop_assert!(!decoder.add_chunk(Chunk { index: held, data: other }), "a repeat was kept");
            }
        }
        prop_assert!(decoder.has_message());
        let extra = indices[k];
        prop_assert!(!decoder.add_chunk(Chunk { index: extra, data: noise }), "a codeword past k was kept");
        prop_assert_eq!(decoder.message(), Some(message.clone()));
    }
}
