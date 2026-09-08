#!/usr/bin/env bash
# Miri over the crates it can actually interpret.
#
# Miri executes Rust's MIR and reports undefined behaviour: out-of-bounds
# access, invalid aliasing, uninitialised reads, misaligned pointers. Every
# crate here is `#![forbid(unsafe_code)]`, so the interesting result is not
# "Miri found UB in our unsafe code" -- there is none -- but that the *safe*
# code, including everything it calls in `core` and `alloc`, executes cleanly.
# That covers things a type system does not: an `unsafe` block inside a
# dependency reached only on one path, or a soundness bug in a std API used the
# wrong way.
#
# **Not every crate is in scope, and the reason is mechanical rather than a
# judgement.** Miri interprets MIR; it cannot execute the SIMD intrinsics that
# `libcrux-ml-kem` and the dalek curve crates use. So anything reaching the
# post-quantum KEM or the curve arithmetic is out: `tacenta-kem`,
# `tacenta-braid`, and `tacenta-core` itself. What remains is the pure protocol
# and arithmetic layer, which is where our own indexing and slicing lives, and
# therefore where our own bugs would be.
#
# Isolation is disabled because the property tests call `getcwd` to find their
# regression files. That weakens Miri's sandbox, not its UB detection, which is
# what this run is for.
set -euo pipefail

here="$(cd "$(dirname "$0")/.." && pwd)"
cd "$here/tacenta-core"

TOOLCHAIN="${MIRI_TOOLCHAIN:-nightly-2026-07-15}"
export MIRIFLAGS="${MIRIFLAGS:--Zmiri-disable-isolation}"

# Fewer proptest cases than the ordinary suite: Miri is roughly two orders of
# magnitude slower than native, and 2,048 cases per property under an
# interpreter is hours rather than minutes. The point here is UB on
# representative inputs, not coverage -- coverage is `tooling/fuzz-smoke.sh`
# and the nightly fuzzing.
export PROPTEST_CASES="${PROPTEST_CASES:-16}"

# **What runs by default, and what does not.**
#
# Miri is roughly two orders of magnitude slower than native, and several
# suites here are dominated by deliberate bound-stress tests: the ratchet skips
# `MAX_SKIP` (1,000) message keys to prove the cap holds, the sparse ratchet
# does the same across epochs and then retires them, and `tacenta-erasure`
# interpolates polynomials over GF(2^16). Those are the right tests to have and
# the wrong ones to interpret. A check nobody runs is not a check, so the
# default set is the part that finishes in seconds.
#
# Skipping the stress tests by name took `tacenta-ratchet` from over
# forty-five minutes to under six seconds, which is what makes it viable here.
# The same filters did not rescue `tacenta-spqr`: its epoch-retirement and
# full-conversation tests are heavy on their own, past half an hour, so it is
# out of the default set. `tacenta-erasure` is out for the same reason and is
# also where Miri adds least, since its field is *proved* a field in Lean
# (`Model.Gf65536`) and `mul` is refinement-proved for every input rather than
# at sampled points (`ErasureT3.lean`).
#
# **What the default set still covers is the point:** every decoder, every
# state transition, and every indexing path in the protocol and parsing layer.
# What it loses is UB coverage of loops repeating an operation those same tests
# already perform once, more cheaply.
#
# The two excluded crates, on demand, when either changes shape:
#
#   MIRIFLAGS=-Zmiri-disable-isolation PROPTEST_CASES=4 \
#     rustup run nightly-2026-07-15 cargo miri test -p tacenta-spqr
#   MIRIFLAGS=-Zmiri-disable-isolation PROPTEST_CASES=4 \
#     rustup run nightly-2026-07-15 cargo miri test -p tacenta-erasure

# Bound-stress tests, skipped by substring: `MAX_SKIP` refusal, the store cap,
# cross-epoch retirement, and the out-of-order recovery walks.
SKIP=(--skip bound --skip cap --skip out_of_order)

# `tacenta-session` (depends on kdf and zeroize only) and `tacenta-triple`
# (ratchet, spqr, kdf, zeroize) meet neither exclusion reason above -- no SIMD
# -- so both are in the set. `tacenta-session` is seconds. `tacenta-triple`
# is about five minutes: its conversation tests
# drive both ratchets through software HMAC and HKDF on every step, which is
# what an interpreter is slowest at. Nightly, so the minutes are affordable,
# and a note here so nobody diagnoses a hung run.
for crate in tacenta-protobuf tacenta-kdf tacenta-ratchet tacenta-session tacenta-triple; do
  echo "== miri: $crate =="
  rustup run "$TOOLCHAIN" cargo miri test -p "$crate" -- "${SKIP[@]}"
done

echo "miri: no undefined behaviour in the interpretable crates"
