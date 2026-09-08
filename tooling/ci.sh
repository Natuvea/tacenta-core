#!/usr/bin/env bash
# The single verification gate for tacenta-core; the project's CI runs
# it on every push. One source of truth for
# "does it pass": the Lean proofs, the model-vector currency check, and the Rust
# crates (fmt, clippy, tests), including the property-based decoder tests.
#
# The runner must provide: elan with Lean v4.31.0 (lake on PATH) and a Rust
# stable toolchain (cargo, clippy, rustfmt). The Aeneas T1 build is heavier and
# is deliberately not part of this every-push gate.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

# Cross-file only: a workflow cannot check its own parseability, because a file
# that does not parse runs nothing. This catches the *other* workflow breaking,
# and the pre-push hook catches both before they leave the machine.
echo "== Workflows parse =="
bash tooling/check-workflows.sh

# The property: nothing durable moves on a message before its authenticator
# verifies. This does not detect a violation directly; it detects the shape
# that carries one and requires an argument on file for each instance.
echo "== Every receive path is registered =="
python3 tooling/check_authentication_boundary.py

# Costs nothing, needs no Aeneas, and catches at authoring time a hand-written
# proof naming a generated constant, which becomes `sorry` the day the
# translator renumbers it. See the script.
echo "== Proof hygiene: no generated names in hand-written proofs =="
bash tooling/check-proof-hygiene.sh

# Derivation labels are protocol constants, and a codebase that cannot enumerate
# its own is one nobody can review. `tacenta-core/LABELS.md` is the freeze;
# this makes it binding rather than aspirational, and enforces prefix-freedom
# for anything new -- the property distinctness does not give you.
echo "== Derivation labels are registered =="
bash tooling/check-labels.sh

echo "== Lean: build the model =="

( cd tacenta-model && lake build )

echo "== Lean: proofs build and use no sorry =="
( cd tacenta-proofs && ./scripts/verify.sh )

# The attestation gate. The claim ledger and the attestation manifests are
# checked against the proofs rather than maintained beside them, because a
# document maintained by hand can describe a state the repository has left.
echo "== Claims and attestations cover what ships =="
python3 tacenta-proofs/scripts/attest.py --check

echo "== Vectors are current with the model =="
tacenta-test-vectors/regenerate-vectors.sh
if ! git diff --quiet -- tacenta-test-vectors/vectors; then
  echo "ERROR: committed vectors differ from the model. Run" >&2
  echo "  tacenta-test-vectors/regenerate-vectors.sh" >&2
  echo "and commit the result." >&2
  git --no-pager diff --stat -- tacenta-test-vectors/vectors >&2
  exit 1
fi

# "Property tests", not "fuzz". `tests/fuzz.rs` drives the decoders with
# proptest, which is property-based and not coverage-guided; the
# coverage-guided fuzzing is the smoke run below and the nightly workflow, and
# the label here should not imply otherwise.
echo "== Rust: every crate (fmt, clippy, test, property tests) =="
export PROPTEST_CASES="${PROPTEST_CASES:-2048}"
# `--locked` everywhere. Without it a manifest edit that lands without its
# lockfile, or a runner toolchain that resolves differently, lets Cargo
# rewrite `Cargo.lock` in place and run against a dependency graph nobody
# reviewed.
for crate in \
  tacenta-core \
  tacenta-test-vectors/runners/rust \
  tacenta-test-vectors/compatibility/adapters/tacenta
do
  if [ ! -d "$crate" ]; then
    echo "-- $crate -- not present in this tree, skipping"
    continue
  fi
  echo "-- $crate --"
  (
    cd "$crate"
    cargo fmt --check
    cargo clippy --locked --workspace --all-targets --quiet -- -D warnings
    cargo test --locked --workspace --quiet
  )
done

# Known advisories against the dependency graph. Fails on a vulnerability;
# warnings (unmaintained, yanked) are printed and do not fail, because those
# present today sit in transitive build-time dependencies and are not fixable
# here. Skips locally
# when the tool is absent and fails in CI, the rule every other gate in this
# file follows.
echo "== Rust: dependency advisories (cargo audit) =="
if command -v cargo-audit >/dev/null 2>&1; then
  (cd tacenta-core && cargo audit)
elif [ "${GITHUB_ACTIONS:-}" = "true" ]; then
  echo "ci: cargo-audit is not installed on the runner; install it with 'cargo install cargo-audit --locked'" >&2
  exit 1
else
  echo "ci: cargo-audit not installed, skipping the advisory check (cargo install cargo-audit --locked)"
fi

# The decoders read attacker-controlled lengths and cast them to `usize`, which
# is a different width here than on a phone. That arithmetic is guarded
# against overflow at 32 bits, so keep the target compiling: a guard that
# stops being built is a guard that stops being checked.
#
# This is a compile check, not a run. Nothing here executes 32-bit code, and the
# overflow guard is covered at every width by
# `a_length_that_cannot_be_added_is_refused_rather_than_wrapping`, which is why
# that test goes at the helper rather than through a decoder.
# The harness runs against the Tacenta adapter on both sides, which proves the
# harness works and nothing about interoperability. The report it writes says so
# in those words. It is here so the scenarios stay exercised.
# The harness and its adapters are not part of this public tree; the step
# skips, and says so, when they are absent.
echo "== Interoperability harness (self-run: exercises the harness only) =="
if [ -d tacenta-test-vectors/compatibility/harness ] \
  && [ -d tacenta-test-vectors/compatibility/adapters/tacenta ]; then
  (
    cd tacenta-test-vectors/compatibility/adapters/tacenta
    cargo build --locked --quiet --bin tacenta-adapter-rpc
  )
  adapter="$PWD/tacenta-test-vectors/compatibility/adapters/tacenta/target/debug/tacenta-adapter-rpc"
  (
    cd tacenta-test-vectors/compatibility/harness
    cargo run --locked --quiet --bin interop-harness -- \
      --a "$adapter" --b "$adapter" \
      --a-label "tacenta 0.0.0" --b-label "tacenta 0.0.0" \
      --out ../reports --transcripts ../transcripts
  )
else
  echo "ci: interoperability harness not present in this tree, skipping"
fi

# The fuzzing gate. A regression gate rather than a search: each target
# replays its committed corpus and fuzzes briefly. The search is the private
# nightly fuzz workflow, which is where a growing corpus lives.
#
# Skipped rather than failed when the tooling is absent, because this gate has
# to stay runnable on a plain stable toolchain. A runner that skips says so.
echo "== Coverage-guided fuzzing (smoke) =="
# **Both halves, not one.** The script this calls needs `cargo-fuzz` and a
# nightly toolchain, and says so in its own header. `cargo-fuzz` can be
# installed on a runner without nightly becoming the default, and then
# `cargo fuzz` fails on `error: the option 'Z' is only accepted on the nightly
# compiler`. A guard that tests one of two preconditions is not a guard.
if ! command -v cargo-fuzz >/dev/null 2>&1; then
  echo "ci: cargo-fuzz not installed, skipping the fuzz smoke run"
  echo "ci: install with 'cargo install cargo-fuzz' (needs a nightly toolchain)"
elif ! rustup toolchain list 2>/dev/null | grep -q '^nightly'; then
  echo "ci: no nightly toolchain, skipping the fuzz smoke run"
  echo "ci: install one with 'rustup toolchain install nightly'"
else
  bash tooling/fuzz-smoke.sh
fi

echo "== Rust: the 32-bit target still compiles =="
if rustup target list --installed 2>/dev/null | grep -q '^armv7-linux-androideabi$'; then
  (cd tacenta-core && cargo check --locked -p tacenta-core --target armv7-linux-androideabi)
else
  echo "ci: armv7-linux-androideabi not installed, skipping the 32-bit check"
fi

echo "ci: all checks green"
