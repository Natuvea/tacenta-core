#!/usr/bin/env bash
# The single verification gate for tacenta-core. One source of truth for
# "does it pass": the Lean proofs, the model-vector currency check, and the Rust
# crates (fmt, clippy, tests), including the property-based decoder tests.
#
# The public workflow, `.github/workflows/ci.yml`, runs these same steps on
# every push and pull request, split into jobs so a failure names its cause;
# this script is the one-command form for a developer's machine. The two are
# meant to agree, and a step added here belongs there too, with one stated
# asymmetry in each direction.
#
# Steps the workflow always runs and this script skips, printing a line that
# says so, when the tooling is absent from the machine: the advisory audit
# (`cargo-audit`), the MSRV compile check (a 1.87 toolchain), the 32-bit
# compile check (the armv7 target), the Linux halves of the constant-time
# disassembly gate (the x86_64 and aarch64 Linux targets; the host is always
# read), and the translation build with its `sorry` scan (`no-sorry.sh`,
# which needs the translation's Mathlib cache and is the heavy one). The
# first four fail rather than skip when `GITHUB_ACTIONS` is set, so a runner
# cannot report green on a check it did not run. Steps this script runs and
# the workflow does not: the interoperability harness, which is not in this
# public tree and skips here, and the fuzz smoke run, which needs
# `cargo-fuzz` and a nightly toolchain. The README's "Building and checking"
# section lists the same five and two, and says what runs outside this
# repository altogether and why.
#
# The runner must provide: elan with Lean v4.31.0 (lake on PATH) and a Rust
# stable toolchain (cargo, clippy, rustfmt). Everything else is optional, and
# the step that needs it says so when it skips.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

# Cross-file only: a workflow cannot check its own parseability, because a file
# that does not parse runs nothing. In CI this catches the *other* workflow
# files breaking; the pre-push hook in `.githooks/`, once enabled as
# CONTRIBUTING.md describes, catches all of them before they leave the machine.
echo "== Workflows parse =="
bash tooling/check-workflows.sh
# And the checker is held to its own cases, passing and refused, so a rule
# loosened by mistake fails this gate rather than the next reader.
bash tooling/tests/run-check-workflows-cases.sh

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

# `TripleT3.lean` cannot cite the two inner ratchets' refinement theorems --
# Charon translates each crate separately -- so it restates their hypotheses
# and conclusions by hand in `RatchetAgreesFor`/`SpqrAgreesFor`. Those are
# `def ... : Prop`, never an application of the leaf theorem, so Lean has
# nothing to compare and the agreement has drifted twice, both times a counter
# bound tightening at the leaf while the bundle kept the older, weaker one.
# This is the comparison the build cannot make. It needs no Lean toolchain,
# which is why it runs here and in the `checks` job rather than beside the
# translation build.
echo "== Bundle clauses still say what their leaf theorems say =="
python3 tooling/check-bundle-drift.py
# And the checker is held to its own cases -- a matching pair, a drifted
# bound, a dropped hypothesis, a deleted clause, an unmarked clause, a marker
# naming a leaf theorem the leaf file no longer declares, and one it cannot
# analyse -- so a substitution loosened by mistake fails this gate rather than
# the next reader.
bash tooling/tests/run-check-bundle-drift-cases.sh

# A numeric precondition of the shape `x + A.max ≤ B.max`, with `A` at least as
# wide as `B` on some target, forces `x` to zero there and describes no state
# that has held anything. One such bound made `receive_no_panic` vacuous on
# 32-bit targets for months while reading as a strong hypothesis. This is a
# tripwire for the forms its docstring lists, not a proof that no bound forces
# its subject to zero, and the docstring also lists what review found it misses.
# PreconditionShapes.lean is excluded, since it states the shape on purpose. The
# cases hold the lint to exact sites, lines and columns.
echo "== The precondition-shape tripwire finds none of the forms it lists =="
python3 tooling/check-precondition-shapes.py
bash tooling/tests/run-check-precondition-shapes-cases.sh

# The three-leaf translation unit is generated from the three leaf crates, and
# a generated crate that has stopped agreeing with its sources is a crate whose
# translation is about code that is no longer there. This regenerates it into a
# temporary directory and diffs; it needs no Charon, no Aeneas and no Lean, so
# it runs here with the other cheap checks rather than beside the translation
# build. `attest.py --check` below is the other half: this says the unit crate
# is what the leaves assemble to, that says the committed translation is the
# one produced from it.
echo "== The three-leaf translation unit is what its leaves assemble to =="
sh tacenta-proofs/scripts/assemble-triple-unit.sh --check

# The unit's copies of the two leaf panic-freedom proofs are generated from
# those proofs, not maintained beside them: the constants differ, so the
# theorems have to exist twice, and this is what stops the second copy drifting
# from the first. Needs no toolchain, so it runs here rather than beside the
# proof build; the build itself is what checks that the copies still prove
# anything.
echo "== The unit's copies of the leaf panic-freedom proofs are the ported originals =="
bash tacenta-proofs/scripts/port-unit-proofs.sh --check

# Derivation labels are protocol constants, and a codebase that cannot enumerate
# its own is one nobody can review. `tacenta-core/LABELS.md` is the freeze;
# this makes it binding rather than aspirational, and enforces prefix-freedom
# for anything new -- the property distinctness does not give you.
echo "== Derivation labels are registered =="
bash tooling/check-labels.sh

# The runners parse vectors with serde, which ignores what it does not know;
# the schemas are stricter, and this is what makes them binding.
echo "== Vector files validate against their schemas =="
python3 tooling/check-vectors.py

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

# The minimum supported Rust version still compiles the workspace: the
# `rust-version` every manifest names, and the version the workflow's `msrv`
# job installs. A check, not a test run (the tests ran on stable above); it
# exists so a use of newer syntax or a newer standard-library feature is
# caught before it reaches a consumer holding the version the manifests
# promise. Skips locally when the toolchain is absent and fails in CI, the
# rule the advisory audit below follows.
msrv=1.87
echo "== Rust: the workspace compiles on the minimum supported version ($msrv) =="
if rustup toolchain list 2>/dev/null | grep -q "^${msrv//./\\.}"; then
  (cd tacenta-core && cargo "+$msrv" check --locked --workspace --all-targets)
elif [ "${GITHUB_ACTIONS:-}" = "true" ]; then
  echo "ci: no $msrv toolchain on the runner; install it with 'rustup toolchain install $msrv'" >&2
  exit 1
else
  echo "ci: no $msrv toolchain, skipping the MSRV check (rustup toolchain install $msrv)"
fi

# The two hand-written constant-time functions -- the Braid's `mac_eq` and
# XEdDSA's `calculate_key_pair` -- compile to straight-line code: the release
# assembly is read and any conditional branch beyond `mac_eq`'s public length
# compare fails, as does a symbol that was inlined away. The timing harness
# cannot see either function (`tests/timing.rs` says why at its floors); this
# is the instrument for them. The host target is always read; each Linux
# target the machine has installed is read too, a missing one is skipped with
# a line saying so, and in CI, where the workflow installs the aarch64 target
# beside its x86_64 host, a run with neither Linux target fails. The script
# builds with `--emit=asm`, which needs no linker, so a target needs only its
# `rust-std` (`rustup target add <target>`).
echo "== Rust: the constant-time functions compile to straight-line code =="
bash tooling/check-constant-time-asm.sh

# Known advisories against the dependency graph. Fails on a vulnerability;
# warnings (unmaintained, yanked) are printed and do not fail, because those
# present today sit in transitive build-time dependencies and are not fixable
# here. Skips locally when the tool is absent and fails in CI, the rule the
# MSRV and 32-bit checks follow.
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
  (cd tacenta-core && cargo check --locked --workspace --target armv7-linux-androideabi)
elif [ "${GITHUB_ACTIONS:-}" = "true" ]; then
  echo "ci: armv7-linux-androideabi is not installed on the runner; install it with 'rustup target add armv7-linux-androideabi'" >&2
  exit 1
else
  echo "ci: armv7-linux-androideabi not installed, skipping the 32-bit check (rustup target add armv7-linux-androideabi)"
fi

# The heavy build, last so that everything cheaper has already reported: the
# committed Rust-to-Lean translation with its T1/T3 proofs, and the model and
# its property theorems again, each built and scanned for incomplete
# declarations by `no-sorry.sh`. Aeneas's Lean library brings Mathlib, which
# `lake exe cache get` fetches prebuilt; without it `lake build` would
# compile Mathlib from source, which is hours, so the step skips when the
# translation's Mathlib cache has not been fetched and says how to fetch it.
# The test is for a built artefact (`Mathlib.olean`), not the package
# directory: `lake` creates the directory on its first attempt, so it exists
# after an aborted build too, and a run that then tried `no-sorry.sh` would
# start the hours-long compile the skip is there to avoid. The workflow's
# `translation` job fetches the cache and always runs this.
echo "== Lean: the translation and its proofs use no sorry (needs the Mathlib cache) =="
if [ -f tacenta-proofs/translation/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]; then
  bash tacenta-proofs/scripts/no-sorry.sh
else
  echo "ci: the translation's Mathlib cache is not fetched, skipping no-sorry.sh"
  echo "ci: fetch it with '(cd tacenta-proofs/translation && lake exe cache get)'"
fi

echo "ci: all checks green"
