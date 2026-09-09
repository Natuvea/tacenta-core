# tacenta-core

A verification-first implementation of selected published Signal Protocol
specifications: a small, standalone cryptographic core with machine-checked
proofs over its verified zone.

## What this is

The cryptographic foundation behind Tacenta, built to stand on its own. It is
protocol, cryptography, and their verification, nothing else: no product
coupling, no application policy, no services. Tacenta is its first consumer, but
it is meant to serve other projects too, the way libsignal does. Each of the
five components is built to lift into its own public repository; they live
together here while the work matures.

This implementation is designed to be inspected and its stated proof claims
reproduced. Its supported protocol surface and interoperability limits are
stated below. It is not yet packaged for installation from a registry; today the
way to engage with it is to read the specification and verify the proofs (see
"Verify it yourself" below).

## The mission

> Build a small, stable, verification-first engine for selected published Signal
> Protocol specifications, with narrowly stated and reproducible compatibility
> results.

Every phrase is a constraint, and each is meant to be falsifiable:

- **Small.** Only security-critical protocol functionality is in the core.
- **Stable.** Tacenta owns and versions its public API.
- **Verification-first.** Specifications, models, and evidence precede claims.
- **Interoperable on the wire.** Match another implementation's protocol
  *behaviour*, not its API architecture. What that covers today is stated below.
- **Explicitly supported versions.** Compatibility is tested and bounded, never
  universal.
- **No product coupling.** Storage and device abstractions belong; application
  policy and unrelated services do not.

## What is and is not claimed

Two of the constraints above carry limits worth stating plainly.

- **Interoperability reaches the bundle layer, not the message layer.** The
  target is exchanging prekey bundles and establishing a session with a pinned
  libsignal release, with any result claimed by version and covered surface
  (ADR-0004). Ongoing messages are not exchanged across implementations: the
  key-derivation constants sit upstream of
  every message byte, no published specification carries test vectors for them,
  and black-box observation cannot recover them. The release gate is scoped to
  the bundle layer accordingly.
- **Stable is a goal, not a state.** There is no versioning policy, deprecation
  policy, or supported-target matrix yet.

The other four constraints can be checked today, and
`tacenta-proofs/CLAIMS.md` is the precise record of what is proven. Where this
README and that document ever disagree, that document is right.

## Components

- **[tacenta-spec](tacenta-spec/)**, the protocol and security specification,
  written as prose.
- **[tacenta-model](tacenta-model/)**, the executable, formal model.
- **[tacenta-proofs](tacenta-proofs/)**, the Lean proofs and a reproducible
  verification environment.
- **[tacenta-test-vectors](tacenta-test-vectors/)**, interoperability vectors
  and conformance tests.
- **[tacenta-core](tacenta-core/)**, the Rust cryptographic implementation.

## Status

Seven crates ship with T1 panic-freedom and T3 refinement proofs: the ratchet,
the session zone, `tacenta-spqr`, `tacenta-braid`, `tacenta-triple`,
`tacenta-protobuf`, and `tacenta-erasure` (the last over its field arithmetic;
its decoder has T1 and no refinement). The post-quantum ratchet is in the
session path, and sessions and prekey stores serialize.
`tacenta-proofs/CLAIMS.md` records exactly what is and is not proven.

## Verify it yourself

The point of a verification-first library is that you do not have to take its
word for it. `tacenta-proofs/CLAIMS.md` states each claim;
`tacenta-proofs/REPRODUCING.md` is how to rebuild the proofs, and
`tacenta-test-vectors/README.md` ("Regenerating the protocol vectors") is how
to check the committed vectors against the model. The model and the
model-layer proofs reproduce on any machine, and the committed Rust-to-Lean
translation with its T1/T3 proofs builds in the public `translation` CI job.
Only regenerating that translation from the Rust needs the pinned
Charon/Aeneas toolchain, which runs outside this repository (see below); the
release and archive digest are stated in `tacenta-proofs/CLAIMS.md` so that
step can be reproduced elsewhere.

## Building and checking

One command runs every gate: `bash tooling/ci.sh`. The public CI
(`.github/workflows/ci.yml`) runs the same steps, split into jobs, on every
push and pull request, so a green run there and a green run here mean the
same thing. The gate is: the workflow, proof-hygiene, label, vector-schema and
authentication-boundary checks under `tooling/`; the Lean model build and the
model-layer proofs with their `sorry` scan; the attestation check; the
committed vectors regenerated from the model and compared; and the Rust
crates (format, lint, tests, property-based decoder tests) with a dependency
advisory audit and a 32-bit compile check.

| Prerequisite | Version | Used by |
| --- | --- | --- |
| Rust toolchain (`cargo`, `clippy`, `rustfmt`) | stable; 1.87 is the minimum every crate names | the Rust crates and the vector runner |
| `cargo-audit` (`cargo install --locked cargo-audit`) | any current release | the advisory audit; skipped locally when absent, failed in CI |
| `rustup target add armv7-linux-androideabi` | matching the toolchain | the 32-bit compile check; skipped locally when absent |
| Lean, through elan | the version `tacenta-model/lean-toolchain` and `tacenta-proofs/lean-toolchain` name (v4.31.0) | the model, the proofs, and vector regeneration |
| `python3` with PyYAML | 3.8 or later | the `tooling/` checks |
| `git` | any | the vector-currency diff |

Individual pieces can be run on their own: `cargo test --locked --workspace`
in `tacenta-core`; `cargo test --locked` in
`tacenta-test-vectors/runners/rust`; `lake build` in `tacenta-model`;
`scripts/verify.sh` in `tacenta-proofs`. CONTRIBUTING.md has the pre-push
hook that runs the cheapest of the checks before a push leaves the machine.

Three things run outside this repository, and the gate says so rather than
pretending to run them. **Regenerating the Rust-to-Lean translation** needs
the pinned Charon and Aeneas release, which is a linux-x86_64 binary that
runs on a dedicated runner; the committed translation is what the public
`translation` job checks, and `tacenta-proofs/CLAIMS.md` records the release
and its digest so the regeneration can be reproduced elsewhere.
**Coverage-guided fuzzing** needs `cargo-fuzz` and a nightly toolchain and
runs for hours, so the search is a nightly job on private infrastructure;
`tooling/fuzz-smoke.sh` replays the committed corpus when the tooling is
present, and `tacenta-core/fuzz/README.md` describes the targets. **Timing
measurements** need a dedicated machine, since a job co-scheduled with other
load on a shared hosted runner cannot tell a leak from noise;
`tacenta-core/tests/timing.rs` carries the tests, run by hand or by a nightly
job outside this repository, and `tacenta-proofs/LIMITATIONS.md` states what
is and is not established about constant-time behaviour. None of the three
changes what the public gate proves; each is named here so that a reader
knows what a green badge does not include.

## Provenance

tacenta-core is a clean-room implementation. Its inputs are the published
Signal Protocol specifications, pinned by SHA-256 in
`tacenta-test-vectors/conformance-manifest.md`; the standards those
specifications cite; this project's own specification, model, and vectors; and,
where a published specification leaves a wire-level convention to the
implementer, black-box observation of a pinned build of a third-party
implementation under the interoperability research boundary (ADR-0003,
ADR-0005), with each such value and its provenance recorded in
`tacenta-spec/CONSTANTS.md`. libsignal's source code, tests, fixtures, schemas,
and internal documentation are not inputs to this project. The public API is
independently designed and does not reproduce libsignal's.

This tree contains no libsignal implementation source, compiled libsignal
objects, reference-adapter implementation, research transcripts, or
libsignal-derived fixtures.

## License

Apache-2.0. See `LICENSE`.

## Trademarks and non-affiliation

tacenta-core and Tacenta are not affiliated with, endorsed by, or sponsored by
Signal Messenger LLC or the Signal Foundation. "Signal" and "libsignal" are used
only to name the published protocols and the third-party software they refer to.
