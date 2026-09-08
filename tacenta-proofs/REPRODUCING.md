# Reproducing the verification

Toolchain, steps, and expected output to reproduce every proof.

Two gates run here, in two different workflows, and the difference matters if
you are checking a claim: the light one runs on every push, the heavy one
translates the Rust and proves things about it. Reproducing "the proofs" means
running both.

## Toolchain

| Component | Pin | Where |
| --- | --- | --- |
| Lean | `leanprover/lean4:v4.31.0` | `lean-toolchain` (and `translation/lean-toolchain`) |
| Lean dependencies, model layer | exact revisions | `lake-manifest.json` |
| Lean dependencies, translation (Aeneas library, Mathlib, Batteries, Aesop) | exact revisions | `translation/lake-manifest.json`, with the Aeneas library `rev` pinned by commit in `translation/lakefile.toml` |
| Charon and Aeneas | release `nightly-2026.07.22-b1214ca`, archive `aeneas-linux-x86_64.tar.gz` with SHA-256 `bc26c30daf92679b57c264c630710096bd9d4428e28795fe0638afdb0c2df65f`, checked on every run, and stated here so a reader elsewhere can confirm they hold the same binaries | the verification workflow; also recorded by `attest.py` in `manifests/verification-manifest.json` |
| Mathlib build artifacts | **not pinned**: `lake exe cache get` fetches prebuilt oleans for the manifest's Mathlib commit from Mathlib's cache over HTTPS, and Lean loads them without re-checking against source | trusted, see `LIMITATIONS.md` |
| Rust, for Charon | whatever the Aeneas release's `rust-toolchain` names | resolved at run time, not pinned here |

The last row is a real dependency edge and not an omission: Charon is a `rustc`
driver, so it must be built against the compiler version its release was built
for. Pinning a second Rust version here would let the two disagree with nothing
to notice.

## The light gate: model and model-layer proofs

```sh
cd tacenta-proofs && ./scripts/verify.sh
```

Builds the Lean proofs on the pinned toolchain and greps `Proofs/` for `sorry`
and `admit`. `tooling/ci.sh` runs it, and it needs nothing but `lake`.

**Its `sorry` check is the weaker of the two, deliberately.** It greps one
directory and matches the word wherever it appears, including in prose that
explains there is no `sorry`. It covers `Proofs/`, not `translation/`. The
authoritative check is below; this one exists so that an every-push gate can
stay cheap.

Expected tail:

```
verify: proofs built clean
```

## The heavy gate: translation, T1, and T3

Run by the verification workflow on every push, nightly, and on demand.
Locally it is three steps, and the first needs Charon and Aeneas on `PATH`:

```sh
bash tacenta-proofs/scripts/run-aeneas.sh
```

Translates the verified zone -- the leaf crates only: ratchet, session, erasure,
protobuf, spqr, braid, triple. It writes into `translation/Translation/`
alongside the hand-written proofs. The drift step in the verification workflow fails if
the committed files differ from what the pinned toolchain regenerates, which
catches both a generated file edited by hand and a committed generation the
toolchain no longer produces. (`scripts/check-generated-files.sh` is a signpost
to that step and always exits zero; it is not a check.)

```sh
cd tacenta-proofs/translation && lake exe cache get && lake build
```

Builds the generated Lean and every T1 (panic-freedom) and T3 (refinement)
proof against the Aeneas library, at the dependency commits recorded in
`translation/lake-manifest.json`. **Not `lake update`**: that re-resolves every
dependency and rewrites the manifest, which is the right thing to do
deliberately when moving the pins and the wrong thing to do while reproducing a
claim. `lake exe cache get` fetches Mathlib rather than building it; skipping
it works and costs hours.

```sh
bash tacenta-proofs/scripts/no-sorry.sh
```

**This is the authoritative completeness check.** It asks the compiler instead
of grepping the source: Lean emits "declaration uses `sorry`" for every
incomplete declaration it elaborates, so a build log is exhaustive where a grep
is not. It covers both lake packages -- `translation/` and the model layer --
and it filters *positively* by our own directories, so a third-party `sorry`
(Aeneas's own library ships four) is not ours and is not failed on, while
anything it does not recognise is treated as third-party rather than quietly as
first-party.

Expected tail:

```
no-sorry: the translation and its T1/T3 proofs is complete
no-sorry: the model-layer proofs is complete
```

## What a green run does and does not establish

`CLAIMS.md` is the ledger and `LIMITATIONS.md` is its counterpart; read both
rather than inferring scope from a green check. Two things worth knowing before
you do:

- **The claims are checked against the proofs, not maintained beside them.**
  `scripts/attest.py --check` runs in the every-push gate and fails if the
  ledger and the attestation manifests drift from the pins.

  **But it reads the pins as written, not as built.** The axiom facts come from
  the `#guard_msgs` docstrings in the source; the script hashes and
  cross-references those, and delegates *checking that they are true* to the
  build. So a green `attest` says the ledger is consistent with what the files
  claim; only a green heavy gate says the files are telling the truth.
- **T1 and T3 are about the Aeneas model of the Rust**, not the machine code
  `rustc` produces. The Charon and Aeneas translation, the Lean kernel, and the
  Rust compiler are all trusted. That trust is the point of writing the pins
  above down.
