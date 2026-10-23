# ADR-0010: the key derivation's SHA-256, HMAC and HKDF are written here

## Status

Accepted, 2026-10-23, by the maintainer on the rule-7 review (ADR-0008) of the
change that lands it, after reading the three Rust files in full and the
measured costs below.

## Context

- **The rule.** Standard cryptography is not implemented here: primitives come
  from vetted crates and are assumed correct at the boundary. ADR-0002 made
  XEdDSA "the deliberate, specified exception" to that rule, because no
  vetted, permissively licensed Rust crate provided it. That record describes
  its own decision and is not edited here, beyond a status note.
- **What the rule cost the key derivation.** `tacenta-kdf` wrapped RustCrypto's
  `hmac`, `hkdf` and `sha2`. Translating those crates was tried with the Aeneas
  release that is still pinned (`nightly-2026.07.22-b1214ca`, already the pin
  of the public tree where that record first appears) and failed:
  RustCrypto's trait hierarchy came into the generated Lean, which ran to
  57,272 lines that would not build (`tacenta-proofs/upstream/README.md`), and
  that is why the KDF became its own crate. So the eleven translations carried
  13 opaque KDF axioms between them: `hmac_sha256` and `hkdf_sha256` in five,
  one of the two in three, and none in the three whose crates do not call the
  KDF. The agreement hypotheses the T1 and T3 theorems take about those
  axioms (`HmacAgrees`, `HkdfAgrees` and their siblings, ASM-05) could not be
  shown of the code at all, only assumed.
- **What was available.** A SHA-256, an HMAC-SHA256 and an HKDF-SHA256 in the
  subset Aeneas translates, with Lean proofs that the translated code computes
  a model written from FIPS 180-4, FIPS 198-1 and RFC 5869, and that this model
  equals tacenta-model's `Model.Sha256` and `Model.Kdf`: written by the
  maintainer with tool assistance in a separate, unpublished repository; the
  three Rust files were read in full by the maintainer on 2026-10-23, and
  before that only by tool-assisted sessions; no reader independent of the
  maintainer has read the three files, and no human has read their proofs.

## Decision

- `tacenta-kdf`'s SHA-256, HMAC and HKDF are that code, copied into
  `kdf/src/` and pinned in `kdf/src/lib.rs` by the source commit and the
  files' digests. The public functions and their signatures do not change.
  This is a second exception to the no-reimplementation rule, after XEdDSA.
- The three copied files are distributed in this repository under its own
  licence, Apache-2.0 (`LICENSE`, `NOTICE`); the source repository carries no
  licence statement.
- Every translation whose crate calls the KDF includes its bodies, and the six
  translations whose theorems take the KDF agreement hypotheses prove them of
  their translated code (ASM-05 lists them). The theorems still take the
  hypotheses as stated.
- The other users of SHA-2 and HMAC stay on RustCrypto: the AEAD's tag check
  on decryption, the root crate's identity and group digests, and XEdDSA's
  SHA-512.

## Alternatives rejected

- **Stay on RustCrypto.** Widely used, reviewed by others, and faster (see
  Costs). Rejected because the agreement hypotheses would stay assumptions
  that no proof in this tree can discharge.
- **Adopt the code as an external dependency.** Depend on a published crate
  instead of copying it. Rejected for now: the source is not published, so
  there is nothing to depend on, and a dependency would add a supply-chain
  input for code no reader independent of the maintainer has read.
- **Translate RustCrypto's crates.** Tried with the current pin and failed, for
  the reason in Context.

## Costs

Measured on one x86_64 Linux machine with SHA extensions and on the source
repository's machine; no other CPU model, and no aarch64 Linux or phone
hardware, was measured.

- **Per call.** On the x86_64 machine, RustCrypto picks the SHA extensions at
  run time, and the copied code is 5.1 to 18.5 times slower than the shipping
  RustCrypto per call (median, rising with input size; about 6.7 to 8.8 times
  at the KDF's own input sizes). Against RustCrypto built without the SHA
  extensions it is 1.37 to 2.16 times slower, which matches the 1.5 to 2.1
  times the source repository measured on its own machine.
- **Protocol level** (the repository's `tests/benchmarks.rs`, on the x86_64
  machine): one 16-byte encrypt and decrypt round 1.12 times; `encrypt` alone
  2.9 to 3.8 times (its tag is the copied HMAC); `decrypt` after 500 lost
  messages 4.5 times; establishment and persistence unchanged.

## Consequences

- **What replaces "vetted".** Proofs that the translated code equals
  tacenta-model's HMAC and HKDF (HKDF for outputs of at most 8160 bytes); a
  differential test against the RustCrypto crates it replaced
  (`kdf/tests/differential.rs`); the RFC test vectors; the maintainer's reading
  of the three Rust files; and an exact inventory of the compiled code's
  branches, indexed accesses and callees (`tooling/check-constant-time-asm.sh`),
  compared for the two Linux targets in CI and for macOS on a local run.
- **Timing and inventory evidence, one machine.** On the x86_64 Linux machine
  above, the inventory built natively under the pinned compiler is
  byte-identical to the committed baseline, while the stable compiler there
  gives a different one (its differences depend on lengths and counts, by a
  tool-assisted reading), which is why the gate pins the compiler; a
  dudect-style test of the copied HMAC detected no timing difference, with a
  control that does detect a few-instruction leak; the workspace's tests pass
  there, and the copied crate's unit tests pass under miri. That is a tripwire
  and one measurement on one CPU, not a proof of constant time.
- **Limits.**
  - Provenance: the source repository is unpublished, so a reader cannot check
    the pinned commit or digests.
  - Timing is measured on one CPU only, and the inventory items were read by a
    tool-assisted session.
  - Erasure: nothing wipes the intermediate values, as before.
  - That tacenta-model's HMAC and HKDF are the RFCs' is checked by vectors, not
    proved, and no pseudorandom-function property is proved.
  - The AEAD's tag is computed by the copied HMAC on encryption and checked by
    RustCrypto's on decryption; that the two agree is tested, not proved.
- **What would reopen it.** A finding in the copied code or its proofs; a
  vetted implementation the translation can read; a cost that matters on the
  devices that run it.
