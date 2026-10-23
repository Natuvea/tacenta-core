# ADR-0010: the key derivation's SHA-256, HMAC and HKDF are written here

## Status

Proposed. For the owner to accept or reject on the rule-7 review (ADR-0008)
of the change that lands it. Until then this record states what that change
does and why; it does not decide it.

## Context

- **The rule.** Standard cryptography is not implemented here: primitives come
  from vetted crates and are assumed correct at the boundary. ADR-0002 made
  XEdDSA "the deliberate, specified exception" to that rule, because no
  vetted, permissively licensed Rust crate provided it. That record describes
  its own decision and is not edited here.
- **What the rule cost the key derivation.** `tacenta-kdf` wrapped RustCrypto's
  `hmac`, `hkdf` and `sha2`. Charon and Aeneas could not read those crates
  (their trait hierarchy and type-level block sizes do not elaborate), so
  `hmac_sha256` and `hkdf_sha256` were two opaque axioms in every translation,
  and the agreement hypotheses the T1 and T3 theorems take about them
  (`HmacAgrees`, `HkdfAgrees` and their siblings, ASM-05) could not be shown of
  the code at all, only assumed.
- **What was available.** The maintainer had written, in a separate,
  unpublished repository, a SHA-256, an HMAC-SHA256 and an HKDF-SHA256 in the
  subset Aeneas translates, with Lean proofs that the translated code computes
  a model written from FIPS 180-4, FIPS 198-1 and RFC 5869, and that this model
  equals tacenta-model's `Model.Sha256` and `Model.Kdf`.

## Decision

- `tacenta-kdf`'s SHA-256, HMAC and HKDF are that code, copied into
  `kdf/src/` and pinned in `kdf/src/lib.rs` by the source commit and the
  files' digests. The public functions and their signatures do not change.
  This is a second exception to the no-reimplementation rule, after XEdDSA.
- Every translation whose crate calls the KDF includes its bodies, and the six
  translations whose theorems take the KDF agreement hypotheses prove them of
  their translated code (ASM-05 lists them). The theorems still take the
  hypotheses as stated.
- The other users of SHA-2 and HMAC stay on RustCrypto: the AEAD's tag check
  on decryption, the root crate's identity and group digests, and XEdDSA's
  SHA-512.

## Alternatives rejected

- **Stay on RustCrypto.** Widely used, reviewed by others, and faster (the
  copied code is about 1.5 to 2.1 times slower on these operations, a
  measurement made in the source repository and not repeated here). Rejected
  because the agreement hypotheses would stay assumptions that no proof in
  this tree can discharge.
- **Adopt the code as an external dependency.** Depend on a published crate
  instead of copying it. Rejected for now: the source is not published, so
  there is nothing to depend on, and a dependency would add a supply-chain
  input for code whose only reader is its author. Publishing the source is
  still open (Consequences).
- **Translate RustCrypto's crates.** Not possible with the toolchain pinned
  here, for the reason in Context.

## Consequences

- **What replaces "vetted".** Proofs that the translated code equals
  tacenta-model's HMAC and HKDF (HKDF for outputs of at most 8160 bytes); a
  differential test against the RustCrypto crates it replaced
  (`kdf/tests/differential.rs`); the RFC test vectors; and an exact inventory
  of the compiled code's branches and indexed accesses, compared in CI
  (`tooling/check-constant-time-asm.sh`). None of these is a reading by
  someone other than the author.
- **Limits.**
  - Provenance: the source repository is unpublished and carries no licence
    statement, so a reader cannot check the pinned commit or digests. Whether
    to publish it, or to state the copied files' licence in this tree, is the
    owner's decision.
  - Timing is not measured. The inventory is a tripwire read from one pinned
    compiler and one codegen unit, cross-compiled for Linux, and its items
    were read by a tool-assisted session, not by a human.
  - Erasure: nothing wipes the intermediate values, as before.
  - That tacenta-model's HMAC and HKDF are the RFCs' is checked by vectors, not
    proved, and no pseudorandom-function property is proved.
  - The AEAD's tag is computed by the copied HMAC on encryption and checked by
    RustCrypto's on decryption; that the two agree is tested, not proved.
- **What would reopen it.** A finding in the copied code or its proofs; a
  vetted implementation the translation can read; the owner declining the
  exception, in which case `tacenta-kdf` returns to RustCrypto and the KDF
  hypotheses return to being assumptions.
