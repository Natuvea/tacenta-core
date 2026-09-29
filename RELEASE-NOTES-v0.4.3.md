# Tacenta assurance v0.4.3

- **Tag:** `tacenta-assurance-v0.4.3`
- **Commit:** `2c89e0898b88231c54ffa5e9058817ea3f0cda75`
- **Tagged:** 2026-09-26

This tag records the proof and evidence tree of this repository at
`2c89e089`. It is a snapshot of the tree, not a product release, and the
number does not relate to `tacenta-spec-v*`, to the `0.0.0` crate versions, or
to the Tacenta product releases (`v1.x`). No product release is claimed to
contain this commit.

## What changed since `tacenta-assurance-v0.4.2`

Six pull requests were merged after `tacenta-assurance-v0.4.2` (`d072ef2`):
#187, #188, #189, #190, #191 and #193.

**No file under `tacenta-core/`, `tacenta-spec/` or `tacenta-test-vectors/`
changed.** The Rust, the specification and the vectors are the same as at
`tacenta-assurance-v0.4.2`.

What did change:

1. **CI evidence gates.** Required jobs may not be disabled or made
   non-failing. The receipt collector now runs even when a required job fails
   or is skipped, and its validator fails closed on missing, failed or
   cross-candidate records. The receipt validator now rejects a required check
   that is declared optional or inapplicable, or that was produced for another
   commit. The validator at `tacenta-assurance-v0.4.2` accepted all three.
2. **`tacenta-model`.** A malformed KEM public key is now modelled as a refusal
   that consumes no random draw, which matches the order in
   `tacenta-core/boundary/src/kem.rs`.
3. **Proof scaffolding.** The KEM-encapsulation and XEdDSA-signing no-panic
   contracts now assume a random source that does not panic, and the evidence
   type for the public `Session::decrypt` proof covers more initial-message
   cases. The added cases take evidence premises whose satisfiability this tag
   does not establish.

None of these adds a claim to the ledger.

## What this tag does not establish

- **No end-to-end proof of `Session::encrypt` or `Session::decrypt`.** The
  ledger proves that they cannot panic, conditional on twelve named boundary
  contracts and explicit headroom. It also holds refinement branch lemmas that
  take the leaf outcomes as hypotheses and are not composed with the leaf
  theorems. Lean theorems named `public_encrypt_end_to_end` and
  `public_session_decrypt_end_to_end` exist at this tag. They take per-branch
  evidence as hypotheses, are not pinned, and are not claims.
- **Not an audit.** No independent audit has issued a report.
- **A symbolic attacker.** The security theorems are proved against a symbolic
  attacker, not a computational one. XEdDSA is our own implementation, and the
  primitives are trusted, not verified.
- **Secret erasure is not proved.** See "Secret deletion is partial" in
  `LIMITATIONS.md`. The published advisory on replay detection states that a
  separate erasure follow-up remains open.
- **The readiness gates are not met.** `GAP-REGISTER.md` has three rows open
  at BLOCKING at this tag: `HL-IMP-01`, `HL-R1-SPARSE-TRANSLATION` and
  `E2E-07`.
- **Stale assessment stamp.** `ASSURANCE.md` and `GAP-REGISTER.md` at this tag
  say they were last assessed at `bba8f04`, not at `2c89e089`.

This is a research implementation and has not been independently audited
(`SECURITY.md`).

## Review status

Of the six pull requests, one (#187) was approved by an account other than the
author of its commits. #188 and #189 were approved by the account that wrote
them. #190, #191 and #193 were merged with no live approval. The independent
review of the proof ledger has not happened: the evidence manifest records
`independent-ledger-review` as `pending`, and gate 3 in `ASSURANCE.md` is not
met. Tool-assisted checks and reviews are evidence of what they ran, not
independent review (`README.md`).

## Relation to published advisories

`tacenta-assurance-v0.4.2` is the patched core version named by the published
advisory GHSA-v95x-f6p3-4qxg. This tag descends from it and contains that fix.

## Signature

The annotated tag is SSH-signed by `will-natuvea`. The public key, fingerprint,
tag-to-commit mapping and the limits of that verification are in
[`RELEASE-SIGNERS.md`](RELEASE-SIGNERS.md).

## The exact claims for this tag

These links are pinned to the tag, not to `main`:

- [`tacenta-proofs/CLAIMS.md`](https://github.com/Natuvea/tacenta-core/blob/tacenta-assurance-v0.4.3/tacenta-proofs/CLAIMS.md)
- [`tacenta-proofs/LIMITATIONS.md`](https://github.com/Natuvea/tacenta-core/blob/tacenta-assurance-v0.4.3/tacenta-proofs/LIMITATIONS.md)
- [`GAP-REGISTER.md`](https://github.com/Natuvea/tacenta-core/blob/tacenta-assurance-v0.4.3/GAP-REGISTER.md)
- [`ASSURANCE.md`](https://github.com/Natuvea/tacenta-core/blob/tacenta-assurance-v0.4.3/ASSURANCE.md)
