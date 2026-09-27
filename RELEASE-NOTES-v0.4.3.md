# Tacenta assurance v0.4.3

**Tag:** `tacenta-assurance-v0.4.3`  
**Commit:** `2c89e0898b88231c54ffa5e9058817ea3f0cda75`

This assurance release records the current core tree and its evidence gates.
It includes the result-shaped Session proof plumbing, stricter randomness and
KEM contract boundaries, workflow and receipt checks, and the conformance
vectors present at the tagged commit.

The release does **not** claim an end-to-end proof of `Session::encrypt` or
`Session::decrypt`. The public proof ledger remains authoritative: those
operations have translated and conditional composition lemmas, but the
concrete primitive certificates and generated-result witnesses needed for an
unconditional Session theorem are still outstanding. Session orchestration and
prekey operations therefore remain tested or modelled where the ledger says so.

This tag also does not widen the cryptographic claims of the project. It is not
an audit, and the security of the underlying primitives and protocol design
remains an assumption stated in the assurance records. Private hardening work
must pass its own review and release process before any erasure-completeness
wording changes.

The annotated tag is SSH-signed by `will-natuvea`; the public key, fingerprint,
and tag-to-commit mapping are in [`RELEASE-SIGNERS.md`](RELEASE-SIGNERS.md).
The exact claims and limitations for this commit are in
[`tacenta-proofs/CLAIMS.md`](tacenta-proofs/CLAIMS.md) and
[`ASSURANCE.md`](ASSURANCE.md).
