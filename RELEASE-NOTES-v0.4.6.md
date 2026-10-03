# Tacenta assurance v0.4.6

- **Tag:** `tacenta-assurance-v0.4.6`
- **Commit:** the commit the tag names. Read it with
  `git for-each-ref refs/tags/tacenta-assurance-v0.4.6 --format='%(tag) %(*objectname)'`.
  A tag object cannot be named inside the commit it tags, so this file does not
  quote it, and the tag's row in `RELEASE-SIGNERS.md` is added in a later commit.
- **Tagged:** 2026-10-03

This tag records the proof and evidence tree of this repository at the commit it
names. It is a snapshot of the tree, not a product release, and the number does
not relate to `tacenta-spec-v*`, to the `0.0.0` crate versions, or to the Tacenta
product releases (`v1.x`). Reference product 1.12.3 pins core `e06f8f41`, which is
earlier than this tag, so no product release is claimed to contain this commit or
any change below.

## Two changes to behaviour and to the model

Unlike `tacenta-assurance-v0.4.5`, this tag contains a change to the
specification, the vectors and the Rust, and changes to the model.

1. **The sparse ratchet counts the store a skip leaves (#229).** A skip from chain
   counter `c` to `upto` now deletes every stored key of the epoch under a number
   `n` with `c < n <= upto` from a working copy, and refuses `SkippedStoreFull` when
   the survivors plus the keys to store exceed `MAX_SKIPPED_STORE` (2,000). Before,
   it counted the store it found. This relaxes one refusal, and only for a stored
   state that already holds a key in the replaced range: a store of 1,999 keys that
   holds keys 1 and 2 of the epoch, with the chain at 0, now accepts message 4 and
   ends at exactly 2,000, where it refused. It is the order the classical ratchet
   already uses. The text is in `tacenta-spec/protocol/sparse-pq-ratchet.md` and
   `tacenta-spec/CHANGELOG.md`; the model, four vectors, `tacenta-core/spqr`, the
   generated translation and the T3 proof of `skip_message_keys_refines` follow it.
   The project's independent reader already implemented this order. It is
   project-controlled evidence (`GAP-REGISTER.md`, row `READER-INDEPENDENCE`). The
   translation was regenerated on one platform, macOS on Apple silicon, with the
   pinned release; no Linux regeneration exists, and the row
   `HL-R1-SPARSE-TRANSLATION` stays Open and BLOCKING until one does. No
   `tacenta-spec-v*` tag covers this change, and it is not a security advisory.
2. **The model's Braid send reads two draws at the first send (#234).**
   `tacenta-model/Model/Lifecycle.lean` computes something different in three
   places. The Braid send reads two draws at `KeysUnsampled` and one at
   `HeaderReceived`, as `mlkem-braid.md` has said since 2026-09-11 (key generation
   draws 64 bytes); before, the model read one 32-byte draw at `KeysUnsampled`.
   KEM encapsulation refuses a key that the oracle's new `kemValid` rejects before
   it reads a draw. XEdDSA signing reads two draws. The tags
   `tacenta-assurance-v0.4.2` to `tacenta-assurance-v0.4.5` contain the one-draw
   model. No claimed theorem took the one-draw form. The shipped code always filled
   64 bytes there, so this corrects the model against the page and not the product.

## Hypotheses found false or empty, and what is now recorded

- **Five hypotheses and evidence records of the lifecycle dispatch layer were false
  or empty (#223).** Seventeen theorems of `UnitLifecycleT3.lean` and
  `UnitLifecycleInitialDispatch.lean` were affected and sixteen held vacuously as
  stated. None was claimed or pinned. Each result has a Lean proof, and the register
  row `DISPATCH-EVIDENCE-VACUITY` records it.
- **The integration screens the records that the session contract branch added
  (#234).** The concrete branch evidence record, the two end-to-end records that
  contain it and the one-draw Braid agreement are refuted in Lean, and no theorem
  takes them now. Their replacements (per-run records and a counted agreement) are
  stated and bounded, and are **not shown satisfiable as a whole**. The row stays
  Open and BLOCKING. The statement of the KEM success clause is also met by an
  oracle that never encapsulates. The register row lists what is not decided.
- **The lifecycle headroom records are shown satisfiable (#226), and the four
  session contract records follow from an axiom base that has a model (#220).**
  `SESSION-CONTRACT-VACUITY` stays Open and BLOCKING: three assumptions that no
  record states are not checked against the real primitives, and the witness session
  has no pending initial message. The register row lists the rest.

## What changed since `tacenta-assurance-v0.4.5`

Sixteen commits on `main`, listed here by pull request. Proofs, scripts and
documents change, apart from the two changes above.

1. **Signer file and counts (#219, #222, #225, #227).** `RELEASE-SIGNERS.md` lists
   `tacenta-assurance-v0.4.5`. `DivCeilValue` counts as the fourteenth session
   contract. A root-level response document is removed. The maintainer's decisions
   are recorded: `HL-IMP-01` is closed, because the session replay with its listed
   limits satisfies the row, and `HL-IMP-01-READER` tracks the step that remains;
   `INV-01` is NONBLOCKING.
2. **Proofs (#220, #224, #226, #230, #231, #234).** Besides the above: the Braid's
   send and receive preserve `State.sized` (#224); what the Session
   unit's Braid theorems assume about the KEM, the KDF, erasure and `Vec::truncate`
   (shown to have a model, not checked against the real functions), the erasure field
   proved by the kernel instead of by `bv_decide` and `native_decide`, and frame results for what a refused lifecycle
   call leaves behind (#231); numeric premises shown met, and a floor of required
   statement pins (#230).
3. **Tooling (#228, #232, #233).** Evidence tooling for gates 3 and 4; the
   translation attestation refreshed after a squash; negative controls for gates
   that had none, a mutation harness (204 single edits) and a generated inventory
   of gates (73 rows, 58 with a control that runs in CI, 3 only locally, 12 none).
4. **A diagram** in the README of how the specification, model, code, proofs and
   record fit together.

Counts from `verification-manifest.json`: pinned theorems 179 to 647, kernel-only 99
to 260, opaque-external 68 to 374, compiler-trusted 12 to 13; statement pins (not
counted in `tacenta-assurance-v0.4.5`) 394, all on a required floor; ledger entries
257 to 734, distinct claimed theorems 253 to 730, claimed without a pin 74 to 83.
The increase counts axiom pins and results about hypotheses and evidence records,
including results that a hypothesis is false or cannot be met. It does not measure
how much of the product is proved.

## What this tag does not establish

- **No end-to-end proof of `Session::encrypt` or `Session::decrypt`.** `E2E-01` is
  Open and BLOCKING. The retry loop's induction, the T3 theorems for establishment
  and `invariant_preserved` do not exist. The lifecycle theorems take records that
  are not shown satisfiable as a whole.
- **The readiness gates are not met.** All four are stated as not met in
  `ASSURANCE.md`. `GAP-REGISTER.md` has four rows open at BLOCKING
  (`HL-R1-SPARSE-TRANSLATION`, `SESSION-CONTRACT-VACUITY`,
  `DISPATCH-EVIDENCE-VACUITY` and `E2E-01`, the last while the tacenta.com home page
  says "proven core"). Gate 3 needs a frozen candidate and a reader who is not the
  maintainer. Twelve gates still have no negative control.
- **Not an audit.** No independent audit has issued a report.
- **A symbolic attacker.** The security theorems are proved against a symbolic
  attacker, not a computational one. XEdDSA is this project's own implementation,
  and the primitives are trusted, not verified.
- **Secret erasure and the identity-key rule are not proved.** See
  `GAP-REGISTER.md`, rows `ERASURE-NOT-PROVED` and `IDKEY-RULE-NOT-PROVED`.
- **Review status.** #229 merged on a recorded acceptance by the maintainer, after
  six readers who had not seen the work. #231 and #234 merged on review comments
  written by the account that authored them, which say they are not independent of
  the maintainer, after four readers each who had not seen the work. The maintainer
  arranged all of those readers. No reader independent of the maintainer has read the
  new Lean or the changed documents end to end. `ASSURANCE.md`, practice 7, has the
  detail.
- **Stamps.** `ASSURANCE.md` and `GAP-REGISTER.md` say they were assessed at
  `dea57eaf`. The pin counts in `ASSURANCE.md` and the trust-base sentences beside
  them are those of this tree.
- **Wording outside this repository.** The tacenta.com home page still uses the
  phrase "proven core" as its heading. The claim this tag supports is the scoped
  one in `ASSURANCE.md`.
- **Known stale statements.** `GAP-REGISTER.md`, row `STALE-WORDING-KNOWN`, lists
  sentences that are known to be out of date and were not changed here.

## Advisories

`GHSA-cgvw-9r5f-xrxp` (fixed in `36b5db2`), `GHSA-v95x-f6p3-4qxg` (fixed in
`ca3eba85`), `GHSA-9hv6-fr6w-9758` (fixed in `fa7cd1bd`) and `GHSA-r8w8-4rg9-mxhm`
(fixed in `e06f8f41`) are published on this repository. This tag contains all four
fixes. The changes above are not security advisories: they concern a refusal rule
of the sparse ratchet, a model definition and hypotheses in the proofs, and not a
flaw in the product.

## Verifying the tag

`RELEASE-SIGNERS.md` names the maintainer key and shows how to check a signature.
Until the key is registered as a signing key, GitHub shows the tag as
"Unverified"; that badge does not mean the signature is bad. The tag's own row in
that file is added after the tag exists.

## Read next

- [`tacenta-proofs/CLAIMS.md`](tacenta-proofs/CLAIMS.md)
- [`tacenta-proofs/LIMITATIONS.md`](tacenta-proofs/LIMITATIONS.md)
- [`GAP-REGISTER.md`](GAP-REGISTER.md)
- [`ASSURANCE.md`](ASSURANCE.md)
- [`ASSURANCE-OBLIGATIONS.md`](ASSURANCE-OBLIGATIONS.md)
