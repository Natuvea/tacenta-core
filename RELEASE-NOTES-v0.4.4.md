# Tacenta assurance v0.4.4

- **Tag:** `tacenta-assurance-v0.4.4`
- **Commit:** the commit the tag names. Read it with
  `git for-each-ref refs/tags/tacenta-assurance-v0.4.4 --format='%(tag) %(*objectname)'`.
  A tag object cannot be named inside the commit it tags, so this file does not
  quote it, and the tag's row in `RELEASE-SIGNERS.md` is added in a later commit.
- **Tagged:** 2026-09-30

This tag records the proof and evidence tree of this repository at the commit it
names. It is a snapshot of the tree, not a product release, and the number does
not relate to `tacenta-spec-v*`, to the `0.0.0` crate versions, or to the Tacenta
product releases (`v1.x`). Reference product 1.12.3 pins core `e06f8f41`, which is
earlier than this tag, so no product release is claimed to contain this commit.

## What changed since `tacenta-assurance-v0.4.3`

Twelve pull requests merged after `tacenta-assurance-v0.4.3` (`2c89e089`): #194,
#195, #200, #201, #202, #204, #205, #206, #208, #209, #210 and #211.

Unlike v0.4.3, this tag changes code, the specification and the vectors:

1. **Secret erasure (#204).** The sparse post-quantum ratchet's chain container no
   longer leaves secret copies behind on chain removal or drop, with three
   allocator-spy regression tests in `tacenta-core/tests/spqr_erasure_public.rs`:
   two through the public `Session` (chain retirement and drop) and one directly
   on the sparse ratchet state. They build only with the non-default feature
   `private-erasure-review`, which one CI step turns on, and they cover the sparse
   ratchet's chain container only. The change completes a sequence of hardening
   changes described in the published advisory `GHSA-9hv6-fr6w-9758`. Erasure is
   tested and is not proved.
2. **Identity keys (#205).** One rule, stated once in
   `tacenta-spec/protocol/identities-and-devices.md`, applies at every boundary
   that admits an identity key: canonical, on the curve and in the prime-order
   subgroup. See the published advisory `GHSA-r8w8-4rg9-mxhm`. The rule is tested
   and pinned by vectors. It is not proved.
3. **Hosted-inventory acceptance (#200)** and **vectors and reader (#202)**: an
   acceptance API and its stated checks, with 239 vector cases in four files (238
   new since v0.4.3), and the vectors and the independent reader brought into line
   with the specification.
4. **CI gates and the axiom allowlist (#194).** Nine of the ten required jobs write
   a receipt that records every command step (the `sign-off` receipt only on pull
   requests), and the tenth, `assurance-receipts`, collects them and refuses a
   receipt that misses a step, records an extra one or records any outcome but
   success. The required workflow is compared with an expected form, and the axioms
   of the generated Lean are compared by name and type with a recorded allowlist.
5. **Documentation and record:** the signer mapping and v0.4.3 notes (#201), the
   assurance stamps (#195), a change to the group-messaging specification page that
   removes one cited paper and adds a section on what the page rests on (#210), and
   the re-assessment of the assurance record (#211).
6. **Attestation refreshes (#206, #208, #209).** Each followed a squash merge that
   left the attestation check red on `main` until the refresh landed.
7. **Lowered assessments (#211).** Practice 2 (explicit assumptions) and practice 10
   (fuzzing and property tests) are now Partial; they were Done and Good. The
   ML-KEM Braid row reads L3; it read "L3/L4". In `ASSURANCE-OBLIGATIONS.md` the
   Braid component row is BLOCKING, and two rows whose reopen condition has fired
   (`MU-01` and the Session orchestration row) are AMBIGUOUS; they were CLOSED.
   `E2E-01` in the gap register is BLOCKING while the tacenta.com home page says
   "proven core". No level was raised and no gap was closed.

## What this tag does not establish

- **No end-to-end proof of `Session::encrypt` or `Session::decrypt`.** The ledger
  proves that they cannot panic, conditional on the contract records named in the
  theorem statements (15 to 44 named hypotheses each) and explicit headroom. Three
  of the five theorems also take an extra class and depend on compiler-trust axioms,
  and none of the six carries an axiom pin. The refinement branch lemmas take the
  leaf outcomes as hypotheses and are not claims. See `tacenta-proofs/CLAIMS.md`.
- **Not an audit.** No independent audit has issued a report.
- **A symbolic attacker.** The security theorems are proved against a symbolic
  attacker, not a computational one. XEdDSA is this project's own implementation,
  and the primitives are trusted, not verified.
- **Secret erasure and the identity-key rule are not proved.** See
  `GAP-REGISTER.md`, rows `ERASURE-NOT-PROVED` and `IDKEY-RULE-NOT-PROVED`.
- **The readiness gates are not met.** All four are stated as not met in
  `ASSURANCE.md`. `GAP-REGISTER.md` has four rows open at BLOCKING
  (`HL-IMP-01`, `HL-R1-SPARSE-TRANSLATION`, `E2E-07` and `E2E-01`, the last while
  the tacenta.com home page says "proven core") and one at AMBIGUOUS (`INV-01`).
- **Review status.** Of the 28 pull requests merged between `bba8f04` and
  `dea57eaf`, 11 were normative. Four of the most recent (#194, #200, #202, #205)
  merged on a review comment written by the account that authored them, and #204 on
  a comment headed "Independent review" from the same account. #210 and #211 are
  the same kind: each merged on a review comment written by the account that
  authored it, which says it is not independent of the maintainer. The review
  comments on #200, #202 and #210 add that no person has read the new specification
  text end to end. `ASSURANCE.md`, practice 7, has the detail.
- **Stamps.** `ASSURANCE.md` and `GAP-REGISTER.md` say they were assessed at
  `dea57eaf`. `ASSURANCE-OBLIGATIONS.md` says so only for its gate evidence
  inventory and the rows that cite it, and dates the rest of the file to
  2026-09-14, at `c7499a9b`. The tagged commit also contains #210 and #211, which
  that assessment does not cover.
- **Wording outside this repository.** The tacenta.com home page still uses the
  phrase "proven core" as its heading. The claim this tag supports is the scoped one
  in `ASSURANCE.md`: the wire decoders, the protobuf profile and the PQXDH
  derivation are at L4, and the Double Ratchet, the sparse post-quantum ratchet and
  the Triple Ratchet are at L4 in its Components table (panic-freedom, and
  success-side refinement under stated premises, against a symbolic attacker), but
  whether those three keep L4 is undecided (`GAP-REGISTER.md`, `HL-FM-04`); the
  ML-KEM Braid and the erasure code are at L3; session orchestration is at L2.
- **Known stale statements.** `GAP-REGISTER.md`, row `STALE-WORDING-KNOWN`, lists
  sentences that are known to be out of date and were not changed here.

## Advisories

`GHSA-cgvw-9r5f-xrxp` (fixed in `36b5db2`), `GHSA-v95x-f6p3-4qxg` (fixed in
`ca3eba85`; the advisory's affected range and fix commit were corrected on
2026-09-30), `GHSA-9hv6-fr6w-9758` (fixed in `fa7cd1bd`) and
`GHSA-r8w8-4rg9-mxhm` (fixed in `e06f8f41`) are published on this repository. This
tag contains all four fixes.

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
- [`tacenta-proofs/GATE-MUTATION-RECORD.md`](tacenta-proofs/GATE-MUTATION-RECORD.md)
