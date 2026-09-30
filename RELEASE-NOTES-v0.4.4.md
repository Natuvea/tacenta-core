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
   allocator-level regression tests through the public `Session`. It completes a
   sequence of hardening changes described in the published advisory
   `GHSA-9hv6-fr6w-9758`. Erasure is tested and is not proved.
2. **Identity keys (#205).** One rule, stated once in
   `tacenta-spec/protocol/identities-and-devices.md`, applies at every boundary
   that admits an identity key: canonical, on the curve and in the prime-order
   subgroup. See the published advisory `GHSA-r8w8-4rg9-mxhm`. The rule is tested
   and pinned by vectors. It is not proved.
3. **Hosted-inventory acceptance (#200)** and **vectors and reader (#202)**: an
   acceptance API and its stated checks, with 239 vector cases, and the vectors and
   the independent reader brought into line with the specification.
4. **CI gates (#194).** Each required job writes a receipt that records every
   command step, and the aggregation job refuses a receipt that misses a step.
5. **Documentation and record:** the signer mapping and v0.4.3 notes (#201), the
   assurance stamps (#195), a specification page on group messaging (#210), and the
   re-assessment of the assurance record (#211).
6. **Attestation refreshes (#206, #208, #209).** Each followed a squash merge that
   left the attestation check red on `main` until the refresh landed.

## What this tag does not establish

- **No end-to-end proof of `Session::encrypt` or `Session::decrypt`.** The ledger
  proves that they cannot panic, conditional on the contract records named in the
  theorem statements (15 to 44 named hypotheses each) and explicit headroom. Three of
  the five theorems also take an extra class and depend on compiler-trust axioms, and
  none of the six carries an axiom pin. The refinement branch lemmas take the leaf
  outcomes as hypotheses and are not claims. See `tacenta-proofs/CLAIMS.md`.
- **Not an audit.** No independent audit has issued a report.
- **A symbolic attacker.** The security theorems are proved against a symbolic
  attacker, not a computational one. XEdDSA is our own implementation, and the
  primitives are trusted, not verified.
- **Secret erasure and the identity-key rule are not proved.** See
  `GAP-REGISTER.md`, rows `ERASURE-NOT-PROVED` and `IDKEY-RULE-NOT-PROVED`.
- **The readiness gates are not met.** All four are stated as not met in
  `ASSURANCE.md`. `GAP-REGISTER.md` has three rows open at BLOCKING
  (`HL-IMP-01`, `HL-R1-SPARSE-TRANSLATION` and `E2E-07`) and one at AMBIGUOUS
  (`INV-01`).
- **Review status.** Of the 28 pull requests merged between `bba8f04` and
  `dea57eaf`, 11 were normative. Four of the most recent (#194, #200, #202, #205) merged
  on a review comment written by the account that authored them, and #204 on a
  comment headed "Independent review" from the same account. #210 and #211 are the
  same kind. No reviewer independent of the maintainer has read them, and no
  person has read the new specification text end to end. `ASSURANCE.md`, practice 7,
  has the detail.
- **Stamps.** `ASSURANCE.md`, `GAP-REGISTER.md` and `ASSURANCE-OBLIGATIONS.md` say
  they were assessed at `dea57eaf`. The tagged commit also contains #210 and #211,
  which that assessment does not cover.
- **Wording outside this repository.** The tacenta.com home page still uses the
  phrase "proven core" as its heading. The claim this tag supports is the scoped one
  in `ASSURANCE.md`: the wire decoders, the Double Ratchet, the sparse
  post-quantum ratchet, the Triple Ratchet, the protobuf profile and the PQXDH
  derivation are at L4 (panic-freedom, and success-side refinement under stated
  premises, against a symbolic attacker); the ML-KEM Braid and the erasure code
  are at L3; session orchestration is at L2.
- **Known stale statements.** `GAP-REGISTER.md`, row `STALE-WORDING-KNOWN`, lists
  sentences that are known to be out of date and were not changed here.

## Advisories

`GHSA-cgvw-9r5f-xrxp`, `GHSA-v95x-f6p3-4qxg` (corrected on 2026-09-30),
`GHSA-9hv6-fr6w-9758` and `GHSA-r8w8-4rg9-mxhm` are published on this repository.

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
