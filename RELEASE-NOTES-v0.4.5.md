# Tacenta assurance v0.4.5

- **Tag:** `tacenta-assurance-v0.4.5`
- **Commit:** the commit the tag names. Read it with
  `git for-each-ref refs/tags/tacenta-assurance-v0.4.5 --format='%(tag) %(*objectname)'`.
  A tag object cannot be named inside the commit it tags, so this file does not
  quote it, and the tag's row in `RELEASE-SIGNERS.md` is added in a later commit.
- **Tagged:** 2026-10-01

This tag records the proof and evidence tree of this repository at the commit it
names. It is a snapshot of the tree, not a product release, and the number does
not relate to `tacenta-spec-v*`, to the `0.0.0` crate versions, or to the Tacenta
product releases (`v1.x`). Reference product 1.12.3 pins core `e06f8f41`, which is
earlier than this tag, so no product release is claimed to contain this commit.

## A correction to the ledger

`tacenta-assurance-v0.4.2`, `v0.4.3` and `v0.4.4` contain a hypothesis that is
false. `SessionUnitBraidT1.DecoderMessageTotal` said that `Decoder::message`
returns for every decoder. A decoder that needs `(Usize.max + 1) / 32` chunks and
holds that many has a message, and assembling it appends more bytes than a vector
can hold. The field was in `BraidReceiveContracts`, which the contract records for
`decrypt` and `establish_responder` contain, so at those three tags the theorems
`decrypt_no_panic`, `decrypt_ratchet_no_panic` and `establish_responder_no_panic`
held vacuously as stated, and so did five Braid theorems of the Session unit. The
notes of `v0.4.3` and `v0.4.4`, which say that the ledger proves that
`Session::encrypt` and `Session::decrypt` cannot panic conditional on the contract
records, are not edited, because they describe those tags.

The defect was in a hypothesis and not in the product: the Braid builds its decoders
from protocol constants or from `Decoder::from_bytes`, which refuses `needed >
MAX_CODEWORDS`, so no decoder the Braid holds has that many chunks. #216 recorded
the defect, with a Lean refutation on both platform widths, and #217 repaired it:
the field is stated for decoders that need at most `MAX_CODEWORDS = 65536` chunks,
and the receive theorems take that bound from the state.

The repair does not show that any of the four contract records can be met. It adds
one assumption (`divCeilValue`, the value of `usize::div_ceil` at divisor 32), and
the repaired field is true of the translation and not of the Rust `Decoder::message`
on a decoder with a small `needed` and a huge `size`, which `Decoder::invariant`
excludes. The gap-register row `SESSION-CONTRACT-VACUITY` stays Open and BLOCKING.

## What changed since `tacenta-assurance-v0.4.4`

Five pull requests merged after `tacenta-assurance-v0.4.4` (`75387aa9`): #213, #214,
#215, #216 and #217. This tag changes proofs, scripts and documents only. No
specification page, model module, vector or Rust source changes.

1. **The signer file (#213).** `RELEASE-SIGNERS.md` lists `tacenta-assurance-v0.4.4`.
2. **`E2E-07` closed (#214).** The register row is closed on a recorded run at
   `75387aa9`, and two cases no test reaches are recorded.
3. **Pins for the six Session T1 theorems (#215).** Each now carries an axiom pin;
   two `native_decide` steps are settled in the kernel; `attest.py` keeps a floor of
   required pins and refuses a pin block left in a comment.
4. **The correction (#216) and the repair (#217)**, above. #217 adds two modules, a
   control that holds the unit-only edits of three generated Braid copies to their
   anchors, and 17 required pins.

Counts from `verification-manifest.json`: pinned theorems 150 to 179, kernel-only 94
to 99, opaque-external 40 to 68, compiler-trusted 16 to 12; distinct claimed theorems
230 to 253, ledger entries 234 to 257, claimed without a pin 80 to 74.

## What this tag does not establish

- **No end-to-end proof of `Session::encrypt` or `Session::decrypt`.** The ledger
  proves that they cannot panic, conditional on the contract records named in the
  theorem statements (15 to 45 named hypotheses each) and explicit headroom. No
  theorem shows any of the four records can be met. Each of the six theorems carries
  an axiom pin, which fixes the axioms it depends on and says nothing about whether
  its hypotheses can be met. The refinement branch lemmas take the leaf outcomes as
  hypotheses and are not claims. See `tacenta-proofs/CLAIMS.md`.
- **Other hypotheses of the same kind are not checked.** `ErasureAgrees` and
  `ErasureCloneAgrees`, the headroom records and the numeric preconditions listed in
  `tacenta-proofs/LIMITATIONS.md` have not been shown satisfiable. The one that was
  checked was false.
- **Not an audit.** No independent audit has issued a report.
- **A symbolic attacker.** The security theorems are proved against a symbolic
  attacker, not a computational one. XEdDSA is this project's own implementation,
  and the primitives are trusted, not verified.
- **Secret erasure and the identity-key rule are not proved.** See
  `GAP-REGISTER.md`, rows `ERASURE-NOT-PROVED` and `IDKEY-RULE-NOT-PROVED`.
- **The readiness gates are not met.** All four are stated as not met in
  `ASSURANCE.md`. `GAP-REGISTER.md` has four rows open at BLOCKING (`HL-IMP-01`,
  `HL-R1-SPARSE-TRANSLATION`, `SESSION-CONTRACT-VACUITY` and `E2E-01`, the last while
  the tacenta.com home page says "proven core") and one at AMBIGUOUS (`INV-01`).
- **Review status.** #214, #215, #216 and #217 merged on a review comment written by
  the account that authored them, which says it is not independent of the
  maintainer. No person has read the new Lean or the changed documents end to end.
  `ASSURANCE.md`, practice 7, has the detail.
- **Stamps.** `ASSURANCE.md` and `GAP-REGISTER.md` say they were assessed at
  `dea57eaf`. The pin counts in `ASSURANCE.md` and the trust-base sentences beside
  them are those of this tree.
- **Wording outside this repository.** The tacenta.com home page still uses the
  phrase "proven core" as its heading, and its assurance page has not been updated
  for the correction above. The claim this tag supports is the scoped one in
  `ASSURANCE.md`: the wire decoders, the protobuf profile and the PQXDH derivation
  are at L4, and the Double Ratchet, the sparse post-quantum ratchet and the Triple
  Ratchet are at L4 in its Components table (panic-freedom, and success-side
  refinement under stated premises, against a symbolic attacker), but whether those
  three keep L4 is undecided (`GAP-REGISTER.md`, `HL-FM-04`); the ML-KEM Braid and the
  erasure code are at L3; session orchestration is at L2.
- **Known stale statements.** `GAP-REGISTER.md`, row `STALE-WORDING-KNOWN`, lists
  sentences that are known to be out of date and were not changed here.

## Advisories

`GHSA-cgvw-9r5f-xrxp` (fixed in `36b5db2`), `GHSA-v95x-f6p3-4qxg` (fixed in
`ca3eba85`), `GHSA-9hv6-fr6w-9758` (fixed in `fa7cd1bd`) and `GHSA-r8w8-4rg9-mxhm`
(fixed in `e06f8f41`) are published on this repository. This tag contains all four
fixes. The correction above is not a security advisory: it concerns a hypothesis in
the proofs and not a flaw in the product.

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
