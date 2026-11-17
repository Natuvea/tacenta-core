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

## Errata (2026-11-12)

Added after the tag. The text above is unchanged and describes the tag as it was
released; these corrections apply to it.

- **"session orchestration is at L2."** That sentence, under "What this tag does
  not establish", is not qualified. The level rested on the target decision of
  2026-09-15 (`tacenta-model/P6-L2-TARGET-DECISION.md`), which covers a bounded
  operation surface (`tacenta-model/SESSION-OPERATION-MODEL.md`), not every
  operation of the component. L2 includes L1, whose element "property tests"
  this tag's documents do not define. Under the definition in
  `tacenta-test-vectors/property-tests.md` on `main`, no property test of the
  prekey operations (creating, replenishing, rotating and publishing prekeys)
  was found in this tag's tree, and its property of the prekey store's
  re-encoding (`tacenta-core/tests/fuzz.rs`, line 108) reached its assertion only
  for a change that relabelled the store as version 4, while the store is
  written as version 5. So the sentence is to be read as: session orchestration
  is at L2 for the surface that decision covers, by that decision, and L1's
  property-test element is not shown for the prekey operations. This erratum
  changes no level or target and adds no evidence to the tag; `ASSURANCE.md` says
  what is shown now.
- **"the wire decoders, the protobuf profile and the PQXDH derivation are at L4,
  and the Double Ratchet, the sparse post-quantum ratchet and the Triple Ratchet
  are at L4 in its Components table".** That sentence, in the same bullet, is not
  qualified either. Every level includes L1, whose element "property tests" this
  tag's documents do not define. The definition in
  `tacenta-test-vectors/property-tests.md` on `main` asks five elements of a
  property test: a generator, a stated property, traceability to a
  specification sentence (in the test's own text, by an unambiguous file or
  module reference, or by an index that maps it), replay information and a
  stated case count. Against it, this tag's tree shows, per component:
  - for all six, no generated-input test cites a specification sentence in its
    own text or has one named in its file or module header (the third
    element), and no index maps one;
  - PQXDH derivation: no generated-input test with the nine functions of
    `tacenta-session` as its subject was found, so none of the five elements is
    shown for them; generated input reaches them only through establishment (for
    example the `session_receive` fuzz target, the seeded establishment tests and
    the differential harness), which tests neither their rules nor their outputs
    against the page;
  - protobuf profile: no property test in the five-element sense. Its one
    generated-input test (`tacenta-core/protobuf/src/lib.rs`, line 1168,
    `no_input_panics`) drives the reader's varint, tag and length reads with no
    stated property, no cited sentence and no assertion; the fuzz target
    `tacenta-core/fuzz/fuzz_targets/protobuf_bodies.rs` feeds generated bytes to
    both body parsers and checks only that they return, and the hosted workflow
    does not run it; nothing generated reaches the encoders;
  - wire decoders: the properties in `tacenta-core/tests/fuzz.rs` have a
    generator, a stated property, replay information and a case count (the
    environment's `PROPTEST_CASES`), and cite no sentence. For the initial message
    and `message_type` the one generated-input test with them as its subject,
    `decoders_never_panic` (line 136), checks only that they return; for the prekey bundle codec and the
    composite header on its own there is none. The fuzz target
    `tacenta-core/fuzz/fuzz_targets/wire_decoders.rs` reaches all four and asserts
    that what the bundle and composite decoders accept re-encodes to the same
    bytes, but it is fuzzing, which ADR-0008 lists as a separate element, and the
    hosted workflow does not run it. So none of the four has a property test with
    a stated property of the page and a cited sentence; and
    `truncation_is_rejected_cleanly` (line 198) asserts nothing a prefix could
    fail;
  - Double Ratchet, sparse post-quantum ratchet and Triple Ratchet: one seeded
    test each (`the_invariant_holds_after_every_step_and_round_trip`, in
    `tacenta-core/ratchet/src/lib.rs` line 1763, `tacenta-core/spqr/src/tests.rs`
    line 622 and `tacenta-core/triple/src/tests.rs` line 424) has every element but
    the third and asserts the crate's own invariant on honest runs; the receive
    rules over generated input are tested only by the differential harness
    (`tacenta-test-vectors/runners/rust/tests/differential.rs`, `check_ratchet`,
    `check_sparse`, `check_triple`), which compares the code with the model and
    is model-dependent evidence, not independent confirmation.

  So the sentence is to be read as: those six rows keep the T1 and T3 results this
  tag records for them, under the premises it states, and whether the Double
  Ratchet, the sparse post-quantum ratchet and the Triple Ratchet keep L4 stays
  the open question the same bullet names (`GAP-REGISTER.md`, `HL-FM-04`); under
  that definition, L1's property-test element, which every level includes, is not
  shown for any of the six at this tag. The
  theorems named in `tacenta-proofs/CLAIMS.md` at this tag are unaffected. This
  erratum concerns L1's property-test element only: it does not re-assess the
  vectors and the readings by the specification-only, project-controlled reader
  that L2 asks for, which this tag's `ASSURANCE.md` records for all six rows;
  whether any of them was missing at this tag is not checked here. It changes no
  level or target and adds no evidence to the tag; `ASSURANCE.md` says what is
  shown now.
