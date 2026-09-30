# Assurance

This records where `tacenta-core` stands against the expectations in
[ADR-0008](tacenta-spec/decisions/ADR-0008-assurance-expectations.md), and what
comes next. It is a summary. For what is proven, `tacenta-proofs/CLAIMS.md` and
`LIMITATIONS.md` are the record. For what the vectors pin,
`tacenta-test-vectors/conformance-manifest.md` is. For current gate and target
obligations, see [ASSURANCE-OBLIGATIONS.md](ASSURANCE-OBLIGATIONS.md).

Last assessed: 2026-09-30, at `dea57eaf`, which is 28 commits after the
assessment of 2026-09-25 at `bba8f04`. Practices 1 to 10, the Rust expectations,
the Roadmap, the Components table and the readiness section were each read again
against the tree at `dea57eaf`, and the counts they quote were recomputed from
the tree. The reads were tool-assisted (see the next paragraph) and were not
made by anyone independent of the maintainer's accounts. This assessment did not
run every acceptance criterion of every closed gap row. `GAP-REGISTER.md` and
`ASSURANCE-OBLIGATIONS.md` carry their own stamps.

Parts of this project are written and reviewed with tool assistance. The
README's "Development assistance" section says how, and that tool-assisted
checks and reviews are evidence of what they ran, not independent review.

The readiness gates below are not met. Gate 1 is not met: practice 5 is
BLOCKING in `ASSURANCE-OBLIGATIONS.md`, and the ML-KEM Braid row is below its L4
target. Gate 2 is not met: three rows are open at BLOCKING in `GAP-REGISTER.md`
(HL-IMP-01, HL-R1-SPARSE-TRANSLATION and E2E-07), and INV-01 is open at
AMBIGUOUS. Gates 3 and 4 have not been met either; see the readiness section.
This record does not close a practice or replace the review and evidence
obligations recorded below.

## Practices

| # | Practice | Status | Where it stands | Next |
|---|---|---|---|---|
| 1 | Specification before implementation | Partial | ADR-0006 makes the specification normative, and the pull-request template asks for the specification to change first. The commit order does not always show it: in #200 the first three commits change the specification and the code together, in #202 a reader commit on `legacy_blocked` precedes the specification commit that states the rule, and in #205 the first commit that implements the identity-key rule precedes the first specification commit. The review records on those pull requests describe the order of the later commits. Much of the text was written after the code, as built. The formal statement of rules is in the model, not the prose. | New rules are written as invariants, preconditions, transitions and failures before code. |
| 2 | Explicit assumptions | Done | `tacenta-spec/threat-model/` states the assets, adversaries, assumptions and exclusions. `tacenta-spec/security-properties/` states the security properties as numbered requirements, each naming the assumptions it rests on, and records the gaps in `limitations.md`. `CLAIMS.md` opens with what is not proved, `LIMITATIONS.md` lists what the proofs trust, and the `#print axioms` pins held under `#guard_msgs` cover 150 theorems (`attest.py --check` recomputes the count). 80 of the 230 theorems that `CLAIMS.md` claims carry no pin, among them the five Session T1 theorems and the lemma `invariant_gives_preconditions`; `tacenta-proofs/manifests/verification-manifest.json` holds both lists (`claims` and `axiom_pins`). | Keep them current as requirements, proofs and code change. |
| 3 | Small trusted base | Good | No `unsafe` in any library of the `tacenta-core` workspace in the default feature set, and `forbid(unsafe_code)` in the library root of each of its 16 packages. One test target, `tests/timing.rs`, has one `unsafe` inline-assembly block, at line 230, compiled only on aarch64 macOS, and the integration-test crates carry no `forbid` attribute. The non-default feature `private-erasure-review`, which one CI step (`rust_spqr_erasure`) turns on, lifts the attribute in `tacenta-spqr` and compiles five `unsafe` blocks into that crate (review instrumentation that keeps key bytes in a static array), and adds an allocator spy with `unsafe` code in `tests/spqr_erasure_public.rs`. It is off in every default and release build. No FFI in the core. Trusted: libcrux, the dalek curves, the RustCrypto AES, CBC, HKDF, HMAC and SHA-2 crates, the in-repository primitive crate `tacenta-boundary` (XEdDSA and the identity-key predicate among its functions), the Aeneas translation, the Lean toolchain, the Mathlib build cache, and proofs checked by evaluation. `LIMITATIONS.md` lists them under "Trusted, not verified", "Secret deletion is partial" and the Session unit's primitive contracts. | Keep it; review any addition. |
| 4 | Model separate from implementation | Good | The Lean model, its translation, and T3 refinement for the ratchets, Braid, decoders and PQXDH derivation. Vectors pin the rest. All six persisted states and the two erasure coders are modelled and pinned by vectors; the prekey store carries two things the model cannot state (the stored-signature rule and `kem_pair`'s content clauses) and the session one (that `ratchet_private`'s public half is `dhs_pub`); the rows below say which. P6 covered its selected durable session/prekey operation surface at L2 by [its target decision](tacenta-model/P6-L2-TARGET-DECISION.md) of 2026-09-15, which keeps the bounded and declared-crypto exclusions explicit. Two later changes touch that surface: the `legacy_blocked` marker rules (#202) and the identity-key refusals at establishment and import (#205). Both are modelled, pinned by vectors and driven by the differential harness. Neither is in `SESSION-OPERATION-MODEL.md` or in the 27-trace corpus, and the decision has not been reopened. | Reopen the P6 decision for the changes named above, as its revisit triggers require. |
| 5 | Invariants, not examples | Partial | T1 panic-freedom, T3 refinement, decoded-state invariants, and forward secrecy and post-compromise security against a symbolic attacker. The classical and sparse ratchets' models stop at the counter ceilings the pages state, and persistence vectors pin those ceilings against `tacenta-core`. `Model.Braid` stops at its epoch ceiling too, and its reserved epoch and `Ct2Sampled` boundary transitions are pinned in vectors and the differential harness. `evidence-index.json` has checked `INV-*` records for the session/prekey invariants, including explicit operation effects and headroom dispositions. The records predate the identity-key clause that #205 added to `Session::invariant` and `PrekeyStore::invariant`; `INV-IDENTITY-ROLE` and `INV-CANONICAL-RESTORE` do not name it. [The recorded scope decision](tacenta-proofs/PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md) keeps the successor-headroom limit on success refinement explicit; it does not claim boundary success refinement. | Obtain the required semantic review of the invariant predicates and their cited coverage. |
| 6 | Verification in CI | Partial | Lean builds, the `sorryAx` audit and scan, kernel replay, translation checksum checks, vectors current with the model (31 of the 45 vector files; the other 14 are checked against their schemas, the Rust runner and the reader only), and a reader that imports nothing from the implementation (written from the specification alone in its first seven passes, and maintained in the repository since with the implementation in view, which its README records). The reader and its pass records are project-controlled evidence, not independent review; the translation checksum does not prove regeneration. All ten jobs of `.github/workflows/ci.yml` are required status checks on `main`. Each required job writes a receipt that records the outcome of every command step, and the `assurance-receipts` job refuses a receipt that misses a step, records an extra one, or records any outcome but success; `tooling/check-workflows.sh` holds the workflow to `tooling/required-steps.json`. A pull request that edits the workflow, that file and the checker together is judged by its own edit, and `main` requires no review. The fuzz targets and the timing measurements run outside this repository. A squash merge to `main` has left the attestation check red until a refresh pull request landed (#204, #194 and #205). | Obtain an independent claim review. |
| 7 | Reviewed normative changes | Partial | ADR-0008 requires a recorded review for each normative change. Historic pull-request records show that this was not consistently done, including [PR #129](https://github.com/Natuvea/tacenta-core/pull/129). The project has not yet produced a complete historic count and retrospective disposition. `main` requires the ten status checks on an up-to-date head and linear history, enforced for administrators. It does not require a pull-request review. Of the 28 pull requests merged since `bba8f04`, 11 changed `tacenta-spec/`, `tacenta-model/` or the trusted base. Five of them (#173, #174, #176, #182, #185) carry an approving review from the second maintainer account, and four of those five do not say what was checked. Four (#194, #200, #202, #205) merged on a rule 7 review comment written by the account that authored every commit, and each says that no reviewer independent of the maintainer has read the change; #205 changed seven specification pages, the model, `CLAIMS.md`, `LIMITATIONS.md` and the generated-axiom allowlist. #204 merged on a comment headed "Independent review" written by the account that authored it, which is not an independent review. #190 carries no standing review. #191, #193, #195, #201, #206, #208 and #209 merged with no review or comment. Eight further pull requests that changed none of those files (#177, #179, #180, #181, #183, #184, #186, #187) carry an approval from the second account. The repository does not record who operates the second account. #168, #188 and #189 were opened from the second maintainer account, contain only the first account's commits and were approved by the first account, so they are not independent reviews, and squash merging recorded the second account as their author. The historic record still needs disposition. `tooling/check-signoff.sh` runs as the `sign-off` job on every pull request and, since #184, as a step of the `checks` job on every push to `main`, against the commits that push adds. The push step runs after the merge, so it reports and does not prevent: it failed on 9 push runs since `bba8f04`, because squash commits carried no sign-off from their author. A DCO sign-off is not a review. | Publish the historic disposition and require a named reviewer who did not author the change before claiming independent review. |
| 8 | Traceability | Good | `CLAIMS.md` maps theorems to claims, the conformance manifest maps sections to vectors, and `mapping-to-spec.md` maps the model to the specification. `security-properties/evidence-index.json` records every current requirement's implementation, proof, claim, vector/test and explicit missing-evidence links. Its version-2 `INV-*` extension records the scoped invariant catalogue. CI checks the structural spine, live evidence links, invariant IDs and requirement links, and focused refusal cases. Semantic sufficiency of those links remains a review obligation. Hosted-inventory acceptance (`tacenta-spec/protocol/identities-and-devices.md`, Accepting a signed statement) has no numbered requirement or evidence-index entry, and the identity-key admission rule is cited from `authentication.md` but has no requirement of its own; `GAP-REGISTER.md` INV-01 records the first. | Keep the requirement and invariant entries current as their evidence changes. |
| 9 | Differential testing | Partial | Model-generated vectors are checked against the Rust, and a reader that imports nothing from the implementation checks 759 of the 760 vectors and 264 derived cases, deriving the session vectors from their inputs up to the ML-KEM and Braid-key-generation boundaries its README lists; the honest initial message in `identity/initial-message-admission.json` is checked in part, because its plaintext needs decapsulation. The reader is project-controlled evidence, not an independent review. Generated operation sequences run through both sides for the two ratchets and the Triple Ratchet (`tacenta-model/Difftest.lean` and `tacenta-test-vectors/runners/rust/tests/differential.rs`), comparing the outcome, the persisted bytes and the export-and-import check at every step, the refusal kind on a corrupted import, and the counter ceilings both sides stop at. The Braid's decoder is driven on generated stored states, its `Ct2Sampled` boundaries are driven from stored bytes, and seeded real-ML-KEM schedules drive all thirteen state-machine transitions; the isolated specification-only reader checks the abstract transition table with its specified KEM double. The prekey store and session are driven over the committed P4 fixtures in their shared structural domains: accepted current and legacy stores, optional branches, record bounds, roles, epoch relations, inner-reader refusals, wrong-version, short-or-malformed and inconsistent refusals, with the cryptographic relations outside the model recorded as exact exclusions. P6's v4 isolated operation reader, as delivered (its SHA-256 is in `P6-OPERATION-READER-EVIDENCE.md`), checked all nine agreed operation families and its five controls failed as required. #202 has since renamed one citation in the reader and three in the corpus, so the committed reader no longer has the recorded hash; it still passes 36 ordinary steps and fails its five controls. [The L2 decision](tacenta-model/P6-L2-TARGET-DECISION.md) records its bounded, declared-crypto scope. This is testing, not proof: it pins the sequences or fixtures a seed reaches and says nothing about the ones it does not. | Extend the operation corpus and the isolated reader to the changes in #202 and #205, with a new isolated run where `P9-GATE-EVIDENCE.md` requires one. |
| 10 | Fuzzing and property tests | Partial | Six cargo-fuzz targets with a committed corpus of 4,107 files, proptest, the constant-time disassembly check, `cargo audit`, and compile checks on the minimum supported Rust version and on `armv7-linux-androideabi`. The public workflow does not run the fuzz targets: `tooling/ci.sh` replays the corpus when `cargo-fuzz` and a nightly toolchain are present, and the search runs outside this repository. No fuzz target or property test reads the hosted-inventory decoders, which take bytes a hosted server chooses (`GAP-REGISTER.md` INV-01). | Add a fuzz target or property test for the hosted-inventory decoders, and either run the fuzz smoke step in the public workflow or keep saying here that it is not run. |

**Rust expectations:**
- **Met:**
  - no `unsafe` in the libraries of the default feature set (practice 3), and no FFI in the core;
  - I/O separated from protocol logic, with bytes in and out and randomness injected;
  - receives run on a copy and commit after authentication (`tooling/check_authentication_boundary.py` registers 29 receive paths; E2E-07 stays open until its final evidence run is recorded);
  - bounded stores and profiles.
- **Weak:**
  - protocol keys are `[u8; 32]` aliases (the ratchet, session and sparse-ratchet crates each define `Key`); X25519 keys are newtypes in `tacenta-boundary` and in `Session`;
  - decoders refuse invalid input but return raw values, except that hosted-inventory acceptance returns an `AcceptedInventory` with a single construction site, which no operation in the crate takes yet;
  - the session's phase is implied by which fields are set.

## Components

A summary by component. A tick means the component has that kind of evidence, not that every part of it does.

| Component | Tests | Fuzz | Model | Vectors | Reader | T1 | T3 | Level now | Target |
|---|---|---|---|---|---|---|---|---|---|
| Wire decoders | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| Double Ratchet | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| Sparse post-quantum ratchet | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| Triple Ratchet | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| ML-KEM Braid | ✓ | ✓ | ✓ | partial (persisted tags 1--4 contain a delegated KEM layout with no universal vector verdict; state-machine controls run separately) | ✓ | ✓ | ✓ | L3 | L4 |
| Erasure code | ✓ | ✓ (through the Braid) | ✓ | ✓ | ✓ | ✓ | field only | L3 | L3, by [recorded target decision](tacenta-proofs/ERASURE-CODEC-TARGET-DECISION.md) |
| Protobuf profile | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| PQXDH derivation | ✓ | ✓ (through the session) | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| Session orchestration and prekey store | ✓ | ✓ | bounded lifecycle model; `Model.IdentityKey` for the identity-key rule | decoders; prekey lifecycle/replay; initiator/responder establishment structural checks; identity-key admission (bundle and initial message) | isolated operation reader | model theorems in `Proofs/SessionTrace.lean`; five conditional entry-point theorems and one lemma on the eight-leaf unit, none for import or export | — | L2 | L2, by [recorded target decision](tacenta-model/P6-L2-TARGET-DECISION.md): modelled and pinned; since the Phase 0 carve-out the lifecycle is also translated (`tacenta-core/lifecycle`), and on the eight-leaf session unit it has five conditional T1 theorems and one lemma, all six listed in `CLAIMS.md`, and conditional T3 branch lemmas, none accepted as a claim and none composed end to end, which does not raise the level. The 27-trace operation corpus and the v4 operation reader predate the identity-key rule (#205), which added the `InvalidIdentityKey` refusal to establishment and narrowed what the session and prekey-store readers accept; the P6 decision has not been reopened for it |
| Persisted formats: ratchet, sparse ratchet | ✓ | ✓ | ✓ | ✓, including the counter ceilings | ✓ | codec | — | L3 | L3 |
| Persisted formats: erasure coders | ✓ | ✓ | ✓ | ✓ | ✓ | codec | — | L3 | L3 |
| Persisted formats: triple ratchet, Braid | ✓ | ✓ | ✓ | ✓; the Braid's `key_pair` content clause is scoped to implementations with the delegated KEM layout and no vector can pin it | ✓ | — | — | L2 | L2 |
| Persisted formats: prekey store | ✓ | ✓ | ✓ five of the page's six semantic rules; not the stored-signature rule (no signatures in the model) and not `kem_pair`'s three content clauses (no FIPS 203 arithmetic), only its length | ✓ v5, accepted legacy v1-v4 upgrade fixtures with the bytes each is written back as, the `legacy_blocked` marker rules, `previous_kem`, stored-signature refusal, five modelled semantic rules and both sides of the record budget | ✓ pass 7: committed vectors and derived cases, and pass 13 for the identity-key refusals; the shared structural domain is now driven through the differential harness, with stored signatures and KEM arithmetic pinned by exact exclusions | — | — | L2 | L2 |
| Persisted formats: session | ✓ | ✓ | ✓ seven of the page's eight semantic rules; not the first, that `ratchet_private`'s public half is the classical ratchet's `dhs_pub` (the model does not compute X25519 public keys; it computes the group law only for the identity-key rule) | ✓ layout, tag 6/7 epoch boundary branches, failed-Braid exemption, Braid-half role agreement, ratchet private/public relation, unanswered-role exclusion, reachable inner invariant refusals and field-level refusal coverage from pass 7 | ✓ pass 7: committed vectors and derived cases, and pass 13 for the identity-key refusals; the shared structural domain is now driven through the differential harness, with the ratchet private/public relation pinned by exact exclusion | — | — | L2 | L2 |


**Notes on the levels.**

- The L4 rows for the ratchets, the Triple Ratchet and the ML-KEM Braid are success-side refinements that take a step of counter headroom as a premise ([PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md](tacenta-proofs/PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md); `GAP-REGISTER.md` row HL-FM-04).
- The Braid row reads L3 because its T3 theorems take `ct1_bounded` and `epoch + 1 < u64::MAX` as premises, and no theorem shows that a send keeps `ct1_bounded` (`CLAIMS.md`, the ML-KEM Braid T1 section). ADR-0008 defines levels L1 to L4 only. An earlier version of this row read "L3/L4".
- The Session row's five T1 theorems take contract records that hold 15 to 44 named contract hypotheses each, plus a headroom record. `CLAIMS.md` gives the per-theorem counts.

## Readiness for external review

Two engagements have different scopes. The first was a review of the
cryptography and code at `d2dc386`; its report was received on 2026-09-12. The
report and reviewer identity are not yet public, so its status is a project
assertion rather than independently checkable evidence. No independent audit
has issued a report. The proof-ledger engagement is not underway.

**The completed first engagement reviewed a pinned public commit.** It needed
nothing private: `tacenta-core` is public. Its findings must be published with
reviewer-kind and relationship, or the review must not be cited as external
assurance. It is not an audit or proof-ledger sign-off.

**The second engagement, the proof ledger, waits for all four gates.** Its
reviewer's work is checking whether the theorems say what `CLAIMS.md` says, and
auditing a ledger that is still moving wastes the engagement.

| # | Gate | How it is checked |
|---|---|---|
| 1 | Every component sits at its stated target level, or the target was lowered by a recorded decision | the Components table above and [ASSURANCE-OBLIGATIONS.md](ASSURANCE-OBLIGATIONS.md) |
| 2 | No gap is open at BLOCKING, and every AMBIGUOUS one is closed or converted into a recorded decision | [GAP-REGISTER.md](GAP-REGISTER.md) and [ASSURANCE-OBLIGATIONS.md](ASSURANCE-OBLIGATIONS.md) |
| 3 | The claims ledger has been verified claim by claim, by a reader who did not write it, since its last change | a recorded review naming the reading |
| 4 | Every gate has been shown to fail when what it checks is broken, and none reports green when it cannot run | each gate's mutation record |

**Where the gates stand at `dea57eaf`.**
- Gate 1 is not met. Practice 5 is BLOCKING in `ASSURANCE-OBLIGATIONS.md` (MU-03), and the ML-KEM Braid row reads L3 against an L4 target.
- Gate 2 is not met. `GAP-REGISTER.md` has three rows open at BLOCKING and one at AMBIGUOUS, and `ASSURANCE-OBLIGATIONS.md` lists MU-02 to MU-05 at BLOCKING.
- Gate 3 has not been requested ([P9-GATE-EVIDENCE.md](tacenta-proofs/P9-GATE-EVIDENCE.md)). No reader who did not write the ledger has checked it claim by claim.
- Gate 4 is not met. "Where the negative controls run" in [ASSURANCE-OBLIGATIONS.md](ASSURANCE-OBLIGATIONS.md) lists which gates have a control that runs in CI, which run only locally and which have none, and names the gates whose control a single edit survived.

**Not gates, but disclosed in the pack:** practices still Partial and why; the
limitations, current at the reviewed commit; and every claim the build does not
pin. At `dea57eaf` that is 80 of the 230 claimed theorems; `verification-manifest.json` holds the data and no file lists them yet.

**What completion does not mean.** Three things stay open by decision, not by
omission, and the pack says so rather than letting a reviewer find them:
- the security properties are proved against a symbolic attacker, not a
  computational one (`LIMITATIONS.md`, and LIM-01 in the requirements);
- the Braid's `key_pair` content clause is scoped to implementations that know
  the delegated KEM layout, and no vector can pin it;
- session orchestration is modelled, pinned and, since the Phase 0 carve-out,
  translated with conditional T1 theorems only, so ASM-19 carries it. Thirteen
  requirements rest on ASM-19 in `evidence-index.json`: eleven are "tested only",
  one is "assumed", and one (`REQ-CONF-02`) is "proved" with
  `session-orchestration-proof` listed as missing evidence. Two further proved
  requirements, `REQ-AUTH-08` and `REQ-AUTH-14`, record a missing session-layer
  proof that points at ASM-19.

Gate 3 is deliberately the last thing done before the second engagement, because
it is only true of the ledger as it stands on the day.

## Roadmap

1. **Reviewed normative changes:**
   - record ADR-0008 (done);
   - every normative pull request carries a recorded review before it merges on green (11 of the 28 pull requests since `bba8f04` were normative; practice 7 describes the records);
   - `main` protection requires the ten status checks on an up-to-date head and linear history, enforced for administrators (done), and does not yet require a non-author review; record any emergency bypass in the assurance ledger.
2. **Assumptions and requirements (done for the 32 requirements in place):** the threat model, with its assets, adversaries, assumptions and exclusions, is in `tacenta-spec/threat-model/`, and the security properties are numbered requirements in `tacenta-spec/security-properties/`. Hosted-inventory acceptance and the identity-key admission rule have no numbered requirement of their own.
3. **Traceability:** the machine-readable evidence index and its `INV-*` invariant extension now check requirement/invariant IDs and live implementation, theorem, claim, vector and test references. Semantic review of the predicates and cited evidence remains required.
4. **Differential testing (done for the two ratchets, Triple Ratchet, and Braid state-machine target; partly for prekey operations):** generated operation sequences run through `tacenta-model` and `tacenta-core`, comparing outcomes, refusals and persisted bytes, in `tooling/ci.sh` and the CI vectors job. The Braid decoder and epoch-boundary transitions are model-compared; five seeded real-ML-KEM schedules then cover every Braid state-machine transition, while the isolated specification-only reader checks the specified abstract table. The `key_pair` content clause remains scoped to implementations knowing the KEM layout ADR-0006, point 5, delegates, so it has no universal vector verdict. The prekey store and session are now driven over their shared structural stored-format domains; stored signatures, KEM arithmetic and the session ratchet-private/public relation remain pinned outside the model by vectors and crate tests.
5. **Model and formats:**
   - the model's counter ceilings: done for the classical ratchet, the sparse ratchet and the Braid, and the Braid's is now pinned by vectors and by the harness as well as stated; the refinements' step of headroom remains a caller premise, with boundary-refusal coverage tracked separately;
   - persisted formats phase 2 (the Triple Ratchet and the Braid): done. The Braid's `key_pair` content clause is scoped to implementations that know the delegated KEM layout, and the model is outside that scope, so it states the clause nowhere and conforms; no vector can pin it, because a state that fails it is refused inside the scope and accepted outside, both conforming;
   - persisted formats phase 3 (the session and the prekey store): modelled and read by the isolated specification-only reader, with the P4 fixture gaps closed in the gap register; the prekey store's and session's shared structural domains are now compared by the differential harness, with cryptographic relations outside the model pinned separately.
6. **Types and state:** validated newtypes at the decoder boundary, and an explicit session state machine, done step by step.
