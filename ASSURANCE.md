# Assurance

This records where `tacenta-core` stands against the expectations in
[ADR-0008](tacenta-spec/decisions/ADR-0008-assurance-expectations.md), and what
comes next. It is a summary. For what is proven, `tacenta-proofs/CLAIMS.md` and
`LIMITATIONS.md` are the record. For what the vectors pin,
`tacenta-test-vectors/conformance-manifest.md` is. For current gate and target
obligations, see [ASSURANCE-OBLIGATIONS.md](ASSURANCE-OBLIGATIONS.md).

Last assessed: 2026-09-18, at `dd6710e`.

## Practices

| # | Practice | Status | Where it stands | Next |
|---|---|---|---|---|
| 1 | Specification before implementation | Partial | ADR-0006 makes the specification normative, and changes land specification-first. Much of the text was written after the code, as built. The formal statement of rules is in the model, not the prose. | New rules are written as invariants, preconditions, transitions and failures before code. |
| 2 | Explicit assumptions | Done | `tacenta-spec/threat-model/` states the assets, adversaries, assumptions and exclusions. `tacenta-spec/security-properties/` states the security properties as numbered requirements, each naming the assumptions it rests on, and records the gaps in `limitations.md`. `CLAIMS.md` opens with what is not proved, `LIMITATIONS.md` lists what the proofs trust, and the axiom audit pins the theorems. | Keep them current as requirements, proofs and code change. |
| 3 | Small trusted base | Good | No `unsafe`, and `forbid(unsafe_code)` in every crate. No FFI in the core. Trusted: libcrux, the dalek curves, the Aeneas translation, and proofs checked by evaluation. | Keep it; review any addition. |
| 4 | Model separate from implementation | Good | The Lean model, its translation, and T3 refinement for the ratchets, Braid, decoders and PQXDH derivation. Vectors pin the rest. All six persisted formats are modelled and pinned by vectors; the prekey store's and the session's carry one cryptographic rule each that the model cannot state, and the rows below say which. P6 now covers its selected durable session/prekey operation surface at L2; [its target decision](tacenta-model/P6-L2-TARGET-DECISION.md) keeps the bounded and declared-crypto exclusions explicit. | Reopen P6 on a recorded decision trigger. |
| 5 | Invariants, not examples | Partial | T1 panic-freedom, T3 refinement, decoded-state invariants, and forward secrecy and post-compromise security against a symbolic attacker. The classical and sparse ratchets' models stop at the counter ceilings the pages state, and persistence vectors pin those ceilings against `tacenta-core`. `Model.Braid` stops at its epoch ceiling too, and its reserved epoch and `Ct2Sampled` boundary transitions are pinned in vectors and the differential harness. `evidence-index.json` now has checked `INV-*` records for the session/prekey invariants, including explicit operation effects and headroom dispositions. [The recorded scope decision](tacenta-proofs/PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md) keeps the successor-headroom limit on success refinement explicit; it does not claim boundary success refinement. | Obtain the required semantic review of the invariant predicates and their cited coverage. |
| 6 | Verification in CI | Partial | Lean builds, the `sorryAx` audit and scan, kernel replay, translation checksum checks, vectors current with the model, and an isolated specification-only reader. The reader and its pass records are project-controlled evidence, not independent review; the translation checksum does not prove regeneration. | Obtain an independent claim review. |
| 7 | Reviewed normative changes | Partial | ADR-0008 requires a recorded review for each normative change. Historic pull-request records show that this was not consistently done, including [PR #129](https://github.com/Natuvea/tacenta-core/pull/129). The project has not yet produced a complete historic count and retrospective disposition. `main` now requires green head checks and a review, with administrator enforcement; the historic record still needs disposition. `tooling/check-signoff.sh` and the `sign-off` job check DCO trailers on pull-request commits; a DCO sign-off is not a review. | Publish the historic disposition and require a named reviewer who did not author the change before claiming independent review. |
| 8 | Traceability | Good | `CLAIMS.md` maps theorems to claims, the conformance manifest maps sections to vectors, and `mapping-to-spec.md` maps the model to the specification. `security-properties/evidence-index.json` records every current requirement's implementation, proof, claim, vector/test and explicit missing-evidence links. Its version-2 `INV-*` extension records the scoped invariant catalogue. CI checks the structural spine, live evidence links, invariant IDs and requirement links, and focused refusal cases. Semantic sufficiency of those links remains a review obligation. | Keep the requirement and invariant entries current as their evidence changes. |
| 9 | Differential testing | Partial | Model-generated vectors are checked against the Rust, and an isolated specification-only reader checks every vector. The reader is project-controlled evidence, not an independent review. Generated operation sequences run through both sides for the two ratchets and the Triple Ratchet (`tacenta-model/Difftest.lean` and `tacenta-test-vectors/runners/rust/tests/differential.rs`), comparing the outcome, the persisted bytes and the export-and-import check at every step, the refusal kind on a corrupted import, and the counter ceilings both sides stop at. The Braid's decoder is driven on generated stored states, its `Ct2Sampled` boundaries are driven from stored bytes, and seeded real-ML-KEM schedules drive all thirteen state-machine transitions; the isolated specification-only reader checks the abstract transition table with its specified KEM double. The prekey store and session are driven over the committed P4 fixtures in their shared structural domains: accepted current and legacy stores, optional branches, record bounds, roles, epoch relations, inner-reader refusals, wrong-version, short-or-malformed and inconsistent refusals, with the cryptographic relations outside the model recorded as exact exclusions. P6's v4 isolated operation reader now checks all nine agreed operation families and its five controls fail as required; [the L2 decision](tacenta-model/P6-L2-TARGET-DECISION.md) records its bounded, declared-crypto scope. This is testing, not proof: it pins the sequences or fixtures a seed reaches and says nothing about the ones it does not. | Keep the operation corpus and reader current when the recorded L2 surface changes. |
| 10 | Fuzzing and property tests | Good | Six cargo-fuzz targets, proptest, the constant-time disassembly check, `cargo audit`, MSRV and 32-bit builds. | Keep it. |

**Rust expectations:**
- **Met:**
  - no `unsafe`, and no FFI in the core;
  - I/O separated from protocol logic, with bytes in and out and randomness injected;
  - receives run on a copy and commit after authentication;
  - bounded stores and profiles.
- **Weak:**
  - keys are `[u8; 32]` aliases rather than newtypes;
  - decoders refuse invalid input, but return raw values rather than validated types;
  - the session's phase is implied by which fields are set.

## Components

A summary by component. A tick means the component has that kind of evidence, not that every part of it does.

| Component | Tests | Fuzz | Model | Vectors | Reader | T1 | T3 | Level now | Target |
|---|---|---|---|---|---|---|---|---|---|
| Wire decoders | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| Double Ratchet | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| Sparse post-quantum ratchet | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| Triple Ratchet | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| ML-KEM Braid | ✓ | ✓ | ✓ | partial (persisted tags 1--4 contain a delegated KEM layout with no universal vector verdict; state-machine controls run separately) | ✓ | ✓ | ✓ | L3/L4 | L4 |
| Erasure code | ✓ | ✓ (through the Braid) | ✓ | ✓ | ✓ | ✓ | field only | L3 | L3, by [recorded target decision](tacenta-proofs/ERASURE-CODEC-TARGET-DECISION.md) |
| Protobuf profile | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| PQXDH derivation | ✓ | ✓ (through the session) | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| Session orchestration and prekey store | ✓ | ✓ | bounded lifecycle model | decoders; prekey lifecycle/replay; initiator/responder establishment structural checks | isolated operation reader | narrow model theorem | — | L2 | L2, by [recorded target decision](tacenta-model/P6-L2-TARGET-DECISION.md): modelled and pinned, not translated |
| Persisted formats: ratchet, sparse ratchet | ✓ | ✓ | ✓ | ✓, including the counter ceilings | ✓ | codec | — | L3 | L3 |
| Persisted formats: erasure coders | ✓ | ✓ | ✓ | ✓ | ✓ | codec | — | L3 | L3 |
| Persisted formats: triple ratchet, Braid | ✓ | ✓ | ✓ | ✓; the Braid's `key_pair` content clause is scoped to implementations with the delegated KEM layout and no vector can pin it | ✓ | — | — | L2 | L2 |
| Persisted formats: prekey store | ✓ | ✓ | ✓ five of the page's six semantic rules; not the stored-signature rule (no signatures in the model) and not `kem_pair`'s three content clauses (no FIPS 203 arithmetic), only its length | ✓ v4, accepted legacy v1/v2/v3 upgrade fixtures, `previous_kem`, stored-signature refusal, five modelled semantic rules and both sides of the record budget | ✓ pass 7: committed vectors and derived cases; the shared structural domain is now driven through the differential harness, with stored signatures and KEM arithmetic pinned by exact exclusions | — | — | L2 | L2 |
| Persisted formats: session | ✓ | ✓ | ✓ seven of the page's eight semantic rules; not the first, that `ratchet_private`'s public half is the classical ratchet's `dhs_pub` (the model does not compute the curve) | ✓ layout, tag 6/7 epoch boundary branches, failed-Braid exemption, Braid-half role agreement, ratchet private/public relation, unanswered-role exclusion, reachable inner invariant refusals and field-level refusal coverage from pass 7 | ✓ pass 7: committed vectors and derived cases; the shared structural domain is now driven through the differential harness, with the ratchet private/public relation pinned by exact exclusion | — | — | L2 | L2 |


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

**Not gates, but disclosed in the pack:** practices still Partial and why; the
limitations, current at the reviewed commit; and every claim the build does not
pin, named individually.

**What completion does not mean.** Three things stay open by decision, not by
omission, and the pack says so rather than letting a reviewer find them:
- the security properties are proved against a symbolic attacker, not a
  computational one (`LIMITATIONS.md`, and LIM-01 in the requirements);
- the Braid's `key_pair` content clause is scoped to implementations that know
  the delegated KEM layout, and no vector can pin it;
- session orchestration is modelled and pinned rather than translated, so ASM-19
  carries it and the five requirements resting on it reach "pinned", not
  "proved".

Gate 3 is deliberately the last thing done before the second engagement, because
it is only true of the ledger as it stands on the day.

## Roadmap

1. **Reviewed normative changes:**
   - record ADR-0008;
   - every normative pull request carries a recorded review before it merges on green;
   - configure `main` protection to require green head CI and a non-author review; record any emergency bypass in the assurance ledger.
2. **Assumptions and requirements (done):** the threat model, with its assets, adversaries, assumptions and exclusions, is in `tacenta-spec/threat-model/`, and the security properties are numbered requirements in `tacenta-spec/security-properties/`.
3. **Traceability:** the machine-readable evidence index and its `INV-*` invariant extension now check requirement/invariant IDs and live implementation, theorem, claim, vector and test references. Semantic review of the predicates and cited evidence remains required.
4. **Differential testing (done for the two ratchets, Triple Ratchet, and Braid state-machine target; partly for prekey operations):** generated operation sequences run through `tacenta-model` and `tacenta-core`, comparing outcomes, refusals and persisted bytes, in `tooling/ci.sh` and the CI vectors job. The Braid decoder and epoch-boundary transitions are model-compared; five seeded real-ML-KEM schedules then cover every Braid state-machine transition, while the isolated specification-only reader checks the specified abstract table. The `key_pair` content clause remains scoped to implementations knowing the KEM layout ADR-0006, point 5, delegates, so it has no universal vector verdict. The prekey store and session are now driven over their shared structural stored-format domains; stored signatures, KEM arithmetic and the session ratchet-private/public relation remain pinned outside the model by vectors and crate tests.
5. **Model and formats:**
   - the model's counter ceilings: done for the classical ratchet, the sparse ratchet and the Braid, and the Braid's is now pinned by vectors and by the harness as well as stated; the refinements' step of headroom remains a caller premise, with boundary-refusal coverage tracked separately;
   - persisted formats phase 2 (the Triple Ratchet and the Braid): done. The Braid's `key_pair` content clause is scoped to implementations that know the delegated KEM layout, and the model is outside that scope, so it states the clause nowhere and conforms; no vector can pin it, because a state that fails it is refused inside the scope and accepted outside, both conforming;
   - persisted formats phase 3 (the session and the prekey store): modelled and read by the isolated specification-only reader, with the P4 fixture gaps closed in the gap register; the prekey store's and session's shared structural domains are now compared by the differential harness, with cryptographic relations outside the model pinned separately.
6. **Types and state:** validated newtypes at the decoder boundary, and an explicit session state machine, done step by step.
