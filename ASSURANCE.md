# Assurance

This records where `tacenta-core` stands against the expectations in
[ADR-0008](tacenta-spec/decisions/ADR-0008-assurance-expectations.md), and what
comes next. It is a summary. For what is proven, `tacenta-proofs/CLAIMS.md` and
`LIMITATIONS.md` are the record. For what the vectors pin,
`tacenta-test-vectors/conformance-manifest.md` is.

Last assessed: 2026-09-12.

## Practices

| # | Practice | Status | Where it stands | Next |
|---|---|---|---|---|
| 1 | Specification before implementation | Partial | ADR-0006 makes the specification normative, and changes land specification-first. Much of the text was written after the code, as built. The formal statement of rules is in the model, not the prose. | New rules are written as invariants, preconditions, transitions and failures before code. |
| 2 | Explicit assumptions | Done | `tacenta-spec/threat-model/` states the assets, adversaries, assumptions and exclusions. `tacenta-spec/security-properties/` states the security properties as numbered requirements, each naming the assumptions it rests on, and records the gaps in `limitations.md`. `CLAIMS.md` opens with what is not proved, `LIMITATIONS.md` lists what the proofs trust, and the axiom audit pins the theorems. | Keep them current as requirements, proofs and code change. |
| 3 | Small trusted base | Good | No `unsafe`, and `forbid(unsafe_code)` in every crate. No FFI in the core. Trusted: libcrux, the dalek curves, the Aeneas translation, and proofs checked by evaluation. | Keep it; review any addition. |
| 4 | Model separate from implementation | Good | The Lean model, its translation, and T3 refinement for the ratchets, Braid, decoders and PQXDH derivation. Vectors pin the rest. Four of the six persisted formats are modelled: the two ratchets', the Triple Ratchet's and the Braid's. Session orchestration is outside the verified zones. | Persisted-format models, phase 3: the session and the prekey store. |
| 5 | Invariants, not examples | Partial | T1 panic-freedom, T3 refinement, decoded-state invariants, and forward secrecy and post-compromise security against a symbolic attacker. The classical and sparse ratchets' models stop at the counter ceilings the pages state, and persistence vectors pin those ceilings against `tacenta-core`. `Model.Braid` stops at its epoch ceiling too, and now that the model states a stored Braid format that ceiling is pinned from both sides: the reader's refusal of the reserved epoch, and the two `Ct2Sampled` transitions that meet it, in vectors and in the differential harness. Their refinements still ask for a step of headroom below the ceilings. The invariants are not catalogued as requirements. | Catalogue the invariants with the requirements. |
| 6 | Verification in CI | Strong | Lean builds, the `sorry` scan, kernel replay, translation attestation, vectors current with the model, the independent reader. | Keep it. |
| 7 | Reviewed normative changes | Gap, being addressed | One maintainer. Branch protection on `main` is off by decision while the project has one maintainer. Specification and model changes were merged on green checks with no recorded review. | ADR-0008 rule 7: every normative change carries a recorded review before merging on green. |
| 8 | Traceability | Partial | `CLAIMS.md` maps theorems to claims, the conformance manifest maps sections to vectors, and `mapping-to-spec.md` maps the model to the specification. `security-properties/` numbers the security requirements and names each one's theorems and tests; no CI check holds that tracing. | Requirement IDs traced through `CLAIMS.md`, the conformance manifest and the tests, with a CI check. |
| 9 | Differential testing | Partial | Model-generated vectors are checked against the Rust, and an independent reader written from the specification alone checks every vector. Generated operation sequences run through both sides for the two ratchets and the Triple Ratchet (`tacenta-model/Difftest.lean` and `tacenta-test-vectors/runners/rust/tests/differential.rs`), comparing the outcome, the persisted bytes and the export-and-import check at every step, the refusal kind on a corrupted import, and the counter ceilings both sides stop at. The Braid's decoder is driven on generated stored states, and its two `Ct2Sampled` transitions, which meet the epoch ceiling, are driven from stored bytes. Each of these comparisons has been shown able to fail, by mutating the model one thing at a time. This is testing, not proof: it pins the sequences a seed generates and says nothing about the ones it does not. Not driven: the session and the prekey store, whose stored formats the model does not state, and the rest of the Braid's state machine, which needs the KEM layout ADR-0006 delegates. | Phase 3, the session and the prekey store. |
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
| Sparse post-quantum ratchet | ✓ | ✓ | ✓ | partial | ✓ | ✓ | ✓ | L3/L4 | L4 |
| Triple Ratchet | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| ML-KEM Braid | ✓ | ✓ | ✓ | partial (no MAC or state-machine vectors) | ✓ | ✓ | ✓ | L3/L4 | L4 |
| Erasure code | ✓ | ✓ (through the Braid) | ✓ | ✓ | ✓ | ✓ | field only | L3 | L4 |
| Protobuf profile | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| PQXDH derivation | ✓ | ✓ (through the session) | ✓ | ✓ | ✓ | ✓ | ✓ | L4 | L4 |
| Session orchestration and prekey store | ✓ | ✓ | — | decoders only | partial | — | — | L1 | L2 |
| Persisted formats: ratchet, sparse ratchet | ✓ | ✓ | ✓ | ✓, including the counter ceilings | ✓ | codec | — | L3 | L3 |
| Persisted formats: erasure coders | ✓ | ✓ | ✓ | ✓ | ✓ | codec | — | L3 | L3 |
| Persisted formats: triple ratchet, Braid | ✓ | ✓ | ✓ | ✓; the Braid's `key_pair` content clause is scoped to implementations with the delegated KEM layout and no vector can pin it | not yet read | — | — | L1 | L2 |
| Persisted formats: session, prekey store | ✓ | ✓ | — | — | — | — | — | L1 | L2 |

## Roadmap

1. **Reviewed normative changes:**
   - record ADR-0008;
   - every normative pull request carries a recorded review before it merges on green;
   - branch protection on `main` stays off while the project has one maintainer, and is revisited when a second joins.
2. **Assumptions and requirements (done):** the threat model, with its assets, adversaries, assumptions and exclusions, is in `tacenta-spec/threat-model/`, and the security properties are numbered requirements in `tacenta-spec/security-properties/`.
3. **Traceability:** requirement IDs in `CLAIMS.md`, the conformance manifest and the tests, with a CI check that every requirement has a property and a test.
4. **Differential testing (done for the two ratchets and the Triple Ratchet, partly for the Braid):** generated operation sequences run through `tacenta-model` and `tacenta-core`, comparing outcomes, refusals and persisted bytes, in `tooling/ci.sh` and the CI vectors job. The Braid is covered for its decoder and the two transitions that meet its epoch ceiling; the rest of its state machine, and the `key_pair` content clause that the page scopes to implementations knowing the KEM layout ADR-0006, point 5, delegates, are covered by `tacenta-braid`'s own tests instead. The session and the prekey store are not covered, because the model states no stored format for them.
5. **Model and formats:**
   - the model's counter ceilings: done for the classical ratchet, the sparse ratchet and the Braid, and the Braid's is now pinned by vectors and by the harness as well as stated; whether the refinements' step of headroom can be dropped has not been checked;
   - persisted formats phase 2 (the Triple Ratchet and the Braid): done. The Braid's `key_pair` content clause is scoped to implementations that know the delegated KEM layout, and the model is outside that scope, so it states the clause nowhere and conforms; no vector can pin it, because a state that fails it is refused inside the scope and accepted outside, both conforming;
   - persisted formats phase 3 (the session and the prekey store).
6. **Types and state:** validated newtypes at the decoder boundary, and an explicit session state machine, done step by step.
