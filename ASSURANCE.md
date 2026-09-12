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
| 4 | Model separate from implementation | Good | The Lean model, its translation, and T3 refinement for the ratchets, Braid, decoders and PQXDH derivation. Vectors pin the rest. All six persisted formats are modelled and pinned by vectors; the prekey store's and the session's carry one cryptographic rule each that the model cannot state, and the rows below say which. Session orchestration is outside the verified zones. | Close the remaining persisted-format coverage gaps in the gap register before raising the prekey store or session rows to L2. |
| 5 | Invariants, not examples | Partial | T1 panic-freedom, T3 refinement, decoded-state invariants, and forward secrecy and post-compromise security against a symbolic attacker. The classical and sparse ratchets' models stop at the counter ceilings the pages state, and persistence vectors pin those ceilings against `tacenta-core`. `Model.Braid` stops at its epoch ceiling too, and now that the model states a stored Braid format that ceiling is pinned from both sides: the reader's refusal of the reserved epoch, and the two `Ct2Sampled` transitions that meet it, in vectors and in the differential harness. Their refinements still ask for a step of headroom below the ceilings; the recorded next step is boundary-refusal coverage, not dropping those premises. The invariants are not catalogued as requirements. | Catalogue the invariants with the requirements. |
| 6 | Verification in CI | Strong | Lean builds, the `sorry` scan, kernel replay, translation attestation, vectors current with the model, the independent reader. | Keep it. |
| 7 | Reviewed normative changes | Done | ADR-0008 rule 7 is in force: every normative change carries a recorded review on its pull request, naming what was checked, before it merges on green pinned to the reviewed head. One maintainer, so the review is delegated and recorded rather than required by branch protection, which stays off by decision. `tooling/check-signoff.sh` and the `sign-off` CI job enforce the DCO on every added commit. | Keep it. Required code-owner review replaces the recorded review when a second maintainer joins. |
| 8 | Traceability | Partial | `CLAIMS.md` maps theorems to claims, the conformance manifest maps sections to vectors, and `mapping-to-spec.md` maps the model to the specification. `security-properties/` numbers the security requirements and names each one's theorems and tests. CI now checks the structural spine: requirement rows, status-table rows, direct assumption dependencies, and live `REQ/ASM/LIM/ADV/AS/EX` references. It does not yet enforce the claim/vector/test evidence links. | Requirement IDs traced through `CLAIMS.md`, the conformance manifest and the tests, with the evidence links enforced by CI. |
| 9 | Differential testing | Partial | Model-generated vectors are checked against the Rust, and an independent reader written from the specification alone checks every vector. Generated operation sequences run through both sides for the two ratchets and the Triple Ratchet (`tacenta-model/Difftest.lean` and `tacenta-test-vectors/runners/rust/tests/differential.rs`), comparing the outcome, the persisted bytes and the export-and-import check at every step, the refusal kind on a corrupted import, and the counter ceilings both sides stop at. The Braid's decoder is driven on generated stored states, and its two `Ct2Sampled` transitions, which meet the epoch ceiling, are driven from stored bytes. Each of these comparisons has been shown able to fail, by mutating the model one thing at a time. This is testing, not proof: it pins the sequences a seed generates and says nothing about the ones it does not. Not driven: the session and the prekey store, whose stored formats the model now states but the harness does not yet exercise, and the rest of the Braid's state machine, which needs the KEM layout ADR-0006 delegates. | Phase 3, the session and the prekey store. |
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
| Session orchestration and prekey store | ✓ | ✓ | — | decoders only | partial | — | — | L1 | L2, by recorded decision: modelled and pinned, not translated (2026-09-12) |
| Persisted formats: ratchet, sparse ratchet | ✓ | ✓ | ✓ | ✓, including the counter ceilings | ✓ | codec | — | L3 | L3 |
| Persisted formats: erasure coders | ✓ | ✓ | ✓ | ✓ | ✓ | codec | — | L3 | L3 |
| Persisted formats: triple ratchet, Braid | ✓ | ✓ | ✓ | ✓; the Braid's `key_pair` content clause is scoped to implementations with the delegated KEM layout and no vector can pin it | ✓ | — | — | L2 | L2 |
| Persisted formats: prekey store | ✓ | ✓ | ✓ five of the page's six semantic rules; not the stored-signature rule (no signatures in the model) and not `kem_pair`'s three content clauses (no FIPS 203 arithmetic), only its length | ✓ the v4 layout and five of the six rules, both sides of the record's budget included; **no vector pins the signature rule, the older versions, or `previous_kem`** — `lifecycle.rs`'s mutation tests hold the first, its version tests the second | ✓ pass 7: committed vectors and derived cases; remaining coverage gaps in [GAPS-7](tacenta-test-vectors/runners/independent/GAPS-7.md) | — | — | L1 | L2 |
| Persisted formats: session | ✓ | ✓ | ✓ seven of the page's eight semantic rules; not the first, that `ratchet_private`'s public half is the classical ratchet's `dhs_pub` (the model does not compute the curve) | ✓ the layout and **five** of the eight rules; no vector reaches the first, "an unanswered initiator is not also a responder", or "each half satisfies its own crate's invariant", nor three of the four field-by-field refusals | ✓ pass 7: committed vectors and derived cases; remaining coverage gaps in [GAPS-7](tacenta-test-vectors/runners/independent/GAPS-7.md) | — | — | L1 | L2 |


## Readiness for external review

Two engagements, and this section says what each waits for. An external review is
scheduled at the project's current state and a second at completion, so the bar
below decides the second, not the first.

**The first engagement, the cryptography and the code, does not wait.** It needs
nothing private: `tacenta-core` is public, so it reviews a pinned public commit.
Its findings are worth most while there is still time to act on them cheaply.

**The second engagement, the proof ledger, waits for all four gates.** Its
reviewer's work is checking whether the theorems say what `CLAIMS.md` says, and
auditing a ledger that is still moving wastes the engagement.

| # | Gate | How it is checked |
|---|---|---|
| 1 | Every component sits at its stated target level, or the target was lowered by a recorded decision | the Components table above |
| 2 | No gap is open at BLOCKING, and every AMBIGUOUS one is closed or converted into a recorded decision | [GAP-REGISTER.md](GAP-REGISTER.md) |
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
   - branch protection on `main` stays off while the project has one maintainer, and is revisited when a second joins.
2. **Assumptions and requirements (done):** the threat model, with its assets, adversaries, assumptions and exclusions, is in `tacenta-spec/threat-model/`, and the security properties are numbered requirements in `tacenta-spec/security-properties/`.
3. **Traceability:** the structural requirement spine is now checked in CI. Next is the machine-readable evidence index: requirement IDs in `CLAIMS.md`, the conformance manifest and the tests, with a CI check that every requirement has the expected evidence or a stated reason.
4. **Differential testing (done for the two ratchets and the Triple Ratchet, partly for the Braid):** generated operation sequences run through `tacenta-model` and `tacenta-core`, comparing outcomes, refusals and persisted bytes, in `tooling/ci.sh` and the CI vectors job. The Braid is covered for its decoder and the two transitions that meet its epoch ceiling; the rest of its state machine, and the `key_pair` content clause that the page scopes to implementations knowing the KEM layout ADR-0006, point 5, delegates, are covered by `tacenta-braid`'s own tests instead. The session and the prekey store are not driven by the differential harness, though the model now states both stored formats.
5. **Model and formats:**
   - the model's counter ceilings: done for the classical ratchet, the sparse ratchet and the Braid, and the Braid's is now pinned by vectors and by the harness as well as stated; the refinements' step of headroom remains a caller premise, with boundary-refusal coverage tracked separately;
   - persisted formats phase 2 (the Triple Ratchet and the Braid): done. The Braid's `key_pair` content clause is scoped to implementations that know the delegated KEM layout, and the model is outside that scope, so it states the clause nowhere and conforms; no vector can pin it, because a state that fails it is refused inside the scope and accepted outside, both conforming;
   - persisted formats phase 3 (the session and the prekey store): modelled and read by the independent reader, with remaining coverage gaps tracked in the gap register.
6. **Types and state:** validated newtypes at the decoder boundary, and an explicit session state machine, done step by step.
