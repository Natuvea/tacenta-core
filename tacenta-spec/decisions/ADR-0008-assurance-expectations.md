# ADR-0008: assurance expectations and the definition of done

## Status

Accepted.

## Context

ADR-0006 made the specification normative. It did not record how the project
reaches and shows assurance:
- what counts as finished;
- what the protocol and its proofs assume;
- how much proof a component needs;
- who reviews a change to what is normative.

In September 2026 the project was assessed against common practice for
verified protocol work. `ASSURANCE.md` keeps the result current.
- **Strong:** verification runs in CI, and the trusted base is small and
  recorded.
- **Weak:**
  - review of normative changes;
  - stated assumptions: the threat-model pages are scaffolds;
  - requirements, and tracing them to proofs and tests;
  - differential testing on generated inputs.

Two facts shape what is realistic here:
- **One maintainer.** Changes are prepared with automated assistance under
  that maintainer's account. Repository settings cannot require a second,
  independent approval.
- **Proof effort is uneven by design.** The leaf crates, where the protocol's
  cryptography and parsing live, carry T1 and T3 proofs. Orchestration,
  storage, transport and the product do not.

## Decision

1. **Specification before implementation.** A change to anything the
   specification defines states its rules first (ADR-0006).
   - In the prose, as invariants, preconditions, state transitions and failure
     behaviour.
   - Formally in `tacenta-model`, where the model covers the area.
   - Behaviour the code has and the specification does not state is a
     finding, not a precedent.

2. **Assumptions are explicit.** `threat-model/assumptions.md` states what the
   protocol and the proofs assume:
   - randomness;
   - the cryptographic primitives;
   - the clock (expiry counts events, not time);
   - storage (integrity against a writer of the store is out of scope,
     ADR-0007);
   - the network adversary;
   - the trusted toolchain.

   Every claim in `tacenta-proofs/CLAIMS.md` names what it rests on, and
   `LIMITATIONS.md` names what is trusted without proof.

3. **The trusted base stays small and recorded.**
   - `tacenta-core` has no `unsafe` (`forbid(unsafe_code)` in every crate) and
     no foreign-function interface.
   - The cryptographic libraries, the translation toolchain and proofs checked
     by evaluation are listed in `LIMITATIONS.md`.
   - Anything added to the trusted base is a normative change under rule 7.

4. **Specification, then model, then implementation, then refinement.**
   - `tacenta-model` is the executable reference.
   - Translated crates refine it (T3) where that is proved.
   - Model-generated vectors pin what is not proved.
   - The independent reader tests that the specification is sufficient
     (ADR-0006).

5. **Invariants over examples.** Required properties are stated as invariants,
   and proved where the component's assurance level asks for proof. Vectors
   and tests are examples of them, not substitutes. The invariants include:
   - reachable states keep their rules;
   - authentication comes before any state is committed;
   - keys are not reused;
   - counters are bounded and monotone;
   - malformed input cannot break a state's assumptions.

6. **Verification is part of the build.** `tooling/ci.sh` and the CI workflow
   fail on any of these, and a pull request is not merged while they fail:
   - a broken proof or a `sorry`;
   - an attestation mismatch;
   - vectors out of date with the model;
   - a failing independent reader.

7. **Normative changes are reviewed before they merge.**
   - **Scope:** changes to `tacenta-spec`, `tacenta-model`, or the proofs'
     trusted base (axioms, the trusted-base lists, `CLAIMS.md`,
     `LIMITATIONS.md`).
   - **Review:** such a change is reviewed against this record before it is
     merged. The maintainer reviews it, or delegates the review.
   - **The record:** the review is written on the pull request and says what
     was checked.
   - **Merging:** only on green checks.
   - **The independent reader:** its passes are an adversarial second reading
     of sufficiency, not a substitute for this review.
   - **When a second reviewer joins:** required code-owner review replaces this
     rule.

8. **Traceability.** Security properties are numbered requirements. Each is
   traced to:
   - the model property or theorem that states it;
   - its proof in `CLAIMS.md`, when proved;
   - the implementation;
   - the vectors or tests that exercise it.

   A requirement with no property or no test is a recorded gap.

9. **Differential testing.** Beyond the fixed vectors, generated inputs and
   operation sequences run through both `tacenta-model` and `tacenta-core`.
   Their outputs, refusals and persisted bytes are compared.

10. **Testing stays.** Fuzzing, property tests, the constant-time check, the
    dependency audit and interoperability tests continue alongside the proofs.

**For the Rust:**
- **Deterministic core:** no I/O in the core logic, with randomness injected.
- **Pure transitions:** derivations and state transitions are pure functions,
  and state is committed only after authentication.
- **Explicit state machines** wherever state has phases.
- **Bounded structures** on critical paths.
- **Validated types:** parsers return validated values, and newtypes for keys
  and identifiers come in step by step, where the translation allows.

**Scope of proof:**
- **Proved:** the leaf crates, where the protocol's security lives.
- **Tested, not proved:** orchestration, storage, transport and the product.
- **Changing it:** extending proof to a component is a decision taken for that
  component.

**Definition of done.** A change is done when all four hold:
- its required properties are stated, citing the specification and requirement;
- it is reviewed, under rule 7 if it is normative;
- it is implemented;
- its component's assurance level has passed in CI.

**Assurance levels.** `ASSURANCE.md` records each component's level and target.

| Level | Name | What it requires |
|---|---|---|
| L1 | Tested | Stated in the specification. Unit and property tests. Fuzzing where input is untrusted. |
| L2 | Pinned | L1, plus the model states it and model-generated vectors pin it. The vectors are checked against the implementation and read by the independent reader. |
| L3 | Panic-free | L2, plus T1 proofs for the translated code. |
| L4 | Refined | L3, plus T3 refinement to the model, with the stated invariants proved. |

A component's level is lowered only by a recorded decision.

## Consequences

- **Recorded reviews:** every normative pull request carries a written review
  before it merges.
- **Writing comes first:** the threat model, the assumptions and the security
  properties must be written before claims can be traced to them.
- **`ASSURANCE.md` is kept current:** the status of each practice, component
  levels and targets, and open gaps.
- **This would be reopened** if:
  - a second reviewer joins (rule 7);
  - the scope of proof changes;
  - the levels turn out to be the wrong granularity.
