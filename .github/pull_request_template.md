## Summary

<!-- What changes and why. -->

## Specification

The specification in `tacenta-spec` is normative and the code is one
implementation of it (ADR-0006). Tick one:

- [ ] This changes nothing the specification defines (bytes emitted or
      accepted, refusals, constants, derivations, bounds, rules over persisted
      state).
- [ ] The specification is changed first, in this pull request, with an
      entry in `tacenta-spec/CHANGELOG.md`, and the model and vectors follow.

Specification text this change implements (page and section):

## Properties and assumptions (ADR-0008)

Requirements or properties this change states or affects (page, requirement):

Assumptions it adds or relies on, and where they are recorded:

- [ ] The trusted base is unchanged, or `tacenta-proofs/LIMITATIONS.md` records the change.

## Assurance reached

For the affected component (levels in `ASSURANCE.md`):

- [ ] Tests, and fuzzing or property tests where input is untrusted (L1)
- [ ] The model states it, and model-generated vectors pin it, checked against the implementation and read by the independent reader (L2)
- [ ] T1: the translated code cannot fail (L3)
- [ ] T3: the translated code refines the model (L4)
- [ ] The component's level in `ASSURANCE.md` is unchanged, or updated here

## Review

- [ ] This changes `tacenta-spec`, `tacenta-model`, or the proofs' trusted base, and is merged by the maintainer after reading it (ADR-0008, rule 7).

## Test plan

- [ ] `bash tooling/ci.sh`
