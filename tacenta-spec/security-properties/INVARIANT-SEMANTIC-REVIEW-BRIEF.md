# Invariant catalogue semantic-review brief

## Assignment

Independently review the eight `INV-*` records in
`evidence-index.json`. This is a semantic assessment of the predicates,
premises and cited evidence, not a rerun of `tooling/check-traceability.py`.
The reviewer must not be the author of the catalogue or of the disposition
being reviewed.

Use the exact source commit and tree identified in the return record. If either
changes while reviewing, stop and record the changed inputs; the maintainer
must decide whether a new review is needed.

## Inputs

Read these documents in full:

- `tacenta-spec/security-properties/evidence-index.json` and
  `evidence-index-format.md`;
- every normative page and anchor named by an `INV-*` record;
- `tacenta-model/SESSION-OPERATION-MODEL.md`;
- `tacenta-proofs/CLAIMS.md`, `tacenta-proofs/LIMITATIONS.md`, and
  `tacenta-proofs/PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md`; and
- the model, proof, test and vector/reader paths cited by each record.

The structural baseline is `python3 tooling/check-traceability.py`. A passing
result shows that references are live; it does not answer the questions below.

## Review questions

For each `INV-*` record, determine whether:

1. the stated predicate is a faithful, bounded reading of its normative source;
2. establishing, preserving, refusal and terminal operations match the source;
3. requirement and assumption links are direct and sufficient;
4. headroom distinguishes a valid-state bound from an operation-success
   premise, and agrees with the headroom decision where relevant;
5. cited model, proof, test, vector and reader evidence supports precisely the
   described scope; and
6. missing evidence, declared cryptographic facts and untranslated/bounded
   exclusions are disclosed rather than silently covered.

Pay particular attention to `INV-COUNTER-EPOCH-BOUNDS`: it must not convert a
reserved-ceiling refusal into a success-refinement claim. Also assess
`INV-TERMINAL-FAILURE` against the distinction between the accepted message
that commits a Braid failure and later refused operations.

## Return record

Create `INVARIANT-SEMANTIC-REVIEW-RECORD.md` with:

- reviewer identity, independence statement, date/time and source commit/tree;
- every input read, including a SHA-256 for `evidence-index.json` and the
  headroom decision;
- one disposition for each `INV-*`: `accepted`, `accepted-with-limit`, or
  `finding`, with the supporting source and evidence paths;
- each finding's severity, required correction and whether it blocks Practice
  5 or a component target;
- the command and unabridged output for the structural baseline; and
- an explicit conclusion on whether Practice 5 can move from BLOCKING.

Do not edit the catalogue to resolve a finding. Return findings to the
maintainer, who updates sources and requests a fresh review when the reviewed
meaning changes.
