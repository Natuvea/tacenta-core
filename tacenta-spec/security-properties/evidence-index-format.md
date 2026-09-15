# Requirement evidence index format

`evidence-index.json` is the machine-readable index used by the P2
traceability gate. It is evidence metadata, not the evidence itself: the
checker validates that referenced files, theorem names, test names, vector
case IDs and gap or assumption references exist. It does not decide whether a
theorem statement or test assertion semantically proves a requirement. That
review remains a human obligation.

The current on-disk format is JSON with `schema_version: 2`, a `requirements`
array and an `invariants` array. Each requirement entry must include:

- `id`: the `REQ-*` identifier from the security-property pages.
- `source`: the source page plus `#REQ-*` anchor.
- `property`: the scoped property this evidence entry is about.
- `status`: the current status class, matching the requirement page and
  limitations table.
- `assumptions`: direct `ASM-*` dependencies.
- `limitations`: direct `LIM-*` references for known evidence limits, or an
  empty array.
- `implementation`: implementation locations as `{ "path", "symbol" }`.
- `model_properties`: Lean model/proof locations as
  `{ "path", "theorem", "coverage" }`.
- `claims`: claims-ledger locations as `{ "path", "section", "references" }`.
- `vectors`: vector locations as `{ "path", "case_ids", "coverage" }`.
- `tests`: test locations as `{ "path", "name", "coverage" }`.
- `missing_evidence`: absent evidence as
  `{ "kind", "reason", "references" }`, where each reference is a live
  assumption, limitation or gap identifier.

The evidence-bearing arrays may be empty when that kind of evidence does not
apply. Empty evidence must still be explained through `missing_evidence` for
non-proved requirements. Proved requirements may also use `missing_evidence`
to document a kind of evidence that is deliberately absent, as in the pilot
entry where tests only pin a proof premise.

Attaching evidence never upgrades a requirement's status. The status remains
the status stated by the requirement page and limitations table.

Each invariant entry uses an `INV-*` identifier and must include:

- `rule_source`: a normative protocol page and anchor containing the rule.
- `scope`: component and state scope.
- `establishing_operations`, `preserving_operations` and
  `refusal_terminal_effects`: operation names or descriptions that establish,
  preserve, refuse or terminally affect the invariant.
- `requirements` and `assumptions`: live `REQ-*` and direct `ASM-*` links.
- `headroom`: the relevant numeric bound or an explicit `not applicable`
  disposition; a state bound does not imply a successor operation succeeds at
  that bound.
- `implementation`, `model_properties`, `proofs` and `tests`: live symbols or
  test functions carrying the selected evidence.
- `missing_evidence`: an explicit limitation or gap where a type of evidence
  is absent. A declared gap is evidence of a limit, not proof that the
  invariant is closed.

The checker validates identifiers and live references only. It cannot decide
that a cited theorem semantically proves a predicate; that remains a recorded
review obligation.
