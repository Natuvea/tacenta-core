# Requirement evidence index format

`evidence-index.json` is the machine-readable index used by the P2
traceability gate. It is evidence metadata, not the evidence itself: the
checker validates that referenced files, theorem names, test names, vector
case IDs and gap or assumption references exist. It does not decide whether a
theorem statement or test assertion semantically proves a requirement. That
review remains a human obligation.

The current on-disk format is JSON with `schema_version: 1` and a
`requirements` array. Each requirement entry must include:

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
