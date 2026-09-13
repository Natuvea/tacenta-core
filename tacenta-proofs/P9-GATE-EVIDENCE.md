# P9 gate evidence pack

This is the reproducible evidence pack for the four readiness gates in
[`ASSURANCE.md`](../ASSURANCE.md).  It is an assembly record, not a declaration
that any gate has passed.  A final candidate is selected only after the open
items in the status table close; its revision and results then replace the
candidate placeholders below.

## Candidate capture and reproduction

Record the candidate before running any final checks:

```sh
git rev-parse HEAD
git status --short
bash tooling/ci.sh
python3 tacenta-proofs/scripts/attest.py --check
```

The record must retain the command output, platform/toolchain information,
start and finish times, and any local skips.  A local skip is not evidence for
a GitHub job that requires the missing tool.  Link the successful GitHub
workflow run for that exact revision, including its translation and proof jobs.
The current reproduction instructions and toolchain pins are in
[`REPRODUCING.md`](REPRODUCING.md); the source-of-truth operation inventory is
[`SESSION-OPERATION-MODEL.md`](../tacenta-model/SESSION-OPERATION-MODEL.md).

## Gate status

| Gate | Evidence to freeze at the candidate | Status before candidate selection | Closure action |
| --- | --- | --- | --- |
| 1 — component targets | `ASSURANCE.md`, `ASSURANCE-OBLIGATIONS.md`, target decisions and the component-specific proof/vector/test results | Open: the session orchestration and prekey-store row remains L1 with an L2 target. | Complete the specification-only reader operation surface, or make a reviewed target decision. |
| 2 — classified gaps | `GAP-REGISTER.md`, `ASSURANCE-OBLIGATIONS.md`, and every decision linked from an open/deferred row | Open while P6 remains BLOCKING. | Re-run the classification check after gate 1’s P6 action; no BLOCKING or unresolved AMBIGUOUS row may remain. |
| 3 — independent ledger review | Candidate `CLAIMS.md`, `LIMITATIONS.md`, requirement evidence index, proof manifests and generated translation attestation | Not yet requested. | A reader distinct from the ledger author records the reviewed revision, artifacts read, claim-by-claim findings and disposition in the final pull request. Any later ledger or supporting-evidence change reopens this review. |
| 4 — negative controls and required inputs | The mutation records below plus full local and hosted CI evidence | Open: the inventory identifies controls still to be run or added. | Execute or add each named control, retain its diagnostic at the candidate revision, and test missing prerequisites separately from malformed inputs. |

The P7 target decisions are inputs to gates 1 and 2, not substitutes for the
P6 reader or P9 review.  In particular,
[`ERASURE-CODEC-TARGET-DECISION.md`](ERASURE-CODEC-TARGET-DECISION.md) records
an L3 engagement target and deliberately does not claim codec refinement.

## Automated-gate mutation inventory

Each final record must identify the command, environment, deliberate fault,
expected failure and observed diagnostic.  The entries below distinguish
existing evidence from work that is still missing, so an unexecuted plan is not
mistaken for a control.

| Check | Protected property | Existing control/evidence | Candidate record still needed |
| --- | --- | --- | --- |
| `tooling/check-traceability.py` | Requirement, status, assumption and evidence-index references stay coherent. | `tooling/tests/run-check-traceability-cases.sh` covers a removed limitation, an unknown assumption, and the existing case corpus. | Add or record controls for every checker rule not covered by the case corpus: missing status, `rests_on`, title/status class, inverse assumption list, and unknown `LIM`/`ADV`/`AS`/`EX` reference. |
| `tooling/check-workflows.sh` | Workflows parse and retain repository security rules. | The 62 cases in `tooling/tests/check-workflows-cases` are the current negative corpus. | Capture its command, platform and successful diagnostic-free result at the candidate. |
| `tooling/check-precondition-shapes.py` | First-party Lean does not gain a listed vacuous numeric precondition shape. | The 71 case directories in `tooling/tests/check-precondition-shapes-cases` are the current negative corpus. | Capture its command, platform and successful diagnostic-free result at the candidate. |
| `tooling/check-labels.sh` | Derivation labels remain registered and prefix-safe. | No standalone mutation corpus is currently recorded. | Add one unregistered-label and one forbidden-prefix control, or record a reviewed reason why a different enforced control covers each condition. |
| `tooling/check-vectors.py` | Vector documents obey their schemas. | The validator refuses malformed input during normal checks. | Add a small schema-negative runner or record the existing executable tests that deliberately make the validator fail. |
| Independent reader | The specification-only reader can interpret the committed vector surface it declares. | Derived reader cases and historical findings cover current component pages. | A clean-room author must run and record a representative incorrect/missing vector-rule control. The author must satisfy ADR-0006’s isolation requirement. |
| Claims and attestation | Declared claims name live theorems and generated artifacts match their recorded source state. | `attest.py --check`, audit-negative and audit-reach checks run in CI. | Map each planted audit/attestation case to the pack’s claim and retain its actual diagnostic. |
| Full CI | Required gates do not silently report success when inputs or tools are absent. | Local `tooling/ci.sh` and the GitHub workflow share the principal checks; workflow scripts state CI-only missing-tool failure behaviour. | Record exact local skips and the hosted job results; plant or identify a missing-prerequisite control for every required hosted-only dependency. |

## Human-review record

Gate 3 is intentionally last because it applies to the ledger at the final
candidate.  Its record must contain all of the following:

- reviewer identity and independence from the ledger author;
- candidate commit and pull request URL;
- `CLAIMS.md`, `LIMITATIONS.md`, manifests, requirement evidence index,
  `ASSURANCE.md`, `ASSURANCE-OBLIGATIONS.md`, `GAP-REGISTER.md`, and applicable
  target decisions read;
- one finding and disposition for each claim, including its stated assumptions,
  theorem symbol/file, scope and limitation; and
- the exact local and hosted check results the reviewer relied on.

The recorded review is evidence of the review only.  It does not replace the
mutation evidence required by gate 4.

## Finalization checklist

1. Freeze a clean candidate revision and collect the local and hosted results.
2. Replace every `Open`, `Not yet requested` and `still needed` entry above
   with a dated evidence record or a reviewed decision that changes the target.
3. Run the independent ledger review on that frozen revision.
4. Confirm no covered artifact changed after the review; otherwise repeat the
   affected checks and review.
