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

The per-job JSON files and the manifest built from them are unsigned records
written by the candidate's own workflow. Their literal `status: pass` means the
job reached a checkpoint placed after its declared checks. It does not
authenticate the GitHub job conclusion, prove that the candidate left the
workflow intact, or become tamper-evident when an outer digest is added later.
`hosted-assurance.yml` supplies the separate path: after CI completes it runs
code checked out from `main`, queries GitHub's API for the selected run and
requires the exact candidate, event, job set and conclusions without checking
out the candidate. Its artifact remains to be demonstrated on `main` and bound
into the final evidence pack before this item closes.

## Gate status

| Gate | Evidence to freeze at the candidate | Status before candidate selection | Closure action |
| --- | --- | --- | --- |
| 1 — component targets | `ASSURANCE.md`, `ASSURANCE-OBLIGATIONS.md`, target decisions and the component-specific proof/vector/test results | P6 is closed at its bounded L2 target by `P6-L2-TARGET-DECISION.md`; Practice 5 and the remaining final-candidate obligations still block the gate. | Complete or record decisions for every remaining component deficit, then assess the matrix at the frozen candidate. |
| 2 — classified gaps | `GAP-REGISTER.md`, `ASSURANCE-OBLIGATIONS.md`, and every decision linked from an open/deferred row | Open: the headroom and erasure deferrals have recorded decisions, but blocking MU-03, MU-04, MU-05 and P9 work remains. | Re-run the classification assessment at the frozen candidate; no BLOCKING or unresolved AMBIGUOUS row may remain. |
| 3 — independent ledger review | Candidate `CLAIMS.md`, `LIMITATIONS.md`, requirement evidence index, proof manifests and generated translation attestation | Not yet requested. | A reader distinct from the ledger author records the reviewed revision, artifacts read, claim-by-claim findings and disposition in the final pull request. Any later ledger or supporting-evidence change reopens this review. |
| 4 — negative controls and required inputs | The mutation records below plus full local and hosted CI evidence | Open: the inventory identifies controls still to be run or added. | Execute or add each named control, retain its diagnostic at the candidate revision, and test missing prerequisites separately from malformed inputs. |

The P7 target decisions are inputs to gates 1 and 2, not substitutes for the
remaining semantic review, hosted evidence or P9 review. In particular,
[`ERASURE-CODEC-TARGET-DECISION.md`](ERASURE-CODEC-TARGET-DECISION.md) records
an L3 engagement target and deliberately does not claim codec refinement.

## Automated-gate mutation inventory

Each final record must identify the command, environment, deliberate fault,
expected failure and observed diagnostic.  The entries below distinguish
existing evidence from work that is still missing, so an unexecuted plan is not
mistaken for a control.

| Check | Protected property | Existing control/evidence | Candidate record still needed |
| --- | --- | --- | --- |
| `tooling/check-traceability.py` | Requirement, status, assumption and evidence-index references stay coherent. | `tooling/tests/run-check-traceability-cases.sh` runs a passing baseline and 22 focused refusals, including missing requirement metadata, status-table title/class drift, both assumption-inverse directions, unknown `LIM`/`ADV`/`AS`/`EX` references, and invariant-catalogue faults. | Capture its command, platform and successful diagnostic-free result at the candidate. |
| `tooling/check-workflows.sh` | Workflows and composite actions parse and retain repository security rules. | The 65 cases in `tooling/tests/check-workflows-cases` include composite-action tag-pin and download-to-shell refusals. Repository-level Actions SHA pinning supplies a second live enforcement layer. | Capture its command, platform and successful diagnostic-free result at the candidate and read back the repository setting. |
| `tooling/check-precondition-shapes.py` | First-party Lean does not gain a listed vacuous numeric precondition shape. | The 71 case directories in `tooling/tests/check-precondition-shapes-cases` are the current negative corpus. | Capture its command, platform and successful diagnostic-free result at the candidate. |
| `tooling/check-labels.sh` | Derivation labels remain registered and prefix-safe. | `tooling/tests/run-check-labels-cases.sh` runs a passing baseline, an unregistered-label refusal and a forbidden-prefix refusal through the production checker. | Capture its command, platform and successful diagnostic-free result at the candidate. |
| `tooling/check-vectors.py` | Vector documents obey their schemas. | `tooling/tests/run-check-vectors-cases.sh` runs a valid baseline, an unexpected-field schema refusal, a duplicate-ID refusal and an unsupported-schema-keyword refusal against the production checker. | Capture its command, platform and successful diagnostic-free result at the candidate. |
| Independent operation reader | The specification-only reader can interpret the committed P6 operation surface it declares. | Jie Sun's v4 record covers 27 traces/41 steps across all nine families. Its five controls reject a wrong durable effect, missing required inputs, an accepted duplicate and malformed-bundle pending state. | Retain the v4 clean-room record, reader/corpus hashes, command, platform and full output at the candidate; any changed operation corpus needs a new isolated run. |
| Claims and attestation | Declared claims name live theorems and generated artifacts match their recorded source state. | `check-audit-negatives.sh` exercises the audit's accepted compiler-trust orphan and 11 refusal cases. `check-attest-negatives.sh` refuses a missing claimed theorem, missing verification manifest, stale source attestation and edited generated translation, matching each diagnostic. | Capture their command, platform and successful diagnostic-free result at the candidate. |
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

`tooling/check-ledger-review-receipt.py` validates the receipt's structure and
binding to the evidence-pack manifest. It cannot establish reviewer
independence or semantic adequacy, which remain human-review findings.
`tooling/validate-reviewed-evidence.py` additionally verifies that the review
receipt, evidence pack and assurance manifest bind the same clean candidate.

## Claims and attestation control record

`bash tacenta-proofs/scripts/check-audit-negatives.sh` holds the first-party
axiom audit to the one permitted unmentioned compiler-trust orphan and to its
eleven distinct refusals: type-only and value references to a compiler-trust
axiom, an orphan without a parent, a free-statement orphan, a malformed unsafe
recursor, and declarations that are an axiom, opaque, `implemented_by`,
`extern`, partial or unsafe.  Each refusal is matched to its individual audit
reason, rather than merely to a nonzero exit.

`bash tacenta-proofs/scripts/check-attest-negatives.sh` makes a separate
detached worktree for each of four P9 mutations and runs the production
attestation script.  It requires these exact fault classes: a ledger theorem
not declared by Lean, a missing generated verification manifest, a stale
source-commit attestation, and a generated translation whose bytes do not
match the recorded provenance.  The runner matches the corresponding
diagnostic, so a failure elsewhere cannot satisfy a case.

## Finalization checklist

1. Freeze a clean candidate revision and collect the local and hosted results.
2. Replace every `Open`, `Not yet requested` and `still needed` entry above
   with a dated evidence record or a reviewed decision that changes the target.
3. Run the independent ledger review on that frozen revision.
4. Confirm no covered artifact changed after the review; otherwise repeat the
affected checks and review.

## Immutable archive

The private archive bucket is `tacenta-core-assurance-evidence-238576302016`
in `eu-west-2`. It has versioning, all public-access blocks, and a default
2,555-day S3 Object Lock **COMPLIANCE** retention. Publish each verified pack
under a new content-addressed candidate prefix, retain its version IDs and
Object-Lock metadata in the publication receipt, then download and run
`python3 tooling/build-evidence-pack.py --verify` on the downloaded pack.
`tooling/publish-evidence-archive.py --pack PACK --dry-run` derives and prints
that prefix; without `--dry-run` it uploads only verified pack files and sends
S3 `If-None-Match: *` so an existing object key is refused. Publication
requires an unused `--receipt` path and records every object key, version ID
and Compliance retain-until timestamp.

The initialization control uploaded
`controls/initialization/object-lock-20260915T151835Z.txt`, version
`NUDN9R0z2n0L.ngQi0NvfKjP4YMKq8hG`. S3 reported Compliance retention until
`2033-09-13T15:18:36Z` and refused a version-specific delete with Object Lock
`AccessDenied`. This verifies configuration, not a candidate publication.
