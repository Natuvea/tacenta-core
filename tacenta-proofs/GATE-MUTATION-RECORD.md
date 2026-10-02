# Gate mutation record, 2026-09-30

This file records a set of single-edit mutations of the project's CI gates and the negative-control runners
that were run against them, at `dea57eaf`. It is evidence for gate 4 of [`ASSURANCE.md`](../ASSURANCE.md)
("every gate has been shown to fail when what it checks is broken") and it is cited by
[`ASSURANCE-OBLIGATIONS.md`](../ASSURANCE-OBLIGATIONS.md), "Where the negative controls run".

It is project-controlled and tool-assisted. It is not an independent review, and it does not say gate 4 is met:
it shows which controls fired, which did not, and which gates have no retained control. A mutation counts as
caught only when a named case, or the gate itself, exits nonzero. The environment was macOS 26.5.1 on Apple
silicon (18 cores), bash 3.2.57 (the hosted runner has a newer bash), Python 3.9.6 with PyYAML 6.0.2, git 2.50.1,
Lean v4.31.0 and cargo 1.99.0-nightly.

## Runner results

Run one after another in a clone at `dea57eaf` (`PYTHONDONTWRITEBYTECODE=1`). Times are wall-clock on the machine above; the initial-dispatch control ran while the mutation harness was also running.

| Runner | Result | Time | Notes |
|---|---|---|---|
| `bash tooling/check-workflows.sh` (baseline) | pass | 0.2 s | "2 workflow file(s) and 1 composite action file(s) parse" |
| `tooling/tests/run-check-workflows-cases.sh` | pass | 30.1 s | 211 file cases, 31 changes |
| `tooling/tests/run-check-actionlint-cases.sh` | CANNOT-VERIFY | 0.0 s | exit 1, "actionlint is not installed"; `tooling/install-actionlint.sh` downloads a binary and was not run |
| `tooling/tests/run-check-constant-time-asm-cases.sh` | pass | 0.1 s | 3 controls |
| `tooling/tests/run-check-lifecycle-boundary-surface-cases.sh` | pass | 0.7 s | 9 |
| `tooling/tests/run-check-precondition-shapes-cases.sh` | pass | 4.5 s | 71 |
| `tooling/tests/run-check-labels-cases.sh` | pass | 0.3 s | 3 refusals |
| `tooling/tests/run-check-traceability-cases.sh` | pass | 7.2 s | prints 22, runs 24 |
| `tooling/tests/run-check-vectors-cases.sh` | pass | 1.0 s | 11 refusals |
| `tooling/tests/run-check-session-operation-traces-cases.sh` | pass | 0.2 s | 3 refusals |
| `tooling/tests/run-build-assurance-manifest-cases.sh` | pass | 1.7 s | 13 refusals |
| `tooling/tests/run-collect-assurance-receipts-cases.sh` | pass | 6.6 s | 44 cases |
| `tooling/tests/run-check-signoff-cases.sh` | pass | 0.4 s | 3 refusals |
| `tooling/tests/run-build-evidence-pack-cases.sh` | pass | 4.3 s | 58 cases |
| `tooling/tests/run-check-ledger-review-receipt-cases.sh` | pass | 0.2 s | 3 refusals |
| `tacenta-proofs/scripts/check-attest-negatives.sh` | pass | 171 s | 79 cases |
| `tacenta-proofs/scripts/check-audit-negatives.sh` | pass | 78 s | 13 planted cases |
| `tacenta-proofs/scripts/check-lifecycle-translation-coverage-negatives.sh` | pass | 0.1 s | python only |
| `tacenta-proofs/scripts/check-session-satisfiability-negatives.sh` | pass | 4.6 s | needs the translation modules built; the two targets these controls need were built first (183 s) |
| `tacenta-proofs/scripts/check-initial-dispatch-negatives.py` | pass | 145 s | 3 mutations refused, machine loaded |
| `.../independent/reader/run.py` | pass | 15.4 s | 1023 / 0 fail / 1 skip |
| `.../independent/reader/test_skip_allowlist.py` | pass | 0.1 s | |
| `.../independent/reader/test_session_e2e_sweep.py` | pass | 30.3 s | |
| `.../independent/session-operation-reader.py` | pass | 0.0 s | 5 controls fail as required |
| `python3 tooling/mutate-inventory.py` | pass | 141 s | 116 killed, 8 claimed equivalent, 0 unexpected |

Baseline gates run for comparison, all pass: `attest.py --check` (4.8 s; 150 pinned theorems, 11 generated files), `check_authentication_boundary.py` (29 paths), `check-lean-constructs.sh` (106 files), `check-audit-reach.sh` (116 modules), `check-lifecycle-translation-coverage.py` (30 operations), `check-constant-time-asm.sh` (21 s; three targets; it ignores `CARGO_TARGET_DIR`, and with one set it fails closed with "found 0").

## Mutation record

Method. Baseline first, in a fresh clone of the repository at `dea57eaf`: `run-build-assurance-manifest-cases.sh`, `run-collect-assurance-receipts-cases.sh`, `run-build-evidence-pack-cases.sh` (2.0 s, 8.2 s, 4.7 s), `check-workflows.sh` (0.2 s), `run-check-workflows-cases.sh` (26.2 s), `run-check-signoff-cases.sh`, `run-check-constant-time-asm-cases.sh`, the reader's `run.py`: all green, `git status` empty. Each mutation is one replacement of a string that the harness first checks occurs exactly once in one file, in its own fresh clone. The named runners are then run. The clone is discarded, which restores the file. The harness that applied the edits is not in this repository; this table is the record.

### The two named mutations

**1. The receipt validator accepts a receipt for another commit.** File `tooling/assurance_validation.py`, in `validate_receipts`. Edit `V1+2`: `if check["run"].get("commit") != commit or check["run"].get("tree") != tree:` becomes `if False:`. Result: caught. Named checks that failed: `run-build-assurance-manifest-cases.sh` case `foreign-signoff` (the receipt was refused for another reason, "names event 'push', for which the workflow runs no sign-off commands", so the case's diagnostic no longer matched) and `run-build-evidence-pack-cases.sh` case `signoff-other-commit` ("expected refusal"). `run-collect-assurance-receipts-cases.sh` stayed green, because the collector has its own candidate check (`C1`, below). Each half alone: `V1` (commit half removed) is caught only by `signoff-other-commit`; `V2` (tree half removed) is caught only by `required-check-other-commit`, both in the evidence-pack runner. The manifest and collector runners have no case that reaches either half alone.

**2. The required-steps check accepts a disabled job.** File `tooling/check-workflows.sh`. Edit `R1`: `found = list(differences(expected, actual, ""))` becomes `found = []`, so the comparison of `ci.yml` with `tooling/required-steps.json` never reports a difference. Result: caught by `run-check-workflows-cases.sh` (first failure `fail-required-step-form-01`: "expected refused (differs from tooling/required-steps.json), was accepted"). With that mutated checker the required `audit` job was also disabled in `ci.yml` (`if: ${{ github.run_id < 0 }}`) and `check-workflows.sh` was run on the real tree: still refused, by rule 8 ("emits a required receipt but has a job-level `if`"). So this one edit does not make the checker accept a disabled job: rule 8 still refuses it. Layer check (deliberately more than one edit, not a mutation record entry): a non-constant condition on a required job is refused by two layers, the rule 10 comparison (`R1`) and the rule 8 job-level-`if` refusal (`R15`); removing either alone leaves the job refused, and removing both together makes `check-workflows.sh` accept the disabled `audit` job (exit 0). A YAML `if: false` was still refused by the constant-false rule after those two edits; that rule was not removed entirely. Each layer's removal alone (`R1`, `R15`, `R5`) is caught by its own named case.

### All mutations

"Killed by" names the runner and the first case that failed. "Diag." means the case failed on a changed diagnostic (or a traceback) while the gate still exited nonzero.

| Id | File and edit | Gate | Result |
|---|---|---|---|
| V1 | `assurance_validation.py`: per-receipt check keeps only the tree comparison | validator | caught: evidence-pack `signoff-other-commit` |
| V2 | same, keeps only the commit comparison | validator | caught: evidence-pack `required-check-other-commit` |
| V1+2 | same, condition replaced by `False` | validator | caught: manifest `foreign-signoff` (diag.), evidence-pack `signoff-other-commit` |
| V3 | document-level `candidate` check drops the commit comparison | validator | caught: manifest `foreign` |
| V4 | document-level `candidate` check drops the tree comparison | validator | survived: no case has the right commit and a wrong document-level tree. The per-receipt tree check (`V2`) still applies, so a forged tree would need both removed |
| V5 | required check with status other than `pass` accepted | validator | caught: manifest `skipped`, evidence-pack `required-check-failed` |
| V6 | non-`success` step outcomes ignored | validator | caught: manifest `failed-step`, collector `outcome-failed`, evidence-pack `step-failed` |
| V7 | steps the workflow does not run ignored | validator | caught: manifest `extra-step`, collector `writer-extra-step`, evidence-pack `step-extra` |
| V8 | steps the receipt does not record ignored | validator | caught: `missing-step`, `writer-missing-step`, `step-missing` (diag.: `KeyError` traceback; production would still exit nonzero) |
| V9 | receipts from more than one event accepted | validator | caught: evidence-pack `two-events` only |
| V10 | receipts from more than one workflow run accepted | validator | caught: manifest `mixed-runs`, evidence-pack `two-runs` |
| V11 | `audit` removed from `REQUIRED_CHECKS` | validator | caught: manifest `downgraded`, collector honest-set step ("unexpected check receipt audit"), evidence-pack `required-check-missing` |
| V12 | `check_step_outcomes` returns at once | validator | caught: manifest `failed-step`, collector `writer-missing-step`, evidence-pack `step-failed` |
| V13 | an event with no expected commands is not refused | validator | caught: collector `writer-unknown-event` (diag.: `TypeError`); manifest and pack runners stay green |
| C1 | `collect-assurance-receipts.py`: per-receipt check drops the commit comparison | collector | caught: collector `foreign` |
| C2 | same, drops the tree comparison | collector | survived: no collector case has the right commit and a wrong tree. Downstream, `validate_receipts` repeats the tree comparison (`V2` shows only the evidence-pack runner tests it) |
| C3 | receipt from another event accepted | collector | caught: `wrong-event` |
| C4 | missing required receipts accepted | collector | caught: `missing` |
| C5 | duplicate receipt accepted | collector | caught: `duplicate` |
| C6 | unexpected receipt id accepted | collector | caught: `unknown` |
| C7 | required receipt with status other than `pass` accepted | collector | caught: `status-fail` |
| W1 | `write-assurance-receipt.py`: the first refusal of a failed required command removed | writer | caught (diag.): `writer-failed-step`; the writer still refuses the receipt at its second check (`check_step_outcomes`), exits 1 and writes no file |
| B1 | `build-assurance-manifest.py --validate`: identity compared with `HEAD` removed | manifest validator | survived: no case for a manifest that names another commit or tree. Receipts are compared against the manifest's own identity, so a change of identity alone is still refused (seen in the live check); a manifest whose identity and receipts were both changed to one other commit would no longer be refused (by reading) |
| B2 | `--validate`: `clean_tree` need not be true | manifest validator | survived; no case |
| B3 | `--validate`: source digest and size not compared | manifest validator | survived; no case |
| B4 | `--validate`: pending review requirement not required | manifest validator | survived; no case |
| B5 | builder: a dirty tree accepted without `--allow-dirty` | manifest builder | survived; every case passes `--allow-dirty` |
| B6 | `--validate`: the check set is not re-validated | manifest validator | survived; the builder validated it at build time |
| R1 | `check-workflows.sh`: comparison with `required-steps.json` reports nothing | required-steps check | caught: `fail-required-step-form-01`; the real-tree disabled job still refused by rule 8 |
| R2 | key `if` skipped when walking manifest keys only | required-steps check | survived: the edit was incomplete; a disabled job adds an `if` key to the workflow, which the second loop reports |
| R2b | key `if` dropped from both sides before comparing | required-steps check | caught: `fail-required-step-form-05` (refused, but not as a difference from the expected form); the real-tree disabled job still refused by rule 8 |
| R3 | key in the manifest and absent from the workflow not reported | required-steps check | caught: `fail-required-step-form-20` |
| R4 | key in the workflow and absent from the manifest not reported | required-steps check | caught: `fail-required-step-form-04` |
| R5 | literal `false` no longer read as constant false (rule 8) | disabled-job check | caught: `fail-condition-form-01`; the real-tree job still refused by rules 8 and 10 |
| R6 | job-level `continue-on-error` on a required job allowed | rule 8 | caught (diag.): `fail-required-job-continue-on-error` |
| R7 | every step-level `if` on a required command step approved | rule 9 | caught: `fail-required-step-form-37` |
| R8 | a missing `required-steps.json` is not a complaint | required-steps check | caught: `fail-manifest-form-01` |
| R9 | another workflow with a required job's name allowed | required-steps check | caught: `fail-required-step-form-41` |
| R10 | a workflow the manifest does not describe allowed | required-steps check | caught: `fail-manifest-form-04` |
| R11 | a manifest naming an absent file allowed | required-steps check | caught: `fail-manifest-form-06` (diag.: `FileNotFoundError`) |
| R12 | any manifest `schema_version` accepted | required-steps check | caught (diag.): `fail-manifest-form-03` |
| R13 | step labels and order not compared | required-steps check | caught: `fail-required-step-form-26` |
| R14 | receipt action `id`, `classification`, `command` need not be literals | rule 9 | caught: `fail-receipt-form-04` |
| R15 | job-level `if` on a required job no longer refused | rule 8 | caught (diag.): `fail-collector-dynamic-if` first, then `fail-receipt-form-17` and `fail-receipt-form-18` |
| CR1 | `check-workflows.sh`: when PyYAML is missing and `GITHUB_ACTIONS=true`, skip instead of fail (lines 121-124 deleted) | required-input rule | survived: the runner unsets `GITHUB_ACTIONS` for every case (`run-check-workflows-cases.sh:113-115`); no case covers the rule. In CI the `checks_01` step installs PyYAML and its outcome is asserted by the receipt, so a failed install is still caught elsewhere |
| Rself | no gate edit. `ci.yml` job `rust`, step `rust_test`: `cargo test --locked --workspace` becomes `... --no-run`; `bash tooling/check-workflows.sh --write-required-steps` rewrites the manifest | required-steps check, receipt validator | survived, as designed: with the workflow edit alone the checker refused (`jobs.rust.steps[5:rust_test].run` differs); after the writer rewrote the manifest (one changed line in each of two files), `check-workflows.sh`, `run-check-workflows-cases.sh`, and the manifest, collector and pack runners all passed, so a job that runs no tests is accepted. This is the limit stated at `check-workflows.sh:98-104` and in MU-04; no reviewer is required (`required_pull_request_reviews` is null) |
| S1 | `check-signoff.sh`: no commit refused for a missing sign-off | DCO check | caught: `unsigned-commit` |
| S2 | only the newest commit of the range is checked | DCO check | survived: in both refusal cases the unsigned commit is the tip |
| S3 | a missing base is not an error | DCO check | caught: `missing-base` |
| S4 | whole-line trailer match relaxed to substring | DCO check | survived; no case with a near-miss trailer |
| S5 | any trailer accepted, not only the author's | DCO check | survived; no case with a trailer naming another person |
| CT1 | `check-constant-time-asm.sh`: x86 conditional branches not counted | constant-time gate | survived: the runner's fixtures hold no branch |
| CT2 | aarch64 conditional branches not counted | constant-time gate | survived, same reason |
| CT3 | indirect calls and jumps not counted | constant-time gate | survived: the runner's fixtures hold no branch; a fixture with an indirect jump or call is still refused, as an unexpected callee, so the mutant changes the diagnostic and not the verdict |
| CT4 | in CI, having neither Linux target is not a failure | constant-time gate | survived; no case; on a GitHub-hosted runner the host is a Linux target, so the rule cannot fire there |
| CT5 | `subtle` and `conditional_` callees accepted | constant-time gate | survived; no case; a fixture with a `subtle` or `conditional_` callee is also refused as off the allow-list |
| RD1 | `aead-encrypt.json`: first hex digit of the first `output` flipped | independent reader | caught: `aead/aead-encrypt.json :: empty-plaintext` |
| RD2 | `protobuf-ratchet-body.json`: first `ratchet_key` digit flipped | independent reader | caught: `protobuf/protobuf-ratchet-body.json :: ascending-order` |
| RD3 | reader `COMPOSITE_LEN` 102 to 103 | independent reader | caught: `aead/aead-decrypt.json :: session-associated-data` |
| RD4 | reader `BUNDLE_LEN_MLKEM1024` 1811 to 1810 | independent reader | caught: `negative :: PB-01 bundle round trip` |

Tally: 60 rows, 59 single edits and one scenario with no edit to a gate (`Rself`). Receipt writer, collector and validator 22 (20 caught, 2 survived); manifest builder and validator 6 (0 caught); `check-workflows.sh` 17 (15 caught; `R2` was an incomplete edit and `R2b` is its caught form; `CR1` survived); `Rself` survived; DCO check 5 (2 caught); constant-time gate 5 (0 caught); independent reader 4 (4 caught).

Live check of the `B` survivors. To rule out equivalent mutants, a manifest was built with the runner's method and `--validate` was called on the unchanged manifest and on seven tampered copies. The unmutated `--validate` accepted the unchanged one and refused all seven tampers (another commit, another tree, `clean_tree` false, an altered source digest, a missing review requirement, an accepted review requirement, a failed required check). With `B1` to `B4` applied together it accepted `clean_tree` false, the altered digest, and both review-requirement tampers. `B1` alone is largely redundant with the receipt check, as noted in the table.

One-off breaks of gates with no retained control (not in the tally, each on a fresh clone, none retained):

| Break | Gate | Result |
|---|---|---|
| `| `theorem probe_hygiene : True := kdf_ck._proof_3` appended to `T1.lean` | `check-proof-hygiene.sh` | refused |
| first registry row deleted from `tacenta-core/AUTHENTICATION-BOUNDARY.md` | `check_authentication_boundary.py` | refused |
| a line appended to a triple-unit and to a session-unit source | `assemble-triple-unit.sh --check`, `assemble-session-unit.sh --check` | both refused |
| a line appended to `UnitT1.lean` | `port-unit-proofs.sh --check` | refused |
| `Model/OrphanProbe.lean` added, not imported by any audit module | `check-audit-reach.sh` | refused (exit 1, "outside the import closure"); accepted again after removal |
| a committed vector's first hex digit flipped, then `regenerate-vectors.sh` | `proofs_vectors` | `git status` shows the file modified (the step's `exit 1` condition); the unmodified tree gives an empty status |
| PyYAML made unimportable | `check-workflows.sh`, `run-check-workflows-cases.sh` | with `GITHUB_ACTIONS=true` both exit 1; without it both print a skip line and exit 0 |
| no `TACENTA_DIFFTEST` binary | `the_model_and_the_core_agree_on_generated_sequences` | `GITHUB_ACTIONS=true` or `TACENTA_DIFFTEST_REQUIRED=1`: panic, exit 101; neither: prints "skipping" and passes |
| no base ref; empty receipts directory | `check-signoff.sh`; collector | both exit 1 |

## Addendum, 2026-10-01: the evidence tooling, with a retained harness

`tooling/mutate-evidence-gates.py` is the harness the section above says is not in this repository, for the receipt, manifest, pack,
publisher, reproduction and review tooling. It copies `tooling/` and the files the case runners read into a throwaway git repository,
requires the unedited copy to pass the four case runners, and then, for each entry in its table, replaces one string that must occur
exactly once, commits the edit there and runs the runners until one fails. It refuses to run if the tooling or the evidence files it copies
differ from `HEAD`, so the commit named below is what ran.

Each edit is reported as one of three things. Seen as accepted: a case that expected a refusal saw an acceptance, an honest input was
refused, or an assertion failed; the check is held. Seen as message only: the first failing case was still refused, for another reason, and
only its expected message no longer matched, and the failing runner run to its end has no case that fails for more than a message. Survived:
every runner stayed green. An edit that is not seen as accepted fails the run unless the harness lists it as equivalent with the reason its
verdict cannot change (the same inputs are refused by a later check). A listed edit that a case sees as accepted is stale and fails the run too.

Run at `543ced7` on macOS 26.5.1 (Apple silicon, bash 3.2.57, Python 3.9.6, git 2.50.1), the whole table in three parts run at the same time: 121 edits: 103 seen as accepted, 17 seen as message only and claimed equivalent, 1 survived and claimed equivalent, 0 unexpected.
Ids beginning MT, PK, PB, RP, RC, RV and SC are this addendum's own and do not refer to rows of the earlier tables; B1 to B6, V1 to V4, C1 and
C2 are the earlier rows the same checks were first named by, and B1 to B6, V4 and C2 survived at `dea57eaf`. Ids beginning X are the edits of
the fresh review of this branch (its report names them), except X41 and X52, which this round added.

Seen as accepted: 103. Seen as message only, claimed equivalent: 17. Survived, claimed equivalent: 1.
Unexpected or stale: 0.

| Id | Edit | Result | Seen by |
| --- | --- | --- | --- |
| B1 | --validate does not compare the manifest identity with HEAD | seen as accepted | manifest: identity-other-commit-consistent |
| B1c | --validate compares the tree with HEAD but not the commit | seen as accepted | manifest: identity-other-commit-consistent |
| B1t | --validate compares the commit with HEAD but not the tree | seen as accepted | manifest: identity-other-tree-consistent |
| B2 | --validate does not need clean_tree to be true | seen as accepted | manifest: not-clean |
| B3d | --validate does not compare a source digest | seen as accepted | manifest: source-digest |
| B3s | --validate does not compare a source size | seen as accepted | manifest: source-size |
| B4 | --validate does not need the pending review requirement | seen as accepted | manifest: review-dropped |
| B5 | the builder accepts a dirty tree without --allow-dirty | seen as accepted | manifest: dirty-tracked |
| B6 | --validate does not re-validate the check set | seen as accepted | manifest: check-failed |
| MT1 | --validate allows extra or missing top-level fields | seen as accepted | manifest: manifest-extra-field |
| MT2 | --validate allows extra or missing identity fields | seen as accepted | manifest: identity-field-added |
| MT3 | --validate allows another repository name | seen as accepted | manifest: identity-repository |
| MT4 | --validate allows a short commit or tree | message only, claimed equivalent | manifest: identity-commit-short |
| MT5 | --validate does not check which generator wrote the manifest | seen as accepted | manifest: generator-digest |
| MT5d | --validate checks the generator path but not its digest | seen as accepted | manifest: generator-digest |
| MT6 | --validate allows extra fields in a source entry | seen as accepted | manifest: source-entry-field-added |
| MT7 | an ignored file anywhere makes the tree clean, not only under .assurance/ | seen as accepted | manifest: dirty-ignored |
| MT7b | the .assurance/ receipt workspace makes the tree dirty | seen as accepted | manifest: an assertion or a step that must pass failed |
| MT8 | an untracked file does not make the tree dirty | seen as accepted | manifest: dirty-untracked |
| MT9 | an ignored file does not make the tree dirty | seen as accepted | manifest: dirty-ignored |
| MT10 | the dirty-path report loses the first character of its first path | message only, claimed equivalent | manifest: dirty-tracked |
| V1 | a receipt for another commit is accepted | seen as accepted | manifest: receipt-other-commit |
| V2 | a receipt for another tree is accepted | seen as accepted | manifest: receipt-other-tree |
| V3 | the receipt document may name another commit | seen as accepted | manifest: foreign |
| V4 | the receipt document may name another tree | seen as accepted | manifest: foreign-tree |
| C1 | the collector accepts a receipt for another commit | seen as accepted | collector: foreign |
| C2 | the collector accepts a receipt for another tree | seen as accepted | collector: foreign-tree |
| PK0 | the pack need not carry the workflow and the receipt action | seen as accepted | pack: missing-workflow |
| PK1 | --candidate-repo is accepted and ignored | seen as accepted | pack: forged-source |
| PK2 | a candidate commit that is not in the repository is not noticed | message only, claimed equivalent | pack: commit-absent |
| PK3 | the pack may name another tree than its commit has | seen as accepted | pack: tree-of-another-commit |
| PK4 | a packed source need not be the commit's file | seen as accepted | pack: forged-source |
| PK5 | a packed source that is not a file of the commit is not named as such | message only, claimed equivalent | pack: source-not-in-commit |
| PK6 | the manifest's generator digest is not compared with the commit's | seen as accepted | pack: forged-generator |
| PK7 | no packed source is compared with git | seen as accepted | pack: forged-source |
| PK8 | a short or non-hex candidate commit or tree is accepted | seen as accepted | pack: pack-candidate-short-everywhere |
| PK9 | --candidate-repo is accepted with a build | seen as accepted | pack: candidate-repo-without-verify |
| PB1 | an unverified pack is uploaded | seen as accepted | pack: publish-forged-source |
| PB2 | the pack is not authenticated against git before upload | seen as accepted | pack: publish-forged-source |
| PB3 | an upload may replace an existing key | seen as accepted | pack: an assertion or a step that must pass failed |
| PB4 | an object without Compliance retention is recorded | seen as accepted | pack: publish-governance-retention |
| PB4m | retention in a mode other than COMPLIANCE is accepted | seen as accepted | pack: publish-governance-retention |
| PB4d | retention without an end date is accepted | seen as accepted | pack: publish-retention-without-date |
| PB5 | an upload that returns no version ID is recorded | seen as accepted | pack: publish-empty-version-id |
| PB6 | an existing publication receipt is replaced | seen as accepted | pack: publish-existing-receipt |
| PB7 | publication without a receipt path | message only, claimed equivalent | pack: publish-needs-a-receipt |
| PB8 | the pack manifest is not uploaded last | seen as accepted | pack: an assertion or a step that must pass failed |
| PB9 | the archive prefix does not carry the pack digest | seen as accepted | pack: publish-dry-run |
| RP1 | a hosted artifact of another candidate is compared with the pack | message only, claimed equivalent | pack: hosted-of-another-candidate |
| RP2 | a hosted file need not be the packed one | seen as accepted | pack: hosted-not-the-packed-manifest |
| RP3 | the candidate tree is not compared with the commit's | message only, claimed equivalent | pack: hosted-names-another-tree |
| RP4 | the rebuilt manifest need not equal the given one | seen as accepted | pack: hosted-manifest-not-the-rebuilt |
| RP5 | the rebuilt pack is not compared | seen as accepted | pack: pack-not-what-the-builder-writes |
| RP6 | the rebuilt pack may list other files | message only, claimed equivalent | pack: pack-with-a-source-the-builder-would-not-pack |
| RP7 | the rebuilt pack may differ in a file | seen as accepted | pack: pack-not-what-the-builder-writes |
| RP8 | a reproduction leaves its worktree in the repository | seen as accepted | pack: WRONG  a reproduction left a worktree in the repository |
| RP9 | the candidate's own pack verifier is not run | message only, claimed equivalent | pack: reproduce-pack-tampered |
| RP10 | the pack is not authenticated against git | message only, claimed equivalent | pack: reproduce-pack-forged-source |
| RC1 | the receipt schema version is not checked | seen as accepted | review receipt: schema-one |
| RC2u | an unknown receipt field is accepted | seen as accepted | review receipt: unknown-field |
| RC2m | a missing receipt field is not named | message only, claimed equivalent | review receipt: pack-binding-absent |
| RC3 | a template placeholder is accepted | seen as accepted | review receipt: placeholder |
| RC4 | a receipt for another candidate is accepted | seen as accepted | review receipt: foreign |
| RC5 | the receipt need not bind the pack manifest | seen as accepted | review receipt: wrong-pack |
| RC6 | a receipt without reviewer identity is accepted | seen as accepted | review receipt: missing-reviewer |
| RC7 | a receipt without artifacts read is accepted | message only, claimed equivalent | review receipt: no-artifacts |
| RC8 | a required artifact need not be named | seen as accepted | review receipt: artifact-unnamed |
| RC9 | malformed cross-cutting notes are accepted | seen as accepted | review receipt: notes-malformed |
| RC10 | a receipt with no dispositions is accepted | message only, claimed equivalent | review receipt: no-claims |
| RC11 | a disposition with other fields is accepted | seen as accepted | review receipt: claim-extra-field |
| RC12 | a repeated or empty reference is accepted | seen as accepted | review receipt: duplicate-exact |
| RC13 | an unknown disposition is accepted | seen as accepted | review receipt: invalid-disposition |
| RC14 | a finding that is not text is accepted | message only, claimed equivalent | review receipt: finding-not-text |
| RC15 | a disposition without finding text is accepted | seen as accepted | review receipt: accepted-without-text |
| RC16 | a reference to a section the ledger lacks is accepted | message only, claimed equivalent | review receipt: unknown-section |
| RC17 | a malformed section digest is accepted | message only, claimed equivalent | review receipt: digest-malformed |
| RC18 | a disposition on other text than the pack's is accepted | seen as accepted | review receipt: digest-of-another-section |
| RC19 | a section with no disposition is accepted | seen as accepted | review receipt: one-section-missing |
| RC20 | --require-no-findings does not refuse a finding | seen as accepted | review receipt: finding-refused |
| RC21 | the pack's CLAIMS.md is not held to its manifest digest | seen as accepted | review receipt: tampered-ledger-crafted |
| RC22 | a pack without CLAIMS.md is read as an empty ledger | seen as accepted | review receipt: ledger-twice |
| RC23 | two sections with one title are accepted | seen as accepted | review receipt: twice-ledger |
| RC24 | the ledger's introduction need not be dispositioned | seen as accepted | review receipt: an assertion or a step that must pass failed |
| RC25 | the pack manifest schema is not checked | seen as accepted | review receipt: pack-schema |
| RC26 | the ledger is read through the platform's newline translation | seen as accepted | review receipt: WRONG  line endings are part of a section's digest |
| RC27 | a receipt with schema_version 2.0 is accepted | seen as accepted | review receipt: schema-two-point-zero |
| RC28 | a disposition that is not a string reaches the membership test | message only, claimed equivalent | review receipt: disposition-not-a-string |
| X1a | CLAIMS.md need not be named as read | seen as accepted | review receipt: unnamed-CLAIMS.md |
| X1b | LIMITATIONS.md need not be named as read | seen as accepted | review receipt: unnamed-LIMITATIONS.md |
| X1c | verification-manifest.json need not be named as read | seen as accepted | review receipt: unnamed-verification-manifest.json |
| X1d | evidence-index.json need not be named as read | seen as accepted | review receipt: unnamed-evidence-index.json |
| X1e | P6-L2-TARGET-DECISION.md need not be named as read | seen as accepted | review receipt: unnamed-P6-L2-TARGET-DECISION.md |
| X1f | PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md need not be named as read | seen as accepted | review receipt: unnamed-PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md |
| X2 | a placeholder in a list of strings (artifacts_read, cross_cutting_notes) is not found | seen as accepted | review receipt: placeholder-in-artifacts |
| X3 | a section title keeps trailing whitespace (the carriage return of a CRLF ledger) | seen as accepted | review receipt: WRONG  line endings are part of a section's digest |
| X4 | a section's digest covers its heading line only, not its text | seen as accepted | review receipt: digest-middle |
| X5 | the last section's digest covers its heading only | seen as accepted | review receipt: digest-last-byte-of-last |
| X6 | the introduction's digest leaves out its last byte | seen as accepted | review receipt: an assertion or a step that must pass failed |
| X7 | the last section's digest leaves out its last byte | seen as accepted | review receipt: digest-last-byte-of-last |
| X8 | every section's digest leaves out its last byte | seen as accepted | review receipt: digest-last-byte-of-last |
| X20 | authentication skips the first listed file | seen as accepted | pack: forge-.github/actions/assurance-receipt/action.yml |
| X20b | authentication skips the last listed file | seen as accepted | pack: source-not-in-commit |
| X21 | the packed workflow and receipt action are not compared with git | seen as accepted | pack: forge-.github/actions/assurance-receipt/action.yml |
| X22 | the packed tooling files (required-steps.json, the checkers) are not compared with git | seen as accepted | pack: forge-tooling/assurance-manifest.schema.json |
| X23 | the packed spec and vector files are not compared with git | seen as accepted | pack: forge-tacenta-spec/security-properties/INVARIANT-EVIDENCE-SOURCE-DECISION.md |
| X24 | the packed verification manifest and LIMITATIONS.md are not compared with git | seen as accepted | pack: forge-tacenta-proofs/LIMITATIONS.md |
| X40 | a reproduction leaves its scratch directory | seen as accepted | pack: a reproduction left its scratch directory |
| X41 | a reproduction may leave bytecode in the repository | seen as accepted | pack: WRONG  a reproduction with bytecode writing allowed changed the repository |
| X50 | a truthy clean_tree is enough | seen as accepted | manifest: clean-tree-truthy |
| X51 | a manifest of schema_version 2 is accepted | seen as accepted | manifest: manifest-schema |
| X52 | an empty version ID is recorded | seen as accepted | pack: publish-empty-version-id |
| RV1 | a reviewed candidate may carry a finding | seen as accepted | review receipt: reviewed-with-a-finding |
| RV2 | the reviewed pack is not authenticated against git | seen as accepted | review receipt: reviewed-pack-forged-workflow |
| RV3 | the pack may name another candidate than the manifest | survived, claimed equivalent | none |
| RV4 | the pack need not hold the reviewed manifest's bytes | seen as accepted | review receipt: reviewed-manifest-not-the-packed-one |
| RV5 | the manifest is not validated | seen as accepted | review receipt: reviewed-manifest-extra-field |
| SC1 | a changed section is reported unchanged | seen as accepted | review receipt: WRONG  an edited section is reported changed |
| SC2 | a removed section is not reported | seen as accepted | review receipt: WRONG  a removed section is reported gone |
| SC3 | a template replaces an existing file | seen as accepted | review receipt: template-exists |
| SC4 | --template is accepted with --since | seen as accepted | review receipt: template-with-since |
| SC5 | a schema 1 receipt serves as an earlier state | seen as accepted | review receipt: since-schema-one |

Claimed equivalent, with the reason each verdict cannot change:

- MT4: the comparison with `git rev-parse HEAD`, which follows, refuses every id that is not the full commit and tree.
- MT10: only the path printed in the refusal changes; the tree is dirty either way.
- PK2: the tree lookup that follows fails for a commit the repository does not hold, so the same pack is refused.
- PK5: the byte comparison that follows refuses a file the commit does not have, as different from the packed one.
- PB7: without a receipt path the publisher fails on `None.exists()` before it uploads anything.
- RP1: the byte comparison of the hosted receipts with the packed receipts, which follows, refuses the same inputs, because the receipts name their candidate.
- RP3: the candidate's manifest builder, which runs next, refuses receipts that name another tree than the commit's, and the pack check refuses a pack that does.
- RP6: the candidate's own verifier requires every file its builder writes, so the rebuilt pack has no file the given pack lacks, and a file only the given pack has fails the lookup that follows.
- RP9: a pack that equals the rebuild byte for byte is one the candidate's builder wrote, which verifies.
- RP10: a pack that equals the rebuild byte for byte has sources the builder copied from the commit.
- RC2m: each required field is refused by its own check below.
- RC7: an empty or missing list names none of the required artifacts, and a list of non-strings raises, so the same receipts are refused.
- RC10: no claims leaves every section uncovered, and claims that are not a list are refused by the loop.
- RC14: a finding that is not a string raises at the text check that follows, which also refuses.
- RC16: an unknown section raises KeyError at its digest lookup, so the same receipts are refused.
- RC17: a digest that is not 64 lower-case hex digits never equals a section's digest.
- RC28: an unhashable disposition raises TypeError at the membership test, which also refuses; the check keeps the refusal on the error path.
- RV3: the pack verifier already requires the packed manifest to name the pack's candidate, and the comparison of the packed manifest bytes with the given manifest follows, so together they refuse the same inputs.

What this does not show: that the harness's table is every check these tools make (it is the checks the cases were written for), that the
receipts are produced by a hosted run, or anything about the gates outside this tooling. Equivalence is by reading the code and is not proved.
`Rself` above is unchanged: the workflow and `tooling/required-steps.json` can still be edited together.


## Re-run and extension, 2026-10-01

The harness that applied the single edits above was not kept, so the record could not be repeated.
`tooling/mutate-gates.py` is a harness, and `tooling/gate-mutations.json` holds the edits. For each edit it makes
a disposable worktree of the commit under test, replaces one text in one file (which must occur exactly the stated
number of times), commits that, runs the named control there and requires it to fail with output that contains `expect`,
the name of a case or a diagnostic. A baseline of each control on the unchanged tree comes first, and a red baseline
stops the run. The failing case is then classified: **accepted** when it saw the gate accept an input it must
refuse; **behaviour** when it saw another wrong verdict (an honest input refused, a count or a call wrong, an
assertion failed); **message only** when every failing line is a refusal whose diagnostic no longer matches, after
the runner has been run to its end with its stop-on-failure switched off to see whether any other case fails for
more. A message-only edit, and an edit no case notices, fails the run unless it carries an `equivalent` reason (its
verdict cannot change) or an `uncovered` reason (a known gap, named); a listed edit that a case sees as accepted or
as another wrong verdict is stale and fails the run. `python3 tooling/mutate-gates.py` runs all of them; `--only
ID...` runs some; `-v` shows the failing output; `--json FILE` writes the results. Like `tooling/mutate-inventory.py` it is a local tool and nothing in
CI runs it. `tooling/tests/run-mutate-gates-cases.sh` holds the harness to eleven cases of its own.

Run on the tree this section was added to (the harness reads the commit it is run in, so the controls and the gates were the committed
ones; only the documents changed afterwards), on macOS (Apple silicon), bash 3.2, Python 3.9 with PyYAML, Lean v4.31.0, on a machine
shared with other builds. All 205 edits turn their control red. For 141 a case saw the gate accept an input it must
refuse; for 49 a case saw another wrong verdict; 15 change only a diagnostic or survive
and are listed below as equivalent or uncovered, with the reason each cannot be seen. 0 turned the control red for another reason than the one named.

Rows of the 2026-09-30 table that survived then and have a case now: `S2`, `S4`, `S5` (the sign-off check), `CT1` to
`CT5` (the constant-time reader), `CR1` (the skip-or-fail rule of `check-workflows.sh`), `B1` to `B6` (the manifest
builder and `--validate`), `V4` and `C2` (the validator and collector, right commit and wrong tree). The one-off
breaks of gates with no retained control (conflict markers, proof hygiene, the authentication boundary, the unit
`--check` modes, `check-audit-reach.sh`, vector currency, the PyYAML rule, the differential harness, a missing base)
each have a retained case now, except that the vector-currency and differential cases are not yet CI steps.

### Equivalent edits

| Id | File | Edit | Why its verdict cannot change |
| --- | --- | --- | --- |
| PK2 | `tooling/build-evidence-pack.py` | the builder accepts receipts of another schema version | `validate_receipts` and the manifest's own `--validate`, which run first, refuse a document of another schema version, so the same inputs are refused |
| PK3 | `tooling/build-evidence-pack.py` | the builder accepts receipts for another candidate than the manifest | the candidate that `validate_receipts` takes comes from the manifest, and the comparison of the receipts' checks with the manifest's, which follows, refuses receipts for another candidate; the pack check refuses a pack that names one |
| PK3a | `tooling/build-evidence-pack.py` | the builder compares the tree of the candidate but not its commit | the candidate that `validate_receipts` takes comes from the manifest, and the comparison of the receipts' checks with the manifest's, which follows, refuses receipts for another candidate; the pack check refuses a pack that names one |
| PK3b | `tooling/build-evidence-pack.py` | the builder compares the commit of the candidate but not its tree | the candidate that `validate_receipts` takes comes from the manifest, and the comparison of the receipts' checks with the manifest's, which follows, refuses receipts for another candidate; the pack check refuses a pack that names one |
| AL4 | `tooling/install-actionlint.sh` | an archive without the executable is not refused as such | the next line runs `$destination/actionlint -version`, which fails for a missing file under `set -e`, so the same archive is refused; only the message changes |
| GA-triple-header | `tacenta-proofs/scripts/assemble-triple-unit.sh` | assemble-triple-unit.sh writes a copy for a leaf with no inner attribute block | the self-check of the written copy refuses the same leaf, and only which check says so changes |
| GA-triple-use | `tacenta-proofs/scripts/assemble-triple-unit.sh` | assemble-triple-unit.sh accepts a copy with the inserted use line twice | with the guard removed the awk scan that follows is given a two-line start value and fails (exit 2), so the same leaf is refused; only the words change |
| GA-triple-block | `tacenta-proofs/scripts/assemble-triple-unit.sh` | assemble-triple-unit.sh accepts a copy with the inserted block twice | the check that exactly one `use` line was inserted, which follows, refuses the same leaf, because the block it holds also carries one |
| GA-braid-header | `tacenta-proofs/scripts/assemble-braid-unit.sh` | assemble-braid-unit.sh writes a copy for a leaf with no inner attribute block | the self-check of the written copy refuses the same leaf, and only which check says so changes |
| GA-braid-use | `tacenta-proofs/scripts/assemble-braid-unit.sh` | assemble-braid-unit.sh accepts a copy with the inserted use line twice | with the guard removed the awk scan that follows is given a two-line start value and fails (exit 2), so the same leaf is refused; only the words change |
| GA-braid-block | `tacenta-proofs/scripts/assemble-braid-unit.sh` | assemble-braid-unit.sh accepts a copy with the inserted block twice | the check that exactly one `use` line was inserted, which follows, refuses the same leaf, because the block it holds also carries one |

### Uncovered edits (known gaps)

| Id | File | Edit | Why no case sees it |
| --- | --- | --- | --- |
| GA-triple-diffq | `tacenta-proofs/scripts/assemble-triple-unit.sh` | assemble-triple-unit.sh does not compare the stripped copy with the leaf | the block is found exactly once at the written position or the check above refuses first; no leaf reaches this comparison with a difference, and the comparison is the self-check that catches a future change of the insertion code |
| GA-triple-late | `tacenta-proofs/scripts/assemble-triple-unit.sh` | assemble-triple-unit.sh does not check where the inserted use landed | it fires when the scan for the header's end stops before an inner attribute; no leaf in the tree is read that way, and none was constructed |
| GA-braid-diffq | `tacenta-proofs/scripts/assemble-braid-unit.sh` | assemble-braid-unit.sh does not compare the stripped copy with the leaf | the block is found exactly once at the written position or the check above refuses first; no leaf reaches this comparison with a difference, and the comparison is the self-check that catches a future change of the insertion code |
| GA-braid-late | `tacenta-proofs/scripts/assemble-braid-unit.sh` | assemble-braid-unit.sh does not check where the inserted use landed | it fires when the scan for the header's end stops before an inner attribute; no leaf in the tree is read that way, and none was constructed |

### Guard removal

`python3 tooling/mutate-gates.py --guards FILE... --verdict`: for each gate file the harness finds every guard, an `if` or `elif` whose next
line fails, replaces its condition by false one at a time and runs the controls that `tooling/gate-inventory.json` names for the gate. A guard
whose removal changes no case's output is a survivor. With `--verdict`, a guard whose removal changes only a diagnostic and no verdict is a survivor
too: its removal is seen by a case that expects the words, and the gate still refuses every input the cases give it.

| Gate | Guards | Removal changes a verdict | Removal changes only a diagnostic | Survive | Lines |
| --- | --- | --- | --- | --- | --- |
| `tooling/check-ledger-review-receipt.py` | 13 | 12 | 1 | 0 | diagnostic only 25 |
| `tooling/collect-assurance-receipts.py` | 14 | 10 | 4 | 0 | diagnostic only 40, diagnostic only 52, diagnostic only 60, diagnostic only 85 |
| `tooling/write-assurance-receipt.py` | 6 | 2 | 4 | 0 | diagnostic only 40, diagnostic only 43, diagnostic only 46, diagnostic only 52 |
| `tooling/build-evidence-pack.py` | 23 | 11 | 10 | 2 | diagnostic only 63, diagnostic only 77, diagnostic only 81, diagnostic only 122, diagnostic only 126, diagnostic only 132, diagnostic only 135, diagnostic only 139, diagnostic only 158, diagnostic only 176, survived 79, survived 98 |
| `tooling/build-assurance-manifest.py` | 13 | 7 | 0 | 6 | survived 98, survived 123, survived 136, survived 139, survived 164, survived 169 |
| `tooling/assurance_validation.py` | 28 | 12 | 5 | 11 | diagnostic only 78, diagnostic only 81, diagnostic only 84, diagnostic only 134, diagnostic only 169, survived 101, survived 107, survived 113, survived 116, survived 119, survived 122, survived 124, survived 126, survived 128, survived 130, survived 143 |
| `tooling/check-lifecycle-boundary-surface.py` | 2 | 2 | 0 | 0 | none |
| `tooling/check_authentication_boundary.py` | 2 | 1 | 1 | 0 | diagnostic only 528 |
| `tooling/check-labels.sh` | 2 | 2 | 0 | 0 | none |
| `tooling/check-traceability.py` | 1 | 1 | 0 | 0 | none |
| `tooling/check-session-operation-traces.py` | 1 | 1 | 0 | 0 | none |
| `tacenta-proofs/scripts/check-lifecycle-translation-coverage.py` | 2 | 2 | 0 | 0 | none |
| `tooling/check-conflict-markers.sh` | 1 | 1 | 0 | 0 | none |
| `tooling/check-proof-hygiene.sh` | 1 | 1 | 0 | 0 | none |
| `tooling/check-signoff.sh` | 1 | 1 | 0 | 0 | none |
| `tooling/install-actionlint.sh` | 3 | 2 | 0 | 1 | survived 42 |
| `tooling/seed-lake-packages.sh` | 1 | 0 | 0 | 1 | survived 60 |
| `tooling/check-precondition-shapes.py` | 3 | 3 | 0 | 0 | none |

Gates this does not cover: `tooling/check-vectors.py` and `tooling/check-workflows.sh` (their failures are not written in the form the harness reads),
`tooling/check-audit-reach.sh` and `tooling/check-vectors-current.sh` (the controls need a built Lean workspace; pass `--link` with the `.lake` directories), and the
assemblers' write-time guards, which are the `GA-*` edits above.

### Gaps these runs found and closed in this change

The label check had no case for two constants with one value (`AL-labels-dupes`). Nine of the thirteen guards of `tooling/check-ledger-review-receipt.py`,
one of `check-lifecycle-translation-coverage.py`, the collector's receipt loader, the boundary-surface check's missing-root guard, the
precondition-shape check's unterminated-string guard and four guards of the evidence-pack builder had no case needing them and now have one.
The fresh-eyes review of this change then found fifteen single edits to the sign-off check, the constant-time reader, the conflict-marker check and the installers that
every case accepted (`S6` to `S8`, `CT12` to `CT16`, `CM7`, `CM8`, `IE7` to `IE9`, `SL4`, `AL3`); each has a case. It found that edits `AB8`, `AB12`, `AR-mentions`, `IE5`
and the seven `GN-port-*-count` edits were red only because a diagnostic changed; each has a case with an input the mutated gate accepts. Defects the new
cases found: `tooling/build-assurance-manifest.py` printed a dirty tree's first path without its first character when that path was an unstaged change
(the refusal itself was right); eight port scripts never printed their "committed copy differs" line, because a `diff | head` under `pipefail` ended the script
first (the exit status was right).

### All edits

| Id | File | Edit | Control | Result |
| --- | --- | --- | --- | --- |
| S1 | `tooling/check-signoff.sh` | no commit is refused for a missing sign-off | `run-check-signoff-cases.sh` | seen as accepted |
| S2 | `tooling/check-signoff.sh` | only the newest commit of the range is checked | `run-check-signoff-cases.sh` | seen as accepted |
| S3 | `tooling/check-signoff.sh` | a missing base is not an error | `run-check-signoff-cases.sh` | seen as accepted |
| S4 | `tooling/check-signoff.sh` | whole-line trailer match relaxed to a substring match | `run-check-signoff-cases.sh` | seen as accepted |
| S5 | `tooling/check-signoff.sh` | any trailer is accepted, not only the author's | `run-check-signoff-cases.sh` | seen as accepted |
| CT1 | `tooling/check-constant-time-asm.sh` | x86 conditional branches are not counted | `run-check-constant-time-asm-cases.sh` | seen as another wrong verdict |
| CT2 | `tooling/check-constant-time-asm.sh` | aarch64 conditional branches are not counted | `run-check-constant-time-asm-cases.sh` | seen as another wrong verdict |
| CT3 | `tooling/check-constant-time-asm.sh` | indirect calls and jumps are read as named callees | `run-check-constant-time-asm-cases.sh` | seen as another wrong verdict |
| CT4 | `tooling/check-constant-time-asm.sh` | in CI, having neither Linux target is not a failure | `run-check-constant-time-asm-cases.sh` | seen as accepted |
| CT5 | `tooling/check-constant-time-asm.sh` | subtle and conditional_ callees are not refused as such | `run-check-constant-time-asm-cases.sh` | seen as another wrong verdict |
| CT6 | `tooling/check-constant-time-asm.sh` | the allowed length compare may follow a load | `run-check-constant-time-asm-cases.sh` | seen as another wrong verdict |
| CT7 | `tooling/check-constant-time-asm.sh` | more than one length compare is allowed | `run-check-constant-time-asm-cases.sh` | seen as another wrong verdict |
| CT8 | `tooling/check-constant-time-asm.sh` | a function the gate cannot find is not a failure | `run-check-constant-time-asm-cases.sh` | seen as accepted |
| CT9 | `tooling/check-constant-time-asm.sh` | several assembly files for one crate are not a failure | `run-check-constant-time-asm-cases.sh` | seen as accepted |
| CT10 | `tooling/check-constant-time-asm.sh` | main ignores a refused or unknown callee | `run-check-constant-time-asm-cases.sh` | seen as accepted |
| CT11 | `tooling/check-constant-time-asm.sh` | main ignores a branch the reader counted | `run-check-constant-time-asm-cases.sh` | seen as accepted |
| CR1 | `tooling/check-workflows.sh` | in CI, missing PyYAML is a skip, not a failure | `run-check-workflows-cases.sh` | seen as accepted |
| CR2 | `tooling/tests/run-check-workflows-cases.sh` | the case runner skips, and passes, in CI without PyYAML | `run-check-workflows-cases.sh` | seen as accepted |
| CR3 | `tooling/check-workflows.sh` | in CI, a missing python3 is a skip, not a failure | `run-check-workflows-cases.sh` | seen as accepted |
| B1 | `tooling/build-assurance-manifest.py` | --validate does not compare the manifest's identity with the commit under test | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| B1a | `tooling/build-assurance-manifest.py` | --validate compares the tree of the identity but not its commit | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| B1b | `tooling/build-assurance-manifest.py` | --validate compares the commit of the identity but not its tree | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| B2 | `tooling/build-assurance-manifest.py` | --validate accepts a manifest that does not assert a clean tree | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| B3 | `tooling/build-assurance-manifest.py` | --validate compares neither the digest nor the size of a source | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| B3a | `tooling/build-assurance-manifest.py` | --validate does not compare the digest of a source | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| B3b | `tooling/build-assurance-manifest.py` | --validate does not compare the size of a source | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| B4 | `tooling/build-assurance-manifest.py` | --validate does not require a pending review requirement | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| B4a | `tooling/build-assurance-manifest.py` | --validate accepts a review requirement that is not pending | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| B5 | `tooling/build-assurance-manifest.py` | the builder accepts a dirty tree without --allow-dirty | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| B5b | `tooling/build-assurance-manifest.py` | any ignored file is excused from the dirty-tree check | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| B5c | `tooling/build-assurance-manifest.py` | a manifest built with --allow-dirty on a dirty tree says the tree is clean | `run-build-assurance-manifest-cases.sh` | seen as another wrong verdict |
| B6 | `tooling/build-assurance-manifest.py` | --validate does not re-validate the check set | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| V1 | `tooling/assurance_validation.py` | the validator reads the tree of a receipt's run but not its commit | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| V2 | `tooling/assurance_validation.py` | the validator reads the commit of a receipt's run but not its tree | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| V3 | `tooling/assurance_validation.py` | the validator reads the tree of the document's candidate but not its commit | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| V4 | `tooling/assurance_validation.py` | the validator reads the commit of the document's candidate but not its tree | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| C1 | `tooling/collect-assurance-receipts.py` | the collector reads the tree of a receipt's run but not its commit | `run-collect-assurance-receipts-cases.sh` | seen as accepted |
| C2 | `tooling/collect-assurance-receipts.py` | the collector reads the commit of a receipt's run but not its tree | `run-collect-assurance-receipts-cases.sh` | seen as accepted |
| CM1 | `tooling/check-conflict-markers.sh` | the separator line of a conflict is not a marker | `run-source-gate-cases.sh` | seen as accepted |
| CM2 | `tooling/check-conflict-markers.sh` | the opening line of a conflict is not a marker | `run-source-gate-cases.sh` | seen as accepted |
| CM3 | `tooling/check-conflict-markers.sh` | the closing line of a conflict is not a marker | `run-source-gate-cases.sh` | seen as accepted |
| CM4 | `tooling/check-conflict-markers.sh` | markers are found and the check passes anyway | `run-source-gate-cases.sh` | seen as accepted |
| CM5 | `tooling/check-conflict-markers.sh` | a .patch file is no longer exempt | `run-source-gate-cases.sh` | seen as another wrong verdict |
| CM6 | `tooling/check-conflict-markers.sh` | a marker need not start the line | `run-source-gate-cases.sh` | seen as another wrong verdict (through the control's baseline step only) |
| PH1 | `tooling/check-proof-hygiene.sh` | the generated files are scanned too | `run-source-gate-cases.sh` | seen as another wrong verdict |
| PH2 | `tooling/check-proof-hygiene.sh` | line comments are not stripped before matching | `run-source-gate-cases.sh` | seen as another wrong verdict |
| PH3 | `tooling/check-proof-hygiene.sh` | the pattern no longer matches the translator's names | `run-source-gate-cases.sh` | seen as accepted |
| PH4 | `tooling/check-proof-hygiene.sh` | a hit is printed nowhere and the check passes | `run-source-gate-cases.sh` | seen as accepted |
| PH5 | `tooling/check-proof-hygiene.sh` | only some hand-written files are scanned | `run-source-gate-cases.sh` | seen as accepted |
| PH6 | `tooling/check-proof-hygiene.sh` | a line with a trailing comment is not read at all | `run-source-gate-cases.sh` | seen as accepted |
| AB1 | `tooling/check_authentication_boundary.py` | a function under #[cfg(test)] is not exempt | `run-source-gate-cases.sh` | seen as another wrong verdict |
| AB3 | `tooling/check_authentication_boundary.py` | discovery stops at the first test module | `run-source-gate-cases.sh` | seen as accepted |
| AB4 | `tooling/check_authentication_boundary.py` | unbalanced braces are not refused | `run-source-gate-cases.sh` | seen as accepted |
| AB5 | `tooling/check_authentication_boundary.py` | a const fn is not a declaration | `run-source-gate-cases.sh` | seen as accepted |
| AB6 | `tooling/check_authentication_boundary.py` | a declaration after a brace on the same line is not discovered | `run-source-gate-cases.sh` | seen as accepted |
| AB7 | `tooling/check_authentication_boundary.py` | the verb parse is not a consuming verb | `run-source-gate-cases.sh` | seen as accepted |
| AB8 | `tooling/check_authentication_boundary.py` | a registered row naming no function is accepted | `run-source-gate-cases.sh` | seen as accepted |
| AB9 | `tooling/check_authentication_boundary.py` | a row under the wrong shape is accepted | `run-source-gate-cases.sh` | seen as accepted |
| AB10 | `tooling/check_authentication_boundary.py` | two rows for one function are accepted | `run-source-gate-cases.sh` | seen as accepted |
| AB11 | `tooling/check_authentication_boundary.py` | the problems found are not a failure | `run-source-gate-cases.sh` | seen as accepted |
| AB12 | `tooling/check_authentication_boundary.py` | a function declared twice in one file is accepted | `run-source-gate-cases.sh` | seen as accepted |
| NS-drop-lifecycle | `tacenta-proofs/scripts/no-sorry.sh` | the call of check-lifecycle-translation-coverage.py is deleted | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-swallow-lifecycle | `tacenta-proofs/scripts/no-sorry.sh` | the failure of check-lifecycle-translation-coverage.py is swallowed | `run-proof-script-cases.sh` | seen as accepted |
| NS-drop-lifecycle-neg | `tacenta-proofs/scripts/no-sorry.sh` | the call of check-lifecycle-translation-coverage-negatives.sh is deleted | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-swallow-lifecycle-neg | `tacenta-proofs/scripts/no-sorry.sh` | the failure of check-lifecycle-translation-coverage-negatives.sh is swallowed | `run-proof-script-cases.sh` | seen as accepted |
| NS-drop-satisfiability | `tacenta-proofs/scripts/no-sorry.sh` | the call of check-session-satisfiability-negatives.sh is deleted | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-swallow-satisfiability | `tacenta-proofs/scripts/no-sorry.sh` | the failure of check-session-satisfiability-negatives.sh is swallowed | `run-proof-script-cases.sh` | seen as accepted |
| NS-drop-port-neg | `tacenta-proofs/scripts/no-sorry.sh` | the call of check-port-negatives.sh is deleted | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-swallow-port-neg | `tacenta-proofs/scripts/no-sorry.sh` | the failure of check-port-negatives.sh is swallowed | `run-proof-script-cases.sh` | seen as accepted |
| NS-drop-dispatch-neg | `tacenta-proofs/scripts/no-sorry.sh` | the call of check-initial-dispatch-negatives.py is deleted | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-swallow-dispatch-neg | `tacenta-proofs/scripts/no-sorry.sh` | the failure of check-initial-dispatch-negatives.py is swallowed | `run-proof-script-cases.sh` | seen as accepted |
| NS-drop-compare-audit | `tacenta-proofs/scripts/no-sorry.sh` | the call of attest.py is deleted | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-swallow-compare-audit | `tacenta-proofs/scripts/no-sorry.sh` | the failure of attest.py is swallowed | `run-proof-script-cases.sh` | seen as accepted |
| NS-drop-constructs | `tacenta-proofs/scripts/no-sorry.sh` | the call of check-lean-constructs.sh is deleted | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-swallow-constructs | `tacenta-proofs/scripts/no-sorry.sh` | the failure of check-lean-constructs.sh is swallowed | `run-proof-script-cases.sh` | seen as accepted |
| NS-drop-audit-reach | `tacenta-proofs/scripts/no-sorry.sh` | the call of check-audit-reach.sh is deleted | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-swallow-audit-reach | `tacenta-proofs/scripts/no-sorry.sh` | the failure of check-audit-reach.sh is swallowed | `run-proof-script-cases.sh` | seen as accepted |
| NS-drop-audit-neg | `tacenta-proofs/scripts/no-sorry.sh` | the call of check-audit-negatives.sh is deleted | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-swallow-audit-neg | `tacenta-proofs/scripts/no-sorry.sh` | the failure of check-audit-negatives.sh is swallowed | `run-proof-script-cases.sh` | seen as accepted |
| NS-scan-ours | `tacenta-proofs/scripts/no-sorry.sh` | the log scan matches no first-party path | `run-proof-script-cases.sh` | seen as accepted |
| NS-scan-verdict | `tacenta-proofs/scripts/no-sorry.sh` | an incomplete declaration found in the log is not a failure | `run-proof-script-cases.sh` | seen as accepted |
| NS-regex-translation | `tacenta-proofs/scripts/no-sorry.sh` | a dependency path that contains Translation/ is read as ours | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-regex-proofs | `tacenta-proofs/scripts/no-sorry.sh` | the proofs package's own path is not read as ours | `run-proof-script-cases.sh` | seen as accepted |
| NS-regex-properties | `tacenta-proofs/scripts/no-sorry.sh` | the property theorems' path is not read as ours | `run-proof-script-cases.sh` | seen as accepted |
| NS-build-failure | `tacenta-proofs/scripts/no-sorry.sh` | a failing build does not stop the script | `run-proof-script-cases.sh` | seen as accepted |
| NS-audit-lines-guard | `tacenta-proofs/scripts/no-sorry.sh` | a build log with no audit lines is compared as if it had them | `run-proof-script-cases.sh` | seen as accepted |
| NS-audit-lines-verdict | `tacenta-proofs/scripts/no-sorry.sh` | a build log with no audit lines is reported and not failed | `run-proof-script-cases.sh` | seen as accepted |
| NS-replay-verdict | `tacenta-proofs/scripts/no-sorry.sh` | a module the kernel refuses is not a failure | `run-proof-script-cases.sh` | seen as accepted |
| NS-replay-swallow | `tacenta-proofs/scripts/no-sorry.sh` | the replay's own failure is not collected | `run-proof-script-cases.sh` | seen as accepted |
| NS-replay-properties | `tacenta-proofs/scripts/no-sorry.sh` | the property theorems are not replayed | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-replay-proofs | `tacenta-proofs/scripts/no-sorry.sh` | the model-layer proofs are not replayed | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-exit | `tacenta-proofs/scripts/no-sorry.sh` | the script exits zero whatever it found | `run-proof-script-cases.sh` | seen as accepted |
| VF-sorry | `tacenta-proofs/scripts/verify.sh` | verify.sh does not search for sorry | `run-proof-script-cases.sh` | seen as accepted |
| VF-admit | `tacenta-proofs/scripts/verify.sh` | verify.sh does not search for admit | `run-proof-script-cases.sh` | seen as accepted |
| VF-exit | `tacenta-proofs/scripts/verify.sh` | verify.sh reports a sorry and exits zero | `run-proof-script-cases.sh` | seen as accepted |
| VF-build | `tacenta-proofs/scripts/verify.sh` | verify.sh goes on after a failed build | `run-proof-script-cases.sh` | seen as accepted |
| VF-scope | `tacenta-proofs/scripts/verify.sh` | verify.sh searches a directory that is not the proofs | `run-proof-script-cases.sh` | seen as accepted |
| TC-olean | `tacenta-proofs/scripts/check-translation-coverage.sh` | a translation module with no olean is not a failure | `run-proof-script-cases.sh` | seen as accepted |
| TC-glob | `tacenta-proofs/scripts/check-translation-coverage.sh` | a narrowed lakefile glob is not a failure | `run-proof-script-cases.sh` | seen as accepted |
| TC-subdir | `tacenta-proofs/scripts/check-translation-coverage.sh` | a module in a subdirectory is not a failure | `run-proof-script-cases.sh` | seen as accepted |
| TC-exit | `tacenta-proofs/scripts/check-translation-coverage.sh` | the script exits zero whatever it found | `run-proof-script-cases.sh` | seen as accepted |
| B5a | `tooling/build-assurance-manifest.py` | an untracked file does not make the tree dirty | `run-build-assurance-manifest-cases.sh` | seen as accepted |
| GN-triple-check | `tacenta-proofs/scripts/assemble-triple-unit.sh` | assemble-triple-unit.sh --check accepts a unit that differs | `check-generation-negatives.sh` | seen as accepted |
| GN-braid-check | `tacenta-proofs/scripts/assemble-braid-unit.sh` | assemble-braid-unit.sh --check accepts a unit that differs | `check-generation-negatives.sh` | seen as accepted |
| GN-session-left | `tacenta-proofs/scripts/assemble-session-unit.sh` | assemble-session-unit.sh --check ignores a file only the committed unit has | `check-generation-negatives.sh` | seen as accepted |
| GN-session-right | `tacenta-proofs/scripts/assemble-session-unit.sh` | assemble-session-unit.sh --check ignores a file only the regenerated unit has | `check-generation-negatives.sh` | seen as accepted |
| GN-session-diff | `tacenta-proofs/scripts/assemble-session-unit.sh` | assemble-session-unit.sh --check ignores a file whose bytes differ | `check-generation-negatives.sh` | seen as accepted |
| GN-session-subdirs | `tacenta-proofs/scripts/assemble-session-unit.sh` | assemble-session-unit.sh --check does not descend into subdirectories | `check-generation-negatives.sh` | seen as accepted |
| GN-port-session-pqxdh-diff | `tacenta-proofs/scripts/port-session-pqxdh-proof.sh` | port-session-pqxdh-proof.sh --check accepts a copy that differs | `check-generation-negatives.sh` | seen as accepted |
| GN-port-session-pqxdh-count | `tacenta-proofs/scripts/port-session-pqxdh-proof.sh` | port-session-pqxdh-proof.sh does not check how often a rewrite target occurs | `check-generation-negatives.sh` | seen as accepted |
| GN-port-session-erasure-diff | `tacenta-proofs/scripts/port-session-erasure-proof.sh` | port-session-erasure-proof.sh --check accepts a copy that differs | `check-generation-negatives.sh` | seen as accepted |
| GN-port-session-erasure-count | `tacenta-proofs/scripts/port-session-erasure-proof.sh` | port-session-erasure-proof.sh does not check how often a rewrite target occurs | `check-generation-negatives.sh` | seen as accepted |
| GN-port-session-braid-diff | `tacenta-proofs/scripts/port-session-braid-proof.sh` | port-session-braid-proof.sh --check accepts a copy that differs | `check-generation-negatives.sh` | seen as accepted |
| GN-port-session-braid-count | `tacenta-proofs/scripts/port-session-braid-proof.sh` | port-session-braid-proof.sh does not check how often a rewrite target occurs | `check-generation-negatives.sh` | seen as accepted |
| GN-port-session-braid-refinement-diff | `tacenta-proofs/scripts/port-session-braid-refinement.sh` | port-session-braid-refinement.sh --check accepts a copy that differs | `check-generation-negatives.sh` | seen as accepted |
| GN-port-session-braid-refinement-count | `tacenta-proofs/scripts/port-session-braid-refinement.sh` | port-session-braid-refinement.sh does not check how often a rewrite target occurs | `check-generation-negatives.sh` | seen as accepted |
| GN-port-session-ratchet-import-diff | `tacenta-proofs/scripts/port-session-ratchet-import-proof.sh` | port-session-ratchet-import-proof.sh --check accepts a copy that differs | `check-generation-negatives.sh` | seen as accepted |
| GN-port-session-ratchet-import-count | `tacenta-proofs/scripts/port-session-ratchet-import-proof.sh` | port-session-ratchet-import-proof.sh does not check how often a rewrite target occurs | `check-generation-negatives.sh` | seen as accepted |
| GN-port-session-braid-import-diff | `tacenta-proofs/scripts/port-session-braid-import-proof.sh` | port-session-braid-import-proof.sh --check accepts a copy that differs | `check-generation-negatives.sh` | seen as accepted |
| GN-port-session-braid-import-count | `tacenta-proofs/scripts/port-session-braid-import-proof.sh` | port-session-braid-import-proof.sh does not check how often a rewrite target occurs | `check-generation-negatives.sh` | seen as accepted |
| GN-port-unit-diff | `tacenta-proofs/scripts/port-unit-proofs.sh` | port-unit-proofs.sh --check accepts a copy that differs | `check-generation-negatives.sh` | seen as accepted |
| GN-port-unit-count | `tacenta-proofs/scripts/port-unit-proofs.sh` | port-unit-proofs.sh does not check how often a rewrite pattern matches (its own self-test refuses it) | `check-generation-negatives.sh` | seen as another wrong verdict (through the control's baseline step only) |
| GN-port-session-unit-diff | `tacenta-proofs/scripts/port-session-unit-proofs.sh` | port-session-unit-proofs.sh --check accepts a copy that differs | `check-generation-negatives.sh` | seen as accepted |
| GN-port-session-unit-count | `tacenta-proofs/scripts/port-session-unit-proofs.sh` | port-session-unit-proofs.sh does not check how often a rewrite target occurs | `check-generation-negatives.sh` | seen as accepted |
| AR-orphan | `tacenta-proofs/scripts/check-audit-reach.sh` | an unreached module is not a failure | `check-audit-reach-negatives.sh` | seen as accepted |
| AR-prefixes | `tacenta-proofs/scripts/check-audit-reach.sh` | an audit with other prefixes is accepted | `check-audit-reach-negatives.sh` | seen as accepted |
| AR-mentions | `tacenta-proofs/scripts/check-audit-reach.sh` | an audit call in another form is not refused | `check-audit-reach-negatives.sh` | seen as accepted |
| AR-one-call | `tacenta-proofs/scripts/check-audit-reach.sh` | an audit module with no call or two calls is accepted | `check-audit-reach-negatives.sh` | seen as accepted |
| AR-exit | `tacenta-proofs/scripts/check-audit-reach.sh` | the script exits zero whatever it found | `check-audit-reach-negatives.sh` | seen as accepted |
| AR-imports | `tacenta-proofs/scripts/check-audit-reach.sh` | imports are not followed, so nothing is reached | `check-audit-reach-negatives.sh` | seen as another wrong verdict (through the control's baseline step only) |
| AR-closure | `tacenta-proofs/scripts/check-audit-reach.sh` | the closure is not followed past the audit modules | `check-audit-reach-negatives.sh` | seen as another wrong verdict (through the control's baseline step only) |
| NS-drop-audit-reach-neg | `tacenta-proofs/scripts/no-sorry.sh` | the call of check-audit-reach-negatives.sh is deleted | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-swallow-audit-reach-neg | `tacenta-proofs/scripts/no-sorry.sh` | the failure of check-audit-reach-negatives.sh is swallowed | `run-proof-script-cases.sh` | seen as accepted |
| IE1 | `tooling/install-elan.sh` | the elan archive is run whatever its digest | `run-install-script-cases.sh` | seen as accepted |
| IE2 | `tooling/install-elan.sh` | elan is never fetched | `run-install-script-cases.sh` | seen as accepted |
| IE3 | `tooling/install-elan.sh` | an elan at the pinned release is fetched again | `run-install-script-cases.sh` | seen as another wrong verdict |
| IE4 | `tooling/install-elan.sh` | the archive is not fetched from the pinned release tag | `run-install-script-cases.sh` | seen as another wrong verdict |
| IE5 | `tooling/install-elan.sh` | the digest is not required | `run-install-script-cases.sh` | seen as accepted |
| IE6 | `tooling/install-elan.sh` | another archive than the pinned one is fetched | `run-install-script-cases.sh` | seen as another wrong verdict |
| AL1 | `tooling/install-actionlint.sh` | the actionlint archive is unpacked whatever its digest | `run-install-script-cases.sh` | seen as accepted |
| AL2 | `tooling/install-actionlint.sh` | an unsupported platform is not a failure | `run-install-script-cases.sh` | seen as accepted |
| SL1 | `tooling/seed-lake-packages.sh` | the dependency is left at the mirror's head, not the pinned revision | `run-install-script-cases.sh` | seen as another wrong verdict |
| SL2 | `tooling/seed-lake-packages.sh` | a present dependency directory is cloned over | `run-install-script-cases.sh` | seen as another wrong verdict |
| SL3 | `tooling/seed-lake-packages.sh` | a path dependency is cloned as a git one | `run-install-script-cases.sh` | seen as another wrong verdict |
| DF1 | `tacenta-test-vectors/runners/rust/tests/differential.rs` | CI no longer requires the model executable | `run-differential-required-input-cases.sh` | seen as accepted |
| DF2 | `tacenta-test-vectors/runners/rust/tests/differential.rs` | the required variable no longer requires the model executable | `run-differential-required-input-cases.sh` | seen as accepted |
| DF3 | `tacenta-test-vectors/runners/rust/tests/differential.rs` | a path that is not a file counts as the executable | `run-differential-required-input-cases.sh` | seen as another wrong verdict |
| VC1 | `tooling/check-vectors-current.sh` | a vector that differs from the model's output is not a failure | `run-check-vectors-current-cases.sh` | seen as accepted |
| VC2 | `tooling/check-vectors-current.sh` | git status looks at a directory that holds no vector | `run-check-vectors-current-cases.sh` | seen as accepted |
| VC3 | `tooling/check-vectors-current.sh` | the vectors are not regenerated | `run-check-vectors-current-cases.sh` | seen as accepted |
| NS-drop-pin-neg | `tacenta-proofs/scripts/no-sorry.sh` | the call of check-pin-negatives.sh is deleted | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-swallow-pin-neg | `tacenta-proofs/scripts/no-sorry.sh` | the failure of check-pin-negatives.sh is swallowed | `run-proof-script-cases.sh` | seen as accepted |
| NS-drop-kernel-replay-neg | `tacenta-proofs/scripts/no-sorry.sh` | the call of check-kernel-replay-negative.sh is deleted | `run-proof-script-cases.sh` | seen as another wrong verdict |
| NS-swallow-kernel-replay-neg | `tacenta-proofs/scripts/no-sorry.sh` | the failure of check-kernel-replay-negative.sh is swallowed | `run-proof-script-cases.sh` | seen as accepted |
| AL-labels-verdict | `tooling/check-labels.sh` | the label check ignores what its parts found | `run-check-labels-cases.sh` | seen as accepted |
| AL-labels-prefix | `tooling/check-labels.sh` | a label that is a prefix of another is accepted | `run-check-labels-cases.sh` | seen as accepted |
| AL-labels-dupes | `tooling/check-labels.sh` | two constants with one label value are accepted | `run-check-labels-cases.sh` | seen as accepted |
| AL-traceability | `tooling/check-traceability.py` | the traceability check always exits zero | `run-check-traceability-cases.sh` | seen as accepted |
| AL-precondition | `tooling/check-precondition-shapes.py` | the precondition-shape check always exits zero | `run-check-precondition-shapes-cases.sh` | seen as accepted |
| AL-boundary-surface | `tooling/check-lifecycle-boundary-surface.py` | the boundary-surface check always exits zero | `run-check-lifecycle-boundary-surface-cases.sh` | seen as accepted |
| AL-vectors | `tooling/check-vectors.py` | the vector schema check always exits zero | `run-check-vectors-cases.sh` | seen as accepted |
| AL-op-traces | `tooling/check-session-operation-traces.py` | the operation-trace check always exits zero | `run-check-session-operation-traces-cases.sh` | seen as accepted |
| AL-ledger-receipt | `tooling/check-ledger-review-receipt.py` | the review-receipt check always exits zero | `run-check-ledger-review-receipt-cases.sh` | seen as accepted |
| AL-evidence-pack | `tooling/build-evidence-pack.py` | the evidence-pack builder and verifier always exit zero | `run-build-evidence-pack-cases.sh` | seen as accepted |
| AL-lifecycle-coverage | `tacenta-proofs/scripts/check-lifecycle-translation-coverage.py` | the lifecycle coverage check always exits zero | `check-lifecycle-translation-coverage-negatives.sh` | seen as accepted |
| PK1 | `tooling/build-evidence-pack.py` | the builder goes on with a manifest that does not validate | `run-build-evidence-pack-build-cases.sh` | seen as accepted |
| PK2 | `tooling/build-evidence-pack.py` | the builder accepts receipts of another schema version | `run-build-evidence-pack-build-cases.sh` | message only, listed equivalent |
| PK3 | `tooling/build-evidence-pack.py` | the builder accepts receipts for another candidate than the manifest | `run-build-evidence-pack-build-cases.sh` | message only, listed equivalent |
| PK3a | `tooling/build-evidence-pack.py` | the builder compares the tree of the candidate but not its commit | `run-build-evidence-pack-build-cases.sh` | message only, listed equivalent |
| PK3b | `tooling/build-evidence-pack.py` | the builder compares the commit of the candidate but not its tree | `run-build-evidence-pack-build-cases.sh` | message only, listed equivalent |
| PK4 | `tooling/build-evidence-pack.py` | the builder writes into a non-empty output directory | `run-build-evidence-pack-build-cases.sh` | seen as accepted |
| PK5 | `tooling/build-evidence-pack.py` | the builder does not compare the manifest's checks with the receipts | `run-build-evidence-pack-build-cases.sh` | seen as accepted |
| PN1 | `tacenta-proofs/translation/Translation/UnitPins.lean` | an axiom pin is weakened with (drop info), which Lean refuses against the docstring | `check-pin-negatives.sh` | seen as another wrong verdict (through the control's baseline step only) |
| PN2 | `tacenta-proofs/translation/Translation/UnitSatisfiabilityRecords.lean` | a statement pin is weakened with (drop info), which Lean refuses against the docstring | `check-pin-negatives.sh` | seen as another wrong verdict (through the control's baseline step only) |
| S6 | `tooling/check-signoff.sh` | any trailer that carries the author's string counts as a sign-off | `run-check-signoff-cases.sh` | seen as accepted |
| S7 | `tooling/check-signoff.sh` | the committer, not the author, must have signed off | `run-check-signoff-cases.sh` | seen as accepted |
| S8 | `tooling/check-signoff.sh` | a merge hides the commits it brings in | `run-check-signoff-cases.sh` | seen as accepted |
| CT12 | `tooling/check-constant-time-asm.sh` | some x86 conditional jumps are not branches | `run-check-constant-time-asm-cases.sh` | seen as another wrong verdict |
| CT13 | `tooling/check-constant-time-asm.sh` | only three aarch64 conditions are branches | `run-check-constant-time-asm-cases.sh` | seen as another wrong verdict |
| CT14 | `tooling/check-constant-time-asm.sh` | an x86 lea counts as a load | `run-check-constant-time-asm-cases.sh` | seen as another wrong verdict |
| CT15 | `tooling/check-constant-time-asm.sh` | aarch64 pair and unscaled loads are not loads | `run-check-constant-time-asm-cases.sh` | seen as another wrong verdict |
| CT16 | `tooling/check-constant-time-asm.sh` | subtle::black_box is refused with the other subtle callees | `run-check-constant-time-asm-cases.sh` | seen as another wrong verdict |
| CM7 | `tooling/check-conflict-markers.sh` | the marker check also excludes source files | `run-source-gate-cases.sh` | seen as accepted |
| CM8 | `tooling/check-conflict-markers.sh` | the marker check does not go to the repository root | `run-source-gate-cases.sh` | seen as accepted |
| IE7 | `tooling/install-elan.sh` | the elan install does not take the lock | `run-install-script-cases.sh` | seen as another wrong verdict |
| IE8 | `tooling/install-elan.sh` | elan is installed with a default toolchain | `run-install-script-cases.sh` | seen as another wrong verdict |
| IE9 | `tooling/install-elan.sh` | elan is not put on the runner's path | `run-install-script-cases.sh` | seen as another wrong verdict |
| SL4 | `tooling/seed-lake-packages.sh` | a fetched revision is not kept under a named ref | `run-install-script-cases.sh` | seen as another wrong verdict |
| AL3 | `tooling/install-actionlint.sh` | only the first four hex digits of the digest are compared | `run-install-script-cases.sh` | seen as accepted |
| AL4 | `tooling/install-actionlint.sh` | an archive without the executable is not refused as such | `run-install-script-cases.sh` | survived, listed equivalent |
| GA-triple-header | `tacenta-proofs/scripts/assemble-triple-unit.sh` | assemble-triple-unit.sh writes a copy for a leaf with no inner attribute block | `check-generation-negatives.sh` | message only, listed equivalent |
| GA-triple-use | `tacenta-proofs/scripts/assemble-triple-unit.sh` | assemble-triple-unit.sh accepts a copy with the inserted use line twice | `check-generation-negatives.sh` | message only, listed equivalent |
| GA-triple-block | `tacenta-proofs/scripts/assemble-triple-unit.sh` | assemble-triple-unit.sh accepts a copy with the inserted block twice | `check-generation-negatives.sh` | message only, listed equivalent |
| GA-triple-diffq | `tacenta-proofs/scripts/assemble-triple-unit.sh` | assemble-triple-unit.sh does not compare the stripped copy with the leaf | `check-generation-negatives.sh` | survived, listed uncovered |
| GA-triple-late | `tacenta-proofs/scripts/assemble-triple-unit.sh` | assemble-triple-unit.sh does not check where the inserted use landed | `check-generation-negatives.sh` | survived, listed uncovered |
| GA-braid-header | `tacenta-proofs/scripts/assemble-braid-unit.sh` | assemble-braid-unit.sh writes a copy for a leaf with no inner attribute block | `check-generation-negatives.sh` | message only, listed equivalent |
| GA-braid-use | `tacenta-proofs/scripts/assemble-braid-unit.sh` | assemble-braid-unit.sh accepts a copy with the inserted use line twice | `check-generation-negatives.sh` | message only, listed equivalent |
| GA-braid-block | `tacenta-proofs/scripts/assemble-braid-unit.sh` | assemble-braid-unit.sh accepts a copy with the inserted block twice | `check-generation-negatives.sh` | message only, listed equivalent |
| GA-braid-diffq | `tacenta-proofs/scripts/assemble-braid-unit.sh` | assemble-braid-unit.sh does not compare the stripped copy with the leaf | `check-generation-negatives.sh` | survived, listed uncovered |
| GA-braid-late | `tacenta-proofs/scripts/assemble-braid-unit.sh` | assemble-braid-unit.sh does not check where the inserted use landed | `check-generation-negatives.sh` | survived, listed uncovered |
| GA-session-anchor | `tacenta-proofs/scripts/assemble-session-unit.sh` | assemble-session-unit.sh accepts a lifecycle root without its ratchet re-export | `check-generation-negatives.sh` | seen as accepted |
| GA-triple-arg | `tacenta-proofs/scripts/assemble-triple-unit.sh` | assemble-triple-unit.sh accepts an argument it does not know | `check-generation-negatives.sh` | seen as accepted |
| GA-port-unit-arg | `tacenta-proofs/scripts/port-unit-proofs.sh` | port-unit-proofs.sh accepts an argument it does not know | `check-generation-negatives.sh` | seen as accepted |
| GA-port-session-unit-arg | `tacenta-proofs/scripts/port-session-unit-proofs.sh` | port-session-unit-proofs.sh accepts an argument it does not know | `check-generation-negatives.sh` | seen as accepted |
| GN-port-unit-diff-all | `tacenta-proofs/scripts/port-unit-proofs.sh` | port-unit-proofs.sh reports only the first copy that differs | `check-generation-negatives.sh` | seen as another wrong verdict |
