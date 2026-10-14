# Record of the ML-KEM and Braid key-generation replay

Copy this file to `RECORD.md` at the root of your directory and fill it in.
Write plain statements. Where a section does not apply, say so in one line.

## 1. Who

- Name:
- Role or affiliation:
- Dates worked:
- Hours spent, by target (K, B, I, R), as you measured them, with reading time
  reported separately:
- Lines of code you added:

## 2. Declaration

Answer 1, 2, 4 and 5 with yes or no, 3 in words, and add a line where an answer
needs one.

1. I did not write `tacenta-model`, `tacenta-proofs`, `tacenta-core` or the
   reader's maintenance code listed in the reader's `README.md`, Provenance.
2. Before and during this work I did not read any of them or any git history of
   the project.
3. Have you ever read the source of an ML-KEM implementation, and which, and when?
   Free text. The maintainer decides what it means for this run.
4. I did not look for or read the project's dry-run record, which is held.
5. Every line of code I added was written by me. If not, say which part was
   written by a program, and which program.

## 3. What I started from

- The manifest file name and its SHA-256:
- The source revision in the manifest:
- Python version and operating system:
- The baseline: the last lines of `python3
  tacenta-test-vectors/runners/independent/reader/run.py` before any change
  (expected `TOTAL 1027 0 1`):

## 4. Isolation

- Everything I read outside the directory, one line each: what, where it came
  from, why. Write "nothing" if nothing.
- Published standards read, with edition and date (for example FIPS 203, August
  2024), and whether you read a copy or worked from memory.
- Published known-answer vectors used: name, source address, date fetched, size,
  SHA-256. Write "none" if none.
- Any existing ML-KEM implementation you ran as a black-box cross-check: which,
  which version, how you ran it, and that its source was not read. Write "none"
  if none.
- Anything written outside the directory:

## 5. Results

One row per target in `TARGETS.md`. Status is one of: MATCHED (computed from
the text and equal to the vector), MISMATCH (computed and different, see
section 6), NOT COMPUTABLE FROM THE TEXT (see the gap), DELEGATED (B4 only; not
attempted), NOT ATTEMPTED.

| ID | Status | How it was checked | Evidence (file under `run-output/` or a gap id) |
|---|---|---|---|
| K1 | | | |
| K2 | | | |
| K3 | | | |
| K4 | | | |
| K5 | | | |
| B1 | | | |
| B2 | | | |
| B3 | | | |
| B4 | | | |
| I1 | | | |
| I2 | | | |
| R1 to R4 | | | |

Known-answer check of the KEM against published vectors: which vectors, how
many cases, how many passed.

A control that has no vector (K5) is reported as CHECKED (control, no vector), and
a self-check with no vector comparison (B3) as MATCHED with the words "self-check".

## 6. Mismatches

For each: the target, the sentence relied on (page, section), expected and
computed values (first 16 bytes and the SHA-256 of the whole), which of the
specification text, the vector or the reading is at fault and why, and every
reading tried. Write "none" if none.

## 7. Gaps

The count by severity in `GAPS-MLKEM.md`: BLOCKING, AMBIGUOUS, MINOR, and
vector gaps. Name the three most important.

## 8. Reader changes

- Files added or changed under `tacenta-test-vectors/runners/independent/reader/`:
- Whether the `honest-initial-message` skip was removed:
- The final output of the three commands (exit status, and for each the line to
  quote: the `TOTAL` line of `run.py`, the one line of `test_skip_allowlist.py`,
  the one sentence of the sweep):
  - `run.py`:
  - `test_skip_allowlist.py`:
  - `test_session_e2e_sweep.py`:
- What the sweep now documents as unchecked:

## 9. Documents made stale

Documents outside the reader (the vectors README, `conformance-manifest.md`, a
specification page) that now say something your work shows to be wrong, or a
count that your work changed. One line each: the file, the passage, and what is
now true. Do not edit them. Write "none" if none.

## 10. Not done

What you did not do, and why.

## 11. Statement

"I wrote the code and the findings above myself, from the text and vectors in
the directory I was given, and the isolation section lists everything else I
read."

Name, date:
