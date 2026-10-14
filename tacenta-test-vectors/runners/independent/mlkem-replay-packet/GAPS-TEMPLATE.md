# Gap report: ML-KEM and Braid key generation

Copy this file to `GAPS-MLKEM.md` at the root of your directory. It is the form
the earlier independent-reader gap reports use. A gap is something the
specification text leaves unsaid or says in a way that allows more than one
reading. A hypothesis that a vector confirms is still a gap.

## What was read

- **Revision read.** The `revision` of the manifest, and the manifest's SHA-256.
- **Baseline.** The totals of `run.py` before any change: pass, fail, skip, for
  vectors and for derived cases. Add the sweep's sentence.
- **Final.** The same after the work, with the exit status of the three commands.
- **Pages read.** Which pages, and which parts of them.
- **Outside material.** The standards and the published vectors, and whether each
  was read from a copy or written from recall.

## Gaps

One block per gap, numbered `GP-01` onward.

### GP-01  SEVERITY  One-line title

- **Where.** The page and section, and any second place that says something
  different.
- **Problem.** What the text says, what it leaves out, and the readings it
  allows.
- **Resolution used.** The reading you used, and what decided it. If a vector
  confirmed it, say so. Add a suggested fix if you have one.

Severity is one of BLOCKING (cannot be implemented from the text without
guessing), AMBIGUOUS (more than one reading, or only a vector decided it) and
MINOR (wording, a pointer, or a value found only in the wrong place).

## Vector gaps

Rules the text states that no vector pins. One line each: the rule, the page, and
what a vector would have to contain.

## Resolved without a gap

The targets that needed nothing the text did not give, and whether each matched on
the first run.
