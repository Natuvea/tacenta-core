#!/usr/bin/env python3
"""Mutation controls for the specification-only, project-controlled reader's real skip gate."""

import contextlib
import io
from collections import OrderedDict

import run


LABEL = "documented-vector"


def invoke(expected, observed, pending=None, output=None):
    """Run ``main`` with a tiny fixture, so the test exercises its exit path.
    ``pending`` replaces PENDING_READER_PASS; ``output`` collects what it prints."""
    original_expected = run.EXPECTED_SKIPS
    original_pending = run.PENDING_READER_PASS
    original_vectors = run.run_vectors
    original_negative = run.run_negative

    def fake_vectors(totals):
        run._OBSERVED_SKIPS.clear()
        run._OBSERVED_SKIPS.update(observed)
        totals["fixture"] = OrderedDict(PASS=0, FAIL=0, SKIP=len(observed))

    buffer = io.StringIO()
    try:
        run.EXPECTED_SKIPS = set(expected)
        run.PENDING_READER_PASS = dict(pending or {})
        run.run_vectors = fake_vectors
        run.run_negative = lambda totals: None
        with contextlib.redirect_stdout(buffer):
            return run.main()
    finally:
        run.EXPECTED_SKIPS = original_expected
        run.PENDING_READER_PASS = original_pending
        run.run_vectors = original_vectors
        run.run_negative = original_negative
        if output is not None:
            output.append(buffer.getvalue())


if invoke({LABEL}, {LABEL}) != 0:
    raise RuntimeError("the exact allowlist must pass the real reader gate")
if invoke(set(), {LABEL}) == 0:
    raise RuntimeError("an unreviewed skip must fail the real reader gate")
if invoke({LABEL}, set()) == 0:
    raise RuntimeError("a silently removed or bypassed skip must fail the real reader gate")
# A skip pending a reader pass is named, with its count, in the run's own output,
# so that a green run cannot be read as having checked it.
printed = []
if invoke({LABEL}, {LABEL}, pending={LABEL: run.PENDING_READER_PASS_REASON}, output=printed) != 0:
    raise RuntimeError("an allowlisted pending skip must pass the real reader gate")
if "SKIP  1 of the 1 skips: " + run.PENDING_READER_PASS_REASON not in printed[0]:
    raise RuntimeError("the run must name how many of its skips await a reader pass")
printed = []
invoke({LABEL}, {LABEL}, output=printed)
if "skips: " in printed[0]:
    raise RuntimeError("a skip not pending a reader pass must not be reported as one")
if not set(run.PENDING_READER_PASS) <= run.EXPECTED_SKIPS:
    raise RuntimeError("every pending label must be on the checked allowlist")
if any(reason != run.PENDING_READER_PASS_REASON for reason in run.PENDING_READER_PASS.values()):
    raise RuntimeError("every pending label must carry the stated reason")

# The documented tally is checked against the run: the sentences the README and
# GAPS-11.md carry must state the numbers the run prints.
README = ("| Vector checks (3 files) | 10 | 10 | 0 | 0 |\n| Derived cases (2 modules) | 5 | 5 | 0 | 0 |\n"
          "| **Total** | 15 | 15 | 0 | 0 |\n**15 PASS, 0 FAIL, 0 SKIP** (10 vector checks and 5 derived cases)")
GAPS = "**15 PASS, 0 FAIL, 0 SKIP**: 10 vector checks (lines that name a vector, in 3 vector files) and 5 derived cases"
if run.documented_tally_problems(README, GAPS, 3, 2, 10, 5, 15):
    raise RuntimeError("a tally that matches the documents must pass")
if not run.documented_tally_problems(README.replace("| 10 | 10 |", "| 9 | 9 |"), GAPS, 3, 2, 10, 5, 15):
    raise RuntimeError("a stale vector count in the README must fail")
if not run.documented_tally_problems(README, GAPS.replace("15 PASS", "14 PASS"), 3, 2, 10, 5, 15):
    raise RuntimeError("a stale total in GAPS-11.md must fail")
if not run.documented_tally_problems(README, GAPS, 4, 2, 10, 5, 15):
    raise RuntimeError("a stale file count must fail")
if run.documented_tally_problems(None, None, 3, 2, 10, 5, 15):
    raise RuntimeError("an absent document is not a stale one")
# An allowlisted skip is a vector check that is neither passed nor failed: the
# tally counts it in the check column and in the SKIP column.
README_SKIP = ("| Vector checks (3 files) | 11 | 10 | 0 | 1 |\n| Derived cases (2 modules) | 5 | 5 | 0 | 0 |\n"
               "| **Total** | 16 | 15 | 0 | 1 |\n**15 PASS, 0 FAIL, 1 SKIP** (11 vector checks and 5 derived cases)")
GAPS_SKIP = "**15 PASS, 0 FAIL, 1 SKIP**: 11 vector checks (lines that name a vector, in 3 vector files) and 5 derived cases"
if run.documented_tally_problems(README_SKIP, GAPS_SKIP, 3, 2, 10, 5, 15, skipped=1):
    raise RuntimeError("a tally that counts an allowlisted skip must pass")
if not run.documented_tally_problems(README, GAPS, 3, 2, 10, 5, 15, skipped=1):
    raise RuntimeError("a tally that leaves out an allowlisted skip must fail")

# Skips pending a reader pass: both documents must name them, with the count.
PENDING_SENTENCE = "1 of the 1 skips are vectors the specification-only reader has not yet read"
if run.documented_tally_problems(README_SKIP + "\n" + PENDING_SENTENCE, GAPS_SKIP + " " + PENDING_SENTENCE,
                                 3, 2, 10, 5, 15, skipped=1, pending=1):
    raise RuntimeError("a tally that names its pending skips must pass")
if not run.documented_tally_problems(README_SKIP, GAPS_SKIP + " " + PENDING_SENTENCE,
                                     3, 2, 10, 5, 15, skipped=1, pending=1):
    raise RuntimeError("a README that does not name its pending skips must fail")
if not run.documented_tally_problems(README_SKIP + "\n" + PENDING_SENTENCE, GAPS_SKIP,
                                     3, 2, 10, 5, 15, skipped=1, pending=1):
    raise RuntimeError("a GAPS-11.md that does not name its pending skips must fail")

print("reader skip allowlist controls: 6 real-gate cases, 2 allowlist checks and 10 tally cases gave the expected result")
