#!/usr/bin/env python3
"""Mutation controls for the independent reader's real skip gate."""

import contextlib
import io
from collections import OrderedDict

import run


LABEL = "documented-vector"


def invoke(expected, observed):
    """Run ``main`` with a tiny fixture, so the test exercises its exit path."""
    original_expected = run.EXPECTED_SKIPS
    original_vectors = run.run_vectors
    original_negative = run.run_negative

    def fake_vectors(totals):
        run._OBSERVED_SKIPS.clear()
        run._OBSERVED_SKIPS.update(observed)
        totals["fixture"] = OrderedDict(PASS=0, FAIL=0, SKIP=len(observed))

    try:
        run.EXPECTED_SKIPS = set(expected)
        run.run_vectors = fake_vectors
        run.run_negative = lambda totals: None
        with contextlib.redirect_stdout(io.StringIO()):
            return run.main()
    finally:
        run.EXPECTED_SKIPS = original_expected
        run.run_vectors = original_vectors
        run.run_negative = original_negative


if invoke({LABEL}, {LABEL}) != 0:
    raise RuntimeError("the exact allowlist must pass the real reader gate")
if invoke(set(), {LABEL}) == 0:
    raise RuntimeError("an unreviewed skip must fail the real reader gate")
if invoke({LABEL}, set()) == 0:
    raise RuntimeError("a silently removed or bypassed skip must fail the real reader gate")

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

print("reader skip allowlist controls: 3 real-gate cases and 5 tally cases gave the expected result")
