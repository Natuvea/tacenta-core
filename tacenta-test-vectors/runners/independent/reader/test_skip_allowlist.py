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

print("reader skip allowlist controls: 3 real-gate cases gave the expected result")
