#!/usr/bin/env python3
"""Mutation controls for the independent reader's explicit skip gate."""

from run import validate_skip_allowlist


EXPECTED = {"documented-vector"}

unexpected, missing = validate_skip_allowlist(EXPECTED, EXPECTED)
assert not unexpected and not missing, "the exact allowlist must pass"

unexpected, missing = validate_skip_allowlist(EXPECTED | {"new-vector"}, EXPECTED)
assert unexpected == ["new-vector"] and not missing, \
    "an unreviewed skip must fail the gate"

unexpected, missing = validate_skip_allowlist(set(), EXPECTED)
assert not unexpected and missing == ["documented-vector"], \
    "a silently removed or bypassed skip must fail the gate"

print("reader skip allowlist controls: 3 refusal cases gave the expected result")
