#!/bin/sh
# Superseded. The check this file is named for lives in the private
# verification workflow, as "The committed translation matches the pinned
# toolchain".
#
# The check is "fail if the committed generated files differ from a fresh
# regeneration". It lives in the workflow because regenerating needs Charon and
# Aeneas, the pinned release is linux-x86_64 only, and this script is invoked
# from machines that have neither.
#
# The workflow's form is the stronger one. `git diff --exit-code` over
# `Translation/` after `run-aeneas.sh` catches a generated file edited by hand --
# the case this script is named for -- and also catches a committed generation
# the toolchain would no longer produce, which a hand-edit check alone would
# not.
#
# Kept as a signpost rather than deleted, because the name is referenced from
# `REPRODUCING.md`, and a reader who goes looking should find out where the
# check went rather than that it vanished.
set -eu
echo "check-generated-files: superseded by the drift check in the verification workflow" >&2
echo "check-generated-files: see the comment in this file for why" >&2
exit 0
