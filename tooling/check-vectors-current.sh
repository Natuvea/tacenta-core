#!/usr/bin/env bash
# Fail unless the committed protocol vectors are what the model generates.
#
#   bash tooling/check-vectors-current.sh
#
# The model is the oracle for the vectors under `tacenta-test-vectors/vectors`: `regenerate-vectors.sh`
# rewrites every file the model produces, and a file that differs from its committed text shows up in
# `git status`. This is that step of the `proofs` job as a script, so that it has a negative control
# (`tooling/tests/run-check-vectors-current-cases.sh`); the `proofs_vectors` step of the workflow runs this script.
#
# What it does not see: a committed vector the model no longer generates stays in the tree, because the
# regeneration overwrites and never deletes.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bash tacenta-test-vectors/regenerate-vectors.sh
vector_status="$(git status --porcelain --untracked-files=all -- tacenta-test-vectors/vectors)"
if [ -n "$vector_status" ]; then
  printf '%s\n' "$vector_status" >&2
  echo "check-vectors-current: the committed vectors are not what the model generates" >&2
  exit 1
fi
echo "check-vectors-current: the committed vectors are what the model generates"
