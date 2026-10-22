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
# It also runs `generate-inventory-vectors.py --check`, the one generator whose files the regeneration does not
# write.
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

# The hosted-inventory files under `vectors/groups/` are not model output (the model has no inventory
# statement), so the regeneration above does not touch them and `git status` cannot see them drift. Their
# generator is a separate implementation of the page; its `--check` regenerates the four files in memory and
# compares them with the committed ones, which is the same question asked of a different oracle. It writes
# nothing, and needs no Lean toolchain.
inventory_out="$(python3 tacenta-test-vectors/generate-inventory-vectors.py --check 2>&1)" || {
  printf '%s\n' "$inventory_out" >&2
  echo "check-vectors-current: the committed inventory vectors are not what generate-inventory-vectors.py produces; run 'python3 tacenta-test-vectors/generate-inventory-vectors.py' and review the diff" >&2
  exit 1
}
echo "check-vectors-current: the committed vectors are what the model generates, and the inventory vectors are what generate-inventory-vectors.py produces"
