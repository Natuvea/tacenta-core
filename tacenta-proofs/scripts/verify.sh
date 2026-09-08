#!/bin/sh
# Reproduce the verification: build the Lean proofs on the pinned toolchain and
# confirm none of them uses sorry. The proofs import the model from
# tacenta-model (a path dependency), so this also builds the model modules they
# rest on.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
cd "$here"

echo "verify: building the Lean proofs on the pinned toolchain"
lake build

echo "verify: checking no proof uses sorry or admit"
if grep -rn --include='*.lean' -e '\bsorry\b' -e '\badmit\b' Proofs; then
  echo "verify: found sorry/admit in Proofs" >&2
  exit 1
fi

echo "verify: proofs built clean"
