#!/bin/sh
# Fail if a generated `Translation/Tacenta*.lean` is not the file the last
# recorded generation produced.
#
# The check compares each generated file's SHA-256, the `axiom` names it
# declares, and the hash of the Rust crate it was generated from against
# `manifests/translation-attestation.json`, which is written only by
# `attest.py --refresh-translation` immediately after `run-aeneas.sh` on the
# pinned toolchain. So a generated file edited by hand fails here, a new axiom
# in one fails here, and a Rust change nobody re-translated fails here with a
# message naming the crate.
#
# What it does not check: that the recorded generation was honest. That is
# the drift step in the private verification workflow, and any linux-x86_64
# reader who runs `run-aeneas.sh` and diffs. This script runs anywhere,
# needs only python3, and is the public half of that pair.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
exec python3 "$here/attest.py" --check-translation
