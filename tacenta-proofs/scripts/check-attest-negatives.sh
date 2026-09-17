#!/usr/bin/env bash
# Hold the claim and source-attestation gate to representative P9 mutations.
#
# `attest.py` is intentionally rooted at its own repository path, so each
# mutation runs in a disposable detached worktree instead of changing the
# caller's tree.  The expected diagnostic is part of every case: a nonzero
# exit alone could be caused by an unrelated stale manifest.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
worktrees=()

cleanup() {
  local work
  for work in "${worktrees[@]}"; do
    git -C "$root" worktree remove --force "$work" >/dev/null 2>&1 || rm -rf "$work"
  done
}
trap cleanup EXIT

make_case() {
  work="$(mktemp -d)"
  git -C "$root" worktree add --detach "$work" HEAD >/dev/null
  worktrees+=("$work")
}

expect_fail() {
  local name="$1"
  local expected="$2"
  shift 2
  local out rc
  set +e
  out="$(cd "$work" && python3 tacenta-proofs/scripts/attest.py "$@" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $name: expected refusal containing '$expected', was accepted" >&2
    return 1
  fi
  if [[ "$out" != *"$expected"* ]]; then
    echo "WRONG  $name: refused, but not for '$expected':" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
}

make_case
python3 - "$work/tacenta-proofs/CLAIMS.md" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
path.write_text(path.read_text() + "\n## Proved P9 mutation\n\n**Location:** `tacenta-proofs/Proofs/SessionEstablishment.lean`\n\n- `P9MissingTheorem`: mutation control.\n")
PY
expect_fail "missing-claimed-theorem" 'CLAIMS.md claims `P9MissingTheorem` but no such theorem is declared' --check

make_case
rm "$work/tacenta-proofs/manifests/verification-manifest.json"
expect_fail "missing-verification-manifest" "tacenta-proofs/manifests/verification-manifest.json is missing" --check

make_case
python3 - "$work/tacenta-proofs/manifests/source-commit-attestation.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
data["p9_mutation"] = "stale"
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "stale-source-attestation" "tacenta-proofs/manifests/source-commit-attestation.json is stale" --check

make_case
printf '\n-- P9 mutation --\n' >> "$work/tacenta-proofs/translation/Translation/TacentaRatchet.lean"
expect_fail "edited-generated-translation" "TacentaRatchet.lean differs from the recorded generation" --check-translation

make_case
python3 - "$work/tacenta-proofs/manifests/translation-attestation.json" <<'PY'
import json, pathlib, subprocess, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
# A recorded file and a source hash must come from the same committed source
# tree. Select the oldest commit that contains the sparse source so this test
# remains valid when the branch is rebased or its history is pruned.
commits = subprocess.check_output(
    ["git", "rev-list", "--all", "--", "tacenta-core/spqr/src/lib.rs"],
    text=True,
).splitlines()
if len(commits) < 2:
    raise SystemExit("not enough sparse source history for the pairing control")
data["generated_at_commit"] = commits[-1]
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "false-source-pairing" "manifest cannot pair a generated file with a different source tree" --check-translation

echo "check-attest-negatives: 5 refusal cases gave the expected result"
