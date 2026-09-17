#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
script="$root/tooling/collect-hosted-check-conclusions.py"
sha="$(git -C "$root" rev-parse HEAD)"

python3 - "$work" "$sha" <<'PY'
import json, pathlib, sys
root, sha = pathlib.Path(sys.argv[1]), sys.argv[2]
run = {"id": 42, "name": "ci", "status": "completed", "conclusion": "success",
       "head_sha": sha, "event": "pull_request", "workflow_id": 7,
       "html_url": "https://example.invalid/run/42",
       "repository": {"full_name": "Natuvea/tacenta-core"}}
names = ["rust", "msrv", "armv7", "vectors", "audit", "proofs",
         "translation", "checks", "sign-off", "assurance-receipts"]
jobs = {"jobs": [{"id": i, "name": name, "conclusion": "success",
                  "head_sha": sha, "html_url": f"https://example.invalid/job/{i}",
                  "started_at": "2026-09-17T00:00:00Z",
                  "completed_at": "2026-09-17T00:01:00Z"}
                 for i, name in enumerate(names, 1)]}
(root / "run.json").write_text(json.dumps(run))
(root / "jobs.json").write_text(json.dumps(jobs))
PY

run_case() {
  TACENTA_HOSTED_CONCLUSIONS_FIXTURES=1 python3 "$script" \
    --repository Natuvea/tacenta-core --run-id 42 \
    --head-sha "$sha" --event "$1" --run-file "$work/$2-run.json" \
    --jobs-file "$work/$2-jobs.json" --output "$work/$2-output.json"
}

cp "$work/run.json" "$work/pass-run.json"
cp "$work/jobs.json" "$work/pass-jobs.json"
run_case pull_request pass >/dev/null

set +e
fixture_in_ci="$(GITHUB_ACTIONS=true python3 "$script" \
  --repository Natuvea/tacenta-core --run-id 42 --head-sha "$sha" \
  --event pull_request --run-file "$work/pass-run.json" \
  --jobs-file "$work/pass-jobs.json" --output "$work/forbidden.json" 2>&1)"
fixture_in_ci_rc=$?
set -e
if [ "$fixture_in_ci_rc" -eq 0 ] || ! printf '%s' "$fixture_in_ci" | grep -qF -- 'fixture input is forbidden in GitHub Actions'; then
  echo 'WRONG  fixture-in-ci: production invocation accepted fixture input' >&2
  printf '%s\n' "$fixture_in_ci" >&2
  exit 1
fi

expect_fail() {
  local name="$1" needle="$2" event="${3:-pull_request}" out rc
  set +e
  out="$(run_case "$event" "$name" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ] || ! printf '%s' "$out" | grep -qF -- "$needle"; then
    echo "WRONG  $name: expected refusal containing '$needle'" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
}

python3 - "$work" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
run = json.loads((root / "run.json").read_text())
jobs = json.loads((root / "jobs.json").read_text())

missing = {"jobs": [j for j in jobs["jobs"] if j["name"] != "proofs"]}
(root / "missing-run.json").write_text(json.dumps(run))
(root / "missing-jobs.json").write_text(json.dumps(missing))

failed = json.loads(json.dumps(jobs))
next(j for j in failed["jobs"] if j["name"] == "translation")["conclusion"] = "failure"
(root / "failed-run.json").write_text(json.dumps(run))
(root / "failed-jobs.json").write_text(json.dumps(failed))

wrong_head = json.loads(json.dumps(run))
wrong_head["head_sha"] = "0" * 40
(root / "wrong-head-run.json").write_text(json.dumps(wrong_head))
(root / "wrong-head-jobs.json").write_text(json.dumps(jobs))

push = json.loads(json.dumps(run))
push["event"] = "push"
push_jobs = json.loads(json.dumps(jobs))
next(j for j in push_jobs["jobs"] if j["name"] == "sign-off")["conclusion"] = "skipped"
(root / "push-run.json").write_text(json.dumps(push))
(root / "push-jobs.json").write_text(json.dumps(push_jobs))
PY

expect_fail missing 'missing hosted jobs: proofs'
expect_fail failed "hosted job translation concluded 'failure'"
expect_fail wrong-head 'workflow run head does not match selected candidate'
run_case push push >/dev/null

echo 'collect-hosted-check-conclusions-cases: 2 pass cases and 4 refusals gave the expected result'
