#!/usr/bin/env python3
"""Build a check inventory from GitHub's completed workflow-run API record.

Production use is from the default-branch ``workflow_run`` workflow. It never
executes code or reads receipt JSON from the candidate revision.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import urllib.request
from pathlib import Path

REQUIRED = {
    "rust", "msrv", "armv7", "vectors", "audit", "proofs", "translation",
    "checks", "assurance-receipts",
}
KNOWN = REQUIRED | {"sign-off"}


def fail(message: str) -> None:
    raise ValueError(message)


def api_json(url: str, token: str) -> dict:
    request = urllib.request.Request(
        url,
        headers={
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {token}",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.load(response)


def load(path: Path) -> dict:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        fail(f"fixture {path} must contain an object")
    return value


def validate(run: dict, jobs_document: dict, repository: str, run_id: int,
             head_sha: str, event: str) -> dict:
    if run.get("id") != run_id:
        fail("workflow run id does not match selected run")
    if run.get("name") != "ci":
        fail("selected workflow is not ci")
    if run.get("status") != "completed" or run.get("conclusion") != "success":
        fail("selected ci workflow did not complete successfully")
    if run.get("head_sha") != head_sha:
        fail("workflow run head does not match selected candidate")
    if run.get("event") != event:
        fail("workflow run event does not match selected event")
    repo = run.get("repository")
    if not isinstance(repo, dict) or repo.get("full_name") != repository:
        fail("workflow run repository does not match selected repository")

    jobs = jobs_document.get("jobs")
    if not isinstance(jobs, list):
        fail("jobs response has no jobs list")
    by_name: dict[str, dict] = {}
    for job in jobs:
        if not isinstance(job, dict) or not isinstance(job.get("name"), str):
            fail("jobs response contains an invalid job")
        name = job["name"]
        if name in by_name:
            fail(f"duplicate hosted job {name}")
        by_name[name] = job

    missing = KNOWN - by_name.keys()
    if missing:
        fail("missing hosted jobs: " + ", ".join(sorted(missing)))
    for name in sorted(REQUIRED):
        if by_name[name].get("conclusion") != "success":
            fail(f"hosted job {name} concluded {by_name[name].get('conclusion')!r}")
        if by_name[name].get("head_sha") != head_sha:
            fail(f"hosted job {name} names a different candidate")
    signoff = by_name["sign-off"]
    expected_signoff = "success" if event == "pull_request" else "skipped"
    if signoff.get("conclusion") != expected_signoff:
        fail(f"hosted sign-off job must be {expected_signoff} for {event}")

    selected = []
    for name in sorted(KNOWN):
        job = by_name[name]
        selected.append({
            "id": job.get("id"),
            "name": name,
            "conclusion": job.get("conclusion"),
            "head_sha": job.get("head_sha"),
            "html_url": job.get("html_url"),
            "started_at": job.get("started_at"),
            "completed_at": job.get("completed_at"),
        })
    return {
        "schema_version": 1,
        "source": "github-actions-api",
        "repository": repository,
        "candidate": {"commit": head_sha, "event": event},
        "workflow_run": {
            "id": run_id,
            "workflow_id": run.get("workflow_id"),
            "html_url": run.get("html_url"),
            "conclusion": run.get("conclusion"),
        },
        "jobs": selected,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", required=True)
    parser.add_argument("--run-id", type=int, required=True)
    parser.add_argument("--head-sha", required=True)
    parser.add_argument("--event", choices=("push", "pull_request"), required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--run-file", type=Path)
    parser.add_argument("--jobs-file", type=Path)
    args = parser.parse_args()
    try:
        if bool(args.run_file) != bool(args.jobs_file):
            fail("--run-file and --jobs-file must be supplied together")
        if args.run_file:
            if (os.environ.get("GITHUB_ACTIONS") == "true" and
                    os.environ.get("TACENTA_HOSTED_CONCLUSIONS_FIXTURES") != "1"):
                fail("fixture input is forbidden in GitHub Actions")
            run = load(args.run_file)
            jobs = load(args.jobs_file)
        else:
            token = os.environ.get("GITHUB_TOKEN")
            if not token:
                fail("GITHUB_TOKEN is required for hosted API collection")
            root = os.environ.get("GITHUB_API_URL", "https://api.github.com")
            base = f"{root}/repos/{args.repository}/actions/runs/{args.run_id}"
            run = api_json(base, token)
            jobs = api_json(base + "/jobs?per_page=100", token)
        result = validate(run, jobs, args.repository, args.run_id,
                          args.head_sha, args.event)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        print(f"hosted conclusions: verified {len(result['jobs'])} jobs for {args.head_sha}")
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"hosted conclusions: ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
