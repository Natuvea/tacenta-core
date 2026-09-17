#!/usr/bin/env python3
"""Aggregate selected CI job checkpoints into one assurance-receipts document.

Jobs write one JSON object containing the fields the assurance manifest records.
This collector supplies the selected HEAD commit/tree and the explicit
conditional ``sign-off`` receipt, then refuses duplicate, missing or
cross-candidate job records. It is deterministic: timestamps and run IDs are
inputs in the job receipts, never generated here. These candidate-produced,
unsigned records are an inventory aid, not authenticated evidence of GitHub job
conclusions; the hosted run remains the authority for those conclusions.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REQUIRED = {"rust", "msrv", "armv7", "vectors", "audit", "proofs", "translation", "checks"}
KNOWN = REQUIRED | {"sign-off"}


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def fail(message: str) -> None:
    raise ValueError(message)


def load(path: Path) -> dict:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read receipt {path}: {exc}")
    if not isinstance(value, dict):
        fail(f"receipt {path} must be an object")
    return value


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--event", choices=("push", "pull_request"), required=True)
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        if not args.input_dir.is_dir():
            fail(f"input directory does not exist: {args.input_dir}")
        candidate = {"commit": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}")}
        checks = []
        seen = set()
        for path in sorted(args.input_dir.glob("*.json")):
            check = load(path)
            cid = check.get("id")
            if not isinstance(cid, str) or not cid:
                fail(f"receipt {path} has no check id")
            if cid in seen:
                fail(f"duplicate check receipt {cid}")
            if cid not in KNOWN:
                fail(f"unexpected check receipt {cid}")
            if cid in REQUIRED:
                if check.get("classification") != "required" or check.get("applicable") is not True:
                    fail(f"required receipt {cid} must be an applicable required check")
                if check.get("status") != "pass":
                    fail(f"required receipt {cid} is {check.get('status')!r}, not pass")
            run = check.get("run")
            if not isinstance(run, dict) or run.get("commit") != candidate["commit"] or run.get("tree") != candidate["tree"]:
                fail(f"receipt {cid} was not produced for the selected candidate")
            environment = check.get("environment")
            if not isinstance(environment, dict) or environment.get("event") != args.event:
                fail(f"receipt {cid} event does not match selected event {args.event}")
            seen.add(cid)
            checks.append(check)
        missing = REQUIRED - seen
        if missing:
            fail("missing required check receipts: " + ", ".join(sorted(missing)))
        if args.event == "pull_request":
            if "sign-off" not in seen:
                fail("missing required conditional check receipt: sign-off")
            signoff = next(c for c in checks if c["id"] == "sign-off")
            if signoff.get("classification") != "conditional" or signoff.get("applicable") is not True:
                fail("pull-request sign-off receipt must be an applicable conditional check")
        elif "sign-off" in seen:
            fail("push receipt set must not supply sign-off")
        else:
            checks.append({
                "id": "sign-off", "classification": "conditional",
                "applicable": False, "status": "not_applicable",
                "command": "tooling/check-signoff.sh",
                "environment": {"event": args.event},
                "run": {"selection": "collector"},
            })
        output = {"schema_version": 1, "candidate": candidate, "checks": sorted(checks, key=lambda c: c["id"])}
        args.output.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
        print(f"assurance receipts: wrote {args.output} for {args.event} ({len(checks)} checks)")
    except ValueError as exc:
        print(f"assurance receipts: ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
