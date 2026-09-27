#!/usr/bin/env python3
"""Write one successful CI check receipt for later assurance aggregation."""
from __future__ import annotations

import argparse
import json
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--id", required=True)
    parser.add_argument("--classification", choices=("required", "optional", "conditional"), required=True)
    parser.add_argument("--command", required=True)
    parser.add_argument("--required-outcomes", default="")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    outcomes = {}
    if args.classification == "required" and not args.required_outcomes.strip():
        raise SystemExit("assurance receipt: required checks must assert command step outcomes")
    for item in filter(None, (part.strip() for part in args.required_outcomes.split(","))):
        if "=" not in item:
            raise SystemExit(f"assurance receipt: malformed required outcome {item!r}")
        step_id, outcome = (part.strip() for part in item.split("=", 1))
        if not step_id or outcome not in {"success", "skipped", "failure", "cancelled"}:
            raise SystemExit(f"assurance receipt: invalid required outcome {item!r}")
        if step_id in outcomes:
            raise SystemExit(f"assurance receipt: duplicate required outcome {step_id!r}")
        outcomes[step_id] = outcome
    failed = sorted(step_id for step_id, outcome in outcomes.items() if outcome != "success")
    if failed:
        raise SystemExit("assurance receipt: required command did not succeed: " + ", ".join(failed))
    event = os.environ.get("GITHUB_EVENT_NAME", "local")
    run_id = os.environ.get("GITHUB_RUN_ID", "local")
    attempt = os.environ.get("GITHUB_RUN_ATTEMPT", "1")
    value = {
        "id": args.id,
        "classification": args.classification,
        "applicable": True,
        "status": "pass",
        "command": args.command,
        "step_outcomes": outcomes,
        "environment": {"event": event, "python": os.environ.get("PYTHON_VERSION", "unknown")},
        "run": {"id": run_id, "attempt": attempt, "commit": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}")},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    print(f"assurance receipt: wrote {args.output} for {args.id}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
