#!/usr/bin/env python3
"""Write a post-check CI checkpoint for later assurance aggregation.

The literal ``status: pass`` means only that execution reached this step after
the preceding job steps. The JSON is produced by the candidate workflow and is
not signed or independently derived from the Actions API.
"""
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
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    event = os.environ.get("GITHUB_EVENT_NAME", "local")
    run_id = os.environ.get("GITHUB_RUN_ID", "local")
    attempt = os.environ.get("GITHUB_RUN_ATTEMPT", "1")
    value = {
        "id": args.id,
        "classification": args.classification,
        "applicable": True,
        "status": "pass",
        "command": args.command,
        "environment": {"event": event, "python": os.environ.get("PYTHON_VERSION", "unknown")},
        "run": {"id": run_id, "attempt": attempt, "commit": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}")},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    print(f"assurance receipt: wrote {args.output} for {args.id}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
