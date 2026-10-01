#!/usr/bin/env python3
"""Make one honest candidate for the evidence case runners, through the production tools.

    make-candidate.py ROOT DEST [--event push|pull_request]

ROOT is the checkout under test. DEST gets:

* `repo/`     a git repository holding that checkout's `tooling/`, the source and
              evidence files the manifest and pack read, and one commit;
* `hosted/`   `assurance-receipts.json` and `assurance-manifest.json`, as the
              `assurance-receipts` job uploads them;
* `pack/`     the evidence pack built from those two files.

Everything is made the way the workflow makes it: the receipt writer in each
job, the collector, the manifest builder and the pack builder, all run from the
new repository so that they name its commit and tree and see a clean tree. The
case runners then change one thing at a time and require a refusal. The
receipts are real writer output with honest outcomes, not fixtures.
"""
from __future__ import annotations

import argparse
import importlib.util
import os
import shutil
import subprocess
import sys
from pathlib import Path


def git(repo: Path, *args: str) -> None:
    subprocess.run(["git", "-c", "user.name=case", "-c", "user.email=case@example.invalid", "-c", "commit.gpgsign=false", *args],
                   cwd=repo, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("dest", type=Path)
    parser.add_argument("--event", choices=("push", "pull_request"), default="push")
    args = parser.parse_args()
    root, dest = args.root.resolve(), args.dest.resolve()
    sys.path.insert(0, str(root / "tooling"))
    os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
    from assurance_validation import REQUIRED_CHECKS, expected_step_outcomes

    manifest_builder = load(root / "tooling/build-assurance-manifest.py", "manifest_builder")
    pack_builder = load(root / "tooling/build-evidence-pack.py", "pack_builder")
    repo = dest / "repo"
    files = set(manifest_builder.SOURCES) | set(pack_builder.EXTRA) | {".gitignore"}
    files |= {"tooling/" + p.name for p in (root / "tooling").iterdir() if p.is_file() and p.suffix in {".py", ".json"}}
    for relative in sorted(files):
        target = repo / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / relative, target)
    git(repo, "init", "-q")
    git(repo, "add", "-A")
    git(repo, "commit", "-q", "-m", "candidate")

    env = {**os.environ, "GITHUB_EVENT_NAME": args.event, "GITHUB_RUN_ID": "control", "GITHUB_RUN_ATTEMPT": "1",
           "PYTHONDONTWRITEBYTECODE": "1"}
    table = expected_step_outcomes()
    receipts = repo / ".assurance" / "receipts"
    receipts.mkdir(parents=True)
    written = [(check_id, "required") for check_id in sorted(REQUIRED_CHECKS)]
    if args.event == "pull_request":
        written.append(("sign-off", "conditional"))
    for check_id, classification in written:
        outcomes = ",".join(f"{step}=success" for step in table[(check_id, args.event)])
        subprocess.run([sys.executable, "-I", "-B", "tooling/write-assurance-receipt.py", "--id", check_id,
                        "--classification", classification, "--command", f"control-{check_id}",
                        "--required-outcomes", outcomes, "--output", f".assurance/receipts/{check_id}.json"],
                       cwd=repo, env=env, check=True, stdout=subprocess.DEVNULL)
    for command in (
        ["tooling/collect-assurance-receipts.py", "--event", args.event, "--input-dir", ".assurance/receipts",
         "--output", ".assurance/assurance-receipts.json"],
        ["tooling/build-assurance-manifest.py", "--receipts", ".assurance/assurance-receipts.json",
         "--output", ".assurance/assurance-manifest.json"],
        ["tooling/build-assurance-manifest.py", "--validate", ".assurance/assurance-manifest.json"],
    ):
        subprocess.run([sys.executable, "-B", *command], cwd=repo, env=env, check=True, stdout=subprocess.DEVNULL)
    hosted = dest / "hosted"
    hosted.mkdir()
    for name in ("assurance-receipts.json", "assurance-manifest.json"):
        shutil.copyfile(repo / ".assurance" / name, hosted / name)
    subprocess.run([sys.executable, "-B", "tooling/build-evidence-pack.py", "--manifest", str(hosted / "assurance-manifest.json"),
                    "--receipts", str(hosted / "assurance-receipts.json"), "--output", str(dest / "pack")],
                   cwd=repo, env=env, check=True, stdout=subprocess.DEVNULL)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
