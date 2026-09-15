#!/usr/bin/env python3
"""Build or validate the candidate assurance manifest (schema v1).

The manifest is an inventory of supplied, selected check receipts and static
evidence. It never turns a missing job, a dirty candidate or a review-pending
state into a pass. Release publication adds an outer digest over this file.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REQUIRED_CHECKS = {"rust", "msrv", "armv7", "vectors", "audit", "proofs", "translation", "checks"}
ALLOWED_STATUSES = {"pass", "fail", "missing", "skipped", "inconclusive", "not_applicable"}
SOURCES = [
    "ASSURANCE.md", "ASSURANCE-OBLIGATIONS.md", "GAP-REGISTER.md",
    "tacenta-proofs/CLAIMS.md", "tacenta-proofs/LIMITATIONS.md",
    "tacenta-proofs/PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md",
    "tacenta-model/P6-L2-TARGET-DECISION.md",
    "tacenta-proofs/manifests/verification-manifest.json",
    "tacenta-spec/security-properties/evidence-index.json",
    "tacenta-spec/security-properties/INVARIANT-SEMANTIC-REVIEW-BRIEF.md",
    "tacenta-test-vectors/conformance-manifest.md",
    "tacenta-test-vectors/traces/session-operation-trace.json",
    "tacenta-test-vectors/runners/independent/P6-OPERATION-READER-EVIDENCE.md",
    "tacenta-test-vectors/runners/independent/session-operation-reader.py",
    "tooling/check-ledger-review-receipt.py",
    "tooling/validate-reviewed-evidence.py",
    "tooling/publish-evidence-archive.py",
]


def canonical(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def fail(message: str) -> None:
    raise ValueError(message)


def load_receipts(path: Path, commit: str, tree: str) -> list[dict]:
    try:
        data = json.loads(path.read_text())
    except OSError as exc:
        fail(f"cannot read receipts: {exc}")
    except json.JSONDecodeError as exc:
        fail(f"receipts are not JSON: {exc}")
    if data.get("schema_version") != 1:
        fail("receipts schema_version must be 1")
    candidate = data.get("candidate")
    if not isinstance(candidate, dict) or candidate.get("commit") != commit or candidate.get("tree") != tree:
        fail("receipts candidate commit/tree does not match selected source")
    checks = data.get("checks")
    if not isinstance(checks, list):
        fail("receipts checks must be a list")
    ids: set[str] = set()
    for check in checks:
        if not isinstance(check, dict):
            fail("receipt check must be an object")
        for field in ("id", "classification", "applicable", "status", "command", "environment", "run"):
            if field not in check:
                fail(f"receipt check missing {field}")
        cid = check["id"]
        if not isinstance(cid, str) or not cid or cid in ids:
            fail(f"duplicate or invalid check id {cid!r}")
        ids.add(cid)
        if check["classification"] not in {"required", "optional", "conditional"}:
            fail(f"check {cid} has invalid classification")
        if not isinstance(check["applicable"], bool):
            fail(f"check {cid} applicable must be boolean")
        if check["status"] not in ALLOWED_STATUSES:
            fail(f"check {cid} has invalid status")
        if not isinstance(check["command"], str) or not check["command"]:
            fail(f"check {cid} has no command")
        if not isinstance(check["environment"], dict) or not isinstance(check["run"], dict):
            fail(f"check {cid} environment and run must be objects")
        if check["applicable"] and check["classification"] in {"required", "conditional"} and check["status"] != "pass":
            fail(f"required applicable check {cid} is {check['status']}")
        if not check["applicable"] and check["status"] != "not_applicable":
            fail(f"inapplicable check {cid} must be not_applicable")
    missing = REQUIRED_CHECKS - ids
    if missing:
        fail("missing required check receipts: " + ", ".join(sorted(missing)))
    return sorted(checks, key=lambda item: item["id"])


def build(receipts_path: Path, allow_dirty: bool) -> dict:
    dirty = bool(git("status", "--porcelain"))
    if dirty and not allow_dirty:
        fail("candidate working tree is dirty")
    commit = git("rev-parse", "HEAD")
    tree = git("rev-parse", "HEAD^{tree}")
    checks = load_receipts(receipts_path, commit, tree)
    source_inputs = []
    for relative in SOURCES:
        path = ROOT / relative
        if not path.is_file():
            fail(f"required source input is missing: {relative}")
        source_inputs.append({"path": relative, "sha256": sha256(path), "bytes": path.stat().st_size})
    generator = Path(__file__)
    return {
        "schema_version": 1,
        "identity": {
            "repository": "Natuvea/tacenta-core",
            "source_commit": commit,
            "source_tree": tree,
            "clean_tree": not dirty,
            "generator": "tooling/build-assurance-manifest.py",
            "generator_sha256": sha256(generator),
        },
        "sources": source_inputs,
        "checks": checks,
        "review_requirements": [{"type": "independent-ledger-review", "status": "pending"}],
    }


def validate(path: Path) -> None:
    try:
        data = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read manifest: {exc}")
    if data.get("schema_version") != 1:
        fail("manifest schema_version must be 1")
    identity = data.get("identity")
    if not isinstance(identity, dict) or identity.get("clean_tree") is not True:
        fail("manifest does not assert a clean source tree")
    if identity.get("source_commit") != git("rev-parse", "HEAD") or identity.get("source_tree") != git("rev-parse", "HEAD^{tree}"):
        fail("manifest candidate commit/tree does not match selected source")
    for source in data.get("sources", []):
        if not isinstance(source, dict) or not isinstance(source.get("path"), str):
            fail("manifest has invalid source entry")
        path = ROOT / source["path"]
        if not path.is_file() or sha256(path) != source.get("sha256"):
            fail(f"manifest source digest mismatch: {source.get('path')}")
    checks = data.get("checks")
    if not isinstance(checks, list):
        fail("manifest checks must be a list")
    ids = {item.get("id") for item in checks if isinstance(item, dict)}
    if REQUIRED_CHECKS - ids:
        fail("manifest omits required check ids")
    for check in checks:
        if check.get("classification") in {"required", "conditional"} and check.get("applicable") and check.get("status") != "pass":
            fail(f"manifest required check {check.get('id')} is not pass")
    reviews = data.get("review_requirements")
    if not isinstance(reviews, list) or not reviews or reviews[0].get("status") != "pending":
        fail("manifest must retain a pending independent review requirement")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--receipts", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--allow-dirty", action="store_true")
    parser.add_argument("--validate", type=Path)
    args = parser.parse_args()
    try:
        if args.validate:
            if args.receipts or args.output:
                fail("--validate cannot be combined with --receipts or --output")
            validate(args.validate)
            print(f"assurance manifest: {args.validate} is valid")
        else:
            if not args.receipts or not args.output:
                fail("--receipts and --output are required to build")
            args.output.write_bytes(canonical(build(args.receipts, args.allow_dirty)))
            print(f"assurance manifest: wrote {args.output}")
    except ValueError as exc:
        print(f"assurance manifest: ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
