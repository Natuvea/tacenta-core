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

from assurance_validation import ALLOWED_STATUSES, REQUIRED_CHECKS, validate_receipts

ROOT = Path(__file__).resolve().parents[1]
SOURCES = [
    "ASSURANCE.md", "ASSURANCE-OBLIGATIONS.md", "GAP-REGISTER.md",
    "tacenta-proofs/CLAIMS.md", "tacenta-proofs/LIMITATIONS.md",
    "tacenta-proofs/PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md",
    "tacenta-model/P6-L2-TARGET-DECISION.md",
    "tacenta-proofs/manifests/verification-manifest.json",
    "tacenta-spec/security-properties/evidence-index.json",
    "tacenta-spec/security-properties/INVARIANT-EVIDENCE-SOURCE-DECISION.md",
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


def working_tree_dirty() -> list[str]:
    """Return dirty paths outside the ephemeral receipt workspace."""
    status = git("status", "--porcelain=v1", "--untracked-files=all", "--ignored=matching")
    dirty: list[str] = []
    for line in status.splitlines():
        # CI downloads and writes receipts below this ignored runtime directory.
        # All tracked source changes and all other untracked paths remain fatal.
        path = line[3:] if len(line) >= 3 else line
        if " -> " in path:
            path = path.split(" -> ", 1)[1]
        if line.startswith("!!") and path.startswith(".assurance/"):
            continue
        dirty.append(path)
    return dirty


def fail(message: str) -> None:
    raise ValueError(message)


def load_receipts(path: Path, commit: str, tree: str) -> list[dict]:
    try:
        data = json.loads(path.read_text())
    except OSError as exc:
        fail(f"cannot read receipts: {exc}")
    except json.JSONDecodeError as exc:
        fail(f"receipts are not JSON: {exc}")
    try:
        return validate_receipts(data, commit, tree)
    except ValueError as exc:
        fail(str(exc))


def build(receipts_path: Path, allow_dirty: bool) -> dict:
    dirty_paths = working_tree_dirty()
    dirty = bool(dirty_paths)
    if dirty and not allow_dirty:
        fail("candidate working tree is dirty: " + ", ".join(dirty_paths))
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
    sources = data.get("sources")
    expected_sources = set(SOURCES)
    source_paths = [item.get("path") if isinstance(item, dict) else None for item in sources] if isinstance(sources, list) else []
    if len(source_paths) != len(expected_sources) or set(source_paths) != expected_sources:
        fail("manifest source inventory does not match the repository-owned source set")
    for source in sources:
        if not isinstance(source, dict) or not isinstance(source.get("path"), str):
            fail("manifest has invalid source entry")
        path = ROOT / source["path"]
        if not isinstance(source.get("sha256"), str) or not isinstance(source.get("bytes"), int):
            fail(f"manifest source entry is incomplete: {source.get('path')}")
        if not path.is_file() or path.stat().st_size != source["bytes"] or sha256(path) != source["sha256"]:
            fail(f"manifest source digest mismatch: {source.get('path')}")
    checks = data.get("checks")
    try:
        validate_receipts({"schema_version": 1, "candidate": {
            "commit": identity["source_commit"], "tree": identity["source_tree"]
        }, "checks": checks}, identity["source_commit"], identity["source_tree"])
    except ValueError as exc:
        fail("manifest checks are not a complete passing receipt set: " + str(exc))
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
