#!/usr/bin/env python3
"""Validate that a P9 review receipt, pack and manifest share one candidate."""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def load(path: Path) -> dict:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ValueError(f"{path} must be an object")
    return value


def run(*args: str) -> None:
    completed = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if completed.returncode:
        raise ValueError(completed.stderr.strip() or completed.stdout.strip())


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()
    try:
        run(sys.executable, str(ROOT / "tooling/build-assurance-manifest.py"), "--validate", str(args.manifest))
        run(sys.executable, str(ROOT / "tooling/build-evidence-pack.py"), "--verify", str(args.pack))
        run(sys.executable, str(ROOT / "tooling/check-ledger-review-receipt.py"), "--receipt", str(args.receipt), "--pack", str(args.pack))
        manifest = load(args.manifest)
        pack = load(args.pack / "PACK-MANIFEST.json")
        candidate = {"commit": manifest["identity"]["source_commit"], "tree": manifest["identity"]["source_tree"]}
        if pack.get("candidate") != candidate:
            raise ValueError("evidence pack candidate does not match assurance manifest")
        packed_manifest = args.pack / "assurance-manifest.json"
        if not packed_manifest.is_file() or hashlib.sha256(packed_manifest.read_bytes()).digest() != hashlib.sha256(args.manifest.read_bytes()).digest():
            raise ValueError("evidence pack does not contain the reviewed assurance manifest bytes")
        print("reviewed evidence: manifest, pack and review receipt bind one candidate")
    except (OSError, ValueError, json.JSONDecodeError, KeyError) as exc:
        print(f"reviewed evidence: ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
