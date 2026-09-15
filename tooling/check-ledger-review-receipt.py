#!/usr/bin/env python3
"""Validate the structure and evidence-pack binding of a P9 review receipt.

This checks provenance fields only. It cannot determine whether a human review
was independent or whether its claim dispositions are substantively correct.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path


def fail(message: str) -> None:
    raise ValueError(message)


def load(path: Path, label: str) -> dict:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read {label}: {exc}")
    if not isinstance(value, dict):
        fail(f"{label} must be an object")
    return value


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--pack", type=Path, required=True)
    args = parser.parse_args()
    try:
        pack_path = args.pack / "PACK-MANIFEST.json"
        pack = load(pack_path, "pack manifest")
        receipt = load(args.receipt, "review receipt")
        if pack.get("schema_version") != 1 or not isinstance(pack.get("candidate"), dict):
            fail("pack manifest has invalid schema or candidate")
        if receipt.get("schema_version") != 1:
            fail("review receipt schema_version must be 1")
        if receipt.get("candidate") != pack["candidate"]:
            fail("review receipt candidate does not match evidence pack")
        binding = receipt.get("evidence_pack")
        if not isinstance(binding, dict) or binding.get("manifest_sha256") != digest(pack_path):
            fail("review receipt does not bind the evidence-pack manifest")
        reviewer = receipt.get("reviewer")
        if not isinstance(reviewer, dict) or not all(isinstance(reviewer.get(k), str) and reviewer[k].strip() for k in ("identity", "independence_statement")):
            fail("review receipt lacks reviewer identity or independence statement")
        artifacts = receipt.get("artifacts_read")
        if not isinstance(artifacts, list) or not artifacts or not all(isinstance(item, str) and item for item in artifacts):
            fail("review receipt must list artifacts read")
        claims = receipt.get("claims")
        if not isinstance(claims, list) or not claims:
            fail("review receipt must contain claim dispositions")
        seen = set()
        for claim in claims:
            if not isinstance(claim, dict) or set(claim) != {"reference", "disposition", "finding"}:
                fail("review receipt has invalid claim disposition")
            reference = claim["reference"]
            if not isinstance(reference, str) or not reference or reference in seen:
                fail("review receipt has duplicate or invalid claim reference")
            seen.add(reference)
            if claim["disposition"] not in {"accepted", "accepted-with-limit", "finding"}:
                fail(f"review receipt has invalid disposition for {reference}")
            if not isinstance(claim["finding"], str):
                fail(f"review receipt has invalid finding for {reference}")
        print(f"ledger review receipt: {args.receipt} binds {len(claims)} claim disposition(s) to the evidence pack")
    except ValueError as exc:
        print(f"ledger review receipt: ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
