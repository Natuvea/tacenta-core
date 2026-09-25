"""Shared fail-closed validation for assurance receipts and manifests."""
from __future__ import annotations

from typing import Any

REQUIRED_CHECKS = {"rust", "msrv", "armv7", "vectors", "audit", "proofs", "translation", "checks"}
ALLOWED_STATUSES = {"pass", "fail", "missing", "skipped", "inconclusive", "not_applicable"}


def validate_receipts(data: Any, commit: str, tree: str) -> list[dict]:
    """Validate the receipt document independently of its supplied labels.

    Required IDs are an owned policy set: a receipt cannot downgrade one by
    changing its classification or applicability.  The returned list is
    canonicalized by ID so callers can compare it with another evidence source.
    """
    if not isinstance(data, dict) or data.get("schema_version") != 1:
        raise ValueError("receipts schema_version must be 1")
    candidate = data.get("candidate")
    if not isinstance(candidate, dict) or candidate.get("commit") != commit or candidate.get("tree") != tree:
        raise ValueError("receipts candidate commit/tree does not match selected source")
    checks = data.get("checks")
    if not isinstance(checks, list):
        raise ValueError("receipts checks must be a list")
    seen: set[str] = set()
    for check in checks:
        if not isinstance(check, dict):
            raise ValueError("receipt check must be an object")
        for field in ("id", "classification", "applicable", "status", "command", "environment", "run"):
            if field not in check:
                raise ValueError(f"receipt check missing {field}")
        cid = check["id"]
        if not isinstance(cid, str) or not cid or cid in seen:
            raise ValueError(f"duplicate or invalid check id {cid!r}")
        seen.add(cid)
        if check["classification"] not in {"required", "optional", "conditional"}:
            raise ValueError(f"check {cid} has invalid classification")
        if not isinstance(check["applicable"], bool):
            raise ValueError(f"check {cid} applicable must be boolean")
        if check["status"] not in ALLOWED_STATUSES:
            raise ValueError(f"check {cid} has invalid status")
        if not isinstance(check["command"], str) or not check["command"]:
            raise ValueError(f"check {cid} has no command")
        if not isinstance(check["environment"], dict) or not isinstance(check["run"], dict):
            raise ValueError(f"check {cid} environment and run must be objects")
        if cid in REQUIRED_CHECKS:
            if check["applicable"] is not True:
                if check["status"] != "not_applicable":
                    raise ValueError(f"inapplicable check {cid} must be not_applicable")
                raise ValueError(f"required receipt {cid} must be an applicable required check")
            if check["classification"] != "required" or check["applicable"] is not True:
                raise ValueError(f"required receipt {cid} must be an applicable required check")
            if check["status"] != "pass":
                raise ValueError(f"required applicable check {cid} is {check['status']}")
            if check["run"].get("commit") != commit or check["run"].get("tree") != tree:
                raise ValueError(f"receipt {cid} was not produced for the selected candidate")
        elif check["applicable"] and check["status"] != "pass":
            raise ValueError(f"applicable non-required check {cid} is {check['status']}")
        elif not check["applicable"] and check["status"] != "not_applicable":
            raise ValueError(f"inapplicable check {cid} must be not_applicable")
    missing = REQUIRED_CHECKS - seen
    if missing:
        raise ValueError("missing required check receipts: " + ", ".join(sorted(missing)))
    return sorted(checks, key=lambda item: item["id"])


def compare_checks(left: list[dict], right: list[dict]) -> None:
    """Reject a pack whose manifest and receipts disagree about any check."""
    by_left = {item.get("id"): item for item in left}
    by_right = {item.get("id"): item for item in right}
    if set(by_left) != set(by_right):
        raise ValueError("manifest and receipts contain different check IDs")
    for cid in sorted(by_left):
        if by_left[cid] != by_right[cid]:
            raise ValueError(f"manifest and receipts disagree for check {cid}")
