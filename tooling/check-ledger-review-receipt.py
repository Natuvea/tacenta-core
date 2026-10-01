#!/usr/bin/env python3
"""Validate the structure and evidence-pack binding of a P9 review receipt (schema 2).

The receipt records a reader's findings on one frozen candidate's claims ledger.
This checks what a program can: that the receipt binds the evidence pack
manifest, that every section of the pack's `CLAIMS.md` has exactly one
disposition and each was given on the text the pack holds (a digest of the
section), that the artifacts the gate's record lists were named, and that the
fields are well formed. A change to a section of `CLAIMS.md` after a
disposition was recorded makes the digest disagree, which is what reopens the
review for that section.

It cannot determine whether a human review was independent, whether the reader
read what the receipt says, or whether a disposition is correct. It does not
treat a receipt as a gate pass either: with `--require-no-findings` it refuses
a receipt that records a `finding`, which is what a reviewed candidate needs.

Receipt fields: `schema_version` (2), `candidate` (commit, tree), `evidence_pack`
(`manifest_sha256`), `reviewer` (`identity`, `independence_statement`),
`artifacts_read` (strings naming at least the artifacts in `REQUIRED_ARTIFACTS`),
`claims` (one `{reference, disposition, finding, section_sha256}` per section),
and optionally `cross_cutting_notes` (strings). `tooling/ledger-review-sections.py
--template` writes a receipt with the references and digests filled in.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

SCHEMA_VERSION = 2
TOP_LEVEL = {"schema_version", "candidate", "evidence_pack", "reviewer", "artifacts_read", "claims"}
OPTIONAL_TOP_LEVEL = {"cross_cutting_notes"}
CLAIM_FIELDS = {"reference", "disposition", "finding", "section_sha256"}
DISPOSITIONS = {"accepted", "accepted-with-limit", "finding"}
# The artifacts the human-review record in P9-GATE-EVIDENCE.md lists as read.
# A receipt names each by its file name (a path or a sentence containing it is
# enough); naming one proves nothing about reading it.
REQUIRED_ARTIFACTS = [
    "CLAIMS.md", "LIMITATIONS.md", "verification-manifest.json", "evidence-index.json", "ASSURANCE.md",
    "ASSURANCE-OBLIGATIONS.md", "GAP-REGISTER.md", "P6-L2-TARGET-DECISION.md",
    "PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md",
]
CLAIMS_IN_PACK = "source/tacenta-proofs/CLAIMS.md"
INTRODUCTION = "Introduction (the text before the first section)"
SECTION_HEADING = re.compile(r"^## (.+)$", re.M)
PLACEHOLDER = "REPLACE_WITH"
SHA256 = re.compile(r"[0-9a-f]{64}")


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


def claim_sections(text: str) -> dict[str, str]:
    """The ledger's sections by title, each with the SHA-256 of its text.

    A section runs from its `## ` heading to the next one, so its `###`
    sub-sections belong to it. The text before the first heading is the
    introduction, which makes claims too. Two sections with one title are an
    error: a reference could not say which was read.
    """
    sections: dict[str, str] = {}

    def add(title: str, body: str) -> None:
        if title in sections:
            fail(f"CLAIMS.md has two sections titled {title!r}")
        sections[title] = hashlib.sha256(body.encode()).hexdigest()

    matches = list(SECTION_HEADING.finditer(text))
    add(INTRODUCTION, text[: matches[0].start() if matches else len(text)])
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        add(match.group(1).rstrip(), text[match.start():end])
    return sections


def pack_sections(pack: Path, pack_manifest: dict) -> dict[str, str]:
    """The sections of the pack's own copy of CLAIMS.md, which the pack manifest digest covers."""
    entries = [e for e in pack_manifest.get("files", []) if isinstance(e, dict) and e.get("path") == CLAIMS_IN_PACK]
    path = pack / CLAIMS_IN_PACK
    if len(entries) != 1 or not path.is_file():
        fail(f"evidence pack has no {CLAIMS_IN_PACK}")
    if digest(path) != entries[0].get("sha256"):
        fail("evidence pack copy of CLAIMS.md does not match the pack manifest")
    return claim_sections(path.read_text())


def strings_in(value: object):
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for item in value.values():
            yield from strings_in(item)
    elif isinstance(value, list):
        for item in value:
            yield from strings_in(item)


def check_receipt(receipt: dict, pack: Path, pack_manifest: dict, require_no_findings: bool) -> int:
    if receipt.get("schema_version") != SCHEMA_VERSION:
        fail(f"review receipt schema_version must be {SCHEMA_VERSION}")
    unknown = sorted(set(receipt) - TOP_LEVEL - OPTIONAL_TOP_LEVEL)
    missing = sorted(TOP_LEVEL - set(receipt))
    if unknown or missing:
        fail("review receipt fields are wrong"
             + (": missing " + ", ".join(missing) if missing else "") + (": unknown " + ", ".join(unknown) if unknown else ""))
    if any(PLACEHOLDER in text for text in strings_in(receipt)):
        fail("review receipt still holds a template placeholder")
    if receipt.get("candidate") != pack_manifest["candidate"]:
        fail("review receipt candidate does not match evidence pack")
    binding = receipt.get("evidence_pack")
    if not isinstance(binding, dict) or binding.get("manifest_sha256") != digest(pack / "PACK-MANIFEST.json"):
        fail("review receipt does not bind the evidence-pack manifest")
    reviewer = receipt.get("reviewer")
    if not isinstance(reviewer, dict) or not all(
            isinstance(reviewer.get(k), str) and reviewer[k].strip() for k in ("identity", "independence_statement")):
        fail("review receipt lacks reviewer identity or independence statement")
    artifacts = receipt.get("artifacts_read")
    if not isinstance(artifacts, list) or not artifacts or not all(isinstance(item, str) and item for item in artifacts):
        fail("review receipt must list artifacts read")
    unnamed = [name for name in REQUIRED_ARTIFACTS if not any(name in item for item in artifacts)]
    if unnamed:
        fail("review receipt does not name these artifacts read: " + ", ".join(unnamed))
    notes = receipt.get("cross_cutting_notes", [])
    if not isinstance(notes, list) or not all(isinstance(note, str) and note.strip() for note in notes):
        fail("review receipt cross_cutting_notes must be a list of non-empty strings")
    claims = receipt.get("claims")
    if not isinstance(claims, list) or not claims:
        fail("review receipt must contain claim dispositions")
    sections = pack_sections(pack, pack_manifest)
    seen: set[str] = set()
    findings = []
    for claim in claims:
        if not isinstance(claim, dict) or set(claim) != CLAIM_FIELDS:
            fail("review receipt has invalid claim disposition")
        reference = claim["reference"]
        if not isinstance(reference, str) or not reference or reference in seen:
            fail("review receipt has duplicate or invalid claim reference")
        seen.add(reference)
        if claim["disposition"] not in DISPOSITIONS:
            fail(f"review receipt has invalid disposition for {reference}")
        if not isinstance(claim["finding"], str):
            fail(f"review receipt has invalid finding for {reference}")
        if claim["disposition"] != "accepted" and not claim["finding"].strip():
            fail(f"review receipt gives no finding text for {claim['disposition']} on {reference}")
        if claim["disposition"] == "finding":
            findings.append(reference)
        if reference not in sections:
            fail(f"review receipt names a section CLAIMS.md does not have: {reference}")
        if not isinstance(claim["section_sha256"], str) or not SHA256.fullmatch(claim["section_sha256"]):
            fail(f"review receipt has no valid section_sha256 for {reference}")
        if claim["section_sha256"] != sections[reference]:
            fail(f"review receipt disposition for {reference} was not given on the text the pack holds (section_sha256 differs)")
    uncovered = [title for title in sections if title not in seen]
    if uncovered:
        fail(f"review receipt has no disposition for {len(uncovered)} CLAIMS.md section(s): "
             + "; ".join(uncovered[:3]) + ("; ..." if len(uncovered) > 3 else ""))
    if require_no_findings and findings:
        fail(f"review receipt records {len(findings)} finding(s): " + "; ".join(findings[:3]) + ("; ..." if len(findings) > 3 else ""))
    return len(claims)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--require-no-findings", action="store_true")
    args = parser.parse_args()
    try:
        pack_manifest = load(args.pack / "PACK-MANIFEST.json", "pack manifest")
        receipt = load(args.receipt, "review receipt")
        if pack_manifest.get("schema_version") != 1 or not isinstance(pack_manifest.get("candidate"), dict):
            fail("pack manifest has invalid schema or candidate")
        count = check_receipt(receipt, args.pack, pack_manifest, args.require_no_findings)
        print(f"ledger review receipt: {args.receipt} binds {count} claim disposition(s) to the evidence pack")
    except ValueError as exc:
        print(f"ledger review receipt: ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
