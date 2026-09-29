#!/usr/bin/env python3
"""Build or verify an allowlisted, content-addressed candidate evidence pack.

`--verify` checks a pack against itself and against this checkout's lists: the
files are the ones its manifest lists with the digests it gives, the sources
and documents this checkout expects are all there, the manifest and the
receipts name the same candidate and agree with each other, and the receipts
record success for the command steps the workflow runs (from
`tooling/required-steps.json`). It does not show that the candidate commit
exists, that the packed sources are the candidate's files, or that the receipts
were produced by a run of the workflow: a pack is internally consistent, not
authentic. Verify a pack with the tooling of the commit that built it, since
the expected lists come from the checkout that runs the verifier.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import shutil
import subprocess
import sys
from pathlib import Path

from assurance_validation import compare_checks, validate_receipts

ROOT = Path(__file__).resolve().parents[1]

_manifest_spec = importlib.util.spec_from_file_location(
    "tacenta_build_assurance_manifest", ROOT / "tooling/build-assurance-manifest.py"
)
_manifest_module = importlib.util.module_from_spec(_manifest_spec)
assert _manifest_spec.loader is not None
_manifest_spec.loader.exec_module(_manifest_module)
ASSURANCE_SOURCES = _manifest_module.SOURCES

EXTRA = [
    "tacenta-proofs/REPRODUCING.md", "ASSURANCE.md", "ASSURANCE-OBLIGATIONS.md",
    "tacenta-proofs/P9-GATE-EVIDENCE.md", "tacenta-proofs/CLAIMS.md",
    "tacenta-proofs/LIMITATIONS.md", "tooling/assurance-manifest.schema.json",
    "tacenta-test-vectors/session-operation-trace.md",
    "tacenta-test-vectors/schema/session-operation-trace.schema.json",
    "tacenta-test-vectors/traces/session-operation-trace.json",
    "tacenta-test-vectors/runners/independent/P6-OPERATION-READER-EVIDENCE.md",
    "tooling/required-steps.json",
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fail(message: str) -> None:
    raise ValueError(message)


def load(path: Path) -> dict:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read JSON {path}: {exc}")
    if not isinstance(value, dict):
        fail(f"JSON document {path} must be an object")
    return value


def build(manifest_path: Path, receipts_path: Path, output: Path) -> None:
    validated = subprocess.run(
        [sys.executable, str(ROOT / "tooling/build-assurance-manifest.py"), "--validate", str(manifest_path)],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if validated.returncode:
        fail("candidate assurance manifest did not validate: " + validated.stderr.strip())
    manifest = load(manifest_path)
    receipts = load(receipts_path)
    if manifest.get("schema_version") != 1 or receipts.get("schema_version") != 1:
        fail("manifest and receipts must use schema version 1")
    if manifest.get("identity", {}).get("clean_tree") is not True:
        fail("manifest does not assert a clean candidate")
    if manifest.get("identity", {}).get("source_commit") != receipts.get("candidate", {}).get("commit") or manifest.get("identity", {}).get("source_tree") != receipts.get("candidate", {}).get("tree"):
        fail("manifest and receipts name different candidates")
    commit = manifest.get("identity", {}).get("source_commit")
    tree = manifest.get("identity", {}).get("source_tree")
    try:
        manifest_checks = validate_receipts({"schema_version": 1, "candidate": {"commit": commit, "tree": tree}, "checks": manifest.get("checks")}, commit, tree)
        receipt_checks = validate_receipts(receipts, commit, tree)
        compare_checks(manifest_checks, receipt_checks)
    except (TypeError, ValueError) as exc:
        fail("manifest and receipts do not form one complete passing evidence set: " + str(exc))
    if output.exists() and any(output.iterdir()):
        fail(f"refusing non-empty pack output {output}")
    paths = set(EXTRA)
    paths.update(item["path"] for item in manifest.get("sources", []) if isinstance(item, dict) and isinstance(item.get("path"), str))
    sources = []
    for relative in sorted(paths):
        source = ROOT / relative
        if not source.is_file():
            fail(f"allowlisted source is missing: {relative}")
        sources.append((relative, source))
    output.mkdir(parents=True, exist_ok=True)
    entries = []
    for relative, source in sources:
        target = output / "source" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        entries.append({"path": "source/" + relative, "sha256": digest(source), "bytes": source.stat().st_size})
    for name, source in (("assurance-manifest.json", manifest_path), ("assurance-receipts.json", receipts_path)):
        target = output / name
        shutil.copyfile(source, target)
        entries.append({"path": name, "sha256": digest(source), "bytes": source.stat().st_size})
    pack = {"schema_version": 1, "candidate": receipts["candidate"], "files": entries}
    (output / "PACK-MANIFEST.json").write_text(json.dumps(pack, indent=2, sort_keys=True) + "\n")
    print(f"evidence pack: wrote {len(entries)} files to {output}")


def verify(root: Path) -> None:
    pack = load(root / "PACK-MANIFEST.json")
    if pack.get("schema_version") != 1 or not isinstance(pack.get("files"), list):
        fail("invalid pack manifest")
    candidate = pack.get("candidate")
    if not isinstance(candidate, dict) or not all(isinstance(candidate.get(field), str) and candidate[field] for field in ("commit", "tree")):
        fail("pack manifest has invalid candidate")
    seen = set()
    for entry in pack["files"]:
        if not isinstance(entry, dict) or not isinstance(entry.get("path"), str):
            fail("invalid pack file entry")
        relative = Path(entry["path"])
        if relative.is_absolute() or ".." in relative.parts or entry["path"] in seen:
            fail(f"invalid pack file path: {entry['path']}")
        seen.add(entry["path"])
        if not isinstance(entry.get("bytes"), int) or entry["bytes"] < 0 or not isinstance(entry.get("sha256"), str):
            fail(f"invalid pack digest entry: {entry['path']}")
        path = root / relative
        if not path.is_file() or path.stat().st_size != entry.get("bytes") or digest(path) != entry.get("sha256"):
            fail(f"pack digest mismatch: {entry['path']}")
    actual = set()
    for path in root.rglob("*"):
        if path.is_symlink():
            fail(f"pack contains a symlink: {path.relative_to(root)}")
        if path.is_file():
            actual.add(path.relative_to(root).as_posix())
    # A listed file that is absent fails its digest check above, so only
    # files nobody listed remain to find.
    extras = sorted(actual - seen - {"PACK-MANIFEST.json"})
    if extras:
        fail("pack contains unlisted files: " + ", ".join(extras))

    # Structural containment is necessary but not sufficient.  A self-declared
    # one-file pack used to verify successfully, so publication could retain a
    # candidate identity without retaining the evidence that identity was
    # meant to bind.  Re-apply this checkout's list of expected paths and its
    # receipt checks to the packed copies before accepting a standalone
    # archive.  That is a check of the pack against this checkout, not of the
    # pack against the candidate commit.
    required_documents = {"assurance-manifest.json", "assurance-receipts.json"}
    missing_documents = sorted(required_documents - seen)
    if missing_documents:
        fail("pack is missing required evidence documents: " + ", ".join(missing_documents))
    required_sources = {"source/" + relative for relative in set(ASSURANCE_SOURCES) | set(EXTRA)}
    missing_sources = sorted(required_sources - seen)
    if missing_sources:
        fail("pack is missing required source evidence: " + ", ".join(missing_sources))

    manifest = load(root / "assurance-manifest.json")
    receipts = load(root / "assurance-receipts.json")
    identity = manifest.get("identity")
    if not isinstance(identity, dict) or identity.get("clean_tree") is not True:
        fail("packed assurance manifest does not assert a clean candidate")
    candidate_identity = {
        "commit": identity.get("source_commit"),
        "tree": identity.get("source_tree"),
    }
    if candidate_identity != candidate:
        fail("packed assurance manifest candidate does not match pack candidate")
    if receipts.get("candidate") != candidate:
        fail("packed receipts candidate does not match pack candidate")
    try:
        manifest_checks = validate_receipts(
            {"schema_version": 1, "candidate": candidate, "checks": manifest.get("checks")},
            candidate["commit"], candidate["tree"],
        )
        receipt_checks = validate_receipts(receipts, candidate["commit"], candidate["tree"])
        compare_checks(manifest_checks, receipt_checks)
    except (TypeError, ValueError) as exc:
        fail("packed manifest and receipts are not one complete passing evidence set: " + str(exc))

    sources = manifest.get("sources")
    expected_sources = set(ASSURANCE_SOURCES)
    if not isinstance(sources, list) or {
        item.get("path") for item in sources if isinstance(item, dict)
    } != expected_sources or len(sources) != len(expected_sources):
        fail("packed assurance manifest source inventory is incomplete or not repository-owned")
    for item in sources:
        relative = item.get("path") if isinstance(item, dict) else None
        if not isinstance(item, dict) or not isinstance(relative, str) \
                or not isinstance(item.get("sha256"), str) \
                or not isinstance(item.get("bytes"), int):
            fail(f"packed assurance manifest has an invalid source entry: {relative}")
        packed = root / "source" / relative
        if not packed.is_file() or packed.stat().st_size != item["bytes"] \
                or digest(packed) != item["sha256"]:
            fail(f"packed source evidence does not match its manifest entry: {relative}")
    print(f"evidence pack: {root} verified ({len(pack['files'])} files; the expected paths are present, "
          "the digests match and the receipts record success for every command step)")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--receipts", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify", type=Path)
    args = parser.parse_args()
    try:
        if args.verify:
            if args.manifest or args.receipts or args.output:
                fail("--verify cannot be combined with build arguments")
            verify(args.verify)
        else:
            if not (args.manifest and args.receipts and args.output):
                fail("--manifest, --receipts and --output are required")
            build(args.manifest, args.receipts, args.output)
    except ValueError as exc:
        print(f"evidence pack: ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
