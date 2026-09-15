#!/usr/bin/env python3
"""Build or verify an allowlisted, content-addressed candidate evidence pack."""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXTRA = [
    "tacenta-proofs/REPRODUCING.md", "ASSURANCE.md", "ASSURANCE-OBLIGATIONS.md",
    "tacenta-proofs/P9-GATE-EVIDENCE.md", "tacenta-proofs/CLAIMS.md",
    "tacenta-proofs/LIMITATIONS.md", "tooling/assurance-manifest.schema.json",
    "tacenta-test-vectors/session-operation-trace.md",
    "tacenta-test-vectors/schema/session-operation-trace.schema.json",
    "tacenta-test-vectors/traces/session-operation-trace.json",
    "tacenta-test-vectors/runners/independent/P6-OPERATION-READER-EVIDENCE.md",
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
    print(f"evidence pack: {root} verified ({len(pack['files'])} files)")


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
