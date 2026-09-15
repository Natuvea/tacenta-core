#!/usr/bin/env python3
"""Export the specification-only packet for the P6 operation reader.

The packet deliberately contains no implementation, model, proof, Rust-runner
or repository-history path. Its manifest records every included file's digest,
so the independent author can name the exact input revision they read.
"""
from __future__ import annotations

import hashlib
import json
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FILES = [
    "tacenta-spec/README.md",
    "tacenta-spec/CONSTANTS.md",
    "tacenta-spec/protocol/session-establishment.md",
    "tacenta-spec/protocol/key-registration.md",
    "tacenta-spec/protocol/key-deletion.md",
    "tacenta-spec/protocol/message-format.md",
    "tacenta-spec/protocol/error-handling.md",
    "tacenta-spec/protocol/ratchet.md",
    "tacenta-spec/protocol/triple-ratchet.md",
    "tacenta-spec/protocol/sparse-pq-ratchet.md",
    "tacenta-spec/protocol/mlkem-braid.md",
    "tacenta-spec/protocol/session-persistence.md",
    "tacenta-test-vectors/README.md",
    "tacenta-test-vectors/conformance-manifest.md",
    "tacenta-test-vectors/session-operation-trace.md",
    "tacenta-test-vectors/schema/vector.schema.json",
    "tacenta-test-vectors/schema/ratchet-vector.schema.json",
    "tacenta-test-vectors/schema/session-operation-trace.schema.json",
    "tacenta-test-vectors/traces/session-operation-trace.json",
]

for directory in ("tacenta-test-vectors/vectors",):
    FILES.extend(str(p.relative_to(ROOT)) for p in sorted((ROOT / directory).rglob("*.json")))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {Path(sys.argv[0]).name} OUTPUT_DIRECTORY", file=sys.stderr)
        return 2
    destination = Path(sys.argv[1]).resolve()
    if destination.exists() and any(destination.iterdir()):
        print("refusing non-empty output directory", file=sys.stderr)
        return 2
    destination.mkdir(parents=True, exist_ok=True)
    manifest = []
    for relative in FILES:
        source = ROOT / relative
        if not source.is_file():
            print(f"missing allowed input {relative}", file=sys.stderr)
            return 1
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        manifest.append({"path": relative, "sha256": digest(source), "bytes": source.stat().st_size})
    (destination / "PACKET-MANIFEST.json").write_text(
        json.dumps({"schema_version": 1, "files": manifest}, indent=2, sort_keys=True) + "\n"
    )
    print(f"operation-reader packet: {len(manifest)} allowlisted files at {destination}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
