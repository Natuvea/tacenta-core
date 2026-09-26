#!/usr/bin/env python3
"""Upload one verified evidence pack to the configured immutable S3 archive."""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BUCKET = "tacenta-core-assurance-evidence-238576302016"


def fail(message: str) -> None:
    raise ValueError(message)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--bucket", default=DEFAULT_BUCKET)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    try:
        verified = subprocess.run([sys.executable, str(ROOT / "tooling/build-evidence-pack.py"), "--verify", str(args.pack)], cwd=ROOT)
        if verified.returncode:
            fail("evidence pack did not verify")
        manifest_path = args.pack / "PACK-MANIFEST.json"
        manifest = json.loads(manifest_path.read_text())
        candidate = manifest.get("candidate", {})
        commit = candidate.get("commit")
        if not isinstance(commit, str) or len(commit) != 40:
            fail("pack manifest has no full candidate commit")
        pack_digest = hashlib.sha256(manifest_path.read_bytes()).hexdigest()
        prefix = f"candidates/{commit}/{pack_digest}"
        listed = [Path(entry["path"]) for entry in manifest.get("files", [])]
        listed.append(Path("PACK-MANIFEST.json"))
        files = []
        for relative in listed:
            path = args.pack / relative
            if path.is_symlink() or not path.is_file():
                fail(f"verified pack entry is not a regular file: {relative}")
            files.append(path)
        files = sorted(files)
        if args.dry_run:
            print(f"archive dry run: s3://{args.bucket}/{prefix}/ ({len(files)} files)")
            return 0
        if args.receipt is None:
            fail("--receipt is required for publication")
        if args.receipt.exists():
            fail(f"refusing to replace publication receipt {args.receipt}")
        uploaded = []
        for path in files:
            key = prefix + "/" + path.relative_to(args.pack).as_posix()
            command = ["aws", "s3api", "put-object", "--bucket", args.bucket, "--key", key,
                       "--body", str(path), "--if-none-match", "*"]
            completed = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            if completed.returncode:
                fail(f"upload refused for {key}: {completed.stderr.strip()}")
            version = json.loads(completed.stdout).get("VersionId")
            if not isinstance(version, str) or not version:
                fail(f"upload returned no version ID for {key}")
            retained = subprocess.run(["aws", "s3api", "get-object-retention", "--bucket", args.bucket,
                                      "--key", key, "--version-id", version], text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            if retained.returncode:
                fail(f"cannot read retention for {key}: {retained.stderr.strip()}")
            retention = json.loads(retained.stdout).get("Retention", {})
            if retention.get("Mode") != "COMPLIANCE" or not isinstance(retention.get("RetainUntilDate"), str):
                fail(f"upload lacks Compliance retention for {key}")
            uploaded.append({"key": key, "version_id": version, "retention": retention})
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps({"schema_version": 1, "bucket": args.bucket,
            "prefix": prefix, "candidate": candidate, "pack_manifest_sha256": pack_digest,
            "objects": uploaded}, indent=2, sort_keys=True) + "\n")
        print(f"archive publication: uploaded {len(files)} files to s3://{args.bucket}/{prefix}/ and wrote {args.receipt}")
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"archive publication: ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
