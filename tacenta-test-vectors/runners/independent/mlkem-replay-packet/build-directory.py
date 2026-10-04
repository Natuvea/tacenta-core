#!/usr/bin/env python3
"""Build the directory a person works in for the ML-KEM and Braid replay packet.

    python3 build-directory.py OUTPUT_DIRECTORY [MANIFEST_FILE]

The directory holds the specification, the vectors and the existing reader, and
nothing else. It keeps the repository's own layout, so the reader runs in it
unchanged and what the person edits can be copied back file for file:

    tacenta-spec/
    tacenta-test-vectors/README.md
    tacenta-test-vectors/conformance-manifest.md
    tacenta-test-vectors/schema/
    tacenta-test-vectors/vectors/
    tacenta-test-vectors/runners/independent/reader/

Only files git tracks at the current commit are copied, so nothing untracked in
the working tree can reach the directory. The script refuses a working tree
with uncommitted changes under those paths, an output directory that is not
empty or that lies inside a git repository, and any Rust, Lean, Cargo, lake or
git file in the result. The manifest (path, size and SHA-256 of every file,
and the revision) is written next to the directory and not into it, so the
directory stays exactly the three things above. Python standard library only.
"""
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]

ALLOWED = [
    "tacenta-spec",
    "tacenta-test-vectors/README.md",
    "tacenta-test-vectors/conformance-manifest.md",
    "tacenta-test-vectors/schema",
    "tacenta-test-vectors/vectors",
    "tacenta-test-vectors/runners/independent/reader",
]
FORBIDDEN_SUFFIXES = (".rs", ".lean")
FORBIDDEN_NAMES = ("Cargo.toml", "Cargo.lock", "lakefile.lean", "lakefile.toml", "lake-manifest.json")


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(ROOT), *args], check=True, capture_output=True, text=True
    ).stdout


def inside_git_repository(path: Path) -> bool:
    probe = path
    while not probe.exists():
        probe = probe.parent
    result = subprocess.run(
        ["git", "-C", str(probe), "rev-parse", "--is-inside-work-tree"],
        capture_output=True, text=True,
    )
    return result.returncode == 0


def main() -> int:
    if len(sys.argv) not in (2, 3):
        print(f"usage: {Path(sys.argv[0]).name} OUTPUT_DIRECTORY [MANIFEST_FILE]", file=sys.stderr)
        return 2
    out = Path(sys.argv[1]).resolve()
    manifest_path = Path(sys.argv[2]).resolve() if len(sys.argv) == 3 else out.with_name(out.name + ".manifest.json")
    if out.exists() and any(out.iterdir()):
        print(f"refusing a non-empty output directory: {out}", file=sys.stderr)
        return 2
    if inside_git_repository(out) or inside_git_repository(manifest_path.parent):
        print("refusing an output location inside a git repository", file=sys.stderr)
        return 2
    if out in manifest_path.parents or manifest_path == out:
        print("the manifest must be written outside the directory", file=sys.stderr)
        return 2

    dirty = git("status", "--porcelain", "--", *ALLOWED).strip()
    if dirty:
        print("refusing: uncommitted changes under the allowed paths:\n" + dirty, file=sys.stderr)
        return 1
    revision = git("rev-parse", "HEAD").strip()

    tracked = [p for p in git("ls-files", "-z", "--", *ALLOWED).split("\0") if p]
    if not tracked:
        print("no tracked files under the allowed paths", file=sys.stderr)
        return 1
    out.mkdir(parents=True, exist_ok=True)
    files = []
    for relative in sorted(tracked):
        name = Path(relative).name
        if relative.endswith(FORBIDDEN_SUFFIXES) or name in FORBIDDEN_NAMES or ".git" in Path(relative).parts:
            print(f"refusing an implementation, model or git file: {relative}", file=sys.stderr)
            return 1
        source = ROOT / relative
        data = source.read_bytes()
        target = out / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        target.chmod(source.stat().st_mode & 0o777)
        files.append({"path": relative, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()})

    manifest = {"schema_version": 1, "revision": revision, "files": files}
    text = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    manifest_path.write_text(text)
    print(f"{len(files)} files at {out}")
    print(f"revision {revision}")
    print(f"manifest {manifest_path} sha256 {hashlib.sha256(text.encode()).hexdigest()}")

    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    run = subprocess.run(
        [sys.executable, "tacenta-test-vectors/runners/independent/reader/run.py"],
        cwd=out, env=env, capture_output=True, text=True,
    )
    tail = run.stdout.strip().splitlines()[-3:]
    print("baseline run.py, last lines (exit status %d):" % run.returncode)
    for line in tail:
        print("  " + line)
    return 0 if run.returncode == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
