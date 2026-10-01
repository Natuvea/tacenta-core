#!/usr/bin/env python3
"""Rebuild a candidate's assurance manifest and evidence pack from public inputs and compare.

A third party holding a clone of the public repository, the candidate's
`assurance-receipts.json` and (optionally) a pack or the hosted artifact can
check, with no private input and no network access:

* the candidate commit is in the clone and its tree is the one the pack names;
* every source file in the pack is byte-identical to that file at that commit
  (`build-evidence-pack.py --verify --candidate-repo`);
* the manifest, rebuilt by the candidate commit's own `build-assurance-manifest.py`
  from the receipts, is byte-identical to the one in the pack and in the hosted
  artifact; and
* the pack, rebuilt by the candidate commit's own `build-evidence-pack.py` from
  that manifest and those receipts, is byte-identical to the pack.

Modes:

    reproduce-evidence.py --pack PACK [--repo REPO] [--hosted DIR]
    reproduce-evidence.py --hosted DIR [--repo REPO]

`--hosted DIR` holds the two files the CI `assurance-receipts` job uploads
(`assurance-receipts.json`, `assurance-manifest.json`). With `--hosted` alone
the candidate is the one the receipts name, and only the manifest is rebuilt.
REPO defaults to this checkout. The candidate is checked out in a throwaway
detached worktree of REPO, which is removed afterwards.

This runs Python from the candidate commit: that commit's own manifest and pack
builders. Run it only on a commit you would run the repository's other scripts
from, in the environment you would use for them.

What this does not show, and says: the receipts are an input. Nothing here shows
that a run of the workflow wrote them, or that a reviewer was independent. A pack
reproduced here is a deterministic function of the candidate commit and the
receipts, which is what an outsider can check; whether the receipts are the
hosted run's is checked against the run itself.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
# The builders are imported in this process. Without this, a run where bytecode may
# be written leaves `tooling/__pycache__/` in the repository, which the next
# manifest build there reports as a dirty tree.
sys.dont_write_bytecode = True
GIT_OBJECT_ID = re.compile(r"[0-9a-f]{40}")


def fail(message: str) -> None:
    raise ValueError(message)


def load_json(path: Path, label: str) -> dict:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read {label}: {exc}")
    if not isinstance(value, dict):
        fail(f"{label} must be an object")
    return value


def candidate_of(document: dict, label: str) -> dict:
    candidate = document.get("candidate")
    if not isinstance(candidate, dict) or not all(
            isinstance(candidate.get(k), str) and GIT_OBJECT_ID.fullmatch(candidate[k]) for k in ("commit", "tree")):
        fail(f"{label} has no valid candidate commit and tree")
    return candidate


def run(args: list[str], cwd: Path, what: str) -> str:
    completed = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
    if completed.returncode:
        fail(f"{what} failed: " + (completed.stderr.strip() or completed.stdout.strip()))
    return completed.stdout


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tree_files(root: Path) -> dict[str, Path]:
    files = {}
    for path in root.rglob("*"):
        if path.is_symlink():
            fail(f"symlink in {root}: {path.relative_to(root)}")
        if path.is_file():
            files[path.relative_to(root).as_posix()] = path
    return files


def compare_trees(left: Path, right: Path, what: str) -> int:
    a, b = tree_files(left), tree_files(right)
    if set(a) != set(b):
        fail(f"{what}: the rebuilt pack lists different files: "
             + ", ".join(sorted(set(a) ^ set(b))))
    for relative in sorted(a):
        if a[relative].read_bytes() != b[relative].read_bytes():
            fail(f"{what}: the rebuilt pack differs from the given pack in {relative}")
    return len(a)


def load_pack_builder():
    spec = importlib.util.spec_from_file_location("tacenta_pack_builder", ROOT / "tooling/build-evidence-pack.py")
    module = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(ROOT / "tooling"))
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--pack", type=Path)
    parser.add_argument("--hosted", type=Path)
    parser.add_argument("--repo", type=Path, default=ROOT)
    args = parser.parse_args()
    scratch = None
    worktree = None
    try:
        if not args.pack and not args.hosted:
            fail("give --pack, --hosted or both")
        repo = args.repo
        builder = load_pack_builder()
        sources = {}
        if args.pack:
            candidate = candidate_of(load_json(args.pack / "PACK-MANIFEST.json", "pack manifest"), "pack manifest")
            sources["pack"] = (args.pack / "assurance-receipts.json", args.pack / "assurance-manifest.json")
        if args.hosted:
            receipts_path = args.hosted / "assurance-receipts.json"
            manifest_path = args.hosted / "assurance-manifest.json"
            hosted_candidate = candidate_of(load_json(receipts_path, "hosted receipts"), "hosted receipts")
            if args.pack:
                if hosted_candidate != candidate:
                    fail("the hosted artifact names a different candidate than the pack")
                for given, packed in zip((receipts_path, manifest_path), sources["pack"]):
                    if given.read_bytes() != packed.read_bytes():
                        fail(f"the hosted {given.name} is not the one in the pack")
            else:
                candidate = hosted_candidate
                sources["hosted"] = (receipts_path, manifest_path)
        receipts_path, manifest_path = sources["pack" if args.pack else "hosted"]
        if builder.git_output(repo, "cat-file", "-e", candidate["commit"] + "^{commit}") is None:
            fail(f"candidate commit {candidate['commit']} is not in the repository {repo}")
        scratch = Path(tempfile.mkdtemp(prefix="reproduce-evidence-"))
        worktree = scratch / "candidate"
        run(["git", "-C", str(repo), "worktree", "add", "--detach", "--quiet", str(worktree), candidate["commit"]], ROOT,
            f"checking out candidate commit {candidate['commit']} from {repo}")
        head_tree = run(["git", "rev-parse", "HEAD^{tree}"], worktree, "reading the candidate tree").strip()
        if head_tree != candidate["tree"]:
            fail("the candidate tree is not the tree of the candidate commit")
        if args.pack:
            # The pack is checked against the lists of the commit that built it,
            # then against that commit's files. A pack this checkout's own lists
            # would refuse (a source added since) is still checked by its own.
            run([sys.executable, "tooling/build-evidence-pack.py", "--verify", str(args.pack.resolve())], worktree,
                "the candidate's own pack verifier")
            builder.authenticate(args.pack, repo)
        rebuilt_manifest = scratch / "assurance-manifest.json"
        run([sys.executable, "tooling/build-assurance-manifest.py", "--receipts", str(receipts_path.resolve()),
             "--output", str(rebuilt_manifest)], worktree, "the candidate's manifest builder")
        if rebuilt_manifest.read_bytes() != manifest_path.read_bytes():
            fail("the manifest rebuilt from the receipts differs from the given manifest")
        note = f"manifest rebuilt byte-identical (sha256 {sha256(rebuilt_manifest)[:16]})"
        if args.pack:
            rebuilt_pack = scratch / "pack"
            run([sys.executable, "tooling/build-evidence-pack.py", "--manifest", str(rebuilt_manifest),
                 "--receipts", str(receipts_path.resolve()), "--output", str(rebuilt_pack)], worktree,
                "the candidate's pack builder")
            count = compare_trees(args.pack, rebuilt_pack, "pack")
            note += f"; pack rebuilt byte-identical ({count} files)"
        if args.hosted:
            note += "; hosted artifact identical to the rebuilt manifest and the given receipts"
        print(f"reproduce evidence: candidate {candidate['commit']}: {note}. "
              "The receipts were taken as given: this does not show that a workflow run wrote them.")
    except (ValueError, OSError) as exc:
        print(f"reproduce evidence: ERROR: {exc}", file=sys.stderr)
        return 1
    finally:
        if worktree is not None:
            subprocess.run(["git", "-C", str(args.repo), "worktree", "remove", "--force", str(worktree)],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            subprocess.run(["git", "-C", str(args.repo), "worktree", "prune"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if scratch is not None:
            shutil.rmtree(scratch, ignore_errors=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
