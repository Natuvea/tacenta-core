#!/usr/bin/env python3
"""Break the evidence gates one edit at a time and require their case runners to notice.

This is a local control, like `tooling/mutate-inventory.py`: nothing in CI runs
it. It answers one question for the receipt, manifest, evidence-pack and
review-receipt tooling: if this check is removed or weakened, does a case runner
go red? Each entry in `MUTATIONS` replaces one string, which must occur exactly
once, in one tooling file of a throwaway copy of the repository's evidence
tooling, commits the edit there, and runs the case runners named in
`RUNNERS` until one fails. An edit that leaves every runner green is a
SURVIVOR: a check no case holds.

A baseline run of the unedited copy comes first, and the harness stops if it is
not green, because a red baseline would make every edit look caught.

    python3 tooling/mutate-evidence-gates.py            # every mutation
    python3 tooling/mutate-evidence-gates.py --list
    python3 tooling/mutate-evidence-gates.py --only B1 --only V4

It exits 1 if the baseline is red or any mutation survives. The copy holds
`tooling/` and the files the case runners read; it is made from the committed
tree at `HEAD`, so commit your edit first.
"""
from __future__ import annotations

import argparse
import importlib.util
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))

# Runners, in the order they are tried. The first to fail catches the edit.
RUNNERS = [
    "tooling/tests/run-build-assurance-manifest-cases.sh",
    "tooling/tests/run-build-evidence-pack-cases.sh",
    "tooling/tests/run-collect-assurance-receipts-cases.sh",
    "tooling/tests/run-check-ledger-review-receipt-cases.sh",
]

BUILDER = "tooling/build-assurance-manifest.py"
VALIDATION = "tooling/assurance_validation.py"
COLLECTOR = "tooling/collect-assurance-receipts.py"
PACK = "tooling/build-evidence-pack.py"
PUBLISH = "tooling/publish-evidence-archive.py"
REPRODUCE = "tooling/reproduce-evidence.py"

# (id, file, old, new, what the edit does)
MUTATIONS: list[tuple[str, str, str, str, str]] = [
    # The manifest validator: GATE-MUTATION-RECORD rows B1 to B6, one edit each.
    ("B1", BUILDER,
     'if identity.get("source_commit") != git("rev-parse", "HEAD") or identity.get("source_tree") != git("rev-parse", "HEAD^{tree}"):',
     "if False:", "--validate does not compare the manifest identity with HEAD"),
    ("B1c", BUILDER, 'if identity.get("source_commit") != git("rev-parse", "HEAD") or ', "if ",
     "--validate compares the tree with HEAD but not the commit"),
    ("B1t", BUILDER, ' or identity.get("source_tree") != git("rev-parse", "HEAD^{tree}"):', ":",
     "--validate compares the commit with HEAD but not the tree"),
    ("B2", BUILDER, 'if not isinstance(identity, dict) or identity.get("clean_tree") is not True:',
     "if not isinstance(identity, dict):", "--validate does not need clean_tree to be true"),
    ("B3d", BUILDER, ' or sha256(path) != source["sha256"]:', ":", "--validate does not compare a source digest"),
    ("B3s", BUILDER, 'path.stat().st_size != source["bytes"] or ', "", "--validate does not compare a source size"),
    ("B4", BUILDER, "if data.get(\"review_requirements\") != REVIEW_REQUIREMENTS:", "if False:",
     "--validate does not need the pending review requirement"),
    ("B5", BUILDER, "if dirty and not allow_dirty:", "if False:", "the builder accepts a dirty tree without --allow-dirty"),
    ("B6", BUILDER, 'fail("manifest checks are not a complete passing receipt set: " + str(exc))', "pass",
     "--validate does not re-validate the check set"),
    ("T1", BUILDER, "if set(data) != MANIFEST_FIELDS:", "if False:", "--validate allows extra or missing top-level fields"),
    ("T2", BUILDER, "if set(identity) != IDENTITY_FIELDS:", "if False:", "--validate allows extra or missing identity fields"),
    ("T3", BUILDER, 'if identity["repository"] != REPOSITORY:', "if False:", "--validate allows another repository name"),
    ("T4", BUILDER, 'GIT_OBJECT_ID.fullmatch(identity[key])', "True", "--validate allows a short commit or tree"),
    ("T5", BUILDER, 'if identity["generator"] != GENERATOR or identity["generator_sha256"] != sha256(Path(__file__)):',
     "if False:", "--validate does not check which generator wrote the manifest"),
    ("T5d", BUILDER, ' or identity["generator_sha256"] != sha256(Path(__file__)):', ":",
     "--validate checks the generator path but not its digest"),
    ("T6", BUILDER, "or set(source) != SOURCE_FIELDS:", ":", "--validate allows extra fields in a source entry"),
    ("T7", BUILDER, 'if line.startswith("!!") and path.startswith(".assurance/"):', 'if line.startswith("!!"):',
     "an ignored file anywhere makes the tree clean, not only under .assurance/"),
    ("T7b", BUILDER, 'if line.startswith("!!") and path.startswith(".assurance/"):', "if False:",
     "the .assurance/ receipt workspace makes the tree dirty"),
    ("T8", BUILDER, "        dirty.append(path)\n", '        if not line.startswith("??"):\n            dirty.append(path)\n',
     "an untracked file does not make the tree dirty"),
    ("T9", BUILDER, '"--untracked-files=all", "--ignored=matching"], cwd=ROOT, text=True)',
     '"--untracked-files=all"], cwd=ROOT, text=True)', "an ignored file does not make the tree dirty"),
    ("T10", BUILDER, '"--ignored=matching"], cwd=ROOT, text=True)', '"--ignored=matching"], cwd=ROOT, text=True).strip()',
     "the dirty-path report loses the first character of its first path"),
    # The receipt validator and collector: GATE-MUTATION-RECORD rows V1, V2, V3, V4, C2.
    ("V1", VALIDATION, 'if check["run"].get("commit") != commit or check["run"].get("tree") != tree:',
     'if check["run"].get("tree") != tree:', "a receipt for another commit is accepted"),
    ("V2", VALIDATION, 'if check["run"].get("commit") != commit or check["run"].get("tree") != tree:',
     'if check["run"].get("commit") != commit:', "a receipt for another tree is accepted"),
    ("V3", VALIDATION, 'candidate.get("commit") != commit or candidate.get("tree") != tree:',
     'candidate.get("tree") != tree:', "the receipt document may name another commit"),
    ("V4", VALIDATION, 'candidate.get("commit") != commit or candidate.get("tree") != tree:',
     'candidate.get("commit") != commit:', "the receipt document may name another tree"),
    ("C1", COLLECTOR, 'run.get("commit") != candidate["commit"] or run.get("tree") != candidate["tree"]:',
     'run.get("tree") != candidate["tree"]:', "the collector accepts a receipt for another commit"),
    ("C2", COLLECTOR, 'run.get("commit") != candidate["commit"] or run.get("tree") != candidate["tree"]:',
     'run.get("commit") != candidate["commit"]:', "the collector accepts a receipt for another tree"),
    # The pack verifier, its authentication against git, and its command line.
    ("P1", PACK, "    if repo is not None:\n        authenticate(root, repo)\n", "    if False:\n        authenticate(root, repo)\n",
     "--candidate-repo is accepted and ignored"),
    ("P2", PACK, 'if git_output(repo, "cat-file", "-e", candidate["commit"] + "^{commit}") is None:', "if False:",
     "a candidate commit that is not in the repository is not noticed"),
    ("P3", PACK, 'if tree is None or tree.decode().strip() != candidate["tree"]:', "if False:",
     "the pack may name another tree than its commit has"),
    ("P4", PACK, 'if committed != (root / entry["path"]).read_bytes():', "if False:",
     "a packed source need not be the commit's file"),
    ("P5", PACK, "        if committed is None:\n", "        if False:\n",
     "a packed source that is not a file of the commit is not named as such"),
    ("P6", PACK, 'if generator is None or hashlib.sha256(generator).hexdigest() != manifest["identity"].get("generator_sha256"):',
     "if False:", "the manifest's generator digest is not compared with the commit's"),
    ("P7", PACK, 'if not entry["path"].startswith("source/"):', "if True:", "no packed source is compared with git"),
    ("P8", PACK, "GIT_OBJECT_ID.fullmatch(candidate[field])", "True", "a short or non-hex candidate commit or tree is accepted"),
    ("P9", PACK, "            if args.candidate_repo:\n", "            if False:\n", "--candidate-repo is accepted with a build"),
    # The publisher: nothing reaches the COMPLIANCE archive unless these hold.
    ("U1", PUBLISH, "        if verified.returncode:", "        if False:", "an unverified pack is uploaded"),
    ("U2", PUBLISH, '"--verify", str(args.pack),\n                                   "--candidate-repo", str(args.candidate_repo)], cwd=ROOT)',
     '"--verify", str(args.pack)], cwd=ROOT)', "the pack is not authenticated against git before upload"),
    ("U3", PUBLISH, '"--body", str(path), "--if-none-match", "*"]', '"--body", str(path)]', "an upload may replace an existing key"),
    ("U4", PUBLISH, 'if retention.get("Mode") != "COMPLIANCE" or not isinstance(retention.get("RetainUntilDate"), str):',
     "if False:", "an object without Compliance retention is recorded"),
    ("U4m", PUBLISH, 'if retention.get("Mode") != "COMPLIANCE" or ', "if ", "retention in a mode other than COMPLIANCE is accepted"),
    ("U4d", PUBLISH, ' or not isinstance(retention.get("RetainUntilDate"), str):', ":", "retention without an end date is accepted"),
    ("U5", PUBLISH, "if not isinstance(version, str) or not version:", "if False:", "an upload that returns no version ID is recorded"),
    ("U6", PUBLISH, "if args.receipt.exists():", "if False:", "an existing publication receipt is replaced"),
    ("U7", PUBLISH, "if args.receipt is None:", "if False:", "publication without a receipt path"),
    ("U8", PUBLISH, '(path.relative_to(args.pack).as_posix() == "PACK-MANIFEST.json", path)', "(False, path)",
     "the pack manifest is not uploaded last"),
    ("U9", PUBLISH, 'prefix = f"candidates/{commit}/{pack_digest}"', 'prefix = f"candidates/{commit}"',
     "the archive prefix does not carry the pack digest"),
    # The reproduction of a candidate from public inputs.
    ("R1", REPRODUCE, "if hosted_candidate != candidate:", "if False:", "a hosted artifact of another candidate is compared with the pack"),
    ("R2", REPRODUCE, "if given.read_bytes() != packed.read_bytes():", "if False:", "a hosted file need not be the packed one"),
    ("R3", REPRODUCE, 'if head_tree != candidate["tree"]:', "if False:", "the candidate tree is not compared with the commit's"),
    ("R4", REPRODUCE, "if rebuilt_manifest.read_bytes() != manifest_path.read_bytes():", "if False:",
     "the rebuilt manifest need not equal the given one"),
    ("R5", REPRODUCE, "count = compare_trees(args.pack, rebuilt_pack, \"pack\")", "count = 0", "the rebuilt pack is not compared"),
    ("R6", REPRODUCE, "if set(a) != set(b):", "if False:", "the rebuilt pack may list other files"),
    ("R7", REPRODUCE, "if a[relative].read_bytes() != b[relative].read_bytes():", "if False:", "the rebuilt pack may differ in a file"),
    ("R8", REPRODUCE, "        if worktree is not None:\n", "        if False:\n", "a reproduction leaves its worktree in the repository"),
    ("R9", REPRODUCE, '"--verify", str(args.pack.resolve())], worktree,', '"--help"], worktree,',
     "the candidate's own pack verifier is not run"),
    ("R10", REPRODUCE, 'builder.authenticate(args.pack, repo)', "pass", "the pack is not authenticated against git"),
]


def copy_tree(destination: Path) -> None:
    spec = importlib.util.spec_from_file_location("builder", ROOT / BUILDER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    pack_spec = importlib.util.spec_from_file_location("packer", ROOT / "tooling/build-evidence-pack.py")
    pack = importlib.util.module_from_spec(pack_spec)
    pack_spec.loader.exec_module(pack)
    files = set(module.SOURCES) | set(pack.EXTRA) | {".gitignore"}
    tracked = subprocess.check_output(["git", "ls-files", "tooling"], cwd=ROOT, text=True).split()
    files |= set(tracked)
    for relative in sorted(files):
        source = ROOT / relative
        if not source.is_file():
            continue
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        shutil.copymode(source, target)
    git(destination, "init", "-q")
    git(destination, "add", "-A")
    git(destination, "commit", "-q", "-m", "evidence tooling")


def git(directory: Path, *args: str) -> None:
    subprocess.run(["git", "-c", "user.name=mutate", "-c", "user.email=mutate@example.invalid", "-c", "commit.gpgsign=false", *args],
                   cwd=directory, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def run_runners(directory: Path, runners: list[str]) -> tuple[str | None, str]:
    """The first runner that fails and its last lines, or (None, "") if all pass."""
    for runner in runners:
        completed = subprocess.run(["bash", str(directory / runner)], cwd=directory, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=900,
                                   env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
        if completed.returncode:
            lines = [line for line in completed.stdout.strip().splitlines() if line.strip()]
            shown = [line for line in lines if line.startswith("WRONG")] or lines[-2:]
            return runner, " | ".join(shown)[:240]
    return None, ""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--only", action="append", default=[])
    args = parser.parse_args()
    mutations = [m for m in MUTATIONS if not args.only or m[0] in args.only]
    if args.list:
        for ident, file, _old, _new, what in mutations:
            print(f"{ident:5} {file}: {what}")
        return 0
    unknown = set(args.only) - {m[0] for m in MUTATIONS}
    if unknown:
        print("unknown mutation id: " + ", ".join(sorted(unknown)), file=sys.stderr)
        return 2
    with tempfile.TemporaryDirectory(prefix="mutate-evidence-") as scratch:
        base = Path(scratch) / "baseline"
        copy_tree(base)
        started = time.time()
        failed, tail = run_runners(base, RUNNERS)
        if failed:
            print(f"BASELINE RED: {failed}: {tail}", file=sys.stderr)
            return 1
        print(f"baseline green ({time.time() - started:.0f} s); {len(mutations)} mutation(s)")
        survivors = []
        for ident, file, old, new, what in mutations:
            text = (base / file).read_text()
            if text.count(old) != 1:
                print(f"{ident}: the string to replace occurs {text.count(old)} times in {file}, not once", file=sys.stderr)
                return 2
            work = Path(scratch) / ident
            shutil.copytree(base, work, symlinks=True)
            (work / file).write_text(text.replace(old, new))
            git(work, "commit", "-q", "-a", "-m", ident)
            caught, tail = run_runners(work, RUNNERS)
            shutil.rmtree(work)
            if caught:
                print(f"caught    {ident:5} {what}\n            by {caught.rsplit('/', 1)[1]}: {tail}")
            else:
                survivors.append(ident)
                print(f"SURVIVED  {ident:5} {what}")
        print(f"{len(mutations) - len(survivors)} caught, {len(survivors)} survived")
        return 1 if survivors else 0


if __name__ == "__main__":
    raise SystemExit(main())
