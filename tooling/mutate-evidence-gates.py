#!/usr/bin/env python3
"""Break the evidence gates one edit at a time and require their case runners to notice.

This is a local control, like `tooling/mutate-inventory.py`: nothing in CI runs
it. It answers one question for the receipt, manifest, evidence-pack and
review-receipt tooling: if this check is removed or weakened, does a case runner
go red? Each entry in `MUTATIONS` replaces one string, which must occur exactly
once, in one tooling file of a throwaway copy of the repository's evidence
tooling, commits the edit there, and runs the case runners named in `RUNNERS`
until one fails.

Each edit is then one of three things. SEEN AS ACCEPTED: a case that expected a
refusal saw an acceptance, or an honest input was refused, or an assertion
failed; the check is held. SEEN AS MESSAGE: the first failing case was still
refused, for another reason, and only its expected message no longer matched,
and no other case of that runner fails for more than a message (the runner is
run to its end to see). SURVIVED: every runner stayed green. An edit seen only as
a message, or survived, fails the run unless `EQUIVALENT` lists it with the
reason its verdict cannot change: the same inputs are refused by a later check,
and only which check says so changes.

A baseline run of the unedited copy comes first, and the harness stops if it is
not green, because a red baseline would make every edit look caught.

    python3 tooling/mutate-evidence-gates.py            # every mutation
    python3 tooling/mutate-evidence-gates.py --list
    python3 tooling/mutate-evidence-gates.py --check-table   # each old string occurs once
    python3 tooling/mutate-evidence-gates.py --only B1 --only V4

It exits 1 if the baseline is red or an edit is neither seen as accepted nor
listed as equivalent, and 2 if the tooling or the evidence files it copies differ
from `HEAD`: the copy is made from the working-tree files, so a record that names
a commit is only true of a clean tree.
"""
from __future__ import annotations

import argparse
import importlib.util
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))

# Runners, in the order they are tried. The first to fail catches the edit.
RUNNERS = [
    "tooling/tests/run-build-assurance-manifest-cases.sh",
    "tooling/tests/run-build-evidence-pack-cases.sh",
    "tooling/tests/run-collect-assurance-receipts-cases.sh",
    "tooling/tests/run-check-ledger-review-receipt-cases.sh",
]

# The runner that covers each file first, so most edits are caught by the first
# runner tried; any other runner is tried only if that one stays green.
HOME_RUNNER = {
    "tooling/build-evidence-pack.py": 1, "tooling/publish-evidence-archive.py": 1, "tooling/reproduce-evidence.py": 1,
    "tooling/collect-assurance-receipts.py": 2,
    "tooling/check-ledger-review-receipt.py": 3, "tooling/validate-reviewed-evidence.py": 3, "tooling/ledger-review-sections.py": 3,
}

BUILDER = "tooling/build-assurance-manifest.py"
VALIDATION = "tooling/assurance_validation.py"
COLLECTOR = "tooling/collect-assurance-receipts.py"
PACK = "tooling/build-evidence-pack.py"
PUBLISH = "tooling/publish-evidence-archive.py"
REPRODUCE = "tooling/reproduce-evidence.py"
REVIEW = "tooling/check-ledger-review-receipt.py"
REVIEWED = "tooling/validate-reviewed-evidence.py"
SECTIONS = "tooling/ledger-review-sections.py"

# Edits that no case sees as more than a changed message, or that survive, because the
# verdict cannot change: a later check refuses the same inputs, and only which check
# says so changes. Each entry gives that reason. An edit not listed here must be seen as
# accepted, and a listed edit that a case sees as accepted is stale and fails the run.
EQUIVALENT = {
    "MT4": "the comparison with `git rev-parse HEAD`, which follows, refuses every id that is not the full commit and tree",
    "MT10": "only the path printed in the refusal changes; the tree is dirty either way",
    "PK2": "the tree lookup that follows fails for a commit the repository does not hold, so the same pack is refused",
    "PK5": "the byte comparison that follows refuses a file the commit does not have, as different from the packed one",
    "PB7": "without a receipt path the publisher fails on `None.exists()` before it uploads anything",
    "RP1": "the byte comparison of the hosted receipts with the packed receipts, which follows, refuses the same inputs, because the receipts name their candidate",
    "RP3": "the candidate's manifest builder, which runs next, refuses receipts that name another tree than the commit's, and the pack check refuses a pack that does",
    "RP6": "the candidate's own verifier requires every file its builder writes, so the rebuilt pack has no file the given pack lacks, and a file only the given pack has fails the lookup that follows",
    "RP9": "a pack that equals the rebuild byte for byte is one the candidate's builder wrote, which verifies",
    "RP10": "a pack that equals the rebuild byte for byte has sources the builder copied from the commit",
    "RC2m": "each required field is refused by its own check below",
    "RC7": "an empty or missing list names none of the required artifacts, and a list of non-strings raises, so the same receipts are refused",
    "RC10": "no claims leaves every section uncovered, and claims that are not a list are refused by the loop",
    "RC16": "an unknown section raises KeyError at its digest lookup, so the same receipts are refused",
    "RC17": "a digest that is not 64 lower-case hex digits never equals a section's digest",
    "RC28": "an unhashable disposition raises TypeError at the membership test, which also refuses; the check keeps the refusal on the error path",
    "RV3": "the pack verifier already requires the packed manifest to name the pack's candidate, and the comparison of the packed manifest bytes with the given manifest follows, so together they refuse the same inputs",
}

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
    ("MT1", BUILDER, "if set(data) != MANIFEST_FIELDS:", "if False:", "--validate allows extra or missing top-level fields"),
    ("MT2", BUILDER, "if set(identity) != IDENTITY_FIELDS:", "if False:", "--validate allows extra or missing identity fields"),
    ("MT3", BUILDER, 'if identity["repository"] != REPOSITORY:', "if False:", "--validate allows another repository name"),
    ("MT4", BUILDER, 'GIT_OBJECT_ID.fullmatch(identity[key])', "True", "--validate allows a short commit or tree"),
    ("MT5", BUILDER, 'if identity["generator"] != GENERATOR or identity["generator_sha256"] != sha256(Path(__file__)):',
     "if False:", "--validate does not check which generator wrote the manifest"),
    ("MT5d", BUILDER, ' or identity["generator_sha256"] != sha256(Path(__file__)):', ":",
     "--validate checks the generator path but not its digest"),
    ("MT6", BUILDER, "or set(source) != SOURCE_FIELDS:", ":", "--validate allows extra fields in a source entry"),
    ("MT7", BUILDER, 'if line.startswith("!!") and path.startswith(".assurance/"):', 'if line.startswith("!!"):',
     "an ignored file anywhere makes the tree clean, not only under .assurance/"),
    ("MT7b", BUILDER, 'if line.startswith("!!") and path.startswith(".assurance/"):', "if False:",
     "the .assurance/ receipt workspace makes the tree dirty"),
    ("MT8", BUILDER, "        dirty.append(path)\n", '        if not line.startswith("??"):\n            dirty.append(path)\n',
     "an untracked file does not make the tree dirty"),
    ("MT9", BUILDER, '"--untracked-files=all", "--ignored=matching"], cwd=ROOT, text=True)',
     '"--untracked-files=all"], cwd=ROOT, text=True)', "an ignored file does not make the tree dirty"),
    ("MT10", BUILDER, '"--ignored=matching"], cwd=ROOT, text=True)', '"--ignored=matching"], cwd=ROOT, text=True).strip()',
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
    ("PK0", PACK, '".github/workflows/ci.yml", ".github/actions/assurance-receipt/action.yml",\n', "",
     "the pack need not carry the workflow and the receipt action"),
    # The pack verifier, its authentication against git, and its command line.
    ("PK1", PACK, "    if repo is not None:\n        authenticate(root, repo)\n", "    if False:\n        authenticate(root, repo)\n",
     "--candidate-repo is accepted and ignored"),
    ("PK2", PACK, 'if git_output(repo, "cat-file", "-e", candidate["commit"] + "^{commit}") is None:', "if False:",
     "a candidate commit that is not in the repository is not noticed"),
    ("PK3", PACK, 'if tree is None or tree.decode().strip() != candidate["tree"]:', "if False:",
     "the pack may name another tree than its commit has"),
    ("PK4", PACK, 'if committed != (root / entry["path"]).read_bytes():', "if False:",
     "a packed source need not be the commit's file"),
    ("PK5", PACK, "        if committed is None:\n", "        if False:\n",
     "a packed source that is not a file of the commit is not named as such"),
    ("PK6", PACK, 'if generator is None or hashlib.sha256(generator).hexdigest() != manifest["identity"].get("generator_sha256"):',
     "if False:", "the manifest's generator digest is not compared with the commit's"),
    ("PK7", PACK, 'if not entry["path"].startswith("source/"):', "if True:", "no packed source is compared with git"),
    ("PK8", PACK, "GIT_OBJECT_ID.fullmatch(candidate[field])", "True", "a short or non-hex candidate commit or tree is accepted"),
    ("PK9", PACK, "            if args.candidate_repo:\n", "            if False:\n", "--candidate-repo is accepted with a build"),
    # The publisher: nothing reaches the COMPLIANCE archive unless these hold.
    ("PB1", PUBLISH, "        if verified.returncode:", "        if False:", "an unverified pack is uploaded"),
    ("PB2", PUBLISH, '"--verify", str(args.pack),\n                                   "--candidate-repo", str(args.candidate_repo)], cwd=ROOT)',
     '"--verify", str(args.pack)], cwd=ROOT)', "the pack is not authenticated against git before upload"),
    ("PB3", PUBLISH, '"--body", str(path), "--if-none-match", "*"]', '"--body", str(path)]', "an upload may replace an existing key"),
    ("PB4", PUBLISH, 'if retention.get("Mode") != "COMPLIANCE" or not isinstance(retention.get("RetainUntilDate"), str):',
     "if False:", "an object without Compliance retention is recorded"),
    ("PB4m", PUBLISH, 'if retention.get("Mode") != "COMPLIANCE" or ', "if ", "retention in a mode other than COMPLIANCE is accepted"),
    ("PB4d", PUBLISH, ' or not isinstance(retention.get("RetainUntilDate"), str):', ":", "retention without an end date is accepted"),
    ("PB5", PUBLISH, "if not isinstance(version, str) or not version:", "if False:", "an upload that returns no version ID is recorded"),
    ("PB6", PUBLISH, "if args.receipt.exists():", "if False:", "an existing publication receipt is replaced"),
    ("PB7", PUBLISH, "if args.receipt is None:", "if False:", "publication without a receipt path"),
    ("PB8", PUBLISH, '(path.relative_to(args.pack).as_posix() == "PACK-MANIFEST.json", path)', "(False, path)",
     "the pack manifest is not uploaded last"),
    ("PB9", PUBLISH, 'prefix = f"candidates/{commit}/{pack_digest}"', 'prefix = f"candidates/{commit}"',
     "the archive prefix does not carry the pack digest"),
    # The reproduction of a candidate from public inputs.
    ("RP1", REPRODUCE, "if hosted_candidate != candidate:", "if False:", "a hosted artifact of another candidate is compared with the pack"),
    ("RP2", REPRODUCE, "if given.read_bytes() != packed.read_bytes():", "if False:", "a hosted file need not be the packed one"),
    ("RP3", REPRODUCE, 'if head_tree != candidate["tree"]:', "if False:", "the candidate tree is not compared with the commit's"),
    ("RP4", REPRODUCE, "if rebuilt_manifest.read_bytes() != manifest_path.read_bytes():", "if False:",
     "the rebuilt manifest need not equal the given one"),
    ("RP5", REPRODUCE, "count = compare_trees(args.pack, rebuilt_pack, \"pack\")", "count = 0", "the rebuilt pack is not compared"),
    ("RP6", REPRODUCE, "if set(a) != set(b):", "if False:", "the rebuilt pack may list other files"),
    ("RP7", REPRODUCE, "if a[relative].read_bytes() != b[relative].read_bytes():", "if False:", "the rebuilt pack may differ in a file"),
    ("RP8", REPRODUCE, "        if worktree is not None:\n", "        if False:\n", "a reproduction leaves its worktree in the repository"),
    ("RP9", REPRODUCE, '"--verify", str(args.pack.resolve())], worktree,', '"--help"], worktree,',
     "the candidate's own pack verifier is not run"),
    ("RP10", REPRODUCE, 'builder.authenticate(args.pack, repo)', "pass", "the pack is not authenticated against git"),
    # The review receipt checker, the section tool and the reviewed-evidence check.
    ("RC1", REVIEW, 'if type(receipt.get("schema_version")) is not int or receipt["schema_version"] != SCHEMA_VERSION:', "if False:", "the receipt schema version is not checked"),
    ("RC2u", REVIEW, "unknown = sorted(set(receipt) - TOP_LEVEL - OPTIONAL_TOP_LEVEL)", "unknown = []", "an unknown receipt field is accepted"),
    ("RC2m", REVIEW, "missing = sorted(TOP_LEVEL - set(receipt))", "missing = []", "a missing receipt field is not named"),
    ("RC3", REVIEW, "if any(PLACEHOLDER in text for text in strings_in(receipt)):", "if False:", "a template placeholder is accepted"),
    ("RC4", REVIEW, 'if receipt.get("candidate") != pack_manifest["candidate"]:', "if False:", "a receipt for another candidate is accepted"),
    ("RC5", REVIEW, 'if not isinstance(binding, dict) or binding.get("manifest_sha256") != digest(pack / "PACK-MANIFEST.json"):',
     "if not isinstance(binding, dict):", "the receipt need not bind the pack manifest"),
    ("RC6", REVIEW, 'isinstance(reviewer.get(k), str) and reviewer[k].strip() for k in ("identity", "independence_statement")',
     'True for k in ("identity", "independence_statement")', "a receipt without reviewer identity is accepted"),
    ("RC7", REVIEW, "if not isinstance(artifacts, list) or not artifacts or not all(isinstance(item, str) and item for item in artifacts):",
     "if False:", "a receipt without artifacts read is accepted"),
    ("RC8", REVIEW, "    if unnamed:\n", "    if False:\n", "a required artifact need not be named"),
    ("RC9", REVIEW, "if not isinstance(notes, list) or not all(isinstance(note, str) and note.strip() for note in notes):", "if False:",
     "malformed cross-cutting notes are accepted"),
    ("RC10", REVIEW, "if not isinstance(claims, list) or not claims:", "if False:", "a receipt with no dispositions is accepted"),
    ("RC11", REVIEW, "if not isinstance(claim, dict) or set(claim) != CLAIM_FIELDS:", "if False:", "a disposition with other fields is accepted"),
    ("RC12", REVIEW, "if not isinstance(reference, str) or not reference or reference in seen:", "if False:",
     "a repeated or empty reference is accepted"),
    ("RC13", REVIEW, 'if not isinstance(claim["disposition"], str) or claim["disposition"] not in DISPOSITIONS:', "if False:", "an unknown disposition is accepted"),
    ("RC14", REVIEW, 'if not isinstance(claim["finding"], str):', "if False:", "a finding that is not text is accepted"),
    ("RC15", REVIEW, 'if not claim["finding"].strip():', "if False:",
     "a disposition without finding text is accepted"),
    ("RC16", REVIEW, "if reference not in sections:", "if False:", "a reference to a section the ledger lacks is accepted"),
    ("RC17", REVIEW, 'if not isinstance(claim["section_sha256"], str) or not SHA256.fullmatch(claim["section_sha256"]):', "if False:",
     "a malformed section digest is accepted"),
    ("RC18", REVIEW, 'if claim["section_sha256"] != sections[reference]:', "if False:", "a disposition on other text than the pack's is accepted"),
    ("RC19", REVIEW, "    if uncovered:\n", "    if False:\n", "a section with no disposition is accepted"),
    ("RC20", REVIEW, "if require_no_findings and findings:", "if False:", "--require-no-findings does not refuse a finding"),
    ("RC21", REVIEW, 'if digest(path) != entries[0].get("sha256"):', "if False:", "the pack's CLAIMS.md is not held to its manifest digest"),
    ("RC22", REVIEW, "if len(entries) != 1 or not path.is_file():", "if False:", "a pack without CLAIMS.md is read as an empty ledger"),
    ("RC23", REVIEW, "        if title in sections:\n", "        if False:\n", "two sections with one title are accepted"),
    ("RC24", REVIEW, "    add(INTRODUCTION, text[: matches[0].start() if matches else len(text)])\n", "    pass\n",
     "the ledger's introduction need not be dispositioned"),
    ("RC25", REVIEW, 'if pack_manifest.get("schema_version") != 1 or not isinstance(pack_manifest.get("candidate"), dict):', "if False:",
     "the pack manifest schema is not checked"),
    ("RC26", REVIEW, 'return claim_sections(path.read_bytes().decode("utf-8"))', "return claim_sections(path.read_text())",
     "the ledger is read through the platform's newline translation"),
    ("RC27", REVIEW, 'type(receipt.get("schema_version")) is not int or ', "", "a receipt with schema_version 2.0 is accepted"),
    ("RC28", REVIEW, 'if not isinstance(claim["disposition"], str) or ', "if ", "a disposition that is not a string reaches the membership test"),
    # Edits the fresh review of this branch made that no case saw (ids as in its report).
    ("X1a", REVIEW, '"CLAIMS.md", "LIMITATIONS.md", "verification-manifest.json", "evidence-index.json", "ASSURANCE.md",\n',
     '"LIMITATIONS.md", "verification-manifest.json", "evidence-index.json", "ASSURANCE.md",\n', "CLAIMS.md need not be named as read"),
    ("X1b", REVIEW, '"CLAIMS.md", "LIMITATIONS.md", "verification-manifest.json", "evidence-index.json", "ASSURANCE.md",\n',
     '"CLAIMS.md", "verification-manifest.json", "evidence-index.json", "ASSURANCE.md",\n', "LIMITATIONS.md need not be named as read"),
    ("X1c", REVIEW, '"CLAIMS.md", "LIMITATIONS.md", "verification-manifest.json", "evidence-index.json", "ASSURANCE.md",\n',
     '"CLAIMS.md", "LIMITATIONS.md", "evidence-index.json", "ASSURANCE.md",\n', "verification-manifest.json need not be named as read"),
    ("X1d", REVIEW, '"CLAIMS.md", "LIMITATIONS.md", "verification-manifest.json", "evidence-index.json", "ASSURANCE.md",\n',
     '"CLAIMS.md", "LIMITATIONS.md", "verification-manifest.json", "ASSURANCE.md",\n', "evidence-index.json need not be named as read"),
    ("X1e", REVIEW, '"ASSURANCE-OBLIGATIONS.md", "GAP-REGISTER.md", "P6-L2-TARGET-DECISION.md",\n    "PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md",\n',
     '"ASSURANCE-OBLIGATIONS.md", "GAP-REGISTER.md",\n    "PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md",\n', "P6-L2-TARGET-DECISION.md need not be named as read"),
    ("X1f", REVIEW, '"ASSURANCE-OBLIGATIONS.md", "GAP-REGISTER.md", "P6-L2-TARGET-DECISION.md",\n    "PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md",\n',
     '"ASSURANCE-OBLIGATIONS.md", "GAP-REGISTER.md", "P6-L2-TARGET-DECISION.md",\n', "PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md need not be named as read"),
    ("X2", REVIEW, "    elif isinstance(value, list):\n        for item in value:\n            yield from strings_in(item)",
     "    elif isinstance(value, list):\n        for item in value:\n            if isinstance(item, dict):\n                yield from strings_in(item)",
     "a placeholder in a list of strings (artifacts_read, cross_cutting_notes) is not found"),
    ("X3", REVIEW, "add(match.group(1).rstrip(), text[match.start():end])", "add(match.group(1), text[match.start():end])",
     "a section title keeps trailing whitespace (the carriage return of a CRLF ledger)"),
    ("X4", REVIEW, "add(match.group(1).rstrip(), text[match.start():end])", "add(match.group(1).rstrip(), text[match.start():match.end()])",
     "a section's digest covers its heading line only, not its text"),
    ("X5", REVIEW, "end = matches[index + 1].start() if index + 1 < len(matches) else len(text)",
     "end = matches[index + 1].start() if index + 1 < len(matches) else matches[index].end()", "the last section's digest covers its heading only"),
    ("X6", REVIEW, "add(INTRODUCTION, text[: matches[0].start() if matches else len(text)])",
     "add(INTRODUCTION, text[: (matches[0].start() if matches else len(text)) - 1])", "the introduction's digest leaves out its last byte"),
    ("X7", REVIEW, "end = matches[index + 1].start() if index + 1 < len(matches) else len(text)",
     "end = matches[index + 1].start() if index + 1 < len(matches) else len(text) - 1", "the last section's digest leaves out its last byte"),
    ("X8", REVIEW, "add(match.group(1).rstrip(), text[match.start():end])", "add(match.group(1).rstrip(), text[match.start():end - 1])",
     "every section's digest leaves out its last byte"),
    ("X20", PACK, '    for entry in pack["files"]:\n        if not entry["path"].startswith("source/"):\n',
     '    for entry in pack["files"][1:]:\n        if not entry["path"].startswith("source/"):\n', "authentication skips the first listed file"),
    ("X20b", PACK, '    for entry in pack["files"]:\n        if not entry["path"].startswith("source/"):\n',
     '    for entry in pack["files"][:-1]:\n        if not entry["path"].startswith("source/"):\n', "authentication skips the last listed file"),
    ("X21", PACK, 'if not entry["path"].startswith("source/"):\n            continue',
     'if not entry["path"].startswith("source/") or entry["path"].startswith("source/.github/"):\n            continue',
     "the packed workflow and receipt action are not compared with git"),
    ("X22", PACK, 'if not entry["path"].startswith("source/"):\n            continue',
     'if not entry["path"].startswith("source/") or entry["path"].startswith("source/tooling/"):\n            continue',
     "the packed tooling files (required-steps.json, the checkers) are not compared with git"),
    ("X23", PACK, 'if not entry["path"].startswith("source/"):\n            continue',
     'if not entry["path"].startswith("source/") or entry["path"].startswith("source/tacenta-spec/") or entry["path"].startswith("source/tacenta-test-vectors/"):\n            continue',
     "the packed spec and vector files are not compared with git"),
    ("X24", PACK, 'if not entry["path"].startswith("source/"):\n            continue',
     'if not entry["path"].startswith("source/") or entry["path"].startswith("source/tacenta-proofs/manifests/") or entry["path"].startswith("source/tacenta-proofs/LIMITATIONS"):\n            continue',
     "the packed verification manifest and LIMITATIONS.md are not compared with git"),
    ("X40", REPRODUCE, "shutil.rmtree(scratch, ignore_errors=True)", "pass", "a reproduction leaves its scratch directory"),
    ("X41", REPRODUCE, "sys.dont_write_bytecode = True\n", "", "a reproduction may leave bytecode in the repository"),
    ("X50", BUILDER, 'identity.get("clean_tree") is not True:\n        fail("manifest does not assert a clean source tree")',
     'not identity.get("clean_tree"):\n        fail("manifest does not assert a clean source tree")', "a truthy clean_tree is enough"),
    ("X51", BUILDER, 'if data.get("schema_version") != 1:', 'if data.get("schema_version") not in (1, 1.0, 2):', "a manifest of schema_version 2 is accepted"),
    ("X52", PUBLISH, 'if not isinstance(version, str) or not version:', 'if version is None:', "an empty version ID is recorded"),
    ("RV1", REVIEWED, '"--pack", str(args.pack),\n            "--require-no-findings")', '"--pack", str(args.pack))',
     "a reviewed candidate may carry a finding"),
    ("RV2", REVIEWED, '"--verify", str(args.pack), "--candidate-repo", str(ROOT))', '"--verify", str(args.pack))',
     "the reviewed pack is not authenticated against git"),
    ("RV3", REVIEWED, 'if pack.get("candidate") != candidate:', "if False:", "the pack may name another candidate than the manifest"),
    ("RV4", REVIEWED, "if not packed_manifest.is_file() or hashlib.sha256(packed_manifest.read_bytes()).digest() != hashlib.sha256(args.manifest.read_bytes()).digest():",
     "if False:", "the pack need not hold the reviewed manifest's bytes"),
    ("RV5", REVIEWED, 'run(sys.executable, str(ROOT / "tooling/build-assurance-manifest.py"), "--validate", str(args.manifest))', "pass",
     "the manifest is not validated"),
    ("SC1", SECTIONS, "before[title] == section_digest", "True", "a changed section is reported unchanged"),
    ("SC2", SECTIONS, "gone = [title for title in before if title not in sections]", "gone = []", "a removed section is not reported"),
    ("SC3", SECTIONS, "if args.template.exists():", "if False:", "a template replaces an existing file"),
    ("SC4", SECTIONS, "if args.template and args.since:", "if False:", "--template is accepted with --since"),
    ("SC5", SECTIONS, "if receipt.get(\"schema_version\") != checker.SCHEMA_VERSION:", "if False:", "a schema 1 receipt serves as an earlier state"),
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


MESSAGE = re.compile(r"missing diagnostic|got rc=[1-9]")


def wrong_lines(output: str) -> list[str]:
    return [line for line in output.splitlines() if line.startswith("WRONG")]


def run_runner(directory: Path, runner: str, keep_going: bool = False) -> tuple[int, str]:
    """Run one runner. With keep_going its errexit is switched off, so every case runs
    and prints its own WRONG line instead of the first failure stopping the runner."""
    script = directory / runner
    if keep_going:
        text = script.read_text().replace("set -euo pipefail", "set -uo pipefail", 1)
        # The helpers switch errexit back on after each case; leave it off.
        text = re.sub(r"(?m)^(\s*)set -e\s*$", r"\1:", text)
        script = script.with_name(script.stem + "-keep-going.sh")
        script.write_text(text)
    completed = subprocess.run(["bash", str(script)], cwd=directory, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=3000, env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
    return completed.returncode, completed.stdout


def run_runners(directory: Path, runners: list[str]) -> tuple[str | None, str]:
    """The first runner that fails and its output, or (None, "") if all pass."""
    for runner in runners:
        code, output = run_runner(directory, runner)
        if code:
            return runner, output
    return None, ""


def seen_as(directory: Path, runner: str, output: str) -> str:
    """"accepted" if some case of the failing runner fails for more than a changed
    message (it expected a refusal and saw an acceptance, an honest input was refused,
    or an assertion failed), else "message"."""
    wrong = wrong_lines(output)
    if not wrong or not all(MESSAGE.search(line) for line in wrong):
        return "accepted"
    _, everything = run_runner(directory, runner, keep_going=True)
    return "accepted" if any(not MESSAGE.search(line) for line in wrong_lines(everything)) else "message"


def first_case(output: str) -> str:
    wrong = wrong_lines(output)
    if wrong:
        match = re.match(r"WRONG\s+([^:]+):", wrong[0])
        return match.group(1) if match else wrong[0][:80]
    return "an assertion or a step that must pass failed"


def evidence_files() -> list[str]:
    spec = importlib.util.spec_from_file_location("builder", ROOT / BUILDER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    pack_spec = importlib.util.spec_from_file_location("packer", ROOT / PACK)
    pack = importlib.util.module_from_spec(pack_spec)
    pack_spec.loader.exec_module(pack)
    return sorted(set(module.SOURCES) | set(pack.EXTRA) | {".gitignore", "tooling"})


def dirty_evidence_files() -> list[str]:
    status = subprocess.run(["git", "status", "--porcelain", "--", *evidence_files()], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True).stdout
    return [line for line in status.splitlines() if line.strip()]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--check-table", action="store_true")
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
    if args.check_table:
        bad = 0
        for ident, file, old, _new, _what in MUTATIONS:
            count = (ROOT / file).read_text().count(old)
            if count != 1:
                print(f"{ident}: the string to replace occurs {count} times in {file}, not once", file=sys.stderr)
                bad += 1
        missing = sorted(set(EQUIVALENT) - {m[0] for m in MUTATIONS})
        if missing:
            print("EQUIVALENT names edits the table does not have: " + ", ".join(missing), file=sys.stderr)
            bad += 1
        print(f"table: {len(MUTATIONS)} edits, {bad} problem(s)")
        return 1 if bad else 0
    dirty = dirty_evidence_files()
    if dirty:
        print("the tooling or an evidence file differs from HEAD, so the commit a record names is not what would run:\n  "
              + "\n  ".join(dirty), file=sys.stderr)
        return 2
    head = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, text=True, stdout=subprocess.PIPE).stdout.strip()
    with tempfile.TemporaryDirectory(prefix="mutate-evidence-") as scratch:
        base = Path(scratch) / "baseline"
        copy_tree(base)
        started = time.time()
        failed, output = run_runners(base, RUNNERS)
        if failed:
            shown = (wrong_lines(output) or [line for line in output.splitlines() if line.strip()][-2:])
            print(f"BASELINE RED: {failed}: {' | '.join(shown)[:240]}", file=sys.stderr)
            return 1
        print(f"baseline green at {head} ({time.time() - started:.0f} s); {len(mutations)} mutation(s)")
        accepted, message_equivalent, survived_equivalent, unexpected = [], [], [], []
        for ident, file, old, new, what in mutations:
            text = (base / file).read_text()
            if text.count(old) != 1:
                print(f"{ident}: the string to replace occurs {text.count(old)} times in {file}, not once", file=sys.stderr)
                return 2
            work = Path(scratch) / ident
            shutil.copytree(base, work, symlinks=True)
            (work / file).write_text(text.replace(old, new))
            git(work, "commit", "-q", "-a", "-m", ident)
            home = HOME_RUNNER.get(file, 0)
            runner, output = run_runners(work, [RUNNERS[home]] + [r for i, r in enumerate(RUNNERS) if i != home])
            kind = seen_as(work, runner, output) if runner else "survived"
            shutil.rmtree(work)
            label = f"{ident:5} {what}"
            if kind == "accepted" and ident in EQUIVALENT:
                unexpected.append(ident)
                print(f"STALE     {label}\n            listed as equivalent, but {runner.rsplit('/', 1)[1]} sees it as accepted ({first_case(output)}): remove it from EQUIVALENT")
            elif kind == "accepted":
                accepted.append(ident)
                print(f"caught    {label}\n            seen as accepted by {runner.rsplit('/', 1)[1]}: {first_case(output)}")
            elif ident in EQUIVALENT:
                (message_equivalent if kind == "message" else survived_equivalent).append(ident)
                seen = f"seen as message only by {runner.rsplit('/', 1)[1]}: {first_case(output)}" if kind == "message" else "survived every runner"
                print(f"EQUIVALENT {label}\n            {seen}; claimed equivalent: {EQUIVALENT[ident]}")
            else:
                unexpected.append(ident)
                seen = f"seen as message only by {runner.rsplit('/', 1)[1]}: {first_case(output)}" if kind == "message" else "survived every runner"
                print(f"UNEXPECTED {label}\n            {seen}")
        print(f"{len(mutations)} edits: {len(accepted)} seen as accepted, {len(message_equivalent)} seen as message only and claimed equivalent, "
              f"{len(survived_equivalent)} survived and claimed equivalent, {len(unexpected)} unexpected" + (": " + ", ".join(unexpected) if unexpected else ""))
        return 1 if unexpected else 0


if __name__ == "__main__":
    raise SystemExit(main())
