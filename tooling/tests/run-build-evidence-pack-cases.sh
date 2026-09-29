#!/usr/bin/env bash
# Exercise the standalone evidence-pack verifier: its containment and digest
# checks, and each check it makes on the documents inside the pack.
#
# Packs are made here with the digests worked out from whatever the case put in
# them, so a pack fails for the change the case made and not because a digest no
# longer matches. The honest packs carry the receipts a push and a pull request
# would produce: every command step the workflow runs, each `success`
# (`tooling/required-steps.json`). Every refusal is one change to an honest pack.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cases=0

# write_pack DIRECTORY EVENT PROGRAM_FILE
#   A pack for EVENT (push or pull_request). PROGRAM_FILE is Python that may
#   change `d` before the files are written: d['sources'] (path -> text),
#   d['manifest'], d['receipts'], d['pack'] (the PACK-MANIFEST.json document),
#   d['skip_documents'], d['skip_sources'] and d['entries'] (a function that
#   edits the list of file entries after the digests are known).
write_pack() {
  PYTHONPATH="$root/tooling" python3 - "$1" "$2" "$3" "$root" <<'PY'
import copy, hashlib, importlib.util, json, pathlib, sys
directory, event, program, root = pathlib.Path(sys.argv[1]), sys.argv[2], pathlib.Path(sys.argv[3]), pathlib.Path(sys.argv[4])
from assurance_validation import REQUIRED_CHECKS, expected_step_outcomes


def load_script(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


SOURCES = load_script("manifest_builder", root / "tooling/build-assurance-manifest.py").SOURCES
EXTRA = load_script("pack_builder", root / "tooling/build-evidence-pack.py").EXTRA
table = expected_step_outcomes()
candidate = {"commit": "a" * 40, "tree": "b" * 40}


def receipt(check_id, classification="required"):
    return {"id": check_id, "classification": classification, "applicable": True,
            "status": "pass", "command": check_id + "-command",
            "environment": {"event": event},
            "step_outcomes": {step: "success" for step in table[(check_id, event)]},
            "run": {"id": "1", "attempt": "1", "commit": candidate["commit"], "tree": candidate["tree"]}}


checks = [receipt(check_id) for check_id in sorted(REQUIRED_CHECKS)]
if event == "pull_request":
    checks.append(receipt("sign-off", "conditional"))
else:
    checks.append({"id": "sign-off", "classification": "conditional", "applicable": False,
                   "status": "not_applicable", "command": "tooling/check-signoff.sh",
                   "environment": {"event": event}, "run": {"selection": "collector"}})
sources = {relative: "candidate evidence: " + relative + "\n" for relative in sorted(set(SOURCES) | set(EXTRA))}
d = {
    "candidate": candidate, "sources": sources, "skip_sources": [], "skip_documents": [],
    "manifest": {"schema_version": 1,
                 "identity": {"source_commit": candidate["commit"], "source_tree": candidate["tree"], "clean_tree": True},
                 "sources": None, "checks": checks,
                 "review_requirements": [{"type": "independent-ledger-review", "status": "pending"}]},
    "receipts": {"schema_version": 1, "candidate": dict(candidate), "checks": copy.deepcopy(checks)},
    "pack": {"schema_version": 1, "candidate": dict(candidate)}, "entries": None,
}
exec(program.read_text(), {"d": d, "SOURCES": SOURCES, "EXTRA": EXTRA, "json": json})

directory.mkdir(parents=True, exist_ok=True)
entries = []
for relative, text in d["sources"].items():
    if relative in d["skip_sources"]:
        continue
    target = directory / "source" / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text)
    entries.append({"path": "source/" + relative, "sha256": hashlib.sha256(target.read_bytes()).hexdigest(),
                    "bytes": target.stat().st_size})
if d["manifest"]["sources"] is None:
    d["manifest"]["sources"] = [
        {"path": relative, "sha256": hashlib.sha256(d["sources"][relative].encode()).hexdigest(),
         "bytes": len(d["sources"][relative].encode())} for relative in SOURCES]
for name, document in (("assurance-manifest.json", d["manifest"]), ("assurance-receipts.json", d["receipts"])):
    if name in d["skip_documents"]:
        continue
    target = directory / name
    target.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")
    entries.append({"path": name, "sha256": hashlib.sha256(target.read_bytes()).hexdigest(), "bytes": target.stat().st_size})
if d["entries"]:
    d["entries"](entries)
d["pack"].setdefault("files", entries)
(directory / "PACK-MANIFEST.json").write_text(json.dumps(d["pack"], indent=2, sort_keys=True) + "\n")
PY
}

# pack NAME EVENT 'python that changes d'
pack() {
  printf '%s\n' "${3:-pass}" > "$work/$1.py"
  write_pack "$work/$1" "$2" "$work/$1.py"
}

verify() {
  python3 "$root/tooling/build-evidence-pack.py" --verify "$1"
}

expect_pass() {
  local name="$1" directory="$2"
  cases=$((cases + 1))
  if ! verify "$directory" >/dev/null 2>"$work/$name.err"; then
    echo "WRONG  $name: an honest pack was refused:" >&2
    cat "$work/$name.err" >&2
    return 1
  fi
}

expect_fail() {
  local name="$1" needle="$2" directory="$3" out rc
  cases=$((cases + 1))
  set +e
  out="$(verify "$directory" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $name: expected refusal" >&2
    return 1
  fi
  if ! printf '%s' "$out" | grep -qF -- "$needle"; then
    echo "WRONG  $name: missing diagnostic '$needle'" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
}

# refuse NAME NEEDLE EVENT 'python that changes d'
refuse() {
  pack "$1" "$3" "$4"
  expect_fail "$1" "$2" "$work/$1"
}

# ---- honest packs are accepted -------------------------------------------
pack pass-push push
expect_pass push "$work/pass-push"
pack pass-pull-request pull_request
expect_pass pull-request "$work/pass-pull-request"

# A receipt for a check the repository does not own has no expected command
# list; it is accepted while it passes and refused once it does not.
optional='for r in (d["manifest"], d["receipts"]): r["checks"].append({"id": "docs", "classification": "optional", "applicable": True, "status": STATUS, "command": "docs-command", "environment": {"event": "push"}, "run": {"id": "1", "attempt": "1", "commit": "a" * 40, "tree": "b" * 40}})'
pack pass-optional push "${optional/STATUS/\"pass\"}"
expect_pass optional-check "$work/pass-optional"
refuse optional-check-failed 'applicable non-required check docs is fail' push "${optional/STATUS/\"fail\"}"

# ---- containment and digests ----------------------------------------------
cp -R "$work/pass-push" "$work/extra"
echo unlisted > "$work/extra/UNLISTED-SENTINEL.txt"
expect_fail extra 'pack contains unlisted files: UNLISTED-SENTINEL.txt' "$work/extra"

cp -R "$work/pass-push" "$work/symlink"
ln -s source/ASSURANCE.md "$work/symlink/SYMLINK-SENTINEL.txt"
expect_fail symlink 'pack contains a symlink: SYMLINK-SENTINEL.txt' "$work/symlink"

cp -R "$work/pass-push" "$work/tampered"
printf 'changed\n' > "$work/tampered/source/ASSURANCE.md"
expect_fail tampered 'pack digest mismatch: source/ASSURANCE.md' "$work/tampered"

cp -R "$work/pass-push" "$work/deleted"
rm "$work/deleted/source/ASSURANCE.md"
expect_fail deleted 'pack digest mismatch: source/ASSURANCE.md' "$work/deleted"

refuse escape 'invalid pack file path: ../source/evidence.txt' push "d['entries'] = lambda e: e[0].update(path='../source/evidence.txt')"
refuse absolute-path 'invalid pack file path: /etc/hosts' push "d['entries'] = lambda e: e[0].update(path='/etc/hosts')"
refuse repeated-path 'invalid pack file path: source/ASSURANCE-OBLIGATIONS.md' push "d['entries'] = lambda e: e.append(dict(e[0]))"
refuse entry-not-a-mapping 'invalid pack file entry' push "d['entries'] = lambda e: e.append('source/x')"
refuse entry-without-a-path 'invalid pack file entry' push "d['entries'] = lambda e: e.append({'sha256': 'x', 'bytes': 1})"
refuse negative-size 'invalid pack digest entry: source/ASSURANCE-OBLIGATIONS.md' push "d['entries'] = lambda e: e[0].update(bytes=-1)"
refuse size-not-a-number 'invalid pack digest entry: source/ASSURANCE-OBLIGATIONS.md' push "d['entries'] = lambda e: e[0].update(bytes='1')"
refuse digest-not-a-string 'invalid pack digest entry: source/ASSURANCE-OBLIGATIONS.md' push "d['entries'] = lambda e: e[0].update(sha256=1)"
refuse pack-schema 'invalid pack manifest' push "d['pack']['schema_version'] = 2"
refuse pack-files-not-a-list 'invalid pack manifest' push "d['pack']['files'] = {}"
refuse pack-candidate-missing 'pack manifest has invalid candidate' push "d['pack']['candidate'] = {'commit': '', 'tree': ''}"
refuse pack-candidate-not-strings 'pack manifest has invalid candidate' push "d['pack']['candidate'] = {'commit': 1, 'tree': 2}"

set +e
unreadable="$(python3 "$root/tooling/build-evidence-pack.py" --verify "$work/no-such-pack" 2>&1)"
unreadable_rc=$?
set -e
cases=$((cases + 1))
if [ "$unreadable_rc" -eq 0 ] || ! printf '%s' "$unreadable" | grep -qF 'cannot read JSON'; then
  echo "WRONG  unreadable-pack: $unreadable" >&2
  exit 1
fi
printf '[]\n' > "$work/not-an-object.json"
mkdir -p "$work/array-manifest"
cp "$work/not-an-object.json" "$work/array-manifest/PACK-MANIFEST.json"
expect_fail array-manifest 'must be an object' "$work/array-manifest"

# ---- what the pack must hold ----------------------------------------------
refuse missing-manifest-document 'pack is missing required evidence documents: assurance-manifest.json' push "d['skip_documents'] = ['assurance-manifest.json']"
refuse missing-receipts-document 'pack is missing required evidence documents: assurance-receipts.json' push "d['skip_documents'] = ['assurance-receipts.json']"
refuse missing-source 'pack is missing required source evidence: source/tacenta-proofs/CLAIMS.md' push "d['skip_sources'] = ['tacenta-proofs/CLAIMS.md']"
refuse missing-step-list 'pack is missing required source evidence: source/tooling/required-steps.json' push "d['skip_sources'] = ['tooling/required-steps.json']"
refuse manifest-lists-fewer-sources 'packed assurance manifest source inventory is incomplete or not repository-owned' push "d['manifest']['sources'] = [{'path': p, 'sha256': '0', 'bytes': 0} for p in SOURCES[1:]]"
refuse manifest-lists-more-sources 'packed assurance manifest source inventory is incomplete or not repository-owned' push "d['manifest']['sources'] = [{'path': p, 'sha256': '0', 'bytes': 0} for p in SOURCES + ['tooling/other.py']]"
refuse manifest-repeats-a-source 'packed assurance manifest source inventory is incomplete or not repository-owned' push "d['manifest']['sources'] = [{'path': p, 'sha256': '0', 'bytes': 0} for p in SOURCES + SOURCES[:1]]"
refuse manifest-source-entry-malformed 'packed assurance manifest has an invalid source entry' push "d['manifest']['sources'] = [{'path': p, 'sha256': '0', 'bytes': '0'} for p in SOURCES]"
refuse manifest-source-digest 'packed source evidence does not match its manifest entry' push "d['manifest']['sources'] = [{'path': p, 'sha256': '0' * 64, 'bytes': len(('candidate evidence: ' + p + chr(10)).encode())} for p in SOURCES]"
refuse manifest-source-size 'packed source evidence does not match its manifest entry' push "import hashlib; d['manifest']['sources'] = [{'path': p, 'sha256': hashlib.sha256(('candidate evidence: ' + p + chr(10)).encode()).hexdigest(), 'bytes': 1} for p in SOURCES]"

# ---- the candidate --------------------------------------------------------
refuse manifest-not-clean 'packed assurance manifest does not assert a clean candidate' push "d['manifest']['identity']['clean_tree'] = False"
refuse manifest-without-identity 'packed assurance manifest does not assert a clean candidate' push "d['manifest']['identity'] = None"
refuse manifest-other-commit 'packed assurance manifest candidate does not match pack candidate' push "d['manifest']['identity']['source_commit'] = 'c' * 40"
refuse manifest-other-tree 'packed assurance manifest candidate does not match pack candidate' push "d['manifest']['identity']['source_tree'] = 'c' * 40"
refuse receipts-other-commit 'packed receipts candidate does not match pack candidate' push "d['receipts']['candidate']['commit'] = 'c' * 40"
refuse receipts-other-tree 'packed receipts candidate does not match pack candidate' push "d['receipts']['candidate']['tree'] = 'c' * 40"

# ---- the receipts inside ----------------------------------------------------
refuse manifest-and-receipts-disagree 'disagree for check rust' push "next(c for c in d['receipts']['checks'] if c['id'] == 'rust')['command'] = 'other'"
refuse manifest-and-receipts-list-other-checks 'manifest and receipts contain different check IDs' push "d['receipts']['checks'] = [c for c in d['receipts']['checks'] if c['id'] != 'sign-off']"
refuse required-check-failed 'required applicable check rust is fail' push "for r in (d['manifest'], d['receipts']): next(c for c in r['checks'] if c['id'] == 'rust')['status'] = 'fail'"
refuse required-check-missing 'missing required check receipts: audit' push "for r in (d['manifest'], d['receipts']): r['checks'] = [c for c in r['checks'] if c['id'] != 'audit']"
refuse step-failed 'receipt rust records command steps that did not succeed: rust_test=failure' push "for r in (d['manifest'], d['receipts']): next(c for c in r['checks'] if c['id'] == 'rust')['step_outcomes']['rust_test'] = 'failure'"
refuse step-skipped 'receipt vectors records command steps that did not succeed: vectors_reader=skipped' push "for r in (d['manifest'], d['receipts']): next(c for c in r['checks'] if c['id'] == 'vectors')['step_outcomes']['vectors_reader'] = 'skipped'"
refuse step-missing 'receipt rust does not record the command steps: rust_clippy' push "for r in (d['manifest'], d['receipts']): del next(c for c in r['checks'] if c['id'] == 'rust')['step_outcomes']['rust_clippy']"
refuse step-extra 'receipt msrv records steps the workflow does not run for push: msrv_extra' push "for r in (d['manifest'], d['receipts']): next(c for c in r['checks'] if c['id'] == 'msrv')['step_outcomes']['msrv_extra'] = 'success'"
refuse steps-absent 'receipt audit records no command step outcomes' push "for r in (d['manifest'], d['receipts']): del next(c for c in r['checks'] if c['id'] == 'audit')['step_outcomes']"
refuse steps-emptied 'receipt proofs records no command step outcomes' push "for r in (d['manifest'], d['receipts']): next(c for c in r['checks'] if c['id'] == 'proofs')['step_outcomes'] = {}"
refuse steps-for-the-other-event 'receipt translation records steps the workflow does not run for pull_request: translation_seed' pull_request "for r in (d['manifest'], d['receipts']): next(c for c in r['checks'] if c['id'] == 'translation')['step_outcomes']['translation_seed'] = 'success'"
refuse signoff-step-failed 'receipt sign-off records command steps that did not succeed: signoff_check=failure' pull_request "for r in (d['manifest'], d['receipts']): next(c for c in r['checks'] if c['id'] == 'sign-off')['step_outcomes']['signoff_check'] = 'failure'"
refuse signoff-other-commit 'receipt sign-off was not produced for the selected candidate' pull_request "for r in (d['manifest'], d['receipts']): next(c for c in r['checks'] if c['id'] == 'sign-off')['run']['commit'] = 'c' * 40"
refuse required-check-other-commit 'receipt rust was not produced for the selected candidate' push "for r in (d['manifest'], d['receipts']): next(c for c in r['checks'] if c['id'] == 'rust')['run']['tree'] = 'c' * 40"
refuse two-events 'receipts come from more than one event: pull_request, push' pull_request "for r in (d['manifest'], d['receipts']): next(c for c in r['checks'] if c['id'] == 'rust')['environment']['event'] = 'push'"
refuse two-runs 'receipts come from more than one workflow run: 1, 2' push "for r in (d['manifest'], d['receipts']): next(c for c in r['checks'] if c['id'] == 'rust')['run']['id'] = '2'"

# ---- the command line -----------------------------------------------------
set +e
combined="$(python3 "$root/tooling/build-evidence-pack.py" --verify "$work/pass-push" --output "$work/x" 2>&1)"
combined_rc=$?
missing_args="$(python3 "$root/tooling/build-evidence-pack.py" --manifest "$work/x" 2>&1)"
missing_args_rc=$?
set -e
cases=$((cases + 2))
if [ "$combined_rc" -eq 0 ] || ! printf '%s' "$combined" | grep -qF -- '--verify cannot be combined with build arguments'; then
  echo "WRONG  verify-with-build-arguments: $combined" >&2
  exit 1
fi
if [ "$missing_args_rc" -eq 0 ] || ! printf '%s' "$missing_args" | grep -qF -- '--manifest, --receipts and --output are required'; then
  echo "WRONG  build-without-arguments: $missing_args" >&2
  exit 1
fi

echo "build-evidence-pack-cases: $cases cases gave the expected result (honest push and pull-request packs verified; each refusal is one change to an honest pack)"
