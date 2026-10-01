#!/usr/bin/env bash
# Exercise the evidence-pack tooling: the standalone verifier (its containment and
# digest checks, and each check it makes on the documents inside the pack), the
# check of a pack against git, the rebuild of a candidate from public inputs
# (`reproduce-evidence.py`) and the archive publisher, which runs here against a
# stand-in for `aws` that cannot reach the real archive.
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

cp -R "$work/pass-push" "$work/tampered-same-size"
python3 - "$work/tampered-same-size/source/ASSURANCE.md" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
data = bytearray(path.read_bytes())
data[-2] = ord("X") if data[-2] != ord("X") else ord("Y")
path.write_bytes(bytes(data))
PY
expect_fail tampered-same-size 'pack digest mismatch: source/ASSURANCE.md' "$work/tampered-same-size"

refuse escape 'invalid pack file path: ../source/evidence.txt' push "d['entries'] = lambda e: e[0].update(path='../source/evidence.txt')"
refuse absolute-path 'invalid pack file path: /etc/hosts' push "d['entries'] = lambda e: e[0].update(path='/etc/hosts')"
refuse repeated-path 'invalid pack file path: source/ASSURANCE-OBLIGATIONS.md' push "d['entries'] = lambda e: e.append(dict(next(x for x in e if x['path'] == 'source/ASSURANCE-OBLIGATIONS.md')))"
refuse entry-not-a-mapping 'invalid pack file entry' push "d['entries'] = lambda e: e.append('source/x')"
refuse entry-without-a-path 'invalid pack file entry' push "d['entries'] = lambda e: e.append({'sha256': 'x', 'bytes': 1})"
refuse negative-size 'invalid pack digest entry: source/ASSURANCE-OBLIGATIONS.md' push "d['entries'] = lambda e: next(x for x in e if x['path'] == 'source/ASSURANCE-OBLIGATIONS.md').update(bytes=-1)"
refuse size-not-a-number 'invalid pack digest entry: source/ASSURANCE-OBLIGATIONS.md' push "d['entries'] = lambda e: next(x for x in e if x['path'] == 'source/ASSURANCE-OBLIGATIONS.md').update(bytes='1')"
refuse digest-not-a-string 'invalid pack digest entry: source/ASSURANCE-OBLIGATIONS.md' push "d['entries'] = lambda e: next(x for x in e if x['path'] == 'source/ASSURANCE-OBLIGATIONS.md').update(sha256=1)"
refuse pack-schema 'invalid pack manifest' push "d['pack']['schema_version'] = 2"
refuse pack-files-not-a-list 'invalid pack manifest' push "d['pack']['files'] = {}"
refuse pack-candidate-missing 'pack manifest has invalid candidate' push "d['pack']['candidate'] = {'commit': '', 'tree': ''}"
refuse pack-candidate-short 'pack manifest has invalid candidate' push "d['pack']['candidate'] = {'commit': 'abc', 'tree': 'def'}"
refuse pack-candidate-short-everywhere 'pack manifest has invalid candidate' push "d['candidate'] = {'commit': 'abc', 'tree': 'def'}; d['manifest']['identity'].update(source_commit='abc', source_tree='def'); d['receipts']['candidate'] = dict(d['candidate']); d['pack']['candidate'] = dict(d['candidate'])
for r in (d['manifest'], d['receipts']):
    for c in r['checks']:
        if 'commit' in c['run']: c['run'].update(commit='abc', tree='def')"
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
refuse missing-manifest-source 'pack is missing required source evidence: source/GAP-REGISTER.md' push "d['skip_sources'] = ['GAP-REGISTER.md']"
refuse missing-step-list 'pack is missing required source evidence: source/tooling/required-steps.json' push "d['skip_sources'] = ['tooling/required-steps.json']"
refuse missing-workflow 'pack is missing required source evidence: source/.github/workflows/ci.yml' push "d['skip_sources'] = ['.github/workflows/ci.yml']"
refuse missing-receipt-action 'pack is missing required source evidence: source/.github/actions/assurance-receipt/action.yml' push "d['skip_sources'] = ['.github/actions/assurance-receipt/action.yml']"
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

# ---- a pack made by the production tools, and the git it must match ----------
# Everything above uses made-up commits, so it cannot show that a pack's files
# are the candidate commit's. These candidates are made by the production
# tools in a small git repository (`tests/make-candidate.py`): the receipt writer,
# the collector, the manifest builder and the pack builder. `--candidate-repo`
# then holds the pack to that repository's history.
export PYTHONDONTWRITEBYTECODE=1
make_candidate() {
  python3 "$here/make-candidate.py" "$root" "$work/$1" --event "$2"
}
make_candidate real-push push
make_candidate real-pull-request pull_request
real="$work/real-push"
verify_in_repo() {
  python3 "$root/tooling/build-evidence-pack.py" --verify "$1" --candidate-repo "$2"
}
expect_real_pass() {
  cases=$((cases + 1))
  if ! verify_in_repo "$1" "$2" >"$work/real.out" 2>&1; then
    echo "WRONG  $3: an honest pack made by the production tools was refused:" >&2
    cat "$work/real.out" >&2
    return 1
  fi
}
expect_real_fail() {
  local name="$1" needle="$2" pack="$3" repo="$4" out rc
  cases=$((cases + 1))
  set +e
  out="$(verify_in_repo "$pack" "$repo" 2>&1)"
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
expect_real_pass "$real/pack" "$real/repo" real-push
expect_real_pass "$work/real-pull-request/pack" "$work/real-pull-request/repo" real-pull-request
python3 "$root/tooling/build-evidence-pack.py" --verify "$real/pack" >/dev/null
cases=$((cases + 1))

# forge PACK RELATIVE TEXT: change a packed source, then make every digest that
# mentions it agree, so that the pack still verifies on its own.
forge() {
  python3 "$here/forge-pack-source.py" "$1" "$2" "$3"
}

cp -R "$real/pack" "$work/forged-source"
forge "$work/forged-source" ASSURANCE.md 'A different ledger text, with digests made to agree.
'
python3 "$root/tooling/build-evidence-pack.py" --verify "$work/forged-source" >/dev/null
cases=$((cases + 1))
expect_real_fail forged-source 'packed source differs from the candidate commit: ASSURANCE.md' "$work/forged-source" "$real/repo"

cp -R "$real/pack" "$work/forged-claims"
forge "$work/forged-claims" tacenta-proofs/CLAIMS.md '# Claims
'
expect_real_fail forged-claims 'packed source differs from the candidate commit: tacenta-proofs/CLAIMS.md' "$work/forged-claims" "$real/repo"

cp -R "$real/pack" "$work/forged-generator"
python3 - "$work/forged-generator" <<'PY'
import hashlib, json, pathlib, sys
pack = pathlib.Path(sys.argv[1])
manifest_path = pack / "assurance-manifest.json"
manifest = json.loads(manifest_path.read_text())
manifest["identity"]["generator_sha256"] = "0" * 64
manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
index_path = pack / "PACK-MANIFEST.json"
index = json.loads(index_path.read_text())
for entry in index["files"]:
    path = pack / entry["path"]
    entry["sha256"], entry["bytes"] = hashlib.sha256(path.read_bytes()).hexdigest(), path.stat().st_size
index_path.write_text(json.dumps(index, indent=2, sort_keys=True) + "\n")
PY
python3 "$root/tooling/build-evidence-pack.py" --verify "$work/forged-generator" >/dev/null
cases=$((cases + 1))
expect_real_fail forged-generator "packed manifest names a generator that is not the candidate commit's" "$work/forged-generator" "$real/repo"

# Every file under source/ is held to git, one at a time: each is forged with every
# digest brought up to date, so the pack still verifies on its own, and refused.
packed_sources="$(python3 -c 'import json,sys; print("\n".join(e["path"][len("source/"):] for e in json.load(open(sys.argv[1]))["files"] if e["path"].startswith("source/")))' "$real/pack/PACK-MANIFEST.json")"
packed_count=0
while IFS= read -r relative; do
  cp -R "$real/pack" "$work/forge-each"
  forge "$work/forge-each" "$relative" "Forged text for $relative.
"
  expect_real_fail "forge-$relative" "packed source differs from the candidate commit: $relative" "$work/forge-each" "$real/repo"
  rm -rf "$work/forge-each"
  packed_count=$((packed_count + 1))
done <<EOF
$packed_sources
EOF
expected_sources="$(python3 -c 'import importlib.util,sys; s=importlib.util.spec_from_file_location("p", sys.argv[1]+"/tooling/build-evidence-pack.py"); sys.path.insert(0, sys.argv[1]+"/tooling"); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); print(len(set(m.ASSURANCE_SOURCES) | set(m.EXTRA)))' "$root")"
if [ "$packed_count" != "$expected_sources" ]; then
  echo "WRONG  forged $packed_count packed sources, but the pack allowlist has $expected_sources" >&2
  exit 1
fi

# The same pack against a repository that does not hold the candidate commit.
expect_real_fail commit-absent 'is not in the repository' "$real/pack" "$work/real-pull-request/repo"
mkdir "$work/empty-repo"
git -C "$work/empty-repo" init -q 2>/dev/null
expect_real_fail repository-empty 'is not in the repository' "$real/pack" "$work/empty-repo"

# The commit is there and the pack names another tree for it. The pack is the one
# the production tools made, so every packed source is the commit's file and the
# generator digest is right; only the tree differs, in every document that names
# it, with the digests brought up to date. Only the comparison with git refuses it.
real_commit="$(git -C "$real/repo" rev-parse HEAD)"
cp -R "$real/pack" "$work/tree-of-another-commit"
python3 - "$work/tree-of-another-commit" <<'PY'
import hashlib, json, pathlib, sys
pack, other = pathlib.Path(sys.argv[1]), "c" * 40
def rewrite(name, edit):
    path = pack / name
    document = json.loads(path.read_text())
    edit(document)
    path.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")
def move_checks(document):
    for check in document["checks"]:
        if "tree" in check["run"]:
            check["run"]["tree"] = other
def manifest(document):
    document["identity"]["source_tree"] = other
    move_checks(document)
def receipts(document):
    document["candidate"]["tree"] = other
    move_checks(document)
rewrite("assurance-manifest.json", manifest)
rewrite("assurance-receipts.json", receipts)
rewrite("PACK-MANIFEST.json", lambda document: document["candidate"].update(tree=other))
index_path = pack / "PACK-MANIFEST.json"
index = json.loads(index_path.read_text())
for entry in index["files"]:
    path = pack / entry["path"]
    entry["sha256"], entry["bytes"] = hashlib.sha256(path.read_bytes()).hexdigest(), path.stat().st_size
index_path.write_text(json.dumps(index, indent=2, sort_keys=True) + "\n")
PY
expect_pass tree-of-another-commit-alone "$work/tree-of-another-commit"
expect_real_fail tree-of-another-commit 'pack candidate tree is not the tree of the candidate commit' "$work/tree-of-another-commit" "$real/repo"

# A source file that is not a file of the commit.
cp -R "$real/pack" "$work/source-not-in-commit"
python3 - "$work/source-not-in-commit" <<'PY'
import hashlib, json, pathlib, sys
pack = pathlib.Path(sys.argv[1])
extra = pack / "source" / "NOT-IN-THE-COMMIT.md"
extra.write_text("Added to the pack, never committed.\n")
index_path = pack / "PACK-MANIFEST.json"
index = json.loads(index_path.read_text())
index["files"].append({"path": "source/NOT-IN-THE-COMMIT.md", "sha256": hashlib.sha256(extra.read_bytes()).hexdigest(), "bytes": extra.stat().st_size})
index_path.write_text(json.dumps(index, indent=2, sort_keys=True) + "\n")
PY
python3 "$root/tooling/build-evidence-pack.py" --verify "$work/source-not-in-commit" >/dev/null
cases=$((cases + 1))
expect_real_fail source-not-in-commit 'packed source is not a file of the candidate commit: NOT-IN-THE-COMMIT.md' "$work/source-not-in-commit" "$real/repo"

# `--candidate-repo` with a build. Run from the candidate's own checkout with real
# inputs, so that nothing but the flag itself can refuse it: if the flag were
# accepted and ignored, this build would succeed.
set +e
repo_without_verify="$(cd "$real/repo" && python3 tooling/build-evidence-pack.py --manifest "$real/hosted/assurance-manifest.json" --receipts "$real/hosted/assurance-receipts.json" --output "$work/fresh-pack" --candidate-repo "$real/repo" 2>&1)"
repo_without_verify_rc=$?
set -e
cases=$((cases + 1))
if [ "$repo_without_verify_rc" -eq 0 ] || ! printf '%s' "$repo_without_verify" | grep -qF -- '--candidate-repo is only for --verify'; then
  echo "WRONG  candidate-repo-without-verify: $repo_without_verify" >&2
  exit 1
fi

# ---- rebuilding a candidate from public inputs -----------------------------
# `reproduce-evidence.py` rebuilds the manifest and the pack with the candidate
# commit's own builders from the receipts and compares byte for byte.
reproduce() {
  python3 "$root/tooling/reproduce-evidence.py" "$@"
}
expect_reproduced() {
  local name="$1"
  shift
  cases=$((cases + 1))
  if ! reproduce "$@" >"$work/reproduce.out" 2>&1; then
    echo "WRONG  $name: an honest candidate did not reproduce:" >&2
    cat "$work/reproduce.out" >&2
    return 1
  fi
}
expect_not_reproduced() {
  local name="$1" needle="$2" out rc
  shift 2
  cases=$((cases + 1))
  set +e
  out="$(reproduce "$@" 2>&1)"
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
no_worktrees_left() {
  [ "$(git -C "$1" worktree list | wc -l | tr -d ' ')" = "1" ]
}
expect_reproduced reproduce-pack-and-hosted --pack "$real/pack" --hosted "$real/hosted" --repo "$real/repo"
expect_reproduced reproduce-pack-alone --pack "$real/pack" --repo "$real/repo"
expect_reproduced reproduce-hosted-alone --hosted "$real/hosted" --repo "$real/repo"
expect_reproduced reproduce-pull-request --pack "$work/real-pull-request/pack" --hosted "$work/real-pull-request/hosted" --repo "$work/real-pull-request/repo"
cases=$((cases + 1))
no_worktrees_left "$real/repo" || { echo "WRONG  a reproduction left a worktree in the repository" >&2; exit 1; }
git -C "$real/repo" status --short --ignored | grep -v '^!! .assurance/$' && { echo "WRONG  a reproduction changed the repository" >&2; exit 1; }

# A reproduction leaves the repository as it found it even when the interpreter is
# allowed to write bytecode (the runner sets PYTHONDONTWRITEBYTECODE, which the
# first runs here rely on): the loaded builders must not leave a cache in the tree.
cases=$((cases + 1))
env -u PYTHONDONTWRITEBYTECODE -u PYTHONPYCACHEPREFIX python3 -X pycache_prefix= "$real/repo/tooling/reproduce-evidence.py" --pack "$real/pack" --hosted "$real/hosted" --repo "$real/repo" >/dev/null
if git -C "$real/repo" status --short --ignored | grep -v '^!! .assurance/$'; then
  echo "WRONG  a reproduction with bytecode writing allowed changed the repository" >&2
  exit 1
fi
# ...and removes its scratch directory.
mkdir "$work/reproduce-tmp"
cases=$((cases + 1))
TMPDIR="$work/reproduce-tmp" python3 "$root/tooling/reproduce-evidence.py" --pack "$real/pack" --hosted "$real/hosted" --repo "$real/repo" >/dev/null
if [ -n "$(ls -A "$work/reproduce-tmp")" ]; then
  echo "WRONG  a reproduction left its scratch directory: $(ls "$work/reproduce-tmp")" >&2
  exit 1
fi

expect_not_reproduced reproduce-nothing 'give --pack, --hosted or both'
expect_not_reproduced reproduce-pack-forged-source 'packed source differs from the candidate commit: ASSURANCE.md' --pack "$work/forged-source" --repo "$real/repo"
expect_not_reproduced reproduce-pack-wrong-repository 'is not in the repository' --pack "$real/pack" --repo "$work/real-pull-request/repo"
expect_not_reproduced reproduce-pack-unreadable 'cannot read pack manifest' --pack "$work/no-such-pack" --repo "$real/repo"
cases=$((cases + 1))
no_worktrees_left "$real/repo" || { echo "WRONG  a refused reproduction left a worktree in the repository" >&2; exit 1; }

cp -R "$real/pack" "$work/real-tampered"
printf '\n' >> "$work/real-tampered/assurance-receipts.json"
expect_not_reproduced reproduce-pack-tampered 'pack digest mismatch: assurance-receipts.json' --pack "$work/real-tampered" --repo "$real/repo"
cp -R "$real/hosted" "$work/hosted-wrong-tree"
python3 - "$work/hosted-wrong-tree/assurance-receipts.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
data["candidate"]["tree"] = "c" * 40
path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
PY
expect_not_reproduced hosted-names-another-tree 'the candidate tree is not the tree of the candidate commit' --hosted "$work/hosted-wrong-tree" --repo "$real/repo"

# The hosted artifact is not the one the pack holds.
cp -R "$real/hosted" "$work/hosted-reformatted"
python3 - "$work/hosted-reformatted/assurance-manifest.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
path.write_text(json.dumps(json.loads(path.read_text())) + "\n")
PY
expect_not_reproduced hosted-not-the-packed-manifest 'the hosted assurance-manifest.json is not the one in the pack' --pack "$real/pack" --hosted "$work/hosted-reformatted" --repo "$real/repo"
expect_not_reproduced hosted-manifest-not-the-rebuilt 'the manifest rebuilt from the receipts differs from the given manifest' --hosted "$work/hosted-reformatted" --repo "$real/repo"
cp -R "$real/hosted" "$work/hosted-other-receipts"
python3 - "$work/hosted-other-receipts/assurance-receipts.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
data["checks"][0]["command"] = "a different command"
path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
PY
expect_not_reproduced hosted-not-the-packed-receipts 'the hosted assurance-receipts.json is not the one in the pack' --pack "$real/pack" --hosted "$work/hosted-other-receipts" --repo "$real/repo"
expect_not_reproduced hosted-receipts-not-the-manifests 'the manifest rebuilt from the receipts differs from the given manifest' --hosted "$work/hosted-other-receipts" --repo "$real/repo"
expect_not_reproduced hosted-of-another-candidate 'names a different candidate than the pack' --pack "$real/pack" --hosted "$work/real-pull-request/hosted" --repo "$real/repo"
expect_not_reproduced hosted-unreadable 'cannot read hosted receipts' --hosted "$work/no-such-directory" --repo "$real/repo"
python3 - "$work/hosted-other-receipts/assurance-receipts.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
data["candidate"]["tree"] = "short"
path.write_text(json.dumps(data) + "\n")
PY
expect_not_reproduced hosted-candidate-malformed 'has no valid candidate commit and tree' --hosted "$work/hosted-other-receipts" --repo "$real/repo"

# A pack that verifies and whose parts agree, but is not what the builders write
# from its receipts: the index reformatted. Digests and contents all agree.
cp -R "$real/pack" "$work/pack-reformatted"
python3 - "$work/pack-reformatted" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1]) / "PACK-MANIFEST.json"
path.write_text(json.dumps(json.loads(path.read_text())) + "\n")
PY
python3 "$root/tooling/build-evidence-pack.py" --verify "$work/pack-reformatted" --candidate-repo "$real/repo" >/dev/null
cases=$((cases + 1))
expect_not_reproduced pack-not-what-the-builder-writes 'the rebuilt pack differs from the given pack in PACK-MANIFEST.json' --pack "$work/pack-reformatted" --repo "$real/repo"
# A file of the commit that the builder does not allowlist, added to the pack and
# listed. It verifies and it matches git; only the rebuild notices.
cp -R "$real/pack" "$work/pack-lists-an-extra-source"
python3 - "$work/pack-lists-an-extra-source" "$real/repo/.gitignore" <<'PY'
import hashlib, json, pathlib, shutil, sys
pack, committed = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
extra = pack / "source" / ".gitignore"
shutil.copyfile(committed, extra)
index_path = pack / "PACK-MANIFEST.json"
index = json.loads(index_path.read_text())
index["files"].append({"path": "source/.gitignore", "sha256": hashlib.sha256(extra.read_bytes()).hexdigest(), "bytes": extra.stat().st_size})
index_path.write_text(json.dumps(index, indent=2, sort_keys=True) + "\n")
PY
python3 "$root/tooling/build-evidence-pack.py" --verify "$work/pack-lists-an-extra-source" --candidate-repo "$real/repo" >/dev/null
cases=$((cases + 1))
expect_not_reproduced pack-with-a-source-the-builder-would-not-pack 'the rebuilt pack lists different files: source/.gitignore' --pack "$work/pack-lists-an-extra-source" --repo "$real/repo"
rm -rf "$work/pack-lists-an-extra-source" "$work/pack-reformatted"

# ---- publication to the archive, with a stand-in for the aws command ---------
# The archive's retention is COMPLIANCE, so an object cannot be deleted once
# written. `publish-evidence-archive.py` is therefore run here against a stub
# `aws` that records every call and fails in the ways S3 can, and the runner
# requires that nothing is uploaded for a pack that does not verify, that does
# not match git, or that has no receipt path, and that every upload asks S3 to
# refuse an existing key.
mkdir -p "$work/stub"
cat > "$work/stub/aws" <<'STUB'
#!/usr/bin/env bash
echo "$*" >> "$AWS_STUB_LOG"
case "$*" in *tacenta-core-assurance-evidence-238576302016*) echo "stub aws: refusing the real archive bucket" >&2; exit 2 ;; esac
mode="${AWS_STUB_MODE:-ok}"
case "$2" in
  put-object)
    count="$(grep -c ' put-object ' "$AWS_STUB_LOG")"
    if [ "$mode" = exists ]; then echo "An error occurred (PreconditionFailed) when calling the PutObject operation" >&2; exit 254; fi
    if [ "$mode" = partial ] && [ "$count" -ge 3 ]; then echo "An error occurred (RequestTimeout)" >&2; exit 254; fi
    if [ "$mode" = no-version ]; then echo '{}'; exit 0; fi
    if [ "$mode" = empty-version ]; then echo '{"VersionId": ""}'; exit 0; fi
    echo "{\"VersionId\": \"version-$count\"}"
    ;;
  get-object-retention)
    case "$mode" in
      governance) echo '{"Retention": {"Mode": "GOVERNANCE", "RetainUntilDate": "2033-01-01T00:00:00+00:00"}}' ;;
      no-retention) echo "An error occurred (AccessDenied)" >&2; exit 254 ;;
      retention-without-date) echo '{"Retention": {"Mode": "COMPLIANCE"}}' ;;
      *) echo '{"Retention": {"Mode": "COMPLIANCE", "RetainUntilDate": "2033-01-01T00:00:00+00:00"}}' ;;
    esac
    ;;
  *) echo "stub aws: unexpected call: $*" >&2; exit 2 ;;
esac
STUB
chmod +x "$work/stub/aws"
export AWS_STUB_LOG="$work/aws.log"
# The archive's retention is irreversible, so these cases are built to be unable
# to reach it: the stub must be the `aws` that runs (checked here, not assumed),
# and every call but the dry run names a bucket that is not the archive's, so
# that a real `aws` that ran by mistake would be refused by S3 for a bucket that
# does not exist.
stub_bucket=tacenta-evidence-cases-stub-bucket-that-does-not-exist
if [ "$(PATH="$work/stub:$PATH" command -v aws)" != "$work/stub/aws" ]; then
  echo "WRONG  the stand-in for aws is not the aws that would run; refusing to run the publisher cases" >&2
  exit 1
fi
publish() {
  # publish MODE ARGS...: runs the publisher with the stub first on PATH.
  local mode="$1" bucket_args="--bucket $stub_bucket"
  shift
  for argument in "$@"; do
    case "$argument" in --bucket|--dry-run) bucket_args="" ;; esac
  done
  : > "$AWS_STUB_LOG"
  # shellcheck disable=SC2086
  PATH="$work/stub:$PATH" AWS_STUB_MODE="$mode" python3 "$root/tooling/publish-evidence-archive.py" "$@" $bucket_args
}
expect_publish_fail() {
  local name="$1" needle="$2" calls="$3" out rc
  shift 3
  cases=$((cases + 1))
  set +e
  out="$(publish "$@" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $name: the publisher accepted it" >&2
    return 1
  fi
  if ! printf '%s' "$out" | grep -qF -- "$needle"; then
    echo "WRONG  $name: missing diagnostic '$needle'" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
  if [ "$(wc -l < "$AWS_STUB_LOG" | tr -d ' ')" != "$calls" ]; then
    echo "WRONG  $name: expected $calls aws calls, saw:" >&2
    cat "$AWS_STUB_LOG" >&2
    return 1
  fi
}
files_to_upload="$(python3 -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["files"]) + 1)' "$real/pack/PACK-MANIFEST.json")"
pack_digest="$(python3 -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$real/pack/PACK-MANIFEST.json")"
bucket=tacenta-core-assurance-evidence-238576302016   # the dry run only prints it

cases=$((cases + 1))
dry="$(publish ok --pack "$real/pack" --candidate-repo "$real/repo" --dry-run | tail -n 1)"
if [ "$dry" != "archive dry run: s3://$bucket/candidates/$real_commit/$pack_digest/ ($files_to_upload files)" ]; then
  echo "WRONG  publish-dry-run: $dry" >&2
  exit 1
fi
if [ -s "$AWS_STUB_LOG" ]; then
  echo "WRONG  publish-dry-run: the dry run called aws" >&2
  exit 1
fi

expect_publish_fail publish-needs-a-receipt '--receipt is required for publication' 0 ok --pack "$real/pack" --candidate-repo "$real/repo"
echo existing > "$work/existing-receipt.json"
expect_publish_fail publish-existing-receipt 'refusing to replace publication receipt' 0 ok --pack "$real/pack" --candidate-repo "$real/repo" --receipt "$work/existing-receipt.json"
expect_publish_fail publish-forged-source 'packed source differs from the candidate commit: ASSURANCE.md' 0 ok --pack "$work/forged-source" --candidate-repo "$real/repo" --receipt "$work/forged.json"
expect_publish_fail publish-forged-source-refused 'evidence pack did not verify' 0 ok --pack "$work/forged-source" --candidate-repo "$real/repo" --receipt "$work/forged.json"
expect_publish_fail publish-tampered-pack 'pack digest mismatch: source/ASSURANCE.md' 0 ok --pack "$work/tampered" --candidate-repo "$real/repo" --receipt "$work/tampered.json"
expect_publish_fail publish-pack-of-another-commit 'is not in the repository' 0 ok --pack "$real/pack" --candidate-repo "$work/real-pull-request/repo" --receipt "$work/other.json"
expect_publish_fail publish-default-repository-is-this-checkout 'is not in the repository' 0 ok --pack "$real/pack" --receipt "$work/default.json"
for refused in forged tampered other default; do
  if [ -e "$work/$refused.json" ]; then
    echo "WRONG  publish-$refused: a receipt was written for a refused publication" >&2
    exit 1
  fi
done

expect_publish_fail publish-key-exists 'upload refused for candidates/' 1 exists --pack "$real/pack" --candidate-repo "$real/repo" --receipt "$work/exists.json"
expect_publish_fail publish-cut-short 'upload refused for candidates/' 5 partial --pack "$real/pack" --candidate-repo "$real/repo" --receipt "$work/partial.json"
expect_publish_fail publish-empty-version-id 'returned no version ID for candidates/' 1 empty-version --pack "$real/pack" --candidate-repo "$real/repo" --receipt "$work/empty-version.json"
expect_publish_fail publish-no-version-id 'returned no version ID for candidates/' 1 no-version --pack "$real/pack" --candidate-repo "$real/repo" --receipt "$work/no-version.json"
expect_publish_fail publish-governance-retention 'upload lacks Compliance retention for candidates/' 2 governance --pack "$real/pack" --candidate-repo "$real/repo" --receipt "$work/governance.json"
expect_publish_fail publish-retention-unreadable 'cannot read retention for candidates/' 2 no-retention --pack "$real/pack" --candidate-repo "$real/repo" --receipt "$work/no-retention.json"
expect_publish_fail publish-retention-without-date 'upload lacks Compliance retention for candidates/' 2 retention-without-date --pack "$real/pack" --candidate-repo "$real/repo" --receipt "$work/no-date.json"
for refused in exists partial no-version empty-version governance no-retention no-date; do
  if [ -e "$work/$refused.json" ]; then
    echo "WRONG  publish-$refused: a receipt was written for a failed publication" >&2
    exit 1
  fi
done

cases=$((cases + 1))
publish ok --pack "$real/pack" --candidate-repo "$real/repo" --receipt "$work/published.json" >/dev/null
python3 - "$work/published.json" "$AWS_STUB_LOG" "$real_commit" "$pack_digest" "$files_to_upload" "$stub_bucket" <<'PY'
import json, sys
receipt = json.load(open(sys.argv[1]))
log = open(sys.argv[2]).read().splitlines()
commit, digest, count, bucket = sys.argv[3], sys.argv[4], int(sys.argv[5]), sys.argv[6]
prefix = f"candidates/{commit}/{digest}"
assert receipt["schema_version"] == 1 and receipt["bucket"] == bucket and receipt["prefix"] == prefix, receipt
assert receipt["candidate"]["commit"] == commit and receipt["pack_manifest_sha256"] == digest, receipt
objects = receipt["objects"]
assert len(objects) == count, (len(objects), count)
assert all(o["key"].startswith(prefix + "/") and o["retention"]["Mode"] == "COMPLIANCE" and o["version_id"] for o in objects)
assert len({o["key"] for o in objects}) == count
assert objects[-1]["key"] == prefix + "/PACK-MANIFEST.json", objects[-1]
puts = [line for line in log if " put-object " in " " + line + " "]
assert len(puts) == count, len(puts)
for line in puts:
    assert "--if-none-match *" in line and f"--bucket {bucket}" in line, line
reads = [line for line in log if line.startswith("s3api get-object-retention")]
assert len(reads) == count and all("--version-id version-" in line for line in reads), reads
PY
cases=$((cases + 1))
publish ok --pack "$real/pack" --candidate-repo "$real/repo" --bucket another-bucket --receipt "$work/other-bucket.json" >/dev/null
python3 - "$work/other-bucket.json" "$AWS_STUB_LOG" <<'PY'
import json, sys
assert json.load(open(sys.argv[1]))["bucket"] == "another-bucket"
assert all("--bucket another-bucket" in line for line in open(sys.argv[2]) if " put-object " in " " + line)
PY

echo "build-evidence-pack-cases: $cases cases gave the expected result (honest push and pull-request packs verified; each refusal is one change to an honest pack)"
