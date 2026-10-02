#!/usr/bin/env bash
# Exercise the review-receipt checker, the section tool that writes its template,
# and the check that binds a reviewed receipt, pack and manifest to one candidate.
#
# The pack is a real one: made by the production tools in a small git repository
# (`tests/make-candidate.py`), so its copy of `CLAIMS.md` is the repository's. The
# honest receipt is the section tool's template with every placeholder filled the
# way a reader would, and each refusal is one change to it. The receipts here are
# made up by this runner; none is a review.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
export PYTHONDONTWRITEBYTECODE=1
cases=0

# must DESCRIPTION COMMAND...: the command has to succeed, or the runner says which check failed.
must() {
  local description="$1"
  shift
  cases=$((cases + 1))
  if ! "$@"; then
    echo "WRONG  $description" >&2
    return 1
  fi
}

python3 "$here/make-candidate.py" "$root" "$work/candidate" --event push
pack="$work/candidate/pack"
repo="$work/candidate/repo"
checker="$root/tooling/check-ledger-review-receipt.py"
sections_tool="$root/tooling/ledger-review-sections.py"

# ---- the section tool and the honest receipt ---------------------------------
python3 "$sections_tool" --pack "$pack" --template "$work/template.json" >/dev/null
cases=$((cases + 1))
python3 - "$work/template.json" "$pack/source/tacenta-proofs/CLAIMS.md" <<'PY'
import json, re, sys
template = json.load(open(sys.argv[1]))
text = open(sys.argv[2]).read()
headings = re.findall(r"^## (.+)$", text, re.M)
refs = [c["reference"] for c in template["claims"]]
assert refs[0].startswith("Introduction") and refs[1:] == [h.rstrip() for h in headings], refs
assert template["schema_version"] == 2 and len(set(refs)) == len(refs)
assert all(len(c["section_sha256"]) == 64 for c in template["claims"])
PY

# fill PROGRAM_FILE OUT: the template, filled in as a reader would, then changed
# by the Python in PROGRAM_FILE (which sees the receipt as `r`).
fill() {
  python3 - "$work/template.json" "$2" "$1" <<'PY'
import json, pathlib, sys
r = json.loads(pathlib.Path(sys.argv[1]).read_text())
program = pathlib.Path(sys.argv[3]).read_text()
r["reviewer"] = {"identity": "A. Reader", "independence_statement": "Did not write the ledger."}
r["artifacts_read"] = ["tacenta-proofs/CLAIMS.md and tacenta-proofs/LIMITATIONS.md",
                       "tacenta-proofs/manifests/verification-manifest.json",
                       "tacenta-spec/security-properties/evidence-index.json",
                       "ASSURANCE.md", "ASSURANCE-OBLIGATIONS.md", "GAP-REGISTER.md",
                       "tacenta-model/P6-L2-TARGET-DECISION.md", "tacenta-proofs/PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md"]
for c in r["claims"]:
    c["disposition"], c["finding"] = "accepted", "Read; the cited theorems and limits match."
exec(program, {"r": r, "json": json})
pathlib.Path(sys.argv[2]).write_text(json.dumps(r, indent=2) + "\n")
PY
}

# receipt NAME 'python that changes r'
receipt() {
  printf '%s\n' "${2:-pass}" > "$work/$1.py"
  fill "$work/$1.py" "$work/$1.json"
}

run_checker() {
  python3 "$checker" --receipt "$1" --pack "${3:-$pack}" ${2:+"$2"}
}

expect_pass() {
  local name="$1" option="${2:-}"
  cases=$((cases + 1))
  if ! run_checker "$work/$name.json" "$option" >"$work/$name.out" 2>&1; then
    echo "WRONG  $name: an honest receipt was refused:" >&2
    cat "$work/$name.out" >&2
    return 1
  fi
}

# refuse NAME NEEDLE 'python that changes r' [PACK] [OPTION]
refuse() {
  local name="$1" needle="$2" out rc
  receipt "$name" "$3"
  cases=$((cases + 1))
  set +e
  out="$(run_checker "$work/$name.json" "${5:-}" "${4:-$pack}" 2>&1)"
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

receipt pass
expect_pass pass
count="$(python3 -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["claims"]))' "$work/pass.json")"
must "the honest receipt reports its $count dispositions" grep -qF "binds $count claim disposition(s)" "$work/pass.out"

# A receipt the reader marked up with findings and limits is still a receipt,
# and is accepted unless findings are refused.
receipt with-limits "r['claims'][1].update(disposition='accepted-with-limit', finding='Scope is the model only.')"
expect_pass with-limits
receipt with-finding "r['claims'][2].update(disposition='finding', finding='The statement is stronger than its theorem.')"
expect_pass with-finding
refuse finding-refused 'review receipt records 1 finding(s):' "r['claims'][2].update(disposition='finding', finding='x')" "$pack" --require-no-findings
receipt limit-passes-strict "r['claims'][1].update(disposition='accepted-with-limit', finding='Scope is the model only.')"
must "a limit is not a finding" run_checker "$work/limit-passes-strict.json" --require-no-findings >/dev/null

# ---- binding ----------------------------------------------------------------
refuse foreign 'candidate does not match evidence pack' "r['candidate']['commit'] = 'c' * 40"
refuse wrong-pack 'does not bind the evidence-pack manifest' "r['evidence_pack']['manifest_sha256'] = '0' * 64"
refuse no-pack-binding 'does not bind the evidence-pack manifest' "r['evidence_pack'] = {}"
refuse pack-binding-absent 'review receipt fields are wrong: missing evidence_pack' "del r['evidence_pack']"
refuse schema-one 'review receipt schema_version must be 2' "r['schema_version'] = 1"
refuse schema-two-point-zero 'review receipt schema_version must be 2' "r['schema_version'] = 2.0"
refuse unknown-field 'review receipt fields are wrong: unknown approved' "r['approved'] = True"
refuse missing-field 'review receipt fields are wrong: missing claims' "del r['claims']"
refuse placeholder 'still holds a template placeholder' "r['reviewer']['identity'] = 'REPLACE_WITH_REVIEWER_IDENTITY'"
refuse placeholder-in-a-finding 'still holds a template placeholder' "r['claims'][3]['finding'] = 'REPLACE_WITH_THE_SECTION_FINDING'"

# ---- the reader ---------------------------------------------------------------
refuse missing-reviewer 'lacks reviewer identity or independence statement' "r['reviewer'] = {}"
refuse blank-independence 'lacks reviewer identity or independence statement' "r['reviewer']['independence_statement'] = '  '"
refuse reviewer-not-an-object 'lacks reviewer identity or independence statement' "r['reviewer'] = 'A. Reader'"
refuse no-artifacts 'review receipt must list artifacts read' "r['artifacts_read'] = []"
refuse artifacts-not-strings 'review receipt must list artifacts read' "r['artifacts_read'] = [1]"
refuse artifact-unnamed 'does not name these artifacts read: GAP-REGISTER.md' "r['artifacts_read'] = [a for a in r['artifacts_read'] if 'GAP-REGISTER' not in a]"
refuse several-artifacts-unnamed 'does not name these artifacts read: ASSURANCE.md, ASSURANCE-OBLIGATIONS.md, GAP-REGISTER.md' "r['artifacts_read'] = [a for a in r['artifacts_read'] if 'ASSURANCE' not in a and 'GAP' not in a]"
for artifact in CLAIMS.md LIMITATIONS.md verification-manifest.json evidence-index.json P6-L2-TARGET-DECISION.md PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md; do
  refuse "unnamed-$artifact" "does not name these artifacts read: $artifact" "r['artifacts_read'] = [a.replace('$artifact', '') for a in r['artifacts_read']]"
done
refuse placeholder-in-artifacts 'still holds a template placeholder' "r['artifacts_read'].append('REPLACE_WITH_X')"
refuse placeholder-in-notes 'still holds a template placeholder' "r['cross_cutting_notes'] = ['REPLACE_WITH_X']"
refuse notes-malformed 'cross_cutting_notes must be a list of non-empty strings' "r['cross_cutting_notes'] = ['']"
receipt with-notes "r['cross_cutting_notes'] = ['Scope: this receipt is for one candidate.']"
expect_pass with-notes

# ---- the dispositions ---------------------------------------------------------
refuse no-claims 'review receipt must contain claim dispositions' "r['claims'] = []"
refuse claim-not-an-object 'review receipt has invalid claim disposition' "r['claims'][0] = 'accepted'"
refuse claim-extra-field 'review receipt has invalid claim disposition' "r['claims'][0]['note'] = 'x'"
refuse claim-without-digest 'review receipt has invalid claim disposition' "del r['claims'][0]['section_sha256']"
refuse duplicate-reference 'review receipt has duplicate or invalid claim reference' "r['claims'][1]['reference'] = r['claims'][0]['reference']"
refuse empty-reference 'review receipt has duplicate or invalid claim reference' "r['claims'][1]['reference'] = ''"
refuse invalid-disposition 'review receipt has invalid disposition for' "r['claims'][1]['disposition'] = 'approved'"
refuse accepted-without-text 'gives no finding text for accepted on' "r['claims'][1]['finding'] = ''"
refuse duplicate-exact 'duplicate or invalid claim reference' "r['claims'].append(dict(r['claims'][3]))"
refuse unknown-disposition-with-text 'invalid disposition for' "r['claims'][1].update(disposition='rejected', finding='x')"
refuse disposition-not-a-string 'invalid disposition for' "r['claims'][1]['disposition'] = ['accepted']"
refuse claim-entry-fields 'each entry has exactly the fields' "del r['claims'][0]['section_sha256']"
refuse finding-not-text 'review receipt has invalid finding for' "r['claims'][1]['finding'] = None"
refuse limit-without-text 'review receipt gives no finding text for accepted-with-limit on' "r['claims'][1].update(disposition='accepted-with-limit', finding='  ')"
refuse finding-without-text 'review receipt gives no finding text for finding on' "r['claims'][1].update(disposition='finding', finding='')"
refuse unknown-section 'review receipt names a section CLAIMS.md does not have: Invented section' "r['claims'][1]['reference'] = 'Invented section'"
refuse digest-malformed 'review receipt has no valid section_sha256 for' "r['claims'][1]['section_sha256'] = 'abc'"
refuse digest-not-text 'review receipt has no valid section_sha256 for' "r['claims'][1]['section_sha256'] = 7"
refuse digest-of-another-section 'was not given on the text the pack holds (section_sha256 differs)' "r['claims'][1]['section_sha256'] = r['claims'][2]['section_sha256']"
refuse digest-uppercase 'review receipt has no valid section_sha256 for' "r['claims'][1]['section_sha256'] = r['claims'][1]['section_sha256'].upper()"
refuse one-section-missing 'review receipt has no disposition for 1 CLAIMS.md section(s): ' "del r['claims'][5]"
refuse introduction-missing 'review receipt has no disposition for 1 CLAIMS.md section(s): Introduction' "del r['claims'][0]"
refuse several-sections-missing 'section(s): ' "r['claims'] = r['claims'][:3]"
refuse one-disposition-only 'review receipt has no disposition for' "r['claims'] = r['claims'][:1]"

# ---- the pack the receipt is checked against -----------------------------------
# forge_claims PACK PROGRAM: change the pack's CLAIMS.md with Python (text in
# `text`, result in `text`), keeping the pack manifest's digest for it current.
forge_claims() {
  python3 - "$1" "$2" <<'PY'
import hashlib, json, pathlib, sys
pack, program = pathlib.Path(sys.argv[1]), sys.argv[2]
target = pack / "source/tacenta-proofs/CLAIMS.md"
scope = {"text": target.read_text()}
exec(program, scope)
target.write_text(scope["text"])
index_path = pack / "PACK-MANIFEST.json"
index = json.loads(index_path.read_text())
for entry in index["files"]:
    if entry["path"] == "source/tacenta-proofs/CLAIMS.md":
        entry["sha256"], entry["bytes"] = hashlib.sha256(target.read_bytes()).hexdigest(), target.stat().st_size
index_path.write_text(json.dumps(index, indent=2, sort_keys=True) + "\n")
PY
}
rebind() {
  python3 - "$1" "$2" <<'PY'
import hashlib, json, pathlib, sys
receipt_path, pack = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
r = json.loads(receipt_path.read_text())
r["evidence_pack"]["manifest_sha256"] = hashlib.sha256((pack / "PACK-MANIFEST.json").read_bytes()).hexdigest()
receipt_path.write_text(json.dumps(r, indent=2) + "\n")
PY
}
# craft_receipt PACK OUT: a receipt for the pack's own copy of the ledger, bound to the
# pack's manifest as it is, with the section digests worked out here (the last section
# of a title wins) and not by the tool under test. It is what a receipt written for an
# altered pack would carry, so only a check of the pack itself can refuse it.
craft_receipt() {
  python3 - "$1" "$2" "$work/pass.json" <<'PY'
import hashlib, json, pathlib, re, sys
pack, out, base = map(pathlib.Path, sys.argv[1:4])
text = (pack / "source/tacenta-proofs/CLAIMS.md").read_bytes().decode("utf-8")
matches = list(re.finditer(r"^## (.+)$", text, re.M))
sections = {}
def add(title, body):
    sections[title] = hashlib.sha256(body.encode()).hexdigest()
add("Introduction (the text before the first section)", text[: matches[0].start() if matches else len(text)])
for index, match in enumerate(matches):
    end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
    add(match.group(1).rstrip(), text[match.start():end])
r = json.loads(base.read_text())
manifest = (pack / "PACK-MANIFEST.json")
r["candidate"] = json.loads(manifest.read_text())["candidate"]
r["evidence_pack"] = {"manifest_sha256": hashlib.sha256(manifest.read_bytes()).hexdigest()}
r["claims"] = [{"reference": title, "disposition": "accepted", "finding": "Read; the cited theorems and limits match.",
                "section_sha256": digest} for title, digest in sections.items()]
out.write_text(json.dumps(r, indent=2) + "\n")
PY
}
expect_refused_for_pack() {
  local name="$1" needle="$2" packdir="$3" out rc
  cases=$((cases + 1))
  set +e
  out="$(run_checker "$work/$name.json" "" "$packdir" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ] || ! printf '%s' "$out" | grep -qF -- "$needle"; then
    echo "WRONG  $name: expected '$needle', got rc=$rc: $out" >&2
    return 1
  fi
}

# The pack's copy of the ledger no longer matches the pack manifest.
cp -R "$pack" "$work/pack-tampered"
printf '\nA line added after the pack was made.\n' >> "$work/pack-tampered/source/tacenta-proofs/CLAIMS.md"
receipt tampered-ledger "r['evidence_pack']['manifest_sha256'] = '$(python3 -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$work/pack-tampered/PACK-MANIFEST.json")'"
expect_refused_for_pack tampered-ledger 'evidence pack copy of CLAIMS.md does not match the pack manifest' "$work/pack-tampered"
craft_receipt "$work/pack-tampered" "$work/tampered-ledger-crafted.json"
expect_refused_for_pack tampered-ledger-crafted 'evidence pack copy of CLAIMS.md does not match the pack manifest' "$work/pack-tampered"

# The ledger changed in the pack, with every digest brought up to date: a
# receipt given on the old text no longer matches the changed section.
cp -R "$pack" "$work/pack-changed"
forge_claims "$work/pack-changed" "text = text.replace('Exactly what is proven', 'Exactly what is claimed', 1)"
receipt changed-ledger 'pass'
rebind "$work/changed-ledger.json" "$work/pack-changed"
expect_refused_for_pack changed-ledger 'review receipt disposition for Introduction (the text before the first section) was not given on the text the pack holds' "$work/pack-changed"

# A section added after the review has no disposition.
cp -R "$pack" "$work/pack-grown"
forge_claims "$work/pack-grown" "text = text.replace('## Read this first', '## A section added after the review\n\nA claim.\n\n## Read this first', 1)"
receipt grown-ledger 'pass'
rebind "$work/grown-ledger.json" "$work/pack-grown"
expect_refused_for_pack grown-ledger 'review receipt has no disposition for 1 CLAIMS.md section(s): A section added after the review' "$work/pack-grown"

# A change inside a section, at the last byte of the last section, or the removal of
# the last byte of the introduction (changing it would join the next heading to the
# line), with every digest of the pack brought up to date, no longer matches the
# digest the receipt carries.
digest_case() {
  cp -R "$pack" "$work/pack-$1"
  forge_claims "$work/pack-$1" "$2"
  receipt "digest-$1" 'pass'
  rebind "$work/digest-$1.json" "$work/pack-$1"
  expect_refused_for_pack "digest-$1" 'was not given on the text the pack holds' "$work/pack-$1"
}
digest_case middle "import re; ms = list(re.finditer(r'^## ', text, re.M)); k = (ms[len(ms) // 2].start() + ms[len(ms) // 2 + 1].start()) // 2; text = text[:k] + 'X' + text[k:]"
digest_case last-byte-of-last "text = text[:-1] + 'Z'"
# A ledger with no section at all is one introduction, whose last byte can be anything:
# a change to that byte alone must no longer match. (With a section after it, the last byte
# of the introduction is the newline that puts the heading at the start of a line, so it
# cannot be changed without changing the sections.)
cp -R "$pack" "$work/pack-only-introduction"
forge_claims "$work/pack-only-introduction" "text = '# Claims\n\nOnly an introduction, with no section.\n'"
craft_receipt "$work/pack-only-introduction" "$work/only-introduction.json"
cp -R "$pack" "$work/pack-only-introduction-changed"
forge_claims "$work/pack-only-introduction-changed" "text = '# Claims\n\nOnly an introduction, with no section.Z'"
rebind "$work/only-introduction.json" "$work/pack-only-introduction-changed"
expect_refused_for_pack only-introduction 'was not given on the text the pack holds' "$work/pack-only-introduction-changed"
cp "$work/only-introduction.json" "$work/only-introduction-honest.json"
rebind "$work/only-introduction-honest.json" "$work/pack-only-introduction"
cases=$((cases + 1))
python3 "$checker" --receipt "$work/only-introduction-honest.json" --pack "$work/pack-only-introduction" >/dev/null
digest_case last-byte-of-introduction "import re; a = re.search(r'^## ', text, re.M).start(); text = text[:a - 1] + text[a:]"

# Two sections with one title: a reference could not say which was read.
cp -R "$pack" "$work/pack-twice"
forge_claims "$work/pack-twice" "import re; first = re.search(r'^## (.+)$', text, re.M).group(0); text = text + '\n' + first + '\n\nA second section with the same title.\n'"
craft_receipt "$work/pack-twice" "$work/twice-ledger.json"
expect_refused_for_pack twice-ledger 'CLAIMS.md has two sections titled' "$work/pack-twice"

# A ledger with Windows line endings: the digests are of the bytes, so the
# template, a filled receipt and the checker agree, and the digests differ from
# the same text with Unix line endings.
cp -R "$pack" "$work/pack-crlf"
forge_claims "$work/pack-crlf" "text = text.replace('\n', '\r\n')"
python3 "$sections_tool" --pack "$work/pack-crlf" --template "$work/template-crlf.json" >/dev/null
fill_for_template() {
  python3 - "$1" "$2" <<'PY'
import json, pathlib, sys
r = json.loads(pathlib.Path(sys.argv[1]).read_text())
r["reviewer"] = {"identity": "A. Reader", "independence_statement": "Did not write the ledger."}
r["artifacts_read"] = ["CLAIMS.md LIMITATIONS.md verification-manifest.json evidence-index.json ASSURANCE.md ASSURANCE-OBLIGATIONS.md GAP-REGISTER.md P6-L2-TARGET-DECISION.md PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md"]
for c in r["claims"]:
    c["disposition"], c["finding"] = "accepted", "Read; the cited theorems and limits match."
pathlib.Path(sys.argv[2]).write_text(json.dumps(r, indent=2) + "\n")
PY
}
fill_for_template "$work/template-crlf.json" "$work/crlf.json"
cases=$((cases + 1))
python3 "$checker" --receipt "$work/crlf.json" --pack "$work/pack-crlf" >/dev/null
must "line endings are part of a section's digest" python3 - "$work/crlf.json" "$work/pass.json" <<'PY'
import json, sys
a, b = (json.load(open(p))["claims"] for p in sys.argv[1:3])
assert [c["reference"] for c in a] == [c["reference"] for c in b]
assert all(x["section_sha256"] != y["section_sha256"] for x, y in zip(a, b))
PY

# The pack manifest lists the ledger twice.
cp -R "$pack" "$work/pack-ledger-twice"
python3 - "$work/pack-ledger-twice" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1]) / "PACK-MANIFEST.json"
d = json.loads(path.read_text())
d["files"].append(dict(next(e for e in d["files"] if e["path"] == "source/tacenta-proofs/CLAIMS.md")))
path.write_text(json.dumps(d, indent=2, sort_keys=True) + "\n")
PY
craft_receipt "$work/pack-ledger-twice" "$work/ledger-twice.json"
expect_refused_for_pack ledger-twice 'evidence pack has no source/tacenta-proofs/CLAIMS.md' "$work/pack-ledger-twice"

# The pack has no copy of the ledger.
cp -R "$pack" "$work/pack-without"
python3 - "$work/pack-without" <<'PY'
import json, pathlib, sys
pack = pathlib.Path(sys.argv[1])
(pack / "source/tacenta-proofs/CLAIMS.md").unlink()
index_path = pack / "PACK-MANIFEST.json"
index = json.loads(index_path.read_text())
index["files"] = [e for e in index["files"] if e["path"] != "source/tacenta-proofs/CLAIMS.md"]
index_path.write_text(json.dumps(index, indent=2, sort_keys=True) + "\n")
PY
receipt without-ledger 'pass'
rebind "$work/without-ledger.json" "$work/pack-without"
expect_refused_for_pack without-ledger 'evidence pack has no source/tacenta-proofs/CLAIMS.md' "$work/pack-without"

# The pack manifest itself.
mkdir "$work/pack-bad-manifest"
printf '[]\n' > "$work/pack-bad-manifest/PACK-MANIFEST.json"
cp "$work/pass.json" "$work/unreadable-pack.json"
cp "$work/pass.json" "$work/pack-schema.json"
expect_refused_for_pack unreadable-pack 'pack manifest must be an object' "$work/pack-bad-manifest"
cp -R "$pack" "$work/pack-schema"
python3 - "$work/pack-schema/PACK-MANIFEST.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
d = json.loads(path.read_text()); d["schema_version"] = 2
path.write_text(json.dumps(d, indent=2, sort_keys=True) + "\n")
PY
rebind "$work/pack-schema.json" "$work/pack-schema"
expect_refused_for_pack pack-schema 'pack manifest has invalid schema or candidate' "$work/pack-schema"

# ---- the section tool -----------------------------------------------------------
tool() {
  python3 "$sections_tool" "$@"
}
expect_tool_fail() {
  local name="$1" needle="$2" out rc
  shift 2
  cases=$((cases + 1))
  set +e
  out="$(tool "$@" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ] || ! printf '%s' "$out" | grep -qF -- "$needle"; then
    echo "WRONG  $name: expected '$needle', got rc=$rc: $out" >&2
    return 1
  fi
}
last_line_has() { [ "$(printf '%s\n' "$1" | tail -n 1 | grep -cF -- "$2")" = 1 ]; }
has_line() { [ "$(printf '%s\n' "$1" | grep -cF -- "$2")" -ge 1 ]; }
must "the listing ends with the section count" last_line_has "$(tool --pack "$pack")" "ledger review sections: $count section(s)"

# An unfilled template is not a receipt.
cases=$((cases + 1))
set +e
unfilled="$(run_checker "$work/template.json" 2>&1)"
unfilled_rc=$?
set -e
if [ "$unfilled_rc" -eq 0 ] || ! printf '%s' "$unfilled" | grep -qF 'still holds a template placeholder'; then
  echo "WRONG  unfilled-template: $unfilled" >&2
  exit 1
fi
expect_tool_fail template-exists 'refusing to replace' --pack "$pack" --template "$work/template.json"
expect_tool_fail template-with-since '--template and --since cannot be combined' --pack "$pack" --template "$work/t2.json" --since "$pack"
expect_tool_fail tool-pack-unreadable 'cannot read pack manifest' --pack "$work/no-such-pack"

# --since: the pack against itself, and against changed and grown ledgers.
same="$(tool --pack "$pack" --since "$pack")"
must "a pack against itself has no change" last_line_has "$same" "$count section(s): $count unchanged, 0 changed, 0 new; 0 earlier section(s) gone"
changed="$(tool --pack "$work/pack-changed" --since "$pack")"
must "an edited section is reported changed" has_line "$changed" 'changed   Introduction (the text before the first section)'
must "one section changed in the count" last_line_has "$changed" "$((count - 1)) unchanged, 1 changed, 0 new; 0 earlier section(s) gone"
grown="$(tool --pack "$work/pack-grown" --since "$pack")"
must "an added section is reported new" has_line "$grown" 'new       A section added after the review'
must "one section new in the count" last_line_has "$grown" "$count unchanged, 0 changed, 1 new; 0 earlier section(s) gone"
shrunk="$(tool --pack "$pack" --since "$work/pack-grown")"
must "a removed section is reported gone" has_line "$shrunk" 'gone      A section added after the review'
must "a receipt of schema 2 serves as the earlier state" last_line_has "$(tool --pack "$pack" --since "$work/pass.json")" "$count unchanged, 0 changed, 0 new"
must "an earlier CLAIMS.md file serves as the earlier state" last_line_has "$(tool --pack "$work/pack-changed" --since "$pack/source/tacenta-proofs/CLAIMS.md")" "1 changed"
python3 - "$work/pass.json" "$work/schema-one-receipt.json" <<'PY'
import json, pathlib, sys
d = json.loads(pathlib.Path(sys.argv[1]).read_text()); d["schema_version"] = 1
pathlib.Path(sys.argv[2]).write_text(json.dumps(d))
PY
expect_tool_fail since-schema-one 'is not schema 2 and records no section digests' --pack "$pack" --since "$work/schema-one-receipt.json"

# ---- reviewed evidence: manifest, pack and receipt bind one candidate ---------
# Run from the candidate's own checkout, as the release operator does: the
# manifest is validated against that checkout and the pack is held to its git.
reviewed() {
  (cd "$repo" && python3 tooling/validate-reviewed-evidence.py "$@")
}
expect_reviewed_fail() {
  local name="$1" needle="$2" out rc
  shift 2
  cases=$((cases + 1))
  set +e
  out="$(reviewed "$@" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ] || ! printf '%s' "$out" | grep -qF -- "$needle"; then
    echo "WRONG  $name: expected '$needle', got rc=$rc: $out" >&2
    return 1
  fi
}
hosted="$work/candidate/hosted"
cases=$((cases + 1))
reviewed --manifest "$hosted/assurance-manifest.json" --pack "$pack" --receipt "$work/pass.json" >"$work/reviewed.out"
must "the honest candidate is reviewed" grep -qF 'reviewed evidence: manifest, pack and review receipt bind one candidate' "$work/reviewed.out"
expect_reviewed_fail reviewed-with-a-finding 'review receipt records 1 finding(s)' --manifest "$hosted/assurance-manifest.json" --pack "$pack" --receipt "$work/with-finding.json"
expect_reviewed_fail reviewed-receipt-unbound 'does not bind the evidence-pack manifest' --manifest "$hosted/assurance-manifest.json" --pack "$pack" --receipt "$work/wrong-pack.json"
expect_reviewed_fail reviewed-receipt-foreign 'candidate does not match evidence pack' --manifest "$hosted/assurance-manifest.json" --pack "$pack" --receipt "$work/foreign.json"
expect_reviewed_fail reviewed-pack-tampered 'pack digest mismatch' --manifest "$hosted/assurance-manifest.json" --pack "$work/pack-tampered" --receipt "$work/pass.json"
cp -R "$pack" "$work/pack-forged-source"
python3 "$here/forge-pack-source.py" "$work/pack-forged-source" ASSURANCE.md 'A different ledger text, with digests made to agree.
'
expect_reviewed_fail reviewed-pack-forged-source 'packed source differs from the candidate commit: ASSURANCE.md' --manifest "$hosted/assurance-manifest.json" --pack "$work/pack-forged-source" --receipt "$work/pass.json"
python3 - "$hosted/assurance-manifest.json" "$work/manifest-reformatted.json" <<'PY'
import json, pathlib, sys
pathlib.Path(sys.argv[2]).write_text(json.dumps(json.loads(pathlib.Path(sys.argv[1]).read_text())) + "\n")
PY
expect_reviewed_fail reviewed-manifest-not-the-packed-one 'evidence pack does not contain the reviewed assurance manifest bytes' --manifest "$work/manifest-reformatted.json" --pack "$pack" --receipt "$work/pass.json"
python3 - "$hosted/assurance-manifest.json" "$work/manifest-dirty.json" <<'PY'
import json, pathlib, sys
d = json.loads(pathlib.Path(sys.argv[1]).read_text()); d["identity"]["clean_tree"] = False
pathlib.Path(sys.argv[2]).write_text(json.dumps(d, indent=2, sort_keys=True) + "\n")
PY
expect_reviewed_fail reviewed-manifest-not-clean 'manifest does not assert a clean source tree' --manifest "$work/manifest-dirty.json" --pack "$pack" --receipt "$work/pass.json"
expect_reviewed_fail reviewed-manifest-missing 'cannot read manifest' --manifest "$work/no-such-manifest.json" --pack "$pack" --receipt "$work/pass.json"
# A manifest that --validate refuses and that the pack holds too (the pack's own
# check does not look at an added field): only --validate refuses it.
cp -R "$pack" "$work/pack-manifest-extra"
python3 - "$work/pack-manifest-extra" <<'PY'
import hashlib, json, pathlib, sys
pack = pathlib.Path(sys.argv[1])
manifest = pack / "assurance-manifest.json"
d = json.loads(manifest.read_text())
d["approved"] = True
manifest.write_text(json.dumps(d, indent=2, sort_keys=True) + "\n")
index_path = pack / "PACK-MANIFEST.json"
index = json.loads(index_path.read_text())
for entry in index["files"]:
    path = pack / entry["path"]
    entry["sha256"], entry["bytes"] = hashlib.sha256(path.read_bytes()).hexdigest(), path.stat().st_size
index_path.write_text(json.dumps(index, indent=2, sort_keys=True) + "\n")
PY
receipt reviewed-extra-field 'pass'
rebind "$work/reviewed-extra-field.json" "$work/pack-manifest-extra"
expect_reviewed_fail reviewed-manifest-extra-field 'manifest fields are not exactly' --manifest "$work/pack-manifest-extra/assurance-manifest.json" --pack "$work/pack-manifest-extra" --receipt "$work/reviewed-extra-field.json"
# A packed file that no manifest digest covers (the workflow), forged with every digest brought up to date.
cp -R "$pack" "$work/pack-forged-workflow"
python3 "$here/forge-pack-source.py" "$work/pack-forged-workflow" .github/workflows/ci.yml 'A different workflow, with digests made to agree.
'
receipt reviewed-forged-workflow 'pass'
rebind "$work/reviewed-forged-workflow.json" "$work/pack-forged-workflow"
expect_reviewed_fail reviewed-pack-forged-workflow 'packed source differs from the candidate commit: .github/workflows/ci.yml' --manifest "$hosted/assurance-manifest.json" --pack "$work/pack-forged-workflow" --receipt "$work/reviewed-forged-workflow.json"
python3 "$here/make-candidate.py" "$root" "$work/other" --event push
expect_reviewed_fail reviewed-manifest-of-another-candidate 'manifest candidate commit/tree does not match selected source' --manifest "$work/other/hosted/assurance-manifest.json" --pack "$pack" --receipt "$work/pass.json"
# The candidate repository holds a different commit than the pack names.
cases=$((cases + 1))
set +e
elsewhere="$(cd "$work/other/repo" && python3 tooling/validate-reviewed-evidence.py --manifest "$work/other/hosted/assurance-manifest.json" --pack "$pack" --receipt "$work/pass.json" 2>&1)"
elsewhere_rc=$?
set -e
if [ "$elsewhere_rc" -eq 0 ] || ! printf '%s' "$elsewhere" | grep -qF 'is not in the repository'; then
  echo "WRONG  reviewed-pack-of-another-checkout: $elsewhere" >&2
  exit 1
fi

echo "check-ledger-review-receipt-cases: $cases cases gave the expected result (an honest receipt accepted; each refusal is one change to it, to the pack or to the manifest)"
