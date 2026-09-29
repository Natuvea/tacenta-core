#!/usr/bin/env bash
# Hold the claim and source-attestation gate to representative mutations.
#
# `attest.py` is intentionally rooted at its own repository path, so each
# mutation runs in a disposable detached worktree instead of changing the
# caller's tree. One worktree is made and reset between cases. The expected
# diagnostic is part of every case: a nonzero exit alone could be caused by an
# unrelated stale manifest. The first check is that the unmodified tree is
# accepted, because a refusal is only evidence if acceptance is possible.
#
# The cases are grouped by what they hold:
#   claims and manifests   -- the claim ledger, the three manifests
#   translation record     -- the generated files against their recorded hashes
#   axiom allowlist        -- every axiom a generated file declares, by
#                             qualified name and type, as a multiset
#   scanner forms          -- spellings of a declaration that the text scan has
#                             to read the same way as the plain one
#   audit comparison       -- `--compare-audit` against the environment's list
#   allowlist writer       -- the only writer of the allowlist
#   construct scanner      -- `check-lean-constructs.sh` reads the same spellings
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
work=""
cases=0
wrong=0

cleanup() {
  if [ -n "$work" ]; then
    git -C "$root" worktree remove --force "$work" >/dev/null 2>&1 || rm -rf "$work"
  fi
}
trap cleanup EXIT

make_case() {
  if [ -z "$work" ]; then
    work="$(mktemp -d)"
    git -C "$root" worktree add -q --detach "$work" HEAD >/dev/null
  else
    git -C "$work" checkout -q --force HEAD -- .
    git -C "$work" clean -fdq
  fi
}

attest() {
  (cd "$work" && python3 tacenta-proofs/scripts/attest.py "$@" 2>&1)
}

expect_fail() {
  local name="$1"
  local expected="$2"
  shift 2
  local out rc
  set +e
  out="$(attest "$@")"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $name: expected refusal containing '$expected', was accepted" >&2
    wrong=$((wrong + 1))
    return 0
  fi
  if [[ "$out" != *"$expected"* ]]; then
    echo "WRONG  $name: refused, but not for '$expected':" >&2
    printf '%s\n' "$out" >&2
    wrong=$((wrong + 1))
  fi
}

expect_pass() {
  local name="$1"
  shift
  local out rc
  set +e
  out="$(attest "$@")"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -ne 0 ]; then
    echo "WRONG  $name: expected acceptance, was refused:" >&2
    printf '%s\n' "$out" >&2
    wrong=$((wrong + 1))
  fi
}

gen="tacenta-proofs/translation/Translation"
allowlist="tacenta-proofs/manifests/translation-axiom-allowlist.json"
record="tacenta-proofs/manifests/translation-attestation.json"

# Run another script of this directory in the worktree; the same shape as attest.
run_script() {
  (cd "$work" && bash "tacenta-proofs/scripts/$1" 2>&1)
}

expect_script_fail() {
  local name="$1" expected="$2" script="$3" out rc
  set +e
  out="$(run_script "$script")"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $name: expected refusal containing '$expected', was accepted" >&2
    wrong=$((wrong + 1))
    return 0
  fi
  if [[ "$out" != *"$expected"* ]]; then
    echo "WRONG  $name: refused, but not for '$expected':" >&2
    printf '%s\n' "$out" >&2
    wrong=$((wrong + 1))
  fi
}

expect_script_pass() {
  local name="$1" script="$2" out rc
  set +e
  out="$(run_script "$script")"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -ne 0 ]; then
    echo "WRONG  $name: expected acceptance, was refused:" >&2
    printf '%s\n' "$out" >&2
    wrong=$((wrong + 1))
  fi
}

# Insert the text on stdin into a generated file just before the `end` that
# closes its namespace, which is where the translator's own declarations sit.
insert_in() {
  local text
  text="$(cat)"
  INSERT_TEXT="$text" python3 - "$work/$gen/$1" <<'PY'
import os, pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
close = list(re.finditer(r"^end (\S+)\s*$", text, re.M))[-1]
path.write_text(text[:close.start()] + os.environ["INSERT_TEXT"] + "\n\n" + text[close.start():])
PY
}

# Run a Python program over a JSON file: `data` is the parsed document.
edit_json() {
  python3 - "$work/$1" "$2" <<'PY'
import json, pathlib, sys
path, program = pathlib.Path(sys.argv[1]), sys.argv[2]
data = json.loads(path.read_text())
exec(program, {"data": data})
path.write_text(json.dumps(data, indent=2) + "\n")
PY
}

# Replace `old` with `new` in a file, once, or stop.
replace_in() {
  python3 - "$work/$1" "$2" "$3" <<'PY'
import pathlib, sys
path, old, new = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3]
text = path.read_text()
assert text.count(old) == 1, (path, old, text.count(old))
path.write_text(text.replace(old, new))
PY
}

# The audit log an honest build of the recorded translation would print.
honest_audit_log() {
  python3 - "$work/$record" "$1" <<'PY'
import json, pathlib, sys
record = json.loads(pathlib.Path(sys.argv[1]).read_text())["generated_files"]
lines = []
for rel, item in sorted(record.items()):
    for name in item["axioms"]:
        lines.append("audit-axiom: Translation.%s %s" % (item["module"], name))
pathlib.Path(sys.argv[2]).write_text("\n".join(lines) + "\n")
PY
}

# ---------------------------------------------------------------------------
# Control: the unmodified tree is accepted.
# ---------------------------------------------------------------------------

make_case
expect_pass "unmodified-tree" --check
expect_pass "unmodified-translation" --check-translation

# ---------------------------------------------------------------------------
# Claims and manifests.
# ---------------------------------------------------------------------------

make_case
python3 - "$work/tacenta-proofs/CLAIMS.md" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
path.write_text(path.read_text() + "\n## Proved P9 mutation\n\n**Location:** `tacenta-proofs/Proofs/SessionEstablishment.lean`\n\n- `P9MissingTheorem`: mutation control.\n")
PY
expect_fail "missing-claimed-theorem" 'CLAIMS.md claims `P9MissingTheorem` but no such theorem is declared' --check

make_case
rm "$work/tacenta-proofs/manifests/verification-manifest.json"
expect_fail "missing-verification-manifest" "tacenta-proofs/manifests/verification-manifest.json is missing" --check

make_case
edit_json tacenta-proofs/manifests/source-commit-attestation.json 'data["p9_mutation"] = "stale"'
expect_fail "stale-source-attestation" "tacenta-proofs/manifests/source-commit-attestation.json is stale" --check

# ---------------------------------------------------------------------------
# The translation record.
# ---------------------------------------------------------------------------

make_case
printf '\n-- P9 mutation --\n' >> "$work/$gen/TacentaRatchet.lean"
expect_fail "edited-generated-translation" "TacentaRatchet.lean differs from the recorded generation" --check-translation

make_case
python3 - "$work/$record" <<'PY'
import json, pathlib, subprocess, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
# A recorded file and a source hash must come from the same committed source
# tree. Select the oldest commit that contains the sparse source so this test
# remains valid when the branch is rebased or its history is pruned.
commits = subprocess.check_output(
    ["git", "rev-list", "--all", "--", "tacenta-core/spqr/src/lib.rs"],
    text=True,
).splitlines()
if len(commits) < 2:
    raise SystemExit("not enough sparse source history for the pairing control")
data["generated_at_commit"] = commits[-1]
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "mismatched-committed-source-hash" "commit the source tree before refreshing" --check-translation

make_case
python3 - "$work/$record" <<'PY'
import json, pathlib, subprocess, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
data["generated_at_commit"] = subprocess.check_output(
    ["git", "rev-parse", "HEAD^{tree}"], text=True
).strip()
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "generation-revision-not-commit" "is not an available commit" --check-translation

make_case
edit_json "$record" 'del data["generated_files"]["'"$gen"'/TacentaSessionUnit.lean"]["assembly"]["sources"]["tacenta-core/lifecycle"]'
expect_fail "missing-session-unit-leaf" "is recorded as assembled from" --check-translation

make_case
edit_json "$record" 'data["generated_files"]["'"$gen"'/TacentaSessionUnit.lean"]["assembly"]["script_sha256"] = "00" * 32'
expect_fail "stale-session-unit-assembler" "its assembly script" --check-translation

make_case
edit_json "$record" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"]["axioms"].pop()'
expect_fail "record-lists-fewer-axioms" "declares a different axiom set from the recorded one" --check-translation

make_case
edit_json "$record" 'a = data["generated_files"]["'"$gen"'/TacentaRatchet.lean"]["axioms"]; a.append(a[0]); a.sort()'
expect_fail "record-lists-an-axiom-twice" "declares a different axiom set from the recorded one" --check-translation

make_case
edit_json "$record" 'data["schema_version"] = 3'
expect_fail "record-schema-is-old" "translation-attestation.json has schema_version 3" --check-translation

# ---------------------------------------------------------------------------
# The axiom allowlist: every declaration, by qualified name and type.
# Each plant is tried through --refresh-translation, the one mode that
# would otherwise record it, and the last one checks nothing was recorded.
# ---------------------------------------------------------------------------

make_case
insert_in TacentaRatchet.lean <<'EOF'
axiom planted_false : False
EOF
expect_fail "planted-generated-axiom" "differ from the allowlist" --refresh-translation
if ! git -C "$work" diff --quiet -- "$record"; then
  echo "WRONG  planted-generated-axiom: the refused refresh still wrote the record" >&2
  wrong=$((wrong + 1))
fi

make_case
insert_in TacentaRatchet.lean <<'EOF'
namespace Other
axiom zeroize.Zeroizing.new : False
end Other
EOF
expect_fail "declaration-in-a-second-namespace" "added: tacenta_ratchet.Other.zeroize.Zeroizing.new" --refresh-translation

make_case
replace_in "$gen/TacentaErasure.lean" \
  "axiom core.num.Usize.div_ceil : Std.Usize → Std.Usize → Result Std.Usize" \
  "axiom core.num.Usize.div_ceil : False"
expect_fail "declaration-with-another-type" "tacenta_erasure.core.num.Usize.div_ceil : False" --refresh-translation

make_case
python3 - "$work/$gen/TacentaErasure.lean" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
line = "axiom core.num.Usize.div_ceil : Std.Usize → Std.Usize → Result Std.Usize\n"
assert text.count(line) == 1
path.write_text(text.replace(line, line + "\n" + line))
PY
expect_fail "declaration-repeated" "added: tacenta_erasure.core.num.Usize.div_ceil" --refresh-translation

make_case
replace_in "$gen/TacentaErasure.lean" \
  "axiom core.num.Usize.div_ceil : Std.Usize → Std.Usize → Result Std.Usize" \
  "-- removed"
expect_fail "declaration-removed" "removed: tacenta_erasure.core.num.Usize.div_ceil" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
private axiom planted_false : False
EOF
expect_fail "private-declaration" "added: private tacenta_ratchet.planted_false" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
@[simp] axiom planted_false : False
EOF
expect_fail "declaration-behind-an-attribute" "added: tacenta_ratchet.planted_false" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
set_option maxRecDepth 100 in axiom planted_false : False
EOF
expect_fail "declaration-after-set-option" "added: tacenta_ratchet.planted_false" --refresh-translation

make_case
insert_in TacentaProtobuf.lean <<'EOF'
axiom planted_false : False
EOF
expect_fail "declaration-in-a-file-with-none" "added: tacenta_protobuf.planted_false" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
axiom
  planted_false : False
EOF
expect_fail "declaration-name-on-the-next-line" "added: tacenta_ratchet.planted_false" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
axiom _root_.planted_false : False
EOF
expect_fail "declaration-in-the-root-namespace" "added: planted_false" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
axiom planted_false
  : False
  -- a comment
EOF
expect_fail "declaration-type-on-later-lines" "planted_false : False" --refresh-translation

# The allowlist file itself.

make_case
rm "$work/$allowlist"
expect_fail "allowlist-missing" "translation-axiom-allowlist.json is missing" --check-translation

make_case
printf '{ not json' > "$work/$allowlist"
expect_fail "allowlist-not-json" "translation-axiom-allowlist.json is not valid JSON" --check-translation

make_case
edit_json "$allowlist" 'data["schema_version"] = 1'
expect_fail "allowlist-schema" "has unsupported schema_version" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"] = []'
expect_fail "allowlist-without-files" "has no generated_files object" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"] = {"zeroize": "x"}'
expect_fail "allowlist-entry-not-a-list" "is not a list of declarations" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"][0]["note"] = "extra"'
expect_fail "allowlist-entry-shape" "has an allowlist entry that is not a name and a type" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"][0]["name"] += "ο"'
expect_fail "allowlist-name-characters" "characters outside" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"].reverse()'
expect_fail "allowlist-unsorted" "has unsorted declarations in the allowlist" --check-translation

make_case
edit_json "$allowlist" 'del data["generated_files"]["'"$gen"'/TacentaRatchet.lean"]'
expect_fail "allowlist-file-without-entry" "is a generated file with no entry in translation-axiom-allowlist.json" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"]["tacenta-proofs/translation/Translation/TacentaNothing.lean"] = []'
expect_fail "allowlist-entry-for-no-file" "is in translation-axiom-allowlist.json but is not a generated file" --check-translation

make_case
python3 - "$work/$allowlist" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
key = '"tacenta-proofs/translation/Translation/TacentaWire.lean": ['
assert text.count(key) == 1
path.write_text(text.replace(key, '"tacenta-proofs/translation/Translation/TacentaWire.lean": [],\n    ' + key))
PY
expect_fail "allowlist-repeats-a-key" "duplicate key" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"].pop()'
expect_fail "allowlist-lists-fewer" "removed: none" --check-translation

make_case
edit_json "$allowlist" 'e = data["generated_files"]["'"$gen"'/TacentaRatchet.lean"]; e.append(e[0]); e.sort(key=lambda x: (x["name"], x["type"]))'
expect_fail "allowlist-lists-a-declaration-twice" "removed: tacenta_ratchet" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"][0]["type"] += " -> False"'
expect_fail "allowlist-type-differs" "declares axioms that differ from the allowlist" --check-translation

# ---------------------------------------------------------------------------
# Scanner forms: spellings of a declaration that must be read as the plain
# one is. Numbered; each is an `axiom` the allowlist does not list.
# ---------------------------------------------------------------------------

make_case
insert_in TacentaRatchet.lean <<'EOF'
def scanner_form_01_a : Char := '"'
axiom scanner_form_01 : False
def scanner_form_01_b : Char := '"'
EOF
expect_fail "scanner-form-01" "added: tacenta_ratchet.scanner_form_01" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
def scanner_form_02_a : String := r#"a"b"#
axiom scanner_form_02 : False
def scanner_form_02_b : String := r#"a"b"#
EOF
expect_fail "scanner-form-02" "added: tacenta_ratchet.scanner_form_02" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
def «/-» : Nat := 1
axiom scanner_form_03 : False
def «-/» : Nat := 2
EOF
expect_fail "scanner-form-03" "added: tacenta_ratchet.scanner_form_03" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
axiom«scanner_form_04» : False
EOF
expect_fail "scanner-form-04" "scanner_form_04" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
def scanner_form_05 : Nat := 1
end scanner_form_05
EOF
expect_fail "scanner-form-05" "does not close the innermost scope" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
namespace
axiom scanner_form_06 : False
EOF
expect_fail "scanner-form-06" "namespace without a name" --refresh-translation

make_case
printf '\naxiom\n' >> "$work/$gen/TacentaRatchet.lean"
expect_fail "scanner-form-07" "axiom without a name" --refresh-translation

make_case
printf '\naxiom planted_false : False\n' >> "$work/$gen/TacentaRatchet.lean"
expect_fail "declaration-after-the-namespace-closes" "added: planted_false : False" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
section scanner_form_08
axiom scanner_form_08 : False
end scanner_form_08
EOF
expect_fail "scanner-form-08" "added: tacenta_ratchet.scanner_form_08 : False;" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
axiom scanner_form_09_a : Nat
  axiom scanner_form_09_b : False
EOF
expect_fail "scanner-form-09" "added: tacenta_ratchet.scanner_form_09_a : Nat; tacenta_ratchet.scanner_form_09_b : False;" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
def scanner_form_10_a : String := "a\"b"
axiom scanner_form_10 : False
def scanner_form_10_b : String := "a\"b"
EOF
expect_fail "scanner-form-10" "added: tacenta_ratchet.scanner_form_10 : False;" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
def scanner_form_16_f'' (c : Char) : Char := c
def scanner_form_16_a := scanner_form_16_f'' '"'
axiom scanner_form_16 : False
def scanner_form_16_b := scanner_form_16_f'' '"'
EOF
expect_fail "scanner-form-16" "added: tacenta_ratchet.scanner_form_16 : False;" --refresh-translation

# Text that is not a declaration must not be read as one: the accepted side of
# the scanner. A keyword in a comment, a string, a character literal or a
# guillemet identifier, and a name that merely contains the keyword.
make_case
insert_in TacentaRatchet.lean <<'EOF'
-- axiom in_a_line_comment : False
/- axiom in_a_block_comment : False -/
/-- axiom in_a_doc_comment : False -/
def not_a_declaration_a : String := "axiom in_a_string : False"
def not_a_declaration_b : Char := 'a'
def «has an axiom inside» : Nat := 1
def axiomatic : Nat := 1
/- outer /- inner -/ axiom in_a_nested_comment : False -/
def not_a_declaration_c : Nat := 1
EOF
expect_pass "text-that-is-not-a-declaration" --refresh-translation
expect_pass "text-that-is-not-a-declaration-is-current" --check

# ---------------------------------------------------------------------------
# The audit comparison.
# ---------------------------------------------------------------------------

make_case
honest_audit_log "$work/audit.log"
expect_pass "audit-matches-the-record" --compare-audit "$work/audit.log"

make_case
honest_audit_log "$work/audit.log"
printf 'audit-axiom: Translation.TacentaRatchet Other.zeroize.Zeroizing.new\n' >> "$work/audit.log"
expect_fail "audit-has-an-extra-name" "in the environment but not in the recorded list: Other.zeroize.Zeroizing.new" --compare-audit "$work/audit.log"

make_case
honest_audit_log "$work/audit.log"
python3 - "$work/audit.log" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
lines = path.read_text().splitlines()
i = next(n for n, l in enumerate(lines) if "TacentaRatchet zeroize.Zeroizing.new" in l or "TacentaRatchet tacenta_ratchet.zeroize.Zeroizing.new" in l)
lines[i] = lines[i].replace("TacentaRatchet ", "TacentaRatchet Other.")
path.write_text("\n".join(lines) + "\n")
PY
expect_fail "audit-name-only-ends-in-a-recorded-name" "in the environment but not in the recorded list: Other.tacenta_ratchet.zeroize.Zeroizing.new" --compare-audit "$work/audit.log"

make_case
honest_audit_log "$work/audit.log"
python3 - "$work/audit.log" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
lines = path.read_text().splitlines()
i = next(n for n, l in enumerate(lines) if "TacentaRatchet" in l)
del lines[i]
path.write_text("\n".join(lines) + "\n")
PY
expect_fail "audit-lacks-a-recorded-name" "in the recorded list but not in the environment" --compare-audit "$work/audit.log"

make_case
honest_audit_log "$work/audit.log"
python3 - "$work/audit.log" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
lines = path.read_text().splitlines()
i = next(n for n, l in enumerate(lines) if "TacentaRatchet" in l)
lines.append(lines[i])
path.write_text("\n".join(lines) + "\n")
PY
expect_fail "audit-repeats-a-name" "in the environment but not in the recorded list" --compare-audit "$work/audit.log"

make_case
honest_audit_log "$work/audit.log"
printf 'audit-axiom: Translation.TacentaNothing tacenta_nothing.x\n' >> "$work/audit.log"
expect_fail "audit-reports-an-unrecorded-module" "which has no record in translation-attestation.json" --compare-audit "$work/audit.log"

make_case
honest_audit_log "$work/audit.log"
grep -v ' Translation.TacentaRatchet ' "$work/audit.log" > "$work/audit.log.new"
mv "$work/audit.log.new" "$work/audit.log"
expect_fail "audit-omits-a-module" "carries no audit-axiom lines for Translation.TacentaRatchet" --compare-audit "$work/audit.log"

make_case
honest_audit_log "$work/audit.log"
edit_json "$allowlist" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"].pop()'
expect_fail "audit-differs-from-the-allowlist" "not in the allowlist list" --compare-audit "$work/audit.log"

# ---------------------------------------------------------------------------
# The allowlist writer.
# ---------------------------------------------------------------------------

make_case
expect_pass "writer-leaves-a-current-allowlist-alone" --write-axiom-allowlist
if ! git -C "$work" diff --quiet -- "$allowlist"; then
  echo "WRONG  writer-leaves-a-current-allowlist-alone: the writer changed the file" >&2
  wrong=$((wrong + 1))
fi

make_case
set +e
out="$(cd "$work" && GITHUB_ACTIONS=true python3 tacenta-proofs/scripts/attest.py --write-axiom-allowlist 2>&1)"
rc=$?
set -e
cases=$((cases + 1))
if [ "$rc" -eq 0 ] || [[ "$out" != *"does not run in CI"* ]]; then
  echo "WRONG  writer-refuses-in-ci: rc=$rc: $out" >&2
  wrong=$((wrong + 1))
fi

make_case
insert_in TacentaRatchet.lean <<'EOF'
def writer_form : Nat := 1
end writer_form
EOF
expect_fail "writer-refuses-an-unreadable-file" "cannot be read" --write-axiom-allowlist

make_case
insert_in TacentaRatchet.lean <<'EOF'
axiom planted_false : False
EOF
set +e
out="$(attest --write-axiom-allowlist)"
rc=$?
set -e
cases=$((cases + 1))
if [ "$rc" -ne 0 ] || [[ "$out" != *"allowlist + TacentaRatchet.lean: tacenta_ratchet.planted_false : False"* ]]; then
  echo "WRONG  writer-reports-what-it-added: rc=$rc, the addition was not printed:" >&2
  printf '%s\n' "$out" >&2
  wrong=$((wrong + 1))
fi

# ---------------------------------------------------------------------------
# The construct scanner reads hand-written Lean the way the attestation scan
# reads the generated files. Each plant goes at the end of a proof file.
# ---------------------------------------------------------------------------

proof="tacenta-proofs/Proofs/ErrorHandling.lean"

make_case
expect_script_pass "constructs-unmodified-tree" check-lean-constructs.sh

make_case
cat >> "$work/$proof" <<'EOF'

def scanner_form_11_a : Char := '"'
run_cmd pure ()
def scanner_form_11_b : Char := '"'
EOF
expect_script_fail "scanner-form-11" "elab-time-command" check-lean-constructs.sh

make_case
cat >> "$work/$proof" <<'EOF'

def scanner_form_12_a : String := r#"a"b"#
run_cmd pure ()
def scanner_form_12_b : String := r#"a"b"#
EOF
expect_script_fail "scanner-form-12" "elab-time-command" check-lean-constructs.sh

make_case
cat >> "$work/$proof" <<'EOF'

def «/-» : Nat := 1
run_cmd pure ()
def «-/» : Nat := 2
EOF
expect_script_fail "scanner-form-13" "elab-time-command" check-lean-constructs.sh

make_case
cat >> "$work/$proof" <<'EOF'

axiom«scanner_form_14» : False
EOF
expect_script_fail "scanner-form-14" ": axiom:" check-lean-constructs.sh

make_case
cat >> "$work/$proof" <<'EOF'

def scanner_form_15_a : Char := '"'
axiom scanner_form_15 : False
def scanner_form_15_b : Char := '"'
EOF
expect_script_fail "scanner-form-15" ": axiom:" check-lean-constructs.sh

make_case
cat >> "$work/$proof" <<'EOF'

-- run_cmd in_a_line_comment
/- run_cmd in_a_block_comment -/
def not_a_construct_a : String := "run_cmd in_a_string"
def not_a_construct_b : Char := 'a'
def «run_cmd in_a_name» : Nat := 1
def not_a_construct_c : String := r#"run_cmd in a raw string"#
def x' : Nat := 1
def axiomatic : Nat := 1
EOF
expect_script_pass "constructs-text-that-is-not-a-construct" check-lean-constructs.sh

if [ "$wrong" -ne 0 ]; then
  echo "check-attest-negatives: $wrong of $cases cases gave the wrong result" >&2
  exit 1
fi
echo "check-attest-negatives: $cases cases gave the expected result (the unmodified tree accepted; each mutation refused for its stated reason)"
