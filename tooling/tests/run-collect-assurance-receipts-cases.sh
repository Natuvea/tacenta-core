#!/usr/bin/env bash
# Exercise the receipt writer's and collector's source, applicability and
# command-outcome controls.
#
# Receipts are written the way the workflow writes them, through
# `write-assurance-receipt.py`, with the outcomes the workflow records for each
# job: the command steps in `tooling/required-steps.json`, all `success`. Every
# refusal starts from that honest set and changes one thing, so it is the change
# that is refused. A receipt that records a step as failed or skipped, leaves a
# step out, records one the workflow does not run, or records no outcomes at all
# is refused by the writer and again by the collector.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cases=0

# The outcomes the workflow records for a receipt id in an event, honest:
# "step=success,step=success,...".
outcomes() {
  PYTHONPATH="$root/tooling" python3 - "$1" "$2" <<'PY'
import sys
from assurance_validation import expected_step_outcomes
print(",".join(f"{step}=success" for step in expected_step_outcomes()[(sys.argv[1], sys.argv[2])]))
PY
}

write_one() {
  local directory="$1" id="$2" event="$3" classification="${4:-required}"
  GITHUB_EVENT_NAME="$event" GITHUB_RUN_ID=control GITHUB_RUN_ATTEMPT=1 \
    python3 -I "$root/tooling/write-assurance-receipt.py" --id "$id" --classification "$classification" \
    --command "control-$id" --required-outcomes "$(outcomes "$id" "$event")" \
    --output "$directory/$id.json" >/dev/null
}

write_receipts() {
  local directory="$1" event="$2"
  mkdir -p "$directory"
  for id in rust msrv armv7 vectors audit proofs translation checks; do
    write_one "$directory" "$id" "$event"
  done
}

expect_fail() {
  local name="$1" needle="$2" directory="$3" event="$4" out rc
  set +e
  out="$(python3 "$root/tooling/collect-assurance-receipts.py" --event "$event" --input-dir "$directory" --output "$work/$name.out" 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
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

# Run the writer with the given arguments and expect it to refuse.
expect_writer_fail() {
  local name="$1" needle="$2" out rc
  shift 2
  set +e
  out="$("$@" 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $name: the writer accepted it" >&2
    return 1
  fi
  if ! printf '%s' "$out" | grep -qF -- "$needle"; then
    echo "WRONG  $name: missing diagnostic '$needle'" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
}

mutate() {
  local path="$1" program="$2"
  python3 - "$path" "$program" <<'PY'
import json, pathlib, sys
path, program = map(pathlib.Path, sys.argv[1:])
data = json.loads(path.read_text())
exec(program.read_text(), {'data': data})
path.write_text(json.dumps(data, indent=2) + '\n')
PY
}

# One receipt mutated from a fresh honest set.
refuse() {
  local name="$1" needle="$2" id="$3" program="$4" event="${5:-push}"
  cp -R "$work/pass-$event" "$work/$name"
  printf '%s\n' "$program" > "$work/$name.py"
  mutate "$work/$name/$id.json" "$work/$name.py"
  expect_fail "$name" "$needle" "$work/$name" "$event"
}

# ---- the expected lists themselves -----------------------------------------
# The lists come from the receipt steps of tooling/required-steps.json, so they
# are checked against what the workflow is known to run rather than against
# themselves.
PYTHONPATH="$root/tooling" python3 - <<'PY'
from assurance_validation import expected_step_outcomes
table = expected_step_outcomes()
assert table[("rust", "push")] == table[("rust", "pull_request")], "rust runs the same commands for both events"
assert table[("rust", "push")][0] == "rust_fmt"
translation_push, translation_pr = table[("translation", "push")], table[("translation", "pull_request")]
assert "translation_seed" in translation_push and "translation_seed" not in translation_pr
assert [s for s in translation_push if s != "translation_seed"] == translation_pr
checks_push, checks_pr = table[("checks", "push")], table[("checks", "pull_request")]
assert "checks_39" in checks_push and "checks_39" not in checks_pr
assert table[("sign-off", "pull_request")] == ["signoff_check"] and ("sign-off", "push") not in table
assert {receipt for receipt, _ in table} == {"rust", "msrv", "armv7", "vectors", "audit", "proofs", "translation", "checks", "sign-off"}
PY
cases=$((cases + 1))

# How the lists are read from a document: the events a receipt step is for,
# taken from the job's and the step's own condition, and a second receipt step
# for one id and event refused. Each document is the real one with one change.
PYTHONPATH="$root/tooling" python3 - "$root" <<'PY'
import copy, json, pathlib, sys
from assurance_validation import expected_from_document, expected_step_outcomes

document = json.loads((pathlib.Path(sys.argv[1]) / "tooling/required-steps.json").read_text())
base = expected_from_document(document)
assert base == expected_step_outcomes()


def receipt_step(doc, job, position=0):
    steps = [s for s in doc["files"][".github/workflows/ci.yml"]["jobs"][job]["steps"]
             if s.get("uses") == "./.github/actions/assurance-receipt"]
    return steps[position]


def refused(doc, needle):
    try:
        expected_from_document(doc)
    except ValueError as exc:
        assert needle in str(exc), (needle, str(exc))
        return
    raise SystemExit("a document with two receipt steps for one id and event was read")

# A step condition other than the two exact ones is read as both events.
other = copy.deepcopy(document)
receipt_step(other, "rust")["if"] = "always()"
assert expected_from_document(other)[("rust", "push")] == base[("rust", "push")]
assert ("rust", "pull_request") in expected_from_document(other)
# The exact pull-request condition is for that event alone.
only = copy.deepcopy(document)
receipt_step(only, "rust")["if"] = "github.event_name == 'pull_request'"
table = expected_from_document(only)
assert ("rust", "pull_request") in table and ("rust", "push") not in table
# A job condition narrows its receipt steps the same way.
job = copy.deepcopy(document)
job["files"][".github/workflows/ci.yml"]["jobs"]["msrv"]["if"] = "github.event_name == 'push'"
table = expected_from_document(job)
assert ("msrv", "push") in table and ("msrv", "pull_request") not in table
# The job and the step must both allow an event.
both = copy.deepcopy(document)
both["files"][".github/workflows/ci.yml"]["jobs"]["msrv"]["if"] = "github.event_name == 'push'"
receipt_step(both, "msrv")["if"] = "github.event_name == 'pull_request'"
table = expected_from_document(both)
assert ("msrv", "push") not in table and ("msrv", "pull_request") not in table
# Two receipt steps for one id and event.
twice = copy.deepcopy(document)
steps = twice["files"][".github/workflows/ci.yml"]["jobs"]["rust"]["steps"]
steps.append(copy.deepcopy(receipt_step(twice, "rust")))
refused(twice, "receipt rust has two steps for event")
PY
cases=$((cases + 1))

# ---- honest receipts are collected ----------------------------------------
write_receipts "$work/pass-push" push
python3 "$root/tooling/collect-assurance-receipts.py" --event push --input-dir "$work/pass-push" --output "$work/pass-push.out" >/dev/null
write_receipts "$work/pass-pull_request" pull_request
write_one "$work/pass-pull_request" sign-off pull_request conditional
python3 "$root/tooling/collect-assurance-receipts.py" --event pull_request --input-dir "$work/pass-pull_request" --output "$work/pass-pull_request.out" >/dev/null
cases=$((cases + 2))

# The writer records the outcomes it was given.
python3 - "$work/pass-push/translation.json" <<'PY'
import json, sys
receipt = json.load(open(sys.argv[1]))
assert receipt["step_outcomes"]["translation_seed"] == "success"
assert set(receipt["step_outcomes"].values()) == {"success"}
PY

# ---- the writer -----------------------------------------------------------
writer_env=(env GITHUB_EVENT_NAME=push GITHUB_RUN_ID=control GITHUB_RUN_ATTEMPT=1)
write_args() {
  local id="$1"
  shift
  "${writer_env[@]}" python3 "$root/tooling/write-assurance-receipt.py" --id "$id" --classification required \
    --command "control-$id" --output "$work/writer.json" "$@"
}

expect_writer_fail duplicate-writer "duplicate required outcome 'one'" \
  "${writer_env[@]}" python3 "$root/tooling/write-assurance-receipt.py" --id duplicate --classification required \
  --command duplicate --required-outcomes "one=success,one=success" --output "$work/duplicate-writer.json"
expect_writer_fail writer-failed-step "required command did not succeed: rust_test" \
  write_args rust --required-outcomes "$(outcomes rust push | sed 's/rust_test=success/rust_test=failure/')"
expect_writer_fail writer-skipped-step "required command did not succeed: rust_test" \
  write_args rust --required-outcomes "$(outcomes rust push | sed 's/rust_test=success/rust_test=skipped/')"
expect_writer_fail writer-missing-step "receipt rust does not record the command steps: rust_clippy" \
  write_args rust --required-outcomes "$(outcomes rust push | sed 's/rust_clippy=success,//')"
expect_writer_fail writer-extra-step "receipt rust records steps the workflow does not run for push: rust_extra" \
  write_args rust --required-outcomes "$(outcomes rust push),rust_extra=success"
expect_writer_fail writer-malformed-outcome "malformed required outcome 'rust_fmt'" \
  write_args rust --required-outcomes "rust_fmt"
expect_writer_fail writer-unknown-outcome-word "invalid required outcome 'rust_fmt=maybe'" \
  write_args rust --required-outcomes "rust_fmt=maybe"
expect_writer_fail writer-no-outcomes "required checks must assert command step outcomes" \
  write_args rust
expect_writer_fail writer-unknown-event "receipt rust names event 'local'" \
  env GITHUB_EVENT_NAME=local GITHUB_RUN_ID=control python3 "$root/tooling/write-assurance-receipt.py" --id rust \
  --classification required --command c --required-outcomes "$(outcomes rust push)" --output "$work/writer.json"
expect_writer_fail writer-step-list-for-the-other-event "receipt translation records steps the workflow does not run for pull_request: translation_seed" \
  env GITHUB_EVENT_NAME=pull_request GITHUB_RUN_ID=control python3 "$root/tooling/write-assurance-receipt.py" --id translation \
  --classification required --command c --required-outcomes "$(outcomes translation push)" --output "$work/writer.json"

# The workflow runs the writer with `python3 -I`; an interpreter setting in the
# environment must not reach it. The first run shows the setting is a real
# hazard (it stops the writer when honoured), the second that -I ignores it.
mkdir -p "$work/poison"
printf 'raise SystemExit("poisoned interpreter setting was honoured")\n' > "$work/poison/sitecustomize.py"
set +e
poisoned="$(PYTHONPATH="$work/poison" GITHUB_EVENT_NAME=push GITHUB_RUN_ID=control python3 "$root/tooling/write-assurance-receipt.py" --id rust --classification required --command c --required-outcomes "$(outcomes rust push)" --output "$work/poisoned.json" 2>&1)"
poisoned_rc=$?
set -e
if [ "$poisoned_rc" -eq 0 ] || ! printf '%s' "$poisoned" | grep -qF "poisoned interpreter setting was honoured"; then
  echo "WRONG  interpreter-setting control: the setting did not reach an ordinary interpreter" >&2
  exit 1
fi
PYTHONPATH="$work/poison" GITHUB_EVENT_NAME=push GITHUB_RUN_ID=control \
  python3 -I "$root/tooling/write-assurance-receipt.py" --id rust --classification required --command c \
  --required-outcomes "$(outcomes rust push)" --output "$work/isolated.json" >/dev/null
cases=$((cases + 2))

# ---- the collector --------------------------------------------------------
refuse foreign 'receipt rust was not produced for the selected candidate' rust "data['run']['commit'] = '0' * 40"
refuse foreign-tree 'receipt rust was not produced for the selected candidate' rust "data['run']['tree'] = '0' * 40"
refuse foreign-sign-off-tree 'receipt sign-off was not produced for the selected candidate' sign-off "data['run']['tree'] = '0' * 40" pull_request
refuse wrong-classification 'required receipt audit must be an applicable required check' audit "data['classification'] = 'optional'"
refuse wrong-event 'receipt vectors event does not match selected event push' vectors "data['environment']['event'] = 'pull_request'"

cp -R "$work/pass-push" "$work/duplicate"
cp "$work/duplicate/rust.json" "$work/duplicate/duplicate.json"
expect_fail duplicate 'duplicate check receipt rust' "$work/duplicate" push

cp -R "$work/pass-push" "$work/unknown"
cp "$work/unknown/rust.json" "$work/unknown/other.json"
python3 - "$work/unknown/other.json" <<'PY'
import json, sys
path = sys.argv[1]
data = json.load(open(path)); data["id"] = "other"; json.dump(data, open(path, "w"))
PY
expect_fail unknown 'unexpected check receipt other' "$work/unknown" push

cp -R "$work/pass-push" "$work/missing"
rm "$work/missing/proofs.json"
expect_fail missing 'missing required check receipts: proofs' "$work/missing" push

expect_fail no-directory 'input directory does not exist' "$work/no-such-directory" push

cp -R "$work/pass-push" "$work/receipt-not-an-object"
printf '[]' > "$work/receipt-not-an-object/rust.json"
expect_fail receipt-not-an-object 'must be an object' "$work/receipt-not-an-object" push
cp -R "$work/pass-push" "$work/receipt-not-json"
printf 'not json' > "$work/receipt-not-json/rust.json"
expect_fail receipt-not-json 'cannot read receipt' "$work/receipt-not-json" push

refuse status-fail 'required receipt rust is' rust "data['status'] = 'fail'"
refuse not-applicable 'required receipt rust must be an applicable required check' rust "data['applicable'] = False"

# Command outcomes, changed after the writer wrote them.
refuse outcome-failed 'receipt rust records command steps that did not succeed: rust_test=failure' rust "data['step_outcomes']['rust_test'] = 'failure'"
refuse outcome-skipped 'receipt vectors records command steps that did not succeed: vectors_reader=skipped' vectors "data['step_outcomes']['vectors_reader'] = 'skipped'"
refuse outcome-cancelled 'receipt audit records command steps that did not succeed: audit_run=cancelled' audit "data['step_outcomes']['audit_run'] = 'cancelled'"
refuse outcome-missing 'receipt rust does not record the command steps: rust_clippy' rust "del data['step_outcomes']['rust_clippy']"
refuse outcome-extra 'receipt msrv records steps the workflow does not run for push: msrv_extra' msrv "data['step_outcomes']['msrv_extra'] = 'success'"
refuse outcome-none 'receipt armv7 records no command step outcomes' armv7 "del data['step_outcomes']"
refuse outcome-empty 'receipt proofs records no command step outcomes' proofs "data['step_outcomes'] = {}"
refuse outcome-not-a-mapping 'receipt checks records no command step outcomes' checks "data['step_outcomes'] = ['checks_01']"
refuse outcome-only-one-step 'receipt checks does not record the command steps: checks_01' checks "data['step_outcomes'] = {'checks_40': 'success'}"
refuse outcome-list-for-the-other-event 'receipt translation records steps the workflow does not run for pull_request: translation_seed' translation "data['step_outcomes']['translation_seed'] = 'success'" pull_request
refuse outcome-missing-seed-on-push 'receipt translation does not record the command steps: translation_seed' translation "del data['step_outcomes']['translation_seed']"

write_receipts "$work/pull-request-alone" pull_request
expect_fail missing-signoff 'missing required conditional check receipt: sign-off' "$work/pull-request-alone" pull_request
cp -R "$work/pass-pull_request" "$work/signoff-failed"
printf "%s\n" "data['step_outcomes']['signoff_check'] = 'failure'" > "$work/signoff-failed.py"
mutate "$work/signoff-failed/sign-off.json" "$work/signoff-failed.py"
expect_fail signoff-failed 'receipt sign-off records command steps that did not succeed: signoff_check=failure' "$work/signoff-failed" pull_request
cp -R "$work/pass-pull_request" "$work/signoff-empty"
printf "%s\n" "data['step_outcomes'] = {}" > "$work/signoff-empty.py"
mutate "$work/signoff-empty/sign-off.json" "$work/signoff-empty.py"
expect_fail signoff-empty 'receipt sign-off records no command step outcomes' "$work/signoff-empty" pull_request
cp -R "$work/pass-pull_request" "$work/signoff-classification"
printf "%s\n" "data['classification'] = 'required'" > "$work/signoff-classification.py"
mutate "$work/signoff-classification/sign-off.json" "$work/signoff-classification.py"
expect_fail signoff-classification 'pull-request sign-off receipt must be an applicable conditional check' "$work/signoff-classification" pull_request
cp -R "$work/pass-push" "$work/push-with-signoff"
write_one "$work/push-with-signoff" sign-off pull_request conditional
expect_fail push-with-signoff 'receipt sign-off event does not match selected event push' "$work/push-with-signoff" push
cp -R "$work/pass-push" "$work/push-with-inapplicable-signoff"
write_one "$work/push-with-inapplicable-signoff" sign-off pull_request conditional
printf "%s\n" "data['environment']['event'] = 'push'; data['applicable'] = False; data['status'] = 'not_applicable'" > "$work/push-with-inapplicable-signoff.py"
mutate "$work/push-with-inapplicable-signoff/sign-off.json" "$work/push-with-inapplicable-signoff.py"
expect_fail push-with-inapplicable-signoff 'push receipt set must not supply sign-off' "$work/push-with-inapplicable-signoff" push
refuse receipt-without-an-id 'has no check id' rust "data['id'] = ''"
refuse receipt-with-a-numeric-id 'has no check id' rust "data['id'] = 7"

echo "collect-assurance-receipts-cases: $cases cases gave the expected result (honest push and pull-request sets collected; the writer and the collector refuse a failed, skipped, missing, extra or absent command outcome)"
