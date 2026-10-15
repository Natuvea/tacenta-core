#!/usr/bin/env bash
# Fail if `tacenta-proofs/scripts/check-refuted-records.sh` accepts a walk that refuses, prints other
# lines than it records, or is never run over one of its five closures.
#
# The script runs the `refuted-records` executable once per translation audit module and compares
# its output with a recorded block. These cases replace the executable, through `REFUTED_RECORDS_BIN`,
# with a stand-in that records what it was asked and answers as told: the recorded block for every
# closure (accepted), a refusal at one closure, one line missing, one line extra, a changed module
# in a record line, and a run that never asks for the Session unit. The stand-in's blocks are
# derived from the script's own, read back from it, so a block edited there is not matched here by
# a stale copy. The repository is never written, and no toolchain is needed: `lake env` is stubbed.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
gate="$root/tacenta-proofs/scripts/check-refuted-records.sh"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# The script runs the walk through `lake env`; these cases need no toolchain (CI runs them in a job
# without one), so a stub `lake` goes first on PATH: `lake env <cmd> <args>` runs the command.
mkdir -p "$work/stub"
cat > "$work/stub/lake" <<'STUB'
#!/usr/bin/env bash
if [ "$1" = env ]; then shift; exec "$@"; fi
echo "stub lake: unexpected invocation: $*" >&2; exit 1
STUB
chmod +x "$work/stub/lake"
export PATH="$work/stub:$PATH"

R=Tacenta.UnitLifecycleT3
V=Tacenta.DispatchEvidenceVacuity
# The blocks, as the script defines them: source its two functions and its `session` array.
eval "$(sed -n '/^session=(/,/^)/p' "$gate")"
eval "$(sed -n '/^block_session() {/,/^}/p' "$gate")"
eval "$(sed -n '/^block_absent() {/,/^}/p' "$gate")"

pass=0
fail=0
wrong() { fail=$((fail + 1)); echo "WRONG  $1: $2"; echo "$out" | sed 's/^/    /' | head -8; }

# standin <mode>: writes the stand-in executable for one case.
standin() {
  cat > "$work/bin" <<STANDIN
#!/usr/bin/env bash
echo "\$1" >> "$work/asked"
printf '[%s]' "\$@" >> "$work/args"; echo >> "$work/args"
mode="$1"
if [ "\$1" = Translation.AxiomAuditSessionUnit ]; then
  block="\$(cat "$work/session")"
else
  block="\$(cat "$work/absent")"
fi
case "\$mode" in
  honest) printf '%s\n' "\$block" ;;
  refuse-session)
    printf '%s\n' "\$block"
    if [ "\$1" = Translation.AxiomAuditSessionUnit ]; then echo "refuted-record audit: planted taker" >&2; exit 1; fi ;;
  missing-line) printf '%s\n' "\$block" | grep -v 'source_of_record' ;;
  extra-line) printf '%s\n' "\$block"; echo "audit-taker: Translation.X Tacenta.X.planted (theorem) $R.CodewordViewOf" ;;
  moved-record) printf '%s\n' "\$block" | sed 's/Translation.UnitLifecycleT3 /Translation.Elsewhere /' ;;
esac
exit 0
STANDIN
  chmod +x "$work/bin"
}
block_session > "$work/session"
block_absent > "$work/absent"

run_gate() { # <mode>; output in $out, exit in $rc, closures asked in $work/asked, arguments in $work/args
  : > "$work/asked"; : > "$work/args"
  standin "$1"
  set +e
  out=$(REFUTED_RECORDS_BIN="$work/bin" bash "$gate" 2>&1)
  rc=$?
  set -e
}

run_gate honest
if [ "$rc" -ne 0 ]; then wrong honest "the recorded blocks were refused"; else pass=$((pass + 1)); fi
if [ "$(sort "$work/asked" | tr '\n' ' ')" != "Translation.AxiomAudit Translation.AxiomAuditBraidUnit Translation.AxiomAuditLifecycle Translation.AxiomAuditSessionUnit Translation.AxiomAuditTripleUnit " ]; then
  wrong closures-asked "the five closures were not each asked once: $(tr '\n' ' ' < "$work/asked")"
else
  pass=$((pass + 1))
fi
# The arguments: every closure is asked with the four first-party roots, the five records in order,
# and the expected list the recorded block names (fifteen names at the Session unit, none elsewhere).
records_args="--records $R.InitialSameEphemeralEvidence $R.CodewordViewOf $R.InitialRatchetBraidEvidenceContracts $R.InitialRatchetTripleConcreteEvidence $R.InitialRatchetAeadConcreteEvidence"
session_expected=""
for pair in "${session[@]}"; do session_expected="$session_expected $V.${pair%%:*}"; done
ok=1
bracket() { local s="" a; for a in "$@"; do s="$s[$a]"; done; printf '%s' "$s"; }
# shellcheck disable=SC2086
while IFS= read -r line; do
  site=${line#[}; site=${site%%]*}
  if [ "$site" = Translation.AxiomAuditSessionUnit ]; then
    want=$(bracket "$site" --prefixes Model Properties Proofs Translation $records_args --expected $session_expected)
  else
    want=$(bracket "$site" --prefixes Model Properties Proofs Translation $records_args --expected)
  fi
  [ "$line" = "$want" ] || { ok=0; echo "    asked: $line"; echo "    want:  $want"; }
done < "$work/args"
if [ $ok -eq 1 ]; then pass=$((pass + 1)); else fail=$((fail + 1)); echo "WRONG  arguments: a closure was asked with other roots, records or expected names than the script records"; fi

for mode in refuse-session missing-line extra-line moved-record; do
  run_gate "$mode"
  if [ "$rc" -eq 0 ]; then wrong "$mode" "accepted (exit 0)"; continue; fi
  case "$mode" in
    refuse-session) needle="refused (exit 1)" ;;
    *) needle="printed other lines than recorded" ;;
  esac
  if [[ "$out" != *"$needle"* ]]; then wrong "$mode" "refused, but not as '$needle'"; continue; fi
  pass=$((pass + 1))
done

# The script's list of closures must be the reach check's: a copy of the script that drops one
# is refused before any walk runs.
sed 's/sites=(AxiomAudit AxiomAuditTripleUnit AxiomAuditBraidUnit AxiomAuditSessionUnit AxiomAuditLifecycle)/sites=(AxiomAudit AxiomAuditTripleUnit AxiomAuditBraidUnit AxiomAuditLifecycle)/' "$gate" > "$work/gate-short.sh"
grep -q 'sites=(AxiomAudit AxiomAuditTripleUnit AxiomAuditBraidUnit AxiomAuditLifecycle)' "$work/gate-short.sh"
mkdir -p "$work/T/tacenta-proofs/scripts"
cp "$work/gate-short.sh" "$work/T/tacenta-proofs/scripts/check-refuted-records.sh"
cp "$root/tacenta-proofs/scripts/check-audit-reach.sh" "$work/T/tacenta-proofs/scripts/"
: > "$work/asked"; standin honest
set +e
out=$(REFUTED_RECORDS_BIN="$work/bin" bash "$work/T/tacenta-proofs/scripts/check-refuted-records.sh" 2>&1)
rc=$?
set -e
if [ "$rc" -eq 0 ] || [[ "$out" != *"are not the ones this script runs over"* ]]; then
  wrong dropped-closure "a script that runs over four closures was not refused (exit $rc)"
else
  pass=$((pass + 1))
fi

if [ $fail -ne 0 ]; then
  echo "check-refuted-records-cases: $fail of $((pass + fail)) cases wrong"
  exit 1
fi
echo "check-refuted-records-cases: $pass cases (the recorded blocks accepted over the five closures, each asked once with the recorded roots, records and expected names; a refusal, a missing line, an extra line and a moved record refused; a script that runs over fewer closures than the reach check refused)"
