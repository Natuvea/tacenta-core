#!/usr/bin/env bash
# Fail if any first-party declaration takes an evidence record `DispatchEvidenceVacuity.lean` shows
# false or empty, other than the vacuity module's own theorems.
#
# `Translation/DispatchEvidenceVacuity.lean` proves five evidence records of the lifecycle dispatch
# layer false, or empty, under stated conditions (`GAP-REGISTER.md`, `DISPATCH-EVIDENCE-VACUITY`;
# `CLAIMS.md`, the vacuity section). A theorem that took one again would be true and say nothing,
# and `#print axioms` would not show it. `Model.AxiomAudit.takers` walks an elaborated environment
# and lists every first-party declaration whose statement or value mentions a record, by name or
# through its constructor, recursor, `casesOn`/`recOn` or projections, and refuses unless the list
# is exactly the declarations it is given.
#
# This script runs that walk as the compiled executable `refuted-records` (the model package's
# lakefile; `Model/AxiomAudit.lean`'s `main`), once per translation audit module: the executable
# loads that module, and so its whole import closure, at run time with `importModules`, walks the
# loaded environment and prints what it found, and `check-audit-reach.sh` holds that every
# translation module is in some audit module's closure, so the five runs between them walk every
# translation module. The executable's source is compiled once, from `Model/AxiomAudit.lean`
# alone, so nothing a module of the tree declares (a `notation` on the walk's name, a `namespace`,
# a macro on `run_cmd`) is parsed anywhere the walk is called: that is why it is an executable and
# not a `run_cmd` in a module or in a probe, both of which parse under the tree's notations. The
# script reads the executable's own output rather than a build log, and the executable runs no
# initializer of the modules it loads (`importModules` with its default `loadExts := false`), so a
# module of the tree prints nothing the script reads. For each run the walk must accept, and the lines it prints must be exactly the
# block recorded below: the five records with their modules and kinds and the fifteen vacuity
# theorems over the Session unit's closure, the five records absent over the other four. A record
# moved, a theorem renamed, a new taker or a lost closure all change the block. Adding a theorem of
# the vacuity module to the Session block is a diff for review, which is the one thing no gate
# decides here. The list of audit modules is held to the one `check-audit-reach.sh` reaches from,
# so an audit module added there without a run here fails.
#
# What the walk does not see is recorded in `CLAIMS.md`: a theorem that restates the `def` record's
# body without naming it, a mention in a comment or string, an `example`.
# `check-refuted-records-negatives.sh` plants takers in a probe and checks the walk reports and
# refuses each; its header records which planted case each removed rule of the walk turns red.
#
# Needs the five translation audit modules built and current (checked with `lake build
# --no-build`; a stale olean would be a stale walk); builds the executable itself, which may write
# under the model package's build directory. Run from any directory. No source or git worktree is
# changed. `REFUTED_RECORDS_BIN` names another executable to run in place of the built one, and
# then neither the build nor the freshness check runs; `tooling/tests/run-check-refuted-records-cases.sh`
# uses it to feed this script a walk that refuses, prints other lines, or is never asked.
set -euo pipefail

cd "$(dirname "$0")/../.."

sites=(AxiomAudit AxiomAuditTripleUnit AxiomAuditBraidUnit AxiomAuditSessionUnit AxiomAuditLifecycle)

# The audit modules this script runs over are the translation ones `check-audit-reach.sh` reaches
# from, no fewer.
reach_sites=$(grep -o '"Translation/AxiomAudit[A-Za-z0-9]*\.lean"' tacenta-proofs/scripts/check-audit-reach.sh \
  | sed 's/"Translation\///; s/\.lean"//' | sort)
if [ "$reach_sites" != "$(printf '%s\n' "${sites[@]}" | sort)" ]; then
  echo "::error::refuted-records: the translation audit modules check-audit-reach.sh reaches from are not the ones this script runs over:" >&2
  diff <(printf '%s\n' "$reach_sites") <(printf '%s\n' "${sites[@]}" | sort) | sed 's/^/    /' >&2 || true
  exit 1
fi

# The first-party module roots the walk holds to: the ones `check-audit-reach.sh` holds every
# audit invocation to, read from it, so a narrower list would have to be edited in both.
prefixes=$(sed -n 's/^PREFIXES = "#\[\(.*\)\]"$/\1/p' tacenta-proofs/scripts/check-audit-reach.sh | tr -d '`' | tr ',' ' ')
# shellcheck disable=SC2086
if [ "$(echo $prefixes)" != "Model Properties Proofs Translation" ]; then
  echo "::error::refuted-records: could not read the first-party prefixes from check-audit-reach.sh (got '$prefixes')" >&2
  exit 1
fi
# shellcheck disable=SC2206
prefixes=($prefixes)

if [ -n "${REFUTED_RECORDS_BIN:-}" ]; then
  bin="$REFUTED_RECORDS_BIN"
else
  if ! (cd tacenta-model && lake build refuted-records 2>&1 | grep -v '^✔' | grep -v '^$'; exit "${PIPESTATUS[0]}"); then
    echo "::error::refuted-records: the executable did not build" >&2
    exit 1
  fi
  bin="$PWD/tacenta-model/.lake/build/bin/refuted-records"
  if [ ! -x "$bin" ]; then
    echo "::error::refuted-records: the executable was not built at $bin" >&2
    exit 1
  fi
  for site in "${sites[@]}"; do
    if ! (cd tacenta-proofs/translation && lake build --no-build "Translation.$site" > /dev/null 2>&1); then
      echo "::error::refuted-records: Translation.$site is not built, or its olean is stale; build the translation first" >&2
      exit 1
    fi
  done
fi

R=Tacenta.UnitLifecycleT3
V=Tacenta.DispatchEvidenceVacuity

# The fifteen theorems of the vacuity module that take a record (the refutations and their lemmas),
# each with the record it takes, in the order the walk prints them (by name).
session=(
  aeadConcreteEvidence_false_of_publicKeyNotConstant:InitialRatchetAeadConcreteEvidence
  aeadConcreteEvidence_forces_constant_dhPublic:InitialRatchetAeadConcreteEvidence
  codewordViewOf_false:CodewordViewOf
  codewordViewOf_false_of_encoderNewTotal:CodewordViewOf
  initialSameEphemeralEvidence_false:InitialSameEphemeralEvidence
  record_empty_ct1Acknowledged:InitialRatchetBraidEvidenceContracts
  record_empty_ct1Sampled_ek:InitialRatchetBraidEvidenceContracts
  record_empty_ct1Sampled_ekCt1Ack:InitialRatchetBraidEvidenceContracts
  record_empty_ekSentCt1Received:InitialRatchetBraidEvidenceContracts
  record_empty_headerSent:InitialRatchetBraidEvidenceContracts
  record_empty_noHeaderReceived:InitialRatchetBraidEvidenceContracts
  record_empty_of_nonempty_decoder:InitialRatchetBraidEvidenceContracts
  source_of_record:InitialRatchetBraidEvidenceContracts
  tripleConcreteEvidence_false_of_publicKeyNotConstant:InitialRatchetTripleConcreteEvidence
  tripleConcreteEvidence_forces_constant_dhPublic:InitialRatchetTripleConcreteEvidence
)

block_session() {
  echo "audit-record: Translation.UnitLifecycleInitialDispatch $R.InitialSameEphemeralEvidence (def)"
  echo "audit-record: Translation.UnitLifecycleT3 $R.CodewordViewOf (inductive)"
  echo "audit-record: Translation.UnitLifecycleInitialDispatch $R.InitialRatchetBraidEvidenceContracts (inductive)"
  echo "audit-record: Translation.UnitLifecycleInitialDispatch $R.InitialRatchetTripleConcreteEvidence (inductive)"
  echo "audit-record: Translation.UnitLifecycleInitialDispatch $R.InitialRatchetAeadConcreteEvidence (inductive)"
  local pair
  for pair in "${session[@]}"; do
    echo "audit-taker: Translation.DispatchEvidenceVacuity $V.${pair%%:*} (theorem) $R.${pair##*:}"
  done
}
block_absent() {
  local r
  for r in InitialSameEphemeralEvidence CodewordViewOf InitialRatchetBraidEvidenceContracts \
      InitialRatchetTripleConcreteEvidence InitialRatchetAeadConcreteEvidence; do
    echo "audit-record: $R.$r absent"
  done
}

fail=0
walked=0
for site in "${sites[@]}"; do
  if [ "$site" = AxiomAuditSessionUnit ]; then
    expected=("${session[@]%%:*}"); expected=("${expected[@]/#/$V.}")
    want=$(block_session)
  else
    expected=(); want=$(block_absent)
  fi
  set +e
  out=$(cd tacenta-proofs/translation && lake env "$bin" "Translation.$site" --prefixes "${prefixes[@]}" --records \
    "$R.InitialSameEphemeralEvidence" "$R.CodewordViewOf" "$R.InitialRatchetBraidEvidenceContracts" \
    "$R.InitialRatchetTripleConcreteEvidence" "$R.InitialRatchetAeadConcreteEvidence" \
    --expected ${expected[@]+"${expected[@]}"} 2>&1)
  status=$?
  set -e
  printed=$(printf '%s\n' "$out" | grep '^audit-' || true)
  if [ $status -ne 0 ]; then
    echo "::error::refuted-records: the walk over Translation.$site refused (exit $status):" >&2
    printf '%s\n' "$out" | sed 's/^/    /' >&2
    fail=1
  elif [ "$printed" != "$want" ]; then
    echo "::error::refuted-records: the walk over Translation.$site printed other lines than recorded:" >&2
    diff <(printf '%s\n' "$want") <(printf '%s\n' "$printed") | sed 's/^/    /' >&2 || true
    fail=1
  else
    walked=$((walked + 1))
  fi
done

if [ $fail -ne 0 ]; then exit 1; fi
echo "refuted-records: the five evidence records DispatchEvidenceVacuity.lean refutes are taken by nothing but its ${#session[@]} theorems, over the import closures of all $walked translation audit modules${REFUTED_RECORDS_BIN:+ (walked by the stand-in $REFUTED_RECORDS_BIN, not the built executable)}"
