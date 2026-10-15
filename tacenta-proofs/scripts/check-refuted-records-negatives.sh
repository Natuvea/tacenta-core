#!/usr/bin/env bash
# Fail if `Model.AxiomAudit.takers` does not report a planted taker of a refuted evidence record,
# or reports honest code that takes none.
#
# `Translation/DispatchEvidenceVacuity.lean` shows five evidence records of the lifecycle dispatch
# layer false or empty. `takersReport`, run by `check-refuted-records.sh` as an executable over each
# translation audit module's closure, lists from the environment each first-party declaration whose statement or value
# mentions one, by name or through the record's structure machinery, and refuses unless the list is
# exactly the declarations it is given (fifteen theorems of the vacuity module over the Session
# unit's closure; none over the other four); the gate compares its printed lines. `takers` is the
# same walk as a command, for these probes, which plant takers where they are declared. The gate shows
# what the walk found in the real tree; this script asks whether the walk finds a taker at all,
# under each spelling a text scan was shown to miss and each route a cold read of the walk raised:
# an unqualified name under `open … in`, an alias, a `where` clause, a `set_option … in`, a `nonrec
# def`, a `notation`, a declaration a macro assembles, a structure field, a `variable`, a mention
# only in a proof term, a name under the record's own namespace, a `private` theorem, the record's
# constructor alone, and an alias wearing the `def` record's flat-constructor name.
#
# Each case is a throwaway first-party module (`Translation/AuditProbe.lean` under a temporary
# root, so its constants are first-party) that imports the vacuity module, holds the case's Lean,
# and runs the command with the fifteen vacuity theorems as the expected takers, as
# the gate does over the Session unit. The command prints what it found and then refuses if
# the takers are not exactly the expected ones. So a `taker:` case must exit 1, print the
# `audit-taker:` line for each named declaration with its kind and record, and name it in the
# refusal, and the refusal must be its only error; a `clean` case must exit 0 and report no
# declaration of the probe. Every case run through `run` must print the five `audit-record:` lines
# naming the records' real modules and the fifteen `audit-taker:` lines of the imported vacuity
# module (the anchor that the probe sees the records and that a taker in an imported module is
# seen: a probe that imported nothing, or a walk that skipped imported modules, would find every
# case clean). One case names the probe `Translation.UnitAuditProbe`, like the unit's own modules.
# One case declares records of its own, so the own-module half of the machinery exemption is
# exercised where it applies. Four cases hold the command's own refusals and its absent arm: an
# expected name that takes nothing, no record named, a record declared outside the first-party
# prefixes, and (as over the four other audit modules' closures) every record absent, which must print `absent`
# and refuse nothing.
#
# Validated by breaking `takers` one rule at a time, rebuilding the model and re-running (redo it
# after changing either file; last run 2026-10-13):
#
#   rule removed from Model/AxiomAudit.lean          cases that go red
#   ----------------------------------------         -----------------
#   `c.type.getUsedConstants` (statements unread)    every case run through `run`: some of the
#                                                      fifteen anchor lines vanish (imported
#                                                      theorems seen only by their statements),
#                                                      so honest goes red too; own-records
#   the value half (values unread)                   alias, nonrec-def, value-only,
#                                                      constructor-route, flat-ctor-alias,
#                                                      own-records
#   machinery names not counted as mentions          constructor-route (own-records' structure
#                                                      taker names its record in a binder type
#                                                      and stays green; its inductive-route taker
#                                                      names only the constructor and goes red)
#   a flat-constructor exemption by name pattern,    own-records
#     confined to the record's module
#   `Translation.Unit*` modules skipped              unit-named-module
#   the `absent` arm (the command throws instead)    absent
#   the `unexpected` refusal                         every taker case (the command exits 0)
#   the `unfound` refusal                            expected-not-a-taker
#   `recordMachinery` (nothing set aside)            own-records, honest (the real records'
#                                                      machinery is listed and refused); the
#                                                      Session unit's invocation fails too
#
# Run from any directory. Needs the model package and `Translation.DispatchEvidenceVacuity` built.
set -euo pipefail

cd "$(dirname "$0")/../.."

root=$(mktemp -d)
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/Translation"
probe="$root/Translation/AuditProbe.lean"

R=Tacenta.UnitLifecycleT3
V=Tacenta.DispatchEvidenceVacuity
vacuity=(aeadConcreteEvidence_false_of_publicKeyNotConstant:InitialRatchetAeadConcreteEvidence
  aeadConcreteEvidence_forces_constant_dhPublic:InitialRatchetAeadConcreteEvidence
  codewordViewOf_false:CodewordViewOf codewordViewOf_false_of_encoderNewTotal:CodewordViewOf
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
  tripleConcreteEvidence_forces_constant_dhPublic:InitialRatchetTripleConcreteEvidence)
expected=""
for pair in "${vacuity[@]}"; do expected="$expected, \`$V.${pair%%:*}"; done
expected="#[${expected#, }]"
records="#[\`$R.InitialSameEphemeralEvidence, \`$R.CodewordViewOf, \`$R.InitialRatchetBraidEvidenceContracts, \`$R.InitialRatchetTripleConcreteEvidence, \`$R.InitialRatchetAeadConcreteEvidence]"
prefixes="#[\`Model, \`Properties, \`Proofs, \`Translation]"
call="run_cmd Model.AxiomAudit.takers $prefixes $records $expected"
anchor=(
  "audit-record: Translation.UnitLifecycleInitialDispatch $R.InitialSameEphemeralEvidence (def)"
  "audit-record: Translation.UnitLifecycleT3 $R.CodewordViewOf (inductive)"
  "audit-record: Translation.UnitLifecycleInitialDispatch $R.InitialRatchetBraidEvidenceContracts (inductive)"
  "audit-record: Translation.UnitLifecycleInitialDispatch $R.InitialRatchetTripleConcreteEvidence (inductive)"
  "audit-record: Translation.UnitLifecycleInitialDispatch $R.InitialRatchetAeadConcreteEvidence (inductive)"
)

for pair in "${vacuity[@]}"; do
  anchor+=("audit-taker: Translation.DispatchEvidenceVacuity $V.${pair%%:*} (theorem) $R.${pair##*:}")
done

pass=0
fail=0

module=AuditProbe # the probe's module under Translation/; a case may change it
elaborate() { # the probe, in a fresh lean; output in $out, status in $status
  set +e
  out=$(cd tacenta-proofs/translation \
        && lake env sh -c "cd '$root' && lean Translation/$module.lean" 2>&1)
  status=$?
  set -e
}

red() { # <case> <why>
  fail=$((fail + 1))
  echo "::error::refuted-records-negatives: case '$1' $2:"
  echo "$out" | sed 's/^/    /'
}

# run <name> <expectation...> -- the case's Lean is read from stdin. An expectation is `clean`, or
# one or more `<decl>:<kind>:<record>` triples, each of which must be printed for the probe on one
# line and named in the refusal. The matches are shell patterns on single lines of the output
# (no pipe into grep: under pipefail `grep -q` can leave the writer with SIGPIPE and a green case
# read as red).
has_line() { # <pattern>: some line of $out matches it whole
  local line
  while IFS= read -r line; do
    # shellcheck disable=SC2254
    case "$line" in $1) return 0 ;; esac
  done <<<"$out"
  return 1
}
run() {
  local name=$1; shift
  probe="$root/Translation/$module.lean"
  { echo "import Model.AxiomAudit"; echo "import Translation.DispatchEvidenceVacuity"; cat; echo "$call"; } > "$probe"
  elaborate
  local a
  for a in "${anchor[@]}"; do
    if ! has_line "$a"; then red "$name" "ran without the anchor line '$a'"; return; fi
  done
  if [ "$1" = clean ]; then
    if [ $status -ne 0 ]; then red "$name" "should be clean, and the command refused (exit $status)"; return; fi
    if has_line "audit-taker: Translation.$module *"; then
      red "$name" "should be clean, and a declaration of the probe was reported"; return
    fi
    pass=$((pass + 1)); return
  fi
  if [ $status -ne 1 ]; then red "$name" "should be refused, and exited $status"; return; fi
  if ! has_line "Translation/$module.lean:*: error: refuted-record audit: the takers of 5 refuted record(s) are not the 15 declaration(s) named:"; then
    red "$name" "was refused, but not for an unexpected taker"; return
  fi
  # The refusal is the only error: the planted Lean elaborated.
  local errors
  errors=$(printf '%s\n' "$out" | grep -c ': error' || true)
  if [ "$errors" -ne 1 ]; then red "$name" "had $errors errors, expected the refusal alone"; return; fi
  local triple
  for triple in "$@"; do
    local decl=${triple%%:*} rest=${triple#*:} kind record
    kind=${rest%%:*}; record=${rest##*:}
    if ! has_line "audit-taker: Translation.$module $decl ($kind) $R.$record"; then
      red "$name" "should print $decl ($kind) taking $record, and did not"; return
    fi
    if ! has_line "  $decl (Translation.$module) takes $R.$record"; then
      red "$name" "should name $decl in the refusal, and did not"; return
    fi
  done
  pass=$((pass + 1))
}

# Each of the five records, taken by a theorem under its full name.
run direct planted1:theorem:InitialSameEphemeralEvidence planted2:theorem:CodewordViewOf \
    planted3:theorem:InitialRatchetBraidEvidenceContracts planted4:theorem:InitialRatchetTripleConcreteEvidence \
    planted5:theorem:InitialRatchetAeadConcreteEvidence <<EOF2
theorem planted1 (_h : $R.InitialSameEphemeralEvidence a b c d) : True := trivial
theorem planted2 (_h : $R.CodewordViewOf v) : True := trivial
theorem planted3 (K : Model.Braid.Kem) (_h : @$R.InitialRatchetBraidEvidenceContracts K a b c d) : True := trivial
theorem planted4 (_h : $R.InitialRatchetTripleConcreteEvidence a b c d) : True := trivial
theorem planted5 (_h : $R.InitialRatchetAeadConcreteEvidence a b c d) : True := trivial
EOF2

# The spellings the text scan missed.
run open-in plantedOpen:theorem:CodewordViewOf <<EOF2
open $R in
theorem plantedOpen (_h : CodewordViewOf v) : True := trivial
EOF2

run alias CWAlias:def:CodewordViewOf <<EOF2
abbrev CWAlias (v : Model.Lifecycle.CodewordView) : Prop := $R.CodewordViewOf v
theorem throughAlias (_h : CWAlias v) : True := trivial
EOF2

run set-option-in plantedOpt:theorem:CodewordViewOf <<EOF2
set_option linter.unusedVariables false in
theorem plantedOpt (h : $R.CodewordViewOf v) : True := trivial
EOF2

run nonrec-def plantedNonrec:def:CodewordViewOf <<EOF2
nonrec def plantedNonrec (v : Model.Lifecycle.CodewordView) : Prop := $R.CodewordViewOf v
EOF2

run where-clause plantedWhere.helper:theorem:CodewordViewOf <<EOF2
theorem plantedWhere : True := trivial
where helper (v : Model.Lifecycle.CodewordView) (_h : $R.CodewordViewOf v) : True := trivial
EOF2

run notation plantedNotation:theorem:CodewordViewOf <<EOF2
notation "CW" v => $R.CodewordViewOf v
theorem plantedNotation (_h : CW v) : True := trivial
EOF2

run macro-assembled macroTaker:theorem:CodewordViewOf <<EOF2
macro "plant_taker" n:ident : command => \`(theorem \$n (v : Model.Lifecycle.CodewordView) (_h : $R.CodewordViewOf v) : True := trivial)
plant_taker macroTaker
EOF2

run structure-field Plant.mk:constructor:CodewordViewOf Plant.h:theorem:CodewordViewOf <<EOF2
structure Plant (v : Model.Lifecycle.CodewordView) : Prop where
  h : $R.CodewordViewOf v
EOF2

run variable plantedVar:theorem:CodewordViewOf <<EOF2
variable (h : $R.CodewordViewOf v)
include h in
theorem plantedVar : True := trivial
EOF2

# The record is in the proof term only: the statement mentions nothing.
run value-only plantedValue:theorem:InitialSameEphemeralEvidence <<EOF2
theorem plantedValue : True := by
  have := @Tacenta.DispatchEvidenceVacuity.initialSameEphemeralEvidence_false
  trivial
EOF2

# A declaration under the record's own namespace is not its machinery.
run own-namespace $R.CodewordViewOf.planted:theorem:CodewordViewOf <<EOF2
theorem $R.CodewordViewOf.planted (_h : $R.CodewordViewOf v) : True := trivial
EOF2

# A private theorem is reported under its mangled name.
run private-theorem _private.Translation.AuditProbe.0.plantedPrivate:theorem:CodewordViewOf <<EOF2
private theorem plantedPrivate (_h : $R.CodewordViewOf v) : True := trivial
EOF2

# A declaration that names only the record's constructor, not the record: it builds a term of the
# record from its fields and hands it to a lemma.
run constructor-route plantedCtor:theorem:CodewordViewOf <<EOF2
open Aeneas Aeneas.Std Result tacenta_session_unit Tacenta.UnitLifecycleT3 Tacenta.DispatchEvidenceVacuity in
theorem plantedCtor (view : Model.Lifecycle.CodewordView) (n : Usize) (hn : 33 ≤ n.val)
    (e1 e2 : tacenta_erasure.Encoder)
    (h1 : tacenta_erasure.Encoder.new (sliceA n) = ok e1)
    (h2 : tacenta_erasure.Encoder.new (sliceB n) = ok e2)
    (hr : ∀ state source chunk, Tacenta.SessionUnitBraidT3.CodewordOf source chunk →
      view.receive state (UInt16.ofNat chunk.index.val) (arrayOf chunk.data) = modelChunkOf source chunk)
    (hs : ∀ state source chunk, Tacenta.SessionUnitBraidT3.CodewordOf source chunk →
      view.send state (modelChunkOf source chunk) = modelCodewordOf chunk) : False :=
  codewordViewOf_false view n hn e1 e2 h1 h2 (CodewordViewOf.mk hr hs)
EOF2

# The `def` record has no flat constructor; a definition wearing that name is an alias and is
# reported, not set aside.
run flat-ctor-alias $R.InitialSameEphemeralEvidence.mk._flat_ctor:def:InitialSameEphemeralEvidence <<EOF2
abbrev $R.InitialSameEphemeralEvidence.mk._flat_ctor := @$R.InitialSameEphemeralEvidence
EOF2

# A probe named like the unit's own modules: a walk that skipped `Translation.Unit*` would miss it.
module=UnitAuditProbe
run unit-named-module plantedUnit:theorem:CodewordViewOf <<EOF2
theorem plantedUnit (_h : $R.CodewordViewOf v) : True := trivial
EOF2
module=AuditProbe
probe="$root/Translation/$module.lean"

# Records of the probe's own: the probe declares a structure record, a plain inductive record and
# a `def` record and is named as their module, so the exemption's own-module half is exercised
# where it applies. An `abbrev` wearing the `def` record's flat-constructor name in that module is
# an alias and is reported; so is a declaration that builds the structure record (it also names it
# in a binder type) and one that names only the inductive record's constructor; the real
# constructors, recursors and projection are set aside.
{ echo "import Model.AxiomAudit"
  cat <<EOF2
structure ProbeRecord (n : Nat) : Prop where
  pos : 0 < n
def ProbeDef (n : Nat) : Prop := 0 < n
abbrev ProbeDef.mk._flat_ctor (n : Nat) : Prop := ProbeDef n
theorem probeCtorRoute (n : Nat) (h : 0 < n) : (fun (_ : ProbeRecord n) => True) (ProbeRecord.mk h) := trivial
inductive ProbeInd : Prop where
  | intro (h : True)
def consumeInd (_ : ProbeInd) : True := trivial
theorem probeIndRoute : True := consumeInd (ProbeInd.intro trivial)
EOF2
  echo "run_cmd Model.AxiomAudit.takers $prefixes #[\`ProbeRecord, \`ProbeInd, \`ProbeDef] #[]"; } > "$probe"
elaborate
if [ $status -ne 1 ] || ! has_line "  ProbeDef.mk._flat_ctor (Translation.AuditProbe) takes ProbeDef" \
  || ! has_line "  probeCtorRoute (Translation.AuditProbe) takes ProbeRecord" \
  || ! has_line "  consumeInd (Translation.AuditProbe) takes ProbeInd" \
  || ! has_line "  probeIndRoute (Translation.AuditProbe) takes ProbeInd" \
  || has_line "audit-taker: * ProbeRecord.mk *" || has_line "audit-taker: * ProbeRecord.rec *" \
  || has_line "audit-taker: * ProbeRecord.pos *" || has_line "audit-taker: * ProbeRecord.mk._flat_ctor *" \
  || has_line "audit-taker: * ProbeInd.intro *" || has_line "audit-taker: * ProbeInd.rec *" \
  || has_line "audit-taker: * ProbeInd.casesOn *"; then
  red own-records "should refuse the def record's flat-constructor alias, the structure taker and the inductive constructor-route takers in the records' own module, and set aside the real machinery (exit $status)"
else
  pass=$((pass + 1))
fi

# A record declared outside the first-party prefixes is refused: the probe is at `Other/`.
mkdir -p "$root/Other"
{ echo "import Model.AxiomAudit"; echo "def OtherRecord : Prop := True"
  echo "run_cmd Model.AxiomAudit.takers $prefixes #[\`OtherRecord] #[]"; } > "$root/Other/AuditProbe.lean"
set +e
out=$(cd tacenta-proofs/translation && lake env sh -c "cd '$root' && lean Other/AuditProbe.lean" 2>&1)
status=$?
set -e
if [ $status -ne 1 ] || ! has_line "*refuted-record audit: OtherRecord is declared in Other.AuditProbe, outside the first-party prefixes*"; then
  red outside-prefixes "should be refused for a record outside the first-party prefixes (exit $status)"
else
  pass=$((pass + 1))
fi

# Honest code: look-alike names, the replacement record, a mention in a docstring and a string,
# and an `example`, which leaves no constant.
run honest clean <<EOF2
def CodewordViewOfX : Prop := True
theorem lookAlike (_h : CodewordViewOfX) : True := trivial
/-- Names \`$R.CodewordViewOf\` and \`InitialSameEphemeralEvidence\` in prose. -/
theorem replacement (_h : $R.CodewordViewSendOf v) : "$R.CodewordViewOf" = "$R.CodewordViewOf" := rfl
example (_h : $R.CodewordViewOf v) : True := trivial
EOF2

# No record imported: each is reported absent, nothing is reported taken, and the command
# refuses nothing. This is the output the gate records over the four other audit modules' closures.
{ echo "import Model.AxiomAudit"; echo "run_cmd Model.AxiomAudit.takers $prefixes $records #[]"; } > "$probe"
elaborate
if [ $status -ne 0 ]; then
  red absent "did not elaborate (exit $status)"
elif has_line "audit-taker: *"; then
  red absent "should report no taker"
else
  ok=1
  for r in InitialSameEphemeralEvidence CodewordViewOf InitialRatchetBraidEvidenceContracts \
      InitialRatchetTripleConcreteEvidence InitialRatchetAeadConcreteEvidence; do
    has_line "audit-record: $R.$r absent" || ok=0
  done
  if [ $ok -eq 1 ]; then pass=$((pass + 1)); else red absent "should report every record absent"; fi
fi

# An expected name that takes no record is refused: the list the invocation holds is exact.
{ echo "import Model.AxiomAudit"; echo "import Translation.DispatchEvidenceVacuity"
  echo "run_cmd Model.AxiomAudit.takers $prefixes $records ${expected%]}, \`Translation.AuditProbe.nobody]"; } > "$probe"
elaborate
if [ $status -ne 1 ] || ! has_line "  Translation.AuditProbe.nobody is named as a taker and takes no record here"; then
  red expected-not-a-taker "should be refused for the expected name that takes nothing (exit $status)"
else
  pass=$((pass + 1))
fi

# No record named is refused.
{ echo "import Model.AxiomAudit"; echo "run_cmd Model.AxiomAudit.takers $prefixes #[] #[]"; } > "$probe"
elaborate
if [ $status -ne 1 ] || ! has_line "*refuted-record audit: no record named*"; then
  red no-record "should be refused for naming no record (exit $status)"
else
  pass=$((pass + 1))
fi

# The executable, over a compiled module that plants a taker, an `initialize` that prints a forged
# line, and a `notation` on the walk's whole name: the walk must report the taker and refuse, the
# forged line must not appear (the executable runs no initializer of the modules it loads), and the
# notation must change nothing (the executable's source was compiled once, from the audit alone).
# The module is compiled to an olean under a root of its own, which is put first on the search
# path; it lives under `Proofs/`, a first-party top directory no other search-path entry has (Lean
# resolves a module at the first root that holds its top directory, so a root with a `Translation/`
# directory, like the probe root above, would hide the real `Translation/` oleans).
exe="$PWD/tacenta-model/.lake/build/bin/refuted-records"
if (cd tacenta-model && lake build refuted-records 2>&1 | grep -v '^✔' | grep -v '^$'; exit "${PIPESTATUS[0]}") && [ -x "$exe" ]; then
  exeroot="$root/exe"
  mkdir -p "$exeroot/Proofs"
  cat > "$exeroot/Proofs/ExeProbe.lean" <<EOF2
import Lean
import Translation.DispatchEvidenceVacuity
open Lean in
initialize do IO.println "audit-taker: Proofs.ExeProbe forged (theorem) $R.CodewordViewOf"
notation "_root_.Model.AxiomAudit.takers" => fun {α : Type} (_ _ _ _ : Array α) => (pure () : IO Unit)
theorem plantedExe (_h : $R.CodewordViewOf v) : True := trivial
EOF2
  set +e
  out=$(cd tacenta-proofs/translation && lake env sh -c "cd '$exeroot' && lean -o Proofs/ExeProbe.olean Proofs/ExeProbe.lean && LEAN_PATH=\"$exeroot:\$LEAN_PATH\" '$exe' Proofs.ExeProbe --prefixes Model Properties Proofs Translation --records $R.CodewordViewOf --expected $V.codewordViewOf_false $V.codewordViewOf_false_of_encoderNewTotal" 2>&1)
  status=$?
  set -e
  if [ $status -ne 1 ] || ! has_line "audit-taker: Proofs.ExeProbe plantedExe (theorem) $R.CodewordViewOf" \
    || ! has_line "  plantedExe (Proofs.ExeProbe) takes $R.CodewordViewOf" || has_line "*forged*"; then
    red executable-over-a-planted-module "should report and refuse the taker, print no forged line and ignore the notation (exit $status)"
  else
    pass=$((pass + 1))
  fi
else
  red executable-over-a-planted-module "the executable did not build at $exe"
fi

if [ $fail -ne 0 ]; then
  echo "::error::refuted-records-negatives: $fail of $((pass + fail)) planted cases came out wrong; Model.AxiomAudit.takers is not reporting what it says it reports."
  exit 1
fi
echo "refuted-records-negatives: the walk called all $pass planted cases correctly (each record taken directly; open-in, alias, set_option-in, nonrec, where, notation, macro, structure-field, variable, proof-term-only, own-namespace, private and constructor-route takers, an alias wearing the def record's flat-constructor name, a taker in a Unit-named module, and records of the probe's own, structure, inductive and def, with their machinery set aside; honest look-alikes, the replacement record, prose mentions and an example clean; every record absent when unimported; an expected name that takes nothing, an empty record list and a record outside the prefixes refused; the executable over a compiled module with a taker, a forging initializer and a notation on its name reports the taker and nothing else)"
