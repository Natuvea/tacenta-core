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
#   pin lists              -- a required pin deleted or left in a comment, a
#                             compiler-trust pin the script does not list, a
#                             pin block copied over another
#   statement pins         -- a required statement pin deleted, commented out,
#                             moved into a docstring or a string, left without
#                             its `#guard_msgs`, given an option that compares
#                             nothing, nested under another `... in`, written
#                             inside a namespace (also one that a `mutual` block
#                             follows), moved to a module no audit imports,
#                             dropped from the floor, or the floor's record
#                             missing, unreadable, keyless or emptied
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

# The cases must give the same result on a developer's machine and on the CI
# runner, where GITHUB_ACTIONS is set and the allowlist writer refuses to run;
# only the case that tests that refusal sets it.
attest() {
  (cd "$work" && env -u GITHUB_ACTIONS python3 tacenta-proofs/scripts/attest.py "$@" 2>&1)
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
  (cd "$work" && env -u GITHUB_ACTIONS bash "tacenta-proofs/scripts/$1" 2>&1)
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
python3 - "$work/tacenta-proofs/translation/Translation/UnitLifecyclePublicT1.lean" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
pattern = re.compile(
    r"/--\s*info: 'Tacenta\.UnitLifecycleT1\.encrypt_no_panic' depends on axioms: "
    r"\[.*?\]\s*-/\s*\n#guard_msgs in\s*\n"
    r"#print axioms\s+Tacenta\.UnitLifecycleT1\.encrypt_no_panic\n",
    re.S,
)
text, count = pattern.subn("", text)
if count != 1:
    raise SystemExit(f"expected one Session T1 pin, removed {count}")
path.write_text(text)
PY
expect_fail "claimed-session-t1-without-pin" 'claimed Session T1 theorem `Tacenta.UnitLifecycleT1.encrypt_no_panic` is not axiom-pinned' --check

make_case
rm "$work/tacenta-proofs/manifests/verification-manifest.json"
expect_fail "missing-verification-manifest" "tacenta-proofs/manifests/verification-manifest.json is missing" --check

make_case
edit_json tacenta-proofs/manifests/source-commit-attestation.json 'data["p9_mutation"] = "stale"'
expect_fail "stale-source-attestation" "tacenta-proofs/manifests/source-commit-attestation.json is stale" --check

# ---------------------------------------------------------------------------
# Pin lists. A pin block that is deleted, or edited to list a compiler-trust
# axiom, leaves a manifest that regenerates cleanly; the required-pin floor and
# the compiler-trust ceiling in attest.py are what refuse both. The mutations
# are made in the session lifecycle pins, and each is refused by the build of
# the manifest itself, so the expected text is the script's own diagnostic.
# ---------------------------------------------------------------------------

session_pins="tacenta-proofs/translation/Translation/UnitLifecyclePublicT1.lean"

for n in encrypt_no_panic decrypt_no_panic decrypt_ratchet_no_panic \
         establish_initiator_for_no_panic establish_responder_no_panic \
         invariant_gives_preconditions; do
  make_case
  python3 - "$work/$session_pins" "Tacenta.UnitLifecycleT1.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "required-pin-deleted-$n" "\`Tacenta.UnitLifecycleT1.$n\` is on REQUIRED_PINS and has no axiom pin" --check
  if [ "$n" = "encrypt_no_panic" ]; then
    expect_fail "required-pin-deleted-refused-by-refresh" "\`Tacenta.UnitLifecycleT1.$n\` is on REQUIRED_PINS and has no axiom pin"
  fi
done

vacuity_pins="tacenta-proofs/translation/Translation/SessionBraidReceiveVacuity.lean"
for n in decoderMessage_not_total braidReceiveContractsUnbounded_false decryptRatchetContractsUnbounded_false \
         establishResponderContractsUnbounded_empty message_eq_messageP all_tr_refute; do
  make_case
  python3 - "$work/$vacuity_pins" "Tacenta.SessionBraidReceiveVacuity.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "required-pin-deleted-vacuity-$n" "\`Tacenta.SessionBraidReceiveVacuity.$n\` is on REQUIRED_PINS and has no axiom pin" --check
done

repair_pins="tacenta-proofs/translation/Translation/SessionBraidReceiveRepair.lean"
for n in old_witness boundary_gt_max_codewords divCeilValue_shape_satisfiable \
         decoderMessageTotal_is DivCeilValue_is \
         old_witness_fails_bounded_premise old_witness_rejected_by_invariant \
         decoderMessageTotal_of_truncate bounded_holds_unbounded_fails \
         message_total_of_invariant boundary_exact mutant_premise_at_boundary_refuted; do
  make_case
  python3 - "$work/$repair_pins" "Tacenta.SessionBraidReceiveRepair.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "required-pin-deleted-repair-$n" "\`Tacenta.SessionBraidReceiveRepair.$n\` is on REQUIRED_PINS and has no axiom pin" --check
done

bound_pins="tacenta-proofs/translation/Translation/SessionUnitDecoderBound.lean"
for n in add_chunk_keeps_needed clone_keeps_needed invariant_true_needed_le new_needed_le; do
  make_case
  python3 - "$work/$bound_pins" "Tacenta.SessionUnitDecoderBound.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "required-pin-deleted-decoder-bound-$n" "\`Tacenta.SessionUnitDecoderBound.$n\` is on REQUIRED_PINS and has no axiom pin" --check
done

make_case
python3 - "$work/tacenta-proofs/translation/Translation/SessionUnitBraidImportInv.lean" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = "Tacenta.SessionUnitBraidImportInv.Braid.invariant_true_gives_decoders_bounded"
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
expect_fail "required-pin-deleted-import-decoders-bounded" "\`Tacenta.SessionUnitBraidImportInv.Braid.invariant_true_gives_decoders_bounded\` is on REQUIRED_PINS and has no axiom pin" --check

# The inhabitation results: every pin of the UnitSatisfiability modules, each deleted in turn.
# One line per module: file, namespace, then the required names.
while IFS=' ' read -r file ns names; do
  for n in $names; do
    make_case
    python3 - "$work/tacenta-proofs/translation/Translation/$file.lean" "$ns.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
    expect_fail "required-pin-deleted-$file-$n" "\`$ns.$n\` is on REQUIRED_PINS and has no axiom pin" --check
  done
done <<'LIST'
UnitSatisfiabilityBraidAgreements Tacenta.UnitSatisfiabilityBraidAgreements braid_agreement_shapes_are_predicates braid_agreements_have_a_model
UnitSatisfiabilityErasureAgrees Tacenta.UnitSatisfiabilityErasureAgrees erasureCloneAgrees erasureAgrees_iff_clauses erasureAgrees_encoder
UnitSatisfiabilityBraidStates Tacenta.UnitSatisfiabilityBraidStates ingredients twelve_states six_receive_witnesses initiator_refines responder_refines
UnitBraidEntryPoints Tacenta.UnitBraidEntryPoints defined_hypotheses_given_erasure Braid.receive_refines_given_erasure Braid.send_refines_given_erasure defined_hypotheses_of_laws Braid.receive_refines_of_laws Braid.send_refines_of_laws twelve_states_of_laws six_receive_witnesses_of_laws
UnitErasureRsStatements Tacenta.UnitErasureRs K_weights K_coefficients K_evaluate K_algebra E_new E_next D_add D_message M_recover
UnitErasureRsGlue Tacenta.UnitErasureRs.Glue erasureAgrees_decoder erasureAgrees
ErasureT3 Tacenta.ErasureT3 mul_refines
UnitSatisfiabilityRecords Tacenta.UnitSatisfiabilityRecords stdLaws_real_iff ratchetLaws_of_base encrypt_contracts_of_axiom_base decrypt_contracts_of_axiom_base initiator_contracts_of_axiom_base responder_contracts_of_axiom_base records_of_axiom_base axiom_base_satisfiable axiom_base_satisfiable_for_total_rng
UnitSatisfiabilityJoint Tacenta.UnitSatisfiabilityJoint all_shapes_are_predicates model_satisfies_all_axiom_shapes stdLaws_of_faithful model_Faithful model_StdLaws encrypt_iff_parts decrypt_iff_parts initiator_toParts_ofParts responder_toParts_ofParts encrypt_axiom_part_satisfiable decrypt_axiom_part_satisfiable initiator_axiom_part_satisfiable responder_axiom_part_satisfiable DecoderNewTotal_is decoderNewShape_of_stdLaws model_DecoderNew badRange_refutes badDeref_refutes_array badDeref_refutes_message_key badOptionClone_refutes badCap_refutes badSeal_refutes model_pop_empty model_capacity_ge model_truncate_is_take
UnitSatisfiabilityErasure Tacenta.UnitSatisfiabilityErasure decoderAddChunk_total encoderNextChunk_total encoderClone_total decoderClone_total decoderNew_iff encoderNew_iff divCeil32_of_value decoderNew_of_divCeilValue encoderNew_of_divCeilValue
UnitSatisfiabilityRatchet Tacenta.UnitSatisfiabilityRatchet kdfRkTotal kdfCkTotal kdfInitTotal spqrRemoveSkippedAtTotal ratchetRemoveSkippedAtTotal setChainsLoopTotal clearChainsLoop0Total clearSkippedLoopTotal vecRetainTotal defined_fields_hold spqrRemoveSkippedAtTotal_false_of_noop_pop ratchetRemoveSkippedAtTotal_false_of_noop_pop ratchetRemoveSkippedAtTotal_forces_blanketU32 setChainsLoopTotal_forces_asMut
UnitSatisfiabilitySession Tacenta.UnitSatisfiabilitySession vec_pop_satisfiable noop_pop_not_faithful VecPopLaw_is all_thirteen_contracts_satisfiable
UnitSatisfiabilityZeroizeScope Tacenta.UnitSatisfiabilityZeroizeScope zeroize_failure_propagation_conflicts faithful_propagates faithful_refutes_unscoped faithful_satisfies_rest ArrayZeroizeU8Total_of_spqr ArrayZeroizeU8Total_of_braid VecZeroizeChainsTotal_of_vecRetain arrayZeroizeScoped_of_total VecZeroizeSkippedTotal_of_vecRetain
DispatchEvidenceVacuity Tacenta.DispatchEvidenceVacuity same_ephemeral_agreement_empty initialSameEphemeralEvidence_false codewordViewOf_false codewordViewOf_false_of_encoderNewTotal record_empty_of_nonempty_decoder record_empty_headerSent record_empty_ekSentCt1Received record_empty_noHeaderReceived record_empty_ct1Sampled_ek record_empty_ct1Sampled_ekCt1Ack record_empty_ct1Acknowledged keysSampled_receive_ct1_holds_chunk tripleConcreteEvidence_forces_constant_dhPublic aeadConcreteEvidence_forces_constant_dhPublic constant_dhPublic_false_of_publicKeyNotConstant tripleConcreteEvidence_false_of_publicKeyNotConstant aeadConcreteEvidence_false_of_publicKeyNotConstant oracleOf_kem_oracle_never_refuses oracleOf_kem_call_never_errs
BraidPreserve Tacenta.BraidPreserve Braid.step_send_sized Braid.step_receive_sized State.clone_sized Braid.send_sized Braid.receive_sized Braid.commit_sized Braid.initiator_sized Braid.responder_sized Braid.Run.sized Braid.Constructed.sized State.sized_ct1_bounded Braid.Run.exists_initiator Braid.Run.exists_responder Braid.Run.exists_send
SessionUnitBraidPreserve Tacenta.SessionUnitBraidPreserve Braid.step_send_sized Braid.step_receive_sized State.clone_sized Braid.send_sized Braid.receive_sized Braid.commit_sized Braid.initiator_sized Braid.responder_sized Braid.Run.sized Braid.Constructed.sized State.sized_ct1_bounded Braid.Run.exists_initiator Braid.Run.exists_responder Braid.Run.exists_send
BraidPreserveWitness Tacenta.BraidPreserveWitness newMsgLen_iff api_newMsgLen erasure_laws_satisfiable model_for_both_widths
BraidPreserveCorollary Tacenta.BraidPreserveCorollary Braid.Run.receive_no_panic Braid.Run.receive_refines
SessionUnitBraidPreserveDecoder Tacenta.SessionUnitBraidPreserveDecoder message_length_le Good.new Good.msg Good.add Good.clone
SessionUnitBraidPreserveFacts Tacenta.SessionUnitBraidPreserveFacts sized_decoders_bounded invariant_true_gives_sized from_bytes_sized Braid.Run.sized_of_start Braid.Run.inv Braid.Run.receive_no_panic Braid.Run.receive_refines inv_not_sized TruncateLen_is truncateLen_model laws_model
UnitHeadroomSatisfiable Tacenta.UnitHeadroomSatisfiable usize_max_ge plaintext_bound_at_widths freshTriple_headroom freshBraid_bounds decryptHeadroom_sessionOf_iff invariantPreconditions_sessionOf encryptHeadroom_sessionOf_iff initiatorHeadroom_iff responderHeadroom_iff decryptHeadroom_satisfiable encryptHeadroom_satisfiable encryptHeadroom_satisfiable_pending initiatorHeadroom_satisfiable responderHeadroom_satisfiable initiatorHeadroom_not_trivial responderHeadroom_not_trivial decryptHeadroom_not_trivial encryptHeadroom_not_trivial nonempty_privateKey_of_dhCodec nonempty_publicKey_of_dhCodec nonempty_derivedZeroizing encrypt_headroom_of_contracts decrypt_headroom_of_contracts initiator_headroom_of_contracts responder_headroom_of_contracts headroomInhabitants_is model_headroomInhabitants axiom_base_model headroom_of_axiom_base headroom_hypotheses_satisfiable
UnitHeadroomInvariant Tacenta.UnitHeadroomInvariant validKeyShape_is model_validKeyShape optionEqU64Shape_is optionEqImpl_shape structural_sessionOf freshTriple_invariant freshBraid_invariant sessionOf_invariant emptyChainTable_fails_invariant epochZero_braid_fails_invariant emptyChain_headroom epochZero_bounds session_emptyChainTable_fails_invariant session_epochZero_fails_invariant structural_gives_ad invariant_gives_ad_length decryptHeadroom_of_invariant encryptHeadroom_iff_of_invariant invariant_session_meets_both invariant_session_of_axiom_base invariant_hypotheses_satisfiable
NumericBoundary Tacenta.NumericBoundary both_widths classical_store_cap_fits classical_skip_cap_fits spqr_chain_cap_fits spqr_skip_cap_fits ratchet_codec_cap_fits spqr_codec_cap_fits erasure_cap_fits erasure_room_exact_at_32 clock_ceiling_excludes_only_parked epoch_ceiling_excludes_only_top
NumericBoundaryLeaf Tacenta.NumericBoundaryLeaf ratchet_constants spqr_constants erasure_constants protobuf_constants code_matches_model max_events_is_parked clock_ceiling_summary
NumericBoundaryTriple Tacenta.NumericBoundaryTriple unit_ratchet_constants unit_spqr_constants unit_code_matches_model
NumericBoundarySession Tacenta.NumericBoundarySession session_unit_ratchet_constants session_unit_spqr_constants session_unit_erasure_constants session_unit_code_matches_model
NumericShapeWitness Tacenta.NumericShapeWitness usize_max_cases every_shape_is_satisfiable
NumericWitnessLeaf Tacenta.NumericWitnessLeaf sat_T1_receive_no_panic sat_T3_receive_refines sat_ImportInv_Ratchet_decoded_receive_refines sat_SpqrT1_receive_no_panic sat_SpqrT1_send_no_panic sat_SpqrT3_receive_refines sat_SpqrT3_send_refines sat_BraidT1_Braid_receive_no_panic sat_BraidT1_Braid_step_receive_no_panic sat_BraidT3_Braid_receive_refines sat_BraidT3_step_receive_refines sat_BraidT3_Braid_send_refines sat_BraidT3_step_send_refines spqrS_inv ratS_inv spqr_receive_premises_at_witness spqr_send_premises_at_witness spqr_advance_premises_at_witness spqr_maybe_advance_premises_at_witness spqr_clear_old_epochs_premises_at_witness ratchet_receive_premises_at_witness braid_receive_premises_at_witness braid_step_receive_premises_at_witness
NumericWitnessTriple Tacenta.NumericWitnessTriple sat_UnitT1_receive_no_panic sat_UnitT3_receive_refines sat_UnitSpqrT1_receive_no_panic sat_UnitSpqrT1_send_no_panic sat_UnitSpqrT3_receive_refines sat_UnitSpqrT3_send_refines sat_UnitTripleT1_State_receive_no_panic sat_UnitTripleT1_State_send_no_panic sat_UnitTripleT3_receive_refines sat_UnitTripleT3_receive_refines_discharged sat_UnitTripleT3_send_refines sat_UnitTripleT3_send_refines_discharged
NumericWitnessSession Tacenta.NumericWitnessSession sat_SessionUnitT1_receive_no_panic sat_SessionUnitT3_receive_refines sat_SessionUnitRatchetImportInv_Ratchet_decoded_receive_refines sat_SessionUnitSpqrT1_receive_no_panic sat_SessionUnitSpqrT1_send_no_panic sat_SessionUnitSpqrT3_receive_refines sat_SessionUnitSpqrT3_send_refines sat_SessionUnitTripleT1_State_receive_no_panic sat_SessionUnitTripleT1_State_send_no_panic sat_SessionUnitTripleT3_receive_refines sat_SessionUnitTripleT3_receive_refines_discharged sat_SessionUnitTripleT3_send_refines sat_SessionUnitTripleT3_send_refines_discharged sat_SessionUnitBraidT1_Braid_receive_no_panic sat_SessionUnitBraidT1_Braid_step_receive_no_panic sat_SessionUnitBraidT3_Braid_receive_refines sat_SessionUnitBraidT3_step_receive_refines sat_SessionUnitBraidT3_Braid_send_refines sat_SessionUnitBraidT3_step_send_refines session_unit_spqrS_inv session_unit_ratS_inv session_unit_spqr_receive_premises_at_witness session_unit_spqr_send_premises_at_witness session_unit_spqr_advance_premises_at_witness session_unit_spqr_maybe_advance_premises_at_witness session_unit_spqr_clear_old_epochs_premises_at_witness session_unit_ratchet_receive_premises_at_witness session_unit_braid_receive_premises_at_witness session_unit_braid_step_receive_premises_at_witness triple_receive_premises_at_witness triple_send_premises_at_witness
DecodedStateDischarge Tacenta.DecodedStateDischarge spqr_epoch_family spqr_receive_premises spqr_send_premises spqr_advance_premises spqr_maybe_advance_premises spqr_clear_old_epochs_premises ratchet_receive_premises braid_receive_premises braid_step_receive_premises
SessionUnitDecodedStateDischarge Tacenta.SessionUnitDecodedStateDischarge session_unit_spqr_epoch_family session_unit_spqr_receive_premises session_unit_spqr_send_premises session_unit_spqr_advance_premises session_unit_spqr_maybe_advance_premises session_unit_spqr_clear_old_epochs_premises session_unit_ratchet_receive_premises session_unit_braid_receive_premises session_unit_braid_step_receive_premises triple_receive_premises triple_send_premises decrypt_headroom_of_invariant decrypt_ratchet_no_panic_of_invariant decrypt_no_panic_of_invariant
SatisfiabilitySpqrLaws Tacenta.SatisfiabilitySpqrLaws kdfRkTotal kdfCkTotal spqrRemoveSkippedAtTotal setChainsLoopTotal clearChainsLoop0Total clearSkippedLoopTotal vecRetainTotal defined_fields_hold removeSkippedAtAgrees setChainsAgrees clearOldEpochsAgrees vecRetainAgreesOfLaws vecRetainAgrees LawPop_is LawAsMut_is LawCapacity_is LawVecZeroize_is LawHkdf_is SpqrCodec_ZeroizingVecTotal_is zeroizing_vec_satisfiable laws_jointly_satisfiable defined_hyps_from_axiom_hyps spqr_zeroizeTotal_conflicts laws_of_shape hkdf_total_satisfiable pop_satisfiable capacity_satisfiable vec_zeroize_satisfiable vec_zeroize_conflicts
SatisfiabilityRatchetLaws Tacenta.SatisfiabilityRatchetLaws ratchetRemoveSkippedAtTotal LawPop_is LawBlanketU32_is ArrZU8_is RatchetCodec_ZeroizingVecTotal_is zeroizing_vec_satisfiable pop_satisfiable blanket_satisfiable arrZU8_satisfiable ratchet_laws_jointly_satisfiable
SatisfiabilityBraidZeroize Tacenta.SatisfiabilityBraidZeroize braid_arrayZeroizeTotal_conflicts
UnitSatisfiabilityTripleLaws Tacenta.UnitSatisfiabilityTripleLaws kdfRkTotal kdfCkTotal kdfInitTotal spqrRemoveSkippedAtTotal ratchetRemoveSkippedAtTotal setChainsLoopTotal clearChainsLoop0Total clearSkippedLoopTotal vecRetainTotal defined_fields_hold removeSkippedAtAgrees setChainsAgrees clearOldEpochsAgrees vecRetainAgreesOfLaws vecRetainAgrees LawPop_is LawAsMut_is LawCapacity_is LawVecZeroize_is LawBlanketU32_is LawHkdf_is laws_jointly_satisfiable laws_of_shape defined_hyps_from_axiom_hyps RoundTrips80_is roundTrips80_satisfiable TripleZeroizeTotal_is arrZ32_satisfiable arrZ32_of_general spqrZeroizeTotal_conflicts hkdf_total_satisfiable pop_satisfiable capacity_satisfiable vec_zeroize_satisfiable blanket_satisfiable vec_zeroize_conflicts
SpqrFromBytesWitness Tacenta.SpqrFromBytesWitness spqr_from_bytes_accepts_witness spqr_from_bytes_establishes_inv_nonvacuous
BraidFromBytesWitness Tacenta.BraidFromBytesWitness braid_from_bytes_accepts_witness braid_from_bytes_establishes_inv_nonvacuous
SessionUnitBraidFromBytesWitness Tacenta.SessionUnitBraidFromBytesWitness braid_from_bytes_accepts_witness braid_from_bytes_establishes_inv_nonvacuous
RatchetDecodedWitness Tacenta.RatchetDecodedWitness ratchet_witness_events decoded_receive_refines_premises_satisfiable
UnitLifecycleAtomicity Tacenta.UnitLifecycleAtomicity decrypt_ratchet_err_leaves_state decrypt_ratchet_ok_writes decrypt_err_leaves_state decrypt_ok_writes establish_responder_err_leaves_store encrypt_err_leaves_state encrypt_ok_writes
UnitLifecycleRepair Tacenta.UnitLifecycleRepair codewordViewSendOf_satisfiable scoped_chunk_fields_iff_consistent
UnitPins Tacenta.UnitT3 receive_store_full_refines
UnitPins Tacenta.UnitSpqrT3 receive_store_full_refines
UnitPins Tacenta.UnitTripleT3 receive_store_full_refines_discharged
AxiomAuditSessionUnit Tacenta.UnitLifecycleT3 concrete_receive_attempt_store_full_from_contracts concrete_receive_attempt_store_full_from_retry_bounds fullStoreOfReal_ne_of_generated_ne
UnitLifecycleIntegrationScreen Tacenta.UnitLifecycleIntegrationScreen concreteBranchEvidence_empty endToEndEvidence_empty agreementEndToEndEvidence_empty byte_random32 random32Clause_of_oracleOf sigSignClause_of_oracleOf kemClauses_of_oracleOf sigSignClause_of_law kemClauses_of_law changed_rng_clauses_have_a_model changed_rng_clauses_of_laws braid_send_keysUnsampled_generate braidSendTrace_conflicts_with_sigSign retryReceiveBounds_initAlice retryReceiveBounds_not_trivial generatedTripleRefusalConditions_initAlice generatedTripleSuccessConditions_initAlice oracleOf_dhAgree_off_view sameEphemeralAgreement_unconstrained concreteBranchEvidenceRun_of_run_parts runRandomDraw_byte braid_send_keysUnsampled_byte_trace braidSendTraceCounted_with_sigSign_byte
UnitLifecycleRetryLoopT3 Tacenta.UnitLifecycleRetryLoopT3 receive_with_eviction_loop_refines receive_with_eviction_refines receiveWithEvictionLoopResult_stop shortfall_covers evict_for_retry_covers
UnitLifecycleDecryptRatchetT3 Tacenta.UnitLifecycleDecryptRatchetT3 DecryptOracleOf.of_oracleOf cMax_usize decrypt_ratchet_refines decrypt_ratchet_refines_statement RetryRunBounds.toRetryReceiveBounds DecryptPrefix.triple_refusal DecryptPrefix.aead_refusal DecryptPrefix.success tripleRefusalOpen_exactly tripleRefusalOpen_false_unless_triple
UnitLifecycleDecryptRatchetScreen Tacenta.UnitLifecycleDecryptRatchetScreen sample_run_satisfiable decrypt_boundary_has_a_model decrypt_shapes_are_predicates run_draw_not_trivial retryRunBounds_not_trivial tripleRefusalOpen_false_of_ok tripleRefusalOpen_false_of_store_full decrypt_ratchet_refines_at_sample sample_model_refuses succ_model_accepts succ_run_satisfiable hypotheses_meet_refusal_and_success
LIST

# The sparse total bound's pins (Proofs/SparseReplacementBound.lean), each deleted in turn. They
# are in the proofs package, not the translation package, so they have their own block.
for n in mem_skipSurvivors_iff skipSurvivors_length_le skipMessageKeys_refused_iff \
         skipMessageKeys_leaves_survivors_then_batch skipMessageKeys_keeps_outside_range \
         skipMessageKeys_keeps_the_key_at_the_counter skipMessageKeys_replaces_the_range \
         replacement_accepts_where_the_count_before_the_deletion_refuses \
         witness_premises_hold witness_refused_one_key_further; do
  make_case
  python3 - "$work/tacenta-proofs/Proofs/SparseReplacementBound.lean" "Proofs.SparseReplacementBound.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "required-pin-deleted-SparseReplacementBound-$n" "\`Proofs.SparseReplacementBound.$n\` is on REQUIRED_PINS and has no axiom pin" --check
done

make_case
python3 - "$work/$session_pins" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = "Tacenta.UnitLifecycleT1.encrypt_no_panic"
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn(lambda m: "/-\n" + m.group(0) + "-/\n", text)
assert n == 1, n
path.write_text(new)
PY
expect_fail "required-pin-commented-out" "sit inside a comment or a string" --check

make_case
python3 - "$work/$session_pins" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
anchor = "info: 'Tacenta.UnitLifecycleT1.decrypt_no_panic' depends on axioms: [propext,"
assert text.count(anchor) == 1
path.write_text(text.replace(anchor, anchor + "\n Tacenta.UnitLifecycleT1.full_store_eq_no_panic._native.native_decide.ax_1_2,"))
PY
expect_fail "compiler-trust-pin-not-listed" "\`Tacenta.UnitLifecycleT1.decrypt_no_panic\` is pinned as compiler-trusted and is not on COMPILER_TRUSTED_PINS" --check
expect_fail "compiler-trust-pin-refused-by-refresh" "\`Tacenta.UnitLifecycleT1.decrypt_no_panic\` is pinned as compiler-trusted and is not on COMPILER_TRUSTED_PINS"

# The field's pins are kernel-only and are on no ceiling: a compiler-trust axiom put back under
# `interp_eq` (the case the stale ceiling entry used to accept) is refused, and so is deleting any
# of the three pins in `Proofs/TrustedBase.lean`; the fourth, `ErasureT3.mul_refines`, is in the LIST below.
make_case
python3 - "$work/tacenta-proofs/Proofs/TrustedBase.lean" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
old = "info: 'Model.Polynomial.interp_eq' depends on axioms: [propext, Classical.choice, Quot.sound]"
assert text.count(old) == 1
path.write_text(text.replace(old, "info: 'Model.Polynomial.interp_eq' depends on axioms: [propext,\n Classical.choice,\n Quot.sound,\n Model.Gf65536.mul_one._native.bv_decide.ax_1_9]"))
PY
expect_fail "field-pin-compiler-trust-returns" "\`Model.Polynomial.interp_eq\` is pinned as compiler-trusted and is not on COMPILER_TRUSTED_PINS" --check
expect_fail "field-pin-compiler-trust-refused-by-refresh" "\`Model.Polynomial.interp_eq\` is pinned as compiler-trusted and is not on COMPILER_TRUSTED_PINS"

for n in Model.Gf65536.mul_assoc Model.Gf65536.mul_inv_cancel Model.Polynomial.interp_eq; do
  make_case
  python3 - "$work/tacenta-proofs/Proofs/TrustedBase.lean" "$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "required-pin-deleted-trustedbase-$n" "\`$n\` is on REQUIRED_PINS and has no axiom pin" --check
done

make_case
python3 - "$work/$session_pins" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
def block(name):
    return re.compile(
        r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
        re.S,
    )
first = "Tacenta.UnitLifecycleT1.encrypt_no_panic"
second = "Tacenta.UnitLifecycleT1.decrypt_no_panic"
copy = block(second).search(text).group(0)
new, n = block(first).subn(lambda _m: copy, text)
assert n == 1, n
path.write_text(new)
PY
expect_fail "pin-block-copied-over-another" "theorems pinned more than once: Tacenta.UnitLifecycleT1.decrypt_no_panic" --check

# ---------------------------------------------------------------------------
# Statement pins. `#guard_msgs in #check @name` holds a theorem's statement, and
# only the Lean build compared it: a deleted pin is a smaller file that builds, and
# the pins are not axiom pins, so REQUIRED_PINS does not see them. The floor
# REQUIRED_STATEMENT_PINS does. One floor name stands for the class: each mutation
# is made to the statement pin of `record_empty_headerSent`, and every one must be
# refused by the floor's own message naming that declaration. Deleting each pin of
# the floor in turn would test the same loop once per name. The accepted spellings are
# cases too, because a refusal is only evidence if the pin can be accepted.
# ---------------------------------------------------------------------------

stmt_name="Tacenta.DispatchEvidenceVacuity.record_empty_headerSent"
stmt_file="tacenta-proofs/translation/Translation/DispatchEvidenceVacuity.lean"
stmt_head="\`$stmt_name\` is on REQUIRED_STATEMENT_PINS and"

# Rewrite the statement pin of $stmt_name in $stmt_file. `mode` picks the mutation;
# `option` is the text between the parentheses of `#guard_msgs` for mode `options`.
rewrite_statement_pin() {
  python3 - "$work/$stmt_file" "$stmt_name" "$1" "${2:-}" <<'PY'
import pathlib, re, sys
path, name, mode, option = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3], sys.argv[4]
text = path.read_text()
pin = re.compile(r"#guard_msgs in\n#check @?" + re.escape(name) + r"\n")
hits = pin.findall(text)
assert len(hits) == 1, hits
block = hits[0]
new = {
    "delete": "",
    "line-comment": "".join("-- " + line + "\n" for line in block.splitlines()),
    "block-comment": "/-\n" + block + "-/\n",
    # The inner `-/` closes only the inner comment, so the pin is still commented out.
    "nested-comment": "/- outer\n/- inner -/\n" + block + "-/\n",
    "docstring": "/-- the pin of the next theorem:\n" + block + "-/\ndef statement_pin_doc : Nat := 0\n",
    "string": 'def statement_pin_text : String := "\n' + block + '"\n',
    "no-guard": "#check @" + name + "\n",
    "options": "#guard_msgs (" + option + ") in\n#check @" + name + "\n",
    "rename": "#guard_msgs in\n#check @" + name + "_renamed\n",
    "namespace": "namespace StatementPinScope\n" + block + "end StatementPinScope\n",
    # A `mutual` block closes with `end`, which must not pop the namespace around the pin.
    "mutual": ("namespace StatementPinScope\nmutual\ndef statementPinA : Nat -> Nat\n  | 0 => 0\n"
               "  | n + 1 => statementPinB n\ndef statementPinB : Nat -> Nat\n  | 0 => 0\n"
               "  | n + 1 => statementPinA n\nend\n" + block + "end StatementPinScope\n"),
    # The pin as the argument of an earlier `... in`: the outer command can swallow the
    # pin's own mismatch (`drop`) or change what it prints (`set_option`, `open`).
    "wrapped-drop-error": "#guard_msgs (drop error) in\n" + block,
    "wrapped-drop-all": "#guard_msgs (drop all) in\n" + block,
    "wrapped-set-option": "set_option pp.deepTerms false in\n" + block,
    "wrapped-open": "open Nat in\n" + block,
    "term": "#guard_msgs in\n#check @" + name + " x\n",
    "at-sign": "#guard_msgs in\n#check @" + name + "\n",
}[mode]
path.write_text(text.replace(block, new))
PY
}

make_case
expect_pass "statement-pins-unmodified-tree" --check

make_case
rewrite_statement_pin delete
expect_fail "statement-pin-deleted" "$stmt_head has no statement pin: no active \`#guard_msgs in\` followed by \`#check @$stmt_name\`" --check
expect_fail "statement-pin-deleted-refused-by-refresh" "$stmt_head has no statement pin"

for mode in line-comment block-comment nested-comment docstring string; do
  make_case
  rewrite_statement_pin "$mode"
  expect_fail "statement-pin-$mode" "$stmt_head its statement pin at $stmt_file:" --check
  expect_fail "statement-pin-$mode-says-why" "sits inside a comment, a docstring or a string, where Lean does not check it" --check
done

make_case
rewrite_statement_pin no-guard
expect_fail "statement-pin-without-guard-msgs" "is not under \`#guard_msgs in\`, so the build compares nothing" --check

make_case
rewrite_statement_pin rename
expect_fail "statement-pin-renamed-declaration" "$stmt_head has no statement pin" --check

make_case
rewrite_statement_pin term
expect_fail "statement-pin-of-an-application-not-a-name" "$stmt_head has no statement pin" --check

make_case
rewrite_statement_pin namespace
expect_fail "statement-pin-inside-namespace" "its statement pin at $stmt_file:" --check
expect_fail "statement-pin-inside-namespace-says-why" "sits inside \`StatementPinScope\`; write it after \`end\` with the full name" --check

# The mutual block that follows a namespace is the same refusal as the namespace alone.
make_case
rewrite_statement_pin mutual
expect_fail "statement-pin-after-mutual-inside-namespace" "its statement pin at $stmt_file:" --check
expect_fail "statement-pin-after-mutual-inside-namespace-says-why" "sits inside \`StatementPinScope\`; write it after \`end\` with the full name" --check

# A pin that is the argument of an earlier `... in` is not the outermost command.
for mode in wrapped-drop-error wrapped-drop-all wrapped-set-option wrapped-open; do
  make_case
  rewrite_statement_pin "$mode"
  expect_fail "statement-pin-$mode" "its \`#guard_msgs\` at $stmt_file:" --check
  expect_fail "statement-pin-$mode-says-why" "is the argument of an earlier \`... in\`, which can swallow its mismatch or change what it prints; write the pin as its own command" --check
done

# Options that leave the `#check` message uncompared. `#guard_msgs` takes the first
# option that covers a kind of message, and a message no option covers passes through.
# Each is refused for its own reason, so a wrong reason string goes red.
covers="is the first option that covers \`info\` and it does not compare it, so the pin holds nothing"
uncovered="no option covers \`info\`, so the message \`#check\` prints passes through without being compared"
for entry in "drop all|$covers" "drop info|$covers" "pass info|$covers" "pass all|$covers" \
             "drop warning|$uncovered" "drop warning, drop error|$uncovered" "drop all, check info|$covers" \
             "whitespace := lax|compares the message with its whitespace removed" \
             "error := true|the option \`error := true\` is not one this gate reads, so it cannot say what is compared"; do
  option="${entry%%|*}"
  reason="${entry#*|}"
  make_case
  rewrite_statement_pin options "$option"
  expect_fail "statement-pin-option-$option" "its \`#guard_msgs ($option)\` at $stmt_file:" --check
  expect_fail "statement-pin-option-$option-says-why" "$reason" --check
done

# A definition pin (`#print`) with its `#guard_msgs` removed is refused for that, not as an
# absent pin.
print_name="Tacenta.BraidPreserve.Braid.sized"
print_file="tacenta-proofs/translation/Translation/BraidPreserve.lean"
make_case
replace_in "$print_file" $'#guard_msgs in\n#print '"$print_name"$'\n' $'#print '"$print_name"$'\n'
expect_fail "definition-pin-without-guard-msgs" "\`$print_name\` is on REQUIRED_STATEMENT_PINS and \`#print $print_name\` at $print_file:" --check
expect_fail "definition-pin-without-guard-msgs-says-why" "is not under \`#guard_msgs in\`, so the build compares nothing" --check

# The model's draw functions and the record bodies of the integration screen: each definition pin
# (and the one equation pin) deleted in turn is refused as a missing statement pin.
for name in Model.Lifecycle.braidSendDrawCount Model.Lifecycle.sendAgreement \
  Model.Lifecycle.braidSendNeedsDraw Model.Lifecycle.takeDraws Model.Lifecycle.takeDraws.eq_def \
  Model.Lifecycle.takeDraw Model.Lifecycle.braidRandomness Tacenta.UnitLifecycleT3.OracleOf \
  Tacenta.UnitLifecycleT3.BraidSendTraceAgreementCounted \
  Tacenta.UnitLifecycleT3.InitialRatchetTripleBranchContracts \
  Tacenta.UnitLifecycleT3.InitialRatchetAeadBranchContracts \
  Tacenta.UnitLifecycleT3.InitialRatchetBraidEvidenceContractsScoped \
  Tacenta.UnitLifecycleT3.verified; do
  make_case
  python3 - "$work/tacenta-proofs/translation/Translation/UnitLifecycleIntegrationScreen.lean" "$name" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: (?:(?!-/).)*?-/\s*\n#guard_msgs in\s*\n#(?:print |check @)" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "statement-pin-deleted-$name" "\`$name\` is on REQUIRED_STATEMENT_PINS and has no statement pin" --check
done

# Package F (`UnitLifecycleRetryLoopT3.lean`, `UnitLifecycleDecryptRatchetT3.lean`,
# `UnitLifecycleDecryptRatchetScreen.lean`): each statement pin and each definition pin, deleted in
# turn, is refused as a missing statement pin. One line per module: file, namespace, then the names.
while IFS=' ' read -r file ns names; do
  for n in $names; do
    make_case
    python3 - "$work/tacenta-proofs/translation/Translation/$file.lean" "$ns.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: (?:(?!-/).)*?-/\s*\n#guard_msgs in\s*\n#(?:print |check @)" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
    expect_fail "statement-pin-deleted-$file-$n" "\`$ns.$n\` is on REQUIRED_STATEMENT_PINS and has no statement pin" --check
  done
done <<'LIST'
UnitLifecycleRetryLoopT3 Tacenta.UnitLifecycleRetryLoopT3 receive_with_eviction_loop_refines receive_with_eviction_refines receiveWithEvictionLoopResult_stop shortfall_covers evict_for_retry_covers LoopRel OutcomeRefines OpenRefusal BatchCovers halfLength evictHalf
UnitLifecycleDecryptRatchetT3 Tacenta.UnitLifecycleDecryptRatchetT3 DecryptOracleOf.of_oracleOf decrypt_ratchet_refines decrypt_ratchet_refines_statement RetryRunBounds.toRetryReceiveBounds DecryptPrefix.triple_refusal DecryptPrefix.aead_refusal DecryptPrefix.success tripleRefusalOpen_exactly tripleRefusalOpen_false_unless_triple DecryptOracleOf RetryRunBounds DecryptRatchetAgreements DecryptRatchetRun TripleRefusalOpen DecryptRatchetRefinesStatement DecryptPrefix
UnitLifecycleDecryptRatchetScreen Tacenta.UnitLifecycleDecryptRatchetScreen sample_run_satisfiable decrypt_boundary_has_a_model decrypt_shapes_are_predicates run_draw_not_trivial retryRunBounds_not_trivial tripleRefusalOpen_false_of_ok tripleRefusalOpen_false_of_store_full decrypt_ratchet_refines_at_sample sample_model_refuses succ_model_accepts succ_run_satisfiable hypotheses_meet_refusal_and_success sampleComposite sampleReal modelOf sampleRng DhCodecOfShape DecryptOracleShape ZeroizeRoundTripShapes succTriple succReal succComposite succBytes oracleDecrypt
LIST

# Package F's open disjunct is on REQUIRED_PRINT_FORM: its pin rewritten as `#check @` is refused.
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleDecryptRatchetT3.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleDecryptRatchetT3.TripleRefusalOpen\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleDecryptRatchetT3.TripleRefusalOpen\n'
expect_fail "definition-pin-check-form-TripleRefusalOpen" "is \`#check @Tacenta.UnitLifecycleDecryptRatchetT3.TripleRefusalOpen\`, which prints the type and not the body" --check

# A definition on REQUIRED_PRINT_FORM is held by `#print`: its pin rewritten as `#check @`, which
# prints the type and not the body, is refused, for a model definition and for a record. A floor
# name not on that list (`takeDraws`, whose body is held by its equation pin) may take either form.
screen="tacenta-proofs/translation/Translation/UnitLifecycleIntegrationScreen.lean"
for name in Model.Lifecycle.braidSendDrawCount Tacenta.UnitLifecycleT3.OracleOf; do
  make_case
  replace_in "$screen" $'#guard_msgs in\n#print '"$name"$'\n' $'#guard_msgs in\n#check @'"$name"$'\n'
  expect_fail "definition-pin-check-form-$name" "\`$name\` is on REQUIRED_STATEMENT_PINS and its pin at $screen:" --check
  expect_fail "definition-pin-check-form-$name-says-why" "is \`#check @$name\`, which prints the type and not the body" --check
  expect_fail "definition-pin-check-form-$name-refused-by-refresh" "is \`#check @$name\`, which prints the type and not the body"
done
make_case
replace_in "$screen" $'#guard_msgs in\n#print Model.Lifecycle.takeDraws\n' $'#guard_msgs in\n#check @Model.Lifecycle.takeDraws\n'
expect_pass "statement-pin-check-form-off-the-print-list"
expect_pass "statement-pin-check-form-off-the-print-list-then-checked" --check

# The spellings the floor accepts: the pin is the pin, not its exact form. The Lean file
# changed, so the source attestation is stale until it is regenerated; regenerating
# refuses on the same statement-pin problems `--check` does, so an accepted case is a
# regeneration that succeeds and a `--check` after it.
for option in "check info, drop warning" "whitespace := normalized" "ordering := sorted" "info"; do
  make_case
  rewrite_statement_pin options "$option"
  expect_pass "statement-pin-accepted-option-$option"
  expect_pass "statement-pin-accepted-option-$option-then-checked" --check
done

make_case
rewrite_statement_pin at-sign
expect_pass "statement-pin-accepted-with-at-sign"
expect_pass "statement-pin-accepted-with-at-sign-then-checked" --check

# A pin in a module that no audit module imports: the pin moves to a new file under the
# translation package, which nothing imports.
make_case
rewrite_statement_pin delete
cat > "$work/tacenta-proofs/translation/Translation/OrphanStatementPin.lean" <<EOF
import Translation.DispatchEvidenceVacuity

#guard_msgs in
#check @$stmt_name
EOF
expect_fail "statement-pin-in-a-module-no-audit-imports" "its statement pin is in tacenta-proofs/translation/Translation/OrphanStatementPin.lean, which no audit module imports" --check

# The floor cannot be shortened by deleting a pin and its name and regenerating: the
# verification manifest records the floor, and a floor shorter than the record is refused.
shorten_floor() {
  python3 - "$work/tacenta-proofs/scripts/attest.py" "$stmt_name" <<'PY'
import pathlib, sys
path, name = pathlib.Path(sys.argv[1]), sys.argv[2]
text = path.read_text()
start = text.index("REQUIRED_STATEMENT_PINS = frozenset(")
last = name.rsplit(".", 1)[1]
line = '        "' + last + '",\n'
at = text.index(line, start)
path.write_text(text[:at] + text[at + len(line):])
PY
}

make_case
shorten_floor
rewrite_statement_pin delete
expect_fail "statement-floor-shortened" "\`$stmt_name\` is on the statement-pin floor that verification-manifest.json records and is not on REQUIRED_STATEMENT_PINS" --check
expect_fail "statement-floor-shortened-refused-by-refresh" "is on the statement-pin floor that verification-manifest.json records and is not on REQUIRED_STATEMENT_PINS"

# The limit of the record: a floor entry is removed by editing the script, the pin and the
# manifest's own list together, a hand edit of a generated file that the diff shows. The
# case is here so that the limit is on record and not found by deleting.
make_case
shorten_floor
rewrite_statement_pin delete
edit_json tacenta-proofs/manifests/verification-manifest.json \
  "data['statement_pin_floor'].remove('$stmt_name')"
expect_pass "statement-floor-shortened-by-hand-edit-and-regenerated"
expect_pass "statement-floor-shortened-by-hand-edit-then-checked" --check

# The record does not fail open: with the script's floor shortened and its pin deleted, a
# manifest that is missing, unreadable, without a floor list or with an empty one leaves
# nothing to compare with, and is refused, by `--check` and by a regeneration alike.
floor_record="tacenta-proofs/manifests/verification-manifest.json"
shortened_floor_without_pin() {
  make_case
  shorten_floor
  rewrite_statement_pin delete
}
no_floor="so the statement-pin floor it records cannot be compared with REQUIRED_STATEMENT_PINS"

shortened_floor_without_pin
rm "$work/$floor_record"
expect_fail "statement-floor-record-missing" "$floor_record is missing, $no_floor" --check
expect_fail "statement-floor-record-missing-refused-by-refresh" "$floor_record is missing, $no_floor"

shortened_floor_without_pin
echo '{' > "$work/$floor_record"
expect_fail "statement-floor-record-unreadable" "$floor_record cannot be read (JSONDecodeError), $no_floor" --check
expect_fail "statement-floor-record-unreadable-refused-by-refresh" "cannot be read (JSONDecodeError), $no_floor"

shortened_floor_without_pin
edit_json "$floor_record" "del data['statement_pin_floor']"
expect_fail "statement-floor-record-keyless" "$floor_record has no \`statement_pin_floor\` list, $no_floor" --check
expect_fail "statement-floor-record-keyless-refused-by-refresh" "has no \`statement_pin_floor\` list, $no_floor"

shortened_floor_without_pin
edit_json "$floor_record" "data['statement_pin_floor'] = None"
expect_fail "statement-floor-record-null" "$floor_record has no \`statement_pin_floor\` list, $no_floor" --check

shortened_floor_without_pin
edit_json "$floor_record" "data['statement_pin_floor'] = []"
expect_fail "statement-floor-record-emptied" "$floor_record records an empty \`statement_pin_floor\`" --check
expect_fail "statement-floor-record-emptied-refused-by-refresh" "records an empty \`statement_pin_floor\`"

# The whole floor emptied in the script, and its record deleted with it, is not "0 on the floor".
make_case
replace_in tacenta-proofs/scripts/attest.py "def check_statement_pins(survey=None, reached=None):" \
  "REQUIRED_STATEMENT_PINS = frozenset()


def check_statement_pins(survey=None, reached=None):"
edit_json "$floor_record" "del data['statement_pin_floor']"
expect_fail "statement-floor-emptied" "REQUIRED_STATEMENT_PINS is empty, so no statement pin is required to exist" --check
expect_fail "statement-floor-emptied-refused-by-refresh" "REQUIRED_STATEMENT_PINS is empty"

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

make_case
printf '\n// zone edit\n' >> "$work/tacenta-core/ratchet/src/lib.rs"
expect_fail "zone-source-edited" "translation is stale for tacenta-core/ratchet" --check-translation

make_case
printf '\n# workspace edit\n' >> "$work/tacenta-core/Cargo.toml"
expect_fail "workspace-input-edited" "the workspace inputs" --check-translation

make_case
printf 'namespace tacenta_nothing\nend tacenta_nothing\n' > "$work/$gen/TacentaNothing.lean"
expect_fail "generated-name-without-a-module" "is named like a generated file but scripts/run-aeneas.sh" --check-translation
expect_fail "generated-name-refused-by-refresh" "refusing to record a file the translation script does not produce" --refresh-translation

make_case
edit_json "$record" 'del data["generated_files"]["'"$gen"'/TacentaWire.lean"]'
expect_fail "record-lacks-a-file" "is a generated file with no record in translation-attestation.json" --check-translation

make_case
edit_json "$record" 'data["generated_files"]["'"$gen"'/TacentaNothing.lean"] = data["generated_files"]["'"$gen"'/TacentaWire.lean"]'
expect_fail "record-has-a-file-not-in-the-tree" "is recorded in translation-attestation.json but is not in the tree" --check-translation

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

make_case
replace_in "$gen/TacentaErasure.lean" \
  "axiom core.num.Usize.div_ceil : Std.Usize → Std.Usize → Result Std.Usize" \
  "-- removed"
set +e
out="$(attest --write-axiom-allowlist)"
rc=$?
set -e
cases=$((cases + 1))
if [ "$rc" -ne 0 ] || [[ "$out" != *"allowlist - TacentaErasure.lean: tacenta_erasure.core.num.Usize.div_ceil : Std.Usize"* ]]; then
  echo "WRONG  writer-reports-what-it-removed: rc=$rc, the removal was not printed:" >&2
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
