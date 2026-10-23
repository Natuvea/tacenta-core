#!/usr/bin/env bash
# Fail if any first-party proof is incomplete.
#
# This asks the compiler rather than grepping the source. Lean emits
# "declaration uses `sorry`" for every incomplete declaration it elaborates, so
# a build log is an exhaustive and authoritative list, where a grep is neither:
# it sees only the files it is pointed at, and matches the word wherever it
# appears, including in prose explaining that there is no sorry.
#
# Third-party sorries are not ours and are not failed on: Aeneas's own library
# ships four. They cannot be filtered by looking for `.lake` in the path,
# because a dependency reports its files relative to its own package root
# (`Aeneas/Std/Slice.lean`, with nothing to distinguish it). So the filter is
# positive, naming the directories that are ours, and anything it does not
# recognise is treated as third-party rather than as first-party.
# The elaborated-environment audit in each build separately refuses any
# first-party declaration that reaches `sorryAx`, covering disabled or consumed
# warnings even when Lean emits no diagnostic for the log scan below.
#
# Phases, parts and the combiner. The run is a list of phases, each a call of `run_phase` in
# `phases` below with an id, a kind and the label its time is reported under. With no variable set
# the script runs every phase in that order, as it always has, and ends with the line
# "no-sorry: all N phases passed" when none failed. CI splits the run over machines instead:
#
#   NO_SORRY_LIST=1             print the phases (and the controls of a sliceable phase) and run nothing
#   NO_SORRY_PART=<part>        run one part of `scripts/no-sorry-parts.txt`: the prelude phases (the three
#   NO_SORRY_PART_DIR=<dir>     package builds and their scans, which every other phase reads) and the
#                               part's own phases, in this order, and write to <dir> its log and a
#                               manifest (`part.json`). A part gives no verdict and prints no final line.
#   NO_SORRY_COMBINE=<dir>      require that <dir> holds exactly the parts of <partition>, each of this
#   NO_SORRY_PARTITION=<name>   commit, tree and script, every one of whose phases passed, which together
#                               run every phase once (a sliced phase: every control once), and only then
#                               print the final line of a full run.
#
# `scripts/no-sorry-parts.py` reads the parts file against the phases this script lists, so a phase
# added here and given to no part fails every part and the combiner; its header says what the combiner
# requires. The variables a phase's script reads to run less than all of it, or to run something else
# in its place, are refused here in every mode: a run with one of them set is not this gate.
set -euo pipefail

cd "$(dirname "$0")/.."

fail=0

# The test seams of the phases' scripts: `check-refuted-records.sh` runs `REFUTED_RECORDS_BIN` in place of
# the built walker, `check-braid-agreement-negatives.sh` runs only the cases `BRAIDNEG_FILTER` names, and
# `check-hypothesis-witnesses.sh` reads the tree `HYPWIT_ROOT` names. Each is for that script's own
# controls; set here, it would make this run hold less than it says.
seam_variables="REFUTED_RECORDS_BIN BRAIDNEG_FILTER HYPWIT_ROOT"
for seam in $seam_variables; do
  if printenv "$seam" >/dev/null 2>&1; then
    echo "::error::no-sorry: $seam is set; it is a test seam of one phase's script, and a run with it set is not the gate" >&2
    exit 2
  fi
done

usage_error() {
  echo "::error::no-sorry: $1" >&2
  exit 2
}

mode=full
modes=0
if [ -n "${NO_SORRY_LIST:-}" ]; then
  [ "$NO_SORRY_LIST" = 1 ] || usage_error "NO_SORRY_LIST takes the value 1"
  mode=list; modes=$((modes + 1))
fi
if [ -n "${NO_SORRY_PART:-}" ]; then
  mode=part; modes=$((modes + 1))
  [ -z "${NO_SORRY_PART_RUN:-}" ] || mode=part-run
fi
if [ -n "${NO_SORRY_COMBINE:-}" ]; then
  mode=combine; modes=$((modes + 1))
fi
[ "$modes" -le 1 ] || usage_error "NO_SORRY_LIST, NO_SORRY_PART and NO_SORRY_COMBINE are three modes; set one"
case "$mode" in part|part-run) ;; *)
  [ -z "${NO_SORRY_PART_DIR:-}" ] || usage_error "NO_SORRY_PART_DIR is set without NO_SORRY_PART"
  [ -z "${NO_SORRY_PART_RUN:-}" ] || usage_error "NO_SORRY_PART_RUN is set without NO_SORRY_PART" ;;
esac
[ "$mode" = combine ] || [ -z "${NO_SORRY_PARTITION:-}" ] \
  || usage_error "NO_SORRY_PARTITION is set without NO_SORRY_COMBINE"

# On the CI runner, say how long each phase took, in the log and in the step
# summary, so the job's one long step can be read apart. Only there: a local
# run prints what `REPRODUCING.md` quotes and nothing else.
timing_header=0
report_time() {
  if [ "${GITHUB_ACTIONS:-}" != "true" ]; then
    return 0
  fi
  local took=$(( SECONDS - $2 ))
  echo "no-sorry: timing: $1 took ${took}s"
  if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
    if [ "$timing_header" -eq 0 ]; then
      printf '| no-sorry phase | seconds |\n| --- | --- |\n' >> "$GITHUB_STEP_SUMMARY"
      timing_header=1
    fi
    echo "| $1 | ${took} |" >> "$GITHUB_STEP_SUMMARY"
  fi
}

# check <lake package dir> <regex matching our source paths> <label> [<keep log at>]
check() {
  local dir="$1" ours="$2" label="$3" keep="${4:-}"
  echo "no-sorry: building $label"
  local log
  log="$(mktemp)"
  # The build must succeed on its own terms first: an incomplete proof is a
  # different failure from one that does not compile, and both must be caught.
  (cd "$dir" && lake build 2>&1) | tee "$log"

  local found
  found="$(grep -E "declaration uses" "$log" | grep -E "$ours" || true)"
  if [ -n "$found" ]; then
    echo "::error::$label contains an incomplete declaration:" >&2
    echo "$found" >&2
    fail=1
  else
    echo "no-sorry: $label is complete"
  fi
  if [ -n "$keep" ]; then
    mv "$log" "$keep"
  else
    rm -f "$log"
  fi
}

# Replay every first-party module through the kernel from its olean.
#
# `lake build` checks a declaration with the kernel when it adds it, unless
# something asked it not to: `set_option debug.skipKernelTC true` adds the
# next declaration on the elaborator's word alone, and nothing in the
# environment records that afterwards, so neither the axiom audit nor the
# pins can see it. `leanchecker`, which ships with the pinned toolchain,
# re-checks each declaration of a module against the kernel starting from the
# module's imports; a declaration the kernel would have refused fails here.
# It is not an external verifier (it is Lean's own kernel), but it is the
# direct defence against environment hacking, and it costs about a minute.
# Four at a time for the translation package, whose modules import Mathlib
# and take a few seconds each to load; the other two are quick in sequence.
replay() {
  local dir="$1" label="$2" jobs="$3"
  shift 3
  echo "no-sorry: replaying $label through the kernel (leanchecker)"
  local failed
  failed="$(cd "$dir" && printf '%s\n' "$@" | xargs -P "$jobs" -n 1 sh -c \
    'lake env leanchecker "$0" > /dev/null 2>&1 || echo "$0"')"
  if [ -n "$failed" ]; then
    echo "::error::the kernel refused a declaration in $label:" >&2
    echo "$failed" >&2
    fail=1
  else
    echo "no-sorry: $label replays clean ($# modules)"
  fi
}
modules() {
  # <dir> <subdir>...: the module name of every .lean under each subdir.
  local dir="$1"; shift
  for sub in "$@"; do
    (cd "$dir" && ls "$sub"/*.lean) | sed 's|/|.|g; s|\.lean$||'
  done
}

# ---- the phases ---------------------------------------------------------------------------------
# Each body is the commands the script ran in that place before it was split into phases, unchanged.
# A body records a failure by setting `fail=1`; a build that does not succeed stops the script.

translation_log=""
trap '[ -z "$translation_log" ] || rm -f "$translation_log"' EXIT

phase_build_translation() {
translation_log="$(mktemp)"
check translation '(^|[^/[:alnum:]])Translation/' "the translation and its T1/T3 proofs" "$translation_log"
}

# A module outside the build target is a proof nothing is holding: the log
# scan above can only see what `lake build` elaborated. Assert every
# Translation/*.lean produced a current olean.
phase_translation_coverage() {
bash scripts/check-translation-coverage.sh || fail=1
}

phase_lifecycle_coverage() {
python3 scripts/check-lifecycle-translation-coverage.py \
  translation/Translation/TacentaLifecycle.lean || fail=1
bash scripts/check-lifecycle-translation-coverage-negatives.sh || fail=1
}

# No first-party declaration takes an evidence record that `DispatchEvidenceVacuity.lean`
# shows false or empty: such a theorem would be true and say nothing, and `#print axioms`
# would not show it (`GAP-REGISTER.md`, `DISPATCH-EVIDENCE-VACUITY`). The gate runs the
# walk as the compiled `refuted-records` executable over each translation audit module's
# closure and holds its printed block to the vacuity module's theorems; its control plants
# takers under the spellings and routes a text scan missed and checks each is reported and
# refused.
phase_refuted_records() {
bash scripts/check-refuted-records.sh || fail=1
bash scripts/check-refuted-records-negatives.sh || fail=1
}

# Each new Session primitive contract of the first proof layer has a non-vacuity witness,
# and one theorem depends on all thirteen names.  The fourteenth, `DivCeilValue`, is held by
# the required pins in attest.py.  Mutation-test that coverage so deleting a witness cannot
# leave the package green.
phase_session_satisfiability() {
bash scripts/check-session-satisfiability-negatives.sh || fail=1
}

# The numeric-precondition witnesses (`NumericWitness*.lean`) and discharge theorems
# (`*DecodedStateDischarge.lean`) are evidence about a theorem only if their statements are
# that theorem's own premises. This reads each theorem's type from the built environment,
# compares it with the module's statement, and mutation-tests the comparison.
phase_precondition_witnesses() {
bash scripts/check-precondition-witnesses.sh || fail=1
}

# The unit-only edits of the three Session Braid ports are held by one property, the anchor count
# in `unit_edit`. `--check` alone cannot see that guard removed (an unchanged source regenerates
# the same file), so break one source anchor per port script (two for the proof script) and require the port
# script to refuse.
phase_port_negatives() {
bash scripts/check-port-negatives.sh || fail=1
}

# The evidence about the Braid refinement agreements of the Session unit (the model of the six KEM
# and KDF agreements, the erasure halves, the state witnesses, the entry points) is held to
# mutations: a shape, a model field, a witness or a pinned statement changed one at a time must
# be refused, after the unmodified modules are accepted.
phase_braid_agreement() {
bash scripts/check-braid-agreement-negatives.sh || fail=1
}

# The initial dispatcher must retain its matching-key guards. These controls
# elaborate disposable copies after the positive build above; timeout or a
# compiler/dependency failure is never counted as a rejected mutation.
# The one sliceable phase: in a part it runs the slice the parts file gives it
# (`--slice k/S`, the controls whose place in `--list` is k modulo S) and keeps
# its logs and result file in the part's directory, for the combiner to read.
phase_initial_dispatch() {
python3 scripts/check-initial-dispatch-negatives.py ${phase_args[@]+"${phase_args[@]}"} || fail=1
}
units_initial_dispatch() {
python3 scripts/check-initial-dispatch-negatives.py --list
}

# The lifecycle frame proofs (`UnitLifecycleAtomicity.lean`) are one walk over each generated body.
# Plant a write in a copy of each body and require the same walk to refuse it, after requiring it
# to accept the unmodified copy; timeout, a compiler that does not start and a syntax error are
# never counted as a refusal.
phase_atomicity() {
python3 scripts/check-atomicity-negatives.py || fail=1
}

# The restated dispatch records' witnesses (`UnitLifecycleRepair.lean`): a witness for a wrong or
# weaker statement would hold nothing, so make one change to a copy of each and require Lean to
# refuse it, after requiring the unmodified copies to be accepted.
phase_repair() {
python3 scripts/check-repair-negatives.py || fail=1
}

# `establish_responder` on the initiator's first frame delivered again, at the store its first success committed
# (`UnitLifecycleResponderEstablishReplay.lean`): a copy with the second call or the commit claimed on the one-time
# path, the fingerprint claimed of the secret before it is read back, the second call claimed to return the store
# before the commit, the bundle claimed to name another KEM key or a one-time curve key, the record claimed to gain
# the one-time identifier, the reach's record claimed empty or its second call claimed to draw, the replay check
# claimed without the entry, the commit claimed with a one-time curve key, and a statement with a variable renamed
# and its pins kept must each be refused at a named declaration or pin, with a message naming the change, after the
# unmodified copies are accepted.
phase_responder_establish_replay() {
python3 scripts/check-responder-establish-replay-negatives.py || fail=1
}

# The composed Triple send theorem must consume the leaf theorem's complete
# classical refusal result, including the finite-width counter edge.  A
# disposable mutation restores the old NoSendingChain-only contract and a
# second collapses the sparse map to `noChain`; each must fail at the exact
# use which handles the generated error.
phase_send_refusal() {
python3 scripts/check-send-refusal-negatives.py || fail=1
}

# The Session unit's sparse skip refines the model's detailed skip, refusal kind included
# (`UnitLifecycleSparseSkipKindT3.lean`).  After the two unmodified copies are accepted, four changes must each be
# refused at a named declaration with a message naming the change: the kind under a mapping that swaps
# `TooManySkipped` and `SkippedStoreFull`, every refusal claimed `skippedStoreFull` and a success claimed to keep
# the state (in the composing proof, each accepted there with that proof emptied), and the error mapping claimed
# injective with `TooManySkipped` sent to `skippedStoreFull`.
phase_sparse_skip_kind() {
python3 scripts/check-sparse-skip-kind-negatives.py || fail=1
}

# The sparse skip's store-full conjunct is proved in one branch that reads the store a skip
# leaves through `hC`: a copy naming another refusal, and a copy whose branch drops `hC`,
# must each be refused at that branch.
phase_sparse_store_full() {
python3 scripts/check-sparse-store-full-negatives.py || fail=1
}

# Under an assumed AEAD law, the initiator's decrypt refuses a reply frame whose ciphertext was replaced
# (`UnitLifecycleTamperedReply.lean`): fifteen changes (in the composing proof, on leaf lemmas, and definitions with
# their pins kept) must each be refused at a named declaration or pin, with a message naming the change, after the
# unmodified copies are accepted.
phase_tampered_reply() {
python3 scripts/check-tampered-reply-negatives.py || fail=1
}

# The decrypt_ratchet refinement, its retry-loop induction, its refusal closure, its per-run bounds and the public decrypt on
# frames that are not initial messages
# (`UnitLifecycleRetryLoopT3.lean`, `UnitLifecycleDecryptRatchetT3.lean`, `UnitLifecycleDecryptRatchetScreen.lean`,
# `UnitLifecycleTripleRefusalT3.lean`, `UnitLifecycleDecryptRatchetCompleteT3.lean`,
# `UnitLifecycleDecryptRatchetCompleteScreen.lean`, `UnitLifecycleDecryptRunBounds.lean`, `UnitLifecycleDecryptT3.lean`): a copy with the fact a proof
# rests on removed, a copy whose open disjunct grows, a copy of the complete statement that regains it, a
# fault planted in a renamed copy of the generated `decrypt` and a copy of the join without its scope premise
# or on the first form must each be refused at a named declaration or pin, after the unmodified copies are
# accepted.
phase_decrypt_ratchet() {
python3 scripts/check-decrypt-ratchet-negatives.py || fail=1
}

# The invariant, the counter ceilings and the model relation at every successful
# `establish_initiator_for` output (`UnitLifecycleEstablishInitiatorShape.lean`): a copy with a law, the
# `verify_bundle` inversion or the generated clock removed, the ceilings or the relation asked of a wrong
# state, and a copy of a law with its pins kept must each be refused at a named declaration or pin, after
# the unmodified copies are accepted.
phase_established() {
python3 scripts/check-established-negatives.py || fail=1
}

# `Session::decrypt` of the responder's reply delivered again, at the initiator's session after its first receipt
# (`UnitLifecycleInitiatorRepeatedReply.lean`): a copy with the refusal claimed to take no draw, to be
# `NoReceivingChain` or to clear the pending initial message, the model's step claimed to keep the draw, the agreement
# claimed failed, the source claimed a draw ahead of the oracle, the second draw claimed of the first receipt's
# source or claimed absent before the rest, the model's step claimed on the plaintext, the relation claimed with the
# second draw as the ratchet key, the second delivery, the invariant or the first receipt claimed at another session
# or source, the reach claimed from the first send's source or accepted, a leaf claimed otherwise (the receive's
# refusal or key, the draw's agreement, the oracle kept, the byte trace's runs swapped), and a statement with a
# variable renamed and its pins kept must each be refused at a named declaration or pin, with a message naming the
# change, after the unmodified copies are accepted.
phase_initiator_repeated_reply() {
python3 scripts/check-initiator-repeated-reply-negatives.py || fail=1
}

# The initiator's second send on the run of the reply's receipt, with Session::invariant and the four ceilings at the
# session the receipt returns derived on that run and kept through the send
# (`UnitLifecycleInitiatorSecondMessage.lean`): eleven changes, to statements and a definition (the budget after the
# send, the fresh-key premise, the second plaintext's bound and the ceilings at the receipt's session in the headline;
# the plaintext bound and the source-choosing law in the reach; forwarded conjuncts; the run's definition at its pin),
# each of which must be refused at a named declaration or pin, with a message naming the change, after the two
# unmodified copies are accepted.
phase_initiator_second_message() {
python3 scripts/check-initiator-second-message-negatives.py || fail=1
}

# What an accepted `Session::import` guarantees, the restored relation and the round trip of an established
# initiator session (`UnitLifecycleRestoredSession.lean`, `UnitLifecycleSessionRoundTrip.lean`,
# `UnitLifecycleSessionCodec.lean`): a copy with the `Inconsistent` refusal, a ceiling clause, a law or a
# hypothesis removed, the scope widened, an encoded field reordered, or the round trip concluding an altered
# session, and a copy of a law with its pins kept, must each be refused at a named declaration or pin, after
# the unmodified copies are accepted.
phase_restored() {
python3 scripts/check-restored-negatives.py || fail=1
}

# The public `encrypt` at every successful `establish_initiator_for` output, its two outcomes and the
# session a successful send leaves (`UnitLifecycleEstablishedEncrypt.lean`): a copy with a law, a bound or a
# premise removed, the draw record or the key-generation law weakened, the model step or the successor
# restated wrongly, or the joint model's key generation leaving the source, and a copy of a law with its pins
# kept, must each be refused at a named declaration or pin, after the unmodified copies are accepted.
phase_encrypt() {
python3 scripts/check-encrypt-negatives.py || fail=1
}

# `establish_responder` over every input (`UnitLifecycleEstablishResponder.lean`): a copy with a law or a
# check the intermediate session's invariant rests on removed, the session's established ephemeral
# dropped, the decoder bounds weakened, the ceilings or the relation asked of a wrong state, a refusal or a
# store or random-source effect claimed otherwise than the generated code has it, a draw or the joint model
# changed, and a copy of the commit with its pins kept must each be refused at a named declaration or pin,
# with a message naming the change, after the unmodified copies are accepted.
phase_responder() {
python3 scripts/check-responder-negatives.py || fail=1
}

# `establish_responder` on the frame the initiator's first `encrypt` emits
# (`UnitLifecycleResponderFirstFrame.lean`): a copy with the agreement law weakened, the joint model's agreement
# or public key changed, the per-run KEM premise or the store's distinctness weakened, a refusal's cause
# claimed otherwise, the parts' secret, peer key or last-resort flag claimed otherwise, the decoded identifier
# or `publish`'s entry claimed otherwise, the lookup's first-occurrence premise dropped, the ratchet agreement
# or the reach's store changed, the composed frame claimed for another plaintext or another message fed to the
# responder, and a copy of the law with its pins kept must each be refused at a named declaration or pin, with a
# message naming the change, after the unmodified copies are accepted.
phase_responder_frame() {
python3 scripts/check-responder-frame-negatives.py || fail=1
}

# `establish_responder` accepting the initiator's first frame (`UnitLifecycleResponderFirstReceipt.lean`): a copy
# with the model's first message changed (chains, root relation, header, decoder condition, the model step's oracle
# or ratchet key), either new law weakened, the associated data, the responder's root or the attributed source
# claimed otherwise, a refusal claimed when its cause is absent, the composition claimed for another plaintext, a
# frame under another key, the plaintext fed instead of the bytes, the store unchanged or the draws untouched, the
# header source without its MAC, the joint model with the empty seal, and a copy of the contributory law with its
# pins kept must each be refused at a named declaration or pin, with a message naming the change, after the
# unmodified copies are accepted.
phase_responder_receipt() {
python3 scripts/check-responder-receipt-negatives.py || fail=1
}

# `Session::decrypt` of the initiator's first frame delivered again, at the responder's session after its first
# receipt (`UnitLifecycleResponderRepeatedFrame.lean`): a copy with the refusal claimed to take no draw or to be
# `NotARepeatedInitial`, the model's step claimed to keep the draw or taken at the first receipt's oracle, the second
# draw claimed of the first source, the first call claimed on the plaintext, the model session claimed at chunk
# index 1, the composed call claimed from the first source, the key generation claimed at swapped draws, the reach
# claimed from the seed or refused as not a repeat, a leaf claimed otherwise (the receive's refusal, the draw's
# agreement, the oracle kept, the ephemeral check on the identity key), and a statement with a variable renamed and its
# pins kept must each be refused at a named declaration or pin, with a message naming the change, after the
# unmodified copies are accepted.
phase_responder_repeated_frame() {
python3 scripts/check-responder-repeated-frame-negatives.py || fail=1
}

# The Session unit's refinement constants, kernel proofs since 2026-10-21 (they were `native_decide`): a copy with a
# label claimed with one byte changed, a bound claimed wrong, the `(1 : u64)` step claimed as two, the export panic
# message claimed to fit 42 bytes, and `native_decide` restored under the constant's live pin must each be refused at
# its own declaration or pin, with a message naming the change, after the unmodified copies are accepted; and
# `export_message_fits` must state exactly the type of the compiler-trust axiom `export` carries, and a copy with a
# word of the message dropped must not.
phase_discharge_native_decide() {
python3 scripts/check-discharge-native-decide-negatives.py || fail=1
}

# `Session::invariant` and the four ceilings at the session `establish_responder` returns on the initiator's first
# frame (`UnitLifecycleResponderSuccessor.lean`): a copy with the received Triple's counters, the clock, the sending
# key's canonicity, the ratchet key's bytes or the agreement's epoch changed, the decoder lemma widened to two chunks
# or without its chunk count, either walk claimed to keep what the code changes, the composition claimed of the
# prepared model, the initiator's session or the plaintext, and a copy of the session definition with its pins kept
# must each be refused at a named declaration or pin, with a message naming the change, after the unmodified copies
# are accepted; each change it labels inside a composing proof must be accepted there with that proof emptied (those
# it labels projections are not probed), and each it labels statement-shape still refused with the projected proof
# emptied (its labels are its own guidance).
phase_responder_successor() {
python3 scripts/check-responder-successor-negatives.py || fail=1
}

# The responder's `encrypt` at the session `establish_responder` returns on the initiator's first frame
# (`UnitLifecycleResponderReply.lean`): a copy with the call claimed to return another source, the reply claimed
# wrapped, sealed on the other sparse chain or under the prepared ratchet key, its relation claimed with the Triple
# unchanged, the receipt's root-key equation claimed with the sparse root or its call taken on the plaintext, the
# agreement's send claimed to emit a header message or an output, the draw record claimed at a drawing state, the
# reply header's sparse number, the headroom's header room, the composite's agreement type or the model step's pending
# premise changed, the reach's source changed, and a copy of the frame definition with its pins kept must each be
# refused at a named declaration or pin, with a message naming the change, after the unmodified copies are accepted;
# each change it labels inside a composing proof must be accepted there with that proof emptied (those it labels
# projections are not probed) (its labels are its own guidance).
phase_responder_reply() {
python3 scripts/check-responder-reply-negatives.py || fail=1
}

# The initiator's `decrypt` of the responder's reply at the session its first `encrypt` left
# (`UnitLifecycleResponderReplyReceipt.lean`): a copy with the decrypt claimed from the source before the first send,
# the reply claimed to carry the peer key, the stale-key refusal claimed as `Aead` or on a fresh key (in the outcomes
# and the two-outcome theorem), the success claimed to keep the pending initial message or to take no draw, the
# plaintext claimed to be the first message, the named agreement claimed of the responder's draw, the freshness
# premise claimed against the initiator's own key, the model receive's premise, refusal or previous chain length
# changed, the joint model's public key made constant, the fresh private key's reading, the first agreement's key, the
# model's stale-key outcome or the first send's agreement epoch changed, the reach's decrypt claimed at the
# responder's session, and a copy of the receipt session definition with its pins kept must each be refused at a named
# declaration or pin, with a message naming the change, after the unmodified copies are accepted; each change it
# labels inside a composing proof must be accepted there with that proof emptied (those it labels projections are not
# probed), and each it labels statement-shape still refused with the projected proof emptied (its labels are its own
# guidance).
phase_responder_reply_receipt() {
python3 scripts/check-responder-reply-receipt-negatives.py || fail=1
}

# The responder's decrypt of the initiator's second message at its session after the reply, with Session::invariant
# and the four ceilings kept through the receive (`UnitLifecycleResponderSecondReceipt.lean`): nineteen changes to
# statements and definitions (the draw, the plaintext, the stale arm's refusal and the decoder after the receipt in
# the two-outcome theorem; the fresh-key premise and the budget after the receipt in the success headline; the
# responder's further bytes and the source-choosing law in the run, the law in the reach and the stale run's key
# equation in the stale reach; forwarded conjuncts; the model's stale receive, the Triple after the receipt, the
# decoder at the responder's session and the in-order step's premise in the leaf lemmas; the two runs' definitions at
# their pins), each of which must be refused at a named declaration or pin, with a message naming the change, after
# the two unmodified copies are accepted; each change it labels inside a composing proof must be accepted there with
# that proof emptied (those it labels projections are not probed) (its labels are its own guidance).
phase_responder_second_receipt() {
python3 scripts/check-responder-second-receipt-negatives.py || fail=1
}

# The responder's encrypt at the session its receipt of the initiator's second message returned
# (`UnitLifecycleResponderSecondSend.lean`): a copy with one change to a statement or a definition (the second reply's
# call claimed to return the source the reply left or at the session before the receipt, the session after it claimed
# unwritten, the frame claimed with the initiator's key or on the responder's receiving sparse chain, the relation
# claimed with the receipt's Triple, the budget claimed beyond the clock, the ceilings claimed as a unit of room and
# the invariant claimed of the session before, and the receipt's plaintext, in the headline; the responder's further
# bytes, the key-choosing law, the plaintext bound and the run's call in the reach; the model's Triple after the send,
# its step's draw and composite type, the model budget and the refinement's invariant premise in the leaf lemmas; the
# run's and the frame's definitions at their pins), each of which must be refused at a named declaration or pin, with
# a message naming the change, after the two unmodified copies are accepted; each change it labels inside a composing
# proof must be accepted there with that proof emptied (those it labels projections are not probed).
phase_responder_second_send() {
python3 scripts/check-responder-second-send-negatives.py || fail=1
}

# The bridge between `Triple::invariant` and the model (`UnitTripleInvModel.lean`) and send preservation at an
# agreement state that takes no draw (`UnitLifecycleSendPreserve.lean`): a copy with the no-draw premise weakened, the
# key-pair clone record swapped for the erasure one, the budget claimed unspent or the relation after the call claimed
# to the model before it (in the general step), the budget after the reply claimed beyond the clock or two operations
# longer (in the run's headline), the establishment's law swapped (in the re-derivation), the reply's call or relation
# changed where the headline forwards them, the sparse send's frame claimed with an agreement output, the budget
# claimed kept with no unit to spend, `next_chunk` claimed to change the codewords, the key-generation state claimed
# to send without a draw, the structural clauses claimed blind to the sparse epoch, the bridge without its roles
# clause or with a plain-sum window, the reply's corollary claimed at the initiator's session, and a copy of the
# bridge's predicate regrouped with its pins kept must each be refused at a named declaration or pin, with a message
# naming the change, after the unmodified copies are accepted; each change it labels inside a composing proof must be
# accepted there with that proof emptied (those it labels projections are not probed), every change refused in a
# composing proof must carry a label, checked at start-up against the module's text, and each it labels
# statement-shape must still be refused with the projected proof emptied (its labels are its own guidance).
phase_send_preservation() {
python3 scripts/check-send-preservation-negatives.py || fail=1
}

# The initiator's second `encrypt` at the session its receipt of the reply returned
# (`UnitLifecycleInitiatorSecondSend.lean`): a copy with the model's second step claimed to take a draw, the call
# claimed to leave the source before the receipt, the second frame claimed at chunk index 0 or sealed on the sparse
# chain the initiator receives on, the relation after the call claimed with the receipt's Triple or the header encoder
# not advanced, the session after the call claimed to keep the first send's pending initial message, the agreement's
# send at `KeysSampled` claimed to change the source or keep the encoder, the providers claimed at a drawing state,
# the draw record claimed with an exhausted encoder, the second header's previous chain length or sparse number
# changed, the model step claimed to keep the encoder, the first send's encoder claimed at position 0, and a copy of
# the frame definition with its pins kept must each be refused at a named declaration or pin, with a message naming
# the change, after the unmodified copies are accepted; each change it labels inside the composing proof must be
# accepted there with that proof emptied (those it labels projections are not probed); every change refused in the
# composing proof must carry a label, checked at start-up against the module's text (its labels are its own guidance).
phase_initiator_second_send() {
python3 scripts/check-initiator-second-send-negatives.py || fail=1
}

# Session::decrypt keeps Session::invariant on an in-order receive at NoHeaderReceived or KeysSampled, and the two
# receipts on their runs (`UnitLifecycleReceivePreserve.lean`): 23 changes, to statements and a definition (the decoder
# scope, the clone record, the budget, the relation after the call, the canonical-key law and the public-key clause in
# the general step; the budget and the fresh-key premise on the reply's run; the leaf lemmas), each of which must be
# refused at a named declaration or pin, with a message naming the change, after the two unmodified copies are
# accepted.
phase_receive_preservation() {
python3 scripts/check-receive-preservation-negatives.py || fail=1
}

# The generated files' axiom sets, as the environment has them. The axiom
# audit that ran inside the build above walked the elaborated environment and
# printed every axiom it found in a generated `Translation.Tacenta*` module as
# an `audit-axiom:` line (Lake replays the lines from its log for an
# up-to-date module, so a cached build carries them too). `attest.py --check`
# holds the same files to the recorded manifest by reading their *text*; this
# compares the manifest with what the text elaborated to, so an axiom the
# text scan cannot recognise (one a macro produced, or a command added) and
# a recorded axiom the environment no longer holds both fail here. It reads the
# log of the translation build of this same run (a prelude phase, so every part
# that runs this phase has built the package first).
phase_axiom_comparison() {
if grep -q "audit-axiom:" "$translation_log"; then
  python3 scripts/attest.py --compare-audit "$translation_log" || fail=1
else
  echo "::error::the translation build log carries no audit-axiom lines; the axiom audit did not run" >&2
  fail=1
fi
rm -f "$translation_log"
translation_log=""
}

phase_build_proofs() {
check .           '(^|[^/[:alnum:]])(Proofs|Model)/' "the model-layer proofs"
}

# The model package on its own terms, so that `Properties/` is built and
# scanned. Nothing in `Proofs/` imports the forward-secrecy, post-compromise,
# secrecy and authentication theorems, so the check above does not elaborate
# them; this one does, and its regex names `Properties` so a `sorry` in any of
# those five files is failed on.
phase_build_model() {
check ../tacenta-model '(^|[^/[:alnum:]])(Model|Properties)/' "the model and its property theorems"
}

# Constructs a `sorry` grep cannot see. An `axiom`, an `opaque`, an
# `@[implemented_by]` or `@[extern]` (which swap a definition's meaning for a
# compiled program's), a `partial def` or `unsafe` in hand-written Lean each
# widen the trust base without any compiler warning. The builds above already
# refused them from the elaborated environment (`Model.AxiomAudit`, run by the
# `AxiomAudit` modules in each package); this is the textual second line, and
# the only one that sees `set_option debug.skipKernelTC`. Relative to this
# package's directory, which the `cd` at the top made the working directory;
# `$(dirname "$0")` would be relative to where the caller was, which on the
# runner is not this package.
phase_lean_constructs() {
bash scripts/check-lean-constructs.sh || fail=1
}

# The audit above walks only what its invoking module imports, and each
# package's audit module carries a hand-maintained import list. A first-party
# module missing from every list is built, scanned and replayed, and never
# audited. This asks Lean for each module's imports and fails if any
# first-party module (the generated `Tacenta*.lean` included, since the
# `audit-axiom:` comparison above sees only the generated modules the audit
# reached) is outside the seven audit modules' import closure.
phase_audit_reach() {
bash scripts/check-audit-reach.sh || fail=1
}

# A hypothesis nothing satisfies makes the theorem that takes it true and empty, and neither the
# kernel nor the pins notice. This reads the hypotheses of every claimed T1 and T3 theorem of the
# leaf crates and the three-leaf unit from the built environment and fails if one is connected to
# nothing (no bridge to a satisfiable shape, no derivation the ledger names), names no predicate, or
# is about a variable only hypotheses mention. It does not show that a connected hypothesis is
# satisfiable or that the hypotheses of one theorem hold together; the header of the script says
# what it cannot see.
# Its mutation controls, `check-hypothesis-witnesses-negatives.sh`, rebuild a copy of the package for
# each case and take about fifteen minutes on an idle machine, so they are not run here. No workflow
# runs them yet; run them by hand with
# `bash tacenta-proofs/scripts/check-hypothesis-witnesses-negatives.sh`.
phase_hypothesis_witnesses() {
bash scripts/check-hypothesis-witnesses.sh || fail=1
}

# `check-audit-reach.sh` is itself a gate that was shown to refuse once, by hand. This plants an orphan
# module in each source directory and a wrong audit call in a disposable worktree, with the builds above
# linked in, and requires it to refuse each for its stated reason.
phase_audit_reach_negatives() {
bash scripts/check-audit-reach-negatives.sh || fail=1
}

# The `#guard_msgs` pins state the axioms and the statements the documents cite. This edits one pin of each
# kind in a disposable worktree and requires Lean to refuse it, so a pin that cannot fail is noticed.
phase_pin_negatives() {
bash scripts/check-pin-negatives.sh || fail=1
}

# Both of the checks above ask what the audit found. This one asks whether the
# audit finds anything: it plants declarations the rule says to refuse, and the
# one shape the rule says to allow, in a throwaway first-party module and
# compares the outcome with the rule. It is the only check that would notice
# the audit going quiet, which matters most for the waiver `compilerTrust`
# grants an unmentioned compiler-trust axiom.
phase_audit_negatives() {
bash scripts/check-audit-negatives.sh || fail=1
}

phase_replay_translation() {
replay translation "the translation and its T1/T3 proofs" 4 $(modules translation Translation)
}
phase_replay_proofs() {
replay .           "the model-layer proofs" 1 $(modules . Proofs)
}
phase_replay_model() {
replay ../tacenta-model "the model and its property theorems" 1 $(modules ../tacenta-model Model Properties)
}

# The replay above reports what `leanchecker` finds. This shows that, on the pinned toolchain, it finds
# a declaration added with the kernel check switched off: two one-line modules, one sound and one not.
phase_kernel_replay_negative() {
bash scripts/check-kernel-replay-negative.sh || fail=1
}

# ---- running them ---------------------------------------------------------------------------------

phase_count=0
phases_failed=""
phases_seen=""
phase_args=()

# selected <id>: the slice (or `-`) the part's selection gives a phase, or status 1 if it is not the part's.
selected() {
  awk -F '\t' -v id="$1" '$1 == id { print $2; found = 1 } END { exit !found }' "$NO_SORRY_PART_SELECTION"
}

# run_phase <id> <prelude|plain|sliceable> <label> <function> [<function listing its controls>]
run_phase() {
  local id="$1" kind="$2" label="$3" fn="$4" units="${5:-}"
  phase_count=$((phase_count + 1))
  phases_seen="$phases_seen $id"
  if [ "$mode" = list ]; then
    printf 'phase\t%s\t%s\t%s\n' "$id" "$kind" "$label"
    if [ "$kind" = sliceable ]; then
      "$units" | awk -v id="$id" '{ print "unit\t" id "\t" $0 }'
    fi
    return 0
  fi
  local slice="-"
  phase_args=()
  if [ "$mode" = part-run ] && [ "$kind" != prelude ]; then
    slice="$(selected "$id")" || return 0
    if [ "$kind" = sliceable ]; then
      mkdir "$NO_SORRY_PART_DIR/$id"
      phase_args=(--slice "$slice" --log-dir "$NO_SORRY_PART_DIR/$id")
    fi
  fi
  local before="$fail" t=$SECONDS status took
  fail=0
  "$fn"
  status="$fail"
  took=$((SECONDS - t))
  fail=$((before | status))
  phase_args=()
  report_time "$label" "$t"
  [ "$status" -eq 0 ] || phases_failed="$phases_failed $id"
  if [ "$mode" = part-run ]; then
    printf '%s\t%s\t%s\t%s\n' "$id" "$slice" "$status" "$took" >> "$NO_SORRY_PART_RUN"
    if [ "$slice" = "-" ]; then
      echo "no-sorry: phase $id finished with status $status in ${took}s"
    else
      echo "no-sorry: phase $id $slice finished with status $status in ${took}s"
    fi
  fi
}

phases() {
  run_phase build-translation prelude "build and scan: translation package" phase_build_translation
  run_phase translation-coverage plain "translation coverage" phase_translation_coverage
  run_phase lifecycle-coverage plain "lifecycle public-root coverage" phase_lifecycle_coverage
  run_phase refuted-records plain "refuted evidence records untaken" phase_refuted_records
  run_phase session-satisfiability plain "Session contract satisfiability control" phase_session_satisfiability
  run_phase precondition-witnesses plain "numeric-precondition witnesses and controls" phase_precondition_witnesses
  run_phase port-negatives plain "port-script unit-edit controls" phase_port_negatives
  run_phase braid-agreement plain "Braid agreement witnesses control" phase_braid_agreement
  run_phase initial-dispatch sliceable "initial dispatcher proof-dependency controls" phase_initial_dispatch units_initial_dispatch
  run_phase atomicity plain "lifecycle frame-proof controls" phase_atomicity
  run_phase repair plain "restated dispatch record controls" phase_repair
  run_phase responder-establish-replay plain "responder-establish-replay proof-dependency control" phase_responder_establish_replay
  run_phase send-refusal plain "send refusal proof-dependency control" phase_send_refusal
  run_phase sparse-skip-kind plain "sparse skip refusal-kind proof-dependency control" phase_sparse_skip_kind
  run_phase sparse-store-full plain "sparse store-full proof-dependency control" phase_sparse_store_full
  run_phase tampered-reply plain "tampered-reply proof-dependency control" phase_tampered_reply
  run_phase decrypt-ratchet plain "decrypt_ratchet refinement proof-dependency control" phase_decrypt_ratchet
  run_phase established plain "established initiator proof-dependency control" phase_established
  run_phase initiator-repeated-reply plain "initiator-repeated-reply proof-dependency control" phase_initiator_repeated_reply
  run_phase initiator-second-message plain "initiator-second-message proof-dependency control" phase_initiator_second_message
  run_phase restored plain "restored session proof-dependency control" phase_restored
  run_phase encrypt plain "established encrypt proof-dependency control" phase_encrypt
  run_phase responder plain "establish_responder proof-dependency control" phase_responder
  run_phase responder-frame plain "first-frame responder proof-dependency control" phase_responder_frame
  run_phase responder-receipt plain "first-receipt responder proof-dependency control" phase_responder_receipt
  run_phase responder-repeated-frame plain "responder-repeated-frame proof-dependency control" phase_responder_repeated_frame
  run_phase discharge-native-decide plain "refinement constants proof-dependency control" phase_discharge_native_decide
  run_phase responder-successor plain "responder successor proof-dependency control" phase_responder_successor
  run_phase responder-reply plain "responder reply proof-dependency control" phase_responder_reply
  run_phase responder-reply-receipt plain "responder reply receipt proof-dependency control" phase_responder_reply_receipt
  run_phase responder-second-receipt plain "responder-second-receipt proof-dependency control" phase_responder_second_receipt
  run_phase responder-second-send plain "responder-second-send proof-dependency control" phase_responder_second_send
  run_phase send-preservation plain "send preservation proof-dependency control" phase_send_preservation
  run_phase initiator-second-send plain "initiator second send proof-dependency control" phase_initiator_second_send
  run_phase receive-preservation plain "receive-preservation proof-dependency control" phase_receive_preservation
  run_phase axiom-comparison plain "axiom comparison" phase_axiom_comparison
  run_phase build-proofs prelude "build and scan: proofs package" phase_build_proofs
  run_phase build-model prelude "build and scan: model package" phase_build_model
  run_phase lean-constructs plain "construct check" phase_lean_constructs
  run_phase audit-reach plain "audit reach" phase_audit_reach
  run_phase hypothesis-witnesses plain "hypothesis witnesses" phase_hypothesis_witnesses
  run_phase audit-reach-negatives plain "audit reach negatives" phase_audit_reach_negatives
  run_phase pin-negatives plain "pin negatives" phase_pin_negatives
  run_phase audit-negatives plain "audit negatives" phase_audit_negatives
  run_phase kernel-replay-translation plain "kernel replay: the translation and its T1/T3 proofs" phase_replay_translation
  run_phase kernel-replay-proofs plain "kernel replay: the model-layer proofs" phase_replay_proofs
  run_phase kernel-replay-model plain "kernel replay: the model and its property theorems" phase_replay_model
  run_phase kernel-replay-negative plain "kernel replay negative control" phase_kernel_replay_negative
}

final_line() {
  echo "no-sorry: all $1 phases passed"
}

# The phase table and the parts file are read together by scripts/no-sorry-parts.py, named in full below so that
# the gate inventory's walk sees each call.
parts_file="scripts/no-sorry-parts.txt"

case "$mode" in
  list)
    phases
    exit 0 ;;
  part)
    # The parent of a part: check the directory and the selection before anything runs, run the part
    # as a child whose output is the part's log, then write the manifest from what the child recorded.
    part_dir="${NO_SORRY_PART_DIR:-}"
    [ -n "$part_dir" ] || usage_error "NO_SORRY_PART needs NO_SORRY_PART_DIR, the directory the part writes"
    if [ -e "$part_dir" ] && { [ ! -d "$part_dir" ] || [ -n "$(ls -A "$part_dir")" ]; }; then
      usage_error "NO_SORRY_PART_DIR $part_dir is not an empty directory"
    fi
    mkdir -p "$part_dir"
    part_dir="$(cd "$part_dir" && pwd -P)"
    work="$(mktemp -d)"
    (mode=list; phases) > "$work/table"
    python3 scripts/no-sorry-parts.py resolve --table "$work/table" --parts "$parts_file" --part "$NO_SORRY_PART" \
      > "$work/selection" || { rm -rf "$work"; exit 2; }
    start="$(git rev-parse HEAD) $(git rev-parse 'HEAD^{tree}') $(
      [ -z "$(git status --porcelain --untracked-files=no)" ] && echo clean || echo changed)"
    echo "no-sorry: part $NO_SORRY_PART on $(git rev-parse --short HEAD): the prelude and" \
      "$(cut -f1 "$work/selection" | tr '\n' ' ')"
    : > "$work/status"
    set +e
    env NO_SORRY_PART_RUN="$work/status" NO_SORRY_PART_SELECTION="$work/selection" \
      NO_SORRY_PART_DIR="$part_dir" bash scripts/no-sorry.sh 2>&1 | tee "$part_dir/part.log"
    rc=${PIPESTATUS[0]}
    set -e
    toolchain="$(cd translation && lean --version 2>/dev/null)" || toolchain=""
    python3 scripts/no-sorry-parts.py manifest --table "$work/table" --parts "$parts_file" --part "$NO_SORRY_PART" \
      --dir "$part_dir" --status "$work/status" --script scripts/no-sorry.sh --start "$start" \
      --toolchain "${toolchain:-unknown}" --build-cache "${NO_SORRY_BUILD_CACHE:-none}" --exit "$rc"
    rm -rf "$work"
    echo "no-sorry: part $NO_SORRY_PART exited $rc and wrote $part_dir; a part is not the gate"
    [ "$rc" -eq 0 ] || exit "$rc"
    exit 0 ;;
  combine)
    [ -n "${NO_SORRY_PARTITION:-}" ] || usage_error "NO_SORRY_COMBINE needs NO_SORRY_PARTITION"
    echo "no-sorry: combining the parts of partition $NO_SORRY_PARTITION on $(git rev-parse --short HEAD)"
    work="$(mktemp -d)"
    (mode=list; phases) > "$work/table"
    if ! python3 scripts/no-sorry-parts.py combine --table "$work/table" --parts "$parts_file" \
        --partition "$NO_SORRY_PARTITION" --dir "$NO_SORRY_COMBINE" --script scripts/no-sorry.sh; then
      rm -rf "$work"
      exit 1
    fi
    count="$(grep -c '^phase' "$work/table")"
    rm -rf "$work"
    final_line "$count"
    exit 0 ;;
esac

phases

if [ "$mode" = part-run ]; then
  # Every phase the selection names was reached: the parent derived it from this same list.
  for id in $(cut -f1 "$NO_SORRY_PART_SELECTION"); do
    case " $phases_seen " in *" $id "*) ;; *)
      echo "::error::no-sorry: the part's phase $id is not a phase of this script" >&2
      fail=1 ;;
    esac
  done
elif [ "$fail" -eq 0 ]; then
  final_line "$phase_count"
else
  echo "no-sorry: phases that failed:$phases_failed" >&2
fi

exit "$fail"
