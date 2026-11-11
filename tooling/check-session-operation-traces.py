#!/usr/bin/env python3
"""Check the committed P6 session/prekey operation-trace corpus.

This is a structural gate for the schema at
``tacenta-test-vectors/schema/session-operation-trace.schema.json``.  It does
not interpret cryptographic fixtures or claim that a trace's declared effect
is true; the specification-only operation reader does that.  Keeping the structural gate here
means an omitted required family, malformed step, or weakened control cannot
quietly leave the committed corpus.

It also checks the separately versioned supplement
(``tacenta-test-vectors/traces/session-operation-trace-supplement.json``,
schema version 2, ``session-operation-trace-supplement.md``) for the message
size bound: version 1's rules, plus its added refusals and ``random_draws``,
its required traces, the stated no-draw no-op of every size refusal, and a
provenance that says it is not independently authored.  The P6
operation reader does not read the supplement; the Rust runner's
``operation_trace_supplement.rs`` interprets it against tacenta-core.
"""

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TRACE = ROOT / "tacenta-test-vectors/traces/session-operation-trace.json"
SUPPLEMENT = ROOT / "tacenta-test-vectors/traces/session-operation-trace-supplement.json"

ACTORS = {"initiator", "responder", "application"}
OPS = {
    "create-prekey-store", "publish-bundle", "replenish",
    "rotate-signed-prekey", "rotate-kem", "establish-initiator",
    "establish-responder", "send", "receive", "receive-repeated-initial",
    "restore-prekey-store", "restore-session",
}
REFUSALS = {
    "decode-failure", "authentication-failure", "NotARepeatedInitial",
    "ReplayedLastResort", "LastResortRecordFull",
}
EFFECTS = {
    "prekey_store": {
        "unchanged", "created", "replenished", "signed-prekey-rotated",
        "kem-prekey-rotated", "one-time-keys-deleted",
        "last-resort-fingerprint-added", "restored",
    },
    "session": {
        "unchanged", "initiator-pending", "responder-established",
        "message-accepted", "terminal-failed", "restored",
    },
    "next_id": {"unchanged", "advanced", "at-ceiling"},
    "one_time_curve": {"unchanged", "deleted", "absent"},
    "one_time_kem": {"unchanged", "deleted", "last-resort"},
    "last_resort_record": {"unchanged", "added", "dropped"},
    "retired_signed_prekey": {"unchanged", "retained", "dropped"},
    "retired_kem_prekey": {"unchanged", "retained", "dropped"},
}
REQUIRED = {
    "prekey-store-lifecycle", "prekey-store-identifier-ceiling",
    "establish-initiator-with-one-time-curve-prekey",
    "establish-initiator-without-one-time-curve-prekey",
    "establish-responder-with-one-time-curve-prekey",
    "establish-responder-last-resort",
    "establish-responder-forged-initial-ciphertext",
    "one-time-kem-prekey-replay-refused",
    "last-resort-handshake-replay-refused", "last-resort-record-full-refused",
    "repeated-initial-accepted-on-responder-session",
    "not-a-repeated-initial-on-initiator-session",
    "not-a-repeated-initial-changed-ephemeral",
    "not-a-repeated-initial-changed-identity",
    "restore-prekey-store-then-replenish", "restore-session-then-send",
    "control-wrong-durable-effect", "control-missing-required-input",
    "receive-ordinary-authenticated",
    "receive-out-of-order-then-recovery-then-duplicate-refused",
    "control-family7-duplicate-wrongly-accepted",
    "braid-terminal-failure-persists-and-refuses",
    "control-family8-missing-message-input",
    "establish-initiator-bad-prekey-signature-refused",
    "establish-initiator-non-contributory-dh-refused",
    "establish-initiator-malformed-bundle-refused",
    "control-family9-malformed-bundle-wrongly-pending",
}

SUPPLEMENT_REFUSALS = REFUSALS | {"PlaintextTooLong", "AgreementFailed"}
SUPPLEMENT_EFFECTS = dict(EFFECTS, random_draws={"none"})
SUPPLEMENT_REQUIRED = {
    "send-plaintext-too-long-pending-and-established",
    "send-plaintext-too-long-before-agreement-failed",
    "establish-responder-frame-too-long",
    "receive-ratchet-frame-too-long",
    "receive-repeated-initial-nested-too-long",
    "receive-frame-too-long-before-agreement-failed",
    "receive-on-failed-session-in-order",
    "control-plaintext-too-long-wrongly-accepted",
}
SUPPLEMENT_PROVENANCE = "Not independently authored"


def problem(problems, where, message):
    problems.append(f"{where}: {message}")


def check_traces(problems, label, traces, refusals, effects, supplement=False):
    """Check one corpus's traces; return (trace ids, step count)."""
    ids = set()
    step_count = 0
    for i, trace in enumerate(traces):
        where = f"{label}traces[{i}]"
        if not isinstance(trace, dict) or set(trace) - {"id", "comment", "fixtures", "steps"} or not {"id", "steps"} <= set(trace if isinstance(trace, dict) else {}):
            problem(problems, where, "must have id and steps, with only id/comment/fixtures/steps")
            continue
        trace_id = trace["id"]
        if not isinstance(trace_id, str) or not trace_id:
            problem(problems, where + ".id", "must be a non-empty string")
        elif trace_id in ids:
            problem(problems, where + ".id", f"duplicate trace id {trace_id!r}")
        else:
            ids.add(trace_id)
        if "fixtures" in trace and (not isinstance(trace["fixtures"], dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in trace["fixtures"].items())):
            problem(problems, where + ".fixtures", "must map string names to string descriptions")
        steps = trace["steps"]
        if not isinstance(steps, list) or not steps:
            problem(problems, where + ".steps", "must be a non-empty array")
            continue
        for j, step in enumerate(steps):
            step_count += 1
            step_where = f"{where}.steps[{j}]"
            if not isinstance(step, dict) or set(step) != {"actor", "op", "inputs", "expect", "effect"}:
                problem(problems, step_where, "must have exactly actor, op, inputs, expect and effect")
                continue
            if step["actor"] not in ACTORS:
                problem(problems, step_where + ".actor", "is not a declared actor")
            if step["op"] not in OPS:
                problem(problems, step_where + ".op", "is not a declared operation")
            if not isinstance(step["inputs"], dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in step["inputs"].items()):
                problem(problems, step_where + ".inputs", "must map string names to string fixture/scalar values")
            expect = step["expect"]
            if not isinstance(expect, dict) or set(expect) - {"outcome", "refusal"} or "outcome" not in expect or expect["outcome"] not in {"ok", "refused"}:
                problem(problems, step_where + ".expect", "must name outcome ok or refused, with optional refusal")
            elif expect["outcome"] == "ok" and "refusal" in expect:
                problem(problems, step_where + ".expect", "an ok step carries no refusal")
            elif "refusal" in expect and expect["refusal"] not in refusals:
                problem(problems, step_where + ".expect.refusal", "is not a source-named refusal")
            effect = step["effect"]
            if not isinstance(effect, dict) or not {"prekey_store", "session"} <= set(effect) or set(effect) - set(effects):
                problem(problems, step_where + ".effect", "must name prekey_store and session, with only declared effect fields")
            else:
                for field, value in effect.items():
                    if value not in effects[field]:
                        problem(problems, step_where + f".effect.{field}", "is not a declared effect")
                # A control may deliberately assert a wrong durable effect so
                # the operation reader can reject it. Ordinary
                # refused traces must still model the specified no-op.
                if (not trace_id.startswith("control-") and expect.get("outcome") == "refused"
                        and (effect.get("prekey_store") != "unchanged" or effect.get("session") != "unchanged")):
                    problem(problems, step_where + ".effect", "a refused operation leaves store and session unchanged")
                # The supplement's size refusals: the sender's rule, and a frame
                # the size rule refuses (named by its fixture), draw nothing.
                if supplement and not trace_id.startswith("control-") and isinstance(expect, dict):
                    sized = expect.get("refusal") == "PlaintextTooLong" or (
                        expect.get("refusal") == "decode-failure"
                        and str(step["inputs"].get("message", "")).endswith("oversized"))
                    if sized and effect.get("random_draws") != "none":
                        problem(problems, step_where + ".effect", "a size refusal states random_draws none")
                    if (sized and step["op"] == "establish-responder"
                            and any(effect.get(f) != "unchanged" for f in ("one_time_curve", "one_time_kem", "last_resort_record"))):
                        problem(problems, step_where + ".effect", "a responder size refusal states its prekeys and replay record unchanged")
    return ids, step_count


def load(problems, path):
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        problem(problems, path.name, f"cannot read {path}: {exc}")
        return None


def main():
    problems = []
    doc = load(problems, TRACE)
    if doc is None:
        print("check-session-operation-traces: " + problems[0], file=sys.stderr)
        return 1
    if not isinstance(doc, dict) or set(doc) != {"schema_version", "algorithm", "source", "traces"}:
        problem(problems, "document", "must have exactly schema_version, algorithm, source and traces")
    if doc.get("schema_version") != 1:
        problem(problems, "document.schema_version", "must be 1")
    if doc.get("algorithm") != "session-operation-trace":
        problem(problems, "document.algorithm", "must be session-operation-trace")
    if not isinstance(doc.get("source"), str) or not doc["source"]:
        problem(problems, "document.source", "must be a non-empty string")
    traces = doc.get("traces")
    if not isinstance(traces, list) or not traces:
        problem(problems, "document.traces", "must be a non-empty array")
        traces = []
    ids, step_count = check_traces(problems, "", traces, REFUSALS, EFFECTS)
    missing = REQUIRED - ids
    if missing:
        problem(problems, "document.traces", "missing required trace(s): " + ", ".join(sorted(missing)))

    sup = load(problems, SUPPLEMENT)
    sup_traces, sup_ids, sup_steps = [], set(), 0
    if sup is not None:
        if not isinstance(sup, dict) or set(sup) != {"schema_version", "algorithm", "source", "provenance", "traces"}:
            problem(problems, "supplement", "must have exactly schema_version, algorithm, source, provenance and traces")
            sup = {}
        if sup.get("schema_version") != 2:
            problem(problems, "supplement.schema_version", "must be 2")
        if sup.get("algorithm") != "session-operation-trace-supplement":
            problem(problems, "supplement.algorithm", "must be session-operation-trace-supplement")
        if not isinstance(sup.get("source"), str) or not sup["source"]:
            problem(problems, "supplement.source", "must be a non-empty string")
        if not isinstance(sup.get("provenance"), str) or SUPPLEMENT_PROVENANCE not in sup["provenance"]:
            problem(problems, "supplement.provenance", f"must say '{SUPPLEMENT_PROVENANCE}'")
        sup_traces = sup.get("traces")
        if not isinstance(sup_traces, list) or not sup_traces:
            problem(problems, "supplement.traces", "must be a non-empty array")
            sup_traces = []
        sup_ids, sup_steps = check_traces(problems, "supplement.", sup_traces, SUPPLEMENT_REFUSALS,
                                          SUPPLEMENT_EFFECTS, supplement=True)
        sup_missing = SUPPLEMENT_REQUIRED - sup_ids
        if sup_missing:
            problem(problems, "supplement.traces", "missing required trace(s): " + ", ".join(sorted(sup_missing)))
        if sup_ids & ids:
            problem(problems, "supplement.traces", "reuses version 1 trace id(s): " + ", ".join(sorted(sup_ids & ids)))

    if problems:
        for item in problems:
            print("check-session-operation-traces: " + item, file=sys.stderr)
        return 1
    print(f"session-operation-traces: {len(traces)} traces, {step_count} steps; current corpus IDs and controls present")
    print(f"session-operation-traces: supplement (version 2, not independently authored): {len(sup_traces)} traces, {sup_steps} steps; required traces and control present")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
