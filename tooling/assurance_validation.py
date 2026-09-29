"""Shared fail-closed validation for assurance receipts and manifests."""
from __future__ import annotations

import functools
import json
import re
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
REQUIRED_CHECKS = {"rust", "msrv", "armv7", "vectors", "audit", "proofs", "translation", "checks"}
ALLOWED_STATUSES = {"pass", "fail", "missing", "skipped", "inconclusive", "not_applicable"}
# The receipt that is conditional, not required: present for a pull request.
CONDITIONAL_CHECKS = {"sign-off"}
# The manifest holding the expected form of the required workflow, and where
# in it the receipt steps are.
REQUIRED_STEPS_FILE = ROOT / "tooling" / "required-steps.json"
REQUIRED_WORKFLOW = ".github/workflows/ci.yml"
RECEIPT_ACTION = "./.github/actions/assurance-receipt"
EVENTS = ("pull_request", "push")


def _events_for(condition: Any) -> list[str]:
    """The events an `if` lets its job or step run in: the event it names, else
    both. Only the two exact conditions the workflow uses are read; any other
    condition is treated as running in both, which is the wider expectation."""
    text = re.sub(r"\s+", "", str(condition or "")).lower()
    return [event for event in EVENTS if not text or text == f"github.event_name=='{event}'"
            or text not in {f"github.event_name=='{e}'" for e in EVENTS}]


@functools.lru_cache(maxsize=1)
def expected_step_outcomes() -> dict[tuple[str, str], list[str]]:
    """The command steps each receipt must record, by (receipt id, event).

    Read from the receipt steps of the required workflow in
    `tooling/required-steps.json`: the ids in a receipt step's
    `required-outcomes`, for the events the job's and the step's `if` let it
    run in. A receipt step with no `if` in a job with none is for both events.
    This is the list `check-workflows.sh` holds the workflow to, so a receipt
    is checked against the commands the workflow runs and not against what the
    receipt says about itself.
    """
    document = json.loads(REQUIRED_STEPS_FILE.read_text())
    workflow = document["files"][REQUIRED_WORKFLOW]
    table: dict[tuple[str, str], list[str]] = {}
    for job in workflow["jobs"].values():
        for step in job.get("steps", []):
            if step.get("uses") != RECEIPT_ACTION:
                continue
            inputs = step["with"]
            events = [e for e in _events_for(job.get("if")) if e in _events_for(step.get("if"))]
            ids = [item.split("=", 1)[0].strip() for item in inputs["required-outcomes"].split(",")]
            for event in events:
                key = (inputs["id"], event)
                if key in table:
                    raise ValueError(f"receipt {inputs['id']} has two steps for event {event}")
                table[key] = ids
    return table


def check_step_outcomes(check: dict) -> None:
    """Raise unless the receipt records `success` for exactly the command steps
    the workflow runs for it: none missing, none extra, none skipped or failed.

    Applies to a receipt the repository owns (a required check, or `sign-off`)
    that claims to have passed; other receipts have no expected list.
    """
    cid = check["id"]
    expected_table = expected_step_outcomes()
    if cid not in {known for known, _ in expected_table}:
        return
    event = check.get("environment", {}).get("event") if isinstance(check.get("environment"), dict) else None
    expected = expected_table.get((cid, event))
    if expected is None:
        raise ValueError(f"receipt {cid} names event {event!r}, for which the workflow runs no {cid} commands")
    outcomes = check.get("step_outcomes")
    if not isinstance(outcomes, dict) or not outcomes:
        raise ValueError(f"receipt {cid} records no command step outcomes")
    missing = [step for step in expected if step not in outcomes]
    if missing:
        raise ValueError(f"receipt {cid} does not record the command steps: " + ", ".join(missing))
    extra = sorted(set(outcomes) - set(expected))
    if extra:
        raise ValueError(f"receipt {cid} records steps the workflow does not run for {event}: " + ", ".join(extra))
    not_success = [f"{step}={outcomes[step]}" for step in expected if outcomes[step] != "success"]
    if not_success:
        raise ValueError(f"receipt {cid} records command steps that did not succeed: " + ", ".join(not_success))


def validate_receipts(data: Any, commit: str, tree: str) -> list[dict]:
    """Validate the receipt document independently of its supplied labels.

    Required IDs are an owned policy set: a receipt cannot downgrade one by
    changing its classification or applicability.  The returned list is
    canonicalized by ID so callers can compare it with another evidence source.
    """
    if not isinstance(data, dict) or data.get("schema_version") != 1:
        raise ValueError("receipts schema_version must be 1")
    candidate = data.get("candidate")
    if not isinstance(candidate, dict) or candidate.get("commit") != commit or candidate.get("tree") != tree:
        raise ValueError("receipts candidate commit/tree does not match selected source")
    checks = data.get("checks")
    if not isinstance(checks, list):
        raise ValueError("receipts checks must be a list")
    seen: set[str] = set()
    events: set[str] = set()
    run_ids: set[str] = set()
    for check in checks:
        if not isinstance(check, dict):
            raise ValueError("receipt check must be an object")
        for field in ("id", "classification", "applicable", "status", "command", "environment", "run"):
            if field not in check:
                raise ValueError(f"receipt check missing {field}")
        cid = check["id"]
        if not isinstance(cid, str) or not cid or cid in seen:
            raise ValueError(f"duplicate or invalid check id {cid!r}")
        seen.add(cid)
        if check["classification"] not in {"required", "optional", "conditional"}:
            raise ValueError(f"check {cid} has invalid classification")
        if not isinstance(check["applicable"], bool):
            raise ValueError(f"check {cid} applicable must be boolean")
        if check["status"] not in ALLOWED_STATUSES:
            raise ValueError(f"check {cid} has invalid status")
        if not isinstance(check["command"], str) or not check["command"]:
            raise ValueError(f"check {cid} has no command")
        if not isinstance(check["environment"], dict) or not isinstance(check["run"], dict):
            raise ValueError(f"check {cid} environment and run must be objects")
        if cid in REQUIRED_CHECKS:
            if check["applicable"] is not True:
                if check["status"] != "not_applicable":
                    raise ValueError(f"inapplicable check {cid} must be not_applicable")
                raise ValueError(f"required receipt {cid} must be an applicable required check")
            if check["classification"] != "required" or check["applicable"] is not True:
                raise ValueError(f"required receipt {cid} must be an applicable required check")
            if check["status"] != "pass":
                raise ValueError(f"required applicable check {cid} is {check['status']}")
        elif check["applicable"] and check["status"] != "pass":
            raise ValueError(f"applicable non-required check {cid} is {check['status']}")
        elif not check["applicable"] and check["status"] != "not_applicable":
            raise ValueError(f"inapplicable check {cid} must be not_applicable")
        if check["applicable"]:
            # An applicable receipt, required or not, was produced for this
            # candidate, in one event and one workflow run, and records
            # success for the commands the workflow runs for it.
            if check["run"].get("commit") != commit or check["run"].get("tree") != tree:
                raise ValueError(f"receipt {cid} was not produced for the selected candidate")
            check_step_outcomes(check)
            events.add(str(check["environment"].get("event")))
            if "id" in check["run"]:
                run_ids.add(str(check["run"]["id"]))
    if len(events) > 1:
        raise ValueError("receipts come from more than one event: " + ", ".join(sorted(events)))
    if len(run_ids) > 1:
        raise ValueError("receipts come from more than one workflow run: " + ", ".join(sorted(run_ids)))
    missing = REQUIRED_CHECKS - seen
    if missing:
        raise ValueError("missing required check receipts: " + ", ".join(sorted(missing)))
    return sorted(checks, key=lambda item: item["id"])


def compare_checks(left: list[dict], right: list[dict]) -> None:
    """Reject a pack whose manifest and receipts disagree about any check."""
    by_left = {item.get("id"): item for item in left}
    by_right = {item.get("id"): item for item in right}
    if set(by_left) != set(by_right):
        raise ValueError("manifest and receipts contain different check IDs")
    for cid in sorted(by_left):
        if by_left[cid] != by_right[cid]:
            raise ValueError(f"manifest and receipts disagree for check {cid}")
