#!/usr/bin/env python3
"""Generate the inventory of the repository's gates and the state of their negative controls.

    python3 tooling/gate-inventory.py --write     rewrite tacenta-proofs/GATE-INVENTORY.md
    python3 tooling/gate-inventory.py --check     fail unless that file is what this generates, and every
                                                  gate that CI runs has a row

Readiness gate 4 asks that every gate has been shown to fail when what it checks is broken, and that none
reports green when it cannot run. Before this file the inventory of which gates have a control, where it
runs and what survived was written by hand in `ASSURANCE-OBLIGATIONS.md` and drifted. This generates it.

Inputs.

  * `tooling/required-steps.json`: the commands of every CI step, in the form `check-workflows.sh` holds
    `.github/workflows/ci.yml` to. A gate or a control is "run in CI" when a CI step names it, directly or
    through a script that a CI step runs (`no-sorry.sh` calls the Session controls, the aggregator
    `tooling/tests/run-gate-controls.sh` calls the controls this change adds). A call is read as an
    interpreter (`bash`, `sh`, `python3`, `source`) followed by the script's path in a line that is not a
    comment, so a script that is only mentioned is not counted, and a call through a variable
    (`bash "$checker"`) is not followed.
  * `tooling/gate-inventory.json`: one row per gate, written by hand: what it protects, the controls that
    hold it, the cheapest control that would hold it when none does.
  * `tooling/gate-mutations.json`: the single edits that `tooling/mutate-gates.py` applies. A row lists the
    mutations whose `file` is the gate's own file.

What the state means.

  control in CI     a control exists, is a file in the tree, and a CI step runs it
  control local only  a control exists and nothing in CI runs it
  none              no control

It does not say that a control fails when it should. That is what `tooling/mutate-gates.py` shows, one edit
at a time, and what the "Mutations" column counts; a gate with a control and no mutation has a control
nobody has seen fail.

`--check` also fails when a step of the required workflow that runs a command is claimed by no row (so a
new gate cannot be added without saying what holds it), when a row names a control or a gate that is not a
file, when a control script does not mention the gate it claims to hold, and when a mutation names a file
that is not in the tree.
"""
import argparse
import json
import os
import re
import subprocess
import sys

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                      check=True).stdout.strip()
OUT = "tacenta-proofs/GATE-INVENTORY.md"
CALL = re.compile(r"""\b(?:bash|sh|python3|python|source|exec)\s+(?:-[A-Za-z]+\s+)*["']?([^\s"'|;&)(]*\.(?:sh|py))\b""")


def load(path):
    with open(os.path.join(ROOT, path), encoding="utf-8") as handle:
        return json.load(handle)


def tracked():
    out = subprocess.run(["git", "ls-files"], cwd=ROOT, capture_output=True, text=True, check=True).stdout
    return set(out.split("\n")) - {""}


def ci_steps(required):
    """[(job, step id or None, command text)] for every step of the required workflow that runs a command."""
    steps = []
    workflow = required["files"][".github/workflows/ci.yml"]
    for job, body in workflow["jobs"].items():
        for step in body.get("steps", []):
            if "run" in step:
                steps.append((job, step.get("id"), step["run"]))
    return steps


def script_text(path):
    """The code of a script with its full-line comments removed, so a comment that names another script is
    not a call of it."""
    try:
        with open(os.path.join(ROOT, path), encoding="utf-8", errors="replace") as handle:
            lines = handle.read().split("\n")
    except OSError:
        return ""
    return "\n".join(line for line in lines if not line.lstrip().startswith("#"))


def resolve(mention, files):
    """The tracked files a script path in a command can mean. A path in a command is relative to a
    directory the command does not say, so the longest suffix match wins and a tie is every candidate."""
    mention = re.sub(r"^(?:\.\./|\./)+", "", mention)
    mention = re.sub(r"^\$\{?\w+\}?/", "", mention)
    return sorted(f for f in files if f == mention or f.endswith("/" + mention))


def reachability(steps, files):
    """{file: first step that runs it, directly or through a script} by a walk from every CI step."""
    reach = {}
    queue = []
    for job, ident, command in steps:
        label = ident or f"{job} (unnamed step)"
        for mention in CALL.findall(command):
            for path in resolve(mention, files):
                if path not in reach:
                    reach[path] = (label, None)
                    queue.append(path)
    while queue:
        path = queue.pop(0)
        for mention in CALL.findall(script_text(path)):
            for target in resolve(mention, files):
                if target not in reach:
                    reach[target] = (reach[path][0], path)
                    queue.append(target)
    return reach


def control_entry(control):
    return {"path": control} if isinstance(control, str) else dict(control)


def build(rows, mutations, steps, files, reach):
    problems = []
    by_file = {}
    for mutation in mutations:
        if mutation["file"] not in files:
            problems.append(f"mutation {mutation['id']} names {mutation['file']}, which is not in the tree")
        by_file.setdefault(mutation["file"], []).append(mutation["id"])
    table = []
    claimed_ids = set()
    row_files = set()
    for number, row in enumerate(rows, 1):
        gate = row["gate"]
        is_path = gate.endswith((".sh", ".py"))
        if is_path and gate not in files:
            problems.append(f"row {number}: gate {gate} is not in the tree")
        if is_path:
            row_files.add(gate)
        if is_path and gate in reach:
            via = reach[gate]
            run = via[0] + (f" (through {os.path.basename(via[1])})" if via[1] else "")
        else:
            run = ", ".join(row.get("ci_steps", [])) or "no CI step"
        claimed_ids.update(row.get("ci_steps", []))
        controls = []
        in_ci = False
        for raw in row.get("controls", []):
            control = control_entry(raw)
            path = control["path"]
            if path not in files:
                problems.append(f"row {number} ({gate}): control {path} is not in the tree")
                continue
            row_files.add(path)
            if is_path and not control.get("indirect") and path.endswith((".sh", ".py")):
                with open(os.path.join(ROOT, path), encoding="utf-8", errors="replace") as handle:
                    text = handle.read()
                if os.path.basename(gate) not in text:
                    problems.append(f"row {number} ({gate}): control {path} does not mention the gate")
            if "ci_steps" in control:
                where = "CI" if control["ci_steps"] else "local"
                note = ", ".join(control["ci_steps"])
                runs = bool(control["ci_steps"])
                claimed_ids.update(control["ci_steps"])
            elif control.get("ci") is False:
                # A hand-set flag may say a control is local only when nothing runs it, but it may not contradict
                # the reachability this file computes.
                if path in reach:
                    problems.append(f"row {number} ({gate}): control {path} is marked local but CI step "
                                    f"{reach[path][0]} runs it")
                where, note, runs = "local", "", False
            elif path in reach:
                where, runs = "CI", True
                note = reach[path][0] + (f" through {os.path.basename(reach[path][1])}" if reach[path][1] else "")
            else:
                where, note, runs = "local", "", False
            in_ci = in_ci or runs
            controls.append((path, where, note, control.get("note", "")))
        if not controls:
            state = "none"
        elif in_ci:
            state = "control in CI"
        else:
            state = "control local only"
        table.append({"number": number, "row": row, "gate": gate, "run": run, "controls": controls,
                      "state": state,
                      "mutations": sorted(i for f in row.get("mutation_files", [gate]) for i in by_file.get(f, []))})
    # Every step that runs a command must be claimed: listed by a row, or running a file a row names.
    # A step without an id is claimed only by the scripts it runs, and every script it runs must have a row: one
    # listed script beside an unlisted one does not claim the step.
    unnamed = {}
    for job, ident, command in steps:
        if ident in claimed_ids:
            continue
        paths = {p for m in CALL.findall(command) for p in resolve(m, files)}
        if paths and paths <= row_files:
            continue
        if ident is None:
            unnamed[job] = unnamed.get(job, 0) + 1
        label = ident or f"{job} (unnamed step {unnamed[job]})"
        problems.append(f"CI step {label} (`{command.strip().splitlines()[0][:60]}`) is claimed by no row"
                        + ("" if not paths else f"; no row names {', '.join(sorted(paths - row_files))}" if paths - row_files else ""))
    return table, problems


def render(table, counts):
    out = [
        "# Gate inventory",
        "",
        "Generated by `python3 tooling/gate-inventory.py --write`; do not edit. `--check` fails when this file",
        "is not what the generator produces from `tooling/gate-inventory.json`, `tooling/required-steps.json`",
        "and `tooling/gate-mutations.json`, or when a step the CI workflow runs has no row. It is evidence",
        "for readiness gate 4 in [`ASSURANCE.md`](../ASSURANCE.md), and it is an inventory, not a verdict:",
        "",
        "- State **control in CI**: a control is in the tree and a CI step runs it, directly or through a script.",
        "- State **control local only**: a control is in the tree and no CI step runs it.",
        "- State **none**: no control.",
        "- A control that exists has not been shown to fail unless the **Mutations** column lists single edits",
        "  to the gate that `tooling/mutate-gates.py` applies and requires the control to catch.",
        "",
        f"{counts['rows']} rows: {counts['control in CI']} with a control in CI, "
        f"{counts['control local only']} with a control that runs only locally, {counts['none']} with none. "
        f"{counts['mutated']} rows carry at least one re-runnable mutation ({counts['mutations']} edits).",
        "",
        "| # | Gate | Kind | Runs in CI | Controls | State | Mutations | What would hold it, if nothing does |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for item in table:
        row = item["row"]
        controls = "<br>".join(
            f"`{path}` ({where}{', ' + steps if steps else ''})" for path, where, steps, _ in item["controls"]
        ) or "none"
        mutations = ", ".join(item["mutations"]) if item["mutations"] else "none"
        cheapest = row.get("cheapest", "") if item["state"] != "control in CI" or not item["mutations"] else ""
        if item["state"] == "control in CI" and not item["mutations"] and not cheapest:
            cheapest = row.get("cheapest", "")
        gate = f"`{item['gate']}`" if item["gate"].endswith((".sh", ".py")) else item["gate"]
        out.append(
            f"| {item['number']} | {gate}: {row['what']} | {row['kind']} | {item['run']} | {controls} | "
            f"{item['state']} | {mutations} | {cheapest} |")
    out.append("")
    return "\n".join(out).replace("|  |", "| |")


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()

    files = tracked()
    rows = load("tooling/gate-inventory.json")["rows"]
    mutations = load("tooling/gate-mutations.json")["mutations"]
    steps = ci_steps(load("tooling/required-steps.json"))
    reach = reachability(steps, files)
    table, problems = build(rows, mutations, steps, files, reach)
    counts = {"rows": len(table), "control in CI": 0, "control local only": 0, "none": 0,
              "mutated": sum(1 for t in table if t["mutations"]),
              "mutations": len({i for t in table for i in t["mutations"]})}
    for item in table:
        counts[item["state"]] += 1
    text = render(table, counts)

    if problems:
        for problem in problems:
            print(f"gate-inventory: {problem}", file=sys.stderr)
        return 1
    path = os.path.join(ROOT, OUT)
    if args.write:
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(text)
        print(f"gate-inventory: wrote {OUT} ({counts['rows']} rows)")
        return 0
    try:
        current = open(path, encoding="utf-8").read()
    except OSError:
        current = None
    if current != text:
        print(f"gate-inventory: {OUT} is not what the generator produces; run "
              f"`python3 tooling/gate-inventory.py --write` and read the difference", file=sys.stderr)
        return 1
    print(f"gate-inventory: {OUT} is current ({counts['rows']} rows)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
