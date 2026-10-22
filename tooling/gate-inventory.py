#!/usr/bin/env python3
"""Generate the inventory of the repository's gates and the state of their negative controls.

    python3 tooling/gate-inventory.py --write     rewrite tacenta-proofs/GATE-INVENTORY.md
    python3 tooling/gate-inventory.py --check     fail unless that file is what this generates, and every
                                                  gate that CI runs has a row
    python3 tooling/gate-inventory.py --print [--steps FILE]   print what it generates (from FILE's CI steps)

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
file, when a control script does not mention the gate it claims to hold, when a mutation names a file
that is not in the tree or that no row holds (its gate or one of its `mutation_files`), and when a row or a
control names a CI step (`ci_steps`) that the workflow does not have, or names one for a control whose command does not run that control. A control is named with its step
when the step that reaches it textually is not the one that gives its verdict: `check-attest-negatives.sh`
runs in the slices (`negatives_slice`), and only the combining step (`negatives_combine`) says whether they
hold the gate. For a control that is a shell script (`.sh`), the named step must also run it: its `run` text
calls the control's path (an interpreter followed by the path), or calls a script whose text does, and so on,
the walk this file makes everywhere. A step that names the script without running it, or runs it through a
variable, does not count, so a step repointed at another command fails. A Rust test file or a Python module
is compiled into a test binary or imported, which the walk cannot see, so for those `ci_steps` stays a claim
that only the step's existence backs. A row's own `ci_steps` are held the same way: for a gate that is a script,
each named step must run it.

Split runs. A step that runs a script in a mode that only reads what other jobs wrote is listed under
`combining_steps`, with the files it really runs: the combining job of the attestation negatives runs
`check-attest-negatives.sh` to read the slices, and the `translation` job runs `no-sorry.sh` to read the parts,
neither running a case or a phase. The walk takes such a step to run only those files (each must be reached by
its command), and a gate is shown at the step that runs it, the part or the slice, with the step that gives the
verdict on the split run named in the row's `verdict_steps`. Where several steps run a file, a step that is not
combining wins, then the most direct, then the first by name, so the inventory does not depend on the order of
the jobs in the workflow.
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


def walk(command, files):
    """{file: (depth, the script that calls it or None)} for what one CI command runs, directly or through the
    scripts it runs. A call is followed by its text, so the walk is the same whatever order the steps come in."""
    found = {}
    frontier = []
    for mention in CALL.findall(command):
        for path in resolve(mention, files):
            if path not in found:
                found[path] = (0, None)
                frontier.append(path)
    depth = 0
    while frontier:
        depth += 1
        following = []
        for path in sorted(frontier):
            for mention in CALL.findall(script_text(path)):
                for target in resolve(mention, files):
                    if target not in found:
                        found[target] = (depth, path)
                        following.append(target)
        frontier = following
    return found


def step_walk(ident, command, files, combining):
    """What one step runs. A combining step (`combining_steps` in tooling/gate-inventory.json) runs a script in
    a mode that reads the outputs of other jobs, so it runs only the files it lists, which must be among the
    files its command reaches, and nothing those files call in their other modes."""
    if ident in combining:
        return {path: (0, None) for path in combining[ident]["runs"]}
    return walk(command, files)


def step_reach(command, files, ident=None, combining=None):
    """The tracked files one CI command runs, directly or through the scripts it runs."""
    return set(step_walk(ident, command, files, combining or {}))


def reachability(steps, files, combining):
    """{file: (step, the script that calls it or None)} over every CI step. Where several steps run a file, the
    step that is not a combining step wins, then the one that runs it most directly, then the first by name:
    the choice does not depend on the order of the jobs or steps in the workflow."""
    best = {}
    for job, ident, command in steps:
        label = ident or f"{job} (unnamed step)"
        for path, (depth, via) in step_walk(ident, command, files, combining).items():
            key = (ident in combining, depth, label, via or "")
            if path not in best or key < best[path][0]:
                best[path] = (key, (label, via))
    return {path: value for path, (_, value) in best.items()}


def control_entry(control):
    return {"path": control} if isinstance(control, str) else dict(control)


def build(rows, mutations, steps, files, reach, combining):
    problems = []
    by_file = {}
    for mutation in mutations:
        if mutation["file"] not in files:
            problems.append(f"mutation {mutation['id']} names {mutation['file']}, which is not in the tree")
        by_file.setdefault(mutation["file"], []).append(mutation["id"])
    table = []
    claimed_ids = set()
    row_files = set()
    step_ids = {ident for _, ident, _ in steps if ident}
    step_commands = {ident: command for _, ident, command in steps if ident}
    for ident, entry in sorted(combining.items()):
        if ident not in step_ids:
            problems.append(f"combining step {ident} is not a step of the workflow")
            continue
        runs = entry.get("runs") if isinstance(entry, dict) else None
        if not isinstance(runs, list) or not runs or not isinstance(entry.get("why"), str):
            problems.append(f"combining step {ident} does not list the files it runs and why")
            continue
        reached = walk(step_commands[ident], files)
        for path in runs:
            if path not in reached:
                problems.append(f"combining step {ident} lists {path}, which its command does not run")
        claimed_ids.add(ident)
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
        for ident in row.get("ci_steps", []):
            if ident not in step_ids:
                problems.append(f"row {number} ({gate}) names CI step {ident}, which the workflow does not have")
            elif is_path and gate not in step_reach(step_commands[ident], files, ident, combining):
                # A row's step runs its gate, directly or through a script; a step that only gives the verdict
                # on a split run is named in `verdict_steps` instead.
                problems.append(f"row {number} ({gate}) names CI step {ident}, whose command does not run it")
        verdict = row.get("verdict_steps", [])
        claimed_ids.update(verdict)
        for ident in verdict:
            if ident not in step_ids:
                problems.append(f"row {number} ({gate}) names verdict step {ident}, which the workflow does not have")
        if verdict:
            run += "; verdict " + ", ".join(verdict)
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
                # A control's named step is the one that gives its verdict. It must exist, and for a shell
                # script its command must run the control, directly or through a script it runs (the walk
                # `reachability` makes, from that one step), so a step repointed at another command fails too.
                for ident in control["ci_steps"]:
                    if ident not in step_ids:
                        problems.append(f"row {number} ({gate}): control {path} names CI step {ident}, "
                                        "which the workflow does not have")
                    elif path.endswith(".sh") and path not in step_reach(step_commands[ident], files, ident,
                                                                         combining):
                        problems.append(f"row {number} ({gate}): control {path} names CI step {ident}, "
                                        "whose command does not run it")
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
    # Every mutation must edit a file a row holds (its gate, or one of its `mutation_files`): a mutation of a
    # file no row holds is counted nowhere, as when a merge drops the rows of the tools it added.
    held = {f for row in rows for f in row.get("mutation_files", [row["gate"]])}
    for mutation in mutations:
        if mutation["file"] not in held:
            problems.append(f"mutation {mutation['id']} edits {mutation['file']}, which no inventory row holds "
                            "(give the file a row, or name it in a row's mutation_files)")
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
    # Print what the generator makes, from another copy of the steps if given, and write or compare nothing: its
    # cases use it to show that the inventory does not depend on the order of the workflow's jobs.
    group.add_argument("--print", action="store_true")
    parser.add_argument("--steps", metavar="FILE", help="with --print: read the CI steps from FILE")
    args = parser.parse_args()
    if args.steps and not args.print:
        parser.error("--steps is for --print only")

    files = tracked()
    inventory = load("tooling/gate-inventory.json")
    rows = inventory["rows"]
    combining = inventory.get("combining_steps", {})
    mutations = load("tooling/gate-mutations.json")["mutations"]
    if args.steps:
        with open(args.steps, encoding="utf-8") as handle:
            steps = ci_steps(json.load(handle))
    else:
        steps = ci_steps(load("tooling/required-steps.json"))
    reach = reachability(steps, files, combining)
    table, problems = build(rows, mutations, steps, files, reach, combining)
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
    if args.print:
        sys.stdout.write(text)
        return 0
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
