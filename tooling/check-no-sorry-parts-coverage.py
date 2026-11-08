#!/usr/bin/env python3
"""The parts of `no-sorry.sh` cover its phases once each, and the workflow runs exactly those parts.

`no-sorry.sh` is a list of phases; CI runs it as the parts of `tacenta-proofs/scripts/no-sorry-parts.txt`, one
job of the `translation-part` matrix each, and the `translation` job combines them. Three things must agree,
and this reads all three from the tree (it runs no Lean and no phase):

  * the phases the script lists (`NO_SORRY_LIST=1`, which prints them and runs nothing);
  * the parts of each partition, resolved as a part job resolves them (`no-sorry-parts.py resolve`);
  * the part names the workflow gives its matrix (one list for a push, one for everything else) and the
    partition its combining job names (`NO_SORRY_PARTITION`).

It fails when

  * a phase that is not a prelude is in no part of a partition, or in two, or both whole and sliced; or a
    sliced phase lacks a slice k/S, has one twice, or is sliced two ways. The parts file's own parser refuses
    these too, and its refusal is reported as it is; the count here is made again from what `resolve` prints,
    so a parser that stopped refusing one would still be caught;
  * a part resolves to a phase the script does not list;
  * the workflow's matrix names a part the parts file does not have (it would fail its job at `resolve`, or
    the combiner would find a directory it does not expect), names a part declared with no phase yet, names a
    part twice, or omits a part that has a phase, of the partition it feeds (the combiner would find no
    directory for it, but only after the run);
  * the workflow's partition is not the one its matrix feeds, or the expression that names it, or the matrix
    expression, is not one of the two shapes read here. A shape this does not read is a failure, not a pass.

  * the `translation-part` job could run fewer legs or fewer steps than the matrix list says: the matrix has a key
    other than `part` (`exclude` drops a leg, `include` adds one), the job or a step has `continue-on-error`, the
    job has an `if`, or a step has an `if` other than the four exact conditions the job has today (all of which
    only choose between a push and a pull request). A step of a part job skipped by an `if` would leave the part
    with no directory or an empty one, which the combiner refuses only after the run;
  The commands of a leg's steps are held by `required-steps.json`, not here.

A part declared `-` (no phase yet) is listed as such. It has no job and no directory until it has a phase: the
matrix must not name it (the combiner would refuse a directory it does not expect), and the check refuses a matrix
that names it. When the part is given its first phase, the check refuses the workflow until the part is named in
the matrix, which is how the entry returns.

What it does not do: run the hosted jobs, or say that the combiner refuses a missing or skipped part when it
runs on GitHub. `tooling/tests/run-no-sorry-parts-cases.sh` holds the combiner's refusals on stubbed phases;
`tooling/check-workflows.sh` (rule 8) holds that the combining job starts with the guard on the matrix's
result. `tooling/tests/run-check-no-sorry-parts-coverage-cases.sh` holds this script to its cases.

    python3 tooling/check-no-sorry-parts-coverage.py [--script F] [--parts F] [--workflow F] [--table F] [--reader F]

`--table` reads the phase table from a file instead of asking the script (the cases use it to give the script a
phase it does not have), and `--reader` names the parts reader to resolve with (the cases give it one whose own
coverage refusals are removed, to show that the count made here does not rest on them). The defaults are the
files of the tree.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

try:
    import yaml
except ImportError:  # the checks job installs it; a run that cannot parse the workflow must not pass
    print("::error::check-no-sorry-parts-coverage: PyYAML is not importable, so the workflow cannot be read",
          file=sys.stderr)
    sys.exit(1)

ROOT = Path(__file__).resolve().parent.parent
NAME = r"[a-z][a-z0-9-]*"
# The two shapes the workflow's expressions take. Anything else is refused rather than guessed at.
MATRIX = re.compile(r"\$\{\{ fromJSON\(github\.event_name == 'push' && '(\[[^'\]]*\])' \|\| '(\[[^'\]]*\])'\) \}\}")
PARTITION = re.compile(r"\$\{\{ github\.event_name == 'push' && '(" + NAME + r")' \|\| '(" + NAME + r")' \}\}")
SLICE = re.compile(r"([0-9]+)/([0-9]+)")


class Failed(Exception):
    pass


def fail(message):
    raise Failed(message)


def table_of(script, table_file):
    """[(phase, kind)] in the script's order, from the table the script prints."""
    if table_file:
        text = Path(table_file).read_text()
    else:
        env = {k: v for k, v in os.environ.items() if not k.startswith("NO_SORRY_")}
        env["NO_SORRY_LIST"] = "1"
        run = subprocess.run(["bash", str(script)], capture_output=True, text=True, env=env)
        if run.returncode != 0:
            fail(f"{script} did not list its phases (status {run.returncode}): {run.stderr.strip()[:300]}")
        text = run.stdout
    phases = []
    for line in text.split("\n"):
        fields = line.split("\t")
        if fields[0] == "phase" and len(fields) == 4:
            if fields[1] in [p for p, _ in phases]:
                fail(f"the script lists phase {fields[1]} twice")
            phases.append((fields[1], fields[2]))
    if not phases:
        fail("the script lists no phase")
    return phases, text


def part_names(parts_file):
    """{partition: [part]} in file order, read with the shape of a part's line, not with the parts reader."""
    out = {}
    for line in Path(parts_file).read_text().split("\n"):
        found = re.fullmatch("(" + NAME + ") (" + NAME + "):((?: \\S+)*)", line)
        if found:
            out.setdefault(found.group(1), []).append(found.group(2))
    if not out:
        fail(f"{parts_file} names no part")
    return out


def resolve(reader, table_path, parts_file, part):
    run = subprocess.run([sys.executable, "-I", str(reader), "resolve", "--table", str(table_path),
                          "--parts", str(parts_file), "--part", part], capture_output=True, text=True)
    if run.returncode != 0:
        fail(f"part {part} does not resolve: {run.stderr.strip() or run.stdout.strip()}")
    chosen = []
    for line in run.stdout.split("\n"):
        if line == "":
            continue
        fields = line.split("\t")
        if len(fields) != 2:
            fail(f"part {part}: resolve printed a line that is not `<phase><tab><slice>`: {line!r}")
        chosen.append((fields[0], fields[1]))
    return chosen


def check_cover(partition, parts, chosen, phases):
    """The phases of a partition, each in one part: whole, or every slice k/S of one S once."""
    problems = []
    kinds = dict(phases)
    whole, sliced = {}, {}
    for part in parts:
        for phase, s in chosen[part]:
            if phase not in kinds:
                problems.append(f"partition {partition}: part {part} runs {phase}, which the script does not list")
            elif kinds[phase] == "prelude":
                problems.append(f"partition {partition}: part {part} names {phase}, a prelude phase every part runs")
            elif s == "-" or s == "0/1":
                whole.setdefault(phase, []).append(part)
            else:
                m = SLICE.fullmatch(s)
                if not m:
                    problems.append(f"partition {partition}: part {part}: {phase} has the slice {s!r}")
                else:
                    sliced.setdefault(phase, []).append((part, int(m.group(1)), int(m.group(2))))
    for phase, kind in phases:
        if kind == "prelude":
            continue
        w, sl = whole.get(phase, []), sliced.get(phase, [])
        if not w and not sl:
            problems.append(f"partition {partition}: phase {phase} is in no part")
        if len(w) > 1:
            problems.append(f"partition {partition}: phase {phase} is in parts {', '.join(w)}")
        if w and sl:
            problems.append(f"partition {partition}: phase {phase} is in part {w[0]} and sliced in "
                            f"{', '.join(p for p, _, _ in sl)}")
        if sl:
            counts = sorted({c for _, _, c in sl})
            if len(counts) > 1:
                problems.append(f"partition {partition}: phase {phase} is sliced {' and '.join(map(str, counts))} ways")
            else:
                for k in range(counts[0]):
                    holders = [p for p, kk, _ in sl if kk == k]
                    if not holders:
                        problems.append(f"partition {partition}: slice {k}/{counts[0]} of {phase} is in no part")
                    if len(holders) > 1:
                        problems.append(f"partition {partition}: slice {k}/{counts[0]} of {phase} is in parts "
                                        f"{', '.join(holders)}")
    return problems


def workflow_parts(workflow):
    """(push list, other list, push partition, other partition) from the workflow's two expressions."""
    document = yaml.safe_load(Path(workflow).read_text())
    jobs = document.get("jobs") if isinstance(document, dict) else None
    if not isinstance(jobs, dict) or "translation-part" not in jobs or "translation" not in jobs:
        fail(f"{workflow} lacks the `translation-part` job or the `translation` job")
    try:
        expression = jobs["translation-part"]["strategy"]["matrix"]["part"]
    except (KeyError, TypeError):
        fail("the `translation-part` job has no `strategy.matrix.part`")
    if not isinstance(expression, str) or not MATRIX.fullmatch(expression.strip()):
        fail(f"the matrix's `part` is not `fromJSON(github.event_name == 'push' && '[...]' || '[...]')`: {expression!r}")
    push_list, other_list = (json.loads(x) for x in MATRIX.fullmatch(expression.strip()).groups())
    for name, lst in (("push", push_list), ("other", other_list)):
        if not isinstance(lst, list) or not all(isinstance(x, str) and re.fullmatch(NAME, x) for x in lst):
            fail(f"the matrix's {name} list is not a list of part names: {lst!r}")
    declared = []
    for step in jobs["translation"].get("steps") or []:
        if isinstance(step, dict) and step.get("id") == "translation_no_sorry":
            env = step.get("env")
            declared.append(env.get("NO_SORRY_PARTITION") if isinstance(env, dict) else None)
    if len(declared) != 1 or not isinstance(declared[0], str) or not PARTITION.fullmatch(declared[0].strip()):
        fail("the `translation` job's step translation_no_sorry does not name its partition as "
             f"`github.event_name == 'push' && '<partition>' || '<partition>'`: {declared!r}")
    push_partition, other_partition = PARTITION.fullmatch(declared[0].strip()).groups()
    return push_list, other_list, push_partition, other_partition


# The only step conditions the part job has: they choose between a push and a pull request, or the runner kind.
ALLOWED_STEP_IF = {
    "runner.environment == 'self-hosted'",
    "github.event_name == 'push' && matrix.part == 'all' && steps.mathlib-files.outputs.cache-hit != 'true'",
    "github.event_name == 'pull_request'",
    "github.event_name == 'push' && matrix.part == 'all'",
}


def truthy_continue(value):
    return value is not None and value is not False and str(value).strip().lower() != "false"


def check_part_job(workflow):
    """Problems with the `translation-part` job that let a leg or a step of the matrix not run."""
    job = yaml.safe_load(Path(workflow).read_text())["jobs"]["translation-part"]
    problems = []
    if not isinstance(job, dict):
        return ["the `translation-part` job is not a mapping"]
    if "if" in job:
        problems.append("the `translation-part` job has an `if`, which can skip a leg")
    if truthy_continue(job.get("continue-on-error")):
        problems.append("the `translation-part` job has `continue-on-error`")
    strategy = job.get("strategy")
    matrix = strategy.get("matrix") if isinstance(strategy, dict) else None
    if not isinstance(matrix, dict) or sorted(matrix) != ["part"]:
        problems.append("the matrix of `translation-part` has keys "
                        f"{sorted(matrix) if isinstance(matrix, dict) else matrix!r}, not only `part`: "
                        "an `exclude` drops a leg and an `include` adds one the part list does not name")
    steps = job.get("steps")
    if not isinstance(steps, list) or not steps:
        return problems + ["the `translation-part` job has no steps"]
    for index, step in enumerate(steps):
        if not isinstance(step, dict):
            problems.append(f"step {index + 1} of `translation-part` is not a mapping")
            continue
        label = step.get("id") or step.get("name") or step.get("uses") or f"step {index + 1}"
        if "if" in step and str(step["if"]).strip() not in ALLOWED_STEP_IF:
            problems.append(f"step {label} of `translation-part` has the condition `{step['if']}`, which can skip "
                            "it for a leg; only the push or pull-request conditions the job has are allowed")
        if truthy_continue(step.get("continue-on-error")):
            problems.append(f"step {label} of `translation-part` has `continue-on-error`")
    return problems


def check_workflow(lists, partitions, empty):
    push_list, other_list, push_partition, other_partition = lists
    problems = []
    for event, lst, partition in (("a push", push_list, push_partition),
                                  ("a pull request or any other event", other_list, other_partition)):
        if partition not in partitions:
            problems.append(f"the workflow names partition {partition} for {event}, which the parts file does not have")
            continue
        repeated = sorted({x for x in lst if lst.count(x) > 1})
        if repeated:
            problems.append(f"the workflow's matrix for {event} names {', '.join(repeated)} twice")
        idle = [x for x in lst if x in empty.get(partition, [])]
        if idle:
            problems.append(f"the workflow's matrix for {event} names {', '.join(idle)}, a part of partition "
                            f"{partition} declared with no phase yet: it has no job until it has a phase, and the "
                            f"combiner does not expect its directory")
        extra = [x for x in lst if x not in partitions[partition]]
        if extra:
            problems.append(f"the workflow's matrix for {event} names {', '.join(extra)}, which is not a part of "
                            f"partition {partition} (the parts file has {', '.join(partitions[partition])})")
        missing = [x for x in partitions[partition] if x not in lst and x not in empty.get(partition, [])]
        if missing:
            problems.append(f"the workflow's matrix for {event} does not run {', '.join(missing)}, a part of "
                            f"partition {partition}")
    if push_partition == other_partition:
        problems.append(f"the workflow names partition {push_partition} for a push and for everything else")
    return problems


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--script", default=str(ROOT / "tacenta-proofs/scripts/no-sorry.sh"))
    parser.add_argument("--parts", default=str(ROOT / "tacenta-proofs/scripts/no-sorry-parts.txt"))
    parser.add_argument("--workflow", default=str(ROOT / ".github/workflows/ci.yml"))
    parser.add_argument("--table")
    parser.add_argument("--reader")
    args = parser.parse_args()
    reader = Path(args.reader) if args.reader else Path(args.script).resolve().parent / "no-sorry-parts.py"
    try:
        phases, text = table_of(args.script, args.table)
        partitions = part_names(args.parts)
        problems = []
        summary = []
        empty = {}
        with tempfile.TemporaryDirectory() as scratch:
            table_path = Path(scratch) / "table"
            table_path.write_text(text)
            for partition, parts in partitions.items():
                chosen = {}
                for part in parts:
                    chosen[part] = resolve(reader, table_path, args.parts, part)
                problems += check_cover(partition, parts, chosen, phases)
                empty[partition] = [part for part in parts if not chosen[part]]
                summary.append(f"{partition}: " + ", ".join(
                    f"{part} ({len(chosen[part])})" if chosen[part] else f"{part} (declared empty, no job)"
                    for part in parts))
        problems += check_workflow(workflow_parts(args.workflow), partitions, empty)
        problems += check_part_job(args.workflow)
    except (Failed, OSError, ValueError, yaml.YAMLError) as error:
        print(f"::error::check-no-sorry-parts-coverage: {error}", file=sys.stderr)
        return 1
    if problems:
        for p in problems:
            print(f"::error::check-no-sorry-parts-coverage: {p}", file=sys.stderr)
        print(f"check-no-sorry-parts-coverage: {len(problems)} problem(s)", file=sys.stderr)
        return 1
    non_prelude = len([p for p, k in phases if k != "prelude"])
    print(f"check-no-sorry-parts-coverage: the {non_prelude} phases that are not the prelude are in exactly one part "
          f"of each partition, and the workflow runs exactly those parts")
    for line in summary:
        print(f"  {line}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
