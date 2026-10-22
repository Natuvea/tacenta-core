#!/usr/bin/env python3
"""Hold the number of controls in the lifecycle negatives scripts to a record, and their shared helpers to one text.

Five negatives scripts (`check-responder-successor-negatives.py`, `check-responder-reply-negatives.py`,
`check-responder-reply-receipt-negatives.py`, `check-send-preservation-negatives.py`,
`check-initiator-second-send-negatives.py`) each plant changes in a copy of a module and require Lean to refuse
every one at a named place.  At start-up each checks that its labels (`INSIDE`, `PROJECTION`, `STATEMENT_SHAPE`)
name controls it has and agree with where those are refused; nothing there says how many controls it should have,
so a control deleted together with its label (its `MUTANTS` entry and its `INSIDE` line) leaves a smaller script
that starts and passes.  This gate compares, for each script, the number of its controls in each class with
`negatives-control-counts.json`:

  inside           controls labelled inside a composing proof (`INSIDE`)
  projection       controls labelled projections of a called theorem's conjunct (`PROJECTION`)
  statement_shape  statement-shape checks (`STATEMENT_SHAPE`)
  pin              controls refused at a pin (`MUTANTS` entries whose place is `('pin', name)`)
  leaf             every other control (refused in a leaf lemma)
  baselines        the unmodified copies the script requires Lean to accept first (the keys of `sources` in `main`)

A count the script and the record disagree on is refused, naming the script and the class, so removing, adding or
relabelling a control fails here unless the record is edited in the same change, where the diff of the record shows
it.  The record must list exactly the negatives scripts of this directory that define the shared `check_labels`, so
a sixth such script is not left out.

The scripts keep their own copies of the shared helpers (`check_labels`, `passed_through`, the guard, the refusal
check and the rest named in SHARED); this gate also requires each named helper to be the same text, character for
character, in all of them, so a fix made to one copy cannot leave another behind.

What it cannot see: whether a control is a good one, or that the record's counts are the right ones (an edit of a
script and of the record together is accepted, and only the diff shows it); it reads the scripts by importing them,
which runs their top-level definitions and nothing else (`main` is not called).
"""
import ast
import importlib.util
import json
import sys
from collections import Counter
from pathlib import Path

# Importing a script must leave nothing behind in the tree.
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
RECORD = HERE / "negatives-control-counts.json"
CLASSES = ("inside", "projection", "statement_shape", "pin", "leaf", "baselines")
# The helpers every lifecycle negatives script carries a copy of, which must be the same text in each.
SHARED = ("mentions", "binding", "called_theorem", "passed_through", "check_labels", "guard_self_test",
          "not_a_refusal", "error_blocks", "is_timeout", "run_lean", "without_pins", "declaration_lines",
          "pin_line", "gutted", "check_inside", "check_refused",
          "BINDER", "PLACING", "NOT_A_REFUSAL", "TIMEOUT", "ERROR_HEAD", "MESSAGE", "DECL", "COMMAND", "ERROR_AT")


def refuse(problems):
    for p in problems:
        print(f"check-negatives-control-counts: {p}", file=sys.stderr)
    return 1


def load(path):
    spec = importlib.util.spec_from_file_location(path.stem.replace("-", "_"), path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def top_level(source):
    """Each top-level function and assignment of `source`, by name, as its source text."""
    tree = ast.parse(source)
    found = {}
    for node in tree.body:
        if isinstance(node, ast.FunctionDef):
            found.setdefault(node.name, []).append(ast.get_source_segment(source, node))
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    found.setdefault(target.id, []).append(ast.get_source_segment(source, node))
    return found


def baselines(source):
    """The number of keys of the `sources = {...}` dictionary in `main`, or None when there is not exactly one."""
    tree = ast.parse(source)
    main = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == "main"]
    if len(main) != 1:
        return None
    dicts = [n.value for n in ast.walk(main[0]) if isinstance(n, ast.Assign) and isinstance(n.value, ast.Dict)
             and any(isinstance(t, ast.Name) and t.id == "sources" for t in n.targets)]
    return len(dicts[0].keys) if len(dicts) == 1 else None


def counts(path):
    source = path.read_text()
    module = load(path)
    names = [m[1] for m in module.MUTANTS]
    pinned = {m[1] for m in module.MUTANTS if isinstance(m[4], tuple)}
    labelled = {"inside": module.INSIDE, "projection": module.PROJECTION, "statement_shape": module.STATEMENT_SHAPE}
    got = {k: sum(1 for n in names if n in v) for k, v in labelled.items()}
    got["pin"] = sum(1 for n in names if n in pinned)
    got["leaf"] = sum(1 for n in names if n not in pinned and not any(n in v for v in labelled.values()))
    got["baselines"] = baselines(source)
    return got, source


def main():
    if len(sys.argv) > 1:
        print("usage: check-negatives-control-counts.py", file=sys.stderr)
        return 2
    try:
        record = json.loads(RECORD.read_text())
        scripts = record["scripts"]
        if not isinstance(scripts, dict) or not scripts:
            raise ValueError("no scripts")
    except (OSError, ValueError, KeyError, TypeError) as error:
        return refuse([f"{RECORD.name} cannot be read as a record of scripts ({type(error).__name__}: {error})"])
    problems = []
    present = sorted(p.name for p in HERE.glob("check-*-negatives.py")
                     if "\ndef check_labels(" in p.read_text())
    problems += [f"{n} defines the shared check_labels and is not in {RECORD.name}"
                 for n in present if n not in scripts]
    problems += [f"{RECORD.name} lists {n}, which is not a negatives script here defining check_labels"
                 for n in sorted(scripts) if n not in present]
    texts = {}
    for name in sorted(set(scripts) & set(present)):
        want = scripts[name]
        if not isinstance(want, dict) or set(want) != set(CLASSES) \
                or not all(isinstance(want.get(c), int) and not isinstance(want.get(c), bool) for c in CLASSES):
            problems.append(f"{RECORD.name}: the entry of {name} must give exactly the integer counts "
                            f"{', '.join(CLASSES)}")
            continue
        got, texts[name] = counts(HERE / name)
        for c in CLASSES:
            if got[c] is None:
                problems.append(f"{name}: its `sources` dictionary in `main` cannot be read, so its baselines "
                                "cannot be counted")
            elif got[c] != want[c]:
                problems.append(f"{name} has {got[c]} {c} control(s) and {RECORD.name} records {want[c]}: a control "
                                f"was removed, added or relabelled without editing the record in the same change")
    if texts:
        shared = {name: top_level(text) for name, text in texts.items()}
        for helper in SHARED:
            copies = {}
            for name in sorted(shared):
                found = shared[name].get(helper, [])
                if len(found) != 1:
                    problems.append(f"{name} defines the shared {helper} {len(found)} times, not once")
                else:
                    copies[name] = found[0]
            # The text most copies have is the reference; each copy that differs from it is named.
            common = Counter(copies.values()).most_common()
            if len(common) > 1:
                problems += [f"{name}'s copy of the shared {helper} differs from the copy in {common[0][1]} of the "
                             "other scripts: the copies must be the same text"
                             for name in sorted(copies) if copies[name] != common[0][0]]
    if problems:
        return refuse(problems)
    total = sum(sum(v for k, v in scripts[n].items()) - scripts[n]["baselines"] for n in scripts)
    print(f"check-negatives-control-counts: {len(scripts)} scripts match {RECORD.name} ({total} controls), and "
          f"their {len(SHARED)} shared helpers are the same text")
    return 0


if __name__ == "__main__":
    sys.exit(main())
