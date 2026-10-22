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
check, `check_complete` and the rest named in SHARED); this gate also requires each named helper to be bound exactly
once in each script, at the top level, by its own `def` or assignment, and to be the same text, character for
character and from its first decorator, in all of them, so a fix made to one copy cannot leave another behind.  Any
other binding of a shared name is refused, at any depth: an annotated or augmented assignment, a `global`, an
import, a loop, `with` or `except` target, a parameter, a walrus, a `del`; so is any use of `globals`, `setattr`,
`exec`, `eval`, `__dict__`, `sys.modules`, `importlib` or `__import__`, through which a name can be rebound without
naming it.

The counts hold what the script contains, not what it runs, so `main` is read too: it must call the shared
`check_complete(results, sources)` as a statement of its own body (not inside an `if`, a loop, a `try` or a `with`),
hold no `return` and call no `exit`, and the script must end its run with exactly `sys.exit(main())`.
`check_complete` refuses, at the end of a real run, a run that refused fewer controls than `MUTANTS` holds (a slice
or a `continue`), accepted other baselines than `sources`, or skipped an emptied-proof run.

What it cannot see: whether a control is a good one, or that the record's counts are the right ones (an edit of a
script and of the record together is accepted, and only the diff shows it); whether the `results` that `main` passes
to `check_complete` are what Lean said (a `main` that fabricates them is read by review); it reads the scripts by
importing them, which runs their top-level definitions and nothing else (`main` is not called).
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
          "pin_line", "gutted", "check_inside", "check_refused", "check_complete",
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


# Names through which a script could rebind a shared helper without a binding this gate reads.
DYNAMIC = ("globals", "setattr", "exec", "eval", "__dict__", "modules", "importlib", "__import__", "vars", "locals")


def targets(node):
    """The names a binding target binds (a name, or the names inside a tuple, list or starred target)."""
    if isinstance(node, ast.Name):
        return [node.id]
    if isinstance(node, (ast.Tuple, ast.List)):
        return [n for e in node.elts for n in targets(e)]
    if isinstance(node, ast.Starred):
        return targets(node.value)
    return []


def bindings(source):
    """Every binding of a name in `source`, at any depth, as (name, kind, top level, text): a `def` or `class`
    (its text from its first decorator), a plain assignment (its text), and every other kind with no text."""
    tree = ast.parse(source)
    lines = source.split("\n")
    top = set(map(id, tree.body))
    out = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            first = min([d.lineno for d in node.decorator_list] + [node.lineno])
            text = "\n".join(lines[first - 1:node.end_lineno])
            out.append((node.name, "def", id(node) in top and not isinstance(node, ast.AsyncFunctionDef), text))
            args = node.args if not isinstance(node, ast.ClassDef) else None
            if args is not None:
                for a in args.posonlyargs + args.args + args.kwonlyargs + [args.vararg, args.kwarg]:
                    if a is not None:
                        out.append((a.arg, "parameter", False, None))
        elif isinstance(node, ast.Lambda):
            for a in node.args.posonlyargs + node.args.args + node.args.kwonlyargs:
                out.append((a.arg, "parameter", False, None))
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                plain = isinstance(target, ast.Name) and len(node.targets) == 1
                for name in targets(target):
                    out.append((name, "assign" if plain else "unpacking", id(node) in top and plain,
                                ast.get_source_segment(source, node)))
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign, ast.NamedExpr)):
            out += [(n, type(node).__name__, False, None) for n in targets(node.target)]
        elif isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension)):
            out += [(n, "loop target", False, None) for n in targets(node.target)]
        elif isinstance(node, (ast.With, ast.AsyncWith)):
            out += [(n, "with target", False, None) for item in node.items if item.optional_vars is not None
                    for n in targets(item.optional_vars)]
        elif isinstance(node, ast.ExceptHandler) and node.name:
            out.append((node.name, "except target", False, None))
        elif isinstance(node, (ast.Global, ast.Nonlocal)):
            out += [(n, type(node).__name__.lower(), False, None) for n in node.names]
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            out += [(a.asname or a.name.split(".")[0], "import", False, None) for a in node.names]
        elif isinstance(node, ast.Delete):
            out += [(n, "del", False, None) for target in node.targets for n in targets(target)]
    return out


def dynamic_uses(source):
    """The names in DYNAMIC that `source` uses, as a name or an attribute."""
    found = set()
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, ast.Name) and node.id in DYNAMIC:
            found.add(node.id)
        elif isinstance(node, ast.Attribute) and node.attr in DYNAMIC:
            found.add(node.attr)
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            found |= {a.name.split(".")[0] for a in node.names if a.name.split(".")[0] in DYNAMIC}
            if isinstance(node, ast.ImportFrom) and (node.module or "").split(".")[0] in DYNAMIC:
                found.add(node.module.split(".")[0])
    return found


def main_problems(name, source):
    """What `main` and the end of the script must hold so that the run is the one the counts describe."""
    tree = ast.parse(source)
    problems = []
    mains = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == "main"]
    if len(mains) != 1:
        return [f"{name} has {len(mains)} top-level `main`, not one"]
    main = mains[0]
    calls = [s for s in main.body if isinstance(s, ast.Expr) and isinstance(s.value, ast.Call)
             and isinstance(s.value.func, ast.Name) and s.value.func.id == "check_complete"
             and [ast.unparse(a) for a in s.value.args] == ["results", "sources"] and not s.value.keywords]
    every = [n for n in ast.walk(main) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
             and n.func.id == "check_complete"]
    if len(calls) != 1 or len(every) != 1:
        problems.append(f"{name}: `main` must call `check_complete(results, sources)` exactly once, as a statement "
                        "of its own body, so that a run that skipped a control fails")
    if any(isinstance(n, ast.Return) for n in ast.walk(main)):
        problems.append(f"{name}: `main` holds a `return`, which can end the run before `check_complete`")
    if any(isinstance(n, ast.Call) and ((isinstance(n.func, ast.Name) and n.func.id in ("exit", "quit"))
                                        or (isinstance(n.func, ast.Attribute) and n.func.attr in ("exit", "_exit")))
           for n in ast.walk(main)):
        problems.append(f"{name}: `main` calls an exit, which can end the run before `check_complete`")
    ends = [n for n in tree.body if isinstance(n, ast.If) and "__main__" in ast.unparse(n.test)]
    if len(ends) != 1 or ast.unparse(ends[0]) != "if __name__ == '__main__':\n    sys.exit(main())":
        problems.append(f"{name}: the script must end its run with exactly `sys.exit(main())` under "
                        "`if __name__ == '__main__':`")
    return problems


def carries_label_check(source):
    """Whether a script defines, binds, imports or reads `check_labels` (any binding or attribute of that name)."""
    tree = ast.parse(source)
    return any(n == "check_labels" for n, _, _, _ in bindings(source)) or any(
        isinstance(node, ast.Attribute) and node.attr == "check_labels" for node in ast.walk(tree))


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
    present = []
    for p in sorted(HERE.glob("*.py")):
        if p.name == Path(__file__).name:
            continue
        try:
            if carries_label_check(p.read_text()):
                present.append(p.name)
        except SyntaxError as error:
            problems.append(f"{p.name} does not parse ({error.msg}), so whether it carries check_labels is unknown")
    problems += [f"{n} carries the shared check_labels and is not in {RECORD.name}"
                 for n in present if n not in scripts]
    problems += [f"{RECORD.name} lists {n}, which is not a script here carrying check_labels"
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
    for name, text in sorted(texts.items()):
        problems += main_problems(name, text)
        used = dynamic_uses(text)
        if used:
            problems.append(f"{name} uses {', '.join(sorted(used))}, through which a shared helper can be rebound "
                            "without a binding this gate reads")
    if texts:
        shared = {name: [b for b in bindings(text) if b[0] in SHARED] for name, text in texts.items()}
        for helper in SHARED:
            copies = {}
            for name in sorted(shared):
                found = [b for b in shared[name] if b[0] == helper]
                proper = [b for b in found if b[2] and b[1] in ("def", "assign")]
                if len(found) != 1 or len(proper) != 1:
                    kinds = ", ".join(sorted(b[1] + ("" if b[2] else " (not at the top level)") for b in found))
                    problems.append(f"{name} binds the shared {helper} {len(found)} time(s) ({kinds or 'none'}); "
                                    "it must be bound once, at the top level, by its own def or assignment")
                else:
                    copies[name] = proper[0][3]
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
