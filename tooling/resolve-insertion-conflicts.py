#!/usr/bin/env python3
"""Resolve the merge conflicts in the shared wiring files that are two insertions at one place, and nothing else.

    python3 tooling/resolve-insertion-conflicts.py [--check]
    python3 tooling/resolve-insertion-conflicts.py --verify

When two branches each add a proof module, both insert lines into the same lists. Where their names sort to
different places the insertions are at different lines and git merges them; where both sort after the same
existing entry, git reports a conflict whose base side is empty: each side only added lines there. For the files
below, the merge of such a conflict is both insertions, this side's first, and that is what this writes.

It reads the three versions git keeps for an unmerged file (base, this side, the other side) and merges them again
with `git merge-file --diff3`, whatever `merge.conflictStyle` says. It resolves a conflict only when its base is
empty, and then:

  - when one side's lines are the start or the end of the other's and the shorter holds an entry (a branch built
    on another that was squash-merged first holds the other's lines too), it keeps the longer; a shorter side of
    punctuation alone, such as a closing `fi`, is refused rather than taken as held;
  - otherwise it keeps both, this side's first, when each side inserts entries and they share none.

An entry is a line that may appear once: in a shell file a line that is not a comment, in attest.py a quoted name,
in the JSON files any line, in a Markdown or Lean file a line led by a backticked name (a script of a list, the
evidence of one, the scaffold's clause, an audit paragraph) or an import, keyed by that name. In a Markdown or Lean
file it also refuses a conflict whose two sides hold an entry with the same key and different text (one entry
edited, not two inserted) and one whose two sides both hold prose (a line that is not an entry, which may be one
line edited on one side). And it refuses when an entry it adds appears anywhere else in the result, verbatim or,
in those files, under the same key. The verdict is for the whole run: if any file cannot be resolved, nothing is
written, the file and its line are named, and it exits 1. A resolved file is staged. (`--zdiff3` is not used: it
takes a common last line such as a closing brace out of two different insertions and leaves one without it.)

    tacenta-proofs/translation/Translation/AxiomAuditSessionUnit.lean, tacenta-proofs/scripts/no-sorry.sh,
    tacenta-proofs/scripts/no-sorry-parts.txt, tacenta-proofs/scripts/attest.py,
    tacenta-proofs/scripts/check-attest-negatives.sh, tooling/tests/run-proof-script-cases.sh,
    tooling/tests/run-no-sorry-parts-cases.sh, tacenta-proofs/scripts/negatives-control-counts.json,
    tooling/gate-inventory.json, tooling/gate-mutations.json, ASSURANCE-OBLIGATIONS.md

`--check` resolves nothing and says what it would do. `--verify` merges nothing: it checks the tree as it is, which
`tooling/regenerate-generated.sh` runs after its generators: the JSON files load, attest.py parses, the shell
files pass `bash -n`, every part of `no-sorry-parts.txt` resolves against the phases `no-sorry.sh` lists, and no
entry of the lists a new module adds to appears twice (an audit import or paragraph, a phase function, `run_phase`
id or control call, a part's phase, a stubbed or called control, an inventory row or one of its controls, a mutation
id, a name of one of attest.py's four lists, a line of the attestation negatives' deletion lists, and in every field of
every list item of the obligations file, an entry led by a backticked name). What it does not do: decide that two insertions belong together; the diff
is still read.
"""
import argparse
import ast
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

FILES = [
    "tacenta-proofs/translation/Translation/AxiomAuditSessionUnit.lean",
    "tacenta-proofs/scripts/no-sorry.sh",
    "tacenta-proofs/scripts/no-sorry-parts.txt",
    "tacenta-proofs/scripts/attest.py",
    "tacenta-proofs/scripts/check-attest-negatives.sh",
    "tooling/tests/run-proof-script-cases.sh",
    "tooling/tests/run-no-sorry-parts-cases.sh",
    "tacenta-proofs/scripts/negatives-control-counts.json",
    "tooling/gate-inventory.json",
    "tooling/gate-mutations.json",
    "ASSURANCE-OBLIGATIONS.md",
]
OURS, BASE, SEP, THEIRS = "<<<<<<< ours", "||||||| base", "=======", ">>>>>>> theirs"
TRIVIAL = re.compile(r"\s*(?:[\]\)}]+[,;]?|\)\]|fi|done|esac|;;)?\s*")


class Refused(Exception):
    pass


def stage(root, path, n):
    result = subprocess.run(["git", "show", f":{n}:{path}"], cwd=root, capture_output=True)
    return result.stdout if result.returncode == 0 else None


PROSE_FILES = (".md", ".lean")


def key_of(rel, line):
    """An entry's key in a Markdown or Lean file: an import line, or the leading backticked name and the mark after
    it (`` `x`, `` in a list of scripts, `` `x` ( `` in the evidence list, `` `X.lean`: `` in the audit's
    docstring), so that the same entry with other text has the same key. None for prose."""
    stripped = line.strip()
    if stripped.startswith("import "):
        return stripped
    m = re.match(r"`([^`]+)`\s*(\S?)", stripped)
    return (m.group(1), m.group(2)) if m else None


def is_entry(rel, line):
    """Whether `line` is an entry of a list (a line that may appear once), rather than prose or punctuation."""
    if TRIVIAL.fullmatch(line):
        return False
    stripped = line.strip()
    if rel.endswith(PROSE_FILES):
        return key_of(rel, line) is not None
    if rel.endswith(".sh"):
        return not stripped.startswith("#")
    if rel.endswith(".py"):
        return stripped.startswith('"')
    return True


def is_prose(rel, line):
    return rel.endswith(PROSE_FILES) and not TRIVIAL.fullmatch(line) and not is_entry(rel, line)


def contained(rel, ours, theirs):
    """The longer insertion when the other is its start, its end or equal to it (a side that already holds the
    other's lines, as after a squash merge of a shared predecessor), else None. Only when the shorter holds an
    entry: a shorter side of punctuation alone (a closing `fi` that ends a block of the other) is not taken as
    held by the longer."""
    longer, shorter = (ours, theirs) if len(ours) >= len(theirs) else (theirs, ours)
    if not shorter:
        return longer
    if not any(is_entry(rel, l) for l in shorter):
        return None
    if longer[:len(shorter)] == shorter or longer[len(longer) - len(shorter):] == shorter:
        return longer
    return None


def resolve(text, rel):
    """The merged text, or Refused naming the region and its lines."""
    out, added, i, lines = [], [], 0, text.split("\n")
    while i < len(lines):
        if lines[i] != OURS:
            out.append(lines[i])
            i += 1
            continue
        start = len(out) + 1
        ours, base, theirs = [], [], []
        i += 1
        try:
            while lines[i] != BASE:
                ours.append(lines[i]); i += 1
            i += 1
            while lines[i] != SEP:
                base.append(lines[i]); i += 1
            i += 1
            while lines[i] != THEIRS:
                theirs.append(lines[i]); i += 1
            i += 1
        except IndexError:
            raise Refused(f"{rel}: an unterminated conflict region")
        if any(line.strip() for line in base):
            raise Refused(f"{rel}: a conflict at line {start} where both sides changed a line: "
                          f"{base[0].strip()[:80]!r}")
        merged = contained(rel, ours, theirs)
        if merged is None:
            if any(is_prose(rel, l) for l in ours) and any(is_prose(rel, l) for l in theirs):
                raise Refused(f"{rel}: both insertions at line {start} hold prose, which may be one line edited "
                              "on one side; resolve it by hand")
            if not any(is_entry(rel, l) for l in ours + theirs):
                raise Refused(f"{rel}: a conflict at line {start} that is not two insertions of entries")
            shared = sorted({l for l in ours if is_entry(rel, l)} & {l for l in theirs if is_entry(rel, l)})
            if shared:
                raise Refused(f"{rel}: the two insertions at line {start} share a line: {shared[0].strip()[:80]!r}")
            keys = {key_of(rel, l) for l in ours if is_entry(rel, l) and key_of(rel, l)} & \
                {key_of(rel, l) for l in theirs if is_entry(rel, l) and key_of(rel, l)}
            if rel.endswith(PROSE_FILES) and keys:
                raise Refused(f"{rel}: both insertions at line {start} hold an entry for {sorted(keys)[0][0]!r} "
                              "with other text: an edit of one entry, not two insertions")
            merged = ours + theirs
        out.extend(merged)
        added.extend(merged)
    counts = {}
    keyed = {}
    for line in out:
        counts[line] = counts.get(line, 0) + 1
        if rel.endswith(PROSE_FILES) and is_entry(rel, line):
            keyed.setdefault(key_of(rel, line), set()).add(line)
    for line in added:
        if is_entry(rel, line) and counts[line] > 1:
            raise Refused(f"{rel}: the insertion would repeat a line the file already holds: {line.strip()[:80]!r}")
        if rel.endswith(PROSE_FILES) and is_entry(rel, line) and len(keyed[key_of(rel, line)]) > 1:
            raise Refused(f"{rel}: the insertion holds an entry the file already holds with other text: "
                          f"{line.strip()[:80]!r}")
    return "\n".join(out)


def remerge(root, rel):
    versions = [stage(root, rel, n) for n in (1, 2, 3)]
    if any(v is None for v in versions):
        raise Refused(f"{rel}: not on both sides and the base")
    with tempfile.TemporaryDirectory(prefix="insertion-conflicts-") as tmp:
        paths = []
        for name, data in zip(("base", "ours", "theirs"), versions):
            p = Path(tmp) / name
            p.write_bytes(data)
            paths.append(str(p))
        merged = subprocess.run(["git", "merge-file", "-p", "--diff3", "-L", "ours", "-L", "base", "-L", "theirs",
                                 paths[1], paths[0], paths[2]], capture_output=True)
    # merge-file exits with the number of conflicts, or a negative status (above 127 here) when it fails.
    if merged.returncode > 127 or merged.returncode < 0 or (not merged.stdout and any(versions)):
        raise Refused(f"{rel}: git merge-file failed (exit {merged.returncode}): "
                      f"{merged.stderr.decode('utf-8', 'replace').strip()[:200]}")
    try:
        return merged.stdout.decode("utf-8")
    except UnicodeDecodeError:
        raise Refused(f"{rel}: not UTF-8 text")


# ---- --verify ----------------------------------------------------------------------------------------------

def repeated(values):
    seen, out = set(), []
    for v in values:
        if v in seen and v not in out:
            out.append(v)
        seen.add(v)
    return out


def verify(root):
    problems = []

    def dup(where, values):
        for v in repeated(values):
            problems.append(f"{where}: {v!r} appears twice")

    text = lambda rel: (root / rel).read_text(encoding="utf-8")
    for rel in ("tooling/gate-inventory.json", "tooling/gate-mutations.json",
                "tacenta-proofs/scripts/negatives-control-counts.json"):
        try:
            json.loads(text(rel))
        except ValueError as error:
            problems.append(f"{rel}: not JSON: {error}")
    try:
        attest_tree = ast.parse(text("tacenta-proofs/scripts/attest.py"))
    except SyntaxError as error:
        problems.append(f"tacenta-proofs/scripts/attest.py: does not parse: {error}")
        attest_tree = None
    for rel in ("tacenta-proofs/scripts/no-sorry.sh", "tacenta-proofs/scripts/check-attest-negatives.sh",
                "tooling/tests/run-proof-script-cases.sh", "tooling/tests/run-no-sorry-parts-cases.sh"):
        r = subprocess.run(["bash", "-n", rel], cwd=root, capture_output=True, text=True)
        if r.returncode:
            problems.append(f"{rel}: bash -n: {r.stderr.strip()[:200]}")
    if problems:
        return problems
    audit = text("tacenta-proofs/translation/Translation/AxiomAuditSessionUnit.lean").split("\n")
    dup("the audit's imports", [l for l in audit if l.startswith("import ")])
    dup("the audit's module paragraphs", [l.split(" ")[0] for l in audit if re.match(r"`UnitLifecycle\w+\.lean`", l)])
    ns = text("tacenta-proofs/scripts/no-sorry.sh")
    dup("no-sorry.sh functions", re.findall(r"^(phase_\w+)\(\) \{", ns, re.M))
    dup("no-sorry.sh run_phase ids", re.findall(r"^  run_phase ([a-z0-9-]+) ", ns, re.M))
    dup("no-sorry.sh control calls", re.findall(r"^python3 scripts/(check-[a-z0-9-]+\.py) \|\| fail=1$", ns, re.M))
    parts = {}
    current = None
    for line in text("tacenta-proofs/scripts/no-sorry-parts.txt").split("\n"):
        m = re.match(r"([a-z][a-z0-9-]*) ([a-z][a-z0-9-]*):((?: \S+)*)$", line)
        if m:
            current = m.group(1)
            parts.setdefault(current, []).extend(m.group(3).split())
        elif current and re.fullmatch(r"  \S+", line):
            parts[current].append(line.strip())
        else:
            current = None
    for partition, phases in parts.items():
        dup(f"the parts of partition {partition}", phases)
    table = subprocess.run(["bash", "scripts/no-sorry.sh"], cwd=root / "tacenta-proofs", capture_output=True,
                           text=True, env=dict(os.environ, NO_SORRY_LIST="1"))
    if table.returncode:
        problems.append(f"no-sorry.sh does not list its phases: {table.stderr.strip()[:200]}")
    else:
        with tempfile.NamedTemporaryFile("w", suffix=".table", delete=False) as handle:
            handle.write(table.stdout)
        for line in text("tacenta-proofs/scripts/no-sorry-parts.txt").split("\n"):
            m = re.match(r"[a-z][a-z0-9-]* ([a-z][a-z0-9-]*):", line)
            if not m:
                continue
            r = subprocess.run([sys.executable, "tacenta-proofs/scripts/no-sorry-parts.py", "resolve", "--table",
                                handle.name, "--parts", "tacenta-proofs/scripts/no-sorry-parts.txt", "--part",
                                m.group(1)], cwd=root, capture_output=True, text=True)
            if r.returncode:
                problems.append(f"no-sorry-parts.py refuses part {m.group(1)}: {(r.stderr or r.stdout).strip()[:200]}")
                break
        Path(handle.name).unlink()
    stubs = re.search(r"^py_stubs=\(\n((?:  \S+\n)*)\)", text("tooling/tests/run-no-sorry-parts-cases.sh"), re.M)
    if stubs:
        dup("run-no-sorry-parts-cases.sh py_stubs", stubs.group(1).split())
    dup("negatives-control-counts.json scripts", re.findall(r'^    "(check-[a-z0-9-]+\.py)": ',
                                                          text("tacenta-proofs/scripts/negatives-control-counts.json"), re.M))
    cases = text("tooling/tests/run-proof-script-cases.sh")
    for name in ("sh_controls", "py_controls"):
        m = re.search(rf"^{name}=\(([^)]*)\)", cases, re.M)
        if m:
            dup(f"run-proof-script-cases.sh {name}", m.group(1).split())
    m = re.search(r"^for called in ((?:[^;]|\\\n)*?); do", cases, re.M)
    if m:
        dup("run-proof-script-cases.sh the controls called", re.findall(r"'[^']*'|\S+", m.group(1).replace("\\\n", " ")))
    inventory = json.loads(text("tooling/gate-inventory.json"))
    dup("gate-inventory.json rows", [r["gate"] for r in inventory["rows"]])
    for row in inventory["rows"]:
        dup(f"gate-inventory.json controls of {row['gate']}",
            [c if isinstance(c, str) else c.get("path") for c in row.get("controls", [])])
    dup("gate-mutations.json ids", [m["id"] for m in json.loads(text("tooling/gate-mutations.json"))["mutations"]])
    for node in attest_tree.body:
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id in (
                "REQUIRED_PINS", "REQUIRED_STATEMENT_PINS", "REQUIRED_PRINT_FORM", "COMPILER_TRUSTED_PINS")
                for t in node.targets):
            name = node.targets[0].id
            entries = []
            for sub in ast.walk(node.value):
                if isinstance(sub, ast.ListComp):
                    prefix = sub.elt.left.value if isinstance(sub.elt, ast.BinOp) and \
                        isinstance(sub.elt.left, ast.Constant) else ""
                    for gen in sub.generators:
                        if isinstance(gen.iter, (ast.Tuple, ast.List)):
                            entries += [prefix + e.value for e in gen.iter.elts if isinstance(e, ast.Constant)]
                elif isinstance(sub, (ast.Set, ast.List)) and not any(isinstance(p, ast.ListComp) for p in [sub]):
                    entries += [e.value for e in sub.elts if isinstance(e, ast.Constant) and isinstance(e.value, str)]
            if not entries:
                problems.append(f"attest.py {name}: no name read (the list's form changed; extend --verify)")
            dup(f"attest.py {name}", entries)
    negatives = text("tacenta-proofs/scripts/check-attest-negatives.sh").split("\n")
    k = 0
    while k < len(negatives):
        if negatives[k] == "done <<'LIST'":
            end = negatives.index("LIST", k + 1)
            dup(f"check-attest-negatives.sh the list at line {k + 1}", negatives[k + 1:end])
            k = end
        k += 1
    # Every field of every list item of the obligations file: an entry (a line that starts with a backticked name)
    # appears once per field, in the gate lists, the evidence lists and the clauses alike.
    obligations = text("ASSURANCE-OBLIGATIONS.md").split("\n")
    field, fields = None, []
    for k, line in enumerate(obligations):
        label = re.fullmatch(r"(?:- |  )\*\*(.+):\*\*", line)
        if label:
            field = (k + 1, label.group(1), [])
            fields.append(field)
        elif field and line.startswith("  ") and line.strip():
            key = key_of("x.md", line)
            if key and key[1] in (",", "(", ":"):
                field[2].append(f"{key[0]} {key[1]}")
        elif not line.startswith("  "):
            field = None
    for number, label, keys in fields:
        dup(f"ASSURANCE-OBLIGATIONS.md the {label} field at line {number}", keys)
    return problems


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--verify", action="store_true")
    args = parser.parse_args()
    root = Path(subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                               check=True).stdout.strip())
    if args.verify:
        problems = verify(root)
        for p in problems:
            print(f"resolve-insertion-conflicts: --verify: {p}", file=sys.stderr)
        print(f"resolve-insertion-conflicts: --verify: {'no structural problem' if not problems else f'{len(problems)} problem(s)'}")
        return 1 if problems else 0
    unmerged = set(subprocess.run(["git", "diff", "--name-only", "--diff-filter=U"], cwd=root, capture_output=True,
                                  text=True, check=True).stdout.split())
    results, refusals = [], []
    for rel in FILES:
        if rel not in unmerged:
            continue
        try:
            results.append((rel, resolve(remerge(root, rel), rel)))
        except Refused as error:
            refusals.append(str(error))
    if refusals:
        for r in refusals:
            print(f"resolve-insertion-conflicts: REFUSED: {r}", file=sys.stderr)
        print(f"resolve-insertion-conflicts: nothing was written; {len(refusals)} file(s) need a hand resolution",
              file=sys.stderr)
        return 1
    if not args.check:
        for rel, new in results:
            (root / rel).write_text(new, encoding="utf-8")
            subprocess.run(["git", "add", "--", rel], cwd=root, check=True)
    verb = "would resolve" if args.check else "resolved"
    print(f"resolve-insertion-conflicts: {verb} {len(results)} file(s) of insertions at one place"
          + (": " + ", ".join(r for r, _ in results) if results else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
