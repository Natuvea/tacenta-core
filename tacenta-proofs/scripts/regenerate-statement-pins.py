#!/usr/bin/env python3
"""Rewrite a translation module's statement pins in the whole-statement form, from what Lean prints.

A statement pin is a docstring holding the message `#check @name` or `#print name` prints, then
`#guard_msgs in` and the command.  Lean's pretty printer cuts a term off at depth 50 (`pp.deepTerms`
is false by default) and replaces each proof inside a term with a bare `⋯` (`pp.proofs` is false), so
a long statement's pin can hold its first binders only.  `attest.py` refuses a statement pin whose
message contains a `⋯` that is not a typed proof, `(⋯ : P)`, and refuses every `set_option pp.*` in
the first-party Lean trees except the two below.

For each module named, this script:

  * puts `set_option pp.deepTerms true` and `set_option pp.proofs.withType true` at file level just
    before the first statement pin's docstring, unless the two lines are already there (both only
    widen what is printed: the first prints every depth, the second prints each omitted proof's
    proposition, `(⋯ : P)`; pins earlier in the file and declarations are not affected);
  * runs `lake env lean --json` on the module (from `tacenta-proofs/translation`) and, for every
    `#guard_msgs` whose docstring does not match, replaces the docstring with `info: ` and the
    message Lean printed at the pinned command;
  * runs Lean again and requires no error, and the warnings the module already had (a linter's) and
    no more.

With `--check` it writes nothing: it reports the pins whose docstring differs from what Lean prints
with the two options, and whether the options are in place, and exits 1 if anything would change.

It rewrites what Lean prints and so cannot tell a right statement from a wrong one: a weakened
theorem regenerated through it gets a weakened pin, which the diff of the pin shows.  It handles
modules of the translation package only.
"""
import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TRANSLATION = ROOT / "tacenta-proofs" / "translation"
OPTIONS = "set_option pp.deepTerms true\nset_option pp.proofs.withType true\n"
# A statement pin: a docstring, `#guard_msgs in`, then `#check @name` / `#check name` / `#print name`.
PIN = re.compile(r"/--\n(?P<doc>(?:(?!-/).)*?)\n?-/\n#guard_msgs in\n(?P<cmd>#(?:check @?|print (?!axioms ))\S+)\n",
                 re.S)


def module_path(arg):
    p = Path(arg)
    if not p.suffix:
        p = TRANSLATION / "Translation" / (arg.split(".")[-1] + ".lean")
    p = p.resolve()
    if TRANSLATION / "Translation" not in p.parents or not p.exists():
        raise SystemExit(f"{arg}: not a module of tacenta-proofs/translation/Translation")
    return p


def lean_messages(path):
    run = subprocess.run(["lake", "env", "lean", "--json", str(path)], cwd=TRANSLATION,
                         capture_output=True, text=True)
    messages = []
    for line in run.stdout.splitlines():
        line = line.strip()
        if line.startswith("{"):
            messages.append(json.loads(line))
    if run.returncode != 0 and not any(m.get("severity") == "error" for m in messages):
        raise SystemExit(f"{path.name}: lean exited {run.returncode} with no error message:\n{run.stderr}")
    return messages


def with_options(text):
    first = PIN.search(text)
    if first is None:
        return text, False
    if OPTIONS in text[:first.start()]:
        return text, False
    return text[:first.start()] + OPTIONS + "\n" + text[first.start():], True


def regenerate(path, check):
    original = path.read_text()
    text, inserted = with_options(original)
    if check and inserted:
        print(f"{path.name}: the two pp options are not in place before the first statement pin")
    if check:
        with tempfile.TemporaryDirectory() as scratch:
            probe = Path(scratch) / path.name
            probe.write_text(text)
            messages = lean_messages(probe)
    else:
        if text != original:
            path.write_text(text)
        messages = lean_messages(path)
    mismatched = {m["pos"]["line"] for m in messages
                  if m.get("severity") == "error" and "does not match generated message" in m.get("data", "")}
    other = [m for m in messages if m.get("severity") == "error" and m["pos"]["line"] not in mismatched]
    if other:
        if not check:
            path.write_text(original)
        raise SystemExit(f"{path.name}: Lean reported {len(other)} error(s) that are not a pin mismatch, "
                         f"first at line {other[0]['pos']['line']}: {other[0]['data'][:300]}")
    # Warnings the module already has (a linter's) are left alone; the rewrite must not add one.
    warnings = sum(1 for m in messages if m.get("severity") == "warning")
    printed = {m["pos"]["line"]: m["data"] for m in messages if m.get("severity") == "information"}
    out, last, changed = [], 0, []
    for m in PIN.finditer(text):
        # The newlines before the command count the lines above it, which is the 1-based line of
        # `#guard_msgs`; Lean prints the message at the command, one line further.
        guard_line = text.count("\n", 0, m.start("cmd"))
        cmd_line = guard_line + 1
        if guard_line not in mismatched:
            continue
        if cmd_line not in printed:
            raise SystemExit(f"{path.name}:{guard_line}: the pin does not match and Lean printed no message "
                             f"at its command")
        out.append(text[last:m.start("doc")])
        out.append("info: " + "\n".join(l.rstrip() for l in printed[cmd_line].split("\n")))
        last = m.end("doc")
        changed.append(m.group("cmd").split()[-1].lstrip("@"))
    out.append(text[last:])
    new = "".join(out)
    unmatched = mismatched - {text.count("\n", 0, m.start("cmd")) for m in PIN.finditer(text)}
    if unmatched:
        if not check:
            path.write_text(original)
        raise SystemExit(f"{path.name}: `#guard_msgs` mismatches at lines {sorted(unmatched)} that are not "
                         "statement pins this script rewrites")
    for name in changed:
        print(f"{path.name}: {'would rewrite' if check else 'rewrote'} the pin of {name}")
    if check:
        return bool(changed or inserted)
    path.write_text(new)
    after = lean_messages(path)
    again = [m for m in after if m.get("severity") == "error"]
    if again:
        raise SystemExit(f"{path.name}: after the rewrite Lean still reports {len(again)} error(s), first at "
                         f"line {again[0]['pos']['line']}: {again[0]['data'][:300]}")
    if sum(1 for m in after if m.get("severity") == "warning") != warnings:
        raise SystemExit(f"{path.name}: the rewrite changed the number of warnings Lean reports")
    return bool(changed or inserted)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("modules", nargs="+", help="module names (UnitLifecycleX) or paths")
    parser.add_argument("--check", action="store_true", help="write nothing; exit 1 if a pin would change")
    a = parser.parse_args()
    changed = [regenerate(module_path(m), a.check) for m in a.modules]
    return 1 if a.check and any(changed) else 0


if __name__ == "__main__":
    sys.exit(main())
