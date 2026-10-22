#!/usr/bin/env python3
"""Wire a new lifecycle proof module into the gates, in two runs, so that only the proof and its controls are
written by hand.

    python3 tacenta-proofs/scripts/new-lifecycle-module.py scaffold --module UnitLifecycleX \\
        --negatives check-x-negatives.py --part decrypt --description "one line" [--imports Translation.M] \\
        [--phase x] [--label "..."] [--check]
    python3 tacenta-proofs/scripts/new-lifecycle-module.py pins --module UnitLifecycleX \\
        [--lean | --keep-pins] [--print-form-case NAME | --no-print-form-case] [--check]

A module of `tacenta-proofs/translation/Translation/` that proves a lifecycle result is held by about a dozen
shared files. Written by hand, two branches each adding a module edited the same lines of those files and their
merge conflicted; and a file missed was a gate that silently did not hold the module. This makes the edits.

`scaffold` (before the proof exists) creates the module from `templates/lifecycle-module.lean.in` (with the two
pretty-printer options that make its statement pins print whole, before the section `genpins.py` writes) and its
negatives script from `templates/lifecycle-negatives.py.in` (the controls' full mechanism, the helpers shared
character for character with the other lifecycle negatives scripts, which `check-negatives-control-counts.py`
holds the template to: the not-a-refusal guard matched without regard to case and its start-up tests on each
error spelling it lists and on a heartbeat timeout, the unmodified baselines, the `COMPOSING`, `INSIDE`,
`PROJECTION`, `PROJECTED` and `STATEMENT_SHAPE` labels checked at start-up against the syntactic projection
standard, the `sorry` probe of each inside control, and `check_complete` over the Lean runs `RUNS` records; with
no control planted it refuses to run), and makes every edit that does not depend on theorem names:

  Translation/AxiomAuditSessionUnit.lean      the import, and a paragraph of the audit's docstring
  scripts/no-sorry.sh                         the phase's function and its `run_phase` line
  scripts/no-sorry-parts.txt                  the phase, in the named part of the `hosted` partition
  tooling/tests/run-proof-script-cases.sh     the script among the stubbed controls and the controls called
  tooling/tests/run-no-sorry-parts-cases.sh   the script among the stubbed scripts
  scripts/negatives-control-counts.json       the script's entry: its number of controls in each class (none
                                              yet) and of baselines, which `check-negatives-control-counts.py`
                                              compares with the script; edit it with each control added
  tooling/gate-inventory.json                 the script among the Lean build's controls, and its own row
  tooling/gate-mutations.json                 `NS-drop-<phase>` and `NS-swallow-<phase>`
  ASSURANCE-OBLIGATIONS.md                    the script in the lifecycle row of the gate evidence list
  tacenta-proofs/GATE-INVENTORY.md, the manifests   regenerated (`gate-inventory.py --write`, `attest.py`)

`pins` (once the proof is written) writes the module's `## Pins` section with `genpins.py` (`--lean`, which runs
Lean) or reads the one there (`--keep-pins`, the default), and from it makes the edits that need the names:

  scripts/attest.py                           the module's names on REQUIRED_PINS, REQUIRED_STATEMENT_PINS,
                                              REQUIRED_PRINT_FORM and COMPILER_TRUSTED_PINS (the pins whose
                                              axioms `attest.py` classifies as compiler trust)
  scripts/check-attest-negatives.sh           the module's line in the axiom-pin and statement-pin deletion
                                              lists, and one print-form case (a definition's pin as `#check @`)
  scripts/attest-negatives-case-count.txt     the count, by the number of cases those add or remove
  the manifests                               regenerated (`attest.py`)

Every edit is anchored on lines the tool finds exactly once, and it refuses, writing nothing, when an anchor is
missing or found twice. A new entry goes after the existing entry its name sorts after (after the first entry
when it sorts before all of them), so that two modules with different names add lines at different places and
their branches merge without a conflict; the lists keep the order they have. Running either step again changes
nothing (`pins` replaces the module's own entries with what the pins say now). `--check` prints the edits as a
diff and writes nothing. Each edit to `attest.py` is checked by loading the edited script and comparing its four
lists with the old ones: they must differ by exactly the module's names.

What it does not write: the prose. `CLAIMS.md` (its section is what `attest.py --check` holds the pins to),
`LIMITATIONS.md`, the Session row of `ASSURANCE.md`, `GAP-REGISTER.md` and both READMEs say what the module
shows; the text it adds elsewhere is marked `SCAFFOLD-TODO`, which `tooling/check-proof-module-preflight.py`
refuses. At the end it lists what is left.
"""
import argparse
import difflib
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TODO = "SCAFFOLD-TODO"

AUDIT = "tacenta-proofs/translation/Translation/AxiomAuditSessionUnit.lean"
NO_SORRY = "tacenta-proofs/scripts/no-sorry.sh"
PARTS = "tacenta-proofs/scripts/no-sorry-parts.txt"
CASES = "tooling/tests/run-proof-script-cases.sh"
INVENTORY = "tooling/gate-inventory.json"
MUTATIONS = "tooling/gate-mutations.json"
OBLIGATIONS = "ASSURANCE-OBLIGATIONS.md"
ATTEST = "tacenta-proofs/scripts/attest.py"
NEGATIVES_SH = "tacenta-proofs/scripts/check-attest-negatives.sh"
COUNT = "tacenta-proofs/scripts/attest-negatives-case-count.txt"
TEMPLATES = "tacenta-proofs/scripts/templates"
PARTS_CASES = "tooling/tests/run-no-sorry-parts-cases.sh"
RECORD = "tacenta-proofs/scripts/negatives-control-counts.json"
COUNTS_GATE = "tacenta-proofs/scripts/check-negatives-control-counts.py"

MODULE_NAME = re.compile(r"UnitLifecycle[A-Z][A-Za-z0-9]*")
NEGATIVES_NAME = re.compile(r"check-[a-z0-9]+(?:-[a-z0-9]+)*-negatives\.py")
PHASE_NAME = re.compile(r"[a-z][a-z0-9-]*")


class Refused(Exception):
    pass


def refuse(message):
    raise Refused(message)


def one(indices, what):
    """The one index of `indices`, or a refusal naming `what`."""
    if len(indices) != 1:
        refuse(f"{what}: found {len(indices)} times, not once")
    return indices[0]


def place_after(keys, new):
    """The position in `keys` (sorted or not) after which an entry named `new` goes: the greatest key below it,
    or the first key when none is below it."""
    if not keys:
        refuse(f"no existing entry to place {new} beside")
    below = [k for k in range(len(keys)) if keys[k] < new]
    return max(below, key=lambda k: keys[k]) if below else 0


def clause(text):
    """A one-line description as a clause: no final full stop."""
    return text.strip().rstrip(".")


def wrap(text, width, prefix):
    words, lines, line = text.split(), [], ""
    for w in words:
        if line and len(prefix) + len(line) + 1 + len(w) > width:
            lines.append(prefix + line)
            line = w
        else:
            line = f"{line} {w}" if line else w
    if line:
        lines.append(prefix + line)
    return lines


class Tree:
    """The files the run reads and the edits it would make, written together at the end or not at all."""

    def __init__(self, root):
        self.root = root
        self.old, self.new, self.modes = {}, {}, {}

    def read(self, rel):
        if rel not in self.new:
            path = self.root / rel
            if not path.exists():
                refuse(f"{rel} does not exist")
            self.old[rel] = path.read_text(encoding="utf-8")
            self.new[rel] = self.old[rel]
        return self.new[rel]

    def write(self, rel, text, mode=None):
        if rel not in self.new:
            path = self.root / rel
            self.old[rel] = path.read_text(encoding="utf-8") if path.exists() else None
        self.new[rel] = text
        if mode:
            self.modes[rel] = mode

    def changed(self):
        return [rel for rel in self.new if self.new[rel] != self.old.get(rel)]

    def diff(self):
        out = []
        for rel in self.changed():
            old = (self.old[rel] or "").splitlines(keepends=True)
            new = self.new[rel].splitlines(keepends=True)
            out.extend(difflib.unified_diff(old, new, f"a/{rel}", f"b/{rel}", n=1))
        return "".join(out)

    def commit(self):
        created = []
        for rel in self.changed():
            path = self.root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            if self.old.get(rel) is None:
                created.append(rel)
            path.write_text(self.new[rel], encoding="utf-8")
            if rel in self.modes:
                os.chmod(path, self.modes[rel])
        # A new file is recorded as intended for the index (`git add -N`), so that the generators, which read the
        # tracked files, see it; its content is staged by whoever commits it.
        if created and (self.root / ".git").exists():
            subprocess.run(["git", "add", "--intent-to-add", "--"] + created, cwd=self.root, check=True)


# ---- scaffold: the module, its script, and the wiring that needs no theorem name --------------------------

def template(tree, name, values):
    text = (tree.root / TEMPLATES / name).read_text(encoding="utf-8")
    for key, value in values.items():
        text = text.replace(f"@{key}@", value)
    if re.search(r"@[A-Z]+@", text):
        refuse(f"{TEMPLATES}/{name} holds a placeholder this tool does not fill")
    return text


def create_files(tree, a):
    module_rel = f"tacenta-proofs/translation/Translation/{a.module}.lean"
    script_rel = f"tacenta-proofs/scripts/{a.negatives}"
    values = {"MODULE": a.module, "IMPORT": a.imports, "DESCRIPTION": a.description,
              "PROBE": a.phase}
    for rel, name, mode in ((module_rel, "lifecycle-module.lean.in", None),
                            (script_rel, "lifecycle-negatives.py.in", 0o755)):
        if (tree.root / rel).exists():
            continue  # written once; the proof and the controls are the author's from then on
        tree.write(rel, template(tree, name, values), mode)


def edit_audit(tree, a):
    lines = tree.read(AUDIT).split("\n")
    line = f"import Translation.{a.module}"
    if line not in lines:
        imports = [(k, m.group(1)) for k, l in enumerate(lines)
                   for m in [re.fullmatch(r"import Translation\.(UnitLifecycle\w+)", l)] if m]
        if not imports:
            refuse(f"{AUDIT}: no `import Translation.UnitLifecycle...` line to place the import beside")
        at = imports[place_after([n for _, n in imports], a.module)][0]
        lines.insert(at + 1, line)
    if not any(l.startswith(f"`{a.module}.lean`") for l in lines):
        anchor = one([k for k, l in enumerate(lines) if l.startswith("`UnitKemWrapperModel.lean` builds that KEM model")],
                     f"{AUDIT}: the docstring line that begins `UnitKemWrapperModel.lean` builds that KEM model")
        # One line, led by the module's name, so that a merge tool can tell this paragraph from another module's.
        paragraph = [f"`{a.module}.lean`: {a.description} {TODO}: say what it shows, under which laws, and "
                     "what it does not show."]
        lines[anchor:anchor] = paragraph
    tree.write(AUDIT, "\n".join(lines))


NEGATIVES_FN = re.compile(r"^phase_(\w+)\(\) \{\npython3 scripts/(check-[a-z0-9-]+-negatives\.py) \|\| fail=1\n\}$",
                          re.M)
RUN_PHASE = re.compile(r'^  run_phase ([a-z0-9-]+) plain "[^"]*" (phase_\w+)$', re.M)


def edit_no_sorry(tree, a):
    text = tree.read(NO_SORRY)
    fn = "phase_" + a.phase.replace("-", "_")
    found = {m.group(2): m for m in NEGATIVES_FN.finditer(text)}
    by_fn = {"phase_" + m.group(1): m.group(2) for m in NEGATIVES_FN.finditer(text)}
    if fn in by_fn and by_fn[fn] != a.negatives:
        refuse(f"{NO_SORRY}: {fn} already runs {by_fn[fn]}")
    if re.search(rf"^{fn}\(\) \{{", text, re.M) and fn not in by_fn:
        refuse(f"{NO_SORRY}: a function {fn} exists and is not a negatives phase")
    if a.negatives not in found:
        if not found:
            refuse(f"{NO_SORRY}: no phase function that runs a check-*-negatives.py to place the new one beside")
        names = sorted(found)
        at = found[names[place_after(names, a.negatives)]].end()
        comment = wrap(f"{clause(a.description)} (`{a.module}.lean`). {TODO}: say which changes the control plants and "
                       "that each must be refused at a named declaration or pin, with a message naming the change, "
                       "after the unmodified copies are accepted.", 112, "# ")
        block = "\n\n" + "\n".join(comment) + f"\n{fn}() {{\npython3 scripts/{a.negatives} || fail=1\n}}"
        text = text[:at] + block + text[at:]
    runs = list(RUN_PHASE.finditer(text))
    if not any(m.group(1) == a.phase for m in runs):
        if any(re.match(rf"  run_phase {re.escape(a.phase)} ", l) for l in text.split("\n")):
            refuse(f"{NO_SORRY}: a run_phase line for {a.phase} exists in another form")
        script_of = {"phase_" + m.group(1): m.group(2) for m in NEGATIVES_FN.finditer(text)}
        candidates = [m for m in runs if m.group(2) in script_of and m.group(1) != a.phase]
        if not candidates:
            refuse(f"{NO_SORRY}: no run_phase line of a negatives phase to place the new one beside")
        names = [script_of[m.group(2)] for m in candidates]
        anchor = candidates[place_after(names, a.negatives)]
        label = a.label.replace('"', "'")
        text = text[:anchor.end()] + f'\n  run_phase {a.phase} plain "{label}" {fn}' + text[anchor.end():]
    tree.write(NO_SORRY, text)


def edit_parts(tree, a):
    lines = tree.read(PARTS).split("\n")
    header = re.compile(r"(hosted) ([a-z][a-z0-9-]*):((?: \S+)*)$")
    parts = {}
    current = None
    for k, l in enumerate(lines):
        m = header.match(l)
        if m:
            current = m.group(2)
            parts[current] = [k, [(k, w) for w in m.group(3).split()]]
        elif current and re.fullmatch(r"  \S+", l):
            parts[current][1].append((k, l.strip()))
        else:
            current = None
    for part, (_, phases) in parts.items():
        if any(w.split("@")[0] == a.phase for _, w in phases):
            if part == a.part:
                return
            refuse(f"{PARTS}: phase {a.phase} is already in part {part}")
    if a.part not in parts:
        refuse(f"{PARTS}: the hosted partition has no part {a.part} (a new part is also a new job of the "
               "`translation-part` matrix in .github/workflows/ci.yml; add it there and here by hand)")
    head, phases = parts[a.part]
    words = [w for _, w in phases]
    if "*" in words or any("@" in w for w in words):
        refuse(f"{PARTS}: part {a.part} is `*` or a slice; give the phase to another part")
    if any(k == head for k, _ in phases):  # one-line form: write the part over several lines first
        lines[head] = f"hosted {a.part}:"
        lines[head + 1:head + 1] = [f"  {w}" for w in words]
        phases = [(head + 1 + i, w) for i, w in enumerate(words)]
    at = phases[place_after(words, a.phase)][0]
    lines.insert(at + 1, f"  {a.phase}")
    tree.write(PARTS, "\n".join(lines))


def insert_word(lines, start, end, pattern, new_line, key, new_key, what):
    """Insert `new_line` among lines[start:end] that match `pattern` (group 1 the key), after its predecessor."""
    entries = [(k, re.fullmatch(pattern, lines[k]).group(1)) for k in range(start, end)
               if re.fullmatch(pattern, lines[k])]
    if any(n == new_key for _, n in entries):
        return False
    if not entries:
        refuse(f"{what}: no entry to place {new_key} beside")
    at = entries[place_after([n for _, n in entries], new_key)][0]
    lines.insert(at + 1, new_line)
    return True


def edit_cases(tree, a):
    lines = tree.read(CASES).split("\n")
    start = one([k for k, l in enumerate(lines) if l == "py_controls=("],
                f"{CASES}: the line `py_controls=(` (run `python3 tooling/reflow-shared-lists.py --write`)")
    end = next((k for k in range(start, len(lines)) if lines[k] == ")"), None)
    if end is None:
        refuse(f"{CASES}: the py_controls array does not end with a line `)`")
    insert_word(lines, start + 1, end, r"  (check-[a-z0-9-]+-negatives\.py)", f"  {a.negatives}", None,
                a.negatives, f"{CASES} py_controls")
    start = one([k for k, l in enumerate(lines) if l == "for called in \\"],
                f"{CASES}: the line `for called in \\` (run `python3 tooling/reflow-shared-lists.py --write`)")
    end = next((k for k in range(start, len(lines)) if lines[k].endswith("; do")), None)
    if end is None:
        refuse(f"{CASES}: the `for called in` list does not end with `; do`")
    insert_word(lines, start + 1, end, r"  (check-[a-z0-9-]+-negatives\.py) \\", f"  {a.negatives} \\", None,
                a.negatives, f"{CASES} the controls called")
    tree.write(CASES, "\n".join(lines))


ROW_GATE = re.compile(r'  \{"gate": "tacenta-proofs/scripts/(check-[a-z0-9-]+-negatives\.py)", "kind": "script \(control\)"')


def edit_inventory(tree, a):
    text = tree.read(INVENTORY)
    lines = text.split("\n")
    path = f"tacenta-proofs/scripts/{a.negatives}"
    start = one([k for k, l in enumerate(lines)
                 if l.startswith('  {"gate": "lake build of the model, proofs and translation"') and
                 l.endswith('"controls": [')],
                f"{INVENTORY}: the Lean build's row with its controls one per line "
                "(run `python3 tooling/reflow-shared-lists.py --write`)")
    end = next(k for k in range(start, len(lines)) if lines[k].startswith("  ]"))
    entries = [(k, m.group(1)) for k in range(start + 1, end)
               for m in [re.fullmatch(r'    "tacenta-proofs/scripts/(check-[a-z0-9-]+-negatives\.py)",?', lines[k])] if m]
    if not any(n == a.negatives for _, n in entries):
        if not entries:
            refuse(f"{INVENTORY}: the Lean build's row lists no negatives script to place the new one beside")
        at = entries[place_after([n for _, n in entries], a.negatives)][0]
        if not lines[at].endswith(","):
            # The last element has no comma; an entry that sorts after it goes before it, so that no edit
            # changes an existing line (two such edits would then conflict in one line).
            at -= 1
        lines.insert(at + 1, f'    "{path}",')
    rows = [(k, m.group(1)) for k, l in enumerate(lines) for m in [ROW_GATE.match(l)] if m]
    if not any(n == a.negatives for _, n in rows):
        if not rows:
            refuse(f"{INVENTORY}: no row of a negatives script to place the new one beside")
        at = rows[place_after([n for _, n in rows], a.negatives)][0]
        row = {"gate": path, "kind": "script (control)",
               "what": f"{clause(a.description)}; {TODO}: say which changes are refused, each at a named declaration or "
                       "pin with a message naming the change",
               "controls": [{"path": path, "indirect": True,
                             "note": "it is the control; nothing holds it but its own mutations"}],
               "cheapest": "a case runner for the control's own guards (its anchors, the expected-error match, "
                           "the timeout and the launch handling): `mutate-gates.py --guards` takes only a shell "
                           "case runner, and none exists for a Python control that compiles Lean, as for the "
                           "other Python proof controls"}
        lines.insert(at + 1, "  " + json.dumps(row, ensure_ascii=False) + ",")
    new = "\n".join(lines)
    try:
        json.loads(new)
    except ValueError as error:
        refuse(f"{INVENTORY}: the edit would leave a file that is not JSON: {error}")
    tree.write(INVENTORY, new)


def edit_parts_cases(tree, a):
    """The script among the stubs of the parts runner (whose phase count is read from no-sorry.sh)."""
    lines = tree.read(PARTS_CASES).split("\n")
    start = one([k for k, l in enumerate(lines) if l == "py_stubs=("], f"{PARTS_CASES}: the line `py_stubs=(`")
    end = next((k for k in range(start, len(lines)) if lines[k] == ")"), None)
    if end is None:
        refuse(f"{PARTS_CASES}: the py_stubs array does not end with a line `)`")
    insert_word(lines, start + 1, end, r"  (check-[a-z0-9-]+-negatives\.py)", f"  {a.negatives}", None,
                a.negatives, f"{PARTS_CASES} py_stubs")
    tree.write(PARTS_CASES, "\n".join(lines))


def edit_record(tree, a):
    """The script's entry in the record of control counts, with the counts of the script as it is now."""
    text = tree.read(RECORD)
    lines = text.split("\n")
    try:
        record = json.loads(text)
        scripts = record["scripts"]
    except (ValueError, KeyError, TypeError) as error:
        refuse(f"{RECORD} cannot be read as a record of scripts ({error})")
    if a.negatives in scripts:
        return
    entries = [(k, m.group(1)) for k, l in enumerate(lines)
               for m in [re.fullmatch(r'    "(check-[a-z0-9-]+-negatives\.py)": \{.*\},?', l)] if m]
    if len(entries) != len(scripts) or not entries:
        refuse(f"{RECORD}: its scripts are not one entry per line (`    \"check-...-negatives.py\": {{...}},`)")
    # The counts the gate reads, from the script's text as it will be written (the template's or the one there).
    rel = f"tacenta-proofs/scripts/{a.negatives}"
    source = tree.new.get(rel) if rel in tree.new else (tree.root / rel).read_text(encoding="utf-8")
    spec = importlib.util.spec_from_file_location("counts_gate_for_new_module", tree.root / COUNTS_GATE)
    gate = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gate)
    with tempfile.TemporaryDirectory(prefix="new-lifecycle-module-") as tmp:
        probe = Path(tmp) / a.negatives
        probe.write_text(source, encoding="utf-8")
        got, _ = gate.counts(probe)
    if got.get("baselines") is None:
        refuse(f"{a.negatives}: its `sources` dictionary in `main` cannot be read, so its baselines cannot be counted")
    entry = {c: got[c] for c in gate.CLASSES}
    at = entries[place_after([n for _, n in entries], a.negatives)][0]
    if not lines[at].endswith(","):
        # The last entry has no comma; an entry that sorts after it goes before it, so that no edit changes an
        # existing line.
        at -= 1
    lines.insert(at + 1, f'    "{a.negatives}": {json.dumps(entry)},')
    new = "\n".join(lines)
    try:
        json.loads(new)
    except ValueError as error:
        refuse(f"{RECORD}: the edit would leave a file that is not JSON: {error}")
    tree.write(RECORD, new)


NS_ENTRY = re.compile(r'    \{"id": "NS-(drop|swallow)-([a-z0-9-]+)", "file": "tacenta-proofs/scripts/no-sorry\.sh", '
                      r'"old": "python3 scripts/(check-[a-z0-9-]+-negatives\.py) \|\| fail=1')


def edit_mutations(tree, a):
    lines = tree.read(MUTATIONS).split("\n")
    entries = [(k, m.group(1), m.group(3)) for k, l in enumerate(lines) for m in [NS_ENTRY.match(l)] if m]
    if any(s == a.negatives for _, _, s in entries):
        return
    swallows = [(k, s) for k, kind, s in entries if kind == "swallow"]
    if not swallows:
        refuse(f"{MUTATIONS}: no NS-swallow entry of a negatives script to place the new ones beside")
    at = swallows[place_after([s for _, s in swallows], a.negatives)][0]
    if not lines[at].endswith(","):
        refuse(f"{MUTATIONS}: the entry to place the new ones after is the last of its list")
    runner = "bash tooling/tests/run-proof-script-cases.sh"
    drop = {"id": f"NS-drop-{a.phase}", "file": NO_SORRY,
            "old": f"python3 scripts/{a.negatives} || fail=1\n", "new": ":\n",
            "what": f"the call of {a.negatives} is deleted", "runner": runner,
            "expect": f"WRONG  no-sorry honest: '{a.negatives}' was not called"}
    swallow = {"id": f"NS-swallow-{a.phase}", "file": NO_SORRY,
               "old": f"python3 scripts/{a.negatives} || fail=1",
               "new": f"python3 scripts/{a.negatives} || true",
               "what": f"the failure of {a.negatives} is swallowed", "runner": runner,
               "expect": f"WRONG  no-sorry a failing {a.negatives}"}
    ids = {json.loads(l.rstrip(","))["id"] for l in lines if l.startswith('    {"id": ')}
    for entry in (drop, swallow):
        if entry["id"] in ids:
            refuse(f"{MUTATIONS}: the id {entry['id']} is taken")
    lines[at + 1:at + 1] = ["    " + json.dumps(e, ensure_ascii=False) + "," for e in (drop, swallow)]
    new = "\n".join(lines)
    try:
        json.loads(new)
    except ValueError as error:
        refuse(f"{MUTATIONS}: the edit would leave a file that is not JSON: {error}")
    tree.write(MUTATIONS, new)


def field_span(lines, label_line, labels):
    """(first, end) of the lines of the field that starts after `label_line`, up to the next label or item."""
    k = label_line + 1
    while k < len(lines) and lines[k].startswith("  ") and not re.fullmatch(r"  \*\*.+:\*\*", lines[k]):
        k += 1
    return label_line + 1, k


def edit_obligations(tree, a):
    lines = tree.read(OBLIGATIONS).split("\n")
    anchor = one([k for k, l in enumerate(lines) if l == "  `check-decrypt-ratchet-negatives.py`,"],
                 f"{OBLIGATIONS}: the line `  \\`check-decrypt-ratchet-negatives.py\\`,` of the lifecycle row")
    item = max(k for k in range(anchor + 1) if lines[k] == "- **Gate/check:**")
    labels = {}
    k = item + 1
    while k < len(lines) and not lines[k].startswith("- ") and lines[k] != "<!-- End of the list. -->":
        m = re.fullmatch(r"  \*\*(.+):\*\*", lines[k])
        if m:
            labels[m.group(1)] = k
        k += 1
    for label in ("Protected property", "Current negative-control evidence"):
        if label not in labels:
            refuse(f"{OBLIGATIONS}: the lifecycle row has no `{label}` field")
    code = f"`{a.negatives}`"
    if any(code in l for l in lines[item:k]):
        return
    # The gate list: one script per line.
    first, end = field_span(lines, item, labels)
    entries = [(j, m.group(1)) for j in range(first, end)
               for m in [re.fullmatch(r"  `(check-[a-z0-9-]+-negatives\.py)`,", lines[j])] if m]
    at = entries[place_after([n for _, n in entries], a.negatives)][0]
    lines.insert(at + 1, f"  {code},")
    for label in labels:
        if labels[label] > at:
            labels[label] += 1
    # The evidence: an item for the script, before the item of the script its name sorts before.
    first, end = field_span(lines, labels["Current negative-control evidence"], labels)
    starts = [(j, m.group(1)) for j in range(first, end)
              for m in [re.match(r"  `(check-[a-z0-9-]+-negatives\.py)` \(", lines[j])] if m]
    after = sorted((n, j) for j, n in starts if n > a.negatives)
    if not starts:
        refuse(f"{OBLIGATIONS}: the lifecycle row's evidence lists no negatives script to place the new one beside")
    # The last item ends the field's sentence mid-line; a script that sorts after every item goes before the last
    # one, so that the grammar of the list holds and no existing line changes.
    j = after[0][1] if after else max(j for j, _ in starts)
    lines.insert(j, f"  {code} ({TODO}: the copies accepted and the changes refused, and what each change is),")
    # The protected property: a clause before the last.
    first, end = field_span(lines, labels["Protected property"], labels)
    last = max(i for i in range(first, end) if lines[i].strip())
    # Led by the script's name, so that a merge tool can tell this clause from another module's.
    lines.insert(last, f"  {code}: {clause(a.description)} ({TODO}: say what it keeps);")
    tree.write(OBLIGATIONS, "\n".join(lines))


def scaffold(tree, a):
    create_files(tree, a)
    edit_audit(tree, a)
    edit_no_sorry(tree, a)
    edit_parts(tree, a)
    edit_cases(tree, a)
    edit_parts_cases(tree, a)
    edit_record(tree, a)
    edit_inventory(tree, a)
    edit_mutations(tree, a)
    edit_obligations(tree, a)


# ---- pins: the edits that need the theorem names ------------------------------------------------------------

def load_attest(path, text=None):
    """attest.py as a module, from its file or from `text` in its place (its lists are read, nothing is run)."""
    spec = importlib.util.spec_from_file_location("attest_for_new_module", path)
    module = importlib.util.module_from_spec(spec)
    if text is None:
        spec.loader.exec_module(module)
    else:
        module.__file__ = str(path)
        exec(compile(text, str(path), "exec"), module.__dict__)
    return module


def read_pins(tree, a, attest):
    text = tree.read(f"tacenta-proofs/translation/Translation/{a.module}.lean")
    cut = text.find("\n/-! ## Pins")
    if cut < 0:
        refuse(f"{a.module}.lean has no `/-! ## Pins` section (run with --lean to write it)")
    pins = text[cut:]
    externals = attest.opaque_externals()
    axiom, compiler = [], []
    for m in attest.AXIOM_PIN.finditer(pins):
        name = m.group("name")
        axioms = [x.strip() for x in m.group("axioms").split(",") if x.strip()]
        axiom.append(name)
        if attest.classify(axioms, externals) == "compiler":
            compiler.append(name)
    if len(axiom) != len(attest.RAW_PIN.findall(pins)):
        refuse(f"{a.module}.lean: an axiom pin's message is not one `attest.py` reads (a theorem that depends "
               "on no axiom prints another sentence)")
    statement = [m.group(2) for m in re.finditer(r"#guard_msgs in\n#(check @|print )(?!axioms )(\S+)\n", pins)]
    printed = [m.group(1) for m in re.finditer(r"#guard_msgs in\n#print (?!axioms )(\S+)\n", pins)]
    # A statement pin in another form (`#check X` without `@`, a `set_option ... in` before it, other spacing)
    # would be left off the lists without a word: refuse instead.
    live = len(re.findall(r"^\s*(?:set_option\s.*\bin\s+)?#(?:check\b|print(?!\s+axioms\b))", pins, re.M))
    if live != len(statement):
        refuse(f"{a.module}.lean: {live} `#check` or `#print` pins, of which {len(statement)} are in the form "
               "`#guard_msgs in` / `#check @name` or `#print name` this reads; write the others in that form")
    prefix = f"Tacenta.{a.module}."
    foreign = sorted({n for n in axiom + statement if not n.startswith(prefix)})
    if foreign:
        refuse(f"{a.module}.lean pins names outside its namespace ({', '.join(foreign)}); add those to "
               "attest.py by hand and remove them from the section, or move them")
    short = lambda names: [n[len(prefix):] for n in names]
    return {"axiom": short(axiom), "statement": short(statement), "print": short(printed),
            "compiler": short(compiler)}


BLOCK_HEAD = re.compile(r'^    (?:\+ )?\["Tacenta\.(\w+)\." \+ n for n in \($')


def list_span(lines, name):
    start = one([k for k, l in enumerate(lines) if l == f"{name} = frozenset("], f"{ATTEST}: `{name} = frozenset(`")
    end = next((k for k in range(start, len(lines)) if lines[k] == ")"), None)
    if end is None:
        refuse(f"{ATTEST}: {name} does not end with a line `)`")
    return start, end


def edit_block(lines, list_name, module, names, comment):
    start, end = list_span(lines, list_name)
    blocks = []
    for k in range(start + 1, end):
        m = BLOCK_HEAD.match(lines[k])
        if m:
            close = next(j for j in range(k, end) if lines[j] == "    )]")
            first = k
            while lines[first - 1].startswith("    #"):
                first -= 1
            blocks.append((m.group(1), first, k, close))
    mine = [b for b in blocks if b[0] == module]
    body = [f'        "{n}",' for n in names]
    if len(mine) > 1:
        refuse(f"{ATTEST}: {list_name} has {len(mine)} blocks for {module}")
    if mine:
        _, _, head, close = mine[0]
        if not names:
            del lines[mine[0][1]:close + 1]
        else:
            lines[head + 1:close] = body
        return
    if not names:
        return
    if not blocks:
        refuse(f"{ATTEST}: {list_name} has no module block to place {module}'s beside")
    at = blocks[place_after([b[0] for b in blocks], module)][3]
    lines[at + 1:at + 1] = ([f"    # {comment}"] + [f'    + ["Tacenta.{module}." + n for n in ('] + body + ["    )]"])


def edit_compiler(lines, module, names):
    start, end = list_span(lines, "COMPILER_TRUSTED_PINS")
    prefix = f'        "Tacenta.{module}.'
    mine = [k for k in range(start, end) if lines[k].startswith(prefix)]
    body = [f'        "Tacenta.{module}.{n}",' for n in names]
    if mine:
        if mine != list(range(mine[0], mine[-1] + 1)):
            refuse(f"{ATTEST}: COMPILER_TRUSTED_PINS holds {module}'s names apart from each other")
        lines[mine[0]:mine[-1] + 1] = body
        return
    if not names:
        return
    groups = {}
    for k in range(start, end):
        m = re.match(r'        "Tacenta\.(UnitLifecycle\w+)\.', lines[k])
        if m:
            groups[m.group(1)] = k
    if not groups:
        refuse(f"{ATTEST}: COMPILER_TRUSTED_PINS names no lifecycle module to place {module}'s beside")
    keys = sorted(groups)
    at = groups[keys[place_after(keys, module)]]
    lines[at + 1:at + 1] = [f"        # `{module}`: the results whose pins list a compiler-trust axiom."] + body


def edit_attest(tree, a, pins):
    path = tree.root / ATTEST
    old_text = tree.read(ATTEST)
    lines = old_text.split("\n")
    comment = f"{clause(a.description)} (`{a.module}`)."
    edit_block(lines, "REQUIRED_PINS", a.module, pins["axiom"], comment)
    edit_block(lines, "REQUIRED_STATEMENT_PINS", a.module, pins["statement"], comment)
    edit_block(lines, "REQUIRED_PRINT_FORM", a.module, pins["print"], comment)
    edit_compiler(lines, a.module, pins["compiler"])
    new_text = "\n".join(lines)
    old, new = load_attest(path, old_text), load_attest(path, new_text)
    prefix = f"Tacenta.{a.module}."
    for name, key in (("REQUIRED_PINS", "axiom"), ("REQUIRED_STATEMENT_PINS", "statement"),
                      ("REQUIRED_PRINT_FORM", "print"), ("COMPILER_TRUSTED_PINS", "compiler")):
        before, after = getattr(old, name), getattr(new, name)
        others_before = {n for n in before if not n.startswith(prefix)}
        others_after = {n for n in after if not n.startswith(prefix)}
        if others_before != others_after or {n for n in after if n.startswith(prefix)} != {prefix + n for n in pins[key]}:
            refuse(f"{ATTEST}: the edited {name} is not the old one with the module's names replaced")
    tree.write(ATTEST, new_text)


def edit_negative_lists(tree, a, pins):
    """The module's lines in the two deletion lists, and the print-form case; returns the change of the count."""
    lines = tree.read(NEGATIVES_SH).split("\n")
    delta = 0
    prefix_line = f"{a.module} Tacenta.{a.module} "
    for key, refusal in (("axiom", "is on REQUIRED_PINS and has no axiom pin"),
                         ("statement", "is on REQUIRED_STATEMENT_PINS and has no statement pin")):
        lists = []
        for k, l in enumerate(lines):
            if l == "done <<'LIST'":
                end = next(j for j in range(k, len(lines)) if lines[j] == "LIST")
                loop = max(j for j in range(k) if lines[j].startswith("while IFS=' ' read -r file ns names; do"))
                if any(refusal in lines[j] for j in range(loop, k)) and \
                        any(lines[j].startswith("UnitLifecycleRestoredSession ") for j in range(k, end)):
                    lists.append((k, end))
        k, end = lists[0] if len(lists) == 1 else one(lists, f"{NEGATIVES_SH}: the lifecycle list of the loop "
                                                             f"that says `{refusal}`")
        names = pins[key]
        mine = [j for j in range(k + 1, end) if lines[j].startswith(prefix_line) or lines[j] == prefix_line.strip()]
        new_line = prefix_line + " ".join(names)
        if mine:
            j = one(mine, f"{NEGATIVES_SH}: {a.module}'s line in the list that says `{refusal}`")
            delta += len(names) - (len(lines[j].split()) - 2)
            if names:
                lines[j] = new_line
            else:
                del lines[j]
        elif names:
            entries = [(j, lines[j].split()[0]) for j in range(k + 1, end) if lines[j].startswith("UnitLifecycle")]
            at = entries[place_after([n for _, n in entries], a.module)][0]
            lines.insert(at + 1, new_line)
            delta += len(names)
    # The print-form case.
    pattern = re.compile(rf'replace_in "tacenta-proofs/translation/Translation/{a.module}\.lean" \$\'#guard_msgs in\\n#print ')
    existing = [k for k, l in enumerate(lines) if pattern.match(l)]
    if a.print_form_case is None or not pins["print"]:
        if a.print_form_case and not pins["print"]:
            refuse(f"{a.module}.lean has no `#print` pin for a print-form case")
    if a.print_form_case is not None and pins["print"] and not existing:
        choice = a.print_form_case if a.print_form_case != "auto" else next(
            (n for n in pins["print"] if n.endswith("Shape")), pins["print"][0])
        if choice not in pins["print"]:
            refuse(f"{choice} has no `#print` pin in {a.module}.lean")
        full = f"Tacenta.{a.module}.{choice}"
        case = f"definition-pin-check-form-{choice}"
        if any(f'"{case}"' in l for l in lines):
            case = f"definition-pin-check-form-{a.module}-{choice}"
        anchor = one([k for k, l in enumerate(lines)
                      if l.startswith("# A definition on REQUIRED_PRINT_FORM is held by `#print`: its pin rewritten as")],
                     f"{NEGATIVES_SH}: the comment that begins `# A definition on REQUIRED_PRINT_FORM is held by`")
        rel = f"tacenta-proofs/translation/Translation/{a.module}.lean"
        block = [f"# `{a.module}`'s `{choice}` is on REQUIRED_PRINT_FORM: its pin rewritten as `#check @` is refused.",
                 "make_case",
                 f"replace_in \"{rel}\" $'#guard_msgs in\\n#print {full}\\n' $'#guard_msgs in\\n#check @{full}\\n'",
                 f"expect_fail \"{case}\" \"is \\`#check @{full}\\`, which prints the type and not the body\" --check",
                 ""]
        cases = [(k, m.group(1)) for k, l in enumerate(lines[:anchor])
                 for m in [re.match(r'replace_in "tacenta-proofs/translation/Translation/(UnitLifecycle\w+)\.lean" '
                                    r"\$'#guard_msgs in\\n#print ", l)] if m]
        if cases:
            k = cases[place_after([n for _, n in cases], a.module)][0]
            at = next(j for j in range(k, len(lines)) if lines[j].startswith("expect_fail ")) + 2
        else:
            at = anchor
        lines[at:at] = block
        delta += 1
    tree.write(NEGATIVES_SH, "\n".join(lines))
    return delta


def edit_count(tree, delta):
    if delta:
        old = tree.read(COUNT).strip()
        if not re.fullmatch(r"[0-9]+", old):
            refuse(f"{COUNT} does not hold one whole number")
        tree.write(COUNT, f"{int(old) + delta}\n")


def pins_step(tree, a):
    if a.lean:
        module = tree.root / f"tacenta-proofs/translation/Translation/{a.module}.lean"
        if a.check:
            refuse("--lean writes the pins section; run it without --check")
        status = subprocess.run([sys.executable, str(tree.root / "tacenta-proofs/scripts/genpins.py"), str(module)])
        if status.returncode:
            refuse("genpins.py did not write the pins section")
        a.wrote_pins = True
    attest = load_attest(tree.root / ATTEST)
    pins = read_pins(tree, a, attest)
    edit_attest(tree, a, pins)
    delta = edit_negative_lists(tree, a, pins)
    edit_count(tree, delta)
    return pins, delta


# ---- running it ---------------------------------------------------------------------------------------------

def regenerate(root):
    for command in ([sys.executable, "tooling/gate-inventory.py", "--write"],
                    [sys.executable, "tacenta-proofs/scripts/attest.py"]):
        result = subprocess.run(command, cwd=root, capture_output=True, text=True)
        print(f"new-lifecycle-module: {' '.join(command[1:])}: exit {result.returncode}")
        if result.returncode:
            sys.stdout.write(result.stdout[-4000:])
            sys.stderr.write(result.stderr[-4000:])
            return False
    return True


LEFT = """What is left, by hand:
  - the proof in {module_rel}, and its controls in {script_rel} (MUTANTS and the labels), with the
    script's counts in tacenta-proofs/scripts/negatives-control-counts.json edited to match
    (`python3 tacenta-proofs/scripts/check-negatives-control-counts.py` names each class that differs);
  - then `python3 tacenta-proofs/scripts/new-lifecycle-module.py pins --module {module} --lean`;
  - the module's section of tacenta-proofs/CLAIMS.md (attest.py --check holds every pinned theorem to it),
    LIMITATIONS.md, the Session row of ASSURANCE.md, GAP-REGISTER.md and both READMEs;
  - every SCAFFOLD-TODO this wrote (`python3 tooling/check-proof-module-preflight.py {module}` lists them)."""


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="step", required=True)
    s = sub.add_parser("scaffold")
    s.add_argument("--module", required=True)
    s.add_argument("--negatives", required=True)
    s.add_argument("--part", required=True)
    s.add_argument("--description", required=True)
    s.add_argument("--imports", default="Translation.UnitLifecycleT3")
    s.add_argument("--phase")
    s.add_argument("--label")
    p = sub.add_parser("pins")
    p.add_argument("--module", required=True)
    p.add_argument("--description")
    how = p.add_mutually_exclusive_group()
    how.add_argument("--lean", action="store_true", help="write the pins section with genpins.py first")
    how.add_argument("--keep-pins", action="store_true", help="read the pins section as it is (the default)")
    form = p.add_mutually_exclusive_group()
    form.add_argument("--print-form-case", default="auto")
    form.add_argument("--no-print-form-case", dest="print_form_case", action="store_const", const=None)
    for q in (s, p):
        q.add_argument("--check", action="store_true", help="print the edits and write nothing")
        q.add_argument("--no-regenerate", action="store_true", help="do not run gate-inventory.py and attest.py")
        q.add_argument("--root", type=Path, default=ROOT)
    a = parser.parse_args()
    root = a.root.resolve()
    tree = Tree(root)
    try:
        if not MODULE_NAME.fullmatch(a.module):
            refuse(f"{a.module} is not a module name `UnitLifecycle<Name>`")
        if a.step == "scaffold":
            if not NEGATIVES_NAME.fullmatch(a.negatives):
                refuse(f"{a.negatives} is not a negatives script name `check-<name>-negatives.py`")
            a.phase = a.phase or a.negatives[len("check-"):-len("-negatives.py")]
            if not PHASE_NAME.fullmatch(a.phase):
                refuse(f"{a.phase} is not a phase name")
            a.label = a.label or f"{a.phase} proof-dependency control"
            if not re.fullmatch(r"Translation\.\w+", a.imports):
                refuse(f"{a.imports} is not a translation module")
            if "\n" in a.description or TODO in a.description:
                refuse("the description is one line")
            scaffold(tree, a)
        else:
            module_text = (root / f"tacenta-proofs/translation/Translation/{a.module}.lean")
            if not module_text.exists():
                refuse(f"{a.module}.lean does not exist; run `scaffold` first")
            if a.description is None:
                found = re.search(rf"^`{a.module}\.lean`: (.*)$", (root / AUDIT).read_text(), re.M)
                a.description = (found.group(1).split(f" {TODO}")[0].rstrip(".") if found
                                 else f"The results of `{a.module}`")
            pins, delta = pins_step(tree, a)
    except Refused as error:
        written = ("genpins.py wrote the module's pins section; nothing else was written"
                   if getattr(a, "wrote_pins", False) else "nothing was written")
        print(f"new-lifecycle-module: REFUSED: {error}; {written}", file=sys.stderr)
        return 2
    changed = tree.changed()
    if a.check:
        sys.stdout.write(tree.diff())
        print(f"new-lifecycle-module: --check: {len(changed)} file(s) would change: {', '.join(changed) or 'none'}")
        return 0
    tree.commit()
    print(f"new-lifecycle-module: {a.step}: {len(changed)} file(s) changed: {', '.join(changed) or 'none'}")
    if a.step == "pins":
        print(f"new-lifecycle-module: {len(pins['axiom'])} axiom pins, {len(pins['statement'])} statement pins, "
              f"{len(pins['print'])} definitions on the print form, {len(pins['compiler'])} compiler-trusted; "
              f"the attestation negatives gain {delta} case(s)")
    if changed and not a.no_regenerate and not regenerate(root):
        print("new-lifecycle-module: the edits were written; a generator refused (see above): fix that, then run "
              "`bash tooling/regenerate-generated.sh`", file=sys.stderr)
        return 3
    if a.step == "scaffold":
        print(LEFT.format(module=a.module, module_rel=f"tacenta-proofs/translation/Translation/{a.module}.lean",
                          script_rel=f"tacenta-proofs/scripts/{a.negatives}"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
