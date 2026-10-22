#!/usr/bin/env python3
"""Write the `## Pins` section of a translation module from what Lean prints.

    python3 tacenta-proofs/scripts/genpins.py <Translation/Module.lean> [--check] [--lean-json FILE]

A proof module ends with a section of pins: for each theorem, its axioms (`#print axioms`) and its statement
(`#check @`), and for each definition, its body (`#print`), each under `#guard_msgs` with the message Lean
printed, so that the build fails when a result starts resting on something new or its statement changes.
`attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`, `REQUIRED_PRINT_FORM`).
This writes that section, so that nobody copies Lean's messages by hand:

  1. the module's text up to `/-! ## Pins` (the old section is dropped);
  2. its declarations, fully qualified by the `namespace` blocks around them: each `theorem` and `lemma`
     gets an axiom pin and a statement pin, each `def`, `abbrev`, `structure` and `inductive` a `#print` pin,
     in the order they are declared; a pin of the old section that names something else (a structure's field,
     a declaration of another namespace) is kept, after them, in its old order;
  3. one run of `lake env lean --json` on a copy of the text with those commands appended, in a temporary
     directory (never in the tree, where a build would pick it up);
  4. each command's one message, which must be `info`, as its pin.

It refuses, and writes nothing, when Lean reports an error, when a command gets no message or more than one,
when a message is not `info`, and when a `private` declaration would need a pin (its name is not the one
written). `--check` writes nothing and fails if the section would change. `--lean-json FILE` reads Lean's
messages from FILE instead of running Lean (for the controls; the line numbers must be those of the probe), and
`--package DIR` runs Lean in another Lake package than the module's.

What it does not do: decide which results deserve a pin. Every declaration gets one; delete a pin and its entry
in `attest.py` by hand if it should not have one (`new-lifecycle-module.py pins` then follows the section).
"""
import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HEADER = ("\n/-! ## Pins\n\nThe constants each result depends on, and the statement of each result and definition, "
          "held by the\nbuild.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,\n"
          "`REQUIRED_PRINT_FORM`). -/\n\n")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?P<mods>(?:private |protected |noncomputable |partial |unsafe )*)"
                  r"(?P<kind>theorem|lemma|def|abbrev|structure|inductive)\s+(?P<name>[^\s:({\[]+)")
SET_OPTION_IN = re.compile(r"^set_option\s+\S+\s+\S+\s+in\s+(?P<rest>.*)$")
SCOPE = re.compile(r"^(?P<kw>namespace|section|end)(?:\s+(?P<name>\S+))?\s*$")
OLD_PIN = re.compile(r"#guard_msgs in\n(?P<cmd>#print axioms \S+|#check @\S+|#print \S+)\n")


class Refused(Exception):
    pass


def split_pins(text):
    cut = text.find("\n/-! ## Pins")
    body = text if cut < 0 else text[:cut]
    return body.rstrip("\n") + "\n", ("" if cut < 0 else text[cut:])


def declarations(body):
    """[(kind, full name)] in order, with the `namespace` blocks applied; a block comment is skipped."""
    out, stack, in_comment = [], [], 0
    for line in body.split("\n"):
        stripped = line.strip()
        if in_comment:
            in_comment += stripped.count("/-") - stripped.count("-/")
            continue
        if stripped.startswith("/-") and "-/" not in stripped:
            in_comment = 1
            continue
        m = SET_OPTION_IN.match(line)
        if m:
            line = m.group("rest")
        scope = SCOPE.match(line)
        if scope:
            kw, name = scope.group("kw"), scope.group("name")
            if kw == "namespace":
                stack.append(("namespace", name))
            elif kw == "section":
                stack.append(("section", name))
            elif stack:
                stack.pop()
            continue
        m = DECL.match(line)
        if m:
            if "private" in m.group("mods"):
                raise Refused(f"`{m.group('name')}` is private: its pin would not name it; pin it by hand")
            prefix = ".".join(n for k, n in stack if k == "namespace")
            name = m.group("name")
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                full = f"{prefix}.{name}" if prefix else name
            out.append(("theorem" if m.group("kind") in ("theorem", "lemma") else "def", full))
    return out


def commands(body, old_section):
    decls = declarations(body)
    theorems = [n for k, n in decls if k == "theorem"]
    defs = [n for k, n in decls if k == "def"]
    cmds = ([f"#print axioms {n}" for n in theorems] + [f"#check @{n}" for n in theorems]
            + [f"#print {n}" for n in defs])
    for m in OLD_PIN.finditer(old_section):
        if m.group("cmd") not in cmds:
            cmds.append(m.group("cmd"))
    return cmds, theorems, defs


def run_lean(probe_text, translation_dir):
    with tempfile.TemporaryDirectory(prefix="genpins-") as tmp:
        probe = Path(tmp) / "PinProbe.lean"
        probe.write_text(probe_text)
        try:
            result = subprocess.run(["lake", "env", "lean", "--json", str(probe)], cwd=translation_dir,
                                    capture_output=True, text=True)
        except OSError as error:
            raise Refused(f"lake did not start: {error}")
        return result.stdout


def messages(output, start, count):
    by_line = {}
    for raw in output.splitlines():
        try:
            message = json.loads(raw)
        except ValueError:
            continue
        line, severity = message["pos"]["line"], message["severity"]
        if severity == "error":
            raise Refused(f"Lean reports an error at line {line} of the probe: {message['data'].strip()[:300]}")
        if line < start:
            continue
        by_line.setdefault(line, []).append((severity, message["data"]))
    blocks = []
    for k in range(count):
        found = by_line.get(start + k, [])
        if len(found) != 1:
            raise Refused(f"command {k + 1} of {count} (probe line {start + k}) got {len(found)} messages")
        severity, data = found[0]
        if severity != "information":
            raise Refused(f"command {k + 1} (probe line {start + k}) got a {severity} message: {data[:200]}")
        blocks.append(data.rstrip())
    return blocks


def section(cmds, blocks):
    return HEADER + "\n".join(f"/--\ninfo: {data}\n-/\n#guard_msgs in\n{cmd}\n" for cmd, data in zip(cmds, blocks))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("module", type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--lean-json", type=Path)
    parser.add_argument("--package", type=Path, help="the Lake package to run Lean in (default: the module's)")
    args = parser.parse_args()
    module = args.module.resolve()
    translation_dir = args.package.resolve() if args.package else \
        next((p for p in module.parents if (p / "lakefile.toml").exists()), None)
    try:
        if translation_dir is None:
            raise Refused(f"{module} is not inside a Lake package")
        text = module.read_text()
        body, old_section = split_pins(text)
        cmds, theorems, defs = commands(body, old_section)
        if not cmds:
            raise Refused("the module declares nothing to pin")
        probe_text = body + "\n" + "\n".join(cmds) + "\n"
        start = (body + "\n").count("\n") + 1
        output = args.lean_json.read_text() if args.lean_json else run_lean(probe_text, translation_dir)
        blocks = messages(output, start, len(cmds))
    except Refused as error:
        print(f"genpins: REFUSED: {error}; nothing was written", file=sys.stderr)
        return 2
    new = body + section(cmds, blocks)
    extra = len(cmds) - 2 * len(theorems) - len(defs)
    summary = f"{len(theorems)} theorems, {len(defs)} definitions" + (f", {extra} kept pins" if extra else "")
    if args.check:
        if new != text:
            print(f"genpins: {module.name}: the pins section is not what Lean prints now ({summary})", file=sys.stderr)
            return 1
        print(f"genpins: {module.name}: the pins section is current ({summary})")
        return 0
    module.write_text(new)
    print(f"genpins: {module.name}: wrote {len(cmds)} pins ({summary})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
