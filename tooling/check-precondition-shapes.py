#!/usr/bin/env python3
"""Refuse a numeric bound that forces its subject to zero on some target.

The defect this exists for: until 2026-09-10 `receive_no_panic` carried

    (hs : max state.skipped.val.length MAX_SKIPPED_STORE.val + U32.max ≤ Usize.max)

Aeneas models `usize` at the platform width. On a 32-bit target `Usize.max` and
`U32.max` are the same number, so the hypothesis demanded a store with nothing
in it, and every theorem carrying it was vacuous on a platform this workspace
compiles for. The documentation called it a genuine constraint for months.

The general shape is a bound `x + A.max ≤ B.max` (or `<`, or with the addend
written first) where the integer type `A` is at least as wide as `B` on some
target. On that target the bound forces `x` to zero. `usize` and `isize` are 32
bits on some targets and 64 on others, so `U32.max` against `Usize.max` is
refused and `U32.max` against `U64.max` is not.

What this checks. Every first-party Lean file, comments and string literals
removed first, in theorem binders, in `def ... : Prop` bodies, and anywhere
else the text appears -- the defect also lived in an assumption bundle, not
only in a signature -- including bounds split across lines.

What it allows. The shape may appear in exactly the declarations named in
`ALLOW`, which are the Lean proofs that the rule is right, and only while each
still takes `h32 : Usize.max = U32.max` as a binder: a declaration keeping its
allow-listed name but carrying the shape as an ordinary precondition is
refused. Every allow-listed declaration must still be present and still state
the shape, so the justification cannot be deleted while the rule stays.

What it does not see, stated so it is not mistaken for more: it catches this
one class and no other. A precondition that is unsatisfiable for any other
reason -- a contradiction between two hypotheses, a bound against the wrong
constant, `2 * x` where `x` is already near the ceiling -- passes. Whether the
tree's numeric preconditions are satisfiable in general is not established by
this script or anywhere else, and `LIMITATIONS.md` says so. It never skips: a
file it cannot strip cleanly is reported as a failure.
"""
import argparse
import os
import re
import sys

# (narrowest, widest) bit width of each integer type across the targets
# Aeneas models.
WIDTH = {
    "U8": (8, 8), "U16": (16, 16), "U32": (32, 32), "U64": (64, 64),
    "U128": (128, 128), "Usize": (32, 64),
    "I8": (8, 8), "I16": (16, 16), "I32": (32, 32), "I64": (64, 64),
    "I128": (128, 128), "Isize": (32, 64),
}
T = r"(?:Std\.)?(" + "|".join(WIDTH) + r")\.max\b"
# The addend last, and the addend first. `[^≤<]` stops at the first relation
# so a later, unrelated bound on the same line is not joined to this one.
ADDEND_LAST = re.compile(r"\+\s*" + T + r"\s*(≤|<)\s*" + T)
ADDEND_FIRST = re.compile(r"(?<![\w.])" + T + r"\s*\+[^≤<]{0,240}?(≤|<)\s*" + T)

DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|axiom|opaque)\s+"
    r"([^\s:(\[{]+)", re.M)
H32 = re.compile(r"\(\s*h32\s*:\s*(?:Std\.)?Usize\.max\s*=\s*(?:Std\.)?U32\.max\s*\)")

SHAPES = "tacenta-proofs/translation/Translation/PreconditionShapes.lean"
ALLOW = {
    (SHAPES, "old_store_bound_unsatisfiable_at_32"),
    (SHAPES, "old_skip_bound_forces_empty_at_32"),
}

SCAN_DIRS = [
    "tacenta-model/Model",
    "tacenta-model/Properties",
    "tacenta-proofs/Proofs",
    "tacenta-proofs/translation/Translation",
]


class StripError(Exception):
    pass


def strip(src):
    """Blank out comments and string literals, keeping every newline so that
    offsets still map to the right line. Block comments nest in Lean."""
    out, i, n = [], 0, len(src)
    blank = lambda c: "\n" if c == "\n" else " "
    while i < n:
        if src.startswith("/-", i):
            depth, start = 1, i
            out.append("  ")
            i += 2
            while i < n and depth:
                if src.startswith("/-", i):
                    depth += 1
                    out.append("  ")
                    i += 2
                elif src.startswith("-/", i):
                    depth -= 1
                    out.append("  ")
                    i += 2
                else:
                    out.append(blank(src[i]))
                    i += 1
            if depth:
                raise StripError("unterminated block comment opened at line %d"
                                 % (src.count("\n", 0, start) + 1))
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
        elif src[i] == '"':
            start = i
            out.append(" ")
            i += 1
            while i < n and src[i] != '"':
                if src[i] == "\\" and i + 1 < n:
                    out.append(blank(src[i]) + blank(src[i + 1]))
                    i += 2
                    continue
                out.append(blank(src[i]))
                i += 1
            if i >= n:
                raise StripError("unterminated string literal opened at line %d"
                                 % (src.count("\n", 0, start) + 1))
            out.append(" ")
            i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def enclosing(text, offset):
    """The name and signature of the declaration containing `offset`."""
    best = None
    for m in DECL.finditer(text, 0, offset + 1):
        best = m
    if best is None:
        return None, ""
    end = text.find(":=", best.start())
    sig = text[best.start(): end if end != -1 else offset]
    return best.group(2), sig


def lean_files(root):
    out = []
    for d in SCAN_DIRS:
        base = os.path.join(root, d)
        if not os.path.isdir(base):
            continue
        for dirpath, _, names in os.walk(base):
            for name in sorted(names):
                if name.endswith(".lean"):
                    out.append(os.path.relpath(os.path.join(dirpath, name), root))
    return sorted(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(
        os.path.abspath(__file__))), help="repository root")
    args = ap.parse_args()

    files = lean_files(args.root)
    if not files:
        print("check-precondition-shapes: no first-party Lean found under %s"
              % args.root, file=sys.stderr)
        return 1

    problems, accepted = [], set()
    for rel in files:
        with open(os.path.join(args.root, rel), encoding="utf-8") as fh:
            src = fh.read()
        try:
            text = strip(src)
        except StripError as exc:
            problems.append("%s: cannot be checked: %s" % (rel, exc))
            continue
        seen = set()
        for pat in (ADDEND_LAST, ADDEND_FIRST):
            for m in pat.finditer(text):
                a, b = m.group(1), m.group(3)
                if WIDTH[a][1] < WIDTH[b][0]:
                    continue  # the addend is narrower on every target
                line = text.count("\n", 0, m.start()) + 1
                if (line, a, b) in seen:
                    continue
                seen.add((line, a, b))
                name, sig = enclosing(text, m.start())
                if (rel, name) in ALLOW:
                    if H32.search(sig):
                        accepted.add((rel, name))
                        continue
                    problems.append(
                        "%s:%d: `%s` is allow-listed as a refutation of this "
                        "shape, and no longer takes `h32 : Usize.max = U32.max`. "
                        "Without it the shape is an ordinary precondition, which "
                        "is exactly what the allow-list must not excuse."
                        % (rel, line, name))
                    continue
                problems.append(
                    "%s:%d: `%s.max` is added to a bound against `%s.max`%s. "
                    "`%s` is at least as wide as `%s` on some target, so there the "
                    "bound forces what it is added to down to zero and describes no "
                    "state that has ever held anything. Bound by what the code "
                    "actually enforces instead -- `receive` uses `MAX_SKIP`, "
                    "because the code refuses larger requests before the addition."
                    % (rel, line, a, b,
                       (" in `%s`" % name) if name else "", a, b))

    for rel, name in sorted(ALLOW - accepted):
        problems.append(
            "%s: the allow-listed refutation `%s` no longer states the refused "
            "shape, or is gone. It is the proof this script's rule is right; the "
            "rule and its justification have to leave together."
            % (rel, name))

    if problems:
        for p in problems:
            print("::error::check-precondition-shapes: " + p, file=sys.stderr)
        print("check-precondition-shapes: %d problem(s)" % len(problems),
              file=sys.stderr)
        return 1
    print("check-precondition-shapes: %d first-party Lean files carry no bound "
          "that forces its subject to zero on some target (%d allow-listed "
          "refutations, both still taking the 32-bit width as a hypothesis)"
          % (len(files), len(accepted)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
