#!/usr/bin/env python3
"""Trip on a numeric bound that forces its subject to zero on some target.

The defect this exists for: until 2026-09-10 `receive_no_panic` carried

    (hs : max state.skipped.val.length MAX_SKIPPED_STORE.val + U32.max ≤ Usize.max)

Aeneas models `usize` at the platform width. On a 32-bit target `Usize.max` and
`U32.max` are the same number, so the hypothesis demanded a store with nothing
in it, and every theorem carrying it was vacuous on a platform this workspace
compiles for. The documentation called it a genuine constraint for months.

THE CLASS. A comparison between an additive term that is one integer type's
maximum `A` and a bound that is another type's maximum `B`, where `A`'s maximum
is at least `B`'s on some target, 32- or 64-bit. There the bound forces what it
constrains down to zero. The forms recognised, each also with `<` or `>`:

    x + A ≤ B    A + x ≤ B    B ≥ x + A    B ≥ A + x    x ≤ B - A    B - A ≥ x

with `≤` or `<=`, and `≥` or `>=`. `A` and `B` may be written `T.max` or
`T.rMax`, qualified by `Std.` or `Aeneas.Std.`, as `UScalar.max .T` or
`IScalar.max .T`, or as the literal value of a fixed-width unsigned maximum.
Parentheses, a `(_ : Nat)` ascription and `↑` around them are ignored. A bound
whose right side carries on with more arithmetic, as in
`≤ Usize.max + U32.max`, is not matched. `usize` and `isize` differ by target,
so `U32` against `Usize` is refused and `U32` against `U64` is not. Maxima are
compared by value on each target, so `I32` against `Usize` is not refused.

WHERE. Every first-party Lean file: the model, its properties and vector
generator, the model-layer proofs, the translation package including its
generated files and its root, and the two lakefiles written in Lean. A scan directory or root file that is
missing, a symbolic link under them, a file that is not UTF-8, and a comment or
string that never terminates are all reported and never skipped. Comments,
docstrings, string literals including raw strings, and character literals are
removed before matching. Matching is confined to one declaration at a time, so
a maximum in one declaration is never joined to a bound in the next.

WHAT IT ALLOWS. The shape may appear in exactly the two declarations named in
`ALLOW`, the Lean refutations proving the rule right. They are identified by
their full names including namespace, and accepted only while each takes
`h32 : Usize.max = U32.max` as a binder before its colon. Each must still state
the shape in its statement, not only inside its proof, so the justification
cannot be emptied while the rule stays.

WHAT IT IS NOT. A tripwire for the spellings this tree uses, not a proof that no
bound forces its subject to zero. It does not see through an `abbrev`, `def`,
`notation` or `macro` that stands for a maximum; `LE.le a b` written as an
application; `UScalar.size` or any form not listed above; an addend further
from its relation than the matching window; or a precondition unsatisfiable for
any other reason, such as two contradictory hypotheses, a bound against the
wrong constant, or `2 * x` near a ceiling. Whether the tree's numeric
preconditions are satisfiable in general is not established by this script or
anywhere else, and `LIMITATIONS.md` says so.
"""
import argparse
import os
import re
import sys

# The value of each integer type's maximum on a 32-bit and on a 64-bit target.
MAXV = {
    "U8": (2**8 - 1, 2**8 - 1), "U16": (2**16 - 1, 2**16 - 1),
    "U32": (2**32 - 1, 2**32 - 1), "U64": (2**64 - 1, 2**64 - 1),
    "U128": (2**128 - 1, 2**128 - 1), "Usize": (2**32 - 1, 2**64 - 1),
    "I8": (2**7 - 1, 2**7 - 1), "I16": (2**15 - 1, 2**15 - 1),
    "I32": (2**31 - 1, 2**31 - 1), "I64": (2**63 - 1, 2**63 - 1),
    "I128": (2**127 - 1, 2**127 - 1), "Isize": (2**31 - 1, 2**63 - 1),
}
# The literal value of each fixed-width unsigned maximum.
LITERAL = {str(v[0]): t for t, v in MAXV.items()
           if t.startswith("U") and t != "Usize"}
TYPES = "|".join(sorted(MAXV, key=len, reverse=True))


def dangerous(a, b):
    """Does `x + a ≤ b` force `x` to zero on some target?"""
    return any(MAXV[a][i] >= MAXV[b][i] for i in (0, 1))


MAX_NAMED = re.compile(
    r"(?<![\w.])(?:Aeneas\.)?(?:Std\.)?(" + TYPES + r")\.(?:max|rMax)(?![\w'])")
MAX_SCALAR = re.compile(
    r"(?<![\w.])(?:Aeneas\.)?(?:Std\.)?(?:UScalar|IScalar)\.max\s*\.(" + TYPES
    + r")(?![\w'])")
MAX_LITERAL = re.compile(
    r"(?<![\w.#])(" + "|".join(sorted(LITERAL, key=len, reverse=True))
    + r")(?![\w.#])")
ASCRIBED = re.compile(r"(«\w+»)\s*:\s*(?:Nat|ℕ|Int|ℤ)(?![\w.'])")


def normalise(t):
    """Canonicalise every recognised spelling of a maximum to «T», drop the
    wrapping that does not change the bound, and make relations uniform."""
    t = MAX_NAMED.sub(lambda m: "«%s»" % m.group(1), t)
    t = MAX_SCALAR.sub(lambda m: "«%s»" % m.group(1), t)
    t = MAX_LITERAL.sub(lambda m: "«%s»" % LITERAL[m.group(1)], t)
    t = t.replace("↑", " ")
    t = re.sub(r"\s+", " ", t)
    t = ASCRIBED.sub(r"\1", t)
    t = re.sub(r"[()]", " ", t)
    t = t.replace("<=", "≤").replace(">=", "≥")
    return re.sub(r"\s+", " ", t)


S = r" ?"
M = r"«(\w+)»"
LE = r"(≤|<)"
GE = r"(≥|>)"
END = r"(?! ?[-+*/])"
# `B` on the left of a relation must not itself be part of a larger sum.
NO_ARITH_BEFORE = r"(?<![-+*/] )(?<![-+*/])"
# An addend written first may follow another `+`, but not a product or a
# difference, which would change what it means.
NO_SCALE_BEFORE = r"(?<![-*/] )(?<![-*/])"
# No relation or logical connective in the gap, so one bound is never joined to
# another; a binder's colon stops it too.
GAP = r"[^≤≥<>=∧∨→↔,:;]{0,160}?"

# (form, pattern, group holding A, group holding B)
FORMS = [
    ("x + A ≤ B", re.compile(r"\+" + S + M + S + LE + S + M + END), 1, 3),
    ("A + x ≤ B", re.compile(NO_SCALE_BEFORE + M + S + r"\+" + GAP + LE + S + M
                             + END), 1, 3),
    ("B ≥ x + A", re.compile(NO_ARITH_BEFORE + M + S + GE + GAP + r"\+" + S + M
                             + END), 3, 1),
    ("B ≥ A + x", re.compile(NO_ARITH_BEFORE + M + S + GE + S + M + S + r"\+"),
     3, 1),
    ("x ≤ B - A", re.compile(LE + S + M + S + r"-" + S + M + END), 3, 2),
    ("B - A ≥ x", re.compile(NO_ARITH_BEFORE + M + S + r"-" + S + M + S + GE),
     2, 1),
]

DECL = re.compile(
    r"^[ \t]*"
    r"(?:(?:open|set_option)\b[^\n]*?\bin\b\s*)*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)"
    r"\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|axiom|opaque|example|"
    r"inductive)\b"
    r"(?:[ \t]+(?![:(\[{⦃])([^\s:(\[{⦃]+))?",
    re.M)
SCOPE = re.compile(r"^[ \t]*(namespace|section|end)\b[ \t]*([^\s]*)", re.M)
H32 = re.compile(
    r"\(\s*h32\s*:\s*(?:Aeneas\.)?(?:Std\.)?Usize\.max\s*=\s*"
    r"(?:Aeneas\.)?(?:Std\.)?U32\.max\s*\)")

SHAPES = "tacenta-proofs/translation/Translation/PreconditionShapes.lean"
ALLOW = {
    (SHAPES, "Tacenta.PreconditionShapes.old_store_bound_unsatisfiable_at_32"),
    (SHAPES, "Tacenta.PreconditionShapes.old_skip_bound_forces_empty_at_32"),
}

# Kept in step with the runner's skeleton in
# tooling/tests/run-check-precondition-shapes-cases.sh; the fail-shape-in-* and
# fail-missing-* cases go red if the two drift apart.
SCAN_DIRS = [
    "tacenta-model/Model",
    "tacenta-model/Properties",
    "tacenta-proofs/Proofs",
    "tacenta-proofs/translation/Translation",
]
# The packages that declare their modules by glob have no root file. The Lean
# files outside the scan directories are the vector generator, the translation
# package's root, and the two lakefiles written in Lean.
SCAN_FILES = [
    "tacenta-model/Vectors.lean",
    "tacenta-model/lakefile.lean",
    "tacenta-proofs/lakefile.lean",
    "tacenta-proofs/translation/Translation.lean",
]

BOUND = ("%s:%d:%d: `%s` against `%s` %s (form `%s`, in its %s). `%s`'s maximum is "
         "at least `%s`'s on some target, so this bound forces what it "
         "constrains to zero there and describes no state that has ever held "
         "anything. Bound by what the code actually enforces instead -- "
         "`receive` uses `MAX_SKIP`, because the code refuses larger requests "
         "before the addition.")
ALLOW_H32 = ("%s: `%s` is allow-listed as a refutation of this shape, and does "
             "not take `h32 : Usize.max = U32.max` as a binder before its "
             "colon. Without it the shape is an ordinary precondition, which is "
             "exactly what the allow-list must not excuse.")
ALLOW_GONE = ("%s: the allow-listed refutation `%s` no longer states the refused "
              "shape in its statement, or is gone. It is the proof this "
              "script's rule is right; the rule and its justification have to "
              "leave together.")
MISSING = ("%s is missing. Every scanned directory and root file must exist; a "
           "missing one would silently narrow what this checks.")
LINK = ("%s is a symbolic link. It would be walked or skipped depending on where "
        "it points; keep the real file in the tree instead.")
ENCODING = "%s is not valid UTF-8, so it cannot be checked."


class StripError(Exception):
    pass


IDENT = re.compile(r"[\w'.!?«»]")
CHAR_LIT = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")
RAW_OPEN = re.compile(r'r(#*)"')


def strip(src):
    """Blank out comments, string and character literals, keeping every newline
    so offsets still map to lines. Block comments nest in Lean."""
    out, i, n = [], 0, len(src)

    def blank(c):
        return "\n" if c == "\n" else " "

    def line_of(pos):
        return src.count("\n", 0, pos) + 1

    while i < n:
        c = src[i]
        prev = src[i - 1] if i else " "
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
                                 % line_of(start))
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
        elif c == "r" and not IDENT.match(prev) and RAW_OPEN.match(src, i):
            m = RAW_OPEN.match(src, i)
            close = '"' + m.group(1)
            j = src.find(close, m.end())
            if j == -1:
                raise StripError("unterminated raw string literal opened at "
                                 "line %d" % line_of(i))
            end = j + len(close)
            out.append("".join(blank(ch) for ch in src[i:end]))
            i = end
        elif c == "'" and not IDENT.match(prev) and CHAR_LIT.match(src, i):
            m = CHAR_LIT.match(src, i)
            out.append(" " * (m.end() - i))
            i = m.end()
        elif c == '"':
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
                                 % line_of(start))
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def namespace_at(events, offset):
    stack = []
    for off, kind, arg in events:
        if off >= offset:
            break
        if kind in ("namespace", "section"):
            stack.append((kind, arg))
        elif kind == "end":
            for idx in range(len(stack) - 1, -1, -1):
                if arg == "" or stack[idx][1] == arg:
                    del stack[idx:]
                    break
    return ".".join(a for k, a in stack if k == "namespace" and a)


def regions(text):
    """(start, end, qualified name or None, declaration match or None) for each
    declaration, plus the text before the first one."""
    decls = list(DECL.finditer(text))
    events = [(m.start(), m.group(1), m.group(2)) for m in SCOPE.finditer(text)]
    out = []
    first = decls[0].start() if decls else len(text)
    if first > 0:
        out.append((0, first, None, None))
    for k, m in enumerate(decls):
        end = decls[k + 1].start() if k + 1 < len(decls) else len(text)
        name = m.group(2)
        ns = namespace_at(events, m.start())
        q = (ns + "." + name) if (name and ns) else name
        out.append((m.start(), end, q, m))
    return out


OPENERS = "([{⦃⟨"
CLOSERS = ")]}⦄⟩"


def split_decl(text, start, end, m):
    """The binders before the top-level colon, the statement before the
    top-level `:=`, and the body after it."""
    i = m.end()
    depth, colon, assign = 0, None, None
    j = i
    while j < end:
        ch = text[j]
        if ch in OPENERS:
            depth += 1
        elif ch in CLOSERS:
            depth = max(0, depth - 1)
        elif depth == 0:
            if text.startswith(":=", j):
                assign = j
                break
            if ch == ":" and colon is None:
                colon = j
        j += 1
    stop = assign if assign is not None else end
    binders = text[i: colon if colon is not None else stop]
    return binders, (start, stop), (stop, end)


def collect(root, problems):
    files = []
    for d in SCAN_DIRS:
        base = os.path.join(root, d)
        if os.path.islink(base):
            problems.append(LINK % d)
            continue
        if not os.path.isdir(base):
            problems.append(MISSING % d)
            continue
        for dirpath, dirnames, filenames in os.walk(base, followlinks=False):
            for dn in list(dirnames):
                full = os.path.join(dirpath, dn)
                if os.path.islink(full):
                    problems.append(LINK % os.path.relpath(full, root))
                    dirnames.remove(dn)
            for fn in sorted(filenames):
                full = os.path.join(dirpath, fn)
                rel = os.path.relpath(full, root)
                if os.path.islink(full):
                    problems.append(LINK % rel)
                    continue
                if fn.lower().endswith(".lean"):
                    files.append(rel)
    for f in SCAN_FILES:
        full = os.path.join(root, f)
        if os.path.islink(full):
            problems.append(LINK % f)
            continue
        if not os.path.isfile(full):
            problems.append(MISSING % f)
            continue
        files.append(f)
    return sorted(set(files))


def max_token_offsets(raw):
    """Offsets in `raw` of every spelling `normalise` turns into «T», in order.

    Each recognised spelling becomes exactly one «T» and the rewrites keep
    their order, so the k-th «T» in the normalised text is the k-th offset
    here. That is what lets a hit found in normalised text be reported at its
    own line and column: without it, two sites in one declaration produce the
    same message and collapse into one, and a reader fixes one of them believing
    it was the only one. That happened, on the proof of `T3.receive_refines`,
    whose four restatements of the bound were reported as one."""
    offs = []
    for rx in (MAX_NAMED, MAX_SCALAR, MAX_LITERAL):
        offs.extend(m.start() for m in rx.finditer(raw))
    return sorted(offs)


def scan(rel, text, problems, stated):
    for start, end, q, m in regions(text):
        if m is not None:
            binders, stmt, body = split_decl(text, start, end, m)
        else:
            binders, stmt, body = "", (start, end), (end, end)
        line = text.count("\n", 0, start) + 1
        if m is None:
            where = "before any declaration"
        elif q is None:
            where = "in an unnamed declaration at line %d" % line
        else:
            where = "in `%s`, declared at line %d" % (q, line)
        # After `:=` a theorem has a proof; a definition, an assumption bundle
        # among them, has a body. Say which, so a bundle clause is not
        # reported as though it were a step inside a proof.
        body_label = "proof"
        if m is not None and m.group(1) not in ("theorem", "lemma", "example"):
            body_label = "definition"
        for part, (p0, p1) in (("statement", stmt), (body_label, body)):
            if p1 <= p0:
                continue
            raw = text[p0:p1]
            norm = normalise(raw)
            offs = max_token_offsets(raw)
            seen = set()
            for form, rx, ga, gb in FORMS:
                for hit in rx.finditer(norm):
                    a, b = hit.group(ga), hit.group(gb)
                    if a not in MAXV or b not in MAXV or not dangerous(a, b):
                        continue
                    # The position of A's own token in the file. A site is
                    # that token: two sites in one declaration, or two bounds
                    # on one line, are two problems; one bound that two forms
                    # both match names the same token and is one.
                    k = norm.count("«", 0, hit.start(ga))
                    pos = p0 + offs[k] if k < len(offs) else start
                    if (pos, a, b) in seen:
                        continue
                    seen.add((pos, a, b))
                    site = text.count("\n", 0, pos) + 1
                    col = pos - (text.rfind("\n", 0, pos) + 1) + 1
                    if (rel, q) in ALLOW:
                        if H32.search(binders):
                            if part == "statement":
                                stated.add((rel, q))
                            continue
                        problems.append(ALLOW_H32 % (rel, q))
                        continue
                    problems.append(BOUND % (rel, site, col, a, b, where, form,
                                             part, a, b))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(
        os.path.abspath(__file__))), help="repository root")
    args = ap.parse_args()

    problems, stated = [], set()
    files = collect(args.root, problems)
    for rel in files:
        try:
            with open(os.path.join(args.root, rel), encoding="utf-8") as fh:
                src = fh.read()
        except UnicodeDecodeError:
            problems.append(ENCODING % rel)
            continue
        try:
            text = strip(src)
        except StripError as exc:
            problems.append("%s: cannot be checked: %s" % (rel, exc))
            continue
        scan(rel, text, problems, stated)

    for rel, q in sorted(ALLOW - stated):
        problems.append(ALLOW_GONE % (rel, q))

    unique = list(dict.fromkeys(problems))
    if unique:
        for p in unique:
            print("::error::check-precondition-shapes: " + p, file=sys.stderr)
        print("check-precondition-shapes: %d problem(s)" % len(unique),
              file=sys.stderr)
        return 1
    print("check-precondition-shapes: %d first-party Lean files, no bound of the "
          "refused shape in a form this tripwire recognises (%d allow-listed "
          "refutations, each taking the 32-bit width as a binder and stating "
          "the shape). This is not a proof that no bound forces its subject to "
          "zero; the script's docstring lists what it misses."
          % (len(files), len(stated)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
