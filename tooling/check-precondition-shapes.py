#!/usr/bin/env python3
"""Trip on a numeric bound that forces its subject to zero on some target.

The defect this exists for: until 2026-09-10 `receive_no_panic` carried

    (hs : max state.skipped.val.length MAX_SKIPPED_STORE.val + U32.max ≤ Usize.max)

Aeneas models `usize` at the platform width. On a 32-bit target `Usize.max` and
`U32.max` are the same number, so the hypothesis demanded a store with nothing
in it, and every theorem carrying it was vacuous on a platform this workspace
compiles for. The documentation called it a genuine constraint for months.

This is a tripwire for a handful of textual forms of that defect. It is not a
proof that no bound in the tree forces its subject to zero, and an earlier
version of this docstring claiming more than that was wrong three times over.
What follows is exactly what it catches and, as far as three adversarial
reviews have found, what it does not.

WHAT IT CATCHES. A comparison between an additive term that is one integer
type's maximum `A` and a bound that is another's maximum `B`, where `A`'s
maximum is at least `B`'s on some target, 32- or 64-bit, in one of these forms,
each also with `<` or `>`, `<=` or `>=`:

    x + A ≤ B    A + x ≤ B    B ≥ x + A    B ≥ A + x    x ≤ B - A    B - A ≥ x

`A` and `B` are recognised when written as `T.max` or `T.rMax`, optionally
qualified by `_root_.`, `Aeneas.` or `Std.`; as `UScalar.max .T` or
`UScalar.max UScalarTy.T`, and the same for `IScalar`; as `core.num.T.MAX.val`
or `(core.num.T.MAX : T).val`; as `2 ^ N - 1` for a fixed width `N`; or as the
literal value of a fixed-width unsigned maximum. Parentheses, `↑`, and a
`(_ : Nat)`, `ℕ`, `Int` or `ℤ` ascription written directly on a maximum are
ignored. Maxima are compared by value on each target, so `U32` against `Usize`
is refused, `U32` against `U64` is not, and `I32` against `Usize` is not.

WHAT IT DOES NOT CATCH. At least these, all found by review:
  * an ascription on the side that is not a maximum, `U32.max + (s : Nat)`;
  * any of `:` `=` `=>` `,` `;` `∧` `∨` `→` `↔` between an addend written first
    and its relation, which ends the matching window, so `fun x => …` inside
    the addend hides the bound;
  * the room form, `U32.max ≤ Usize.max - s` or `Usize.max - s ≥ U32.max`;
  * a bound shifted by a constant: `≤ Usize.max - 1`, `< Usize.max + 1`,
    `s + U32.max - 1 < Usize.max`;
  * `T.size`, `LE.le` applied as a function, `.succ`, `2 * U32.max`, and the
    comparison under `¬` written with the relation reversed;
  * anything standing for a maximum through an `abbrev`, `def`,
    `irreducible_def`, `notation` or `macro`;
  * any precondition unsatisfiable for another reason: two contradictory
    hypotheses, a bound against the wrong constant, `2 * x` near a ceiling.

WHAT IT REFUSES THAT IS LEGITIMATE. A bound deliberately scoped to 64-bit
targets by a width hypothesis; the shape used as a decidable guard in
`if … then` or under `¬`; and a maximum placed beside an unrelated bound once
parentheses are removed, as in `min y (x + U32.max) ≤ Usize.max`.

HOW SITES ARE ATTRIBUTED. Matching runs one declaration at a time, found by a
keyword at the start of a line. A declaration introduced any other way --
`open … in theorem` on one line, `include … in`, `variable`, `notation`,
`macro_rules` -- is folded into the declaration before it. A site there is
still reported, because nothing is excused by region, but it is attributed to
the wrong declaration and can be joined to a bound in the other one. Each site
is reported at the line and column of `A`'s own token.

WHAT IS EXCLUDED. `PreconditionShapes.lean` is not scanned. It holds the two
Lean refutations that state the refused shape on purpose. The script checks
only that both refutations are still present by name. It does not check what
they say, and it does not look at anything else in that file. An earlier
version tried to excuse the refutations by name and binder instead, and review
found five ways to smuggle an ordinary precondition past that; an explicit
exclusion claims less and cannot be slipped past.

WHERE IT LOOKS. The model, its properties, the vector generator, the
model-layer proofs, the translation package including its generated files and
root, and the two lakefiles written in Lean. Every `.lean` under
`tacenta-model/` and `tacenta-proofs/` must be in that set, or the run fails;
directories named `.lake` or `Generated` are skipped, and Lean outside those two
package directories is not looked for. A missing path, a symbolic link, a
non-UTF-8 file, and a comment or string that never terminates are reported,
never skipped.
"""
import argparse
import bisect
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
LITERAL = {str(v[0]): t for t, v in MAXV.items()
           if t.startswith("U") and t != "Usize"}
TYPES = "|".join(sorted(MAXV, key=len, reverse=True))
WIDTHS = "128|64|32|16|8"


def dangerous(a, b):
    """Does `x + a ≤ b` force `x` to zero on some target?"""
    return any(MAXV[a][i] >= MAXV[b][i] for i in (0, 1))


# Every recognised spelling of a maximum, as one alternation with one named
# group per spelling. One regex means one left-to-right pass, and that is what
# makes the k-th marker in the normalised text the k-th match in the raw text.
_Q = r"(?:_root_\.)?(?:Aeneas\.)?(?:Std\.)?"
_SPELLINGS = [
    ("named", r"(?<![\w.])" + _Q + r"(?P<named>" + TYPES + r")\.(?:max|rMax)(?![\w'])",
     lambda g: g),
    ("dot", r"(?<![\w.])" + _Q + r"(?:UScalar|IScalar)\.(?:max|rMax)\s*\.(?P<dot>"
     + TYPES + r")(?![\w'])", lambda g: g),
    ("ty", r"(?<![\w.])" + _Q + r"(?:UScalar|IScalar)\.(?:max|rMax)\s+" + _Q
     + r"(?:UScalarTy|IScalarTy)\.(?P<ty>" + TYPES + r")(?![\w'])", lambda g: g),
    ("coreasc", r"\(\s*core\.num\.(?P<coreasc>" + TYPES
     + r")\.MAX\s*:\s*[\w.]+\s*\)\s*\.val(?![\w'])", lambda g: g),
    ("core", r"(?<![\w.])core\.num\.(?P<core>" + TYPES + r")\.MAX\.val(?![\w'])",
     lambda g: g),
    ("pow", r"(?<![\w.])2\s*\^\s*(?P<pow>" + WIDTHS + r")\s*-\s*1(?![\w.#])",
     lambda g: "U" + g),
    ("lit", r"(?<![\w.#])(?P<lit>" + "|".join(sorted(LITERAL, key=len, reverse=True))
     + r")(?![\w.#])", lambda g: LITERAL[g]),
]
MAXIMUM = re.compile("|".join("(?:%s)" % pat for _, pat, _ in _SPELLINGS))
_TYPE_OF = {name: fn for name, _, fn in _SPELLINGS}

# Private-use code points as markers: Lean source has no reason to contain
# them, unlike the guillemets Lean uses for identifiers such as `r.«end»`, which
# an earlier version used as markers and so miscounted.
OPEN_MARK, CLOSE_MARK = "", ""
M = OPEN_MARK + r"(\w+)" + CLOSE_MARK
ASCRIBED = re.compile("(" + OPEN_MARK + r"\w+" + CLOSE_MARK
                      + r")\s*:\s*(?:Nat|ℕ|Int|ℤ)(?![\w.'])")


def _type_of(m):
    name = m.lastgroup
    return _TYPE_OF[name](m.group(name))


def normalise(t):
    """Mark every recognised maximum, drop wrapping that does not change the
    bound, and make relations uniform."""
    t = MAXIMUM.sub(lambda m: OPEN_MARK + _type_of(m) + CLOSE_MARK, t)
    t = t.replace("↑", " ")
    t = re.sub(r"\s+", " ", t)
    t = ASCRIBED.sub(r"\1", t)
    t = re.sub(r"[()]", " ", t)
    t = t.replace("<=", "≤").replace(">=", "≥")
    return re.sub(r"\s+", " ", t)


S = r" ?"
LE = r"(≤|<)"
GE = r"(≥|>)"
END = r"(?! ?[-+*/])"
NO_ARITH_BEFORE = r"(?<![-+*/] )(?<![-+*/])"
NO_SCALE_BEFORE = r"(?<![-*/] )(?<![-*/])"
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

# A declaration starts at a keyword at the start of a line, after any
# attributes (one level of bracket nesting inside them) and modifiers. No
# repeated `open … in` prefix: that was exponential on a long line, and a
# declaration missed here is folded into the one before rather than excused.
DECL = re.compile(
    r"^[ \t]*(?:@\[(?:[^\[\]\n]|\[[^\[\]\n]*\])*\][ \t]*\n?[ \t]*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)"
    r"\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|axiom|opaque|example|"
    r"inductive|irreducible_def)\b"
    r"(?:[ \t]+(?![:(\[{⦃])([^\s:(\[{⦃]+))?",
    re.M)
SCOPE = re.compile(
    r"^[ \t]*(?:noncomputable[ \t]+)?(namespace|section|mutual|end)\b[ \t]*([^\s]*)",
    re.M)

EXCLUDED = "tacenta-proofs/translation/Translation/PreconditionShapes.lean"
REFUTATIONS = ["old_store_bound_unsatisfiable_at_32",
               "old_skip_bound_forces_empty_at_32"]

# Kept in step with the runner's skeleton in
# tooling/tests/run-check-precondition-shapes-cases.sh.
SCAN_DIRS = [
    "tacenta-model/Model",
    "tacenta-model/Properties",
    "tacenta-proofs/Proofs",
    "tacenta-proofs/translation/Translation",
]
# The packages that declare their modules by glob have no root file.
SCAN_FILES = [
    "tacenta-model/Vectors.lean",
    "tacenta-model/lakefile.lean",
    "tacenta-proofs/lakefile.lean",
    "tacenta-proofs/translation/Translation.lean",
]
PACKAGE_DIRS = ["tacenta-model", "tacenta-proofs"]
SKIPPED_DIR_NAMES = {".lake", "Generated", ".git"}

BOUND = ("%s:%d:%d: `%s` against `%s` %s (form `%s`, in its %s). `%s`'s maximum "
         "is at least `%s`'s on some target, so this bound forces what it "
         "constrains to zero there and describes no state that has ever held "
         "anything. Bound by what the code actually enforces instead -- "
         "`receive` uses `MAX_SKIP`, because the code refuses larger requests "
         "before the addition.")
REFUTATION_GONE = ("%s: the refutation `%s` is gone. It is the Lean proof that "
                   "this script's rule is right, and this file is excluded from "
                   "the scan on the strength of holding it; the exclusion and "
                   "the refutation have to leave together.")
UNSCANNED = ("%s is a Lean file in a package directory that this script does not "
             "scan. Add its directory to SCAN_DIRS or the file to SCAN_FILES; a "
             "bound written there would never be checked.")
MISSING = ("%s is missing. Every scanned directory and root file must exist; a "
           "missing one would silently narrow what this checks.")
LINK = ("%s is a symbolic link. It would be walked or skipped depending on where "
        "it points; keep the real file in the tree instead.")
ENCODING = "%s is not valid UTF-8, so it cannot be checked."


class StripError(Exception):
    pass


# Characters that make a following `'` part of an identifier. `!` and `?` are
# not among them: in `!'"'` the `!` is boolean negation and the `'` opens a
# character literal, which an earlier version missed.
IDENT = re.compile(r"[\w'.«»]")
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
        if kind in ("namespace", "section", "mutual"):
            stack.append((kind, arg))
        elif kind == "end":
            for idx in range(len(stack) - 1, -1, -1):
                if arg == "" or stack[idx][1] == arg:
                    del stack[idx:]
                    break
    return ".".join(a for k, a in stack if k == "namespace" and a)


def regions(text):
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
    """The statement, up to the top-level `:=`, and what follows it."""
    depth, j = 0, m.end()
    while j < end:
        ch = text[j]
        if ch in OPENERS:
            depth += 1
        elif ch in CLOSERS:
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(":=", j):
            return (start, j), (j, end)
        j += 1
    return (start, end), (end, end)


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
                elif dn in SKIPPED_DIR_NAMES:
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
    scanned = set(files)
    # Every Lean file in the two package directories has to be in that set, so
    # a new library does not quietly go unchecked.
    for pkg in PACKAGE_DIRS:
        base = os.path.join(root, pkg)
        if not os.path.isdir(base):
            continue
        for dirpath, dirnames, filenames in os.walk(base, followlinks=False):
            dirnames[:] = [dn for dn in dirnames if dn not in SKIPPED_DIR_NAMES]
            for fn in filenames:
                if fn.lower().endswith(".lean"):
                    rel = os.path.relpath(os.path.join(dirpath, fn), root)
                    if rel not in scanned:
                        problems.append(UNSCANNED % rel)
    return sorted(scanned)


def scan(rel, text, problems):
    starts = [0] + [m.end() for m in re.finditer("\n", text)]

    def line_col(pos):
        line = bisect.bisect_right(starts, pos)
        return line, pos - starts[line - 1] + 1

    for start, end, q, m in regions(text):
        if m is not None:
            stmt, body = split_decl(text, start, end, m)
            body_label = ("proof" if m.group(1) in ("theorem", "lemma", "example")
                          else "definition")
        else:
            stmt, body, body_label = (start, end), (end, end), "proof"
        decl_line = line_col(start)[0]
        if m is None:
            where = "before any declaration"
        elif q is None:
            where = "in an unnamed declaration at line %d" % decl_line
        else:
            where = "in `%s`, declared at line %d" % (q, decl_line)
        for part, (p0, p1) in (("statement", stmt), (body_label, body)):
            if p1 <= p0:
                continue
            raw = text[p0:p1]
            norm = normalise(raw)
            offs = [mm.start() for mm in MAXIMUM.finditer(raw)]
            seen = set()
            for form, rx, ga, gb in FORMS:
                for hit in rx.finditer(norm):
                    a, b = hit.group(ga), hit.group(gb)
                    if a not in MAXV or b not in MAXV or not dangerous(a, b):
                        continue
                    # The group starts just after A's own marker, so the
                    # markers strictly before that one number A's token.
                    k = norm.count(OPEN_MARK, 0, hit.start(ga) - 1)
                    pos = p0 + offs[k]
                    if (pos, a, b) in seen:
                        continue
                    seen.add((pos, a, b))
                    line, col = line_col(pos)
                    problems.append(BOUND % (rel, line, col, a, b, where, form,
                                             part, a, b))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(
        os.path.abspath(__file__))), help="repository root")
    args = ap.parse_args()

    problems = []
    files = collect(args.root, problems)
    checked = 0
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
        if rel == EXCLUDED:
            for name in REFUTATIONS:
                if not re.search(r"^[ \t]*theorem[ \t]+%s\b" % re.escape(name),
                                 text, re.M):
                    problems.append(REFUTATION_GONE % (rel, name))
            continue
        checked += 1
        scan(rel, text, problems)
    if EXCLUDED not in files:
        problems.append(MISSING % EXCLUDED)

    unique = list(dict.fromkeys(problems))
    if unique:
        for p in unique:
            print("::error::check-precondition-shapes: " + p, file=sys.stderr)
        print("check-precondition-shapes: %d problem(s)" % len(unique),
              file=sys.stderr)
        return 1
    print("check-precondition-shapes: %d Lean files checked for the forms this "
          "script's docstring lists, none found; PreconditionShapes.lean "
          "excluded, both its refutations present. A tripwire for those forms, "
          "not a proof that no bound forces its subject to zero." % checked)
    return 0


if __name__ == "__main__":
    sys.exit(main())
