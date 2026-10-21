#!/usr/bin/env python3
"""Hold `lean_code` in `tacenta-proofs/scripts/attest.py` to the stripper it replaced.

`lean_code` blanks Lean comments, strings and char literals so that the scans of `attest.py` read code
only. It was a loop over every character; it is now a scan that copies ordinary code a stretch at a
time and stops only where a comment, a literal or a guillemet identifier can start, and it keeps each
result so a file read by several scans is stripped once. Neither change may alter a single character
of the output, since every scan of the attestation reads it. This compares the two:

  * `reference_lean_code` below is the character loop, copied verbatim from `attest.py` as it was
    before the change (with the two patterns it used), and is not to be edited: the block is pinned by
    its sha256 (`REFERENCE_SHA256`), so an edit to it, or its replacement by the new scan (which would
    agree with the new scan on every input), fails here, and the self-check shows the replacement is
    refused;
  * the stripper of `tacenta-proofs/scripts/check-lean-constructs.sh` (`strip_lean`, its default
    reading), which is a second copy of the same character loop, is read out of that script and
    compared with the reference with `keep_names` off (the scanner has no `keep_names`), so for that
    reading the reference is also tied to a copy that is in use;
  * the inputs are every tracked `*.lean` file of the tree, with `keep_names` off and on; a list of
    hand-written hostile inputs (nested and unterminated comments, comment openers and quotes in
    strings, in char literals and in guillemet names, raw strings with and without hashes and with a
    backslash in them, `r` and `'` after identifier characters, `!`, `?`, `λ`, CRLF, tabs, non-ASCII
    text, the empty input), each also with code after it; and some thousands of strings drawn from an
    alphabet of the characters the stripper reacts to, and of slices of real files with such
    characters inserted and deleted, from a fixed seed, so every run sees the same ones. Each group
    has a floor, so a shrunken corpus fails;
  * `lean_code` is called on a fresh copy of each input and again on another fresh copy, so the
    second answer comes from what the first kept, and a memo that keyed on the object rather than on
    the text would be seen returning another input's result.

It then shows it can fail: it applies each of thirteen single edits to the live source of the new
stripper, each a plausible slip (a nested comment not counted, the character after a top-level `/-`
not consumed, a backslash escape in a string not read, a raw string not seen or read with escapes, a
newline not kept, the identifier rule at `!` dropped, a guillemet name kept, the first character's
predecessor read from the end of the text, a memo keyed on the object), and requires that the inputs
above tell each edited stripper from the reference; the raw-string escape edit must be told by the
hostile inputs alone and by the generated inputs alone. An edit that no longer applies to the source is
a failure too, so the self-check cannot go stale silently.

The comparison is over these inputs only: it is a test, not a proof that the two agree on every
input.

Not checked here: that the reference reads Lean as Lean does. That is the business of the scans'
own cases (`check-attest-negatives.sh`, `run-lean-constructs-cases.sh`); this holds only that the
new scan says what the old loop said.
"""
import hashlib
import importlib.util
import os
import random
import re
import subprocess
import sys

ROOT = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(__file__), "..", ".."))
ATTEST = os.path.join(ROOT, "tacenta-proofs", "scripts", "attest.py")
CONSTRUCTS = os.path.join(ROOT, "tacenta-proofs", "scripts", "check-lean-constructs.sh")
SEED = 20261021
# Floors on the inputs, so that a shrunken corpus fails rather than passes on less.
MIN_FILES, MIN_HOSTILE, MIN_GENERATED = 200, 240, 7000
# The sha256 of the reference block below, from its first marker line to the end of its last. The block
# is the old loop and is not edited; if a reviewed change must touch it, the failure message prints the
# new digest to put here.
REFERENCE_SHA256 = "86fd7832c0e830033860020a42d4bd75228320ed01f3168f1b5efa11cf3c8cbf"
REFERENCE_START = "# ---- The reference: verbatim from attest.py before the change."
REFERENCE_END = "# ---- End of the reference. -----------------------------------------------------------------------\n"


# ---- The reference: verbatim from attest.py before the change. Do not edit. ----------------------
_CHAR_LITERAL = re.compile(r"'(?:\\(?:x[0-9A-Fa-f]{2}|u[0-9A-Fa-f]{4}|.)|[^\\'])'")  # Lean accepts a raw newline here
# The characters that can continue an identifier, for telling `r"..."`, `'a'`
# and `«...»` at the start of a token from the same characters inside one.
_IDENT_CHARS = re.compile(r"(?![\u03bb\u03a0\u03a3])[\w'!?«»]")  # `λ`, `Π`, `Σ` are tokens, not identifier characters


def lean_code(text, keep_names=False):
    """`text` with `--` line comments, `/- ... -/` block comments (docstrings
    included, and nested blocks), `"..."` and raw `r#"..."#` string literals
    and `'x'` character literals replaced by spaces, newlines kept, so that
    what remains is code and line numbers and offsets survive. Shared by every
    scan below: a keyword in prose or in a string is not a declaration, and a
    declaration is one wherever it sits on a line.

    An identifier written in guillemets (`«a b»`) is one token whatever it
    contains: a comment opener, a quote or a keyword inside it is part of the
    name. Its contents are replaced by `_` so a keyword scan does not see
    them, or kept as written when `keep_names` is set so the name can be read
    back. The output is the same length as the input, character for
    character, so an offset in one is an offset in the other.

    The same stripper as `scripts/check-lean-constructs.sh`, which keeps its
    own copy."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        ch = text[i]
        two = text[i:i + 2]
        if depth == 0 and two == "--":
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
            continue
        if two == "/-":
            # At the top level Lean consumes the character after `/-` without
            # reading it (see check-lean-constructs.sh); inside a comment it
            # reads `/-` then whatever follows.
            k = 3 if depth == 0 and i + 2 < n else 2
            depth += 1
            out.append("".join("\n" if c == "\n" else " " for c in text[i:i + k]))
            i += k
            continue
        if depth > 0 and two == "-/":
            depth -= 1
            out.append("  ")
            i += 2
            continue
        if depth > 0:
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        prev = text[i - 1] if i else " "
        # A `!` or `?` continues an identifier only when it ends one; alone it
        # is an operator and a char literal or raw string may follow it.
        in_ident = bool(_IDENT_CHARS.match(prev)) and (
            prev not in "!?" or (i >= 2 and bool(_IDENT_CHARS.match(text[i - 2])) and text[i - 2] not in "!?"))
        if ch == "«":
            j = text.find("»", i)
            j = n if j < 0 else j + 1
            inner = text[i:j]
            out.append(inner if keep_names else "".join(
                c if c in "«»\n" else "_" for c in inner))
            i = j
            continue
        if ch == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append("".join("\n" if c == "\n" else " " for c in text[i:j]))
            i = j
            continue
        if ch == "r" and not in_ident:
            raw = re.compile(r'r(#*)"').match(text, i)
            if raw:
                close = '"' + raw.group(1)
                j = text.find(close, raw.end())
                j = n if j < 0 else j + len(close)
                out.append("".join("\n" if c == "\n" else " " for c in text[i:j]))
                i = j
                continue
        if ch == "'" and not in_ident:
            lit = _CHAR_LITERAL.match(text, i)
            if lit:
                out.append("".join("\n" if c == "\n" else " " for c in text[i:lit.end()]))
                i = lit.end()
                continue
        out.append(ch)
        i += 1
    return "".join(out)


reference_lean_code = lean_code
del lean_code
# ---- End of the reference. -----------------------------------------------------------------------


def load_attest():
    spec = importlib.util.spec_from_file_location("attest_under_test", ATTEST)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_constructs_stripper():
    """`strip_lean` and the two patterns it uses, read out of the scanner's embedded program."""
    with open(CONSTRUCTS, encoding="utf-8") as fh:
        script = fh.read()
    start = script.find("\nCHAR_LITERAL = re.compile(")
    end = script.find("\ndef strip_toml(", start)
    if start < 0 or end < 0 or "\ndef strip_lean(" not in script[start:end]:
        fail("could not find strip_lean and its patterns in %s" % CONSTRUCTS)
    namespace = {"re": re}
    exec(compile(script[start:end], CONSTRUCTS + ":strip_lean", "exec"), namespace)
    return namespace["strip_lean"]


def fail(message):
    print("lean-code-differential: FAIL: " + message)
    sys.exit(1)


def lean_files():
    out = subprocess.run(["git", "ls-files", "-z", "--", "*.lean"], cwd=ROOT, capture_output=True,
                         check=True).stdout.decode("utf-8")
    paths = [p for p in out.split("\0") if p]
    texts = []
    for path in paths:
        with open(os.path.join(ROOT, path), encoding="utf-8", newline="") as fh:
            texts.append((path, fh.read()))
    return texts


HOSTILE = [
    "",
    "-", "/", "\"", "'", "r", "«", "»", "\\", "\n", "#",
    "--", "/-", "-/", "/--", "/-!", "/-/", "-/-", "/--/", "/-/- -/", "/- /- -/ -/ x",
    "/- /- -/ x", "/- unterminated", "/- a -/ b -/ c", "/-\n-/x", "/-\nx", "x /-", "x /-\n",
    "a -- b\nc", "a --", "a --\n", "-- /- \nx -/ y", "a -/ b", "/- -- -/ code",
    "\"--\" x", "\"/-\" x -/", "\"a\\\"b\" c", "\"a\\\\\" b \"c\"", "\"unterminated", "\"ends in \\",
    "\"\\", "\"multi\nline\" x", "\"\\\n\" y", "x\"y\"z",
    "r\"raw\" x", "r#\"a \" b\"# c", "r##\"a \"# b\"## c", "r#\"unterminated", "r#x", "r#", "r",
    "for\"x\"", "xr\"y\" z", "_r\"y\"", "(r\"y\")", "!r\"y\"", "a!r\"y\"", "a?r\"y\"", "λr\"y\"",
    "'a'", "'\\''", "'\\\\'", "'\\n'", "'\\x41'", "'\\u0041'", "'\\x4'", "'\\u004'", "'\n'", "''",
    "'ab'", "x'a'", "x' 'a'", "h'", "f x' y'", "!'\"'.isAlpha", "a!'\"' b", "a?'\"' b", "!!'\"'",
    "λ'\"' -- x", "Π'a'", "Σ'a'", "#check'\"'", "×ˢ'\"'", "'«'", "'\"' \"x\"", "' -- '",
    "«a b»", "«a -- b» c", "«a /- b» c -/", "«a \" b» \"c\"", "«unterminated", "«a\nb» c",
    "«»", "«a»«b»", "x«y»", "«a»'b'", "«a»r\"b\"", "« '\" »", "»", "a»b",
    "a\r\nb -- c\r\nd", "/- a\r\n-/ b", "\"a\r\nb\"", "\t-- tab\n\tx\t'\t'",
    "def café := \"é\" -- ünïcödé\nθ'", "def 名前 := '字' -- 注\n", "x := \"😀\" -- 😀\n«😀»",
    "theorem x : a = b := by\n  /-- doc -/\n  simp -- done\n",
    "/-- a docstring with \"quotes\" and 'chars' and -- dashes -/\ndef x := 1",
    "set_option warn.sorry false -- x\n", "#guard_msgs in\n#check @x -- pin\n",
    # A raw string reads no escape: a backslash in it is a character, and its first `"` (followed
    # by its hashes) ends it, so the code after is code.
    "def p := r\"C:\\\" \naxiom bad : False -- \"",
    "r\"\\\" x -- \"", "r\"a\\\"", "r\"\\\\\" y", "r#\"\\\"#\"# z", "r##\"\\\"#\"## z", "r\"\\\"", "r#\"\\\"#",
    "r\"\\\"\nx -- \"", "r\"a\\\"\ny", "r\"\\\\\"\ny", "r#\"\\\"#\"#\nz", "r##\"\\\"#\"##\nz",
]
# Each again with code after it, on the same line and the next, so that an input whose stripped text is
# all blank either way (`/--/` read as one comment or as two) shows whether the code after it is hidden.
HOSTILE = HOSTILE + [h + " code «a» 'b'\nmore -- x" for h in HOSTILE]

ALPHABET = ["-", "-", "/", "/", "\"", "'", "r", "r", "#", "«", "»", "\\", "\n", " ", "\t", "\r",
            "a", "x", "_", "!", "?", ".", "λ", "Π", "é", "u", "0", "4", "(", ")", "-/", "/-", "--",
            "\\x41", "\\u0041", "r#\"", "\"#", "r\"\\", "\\\"", "r#\"\\"]


def random_inputs(texts, rng):
    out = []
    for _ in range(4000):
        out.append("".join(rng.choice(ALPHABET) for _ in range(rng.randrange(0, 40))))
    seeds = HOSTILE + [t for _, t in texts]
    for _ in range(3000):
        base = rng.choice(seeds)
        if len(base) > 300:
            start = rng.randrange(0, len(base) - 300)
            base = base[start:start + rng.randrange(1, 300)]
        chars = list(base)
        for _ in range(rng.randrange(1, 6)):
            pos = rng.randrange(0, len(chars) + 1)
            if chars and rng.random() < 0.3:
                del chars[min(pos, len(chars) - 1)]
            else:
                chars.insert(pos, rng.choice(ALPHABET))
        out.append("".join(chars))
    return out


# Single edits to the new stripper, each a slip the comparison must catch: (name, where, old text, new
# text). `where` is the function edited (`lean_code`, `_lean_code_scan` or `_blank`), or the name of a
# module pattern that the edit replaces, in which case the new text is the replacement pattern. Each
# edit keeps the scan moving forward, so an edited scan ends on every input.
MUTANTS = [
    ("nested comment not counted", "_lean_code_scan", 'depth += 1 if text[p] == "/" else -1', "depth -= 1"),
    ("top-level /- takes two characters", "_lean_code_scan", "k = 3 if i + 2 < n else 2", "k = 2"),
    ("identifier rule at ! and ? dropped", "_lean_code_scan", 'prev not in "!?" or', "True or"),
    ("guillemet name kept", "_lean_code_scan", "out.append(inner if keep_names else",
     "out.append(inner if True else"),
    ("predecessor of the first character from the end", "_lean_code_scan",
     'prev = text[i - 1] if i else " "', "prev = text[i - 1]"),
    ("unterminated string ends early", "_lean_code_scan",
     "j = j + 1 if j < n and text[j] == '\"' else n", "j = j + 1 if j < n and text[j] == '\"' else j"),
    ("line comment runs to the end of the text", "_lean_code_scan", 'j = text.find("\\n", i)', "j = -1"),
    ("newline in a blanked stretch not kept", "_blank", 'if "\\n" not in segment:', "if True:"),
    ("backslash escape not read", "_STRING_BODY", None, r'"[^"]*'),
    ("raw string not seen", "_TOP_STOP", None, r'--|/-|["\'«]'),
    ("nested opener not seen", "_BLOCK_STOP", None, r"-/"),
    ("raw string reads escapes", "_lean_code_scan", "j = text.find(close, raw.end())",
     "j = text.find(close, raw.end()) if raw.group(1) else (lambda e: e if e < n and text[e] == '\"' else -1)"
     "(_STRING_BODY.match(text, raw.end() - 1).end())"),
    ("memo keyed on the object, not the text", "lean_code", "key = (text, bool(keep_names))",
     "key = (id(text), bool(keep_names))"),
]
# The edit above that only inputs with a backslash in a raw string can tell; the hostile inputs and
# the generated ones must each tell it on their own.
RAW_ESCAPE_MUTANT = "raw string reads escapes"


def mutant_strippers(attest):
    """(name, lean_code) for each edit: `lean_code` with an empty memo, built from the live source of
    attest.py with that edit applied."""
    import inspect
    for name, where, old, new in MUTANTS:
        namespace = dict(vars(attest))
        namespace["_LEAN_CODE_MEMO"] = {}
        if old is None:
            if not isinstance(namespace.get(where), type(re.compile(""))):
                fail("the self-check edit %r names %s, which is no longer a pattern of attest.py" % (name, where))
            namespace[where] = re.compile(new)
        else:
            source = inspect.getsource(getattr(attest, where))
            if source.count(old) != 1:
                fail("the self-check edit %r no longer applies once to %s" % (name, where))
            exec(compile(source.replace(old, new), "<mutant: %s>" % name, "exec"), namespace)
        # The functions read each other, the memo and the patterns from their globals, so the ones not
        # edited are rebuilt in the edited namespace.
        for other in ("_blank", "_lean_code_scan", "lean_code"):
            if other != where:
                exec(compile(inspect.getsource(getattr(attest, other)), "<mutant: %s>" % name, "exec"), namespace)
        yield name, namespace["lean_code"]


def fresh(text):
    """An equal string that is a new object (for any text of two characters or more), so that a call
    on it shares nothing with an earlier call on the same text but its content, and the object is
    freed when the call returns, as a scan's temporary would be."""
    return (text + " ")[:-1]


def stripped_twice(lean_code, text, keep):
    """`lean_code` on a fresh copy of `text`, then on another: the second answer comes from what the
    first kept."""
    return lean_code(fresh(text), keep_names=keep), lean_code(fresh(text), keep_names=keep)


def reference_block():
    with open(os.path.abspath(__file__), encoding="utf-8") as fh:
        source = fh.read()
    # At the start of a line, so the constants above, which spell the markers, are not taken for them.
    start = source.find("\n" + REFERENCE_START) + 1
    end = source.find("\n" + REFERENCE_END, start) + 1
    if start <= 0 or end <= start:
        fail("cannot find the reference block in %s" % __file__)
    return source[start:end + len(REFERENCE_END)]


def reference_pinned(block):
    return hashlib.sha256(block.encode("utf-8")).hexdigest() == REFERENCE_SHA256


def main():
    block = reference_block()
    if not reference_pinned(block):
        fail("the reference block (the old character loop) has changed: its sha256 is now %s, not the "
             "pinned %s. It is the loop lean_code is held to and is not edited; a change to it is a change "
             "to what this control checks, for review, that also updates REFERENCE_SHA256"
             % (hashlib.sha256(block.encode("utf-8")).hexdigest(), REFERENCE_SHA256))
    attest = load_attest()
    # The pin is what stops the reference being replaced by the new scan, which would agree with it on
    # every input: show that such a replacement is refused.
    import inspect
    swapped = re.sub(r"(?s)\ndef lean_code\(.*?\n    return \"\"\.join\(out\)\n",
                     lambda _: "\n" + inspect.getsource(attest._lean_code_scan).replace(
                         "def _lean_code_scan(text, keep_names):", "def lean_code(text, keep_names=False):"),
                     block, count=1)
    if swapped == block or reference_pinned(swapped):
        fail("the self-check that replaces the reference by the new scan was not refused by the pin")
    strip_lean = load_constructs_stripper()
    texts = lean_files()
    rng = random.Random(SEED)
    generated = random_inputs(texts, rng)
    for what, have, floor in (("tracked Lean files", len(texts), MIN_FILES),
                              ("hostile inputs", len(HOSTILE), MIN_HOSTILE),
                              ("generated inputs", len(generated), MIN_GENERATED)):
        if have < floor:
            fail("only %d %s, fewer than the floor of %d" % (have, what, floor))
    corpus = [t for _, t in texts] + HOSTILE + generated
    kinds = ["file"] * len(texts) + ["hostile"] * len(HOSTILE) + ["generated"] * len(generated)
    names = [p for p, _ in texts] + ["hostile #%d" % k for k in range(len(HOSTILE))] + \
        ["generated #%d" % k for k in range(len(generated))]

    compared = 0
    references = {}
    for name, text in zip(names, corpus):
        for keep in (False, True):
            want = reference_lean_code(text, keep_names=keep)
            references[(name, keep)] = want
            for attempt, got in zip(("first", "kept"), stripped_twice(attest.lean_code, text, keep)):
                if got != want:
                    at = next((k for k in range(min(len(got), len(want))) if got[k] != want[k]),
                              min(len(got), len(want)))
                    fail("lean_code (%s call, keep_names=%s) differs from the reference on %s at offset %d: "
                         "%r against %r" % (attempt, keep, name, at, got[at:at + 40], want[at:at + 40]))
                compared += 1
            if not keep and strip_lean(text) != want:
                fail("check-lean-constructs.sh's strip_lean differs from the reference on %s" % name)

    caught = []
    for mutant_name, stripper in mutant_strippers(attest):
        differs = {"file": 0, "hostile": 0, "generated": 0}
        for name, kind, text in zip(names, kinds, corpus):
            for keep in (False, True):
                try:
                    got = stripped_twice(stripper, text, keep)
                except Exception:
                    got = (None, None)
                want = references[(name, keep)]
                if got[0] != want or got[1] != want:
                    differs[kind] += 1
        if sum(differs.values()) == 0:
            fail("the self-check edit %r is not told from the reference by any input" % mutant_name)
        if mutant_name == RAW_ESCAPE_MUTANT and not (differs["hostile"] and differs["generated"]):
            fail("the self-check edit %r is not told from the reference by the hostile inputs alone and by "
                 "the generated inputs alone (%d and %d)" % (mutant_name, differs["hostile"], differs["generated"]))
        caught.append("%s (%d)" % (mutant_name, sum(differs.values())))

    print("lean-code-differential: lean_code matches the reference character loop on %d inputs "
          "(%d tracked Lean files, %d hostile, %d generated from seed %d), each with keep_names off and on, "
          "on a fresh copy and again on another from what it kept (%d comparisons); check-lean-constructs.sh's "
          "strip_lean matches the reference with keep_names off; the reference block matches its pinned "
          "sha256, and a reference replaced by the new scan is refused; the inputs tell each of %d edited "
          "strippers from the reference: %s"
          % (len(corpus), len(texts), len(HOSTILE), len(generated), SEED, compared, len(caught),
             "; ".join(caught)))


if __name__ == "__main__":
    main()
