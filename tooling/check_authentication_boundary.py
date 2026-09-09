#!/usr/bin/env python3
"""Fail if a function that consumes an unauthenticated message is unregistered,
or is registered under a shape its signature does not have.

The registry, `tacenta-core/AUTHENTICATION-BOUNDARY.md`, claims a *property*:
nothing durable moves until the authenticator verifies. This check cannot
read a body, so it checks the two things a signature and a table can carry --
that every function shaped like a receive path is written down, and that the
shape the table promises for it is the shape it has -- and it is built so
that neither direction can be satisfied by a name alone.

## What it does

Discovery is **by name**: a function is looked at when its name contains one of
the verbs `receive`, `decrypt`, `accept`, `process`, `commit`, `establish`,
`handle`, `ingest`, `verify`, `import`, `from_bytes`, `open`, `read`, or `parse`
(CR-09). A short list of pure functions that consume bundle material under a
verb-less name (`initiator_shared_secret`, `responder_shared_secret`) is added
explicitly. This is a name-based heuristic, not body analysis, and it says so.

Discovery covers private functions as well as `pub fn` (`Session::decrypt_ratchet`
is private), matches the verb anywhere in the name rather than only as a prefix
(`establish_responder`, `step_receive`), and identifies a function by
`(file, Type::name)` -- the enclosing `impl` type when there is one, so two
types in one file can each carry a `from_bytes` without colliding, and so a new
type with a method called `receive` is not covered by some other `receive`
already in the document. Pure byte-reading helpers (`read_key`, `read_u32`, and
the like) are exempted by name: the consuming path is the `from_bytes` that
calls them, which is registered. Both directions are checked: everything
discovered must be registered, and everything registered must still exist.

- **The registry is the tables, not the prose.** An entry is a row whose first
  cell is `` `path::name` ``, under one of three `###` headings, and the heading
  says what shape the function must have. "Transactional" rows must take
  `&self`; "Mutating" rows must take `&mut self`; "Orchestration" rows may be
  either, because the argument for them is in the row and the tests. A
  backticked name in prose registers nothing.
- **The shape is checked against the signature.** A transactional entry whose
  function has become `&mut self` fails, which is the regression that matters:
  the type stopped defending the property and the registry still says it does.
- **`#[cfg(test)]` counts only as the attribute directly on the item**, not as
  text nearby; a comment mentioning it exempts nothing. A `#[cfg(test)] mod`
  is removed by its own byte range (blanked in place, so line numbers hold),
  not by cutting the file at the first one, so real code below a test module is
  still discovered (CR-09). The walk that finds a module's closing brace, like
  every match in this file, reads a view of the source with every string,
  character literal, and comment blanked to spaces, so a `"{"` inside a test
  string cannot shift the span over the code that follows the module. The
  walk refuses to guess: a file whose braces do not balance in that view, or
  a module or `impl` block that never closes, is an error, not a silent
  truncation.
- **`const fn`, `unsafe fn`, `async fn`, and `extern "C" fn` are declarations
  too**, in any order of qualifiers; a qualifier is not a way out of discovery.
- **A declaration is discovered wherever a statement can begin**: at the start
  of a line, or after `{`, `;`, or `}` on the same line. Anchoring at the line
  start alone would miss `} fn receive(` and a one-line block, which is a way
  out of discovery that costs nothing to close.
- **Verbs match anywhere in the name**, so `step_receive` is discovered, with a
  small exemption list for accessors (`receive_count` and friends) and the pure
  `read_*` byte helpers.
- **`receiver_of` scans the whole parameter list for `&mut`** (CR-09), so a
  free function `fn receive(msg: &[u8], state: &mut State)` is classified as
  mutating on the strength of its second argument, not read as transactional
  from its first.
- **A `(file, Type::name)` seen twice is an error**, since one row cannot vouch
  for two functions.

What it does not do, and says so: it does not read a body. "Clones then
assigns after the tag verifies" is an argument, and arguments are for the rows
and for `tests/failed_decrypt_changes_nothing.rs`, which is the test that
actually holds the property.
"""

import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(
    subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
)
REGISTRY = ROOT / "tacenta-core" / "AUTHENTICATION-BOUNDARY.md"

# The crates on the path from the wire to a key. Deliberately not every crate:
# a check that flags noise is a check somebody switches off.
ZONES = [
    "tacenta-core/src/sessions",
    "tacenta-core/ratchet/src",
    "tacenta-core/spqr/src",
    "tacenta-core/triple/src",
    "tacenta-core/braid/src",
]

# Verbs a function that consumes a message goes by here, matched anywhere in
# the name rather than only as a prefix. The second group -- verify, import,
# from_bytes, open, read, parse -- covers the paths that take attacker-supplied
# or persisted bytes before anything authenticates them (CR-09): a bundle
# verifier, the persisted-state decoders, and any future `open_session` or
# `read_initial`.
FAMILY = (
    r"(receive|decrypt|accept|process|commit|establish|handle|ingest"
    r"|verify|import|from_bytes|open|read|parse)"
)

# A function declaration, `pub` or not, with its receiver captured: the text
# between the opening parenthesis and the first comma or closing parenthesis,
# which is `&self`, `&mut self`, `self`, or an ordinary first parameter.
# `const`, `async`, `unsafe`, and `extern` (with or without an ABI string;
# the string is blanked in the code view, so both spellings are matched) may
# precede `fn` in any order; a `const fn receive` is a receive.
QUALIFIERS = r'(?:(?:const|async|unsafe|extern(?:\s+"[^"]*")?)\s+)*'
# Where a declaration may begin: the start of a line, or after a `{`, `;`, or
# `}` earlier on it. The position is a statement position either way, and
# nothing else in Rust puts `fn` followed by a lower-case name there (a
# closure has no `fn`; `Fn(...)` and a `fn(...)` pointer type have no name).
STATEMENT_START = r"(?:^|(?<=[{;}]))(?P<indent>[ \t]*)"
DECL = re.compile(
    STATEMENT_START + r"(?:pub(?:\([^)]*\))?\s+)?" + QUALIFIERS + r"fn\s+"
    # The generic list may nest one level (`<F: Fn(&Msg) -> Option<Key>>`), which
    # a plain `<[^>]*>` cannot span; discovery must accept every declaration,
    # so the pattern spans one level of nesting.
    r"(?P<name>[a-z0-9_]*" + FAMILY + r"[a-z0-9_]*)\s*(?:<(?:[^<>]|<[^<>]*>)*>)?\s*\("
    r"(?P<first>[^,)]*)",
    re.M,
)

# Reading a counter or a chain is not consuming a message, and neither is
# initialising a party (`init_receiver` matches `receive` as a substring; it
# is the one `init_*` name that does, so it is exempted exactly rather than by
# prefix, and a future `init_from_bytes` is discovered). The `read_*` byte
# helpers are pure primitives the decoders call, not decoders themselves --
# they take an offset into a buffer and return one field -- so the consuming
# path is the `from_bytes` that calls them, which is registered; the helpers
# are exempted by name rather than each given a row (CR-09).
EXEMPT = {
    "receive_count",
    # The Triple's passthrough to the sparse ratchet's counter. Exempt for the
    # same reason `receive_count` is: it reads a counter and consumes nothing.
    # Named exactly rather than matched by a `_count` suffix, because widening
    # the rule of a gate is how a gate stops gating.
    "post_quantum_receive_count",
    "receive_chain",
    "receive_chain_key",
    "receive_chains",
    "init_receiver",
    "read_key",
    "read_optional_key",
    "read_u32",
    "read_u64",
    "read_auth",
    "read_epoch",
    "read_prekey_u32",
}

# Pure functions that consume attacker-supplied bundle material before anything
# authenticates it, but whose names carry none of the verbs above, so discovery
# by name would miss them (CR-09). Named explicitly so they are registered and
# shape-checked with the rest; their rows say why each is safe (they compute a
# value and mutate no state).
ALSO_DISCOVER = {
    "tacenta-core/src/sessions/mod.rs": ("initiator_shared_secret", "responder_shared_secret"),
}


def _explicit_decl(name: str) -> "re.Pattern":
    """A declaration matcher for one exact function name, capturing `name` and
    the start of the first parameter the way `DECL` does, so the same parameter
    extraction works on it."""
    return re.compile(
        STATEMENT_START + r"(?:pub(?:\([^)]*\))?\s+)?" + QUALIFIERS + r"fn\s+"
        r"(?P<name>" + re.escape(name) + r")\s*(?:<(?:[^<>]|<[^<>]*>)*>)?\s*\("
        r"(?P<first>[^,)]*)",
        re.M,
    )


EXPLICIT_DECL = {
    name: _explicit_decl(name) for names in ALSO_DISCOVER.values() for name in names
}

# Registry headings, and the receiver shape each one promises.
SHAPES = {
    "transactional": "&self",
    "orchestration": None,
    "mutating": "&mut self",
}
# Any heading level ends the current table section; only the three named
# `###` headings begin one. A `##` after the last table therefore closes it,
# so a row under it registers nothing rather than counting as "mutating".
HEADING = re.compile(r"^#{1,6}\s+(?P<title>.+)$", re.M)
# A row's first cell is `` `path::name` ``, where `name` may be qualified by a
# type (`State::from_bytes`) so two decoders in one file are distinct.
ROW = re.compile(r"^\|\s*`(?P<path>[A-Za-z0-9_./-]+\.rs)::(?P<name>[A-Za-z0-9_]+(?:::[a-z0-9_]+)?)`\s*\|", re.M)


def _split_top_level(params: str) -> list:
    """Split a parameter list on commas that are not inside brackets, so a
    parameter whose type itself contains a comma (`Foo<A, B>`, `[u8; N]`,
    `impl Fn(&A, &B)`) is not torn in two."""
    out = []
    depth = 0
    current = []
    for c in params:
        if c in "([<":
            depth += 1
        elif c in ")]>":
            depth -= 1
        if c == "," and depth == 0:
            out.append("".join(current))
            current = []
        else:
            current.append(c)
    if "".join(current).strip():
        out.append("".join(current))
    return out


# A `&mut` borrow, allowing an intervening lifetime (`&'a mut T`).
MUT_BORROW = re.compile(r"&\s*(?:'[a-z_]+\s+)?mut\b")


def receiver_of(params: str) -> str:
    """The shape of a function's parameters, as far as the property cares: can
    it mutate any state it is handed?

    The whole list is scanned, not just the first parameter (CR-09): a function
    such as `fn receive(msg: &[u8], state: &mut State)` mutates through its
    *second* argument and is every bit as much a mutation as `&mut self`, so any
    `&mut` parameter -- `&mut self` included -- makes the shape `&mut self`. A
    free function taking `state: &mut State` is the same shape as a method
    taking `&mut self`; the test is on the borrow, not on the word `self`.

    Failing that, the first parameter decides between a shared borrow (`&self`
    or `name: &T`), an owned `self`, and a free function."""
    if MUT_BORROW.search(params):
        return "&mut self"
    first = (_split_top_level(params) or [""])[0].strip()
    if first.startswith("&self") or re.match(r"^[a-z_]+\s*:\s*&", first):
        return "&self"
    if first == "self" or first.startswith("mut self") or first.startswith("self:"):
        return "self"
    return "free"


# The head of an `impl` block, capturing the type it is for. `impl Trait for
# Type` puts the type in the second group; a plain `impl Type` in the first.
IMPL_START = re.compile(
    r"^impl(?:\s*<(?:[^<>]|<[^<>]*>)*>)?\s+"
    r"(?P<a>[A-Za-z0-9_]+)(?:\s*<(?:[^<>]|<[^<>]*>)*>)?"
    r"(?:\s+for\s+(?P<b>[A-Za-z0-9_]+))?"
    r"[^{;]*\{",
    re.M,
)


def _impl_spans(text: str, rel: str):
    """Every `impl` block as `(type, start, end)`, so a function's enclosing
    type can be recovered. Rust does not nest `impl` blocks, so at most one span
    contains a given position. `text` is the code view (see `_code_view`), so
    the brace walk counts only braces that are code; a block that never
    closes is an error rather than a span to the end of the file."""
    spans = []
    for m in IMPL_START.finditer(text):
        ty = m.group("b") or m.group("a")
        end = _matching_brace(text, m.end() - 1)
        if end is None:
            _refuse(f"{rel}: the `impl {ty}` block at offset {m.start()} never closes")
        spans.append((ty, m.start(), end + 1))
    return spans


def _enclosing_type(spans, pos: int):
    """The type of the `impl` block containing `pos`, or `None` for a free
    function. A function is identified by `Type::name` when it has one, so that
    two types in one file can each carry a `from_bytes` without colliding on the
    `(file, name)` identity (CR-09)."""
    for ty, start, end in spans:
        if start <= pos < end:
            return ty
    return None


def _param_list(text: str, open_paren: int) -> str:
    """The text between the `(` at `open_paren` and its matching `)`."""
    depth = 0
    i = open_paren
    while i < len(text):
        c = text[i]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return text[open_paren + 1 : i]
        i += 1
    return text[open_paren + 1 :]


def _refuse(why: str):
    """Stop the check outright. Discovery that cannot see a file's structure
    must not guess at it: a guess that hides a function reads as a pass."""
    print(f"::error::{why}; refusing to guess at the file's structure", file=sys.stderr)
    sys.exit(1)


# The pieces of a Rust source that are not code, as far as brace counting and
# declaration matching care: line and block comments (block comments nest),
# ordinary and byte strings, raw strings with any number of hashes, and
# character and byte-character literals. A lifetime (`'a`) is a lone quote
# with no closing one and is left alone. Each is matched at a position and
# replaced, newlines kept, by spaces.
_LINE_COMMENT = re.compile(r"//[^\n]*")
_STRING = re.compile(r'(?:b|c)?"(?:[^"\\]|\\.|\\\n)*"', re.S)
_RAW_STRING_START = re.compile(r'(?:b|c)?r(?P<hashes>#*)"')
_CHAR = re.compile(r"b?'(?:[^'\\\n]|\\(?:[^u]|u\{[0-9a-fA-F_]{1,6}\}))'")


def _code_view(text: str) -> str:
    """`text` with every comment, string literal, and character literal
    replaced by spaces of the same length, newlines kept, so that offsets and
    line numbers in the view are those of the source and a brace inside a
    string or a comment is not a brace. Every regular-expression match in this
    file runs over the view, and so does every brace walk."""
    out = []
    i = 0
    n = len(text)

    def blank(s: str) -> str:
        return "".join("\n" if ch == "\n" else " " for ch in s)

    while i < n:
        c = text[i]
        two = text[i : i + 2]
        if two == "//":
            m = _LINE_COMMENT.match(text, i)
            out.append(blank(m.group()))
            i = m.end()
        elif two == "/*":
            depth = 0
            j = i
            while j < n:
                if text.startswith("/*", j):
                    depth += 1
                    j += 2
                elif text.startswith("*/", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            out.append(blank(text[i:j]))
            i = j
        elif c == "'":
            m = _CHAR.match(text, i)
            if m:
                out.append(blank(m.group()))
                i = m.end()
            else:
                out.append(c)
                i += 1
        elif c == '"' or (
            c in "rbc" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_"))
        ):
            m = _RAW_STRING_START.match(text, i)
            if m:
                close = '"' + m.group("hashes")
                j = text.find(close, m.end())
                j = n if j < 0 else j + len(close)
                out.append(blank(text[i:j]))
                i = j
                continue
            m = _CHAR.match(text, i) if c == "b" else None
            if m is None:
                m = _STRING.match(text, i)
            if m:
                out.append(blank(m.group()))
                i = m.end()
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def _matching_brace(text: str, open_pos: int):
    """The index of the `}` that closes the `{` at `open_pos`, or `None` if
    the text ends first. `text` must be the code view, so every brace seen is
    code."""
    depth = 0
    i = open_pos
    while i < len(text):
        c = text[i]
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return None


def _blank_test_modules(text: str, rel: str) -> str:
    """Remove every `#[cfg(test)] mod ... { ... }` span, replacing it with as
    many blank lines as it spanned.

    Only the test module's own byte range is removed, not everything after the
    first one (CR-09): cutting at the first `#[cfg(test)]` would blind discovery
    to any real code below a test module. Blanking rather than deleting keeps
    every surviving declaration on its original line number.

    `text` is the code view, so a brace inside a test's string or a comment
    cannot move the module's end over the code that follows it. The walk
    fails closed: the view's braces must balance before a module is looked
    for, and a module that never closes is an error, because either would
    otherwise leave the walk free to blank real code below the module and
    report the file as covered."""
    if text.count("{") != text.count("}"):
        _refuse(f"{rel}: braces do not balance outside strings and comments")
    pattern = re.compile(r"#\[cfg\(test\)\]\s*\n\s*mod\s+[A-Za-z0-9_]+\s*\{", re.M)
    while True:
        m = pattern.search(text)
        if not m:
            return text
        end = _matching_brace(text, m.end() - 1)
        if end is None:
            _refuse(f"{rel}: the test module at offset {m.start()} never closes")
        end += 1
        span = text[m.start() : end]
        text = text[: m.start()] + ("\n" * span.count("\n")) + text[end:]


def _is_under_test_attribute(lines: list, line: int) -> bool:
    """Whether the item declared at `line` (1-based) carries `#[cfg(test)]` as
    the attribute directly on it: the nearest non-blank, non-comment line above.
    Text in a comment counting would be a one-line bypass."""
    above = line - 2
    while above >= 0 and (
        lines[above].strip() == "" or lines[above].strip().startswith("//")
    ):
        above -= 1
    return above >= 0 and lines[above].strip().startswith("#[cfg(test)]")


def discovered():
    """Every function in the zones whose name says it consumes a message,
    with the receiver it takes, plus the pure helpers named in `ALSO_DISCOVER`
    that consume bundle material under a name with no verb in it."""
    found = []
    for zone in ZONES:
        base = ROOT / zone
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.rs")):
            if path.name in ("tests.rs",) or "/tests/" in str(path):
                continue
            rel = path.relative_to(ROOT).as_posix()
            # Match against the code view -- strings and comments blanked, so
            # neither a brace nor a declaration inside one counts -- with every
            # test module's byte range blanked too, keeping line numbers and
            # any real code below a test module.
            text = _blank_test_modules(_code_view(path.read_text()), rel)
            lines = text.split("\n")
            spans = _impl_spans(text, rel)

            def record(m):
                """Turn a `DECL`/explicit match into a discovery entry, reading
                the *whole* parameter list from the opening parenthesis and
                qualifying the name by its enclosing type."""
                line = text[: m.start()].count("\n") + 1
                if _is_under_test_attribute(lines, line):
                    return None
                params = _param_list(text, m.start("first") - 1)
                ty = _enclosing_type(spans, m.start())
                name = m.group("name")
                qual = f"{ty}::{name}" if ty else name
                return (rel, qual, line, receiver_of(params))

            for m in DECL.finditer(text):
                name = m.group("name")
                if name in EXEMPT:
                    continue
                entry = record(m)
                if entry is not None:
                    found.append(entry)

            # Explicit, verb-less consumers for this file, if any.
            for name in ALSO_DISCOVER.get(rel, ()):
                for m in EXPLICIT_DECL[name].finditer(text):
                    entry = record(m)
                    if entry is not None:
                        found.append(entry)
    return found


def registered():
    """Entries in the registry: `(path, name) -> section`, from table rows
    under the three headings only."""
    text = REGISTRY.read_text()
    out = {}
    section = None
    for line in text.split("\n"):
        h = HEADING.match(line)
        if h:
            title = h.group("title").lower()
            section = next((k for k in SHAPES if title.startswith(k)), None)
            continue
        r = ROW.match(line)
        if r and section is not None:
            key = (r.group("path"), r.group("name"))
            if key in out:
                print(f"::error::registry lists `{key[0]}::{key[1]}` twice", file=sys.stderr)
                sys.exit(1)
            out[key] = section
    return out


def main():
    if not REGISTRY.exists():
        print(f"missing {REGISTRY}", file=sys.stderr)
        return 1

    found = discovered()
    reg = registered()
    problems = []

    # One row vouches for one function. Two declarations with the same
    # `(file, name)` -- a second `impl` block, say -- cannot share it.
    dupes = [k for k, n in Counter((rel, name) for rel, name, _, _ in found).items() if n > 1]
    for rel, name in sorted(dupes):
        problems.append(
            f"::error::`{rel}::{name}` is declared more than once in that file; "
            f"a registry row cannot cover both"
        )

    # Direction one: everything the code has is written down, under a heading
    # whose shape its signature actually has.
    for rel, name, line, receiver in found:
        section = reg.get((rel, name))
        if section is None:
            problems.append(
                f"::error::{rel}:{line} `{rel}::{name}` consumes a message and is "
                f"not registered in a table of AUTHENTICATION-BOUNDARY.md"
            )
            continue
        want = SHAPES[section]
        # `commit` is the adopting half of a transactional pair: it must be
        # the one that takes `&mut self`, and it is listed beside the
        # `&self` receive it adopts for. The name is type-qualified, so the
        # test is on the tail.
        if section == "transactional" and name.split("::")[-1] == "commit":
            want = "&mut self"
        if want is not None and receiver != want:
            problems.append(
                f"::error::{rel}:{line} `{rel}::{name}` is registered as "
                f"{section} (must take `{want}`) but takes `{receiver}`. Either "
                f"the type stopped defending the property or the row is wrong."
            )

    # Direction two: everything written down still exists. Without this a
    # registry could list functions discovery never looked at while the gate
    # reports that all paths are registered.
    have = {(rel, name) for rel, name, _, _ in found}
    for rel, name in sorted(reg):
        if (rel, name) not in have:
            problems.append(
                f"::error::`{rel}::{name}` is registered but no such function was "
                f"found. Either it moved and the registry needs updating, or "
                f"discovery cannot see it."
            )

    if problems:
        for p in problems:
            print(p, file=sys.stderr)
        print(
            "\nA function that consumes a message before it is authenticated must "
            "be a row in one of the three tables of "
            "tacenta-core/AUTHENTICATION-BOUNDARY.md, identified by its file path "
            "and name joined by a double colon, under the heading whose shape "
            "its signature has, with the argument for why it is safe.\n",
            file=sys.stderr,
        )
        return 1

    shapes = Counter(reg.values())
    print(
        f"authentication boundary: {len(found)} paths discovered, {len(reg)} registered "
        f"({shapes.get('transactional', 0)} transactional, "
        f"{shapes.get('orchestration', 0)} orchestration, "
        f"{shapes.get('mutating', 0)} mutating), signatures match, both directions agree"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
