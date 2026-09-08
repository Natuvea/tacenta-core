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

Discovery covers private functions as well as `pub fn` (`Session::decrypt_ratchet`
is private), matches the verb anywhere in the name rather than only as a prefix
(`establish_responder`, `step_receive`), and identifies a function by
`(file, name)` rather than by bare name, so a new type with a method called
`receive` is not covered by some other `receive` already in the document. Both
directions are checked: everything discovered must be registered, and
everything registered must still exist.

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
  text nearby; a comment mentioning it exempts nothing.
- **Verbs match anywhere in the name**, so `step_receive` is discovered, with a
  small exemption list for accessors (`receive_count` and friends).
- **A `(file, name)` seen twice is an error**, since one row cannot vouch for
  two functions.

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
# the name rather than only as a prefix.
FAMILY = r"(receive|decrypt|accept|process|commit|establish|handle|ingest)"

# A function declaration, `pub` or not, with its receiver captured: the text
# between the opening parenthesis and the first comma or closing parenthesis,
# which is `&self`, `&mut self`, `self`, or an ordinary first parameter.
DECL = re.compile(
    r"^(?P<indent>[ \t]*)(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?fn\s+"
    # The generic list may nest one level (`<F: Fn(&Msg) -> Option<Key>>`), which
    # a plain `<[^>]*>` cannot span; discovery must accept every declaration,
    # so the pattern spans one level of nesting.
    r"(?P<name>[a-z0-9_]*" + FAMILY + r"[a-z0-9_]*)\s*(?:<(?:[^<>]|<[^<>]*>)*>)?\s*\("
    r"(?P<first>[^,)]*)",
    re.M,
)

# Reading a counter or a chain is not consuming a message, and neither is
# initialising a party (`init_receiver` matches `receive` as a substring).
EXEMPT = {"receive_count", "receive_chain", "receive_chain_key", "receive_chains"}
EXEMPT_PREFIXES = ("init_",)

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
ROW = re.compile(r"^\|\s*`(?P<path>[A-Za-z0-9_./-]+\.rs)::(?P<name>[a-z0-9_]+)`\s*\|", re.M)


def receiver_of(first: str) -> str:
    """The shape of a function's first parameter, as far as the property
    cares: can it mutate the state it is handed?

    A free function taking `state: &mut State` is the same shape as a method
    taking `&mut self` -- the classical ratchet's `receive` is written that
    way -- so the test is on the borrow, not on the word `self`."""
    first = first.strip()
    if first.startswith("&mut self") or re.match(r"^[a-z_]+\s*:\s*&mut\b", first):
        return "&mut self"
    if first.startswith("&self") or re.match(r"^[a-z_]+\s*:\s*&", first):
        return "&self"
    if first == "self" or first.startswith("mut self") or first.startswith("self:"):
        return "self"
    return "free"


def discovered():
    """Every function in the zones whose name says it consumes a message,
    with the receiver it takes."""
    found = []
    for zone in ZONES:
        base = ROOT / zone
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.rs")):
            if path.name in ("tests.rs",) or "/tests/" in str(path):
                continue
            text = path.read_text()
            # Strip the trailing test *module*, and only that. Cutting at the
            # first `#[cfg(test)]` anywhere would blind discovery to everything
            # below a per-function attribute.
            m = re.search(r"^#\[cfg\(test\)\]\s*\n\s*mod\s", text, re.M)
            if m:
                text = text[: m.start()]
            rel = path.relative_to(ROOT).as_posix()
            lines = text.split("\n")
            for m in DECL.finditer(text):
                name = m.group("name")
                if name in EXEMPT or name.startswith(EXEMPT_PREFIXES):
                    continue
                line = text[: m.start()].count("\n") + 1
                # `#[cfg(test)]` counts only as the attribute immediately on the
                # item: the nearest non-blank, non-comment line above it. Text
                # in a comment counting would be a one-line bypass.
                above = line - 2
                while above >= 0 and (
                    lines[above].strip() == "" or lines[above].strip().startswith("//")
                ):
                    above -= 1
                if above >= 0 and lines[above].strip().startswith("#[cfg(test)]"):
                    continue
                found.append((rel, name, line, receiver_of(m.group("first"))))
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
        # `&self` receive it adopts for.
        if section == "transactional" and name == "commit":
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
