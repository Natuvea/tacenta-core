#!/usr/bin/env python3
"""Keep the files every new proof module edits in a form where two changes touch different lines.

    python3 tooling/reflow-shared-lists.py --check      fail if --write would change a file
    python3 tooling/reflow-shared-lists.py --write      rewrite the files into that form
    python3 tooling/reflow-shared-lists.py --write --root DIR   the same, in another checkout

Each new lifecycle module adds an entry to the same few lists. Where a list was packed several entries to a
line, two branches that each added an entry changed the same line, and git reported a conflict that had to
be resolved word by word. This rewrites each of those lists with one entry per line, in the order the
entries already have; it adds, removes and reorders nothing. What it rewrites:

  tacenta-proofs/scripts/no-sorry-parts.txt   a part with more than one phase as its header line followed by
                                              one indented line per phase (the form `no-sorry-parts.py`
                                              reads as the same part)
  tooling/tests/run-proof-script-cases.sh     the `sh_controls` and `py_controls` arrays and the list of the
                                              `for called in` loop, one word per line
  tooling/gate-inventory.json                 a row's `controls` list of more than three entries, one entry
                                              per line (the JSON value is unchanged)
  ASSURANCE-OBLIGATIONS.md                    a table one of whose rows is longer than 1000 characters, as a
                                              list with one item per row, a bold label per column, and one
                                              sentence or clause per line (see `reflow_markdown`); a line of
                                              such a list longer than 400 characters is split the same way

Every rewrite is checked before it is written: the parts file is read back by `no-sorry-parts.py`'s own
parser, which must give the same parts and phases; the shell words must be the same words, in the same
order; the JSON must load to the same value; and the Markdown list must hold, column by column, the text
of the table's cells with only the white space changed. A rewrite that fails its check stops the run and
writes nothing.

What this does not do: decide where a new entry goes. `tacenta-proofs/scripts/new-lifecycle-module.py`
places one after the existing entry its name sorts after, so that two modules with different names add
lines at different places.
"""
import argparse
import importlib.util
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PARTS = "tacenta-proofs/scripts/no-sorry-parts.txt"
CASES = "tooling/tests/run-proof-script-cases.sh"
INVENTORY = "tooling/gate-inventory.json"
OBLIGATIONS = "ASSURANCE-OBLIGATIONS.md"
ROW_LIMIT = 1000
LINE_LIMIT = 400
LIST_OPEN = "<!-- One item per table row, one sentence or clause per line: tooling/reflow-shared-lists.py. -->"
LIST_CLOSE = "<!-- End of the list. -->"


class Refused(Exception):
    pass


# ---- the parts file ----------------------------------------------------------------------------

def load_parts_reader(root):
    path = root / "tacenta-proofs" / "scripts" / "no-sorry-parts.py"
    spec = importlib.util.spec_from_file_location("no_sorry_parts", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def parts_records(text, reader):
    """[(partition, part, [spec...])] in file order, read with the parser's own patterns."""
    out = []
    for line in text.split("\n"):
        continued = reader.CONTINUATION.fullmatch(line)
        if continued:
            out[-1][2].append(continued.group(1))
            continue
        if line == "" or line.startswith("#"):
            continue
        found = reader.LINE.fullmatch(line)
        if not found:
            raise Refused(f"{PARTS}: a line the parser would refuse: {line!r}")
        out.append((found.group(1), found.group(2), found.group(3).split(" ")[1:]))
    return out


def reflow_parts(text, reader):
    lines = []
    for line in text.split("\n"):
        found = reader.LINE.fullmatch(line) if not line.startswith("#") else None
        words = found.group(3).split(" ")[1:] if found else []
        if found and len(words) > 1:
            lines.append(f"{found.group(1)} {found.group(2)}:")
            lines.extend("  " + w for w in words)
        else:
            lines.append(line)
    new = "\n".join(lines)
    if parts_records(new, reader) != parts_records(text, reader):
        raise Refused(f"{PARTS}: the reflowed file reads as other parts")
    return new


# ---- shell word lists ----------------------------------------------------------------------------

def shell_words(text):
    """The words of a run of shell text: split at unquoted white space, a backslash-newline is white space,
    each word kept as written (quotes included)."""
    words, word, quote, i = [], "", None, 0
    while i < len(text):
        c = text[i]
        if quote:
            word += c
            if c == quote:
                quote = None
        elif c == "\\" and text[i + 1:i + 2] == "\n":
            if word:
                words.append(word)
                word = ""
            i += 1
        elif c in "'\"":
            quote = c
            word += c
        elif c.isspace():
            if word:
                words.append(word)
                word = ""
        else:
            word += c
        i += 1
    if quote:
        raise Refused("an unterminated quote in a shell word list")
    if word:
        words.append(word)
    return words


ARRAY = re.compile(r"^(?P<name>sh_controls|py_controls)=\((?P<body>[^)]*)\)$", re.M)
FOR_LIST = re.compile(r"^for called in (?P<body>(?:[^;]|\\\n)*?); do$", re.M)


def reflow_cases(text):
    def array(m):
        words = shell_words(m.group("body"))
        return m.group("name") + "=(\n" + "".join(f"  {w}\n" for w in words) + ")"

    def loop(m):
        words = shell_words(m.group("body"))
        if not words:
            raise Refused(f"{CASES}: the `for called in` list is empty")
        return "for called in \\\n" + " \\\n".join("  " + w for w in words) + "; do"

    new, n_arrays = ARRAY.subn(array, text)
    new, n_loops = FOR_LIST.subn(loop, new)
    if n_arrays != 2 or n_loops != 1:
        raise Refused(f"{CASES}: expected the two control arrays and one `for called in` list, found "
                      f"{n_arrays} and {n_loops}")
    before = [shell_words(m.group("body")) for m in ARRAY.finditer(text)] + \
             [shell_words(m.group("body")) for m in FOR_LIST.finditer(text)]
    after = [shell_words(m.group("body")) for m in ARRAY.finditer(new)] + \
            [shell_words(m.group("body")) for m in FOR_LIST.finditer(new)]
    if before != after:
        raise Refused(f"{CASES}: the reflowed lists hold other words")
    return new


# ---- the gate inventory ----------------------------------------------------------------------------

def json_value_end(text, start):
    """The index just past the JSON value (an array) that starts at `start`."""
    depth, i, in_string = 0, start, False
    while i < len(text):
        c = text[i]
        if in_string:
            if c == "\\":
                i += 1
            elif c == '"':
                in_string = False
        elif c == '"':
            in_string = True
        elif c in "[{":
            depth += 1
        elif c in "]}":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    raise Refused(f"{INVENTORY}: an unterminated array")


def split_top(body):
    """The elements of the inside of a JSON array, as written."""
    parts, depth, in_string, start, i = [], 0, False, 0, 0
    while i < len(body):
        c = body[i]
        if in_string:
            if c == "\\":
                i += 1
            elif c == '"':
                in_string = False
        elif c == '"':
            in_string = True
        elif c in "[{":
            depth += 1
        elif c in "]}":
            depth -= 1
        elif c == "," and depth == 0:
            parts.append(body[start:i].strip())
            start = i + 1
        i += 1
    tail = body[start:].strip()
    if tail:
        parts.append(tail)
    return parts


def reflow_inventory(text):
    key = '"controls": ['
    out = []
    for line in text.split("\n"):
        at = line.find(key)
        if line.startswith("  {") and at >= 0 and not line.endswith(key):
            start = at + len(key) - 1
            end = json_value_end(line, start)
            elements = split_top(line[start + 1:end - 1])
            if len(elements) > 3:
                out.append(line[:start + 1])
                out.extend(f"    {e}," for e in elements[:-1])
                out.append(f"    {elements[-1]}")
                out.append("  ]" + line[end:])
                continue
        out.append(line)
    new = "\n".join(out)
    try:
        same = json.loads(new) == json.loads(text)
    except ValueError as error:
        raise Refused(f"{INVENTORY}: the reflowed file is not JSON: {error}")
    if not same:
        raise Refused(f"{INVENTORY}: the reflowed file holds another value")
    return new


# ---- the obligations file --------------------------------------------------------------------------

# A piece of text that begins one of these would start a block of its own on a line of its own (a list item,
# a heading, a quote, a table, a fence, HTML, a link definition, a setext underline or a thematic break), so a
# line is never split before it.
BLOCK_START = re.compile(r"(?:[-+*](?:\s|$)|\d+[.)](?:\s|$)|#|>|\||=|```|~~~|<|\[|_|\*\*\*)")


def split_points(text, fine=False):
    """Where a line may be broken without changing what it renders as, as (start, end) of a run of spaces
    outside code spans: after `. `, `; ` or `: `, and before a code span that follows `, `, outside brackets
    and parentheses; with `fine`, also after `,`, and inside brackets and parentheses."""
    points, depth, i, code = [], 0, 0, 0
    while i < len(text):
        c = text[i]
        if c == "`":
            run = len(text[i:]) - len(text[i:].lstrip("`"))
            if code == 0:
                code = run
            elif code == run:
                code = 0
            i += run
            continue
        if code:
            i += 1
            continue
        if c in "([":
            depth += 1
        elif c in ")]":
            depth = max(0, depth - 1)
        elif c == " " and i > 0:
            j = i
            while j < len(text) and text[j] == " ":
                j += 1
            before, after = text[i - 1], text[j:j + 1]
            if after and (depth == 0 or fine):
                if before in ".;:" or (before == "," and (after == "`" or fine)):
                    points.append((i, j))
            i = j
            continue
        i += 1
    return points


def split_once(text, fine):
    lines, start = [], 0
    for lo, hi in split_points(text, fine):
        piece = text[start:lo]
        if BLOCK_START.match(text[hi:]) or piece.endswith("\\") or not piece.strip():
            continue
        lines.append(piece)
        start = hi
    lines.append(text[start:])
    return lines


def split_text(text):
    """`text` as lines broken at its split points (a piece longer than LINE_LIMIT broken again at the finer
    ones), never before a block start, never inside a code span, a line never ending in a backslash or a
    space. The text of a code span is not touched, and a run of spaces outside one becomes a line break, which
    renders as the space it was."""
    text = text.strip()
    out = []
    for piece in split_once(text, False):
        out.extend(split_once(piece, True) if len(piece) > LINE_LIMIT else [piece])
    return [line.strip() for line in out if line.strip()]


def rendered(text):
    """`text` with each run of white space outside code spans made one space: what the comparison of a
    table cell with its list item holds equal."""
    out, i, code = [], 0, 0
    while i < len(text):
        if text[i] == "`":
            run = len(text[i:]) - len(text[i:].lstrip("`"))
            code = run if code == 0 else (0 if code == run else code)
            out.append(text[i:i + run])
            i += run
            continue
        if not code and text[i].isspace():
            j = i
            while j < len(text) and text[j].isspace():
                j += 1
            out.append(" ")
            i = j
            continue
        out.append(text[i])
        i += 1
    return "".join(out).strip()


def unescape_code_pipes(cell):
    """A table cell's text as a paragraph needs it: GitHub reads `\\|` as `|` everywhere in a table cell, code
    spans included, while in a paragraph a code span keeps the backslash. So `\\|` inside a code span becomes
    `|`; outside one it stays, where a paragraph reads it as `|` too."""
    out, i, code = [], 0, 0
    while i < len(cell):
        if cell[i] == "`":
            run = len(cell[i:]) - len(cell[i:].lstrip("`"))
            code = run if code == 0 else (0 if code == run else code)
            out.append(cell[i:i + run])
            i += run
            continue
        if code and cell.startswith("\\|", i):
            out.append("|")
            i += 2
            continue
        out.append(cell[i])
        i += 1
    return "".join(out)


def cells(row):
    inner = row.strip()
    if not (inner.startswith("|") and inner.endswith("|")):
        raise Refused(f"{OBLIGATIONS}: a table row that does not start and end with `|`: {row[:80]!r}")
    return [unescape_code_pipes(c.strip()) for c in re.split(r"(?<!\\)\|", inner[1:-1])]


def table_spans(lines):
    """[(first, last)] line indices (inclusive) of each table: a header row, a delimiter row and body rows."""
    spans, i = [], 0
    while i + 1 < len(lines):
        if lines[i].startswith("|") and re.fullmatch(r"\|(?:\s*:?-+:?\s*\|)+", lines[i + 1].strip()):
            j = i + 2
            while j < len(lines) and lines[j].startswith("|"):
                j += 1
            spans.append((i, j - 1))
            i = j
        else:
            i += 1
    return spans


def as_list(header, rows):
    out = [LIST_OPEN, ""]
    for row in rows:
        values = cells(row)
        if len(values) != len(header):
            raise Refused(f"{OBLIGATIONS}: a row with {len(values)} cells under {len(header)} columns")
        first = True
        for label, value in zip(header, values):
            lead = "- " if first else "  "
            out.append(f"{lead}**{label}:**")
            out.extend("  " + line for line in split_text(value))
            out.append("")
            first = False
    out.append(LIST_CLOSE)
    return out


def read_list(lines, header):
    """The rows of a list `as_list` wrote, as lists of cell texts with white space collapsed."""
    rows, current, label, buffer = [], None, None, []

    def flush():
        if current is not None and label is not None:
            current.append(rendered("\n".join(buffer)))

    for line in lines:
        if line in (LIST_OPEN, LIST_CLOSE):
            continue
        m = re.fullmatch(r"(- |  )\*\*(.+?):\*\*", line)
        if m:
            flush()
            if m.group(1) == "- ":
                if current is not None:
                    rows.append(current)
                current = []
            label, buffer = m.group(2), []
            continue
        if line.strip():
            buffer.append(line.strip())
    flush()
    if current is not None:
        rows.append(current)
    return rows


def reflow_markdown(text):
    lines = text.split("\n")
    out, i = [], 0
    spans = {first: last for first, last in table_spans(lines)}
    in_list = False
    while i < len(lines):
        line = lines[i]
        if line == LIST_OPEN:
            in_list = True
        elif line == LIST_CLOSE:
            in_list = False
        if i in spans:
            last = spans[i]
            body = lines[i + 2:last + 1]
            if any(len(row) > ROW_LIMIT for row in body):
                header = cells(lines[i])
                converted = as_list(header, body)
                got = read_list(converted, header)
                want = [[rendered(c) for c in cells(row)] for row in body]
                if got != want:
                    raise Refused(f"{OBLIGATIONS}: the list made of the table at line {i + 1} does not hold "
                                  "its cells")
                out.extend(converted)
            else:
                out.extend(lines[i:last + 1])
            i = last + 1
            continue
        if in_list and len(line) > LINE_LIMIT and line.startswith("  ") and not line.startswith("  **"):
            pieces = split_text(line)
            if rendered("\n".join(pieces)) != rendered(line):
                raise Refused(f"{OBLIGATIONS}: line {i + 1} does not split cleanly")
            out.extend("  " + piece for piece in pieces)
        else:
            out.append(line)
        i += 1
    return "\n".join(out)


# ---- running it ----------------------------------------------------------------------------------

def targets(root):
    reader = load_parts_reader(root)
    return [
        (PARTS, lambda t: reflow_parts(t, reader)),
        (CASES, reflow_cases),
        (INVENTORY, reflow_inventory),
        (OBLIGATIONS, reflow_markdown),
    ]


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    root = args.root.resolve()
    changed, results = [], []
    try:
        for rel, reflow in targets(root):
            path = root / rel
            text = path.read_text(encoding="utf-8")
            new = reflow(text)
            if new != reflow(new):
                raise Refused(f"{rel}: the reflow is not stable (a second run changes it again)")
            results.append((path, text, new))
    except Refused as error:
        print(f"reflow-shared-lists: REFUSED: {error}", file=sys.stderr)
        return 2
    for path, text, new in results:
        if new != text:
            changed.append(str(path.relative_to(root)))
            if args.write:
                path.write_text(new, encoding="utf-8")
    if args.check and changed:
        print("reflow-shared-lists: not in the one-entry-per-line form: " + ", ".join(changed)
              + "; run `python3 tooling/reflow-shared-lists.py --write`", file=sys.stderr)
        return 1
    verb = "rewrote" if args.write and changed else "checked"
    print(f"reflow-shared-lists: {verb} {len(results)} files"
          + (f" ({', '.join(changed)})" if changed and args.write else "; every list is one entry per line"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
