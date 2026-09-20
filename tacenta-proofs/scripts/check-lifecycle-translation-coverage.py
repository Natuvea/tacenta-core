#!/usr/bin/env python3
"""Require every public lifecycle operation to appear in generated Lean."""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RUST = ROOT / "tacenta-core" / "lifecycle" / "src" / "lifecycle.rs"
TYPES = ("Identity", "PrekeyStore", "Session")


def code_view(text: str) -> str:
    """Blank comments and literals while preserving offsets and newlines."""
    out = list(text)
    i = 0
    while i < len(text):
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        elif text.startswith("/*", i):
            depth, j = 1, i + 2
            while j < len(text) and depth:
                if text.startswith("/*", j):
                    depth += 1
                    j += 2
                elif text.startswith("*/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < len(text):
                if text[j] == "\\":
                    j += 2
                elif text[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            for k in range(i, min(j, len(text))):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        else:
            i += 1
    return "".join(out)


def matching_brace(text: str, opening: int) -> int:
    depth = 0
    for at in range(opening, len(text)):
        if text[at] == "{":
            depth += 1
        elif text[at] == "}":
            depth -= 1
            if depth == 0:
                return at
    raise ValueError(f"unclosed brace at byte {opening}")


def public_operations(text: str) -> set[str]:
    view = code_view(text)
    operations: set[str] = set()
    occupied: list[tuple[int, int]] = []
    for ty in TYPES:
        for match in re.finditer(rf"^impl\s+{ty}\s*\{{", view, re.M):
            opening = view.find("{", match.start())
            closing = matching_brace(view, opening)
            occupied.append((match.start(), closing + 1))
            body = view[opening + 1 : closing]
            depth = 0
            for line in body.splitlines():
                if depth == 0:
                    method = re.search(r"\bpub\s+fn\s+([a-z0-9_]+)", line)
                    if method:
                        operations.add(f"lifecycle.{ty}.{method.group(1)}")
                depth += line.count("{") - line.count("}")

    top = list(view)
    for start, end in occupied:
        for at in range(start, end):
            if top[at] != "\n":
                top[at] = " "
    top_view = "".join(top)
    for match in re.finditer(r"^pub\s+fn\s+(establish_[a-z0-9_]+)", top_view, re.M):
        operations.add(f"lifecycle.{match.group(1)}")
    return operations


def generated_operations(text: str) -> set[str]:
    names = set(
        re.findall(r"^(?:def|opaque|axiom)\s+(lifecycle\.[A-Za-z0-9_.]+)", text, re.M)
    )
    return {name.replace(".impl.", ".") for name in names}


def main() -> int:
    lean = Path(sys.argv[1]) if len(sys.argv) == 2 else None
    if lean is None or not lean.is_file():
        print("usage: check-lifecycle-translation-coverage.py TacentaLifecycle.lean", file=sys.stderr)
        return 2
    public = public_operations(RUST.read_text())
    generated = generated_operations(lean.read_text())
    missing = sorted(public - generated)
    if missing:
        for name in missing:
            print(f"missing generated public lifecycle operation: {name}", file=sys.stderr)
        return 1
    if len(public) != 30:
        print(
            f"public lifecycle inventory changed from 30 to {len(public)}; "
            "review the new surface and update this control deliberately",
            file=sys.stderr,
        )
        return 1
    print(f"lifecycle-translation-coverage: all {len(public)} public operations generated")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
