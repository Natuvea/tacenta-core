#!/usr/bin/env bash
# Refuse, textually, the Lean constructs that widen a proof's trust base
# without a warning. The second line of defence; the first is
# `Model.AxiomAudit`, which asks the elaborated environment rather than the
# source and runs inside every `lake build` (see `Model/AxiomAudit.lean`).
#
# `no-sorry.sh` asks the compiler for incomplete declarations, and the
# `#print axioms` pins catch a theorem that starts resting on something new.
# Neither sees a *declaration* that is itself the new thing:
#
#   - `axiom`: a proposition assumed rather than proved, which `#print axioms`
#     reports only for the theorems that are pinned, and most are not.
#   - `opaque`: a constant with no definition the kernel can unfold, and the
#     form a `partial def` elaborates to.
#   - `@[implemented_by]` / `@[extern]`: the compiled program `native_decide`
#     runs is a different definition from the one the kernel reasons about.
#     This is the textbook route to proving `False` with `native_decide`.
#   - `partial def`: opts out of termination checking; `unsafe`: opts out of
#     everything.
#   - `set_option debug.skipKernelTC true`: the next declaration is added
#     without the kernel checking it at all. Nothing in the environment
#     records that afterwards, so this is the one the audit module cannot
#     see, and `leanchecker` (which `no-sorry.sh` runs) is the check that
#     matters; refusing the text is cheap insurance on top.
#
# An earlier version of this script required the keyword at the start of the
# statement, and so missed `private axiom`, an axiom behind an attribute,
# `private unsafe def`, `opaque` and the option. This one strips comments and
# docstrings first, then matches the keyword after any run of attributes and
# modifiers, so that prose *about* these constructs -- including this comment
# -- does not trip the rule it describes.
#
# None is present in first-party Lean today, and the generated translation
# legitimately carries `axiom` declarations for the opaque externals (`opaque`
# in Aeneas's output), so the generated files are excluded and everything
# hand-written is scanned; `attest.py --check` holds the generated files'
# axiom sets to the recorded manifest instead.
set -euo pipefail

cd "$(dirname "$0")/../.."

# Hand-written first-party Lean: the model, the property theorems, the
# model-layer proofs, and every translation-package file that is not a
# generated `Tacenta*.lean`.
files=$(
  {
    find tacenta-model/Model tacenta-model/Properties tacenta-proofs/Proofs \
      -name '*.lean' 2>/dev/null
    find tacenta-proofs/translation/Translation -name '*.lean' \
      -not -name 'Tacenta*.lean' 2>/dev/null
  } | sort
)

if [ -z "$files" ]; then
  echo "check-lean-constructs: no first-party Lean found" >&2
  exit 1
fi

# python3 for the comment stripping: a block comment spans lines, and the
# repository already needs python3 for attest.py. Standard library only.
found=$(echo "$files" | python3 -c '
import re, sys

# Attributes and modifiers that may precede the keyword.
PREFIX = r"(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
RULES = [
    ("axiom",          re.compile(r"^\s*" + PREFIX + r"axiom\s")),
    ("opaque",         re.compile(r"^\s*" + PREFIX + r"opaque\s")),
    ("partial",        re.compile(r"^\s*" + PREFIX + r"partial\s")),
    ("unsafe",         re.compile(r"^\s*" + PREFIX + r"unsafe\s")),
    ("implemented_by", re.compile(r"@\[[^\]]*implemented_by")),
    ("extern",         re.compile(r"@\[[^\]]*\bextern\b")),
    ("skipKernelTC",   re.compile(r"set_option\s+debug\.skipKernelTC")),
]

def strip_comments(text):
    """Remove `--` line comments and `/- ... -/` block comments (docstrings
    included, and nested blocks), replacing them with spaces so that line
    numbers survive."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i:i+2]
        if depth == 0 and two == "--":
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        if two == "/-":
            depth += 1; out.append("  "); i += 2; continue
        if depth > 0 and two == "-/":
            depth -= 1; out.append("  "); i += 2; continue
        out.append(text[i] if depth == 0 or text[i] == "\n" else " ")
        i += 1
    return "".join(out)

hits = []
for path in sys.stdin.read().split():
    text = strip_comments(open(path, encoding="utf-8").read())
    for lineno, line in enumerate(text.split("\n"), 1):
        for kind, rule in RULES:
            if rule.search(line):
                hits.append(f"{path}:{lineno}: {kind}: {line.strip()}")
print("\n".join(hits))
')

status=0
if [ -n "$found" ]; then
  echo "" >&2
  echo "REFUSING: hand-written Lean declares something the proof gates cannot see:" >&2
  echo "$found" | sed 's/^/    /' >&2
  echo "" >&2
  echo "An axiom, an opaque, an implemented_by/extern attribute, a partial def, an" >&2
  echo "unsafe declaration, or debug.skipKernelTC widens the trust base of every" >&2
  echo "theorem downstream of it without a compiler warning. If one is genuinely" >&2
  echo "needed, record it in LIMITATIONS.md and add it to the allow-list in this" >&2
  echo "script and in Model/AxiomAudit.lean with the reason." >&2
  status=1
fi

count=$(echo "$files" | wc -l | tr -d ' ')
if [ "$status" -eq 0 ]; then
  echo "check-lean-constructs: $count first-party Lean files declare no axiom, opaque, implemented_by, extern, partial, unsafe or debug.skipKernelTC"
fi
exit "$status"
