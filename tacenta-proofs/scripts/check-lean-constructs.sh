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
#   - `@[implemented_by]` / `@[extern]`, as an attribute on the declaration or
#     added afterwards with `attribute [...]`: the compiled program
#     `native_decide` runs is a different definition from the one the kernel
#     reasons about. This is the textbook route to proving `False` with
#     `native_decide`.
#   - `partial def`: opts out of termination checking; `unsafe`: opts out of
#     everything.
#   - A declaration named into the compiler's own namespace, `_unsafe_rec` or
#     `_native`: the code generator calls `<f>._unsafe_rec` in place of `<f>`
#     whenever that constant exists, so a hand-written one is an
#     `implemented_by` in disguise, and `<t>._native.<tactic>.ax_*` is the
#     name the compiler-trust axioms carry. Nothing hand-written has a reason
#     to use either name.
#   - `set_option debug.skipKernelTC true`: the next declaration is added
#     without the kernel checking it at all. Nothing in the environment
#     records that afterwards, so this is the one the audit module cannot
#     see, and `leanchecker` (which `no-sorry.sh` runs) is the check that
#     matters; refusing the text is cheap insurance on top. The option can
#     also be set from outside the source, by a lakefile passing `-D` to
#     `lean` or setting `leanOptions`, so the three lakefiles are scanned for
#     any option-setting key and for the option by name.
#
# Earlier versions of this script required the keyword at the start of a line,
# after at most a run of attributes and modifiers, and so missed `set_option
# ... in axiom`, `namespace X axiom`, and `theorem t := ... axiom x : False` on
# one line, all of which Lean accepts. This one strips comments, docstrings
# and string literals first, and then matches the keyword *anywhere* it
# appears as a token: `axiom`, `opaque`, `partial` and `unsafe` are reserved
# words in Lean, so outside a comment or a string a token of that spelling is
# the keyword and nothing else, whatever precedes it. Prose *about* these
# constructs, this comment included, is stripped before the rules run.
#
# None is present in first-party Lean today, and the generated translation
# legitimately carries `axiom` declarations for the opaque externals (`opaque`
# in Aeneas's output), so the generated files are excluded and everything
# hand-written is scanned: the model, its properties and vector generator, the
# proofs, every hand-written translation module, the package root modules, and
# the lakefiles. `attest.py --check` holds the generated files' axiom sets to
# the recorded manifest instead, and `no-sorry.sh` compares that record with
# what the axiom audit saw in the environment.
set -euo pipefail

cd "$(dirname "$0")/../.."

# Hand-written first-party Lean: the model, its property theorems and vector
# generator, the model-layer proofs, every translation-package file that is
# not a generated `Tacenta*.lean`, and each package's root module.
lean_files=$(
  {
    find tacenta-model/Model tacenta-model/Properties tacenta-proofs/Proofs \
      -name '*.lean' 2>/dev/null
    find tacenta-proofs/translation/Translation -name '*.lean' \
      -not -name 'Tacenta*.lean' 2>/dev/null
    ls tacenta-model/Vectors.lean tacenta-proofs/translation/Translation.lean \
      tacenta-model/Model.lean tacenta-model/Properties.lean \
      tacenta-proofs/Proofs.lean 2>/dev/null || true
  } | sort
)

# The lakefiles, which can set Lean options for every module they build.
lakefiles=$(
  ls tacenta-model/lakefile.lean tacenta-model/lakefile.toml \
    tacenta-proofs/lakefile.lean tacenta-proofs/lakefile.toml \
    tacenta-proofs/translation/lakefile.lean tacenta-proofs/translation/lakefile.toml \
    2>/dev/null | sort || true
)

if [ -z "$lean_files" ]; then
  echo "check-lean-constructs: no first-party Lean found" >&2
  exit 1
fi
if [ "$(echo "$lakefiles" | wc -l | tr -d ' ')" -ne 3 ]; then
  echo "check-lean-constructs: expected exactly three lakefiles, found:" >&2
  echo "$lakefiles" >&2
  exit 1
fi

# python3 for the stripping: a block comment spans lines, and the repository
# already needs python3 for attest.py. Standard library only.
found=$(LEAN_FILES="$lean_files" LAKEFILES="$lakefiles" python3 - <<'PY'
import os, re, sys

# A reserved word as a token: not glued to an identifier character, a dot
# (`Foo.axiom` would be a name, not the keyword, though no such name exists
# here) or a guillemet.
def keyword(word):
    return re.compile(r"(?<![\w.«])" + word + r"(?![\w.'«])")

LEAN_RULES = [
    ("axiom",              keyword("axiom")),
    ("opaque",             keyword("opaque")),
    ("partial",            keyword("partial")),
    ("unsafe",             keyword("unsafe")),
    # As an attribute on the declaration (`@[...]`) or added afterwards
    # (`attribute [...] name`).
    ("implemented_by",     re.compile(r"(?:@|attribute\s*)\[[^\]]*\bimplemented_by\b")),
    ("extern",             re.compile(r"(?:@|attribute\s*)\[[^\]]*\bextern\b")),
    ("compiler-namespace", re.compile(r"(?<!\w)_(?:unsafe_rec|native)(?!\w)")),
    ("skipKernelTC",       re.compile(r"skipKernelTC")),
]

# A lakefile that sets any Lean option, or names the option, is refused: none
# of the three sets any today, and the one option that matters here is the
# one the environment cannot record.
LAKEFILE_RULES = [
    ("skipKernelTC", re.compile(r"skipKernelTC")),
    ("lean-options", re.compile(
        r"\b(?:moreLeanArgs|weakLeanArgs|moreServerArgs|weakServerArgs|"
        r"moreGlobalServerArgs|leanOptions|weakLeanOptions|moreServerOptions|"
        r"serverOptions)\b")),
]

def strip_lean(text):
    """Remove `--` line comments, `/- ... -/` block comments (docstrings
    included, and nested blocks) and `"..."` string literals, replacing them
    with spaces so that line numbers survive."""
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
        if depth == 0 and text[i] == "\"":
            j = i + 1
            while j < n and text[j] != "\"":
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append("".join("\n" if ch == "\n" else " " for ch in text[i:j]))
            i = j; continue
        out.append(text[i] if depth == 0 or text[i] == "\n" else " ")
        i += 1
    return "".join(out)

def strip_toml(text):
    """Remove `#` comments and `"..."` strings from a TOML lakefile. Keys are
    what the rules look for, and a key is never inside a string."""
    out = []
    for line in text.split("\n"):
        res, i, n = [], 0, len(line)
        while i < n:
            ch = line[i]
            if ch == "#":
                res.append(" " * (n - i)); break
            if ch == "\"":
                j = i + 1
                while j < n and line[j] != "\"":
                    j += 2 if line[j] == "\\" else 1
                j = min(j + 1, n)
                res.append(" " * (j - i)); i = j; continue
            res.append(ch); i += 1
        out.append("".join(res))
    return "\n".join(out)

lean_paths, lake_paths = os.environ["LEAN_FILES"], os.environ["LAKEFILES"]
hits = []
for path in lean_paths.split():
    text = strip_lean(open(path, encoding="utf-8").read())
    for lineno, line in enumerate(text.split("\n"), 1):
        for kind, rule in LEAN_RULES:
            if rule.search(line):
                hits.append(f"{path}:{lineno}: {kind}: {line.strip()}")
for path in lake_paths.split():
    raw = open(path, encoding="utf-8").read()
    text = strip_toml(raw) if path.endswith(".toml") else strip_lean(raw)
    for lineno, line in enumerate(text.split("\n"), 1):
        for kind, rule in LAKEFILE_RULES:
            if rule.search(line):
                hits.append(f"{path}:{lineno}: {kind}: {line.strip()}")
print("\n".join(hits))
PY
)

status=0
if [ -n "$found" ]; then
  echo "" >&2
  echo "REFUSING: hand-written Lean declares something the proof gates cannot see:" >&2
  echo "$found" | sed 's/^/    /' >&2
  echo "" >&2
  echo "An axiom, an opaque, an implemented_by/extern attribute, a partial def, an" >&2
  echo "unsafe declaration, a name in the compiler's _unsafe_rec/_native namespace," >&2
  echo "debug.skipKernelTC, or a lakefile that sets Lean options widens the trust" >&2
  echo "base of every theorem downstream of it without a compiler warning. If one" >&2
  echo "is genuinely needed, record it in LIMITATIONS.md and add it to the" >&2
  echo "allow-list in this script and in Model/AxiomAudit.lean with the reason." >&2
  status=1
fi

count=$(echo "$lean_files" | wc -l | tr -d ' ')
if [ "$status" -eq 0 ]; then
  echo "check-lean-constructs: $count first-party Lean files declare no axiom, opaque, implemented_by, extern, partial, unsafe, compiler-namespace name or debug.skipKernelTC; 3 lakefiles set no Lean option"
fi
exit "$status"
