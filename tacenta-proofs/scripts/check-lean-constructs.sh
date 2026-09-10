#!/usr/bin/env bash
# Refuse, textually, the Lean constructs that widen a proof's trust base
# without a warning, and the elaboration-time code that could forge the one
# shape the environment audit accepts. The second line of defence; the first
# is `Model.AxiomAudit`, which asks the elaborated environment rather than the
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
#     matters; refusing the text is cheap insurance on top. Every other
#     `debug.*` option is refused with it. The option can also be set from
#     outside the source, by a lakefile passing `-D` to `lean` or setting
#     `leanOptions`, so the three lakefiles are scanned for any
#     option-setting key and for the option by name.
#
# And one thing the environment audit accepts by shape and cannot tell from
# the real thing: a *planted* compiler-trust axiom or auxiliary. The audit
# allows an axiom named `<t>._native.native_decide.ax_1_1` that states
# `decide p = true` and is applied by `<t>`'s proof, because that is what
# `native_decide` produces; and a partial `<f>._unsafe_rec` beside a
# recursive `<f>`, because that is what the compiler produces. Code that
# runs at elaboration time -- `run_cmd`, `#eval`, an `elab`, a `macro`, an
# `initialize` -- can call `addDecl` and produce exactly that, with the name
# assembled from string literals so that no `axiom` and no `_native` token
# is in the text (the strings are stripped below, so the compiler-namespace
# rule does not fire), after which a theorem proves `False` and
# `leanchecker` accepts every declaration involved, since an axiom is a
# kernel-valid declaration. So this script refuses elaboration-time code
# altogether in hand-written first-party Lean:
#
#   - the commands that run code at elaboration time: `run_cmd`, `run_elab`,
#     `run_meta`, `run_tac`, `by_elab`, `#eval`, `#exit`;
#   - the declarations that register code to run later: `elab`,
#     `elab_rules`, `macro`, `macro_rules`, `syntax`, `declare_syntax_cat`,
#     `initialize`, `builtin_initialize`, and the attributes that do the
#     same (`@[init]`, `@[command_elab]`, `@[term_elab]`, `@[tactic]`,
#     `@[macro]`, `@[builtin_*]`);
#   - the environment-mutating API by name, however qualified: `addDecl`,
#     `addAndCompile`, `modifyEnv`, `setEnv`, `compileDecl`, `evalDecl`,
#     `evalExpr`, `evalTerm`, `ofReduceBool`, `ofReduceNat`;
#   - and any reference to the `Lean` namespace at all -- `import Lean`,
#     `open Lean`, `namespace Lean`, `export Lean`, `Lean.Elab.…`,
#     `Lean.Meta.…` -- since that is where every such API lives. Hand-written
#     first-party Lean names nothing under `Lean`; the model, the proofs and
#     the refinement theorems are ordinary definitions and theorems.
#
# The one legitimate elaboration-time code is the audit itself:
# `Model/AxiomAudit.lean` imports `Lean` and is meta code by nature, and each
# package invokes it with one `run_cmd Model.AxiomAudit.run …` line. Those
# are allow-listed below by file path AND exact line content, so a second
# `run_cmd` in an audit module, a `run_cmd` in any other file, or an audit
# module invoking something other than `Model.AxiomAudit.run` fails. The
# allow-list entries must also all be present, so an audit invocation that
# is deleted fails here as well; `check-audit-reach.sh` checks that the five
# modules carrying them reach every first-party module, and that all four
# name the same first-party prefixes.
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

# An identifier as a token, allowing a following dot (`Lean.Elab`, `addDecl.go`).
def ident(word):
    return re.compile(r"(?<![\w.«])" + word + r"(?![\w'«])")

# The declaration kinds the environment audit refuses too. Never allow-listed.
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
    ("debug-option",       re.compile(r"set_option\s+debug\.")),
]

# Elaboration-time code: the only rules the allow-list below can excuse.
ELAB_RULES = [
    ("elab-time-command",
     keyword(r"(?:run_cmd|run_elab|run_meta|run_tac|by_elab|#eval|#exit)")),
    ("elab-time-declaration",
     keyword(r"(?:elab|elab_rules|macro|macro_rules|syntax|declare_syntax_cat|"
             r"initialize|builtin_initialize)")),
    ("elab-time-attribute",
     re.compile(r"(?:@|attribute\s*)\[[^\]]*\b(?:init|command_elab|term_elab|tactic|"
                r"macro|builtin_\w+)\b")),
    ("environment-api",
     ident(r"(?:addDecl\w*|addAndCompile\w*|modifyEnv|setEnv|compileDecl\w*|"
           r"evalDecl|evalExpr|evalTerm|ofReduceBool|ofReduceNat)")),
    # `import Lean`, `open Lean`, `namespace Lean`, `export Lean`, `Lean.X`,
    # and a bare `Lean` anywhere else.
    ("lean-namespace",     ident("Lean")),
]

# The allow-list: file path -> the exact source lines (whitespace collapsed)
# on which an ELAB_RULES hit is accepted. Every entry must be present in its
# file, or the run fails: the four `run_cmd` lines are the audit invocations
# and a missing one is an audit nothing runs. `Model/AxiomAudit.lean` is the
# audit's implementation and is otherwise held to every rule here, so a
# `run_cmd` or an `addDecl` added to it fails like anywhere else.
# (`\x60` is a backtick, Lean's name-literal quote: this program sits inside
# a `$(...)` substitution, and the shell would pair backticks in it.)
BT = "\x60"
# One line, the same at all four sites. The prefixes name every first-party
# namespace whether or not the invoking module's environment holds any of
# them, because the audit's waiver for an unmentioned compiler-trust axiom
# asks whether any first-party declaration mentions it, and a narrower list at
# one site would make a real use invisible there.
# `check-audit-reach.sh` checks the same thing from the other side.
AUDIT_CALL = ("run_cmd Model.AxiomAudit.run #[" + BT + "Model, " + BT
              + "Properties, " + BT + "Proofs, " + BT + "Translation]")
ALLOW = {
    "tacenta-model/Properties/AxiomAudit.lean": [AUDIT_CALL],
    "tacenta-proofs/Proofs/AxiomAudit.lean": [AUDIT_CALL],
    "tacenta-proofs/translation/Translation/AxiomAudit.lean": [AUDIT_CALL],
    # The three-leaf translation unit, which cannot share an environment with
    # the rest of the translation.
    "tacenta-proofs/translation/Translation/AxiomAuditTripleUnit.lean": [AUDIT_CALL],
    "tacenta-model/Model/AxiomAudit.lean": [
        "import Lean",
        "open Lean",
        '| "native_decide" => [' + BT + "Decidable.decide, " + BT + "Lean.reduceBool]",
        '| "decide" => [' + BT + "Decidable.decide, " + BT + "Lean.reduceBool]",
        BT + "Lean.reduceBool]",
    ],
}

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

def collapse(line):
    return " ".join(line.split())

lean_paths, lake_paths = os.environ["LEAN_FILES"], os.environ["LAKEFILES"]
hits = []
present = {path: set() for path in ALLOW}
for path in lean_paths.split():
    raw = open(path, encoding="utf-8").read()
    raw_lines = raw.split("\n")
    text = strip_lean(raw)
    allowed = ALLOW.get(path, [])
    for lineno, line in enumerate(text.split("\n"), 1):
        for kind, rule in LEAN_RULES:
            if rule.search(line):
                hits.append(f"{path}:{lineno}: {kind}: {line.strip()}")
        for kind, rule in ELAB_RULES:
            if rule.search(line):
                source = collapse(raw_lines[lineno - 1])
                if source in allowed:
                    present[path].add(source)
                else:
                    hits.append(f"{path}:{lineno}: {kind}: {line.strip()}")
for path, lines in ALLOW.items():
    for source in lines:
        if source not in present[path]:
            hits.append(f"{path}: allow-listed line missing (the audit is not invoked, "
                        f"or its implementation changed): {source}")
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
  echo "a debug.* option, or a lakefile that sets Lean options widens the trust" >&2
  echo "base of every theorem downstream of it without a compiler warning; and" >&2
  echo "elaboration-time code (run_cmd, #eval, elab, macro, syntax, initialize," >&2
  echo "addDecl, any reference to the Lean namespace) could plant a compiler-trust" >&2
  echo "axiom the environment audit accepts by shape. If one is genuinely needed," >&2
  echo "record it in LIMITATIONS.md and add it to the allow-list in this script" >&2
  echo "and in Model/AxiomAudit.lean with the reason." >&2
  status=1
fi

count=$(echo "$lean_files" | wc -l | tr -d ' ')
if [ "$status" -eq 0 ]; then
  echo "check-lean-constructs: $count first-party Lean files declare no axiom, opaque, implemented_by, extern, partial, unsafe, compiler-namespace name or debug option, and carry no elaboration-time code outside the audit's 4 allow-listed invocations and its implementation; 3 lakefiles set no Lean option"
fi
exit "$status"
