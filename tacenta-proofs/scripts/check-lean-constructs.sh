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
# package invokes it with one `run_cmd _root_.Model.AxiomAudit.run …` line. Those
# are allow-listed below by file path AND exact line content, so a second
# `run_cmd` in an audit module, a `run_cmd` in any other file, or an audit
# module invoking something other than `Model.AxiomAudit.run` fails. An
# allowed invocation must also stand alone: at column 0, not the body of a
# `… in` wrapper on the line before, and followed by nothing but another
# allowed invocation or the end of the file, since a wrapper or a
# continuation could consume its refusal or skip it, and a declaration after
# it is outside its walk. The allow-list entries must also all be present,
# so an audit invocation that is deleted fails here as well;
# `check-audit-reach.sh` checks that the seven modules carrying them reach
# every first-party module, and that all seven name the same first-party
# prefixes. Around the invocations, further text is refused: a notation
# (`notation "Model.AxiomAudit.run" => …` would rebind the name as a token),
# anything but imports, pins and the invocation in the seven invoking
# modules, one per line (a `namespace` or `open` could make the name resolve
# to a shadow), the audit's log tags in any other file's code or strings,
# `#reduce`, `#print "…"` and `dbg_trace` (which print into the build log
# `no-sorry.sh` reads the audit's lines from), every interpolating message
# head and `ident!` macro outside the audit, in the audit any string literal
# that holds a brace (the audit builds its messages by concatenation and
# interpolates nowhere: an interpolation can hold a quote, a char literal or a
# comment, which no brace count reads and which desynchronise the stripper),
# and any change to the three lakefiles, pinned by content. These textual rules
# are defence in depth around the invocations, not a tokenizer: the stripper
# does not parse interpolations, and a hostile reading of Lean's surface
# syntax has found a new shape at each review. The refuted-record walk
# (`Model.AxiomAudit.takers`) does not rest on them: `check-refuted-records.sh`
# runs it as a compiled executable that loads each closure at run time, so
# nothing a module declares is parsed where the walk is called. `tooling/tests/run-lean-constructs-cases.sh` plants
# each of the shapes above in a copy of the audit modules.
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
    ls tacenta-model/Vectors.lean tacenta-model/Difftest.lean \
      tacenta-proofs/translation/Translation.lean \
      tacenta-model/Model.lean tacenta-model/Properties.lean \
      tacenta-proofs/Proofs.lean 2>/dev/null || true
  } | sort
)

# The lakefiles, which can set Lean options for every module they build.
# This narrower structural gate permits generated Translation/Tacenta*.lean
# files to declare their recorded opaque externals. A disabled `sorry` warning
# is different: it can hide incompleteness in any first-party module, including
# generated translation, so scan the complete first-party source set for it.
all_lean_files=$(find tacenta-model tacenta-proofs -type f -name '*.lean' \
  -not -path '*/.lake/*' 2>/dev/null | sort)

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
# The program is written out first and run after, not embedded in the command
# substitution: a shell that reads a heredoc inside $( ) as shell text (bash 3.2
# does) would pair the quotes and parentheses in a program that has to spell
# out Lean's quote characters.
program="$(mktemp)"
trap 'rm -f "$program"' EXIT
cat > "$program" <<'PY'
import hashlib, os, re, sys
from collections import Counter

# A reserved word as a token: not glued to an identifier character or a dot
# (`Foo.axiom` would be a name, not the keyword, though no such name exists
# here). A guillemet identifier may follow it directly.
def keyword(word):
    return re.compile(r"(?<![\w.«])" + word + r"(?![\w.'])")

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
    # `_root_.Lean.X`, `«Lean».X`, and a bare `Lean` anywhere else.
    ("lean-namespace",     re.compile(r"(?<![\w.«])(?:_root_\.)?«?Lean»?(?![\w'«])")),
    # The notation family: `notation "Model.AxiomAudit.takers" => …` rebinds
    # the audit's name as a token in every module that imports it, and no
    # hand-written first-party module defines a notation. (`macro`, `syntax`
    # and `macro_rules` are refused above.)
    ("notation-family",
     keyword(r"(?:notation|infix|infixl|infixr|prefix|postfix)")),
    # `#reduce`, and `#print` of a string: either prints what it is given into
    # the build log, where `no-sorry.sh` reads the audit's lines.
    ("print-to-log",       keyword(r"(?:#reduce|dbg_trace|println!|dbg_trace!|dbgTrace)")),
    # The message heads that interpolate a plain string literal: none is used
    # outside `Model/AxiomAudit.lean`, and inside an interpolation a quote
    # desynchronises the stripper (see the brace-in-string rule below).
    # The rule is waived for `Model/AxiomAudit.lean`, which reports through
    # them; `trace` alone is an ordinary identifier (a variable name in the
    # translation), so only its bracketed message form is named.
    ("interpolating-head",
     re.compile(r"(?<![\w.«])(?:throwError|throwErrorAt|throwNamedError|throwNamedErrorAt|logInfo|"
                r"logInfoAt|logWarning|logWarningAt|logError|logErrorAt|logNamedInfo|logNamedWarning|"
                r"logNamedError|logNamedInfoAt|logNamedWarningAt|logNamedErrorAt|logAt|logNamedAt|"
                r"withTraceNode)(?![\w.'])|[\w.]*trace(?:_goal)?!?\[")),
]


# Rules on the raw text, strings and comments included.
#   - The audit's log lines may be produced by nothing but the audit: the
#     tags `no-sorry.sh` reads and compares appear in no other hand-written
#     file, in a string, a comment or anywhere else.
#   - An interpolated string (`s!"…{…}…"`) is refused outside the audit's
#     implementation, and inside it no string literal may hold a brace:
#     `s!"{"--"}"` reads to the stripper as a string followed by a comment and
#     hides the rest of the line from every rule here, and no brace count can
#     read what an interpolation holds, so the audit interpolates nowhere.
#   - `#print "…"` prints its string into the build log.
AUDIT_LINE_TAGS = re.compile(r"audit-(?:record|taker|axiom|native):")
PRINT_STRING = re.compile(r"#print\s+\"")
GUILLEMET_LEAN = re.compile(r"«(?:_root_\.)?Lean(?:\.|»)")
AUDIT_IMPLEMENTATION = "tacenta-model/Model/AxiomAudit.lean"

# The seven modules that invoke the audit hold nothing but imports, the
# invocations and the `#guard_msgs`, `#print` and `#check` pins of the Session
# unit: a `namespace` or `open` there could make the invocation resolve to a
# shadow, and a declaration there would be outside the walk or could redefine
# what the invocation calls.
AUDIT_MODULE_LINES = [
    re.compile(r"^import [\w.]+$"),
    re.compile(r"^#guard_msgs in$"),
    re.compile(r"^#print axioms [\w.'«»]+$"),
    re.compile(r"^#check @?[\w.'«»]+$"),
]

# The allow-list: file path -> the exact source lines (whitespace collapsed)
# on which an ELAB_RULES hit is accepted. Every entry must be present in its
# file, or the run fails: the seven `run_cmd` lines are the audit invocations
# and a missing one is an audit nothing runs. `Model/AxiomAudit.lean` is the
# audit's implementation and is otherwise held to every rule here, so a
# `run_cmd` or an `addDecl` added to it fails like anywhere else.
# (`\x60` is a backtick, Lean's name-literal quote: this program sits inside
# a `$(...)` substitution, and the shell would pair backticks in it.)
BT = "\x60"
# One line, the same at all seven sites. The prefixes name every first-party
# namespace whether or not the invoking module's environment holds any of
# them, because the audit's waiver for an unmentioned compiler-trust axiom
# asks whether any first-party declaration mentions it, and a narrower list at
# one site would make a real use invisible there.
# `check-audit-reach.sh` checks the same thing from the other side.
# By its `_root_` name, so that no `namespace` or `open` in scope can make
# it resolve to a shadow.
AUDIT_CALL = ("run_cmd _root_.Model.AxiomAudit.run #[" + BT + "Model, " + BT
              + "Properties, " + BT + "Proofs, " + BT + "Translation]")
# An allow-list entry is an exact collapsed line.
def allowed_entry(source, allowed):
    return source if source in allowed else None
def entry_text(entry):
    return entry
ALLOW = {
    "tacenta-model/Properties/AxiomAudit.lean": [AUDIT_CALL],
    "tacenta-proofs/Proofs/AxiomAudit.lean": [AUDIT_CALL],
    "tacenta-proofs/translation/Translation/AxiomAudit.lean": [AUDIT_CALL],
    # The three-leaf translation unit, which cannot share an environment with
    # the rest of the translation.
    "tacenta-proofs/translation/Translation/AxiomAuditTripleUnit.lean": [AUDIT_CALL],
    # The Braid-and-erasure translation unit, for the same reason.
    "tacenta-proofs/translation/Translation/AxiomAuditBraidUnit.lean": [AUDIT_CALL],
    # The lifecycle and all seven verified leaves compiled as one unit.
    "tacenta-proofs/translation/Translation/AxiomAuditSessionUnit.lean": [AUDIT_CALL],
    "tacenta-proofs/translation/Translation/AxiomAuditLifecycle.lean": [AUDIT_CALL],
    "tacenta-model/Model/AxiomAudit.lean": [
        "import Lean",
        "open Lean",
        '| "native_decide" => [' + BT + "Decidable.decide, " + BT + "Lean.reduceBool]",
        '| "decide" => [' + BT + "Decidable.decide, " + BT + "Lean.reduceBool]",
        BT + "Lean.reduceBool]",
    ],
}

# Instances and coercions. A statement pin prints the statement as Lean shows it,
# and Lean does not show the instance behind `<`, `+` or a numeral, or the
# function behind a coercion arrow; so a new `instance` in scope, or a function
# given the `coe` attribute, can change what a pinned statement means while its
# pin still matches. This is a textual guard on the stripped source, with these
# rules:
#   - an `instance` declaration (`local`, `scoped`, `noncomputable`, after
#     `open ... in` or anything else on its line) is refused unless its whole
#     declaration, from the line holding `instance` to the next blank line or
#     line at column 0, whitespace collapsed, is listed below for its file and
#     namespace, and each listed declaration must occur exactly once (a second
#     copy, in another namespace too, or a changed class or value on a
#     continuation line, is refused; matching is by text, so lines may move);
#   - `deriving instance C for T` is accepted when every `T` is a type the file
#     declares, and is otherwise an instance declaration like the above;
#   - an attribute list, `@[...]` or `attribute [...]`, read on the whole file
#     so that a list split over lines is one list, may not name `instance`,
#     `default_instance` or `coe`; and the tokens `coe` and `default_instance`
#     are refused anywhere in code, whatever carries them.
# It does not see an instance a dependency declares `scoped` and an `open` brings
# into scope, nor a class whose parent is a notation class (its use needs a
# binder the pin prints). A new entry is a diff for review.
INSTANCE_ALLOW = {
    "tacenta-model/Model/IdentityRecords.lean": [("Model.IdentityRecords", "local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) | .error a, .error b => if h : a = b then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl) | .ok a, .ok b => if h : a = b then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl) | .error _, .ok _ => isFalse (by intro h; cases h) | .ok _, .error _ => isFalse (by intro h; cases h)")],
    "tacenta-model/Model/InitiatorExpectation.lean": [("Model.InitiatorExpectation", "local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) | .error a, .error b => if h : a = b then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl) | .ok a, .ok b => if h : a = b then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl) | .error _, .ok _ => isFalse (by intro h; cases h) | .ok _, .error _ => isFalse (by intro h; cases h)")],
    "tacenta-model/Model/PersistedState.lean": [
        ("Model.PersistedState", "deriving instance DecidableEq for Model.State.State"),
        ("Model.PersistedState", "deriving instance DecidableEq for Model.SparseRatchet.State"),
        ("Model.PersistedState.TripleState", "deriving instance DecidableEq for Model.Triple.State")],
    "tacenta-proofs/translation/Translation/ErasureWitness.lean": [
        ("Tacenta.ErasureWitness", "instance : Fintype (BitVec 8) := Fintype.ofEquiv (Fin (2 ^ 8)) ⟨BitVec.ofFin, BitVec.toFin, fun _ => rfl, fun _ => rfl⟩"),
        ("Tacenta.ErasureWitness", "instance : Fintype Std.U8 := Fintype.ofEquiv (BitVec 8) ⟨fun b => ⟨b⟩, fun u => u.bv, fun _ => rfl, fun _ => rfl⟩"),
        ("Tacenta.ErasureWitness", "instance : Fintype Data32 := Fintype.ofEquiv _ data32Equiv.symm"),
        ("Tacenta.ErasureWitness", "noncomputable instance : Fintype F := Fintype.ofFinite F")],
    "tacenta-proofs/translation/Translation/ImportInv.lean": [("Tacenta.ImportInv", 'instance instDecidableEqArray {α : Type} [DecidableEq α] {N : Std.Usize} : DecidableEq (Array α N) := fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm')],
    "tacenta-proofs/translation/Translation/SessionUnitRatchetImportInv.lean": [
        ("Tacenta.SessionUnitRatchetImportInv", 'instance instDecidableEqArray {α : Type} [DecidableEq α] {N : Std.Usize} : DecidableEq (Array α N) := fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm')],
    "tacenta-proofs/translation/Translation/SessionUnitSpqrT1.lean": [("Tacenta.SessionUnitSpqrT1", 'instance spqrChainsInhabited : Inhabited Chains := ⟨{ send := none, receive := none }⟩')],
    "tacenta-proofs/translation/Translation/SpqrT1.lean": [("Tacenta.SpqrT1", 'instance spqrChainsInhabited : Inhabited Chains := ⟨{ send := none, receive := none }⟩')],
    "tacenta-proofs/translation/Translation/UnitSpqrT1.lean": [("Tacenta.UnitSpqrT1", 'instance spqrChainsInhabited : Inhabited Chains := ⟨{ send := none, receive := none }⟩')],
}
if os.environ.get("INSTANCE_ALLOW_COUNT") == "1":
    # The number of allow-listed instance declarations, for the line this scan prints when it passes.
    print(sum(len(entries) for entries in INSTANCE_ALLOW.values()))
    sys.exit(0)
INSTANCE_KEYWORD = re.compile(r"(?<![\w.«])instance(?![\w.'])")
# An attribute list, `@[...]` or `attribute [...]` (with `local` or `scoped` inside it), read on the
# whole stripped file so that a list split over lines is one list.
ATTRIBUTE_LIST = re.compile(r"(?:@|(?<![\w.«])attribute)\s*\[([^\]]*)\]")
INSTANCE_ATTRIBUTE_NAME = re.compile(r"(?<![\w.«])(?:instance|default_instance|coe)(?![\w.'])")
# `coe` and `default_instance` name nothing else in hand-written Lean here, so either token anywhere
# in code is refused as well, whatever attribute syntax carries it.
COERCION_TOKEN = re.compile(r"(?<![\w.«])(?:coe|default_instance)(?![\w.'])")
DECLARED_TYPE = re.compile(r"(?<![\w.«])(?:structure|inductive|class|abbrev|def)\s+([\w.'«»]+)")
DERIVING_INSTANCE = re.compile(r"(?<![\w.«])deriving\s+instance\s+(.*?)\s+for\s+(.*)$")

def instance_declarations(text, collapse):
    """Every instance declaration of the stripped text `text`: (line, namespace, declaration, kind). The
    declaration is the collapsed text from the line holding `instance` to the next blank line or the next
    line at column 0; the namespace is the dotted list of the open `namespace`s, sections and mutual blocks
    counting as frames with no name. A scope may carry modifiers (`noncomputable section`, `public section`);
    `namespace A.B` opens one frame per component and `end A.B` closes as many, as Lean does. `kind` is
    `deriving` for `deriving instance ... for` and `instance` otherwise."""
    lines = text.split("\n")
    frames, out = [], []
    for k, line in enumerate(lines):
        head = re.match(r"\s*(?:(?:noncomputable|public|private|protected)\s+)*(namespace|section|mutual|end)"
                        r"(?![\w.'])\s*([\w.'«»]*)", line)
        if head:
            parts = [p for p in head.group(2).split(".") if p] if head.group(2) else []
            if head.group(1) == "end":
                for _ in range(max(1, len(parts))):
                    if frames:
                        frames.pop()
            elif head.group(1) == "namespace":
                frames.extend(parts or [""])
            else:
                frames.extend([""] * max(1, len(parts)))
        for m in INSTANCE_KEYWORD.finditer(line):
            deriving = re.search(r"(?<![\w.«])deriving\s+$", line[:m.start()])
            end = k + 1
            while end < len(lines) and lines[end].strip() and lines[end][:1].isspace():
                end += 1
            decl = collapse(" ".join(lines[k:end]))
            out.append((k + 1, ".".join(f for f in frames if f), decl, "deriving" if deriving else "instance"))
    return out

# A lakefile that sets any Lean option, or names the option, is refused: none
# of the three sets any today, and the one option that matters here is the
# one the environment cannot record.
# The three lakefiles are pinned by content: what they build (libraries,
# their globs and roots, executables, requires) decides what the audits walk,
# the reach check requires and this scan reads, and a rule that read the
# library names alone missed a widened glob, a second library under an allowed
# name and three TOML spellings of a name. A lakefile change is a diff for
# review that updates its pin here.
LAKEFILE_SHA256 = {
    "tacenta-model/lakefile.lean": "b6fd4613b1f9965137ccb2e874e0ec6add5e90f9ec3c0b4c04cadd9c621b0868",
    "tacenta-proofs/lakefile.lean": "65d875dfd50cf217f84792ca0da1144ebc971fad4fa4290f79a12efb4eff0732",
    "tacenta-proofs/translation/lakefile.toml": "926a7a7bbd8649a0843a603cee690f61bb8dbad4bba0f5704b707440fd480bfd",
}
LAKEFILE_RULES = [
    ("skipKernelTC", re.compile(r"skipKernelTC")),
    ("lean-options", re.compile(
        r"\b(?:moreLeanArgs|weakLeanArgs|moreServerArgs|weakServerArgs|"
        r"moreGlobalServerArgs|leanOptions|weakLeanOptions|moreServerOptions|"
        r"serverOptions)\b")),
]

CHAR_LITERAL = re.compile(r"'(?:\\(?:x[0-9A-Fa-f]{2}|u[0-9A-Fa-f]{4}|.)|[^\\'])'")  # Lean accepts a raw newline here
# Lean's identifier characters, near enough: Python's `\w` less the Greek
# letters Lean reserves as tokens (`λ` is `fun`; `Π` and `Σ` are binders), so
# `λ'"'` is a `fun` followed by a char literal, as Lean reads it, and not an
# identifier swallowing a quote. Other characters `\w` accepts and Lean reads
# as the end of a token (`#check'"'`, Mathlib's `×ˢ`, superscripts) are caught
# by the ambiguity check in the main loop, which refuses a file whose stripped
# text depends on this rule at all.
IDENT_CHARS = re.compile(r"(?![\u03bb\u03a0\u03a3])[\w'!?\u00ab\u00bb]")

def strip_lean(text, keep_strings=False, spans=None, ident_rule=True, starts=None):
    """Remove line comments, block comments (docstrings included, and nested
    blocks), string literals (plain and raw) and character literals, replacing
    them with spaces so that line numbers survive. An identifier written in
    guillemets is one token whatever it contains: its contents become
    underscores, so a keyword or a comment opener inside it is not read.
    With keep_strings, string literals stay (comments still go), for the rules
    that look inside strings; with spans (a list), the (start, end) offsets of
    every string and raw-string literal are appended to it, so a rule can look
    at exactly the literals this stripper saw. With ident_rule=False, a `'` or
    `r"` is read as a literal start wherever it occurs, without asking whether
    the character before continues an identifier; a file whose stripped text
    differs between the two readings is refused by the caller, since the
    stripper decides from the previous character where Lean decides from the
    previous token (`#check'"'`, `×ˢ'"'`), and no honest first-party file
    depends on the difference.
    With starts (a list), the offset of every literal the stripper opened (string,
    raw string, char literal) and of every top-level `--` or `/-` is appended,
    for the adjacency rule in the caller. Kept in step with lean_code in
    attest.py, which is a separate copy."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        ch = text[i]
        two = text[i:i+2]
        if depth == 0 and two == "--":
            if starts is not None:
                starts.append(i)
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        if two == "/-":
            # At the top level Lean consumes the character after `/-` without
            # reading it (`/--` and `/-!` are one token, and `/-/- -/` is one
            # comment, not two), so three characters are taken at depth 0;
            # inside a comment Lean reads `/-` then whatever follows.
            if depth == 0 and starts is not None:
                starts.append(i)
            k = 3 if depth == 0 and i + 2 < n else 2
            depth += 1
            out.append("".join("\n" if c == "\n" else " " for c in text[i:i+k])); i += k; continue
        if depth > 0 and two == "-/":
            depth -= 1; out.append("  "); i += 2; continue
        if depth > 0:
            out.append("\n" if ch == "\n" else " "); i += 1; continue
        prev = text[i-1] if i else " "
        # Does the character before `i` continue an identifier? A `!` or `?`
        # does only when it ends one (`get!`); alone it is an operator, and a
        # char literal or raw string may follow it (`!'"'.isAlpha`).
        in_ident = ident_rule and bool(IDENT_CHARS.match(prev)) and (
            prev not in "!?" or (i >= 2 and bool(IDENT_CHARS.match(text[i-2])) and text[i-2] not in "!?"))
        if ch == "\u00ab":
            j = text.find("\u00bb", i)
            j = n if j < 0 else j + 1
            out.append("".join(c if c in "\u00ab\u00bb\n" else "_" for c in text[i:j])); i = j; continue
        if ch == "\"":
            j = i + 1
            while j < n and text[j] != "\"":
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            if spans is not None:
                spans.append((i, j))
            if starts is not None:
                starts.append(i)
            out.append(text[i:j] if keep_strings else "".join("\n" if c == "\n" else " " for c in text[i:j]))
            i = j; continue
        if ch == "r" and not in_ident:
            raw = re.compile(r'r(#*)"').match(text, i)
            if raw:
                close = '"' + raw.group(1)
                j = text.find(close, raw.end())
                j = n if j < 0 else j + len(close)
                if spans is not None:
                    spans.append((i, j))
                if starts is not None:
                    starts.append(i)
                out.append(text[i:j] if keep_strings else "".join("\n" if c == "\n" else " " for c in text[i:j]))
                i = j; continue
        if ch == "'" and not in_ident:
            lit = CHAR_LITERAL.match(text, i)
            if lit:
                if starts is not None:
                    starts.append(i)
                out.append("".join("\n" if c == "\n" else " " for c in text[i:lit.end()])); i = lit.end(); continue
        out.append(ch); i += 1
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

lean_paths, all_lean_paths = os.environ["LEAN_FILES"], os.environ["ALL_LEAN_FILES"]
lake_paths = os.environ["LAKEFILES"]
hits = []
# Lean ends a line at a newline or at CRLF and nowhere else; Python's default
# reading, used below, also ends one at a lone carriage return, so a file that
# holds one would be read differently here and by Lean (a line comment would end
# early for this scan and run on for Lean, and a quote after the return would
# open a string for the scan only). No honest first-party file holds a carriage
# return or a NUL, so any is refused before the rules below read the file.
for path in sorted(set(lean_paths.split()) | set(all_lean_paths.split()) | set(lake_paths.split())):
    with open(path, encoding="utf-8", newline="") as fh:
        exact = fh.read()
    if "\r" in exact or "\x00" in exact:
        hits.append(f"{path}: control-character: the file holds a carriage return or a NUL, which "
                    "Lean and this scan read differently; use plain newlines")
present = {path: set() for path in ALLOW}
for path in lean_paths.split():
    raw = open(path, encoding="utf-8").read()
    raw_lines = raw.split("\n")
    opened = []
    text = strip_lean(raw, starts=opened)
    # The stripper reads a `'` or `r"` as a literal start by the character
    # before it; Lean by the token before it. Where the two readings of a
    # file differ, the file is refused rather than guessed about.
    if strip_lean(raw, ident_rule=False) != text:
        hits.append(f"{path}: ambiguous-literal: a char literal or raw string in this file is read "
                    f"differently with and without the identifier rule; rewrite it with a space before the quote")
    # And every literal or comment the stripper opens must follow whitespace,
    # the start of the file, or an opening bracket or comma, each a complete
    # token of its own. Lean reads a literal or a comment opener only at a
    # token boundary; the stripper reads it anywhere. A token that ends in `'`
    # (`×'`), a comment opener inside a token (`//-`, `<--`) or an identifier
    # character Python's `\w` lacks (`℃`) would otherwise make the stripper open
    # a literal or comment where Lean reads code, and hide what follows. No
    # honest first-party file has one of these after anything else.
    for s in opened:
        if s > 0 and not raw[s - 1].isspace() and raw[s - 1] not in "([{,⟨":
            lineno = raw.count("\n", 0, s) + 1
            hits.append(f"{path}:{lineno}: adjacent-literal: a literal or comment opener follows "
                        f"{raw[s-1]!r}; put a space before it")
    allowed = ALLOW.get(path, [])
    # Code with its strings but without its comments: a tag or a string in a
    # comment is prose, in a string it is output.
    spans = []
    code_with_strings = strip_lean(raw, keep_strings=True, spans=spans)
    starts = {s for s, _ in spans}
    if path != AUDIT_IMPLEMENTATION:
        # An identifier ending in `!` and followed by a string literal (its
        # opening quote, as the stripper found it, so `"Done!"` is not one) or a
        # bracket, on the line or on the next: the interpolating and tracing
        # macros (`s!`, `m!`, `aesop_trace![`). The partial-function spelling
        # (`w.set! i`, `l.head!`, `(f x).get!`) is followed by neither and stays.
        # Read on the string-aware text, so a `!` inside a comment is blank.
        for m in re.finditer(r"(?<=\w)!\s*(?:\"|\[)", code_with_strings):
            if m.group(0).endswith("\"") and m.end() - 1 not in starts:
                continue
            lineno = code_with_strings.count("\n", 0, m.start()) + 1
            hits.append(f"{path}:{lineno}: bang-identifier: a `!` macro with a string or bracket")
    else:
        # In the audit's implementation, the one file that may call the
        # message heads: no string literal holds a brace at all. The stripper
        # cannot read an interpolation (`{…}` may hold a quote, a char literal,
        # a comment, anything), so the file builds its messages by
        # concatenation and interpolates nowhere; a brace in a literal is then
        # never honest. A plain string cannot hold an unescaped quote, so with
        # no interpolation anywhere the stripper's string boundaries are Lean's,
        # as far as eighteen hostile reads could tell (the eighteenth found a
        # lone carriage return ending a line for this scan and not for Lean;
        # the pre-pass above refuses such a file, and the rules below still run
        # over it, the refusal standing): the stripper is a scanner,
        # not Lean's lexer, and each spelling a read found is a case in
        # tooling/tests/run-lean-constructs-cases.sh.
        for s, e in spans:
            body = raw[s:e]
            if "{" in body or "}" in body:
                lineno = raw.count("\n", 0, s) + 1
                hits.append(f"{path}:{lineno}: brace-in-string: a string literal in the audit holds a "
                            f"brace: {body[:60]!r}")
    for lineno, codeline in enumerate(code_with_strings.split("\n"), 1):
        if path != AUDIT_IMPLEMENTATION and AUDIT_LINE_TAGS.search(codeline):
            hits.append(f"{path}:{lineno}: audit-line-literal: {codeline.strip()}")
        if PRINT_STRING.search(codeline):
            hits.append(f"{path}:{lineno}: print-to-log: {codeline.strip()}")
        # The stripper turns a guillemet identifier's contents into underscores
        # before the rules see it, so `«Lean».X` is read on the raw line.
        if GUILLEMET_LEAN.search(raw_lines[lineno - 1]):
            hits.append(f"{path}:{lineno}: lean-namespace: {raw_lines[lineno - 1].strip()}")
    if path in ALLOW and path != AUDIT_IMPLEMENTATION:
        for lineno, line in enumerate(text.split("\n"), 1):
            # Whole lines: Lean allows several commands on one line, so a
            # line is one import, one pin or one invocation, and nothing more.
            if line.strip() and not any(r.match(collapse(line)) for r in AUDIT_MODULE_LINES) \
                    and allowed_entry(collapse(raw_lines[lineno - 1]), allowed) is None:
                hits.append(f"{path}:{lineno}: audit-module-shape: an audit module holds only "
                            f"imports, pins and the audit invocations, one per line: {line.strip()}")
    # Instances and coercions, on the whole stripped file (names kept, so a guillemet name is read).
    whole = strip_lean(raw)
    for m in ATTRIBUTE_LIST.finditer(whole):
        if INSTANCE_ATTRIBUTE_NAME.search(m.group(1)):
            hits.append(f"{path}:{whole.count(chr(10), 0, m.start()) + 1}: instance-or-coe-attribute: "
                        f"{collapse(m.group(0))}")
    for m in COERCION_TOKEN.finditer(whole):
        hits.append(f"{path}:{whole.count(chr(10), 0, m.start()) + 1}: coercion-token: `{m.group(0)}`")
    # A type the file declares, by the name as the declaration writes it (no namespace resolution: a
    # qualified name in `for` that the file does not write as such is read as another file's type).
    declared = set(DECLARED_TYPE.findall(whole))
    allowed_instances = Counter(INSTANCE_ALLOW.get(path, []))
    seen_instances = Counter()
    for lineno, namespace, decl, kind in instance_declarations(whole, collapse):
        if kind == "deriving":
            derived = DERIVING_INSTANCE.search(decl)
            if derived and all(t.strip() in declared for t in derived.group(2).split(",")):
                continue
        seen_instances[(namespace, decl)] += 1
        if (namespace, decl) not in allowed_instances:
            hits.append(f"{path}:{lineno}: instance-declaration: {decl[:160]}")
        elif seen_instances[(namespace, decl)] > allowed_instances[(namespace, decl)]:
            hits.append(f"{path}:{lineno}: instance-declaration: a second copy of an allow-listed instance: "
                        f"{decl[:160]}")
    for key in allowed_instances:
        if seen_instances[key] == 0:
            hits.append(f"{path}: instance allow-list entry missing (the declaration moved, changed or went; "
                        f"edit INSTANCE_ALLOW in the same change): {key[0]}: {key[1][:160]}")
    for lineno, line in enumerate(text.split("\n"), 1):
        for kind, rule in LEAN_RULES:
            if rule.search(line):
                hits.append(f"{path}:{lineno}: {kind}: {line.strip()}")
        for kind, rule in ELAB_RULES:
            if kind == "interpolating-head" and path == AUDIT_IMPLEMENTATION:
                continue
            if rule.search(line):
                source = collapse(raw_lines[lineno - 1])
                entry = allowed_entry(source, allowed)
                if entry is not None:
                    present[path].add(entry)
                if entry == AUDIT_CALL:
                    # At column 0: an indented invocation is the argument of
                    # something on the line before (`with_weak_namespace`
                    # takes a command with no `in`).
                    if not raw_lines[lineno - 1].startswith("run_cmd"):
                        hits.append(f"{path}:{lineno}: indented-invocation: the audit invocation "
                                    f"does not start at column 0")
                    # An allowed invocation must stand on its own: a `… in`
                    # before it (`#guard_msgs (drop all) in`, `set_option … in`)
                    # would make it the body of another command, which could
                    # consume its refusal. The previous non-blank line of the
                    # stripped text (comments and strings blanked) must not
                    # end in `in`.
                    stripped = text.split("\n")
                    before = [l for l in stripped[:lineno - 1] if l.strip()]
                    if before and re.search(r"(?<![\w.'])in$", collapse(before[-1])):
                        hits.append(f"{path}:{lineno}: wrapped-invocation: the audit "
                                    f"invocation is the body of `{collapse(before[-1])}`")
                    # And nothing may follow it but another allowed invocation:
                    # a continuation line (`<|> pure ()`, `|> fun _ => pure ()`)
                    # would swallow its refusal or skip the walk, and a
                    # declaration after it would be outside the walk. So the
                    # next non-blank stripped line is the end of the file or
                    # an allowed invocation.
                    after = [(n, l) for n, l in enumerate(stripped[lineno:], lineno + 1) if l.strip()]
                    if after:
                        n_after, l_after = after[0]
                        if allowed_entry(collapse(raw_lines[n_after - 1]), allowed) is None:
                            hits.append(f"{path}:{lineno}: followed-invocation: the audit "
                                        f"invocation is followed at line {n_after} by "
                                        f"`{collapse(l_after)}`; only another audit invocation "
                                        f"or the end of the file may follow it")
                if entry is None:
                    hits.append(f"{path}:{lineno}: {kind}: {line.strip()}")
# Lean only emits the diagnostic the no-sorry gate scans when this option is
# enabled. It must remain enabled in generated translation as well as the
# hand-written proof/model files, so this scan is deliberately broader than
# the structural rules above.
for path in all_lean_paths.split():
    text = strip_lean(open(path, encoding="utf-8").read())
    # Search the complete file so a line break (or spaces around the dot)
    # cannot split the option name and evade the gate.
    for match in re.finditer(r"set_option\s+warn\s*\.\s*sorry\s+false", text):
        lineno = text.count("\n", 0, match.start()) + 1
        line = text.splitlines()[lineno - 1] if text.splitlines() else ""
        hits.append(f"{path}:{lineno}: sorry-warning-disabled: {line.strip()}")

for path, lines in ALLOW.items():
    for source in lines:
        if source not in present[path]:
            hits.append(f"{path}: allow-listed line missing (the audit is not invoked, "
                        f"or its implementation changed): {entry_text(source)}")
for path in lake_paths.split():
    raw = open(path, encoding="utf-8").read()
    text = strip_toml(raw) if path.endswith(".toml") else strip_lean(raw)
    for lineno, line in enumerate(text.split("\n"), 1):
        for kind, rule in LAKEFILE_RULES:
            if rule.search(line):
                hits.append(f"{path}:{lineno}: {kind}: {line.strip()}")
    with open(path, "rb") as fh:
        digest = hashlib.sha256(fh.read()).hexdigest()
    if LAKEFILE_SHA256.get(path) != digest:
        hits.append(f"{path}: lakefile-pinned: the lakefile's content ({digest[:12]}…) is not the pinned one; "
                    f"a change to what it builds is a diff for review that updates LAKEFILE_SHA256 here")
for path in LAKEFILE_SHA256:
    if path not in lake_paths.split():
        hits.append(f"{path}: lakefile-pinned: the pinned lakefile is missing")
print("\n".join(hits))
PY
found=$(LEAN_FILES="$lean_files" ALL_LEAN_FILES="$all_lean_files" LAKEFILES="$lakefiles" python3 "$program")

status=0
if [ -n "$found" ]; then
  echo "" >&2
  echo "REFUSING: hand-written Lean declares something the proof gates cannot see:" >&2
  echo "$found" | sed 's/^/    /' >&2
  echo "" >&2
  echo "An axiom, an opaque, an implemented_by/extern attribute, a partial def, an" >&2
  echo "unsafe declaration, a name in the compiler's _unsafe_rec/_native namespace," >&2
  echo 'a disabled warn.sorry diagnostic, a debug.* option, or a lakefile that sets Lean options widens the trust' >&2
  echo "base of every theorem downstream of it without a compiler warning; an instance" >&2
  echo "declaration not on INSTANCE_ALLOW, or an instance, default_instance or coe attribute," >&2
  echo "can change what a pinned statement means while its pin still matches, since Lean" >&2
  echo "prints neither the instance nor the coercion function; and" >&2
  echo "elaboration-time code (run_cmd, #eval, elab, macro, syntax, initialize," >&2
  echo "addDecl, any reference to the Lean namespace) could plant a compiler-trust" >&2
  echo "axiom the environment audit accepts by shape. If one is genuinely needed," >&2
  echo "record it in LIMITATIONS.md and add it to the allow-list in this script" >&2
  echo "and in Model/AxiomAudit.lean with the reason." >&2
  status=1
fi

count=$(echo "$lean_files" | wc -l | tr -d ' ')
allowed_instances=$(INSTANCE_ALLOW_COUNT=1 python3 "$program")
if [ "$status" -eq 0 ]; then
  echo "check-lean-constructs: $count first-party Lean files declare no axiom, opaque, implemented_by, extern, partial, unsafe, compiler-namespace name or debug option, and carry no elaboration-time code outside the audit's 7 allow-listed invocations and its implementation, no instance declaration outside the $allowed_instances allow-listed and no instance, default_instance or coe attribute or token; 3 lakefiles set no Lean option and match their pins"
fi
exit "$status"
