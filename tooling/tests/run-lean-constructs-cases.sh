#!/usr/bin/env bash
# Fail if `tacenta-proofs/scripts/check-lean-constructs.sh` accepts an audit invocation that does
# not stand alone, or an invoking line that is not the allow-listed one.
#
# The scan allow-lists the seven audit invocations by file and exact line and requires each to
# stand alone: at column 0, not the body of a `… in` wrapper, followed by nothing but another
# invocation or the end of the file, in a module that holds only imports, pins and the invocation,
# one per line; around them it refuses a notation, the audit's log tags in code or strings, printed
# strings, `#reduce`, `dbg_trace`, interpolated strings, and in the audit a string literal holding a brace,
# each a way found at a review of consuming the audit's refusal, redirecting its name, forging its
# log lines or hiding text from the stripper. Each case here plants one such shape in a copy of
# the audit modules and runs the scan on the copy; the repository is never written. The copy holds
# only what the scan reads for these rules: the eight audit modules, the lakefiles and the scan,
# plus one planted model module where a case needs a hand-written file that is not an audit
# module.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

fresh_copy() {
  rm -rf "$work/T"
  mkdir -p "$work/T/tacenta-model/Model" "$work/T/tacenta-model/Properties" "$work/T/tacenta-proofs/Proofs" \
    "$work/T/tacenta-proofs/scripts" "$work/T/tacenta-proofs/translation/Translation"
  cp "$root/tacenta-model/Model/AxiomAudit.lean" "$work/T/tacenta-model/Model/"
  cp "$root/tacenta-model/Properties/AxiomAudit.lean" "$work/T/tacenta-model/Properties/"
  cp "$root/tacenta-proofs/Proofs/AxiomAudit.lean" "$work/T/tacenta-proofs/Proofs/"
  cp "$root"/tacenta-proofs/translation/Translation/AxiomAudit*.lean "$work/T/tacenta-proofs/translation/Translation/"
  cp "$root/tacenta-proofs/scripts/check-lean-constructs.sh" "$work/T/tacenta-proofs/scripts/"
  for f in tacenta-model/lakefile.lean tacenta-model/lakefile.toml tacenta-proofs/lakefile.lean \
      tacenta-proofs/lakefile.toml tacenta-proofs/translation/lakefile.toml tacenta-proofs/translation/lakefile.lean; do
    [ -f "$root/$f" ] && cp "$root/$f" "$work/T/$f"
  done
  return 0
}

run_scan() { # exit code in $rc, output in $out
  set +e
  out=$(cd "$work/T" && bash tacenta-proofs/scripts/check-lean-constructs.sh 2>&1)
  rc=$?
  set -e
}

pass=0
fail=0
wrong() { fail=$((fail + 1)); echo "WRONG  $1: $2"; echo "$out" | sed 's/^/    /' | head -12; }

refused_with() { # <case> <kind>: exit 1 and a hit of that kind
  run_scan
  if [ "$rc" -eq 0 ]; then wrong "$1" "accepted (exit 0)"; return; fi
  if [[ "$out" != *"$2"* ]]; then wrong "$1" "refused, but not as $2"; return; fi
  pass=$((pass + 1))
}

edit() { # <file under T> <old> <new>: exactly one occurrence
  python3 - "$work/T/$1" "$2" "$3" <<'PY'
import sys
from pathlib import Path
p = Path(sys.argv[1]); t = p.read_text(); a, b = sys.argv[2], sys.argv[3]
if t.count(a) != 1:
    raise SystemExit(f"{p.name}: {a!r} occurs {t.count(a)} time(s), expected once")
p.write_text(t.replace(a, b))
PY
}

L=tacenta-proofs/translation/Translation/AxiomAuditLifecycle.lean
P=tacenta-proofs/Proofs/AxiomAudit.lean
M=tacenta-model/Model/Planted.lean
A="run_cmd _root_.Model.AxiomAudit.run"

# 0. The copy of the committed sources passes.
fresh_copy; run_scan
if [ "$rc" -ne 0 ]; then wrong unmodified "the unmodified copy is refused"; else pass=$((pass + 1)); fi

# 1. A wrapper on the line before an invocation: a bare `#guard_msgs in` (a line an audit module may
#    hold, so only the wrapper rule sees it), `#guard_msgs (drop all) in`, and `set_option … in`
#    with a line comment, a block comment or `open … in` between; planted before the first
#    invocation of a module.
fresh_copy; edit $P "$A" "#guard_msgs in
$A"
refused_with wrapper-before wrapped-invocation
fresh_copy; edit $P "$A" "#guard_msgs (drop all) in
$A"
refused_with wrapper-drop-all wrapped-invocation
fresh_copy; edit $P "$A" "set_option maxHeartbeats 1 in

-- a note between
$A"
refused_with wrapper-with-comment-between wrapped-invocation
fresh_copy; edit $P "$A" "set_option maxHeartbeats 1 in
/- a block
   comment between -/
$A"
refused_with wrapper-with-block-comment wrapped-invocation
fresh_copy; edit $P "$A" "open Nat in
$A"
refused_with open-in-wrapper wrapped-invocation

# 2. An indented invocation is the argument of a wrapper that needs no `in`.
fresh_copy; edit $L "$A" "  $A"
refused_with indented-invocation indented-invocation

# 3. A continuation, a declaration or a pin after the last invocation. The pin is a line an audit
#    module may hold, so only the "followed by" rule refuses it.
fresh_copy; printf '  <|> pure ()\n' >> "$work/T/$L"
refused_with continuation-after followed-invocation
fresh_copy; printf '\ntheorem late : True := trivial\n' >> "$work/T/$L"
refused_with declaration-after followed-invocation
fresh_copy; printf '\ntheorem late : True := trivial\n' >> "$work/T/$P"
refused_with declaration-after-axiom-audit followed-invocation
fresh_copy; printf '\n#check Nat\n' >> "$work/T/$L"
refused_with pin-after-invocation followed-invocation

# 4. Other prefixes, or a deleted invocation, are not the allowed line.
fresh_copy; edit $L "\`Model, \`Properties, \`Proofs, \`Translation]" "\`Model, \`Properties, \`Translation]"
refused_with narrowed-prefixes "allow-listed line missing"
fresh_copy; python3 - "$work/T/$L" <<'PY2'
import sys
from pathlib import Path
p = Path(sys.argv[1]); t = p.read_text()
p.write_text("\n".join(l for l in t.split("\n") if not l.startswith("run_cmd _root_.Model.AxiomAudit.run")))
PY2
refused_with deleted-invocation "allow-listed line missing"

# 5. The invoking modules hold only imports, pins and the invocation, one per line: a `namespace`,
#    an `open`, a declaration, or two commands on one line (`#check Nat namespace Translation`)
#    could make the name resolve to a shadow or put a declaration outside the walk.
fresh_copy; edit $L "$A" "namespace Translation
$A"
refused_with namespace-in-audit-module audit-module-shape
fresh_copy; edit $L "$A" "open Nat
$A"
refused_with open-in-audit-module audit-module-shape
fresh_copy; edit $P "$A" "def Model.AxiomAudit.shadow : Nat := 0
$A"
refused_with declaration-in-audit-module audit-module-shape
fresh_copy; edit $L "$A" "#check Nat namespace Translation
$A"
refused_with two-commands-on-a-line audit-module-shape

# 6. Around the invocations, in any hand-written module: a notation on the audit's name; the
#    audit's log tags in a string (in a comment they are prose); a printed string, `#reduce` and
#    `dbg_trace`; an interpolated string; and, in the audit's implementation, a quote inside an
#    interpolation, which the stripper reads as a string followed by a comment.
fresh_copy; printf 'notation "_root_.Model.AxiomAudit.run" => fun {α : Type} (_ : Array α) => pure ()\n' > "$work/T/$M"
refused_with notation-hijack notation-family
fresh_copy; printf 'def viaRoot := _root_.Lean.Name.anonymous\n' > "$work/T/$M"
refused_with root-lean-namespace lean-namespace
fresh_copy; printf 'def viaGuillemets := «Lean».Name.anonymous\n' > "$work/T/$M"
refused_with guillemet-lean-namespace lean-namespace
fresh_copy; printf 'infix:50 " ⊕⊕ " => Nat.add\n' > "$work/T/$M"
refused_with infix-notation notation-family
fresh_copy; printf 'def forged : String := "audit-axiom: Translation.TacentaX forged"\n' > "$work/T/$M"
refused_with audit-tag-in-string audit-line-literal
fresh_copy; printf 'def honestComment : Nat := 0 -- the audit-axiom: lines are compared\n' > "$work/T/$M"
run_scan; if [ "$rc" -ne 0 ]; then wrong tag-in-comment-accepted "a tag in a comment is refused"; else pass=$((pass + 1)); fi
fresh_copy; printf '#print "a line for the log"\n' > "$work/T/$M"
refused_with print-string print-to-log
fresh_copy; printf 'def five : Nat := 5\n#reduce five\n' > "$work/T/$M"
refused_with reduce print-to-log
fresh_copy; printf 'def traced : Nat := dbg_trace "a line for the log" fun _ => 0\n' > "$work/T/$M"
refused_with dbg-trace print-to-log
fresh_copy; printf 'def greet (n : Nat) : String := s! "{n}"\n' > "$work/T/$M"
refused_with interpolated-string bang-identifier
fresh_copy; printf 'def msg : MetaM Unit := do trace[debug] "a line"\n' > "$work/T/$M"
refused_with interpolating-head interpolating-head
fresh_copy; printf '\n[[lean_lib]]\nname = "Extra"\n' >> "$work/T/tacenta-proofs/translation/lakefile.toml"
refused_with extra-library lakefile-pinned
fresh_copy; sed -i.bak 's/globs = \["Translation.\*"\]/globs = ["Translation.*", "Extra.*"]/' "$work/T/tacenta-proofs/translation/lakefile.toml" && rm -f "$work/T/tacenta-proofs/translation/lakefile.toml.bak"
refused_with globs-widened lakefile-pinned
fresh_copy; printf 'def msg (n : Nat) : String := s!\n  "{n}"\n' > "$work/T/$M"
refused_with bang-string-on-next-line bang-identifier
fresh_copy; printf 'def msg : MetaM Unit := do aesop_trace![debug] "a line"\n' > "$work/T/$M"
refused_with aesop-trace interpolating-head
fresh_copy; printf 'def msg : MacroM Unit := do Macro.trace[debug]\n  "a line"\n' > "$work/T/$M"
refused_with qualified-trace interpolating-head
fresh_copy; printf 'def msg : TacticM Unit := do trace_goal[debug] "a line"\n' > "$work/T/$M"
refused_with trace-goal interpolating-head
fresh_copy; printf 'def msg : MetaM Unit := do logNamedErrorAt .missing \x60name "a line"\n' > "$work/T/$M"
refused_with named-at-head interpolating-head
fresh_copy; printf 'def msg (n : Nat) : String := s!"{n}"\n' > "$work/T/$M"
refused_with bang-string-same-line bang-identifier
fresh_copy; printf 'def hiddenSplit (r : Syntax) : MetaM Unit := throwErrorAt r "{\n  "--"}" -- run_cmd Lean.logInfo "x"\n' >> "$work/T/tacenta-model/Model/AxiomAudit.lean"
refused_with unbalanced-brace-across-lines brace-in-string
fresh_copy; printf 'def jsonFragment : String := "{ \\"k\\": "\n' > "$work/T/$M"
run_scan; if [ "$rc" -ne 0 ]; then wrong plain-brace-elsewhere-accepted "a plain string with a lone brace outside the audit is refused"; else pass=$((pass + 1)); fi
#    The six interpolations a brace count cannot read, each in the audit's implementation.
A6="$work/T/tacenta-model/Model/AxiomAudit.lean"
fresh_copy; printf 'def h1 : String := s!"{toString \x27}\x27 ++ "--"}" -- run_cmd Lean.logInfo "x"\n' >> "$A6"
refused_with brace-char-literal-in-interpolation brace-in-string
fresh_copy; printf 'def h6 : String := s!"{toString \x27}\x27 ++ \\\n  "--"}"\n' >> "$A6"
refused_with brace-with-string-gap brace-in-string
fresh_copy; printf 'def h7 : String := r"{"\n' >> "$A6"
refused_with brace-in-raw-string brace-in-string
fresh_copy; printf 'def h2 : String := s!"{ /- } -/ "--"}" -- run_cmd Lean.logInfo "x"\n' >> "$A6"
refused_with brace-comment-in-interpolation brace-in-string
fresh_copy; printf 'def h3 : String := s!"}{\n  "--"}"\n' >> "$A6"
refused_with brace-before-interpolation brace-in-string
fresh_copy; printf 'def h4 : String := s!"\\\\{ "--"}"\n' >> "$A6"
refused_with brace-after-escaped-backslash brace-in-string
fresh_copy; printf 'def h5 : String := r"\\" ++ s!"{"--"}" ++ r"\\"\n' >> "$A6"
refused_with brace-beside-raw-strings brace-in-string
fresh_copy; printf 'def ok : String := "Done!"\n' > "$work/T/$M"
run_scan; if [ "$rc" -ne 0 ]; then wrong bang-at-string-end-accepted "a string ending in a bang is refused"; else pass=$((pass + 1)); fi


# 7. Spellings the stripper once read differently from Lean, each followed by hidden
#    elaboration-time code: a doc comment opened by `/--` whose fourth character is `/`; a char
#    literal after the `!` operator; a raw string after the `!` operator.
fresh_copy; printf '/--/ " -/ run_cmd Lean.logInfo "x"\ndef d : Nat := 0 -- "\n' > "$work/T/$M"
refused_with doc-comment-token "elab-time-command"
fresh_copy; printf 'def b : Bool := !\x27"\x27.isAlpha\nrun_cmd Lean.logInfo "x" -- "\n' > "$work/T/$M"
refused_with char-literal-after-operator "elab-time-command"
fresh_copy; printf 'def e : Bool := !r"\\".isEmpty\nrun_cmd Lean.logInfo "x" -- "\n' > "$work/T/$M"
refused_with raw-string-after-operator "elab-time-command"
#    Inside a comment `/--` is `/-` then `-/` to Lean: the three-character token is top-level only.
fresh_copy; printf '/- /--/ -/ run_cmd Lean.logInfo "x" -- -/\n' > "$work/T/$M"
refused_with doc-token-in-comment "elab-time-command"
#    `λ` is the `fun` token, not an identifier character: a char literal may follow it.
fresh_copy; printf 'def t : Char → Nat := λ\x27"\x27 => 0\nrun_cmd Lean.logInfo "x" -- "\n' > "$work/T/$M"
refused_with lambda-before-char-literal "elab-time-command"
fresh_copy; cat > "$work/T/$M" <<'LEAN'
def u : String → Bool := λr"\" => true
run_cmd Lean.logInfo "x" -- "
LEAN
refused_with lambda-before-raw-string "elab-time-command"
#    A token that ends in a letter-like character, followed directly by a char literal or a raw
#    string: Lean reads the literal by the token before it, the stripper by the character, so a
#    file whose stripped text depends on that rule is refused outright.
fresh_copy; cat > "$work/T/$M" <<'LEAN'
#check'"'
run_cmd Lean.logInfo "x" -- '
LEAN
refused_with token-before-char-literal ambiguous-literal
fresh_copy; cat > "$work/T/$M" <<'LEAN'
#checkr"\"
run_cmd Lean.logInfo "x" -- "
LEAN
refused_with token-before-raw-string ambiguous-literal
#    The same rule on a file that hides nothing: `x'a'` is one identifier to Lean and to the stripper's
#    identifier reading, a name and a char literal to its other reading, so the file is refused for the
#    difference alone. Every other text in this section is also refused by the adjacency rule below;
#    this one is refused by the ambiguity rule only, which is what shows that rule's own verdict.
fresh_copy; printf 'def f := x\x27a\x27\n' > "$work/T/$M"
refused_with identifier-with-char-literal-shape ambiguous-literal
#    At the top level Lean consumes the character after `/-` unread: `/-/- -/` is one comment.
fresh_copy; printf '/-/- -/ run_cmd Lean.logInfo "x" -- -/\n' > "$work/T/$M"
refused_with slash-after-comment-opener "elab-time-command"
#    A literal or a comment opener the stripper takes must follow whitespace, an opening bracket or a
#    comma: Lean reads them only
#    at a token boundary, so a token ending in `'` (`×'`), a comment opener inside a token (`//-`)
#    or an identifier character outside Python's `\w` (`℃`) could otherwise open one where Lean
#    reads code.
fresh_copy; cat > "$work/T/$M" <<'LEAN'
#check_failure Nat ×'"' ++ "
run_cmd Lean.logInfo "x" -- "
LEAN
refused_with token-ending-in-prime adjacent-literal
fresh_copy; cat > "$work/T/$M" <<'LEAN'
def s := { x : Int //-x = 0 }
run_cmd Lean.logInfo "x" -- -/
LEAN
refused_with comment-opener-inside-token adjacent-literal
fresh_copy; cat > "$work/T/$M" <<'LEAN'
#guard_msgs (drop error) in
set_option ℃'"' "
run_cmd Lean.logInfo (Lean.MessageData.ofName `x) -- "
LEAN
refused_with identifier-character-outside-w adjacent-literal
fresh_copy; cat > "$work/T/$M" <<'LEAN'
#check_failure fun '
'"' x " => 0
run_cmd Lean.logInfo (Lean.MessageData.ofName `hidden) -- "
LEAN
refused_with newline-in-char-literal adjacent-literal
#    A lone carriage return: Lean ends a line at a newline or CRLF only, Python's default reading
#    at a lone CR too, so a line comment ends early for the scan and a quote after the CR opens a
#    string the scan alone sees. Any carriage return or NUL is refused before the file is read.
fresh_copy; printf 'def a : Nat := 0 -- \r" hides\nrun_cmd Lean.logInfo (Lean.MessageData.ofName `x) -- "\n' > "$work/T/$M"
refused_with carriage-return control-character
fresh_copy; printf 'def hidden : String := s!"{"--"}" -- run_cmd Lean.logInfo "x"\n' >> "$work/T/tacenta-model/Model/AxiomAudit.lean"
refused_with quote-in-interpolation brace-in-string
fresh_copy; printf 'def hiddenAt (r : Syntax) : MetaM Unit := throwErrorAt r "{"--"}" -- run_cmd Lean.logInfo "x"\n' >> "$work/T/tacenta-model/Model/AxiomAudit.lean"
refused_with quote-in-interpolation-after-argument brace-in-string

# Instances and coercions: Lean prints neither the instance behind a notation nor the function
# behind a coercion, so either can change what a pinned statement means with its pin unchanged.
plant_refused() { # <case> <kind> <Lean text>
  fresh_copy; printf '%s\n' "$3" > "$work/T/$M"
  refused_with "$1" "$2"
}
plant_refused instance-lt instance-declaration $'namespace Planted\ninstance : LT Nat := ⟨fun _ _ => False⟩\nend Planted'
plant_refused local-instance-ofnat instance-declaration $'namespace Planted\nlocal instance : OfNat Nat 96 := ⟨97⟩\nend Planted'
plant_refused scoped-instance-hadd instance-declaration $'namespace Planted\nscoped instance : HAdd Nat Nat Nat := ⟨fun a _ => a⟩\nend Planted'
plant_refused instance-with-priority instance-declaration 'noncomputable instance (priority := high) : Inhabited Nat := ⟨1⟩'
plant_refused coe-attribute instance-or-coe-attribute '@[coe] def indexOf (_x : Nat) : Nat := 0'
plant_refused coe-attribute-added-later instance-or-coe-attribute $'def indexOf (_x : Nat) : Nat := 0\nattribute [coe] indexOf'
plant_refused local-instance-attribute instance-or-coe-attribute $'def bogusLT : LT Nat := ⟨fun _ _ => False⟩\nattribute [local instance] bogusLT in\ntheorem planted : True := trivial'
plant_refused instance-attribute-in-a-list instance-or-coe-attribute '@[simp, instance] def bogusLE : LE Nat := ⟨fun _ _ => True⟩'
plant_refused default-instance-attribute instance-or-coe-attribute '@[default_instance] def bogusAdd : Add Nat := ⟨fun a _ => a⟩'
# The same names in attribute lists split over lines, which Lean reads as one list, and the other
# attribute and declaration forms.
plant_refused coe-in-a-two-line-list instance-or-coe-attribute $'@[simp,\n  coe] def indexOf (_x : Nat) : Nat := 0'
plant_refused coe-attribute-over-two-lines instance-or-coe-attribute $'def indexOf (_x : Nat) : Nat := 0\nattribute\n  [coe] indexOf'
plant_refused default-instance-in-a-two-line-list instance-or-coe-attribute $'@[simp,\n  default_instance] def bogusAdd : Add Nat := ⟨fun a _ => a⟩'
plant_refused instance-attribute-added-later instance-or-coe-attribute $'def bogusLT : LT Nat := ⟨fun _ _ => False⟩\nattribute [instance] bogusLT'
plant_refused coe-token-alone coercion-token 'def planted : Nat := coe 0'
plant_refused default-instance-token-alone coercion-token 'def planted : Nat := default_instance'
plant_refused open-in-instance instance-declaration $'open Nat in instance : LT Nat := ⟨fun _ _ => False⟩'
plant_refused deriving-instance-for-another-files-type instance-declaration $'deriving instance BEq for Model.State.State'
# The coercion counterexample of the review, in the module itself: a `coe` function in a two-line list,
# the pinned conjunct `c.index.val = 0` rewritten through it to a statement that is always true, and the
# proof bullet closed by `rfl`. Lean accepts the module with its pin unchanged; this scan refuses it.
fresh_copy; mkdir -p "$work/T/tacenta-proofs/translation/Translation"
python3 - "$root/tacenta-proofs/translation/Translation/UnitHeldKemWitness.lean" \
  "$work/T/tacenta-proofs/translation/Translation/UnitHeldKemWitness.lean" <<'PY3'
import sys
t = open(sys.argv[1]).read()
anchor = "/-- **The header encoder.**"
assert t.count(anchor) == 1
t = t.replace(anchor, "@[simp,\n  coe] def indexOf (_x : Std.U16) : Nat := 0\n\n" + anchor)
old = "      c.index.val = 0 ∧ CodewordOf m c ∧ EncoderRefines enc1 ⟨m, 1⟩ ∧\n"
assert t.count(old) == 1
t = t.replace(old, "      indexOf c.index = 0 ∧ CodewordOf m c ∧ EncoderRefines enc1 ⟨m, 1⟩ ∧\n")
old = "  · simp [Model.Braid.encode, Model.Braid.Encoder.nextChunk, hnext0] at hidx ⊢\n"
assert t.count(old) == 1
open(sys.argv[2], "w").write(t.replace(old, "  · rfl\n"))
PY3
refused_with coercion-counterexample-in-held-encoder instance-or-coe-attribute

# An allow-listed declaration is matched whole, in its namespace and once: a copy in another namespace with
# another class on its continuation line, an exact copy in another namespace, a second copy in the same
# namespace, a changed class on a continuation line in place, and a changed `default` value.
inst_copy() { # <file> : copy one allow-listed module into the copy
  mkdir -p "$work/T/tacenta-proofs/translation/Translation"
  cp "$root/tacenta-proofs/translation/Translation/$1" "$work/T/tacenta-proofs/translation/Translation/$1"
}
I=tacenta-proofs/translation/Translation/ImportInv.lean
fresh_copy; inst_copy ImportInv.lean
printf '\nnamespace Evil\ninstance instDecidableEqArray {α : Type} [DecidableEq α] {N : Std.Usize} :\n    LT (Array α N) := ⟨fun _ _ => False⟩\nend Evil\n' >> "$work/T/$I"
refused_with allow-listed-first-line-new-class instance-declaration
fresh_copy; inst_copy ImportInv.lean
printf '\nnamespace Evil\ninstance instDecidableEqArray {α : Type} [DecidableEq α] {N : Std.Usize} :\n    DecidableEq (Array α N) :=\n  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm\nend Evil\n' >> "$work/T/$I"
refused_with allow-listed-copy-in-another-namespace instance-declaration
fresh_copy; inst_copy ImportInv.lean
edit $I $'instance instDecidableEqArray {α : Type} [DecidableEq α] {N : Std.Usize} :\n    DecidableEq (Array α N) :=\n  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm\n' \
  $'instance instDecidableEqArray {α : Type} [DecidableEq α] {N : Std.Usize} :\n    DecidableEq (Array α N) :=\n  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm\n\ninstance instDecidableEqArray {α : Type} [DecidableEq α] {N : Std.Usize} :\n    DecidableEq (Array α N) :=\n  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm\n'
refused_with allow-listed-second-copy "a second copy of an allow-listed instance"
fresh_copy; inst_copy ImportInv.lean
edit $I $'    DecidableEq (Array α N) :=\n  fun a b => decidable_of_iff' $'    LT (Array α N) :=\n  fun a b => decidable_of_iff'
refused_with allow-listed-continuation-class-changed instance-declaration
fresh_copy; inst_copy ImportInv.lean
edit $I $'instance instDecidableEqArray {α : Type} [DecidableEq α] {N : Std.Usize} :\n    DecidableEq (Array α N) :=\n  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm\n' \
  $'namespace Evil\ninstance instDecidableEqArray {α : Type} [DecidableEq α] {N : Std.Usize} :\n    DecidableEq (Array α N) :=\n  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm\nend Evil\n'
refused_with allow-listed-moved-to-another-namespace instance-declaration
fresh_copy; inst_copy SpqrT1.lean
edit tacenta-proofs/translation/Translation/SpqrT1.lean $'  ⟨{ send := none, receive := none }⟩' $'  ⟨{ send := none, receive := some default }⟩'
refused_with allow-listed-default-value-changed instance-declaration
fresh_copy; inst_copy ImportInv.lean
edit $I $'instance instDecidableEqArray {α : Type}' $'\ninstance instDecidableEqArray {α : Type}'
run_scan
if [ "$rc" -ne 0 ]; then wrong allow-listed-moved-down-a-line "an allow-listed instance moved by a line is refused"; else pass=$((pass + 1)); fi
# Scopes with modifiers and dotted names open and close frames as Lean does: a `noncomputable section ... end`
# and a `namespace A.B ... end A.B` above an allow-listed instance leave it in its namespace, accepted.
fresh_copy; inst_copy SpqrT1.lean
edit tacenta-proofs/translation/Translation/SpqrT1.lean $'instance spqrChainsInhabited' \
  $'noncomputable section\ndef plantedA : Nat := 1\nend\n\nnamespace Planted.Inner\ndef plantedB : Nat := 2\nend Planted.Inner\n\ninstance spqrChainsInhabited'
run_scan
if [ "$rc" -ne 0 ]; then wrong scopes-with-modifiers-and-dotted-names "an allow-listed instance after a noncomputable section and a dotted namespace is refused"; else pass=$((pass + 1)); fi
fresh_copy; inst_copy SpqrT1.lean
edit tacenta-proofs/translation/Translation/SpqrT1.lean $'instance spqrChainsInhabited' \
  $'@[expose] public section\ndef plantedC : Nat := 3\nend\n\ninstance spqrChainsInhabited'
run_scan
if [ "$rc" -ne 0 ]; then wrong scope-with-an-attribute "an allow-listed instance after an @[expose] public section is refused"; else pass=$((pass + 1)); fi

# A derived structural instance is not refused, nor the word in a comment.
fresh_copy; printf 'structure PlantedS where\n  x : Nat\nderiving Repr\nderiving instance BEq for PlantedS\n-- an instance in prose\n' > "$work/T/$M"
run_scan
if [ "$rc" -ne 0 ]; then wrong derived-instance-accepted "a derived instance is refused"; else pass=$((pass + 1)); fi
# An allow-listed instance whose line changed is refused as a new declaration; one that is no longer an
# instance leaves its entry missing, which is refused too, so the list stays exact.
fresh_copy; mkdir -p "$work/T/tacenta-proofs/translation/Translation"
sed 's/^instance instDecidableEqArray /instance instDecidableEqArray2 /' \
  "$root/tacenta-proofs/translation/Translation/ImportInv.lean" > "$work/T/tacenta-proofs/translation/Translation/ImportInv.lean"
refused_with allow-listed-instance-changed instance-declaration
fresh_copy; mkdir -p "$work/T/tacenta-proofs/translation/Translation"
sed 's/^instance instDecidableEqArray /def instDecidableEqArray /' \
  "$root/tacenta-proofs/translation/Translation/ImportInv.lean" > "$work/T/tacenta-proofs/translation/Translation/ImportInv.lean"
refused_with allow-listed-instance-gone "instance allow-list entry missing"

if [ $fail -ne 0 ]; then
  echo "lean-constructs-cases: $fail of $((pass + fail)) cases wrong"
  exit 1
fi
echo 'lean-constructs-cases: '"$pass"' cases (the unmodified copy and a tag in a comment accepted; a wrapper before an invocation, with a line or block comment between, or open-in; an indented invocation; a continuation, a declaration and a pin after the last invocation, in two packages; narrowed prefixes and a deleted invocation; a namespace, an open, a declaration and two commands on a line in an audit module; a notation and an infix; the Lean namespace by _root_ and in guillemets; the audit log tag in a string, a printed string, #reduce, dbg_trace and an interpolated string elsewhere; an interpolating head, a qualified, a goal and an aesop trace, a named-at head, and a bang macro with its string on the same or the next line elsewhere; a string literal holding a brace in the audit, in the shapes a brace count cannot read, with a string gap and in a raw string (a plain lone brace elsewhere, and a string ending in a bang, accepted); a doc comment opened by `/--/`, a `/--` inside a comment, `/-/- -/`, a char literal and a raw string after the `!` operator and after `λ`, each followed by hidden code; a char literal or raw string straight after a token, refused as ambiguous; a literal or comment opener after a non-space (a token ending in a prime, an opener inside a token, an identifier character outside `\\w`), refused as adjacent; a fifth library and a widened glob in a lakefile; a quote inside an interpolation in the audit, after an argument too, as unbalanced-brace strings, each refused; a char literal holding a newline, an identifier of char-literal shape and a lone carriage return, each refused; four instance declarations of notation and default classes and five instance, default_instance or coe attributes refused, and the same names in lists split over lines, an instance attribute added later, the bare coe and default_instance tokens, an instance after open-in and a derived instance for a type another file declares; the coercion counterexample from review in the held-encoder module refused; a derived instance of a type the file declares accepted; an allow-listed instance changed on its first line, a copy with another class or exact in another namespace, a second copy, moved to another namespace, a changed class on a continuation line and a changed default value refused, one moved down a line accepted, and one that is no longer an instance refused as a missing entry)'
