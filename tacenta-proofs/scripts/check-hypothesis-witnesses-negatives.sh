#!/usr/bin/env bash
# Hold check-hypothesis-witnesses.sh to mutations.
#
# Each case below applies changes to a disposable copy of the translation package, rebuilds what
# they touch, and requires the gate to refuse with the stated messages. The unmodified copy is
# checked first and must be accepted: a refusal is only evidence if acceptance is possible. A copy
# that fails to build, or a gate that fails because the environment could not be loaded (exit 2),
# is not a refusal and is reported as a failure of this script.
#
# The cases:
#   unmodified          the copy as it is: accepted.
#   dead-hypotheses     six dead hypotheses added to claimed theorems of `ErasureCodecT1.lean`, one
#                       rebuild. The proofs still close, the module builds, and every other gate
#                       accepted these forms:
#                         - `∀ n : Nat, n < n`, which names no predicate (on `encoder_to_bytes_no_panic`);
#                         - `(n : Nat) (hn : n < 0)`, a variable only a hypothesis mentions (on
#                           `decoder_to_bytes_no_panic`);
#                         - a false predicate `DeadSelf` bridged to itself, with a refutation that
#                           names it, taken by `encoder_from_bytes_no_panic`;
#                         - a predicate `RefutP` bridged to a shape that no function satisfies, whose
#                           only theorem about the shape is a refutation;
#                         - two predicates `AliasP` and `AliasQ` bridged to each other, each the shape
#                           applied to a defined function;
#                         - a predicate `AliasR` bridged to the shape applied to an alias of a defined
#                           function.
#   witness-deleted     the bridge `SpqrT1_OptionCloneTotal_is` deleted from `Satisfiability.lean`.
#                       Everything still builds; the hypothesis it connected is connected to nothing.
#   law-bridge-deleted  the bridge `LawPop_is` and its pins deleted from `SatisfiabilitySpqrLaws.lean`.
#                       The derivations of the defined-function hypotheses all take `LawPop`, so none
#                       of them is connected any more, and the void bridges that remain do not count.
#   existence-deleted   the existence theorem `pop_satisfiable` and its pins deleted. `LawPop_is` is
#                       still a bridge, with nothing showing its shape is satisfiable.
#   derivation-dead-hypothesis
#                       `vecRetainAgreesOfLaws`, the derivation of `SpqrT3.VecRetainAgrees`, given a
#                       hypothesis `(n : Nat) (hn : n < 0)`; its statement pin removed, as an author
#                       who updates the pin would. Build, attest and the pin accept it.
#   ledger-derivation-removed
#                       the ledger entries (`manifests/verification-manifest.json`) of the derivations
#                       of `SpqrT1.RemoveSkippedAtTotal` removed. Its only remaining bridge is the void
#                       one. No rebuild: the gate reads the ledger as data.
#   heading-reworded    the heading of the sparse T3 section in the ledger loses the words the gate
#                       selects theorems by, so twelve claimed theorems drop out. No rebuild.
#
# The copy is a layout the package needs: `tacenta-proofs/translation` with its sources and a copy of
# `.lake/build`, a symbolic link to the original `.lake/packages` (read, never written), the
# manifests, and `tacenta-model` with its build. About 750 MB; the five cases that rebuild take about
# fifteen minutes on an idle machine, and about forty under load. `HYPWIT_WORK` names the directory the
# copy is made in (default `$TMPDIR`). Needs the translation package built. No workflow runs this
# script.
set -euo pipefail

src="$(cd "$(dirname "$0")/.." && pwd)"
repo="$(cd "$src/.." && pwd)"
work="$(mktemp -d "${HYPWIT_WORK:-${TMPDIR:-/tmp}}/hypwit-negatives.XXXXXX")"
trap 'rm -rf "$work"' EXIT INT TERM
cases=0
wrong=0

pkg="$work/tacenta-proofs"
trans="$pkg/translation"

reset_copy() {
  rm -rf "$work/tacenta-proofs" "$work/tacenta-model"
  mkdir -p "$trans/.lake"
  (cd "$src/translation" && for f in $(ls -A | grep -v '^\.lake$'); do cp -R "$f" "$trans/"; done)
  cp -R "$src/translation/.lake/build" "$trans/.lake/build"
  ln -s "$src/translation/.lake/packages" "$trans/.lake/packages"
  cp -R "$src/manifests" "$pkg/manifests"
  mkdir -p "$work/tacenta-model"
  (cd "$repo/tacenta-model" && for f in $(ls -A); do cp -R "$f" "$work/tacenta-model/"; done)
}

rebuild() {
  (cd "$trans" && lake build Translation.AxiomAudit Translation.AxiomAuditTripleUnit >"$work/build.log" 2>&1) || {
    echo "WRONG  $1: the mutated copy did not build:" >&2
    tail -20 "$work/build.log" >&2
    wrong=$((wrong + 1))
    return 1
  }
}

run_gate() {
  set +e
  out="$(HYPWIT_ROOT="$pkg" bash "$src/scripts/check-hypothesis-witnesses.sh" 2>&1)"
  rc=$?
  set -e
}

expect_pass() {
  cases=$((cases + 1))
  run_gate
  if [ "$rc" -ne 0 ]; then
    echo "WRONG  $1: expected acceptance, was refused:" >&2
    printf '%s\n' "$out" >&2
    wrong=$((wrong + 1))
  fi
}

# expect_fail <name> <message>...: refused (exit 1), and the output holds every message
expect_fail() {
  local name="$1"
  shift
  cases=$((cases + 1))
  run_gate
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $name: expected refusal, was accepted" >&2
    wrong=$((wrong + 1))
    return 0
  fi
  if [ "$rc" -ne 1 ]; then
    echo "WRONG  $name: the gate did not run (exit $rc):" >&2
    printf '%s\n' "$out" >&2
    wrong=$((wrong + 1))
    return 0
  fi
  local m
  for m in "$@"; do
    if [[ "$out" != *"$m"* ]]; then
      echo "WRONG  $name: refused, but not for '$m':" >&2
      printf '%s\n' "$out" >&2
      wrong=$((wrong + 1))
      return 0
    fi
  done
}

replace_in() { # <file under Translation/> <old> <new>, once or stop
  python3 - "$trans/Translation/$1" "$2" "$3" <<'PY'
import pathlib, sys
path, old, new = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3]
text = path.read_text()
assert text.count(old) == 1, (path, old, text.count(old))
path.write_text(text.replace(old, new))
PY
}

delete_theorem() { # <file> <theorem name> [pins]: the theorem (up to the next blank line), and its pin blocks if `pins`
  python3 - "$trans/Translation/$1" "$2" "${3:-}" <<'PY'
import pathlib, re, sys
path, name, with_pins = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3] == "pins"
text = path.read_text()
decl = re.compile(r"(?:/--(?:(?!-/).)*-/\n)?theorem " + re.escape(name) + r"\b.*?\n\n", re.S)
text, n = decl.subn("", text, count=1)
assert n == 1, (name, n)
if with_pins:
    pins = re.compile(r"/--\s*\ninfo: [^\n]*" + re.escape(name) + r"\b.*?-/\n#guard_msgs in\n#(?:print axioms|check) [^\n]*\." + re.escape(name) + r"\n\n?", re.S)
    text, k = pins.subn("", text)
    assert k >= 1, (name, "no pin block removed")
path.write_text(text)
PY
}

# ---------------------------------------------------------------------------
reset_copy
expect_pass "unmodified"

reset_copy
python3 - "$trans/Translation/ErasureCodecT1.lean" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
t = path.read_text()
def sub(old, new):
    global t
    assert t.count(old) == 1, (old, t.count(old))
    t = t.replace(old, new)
decls = '''def AddShape (f : Std.U16 → Std.U16 → Result Std.U16) : Prop := ∀ a b, ∃ r, f a b = ok r
def DeadSelf : Prop := ∀ n : Nat, n < 0
theorem DeadSelf_refl : DeadSelf ↔ DeadSelf := Iff.rfl
theorem DeadSelf_refuted : ¬ ∃ n : Nat, DeadSelf := fun ⟨_, h⟩ => Nat.not_lt_zero 0 (h 0)
def DeadShape (f : Nat → Nat) : Prop := ∀ n, f n < 0
def RefutP : Prop := DeadShape id
theorem RefutP_is : RefutP ↔ DeadShape id := Iff.rfl
theorem DeadShape_unsat : ¬ ∃ f : Nat → Nat, DeadShape f := fun ⟨_, h⟩ => Nat.not_lt_zero _ (h 0)
def AliasP : Prop := AddShape tacenta_erasure.gf.add
def AliasQ : Prop := AddShape tacenta_erasure.gf.add
theorem AliasP_is : AliasP ↔ AliasQ := Iff.rfl
theorem AliasQ_is : AliasQ ↔ AliasP := Iff.rfl
theorem AddShape_exists : ∃ f, AddShape f := ⟨fun a _ => ok a, fun _ _ => ⟨_, rfl⟩⟩
def AddFn : Std.U16 → Std.U16 → Result Std.U16 := tacenta_erasure.gf.add
def AliasR : Prop := AddShape tacenta_erasure.gf.add
theorem AliasR_is : AliasR ↔ AddShape AddFn := Iff.rfl

'''
sub("theorem encoder_from_bytes_no_panic (bytes : Slice U8)",
    decls + "theorem encoder_from_bytes_no_panic (hd1 : DeadSelf) (hd2 : RefutP) (hd3 : AliasP) (hd4 : AliasR)\n    (bytes : Slice U8)")
sub("theorem encoder_to_bytes_no_panic (e : Encoder)", "theorem encoder_to_bytes_no_panic (hdead : ∀ n : Nat, n < n) (e : Encoder)")
sub("theorem decoder_to_bytes_no_panic (d : Decoder)", "theorem decoder_to_bytes_no_panic (n : Nat) (hn : n < 0) (d : Decoder)")
path.write_text(t)
PY
rebuild "dead-hypotheses" && expect_fail "dead-hypotheses" \
  "names no predicate and so has no witness" \
  "quantifies over \`n\`, which only hypotheses mention" \
  "\`Tacenta.ErasureCodecT1.DeadSelf\`" \
  "\`Tacenta.ErasureCodecT1.RefutP\`" \
  "\`Tacenta.ErasureCodecT1.AliasP\`" \
  "\`Tacenta.ErasureCodecT1.AliasR\`"

reset_copy
delete_theorem Satisfiability.lean SpqrT1_OptionCloneTotal_is
rebuild "witness-deleted" && expect_fail "witness-deleted" "\`Tacenta.SpqrT1.OptionCloneTotal\`"

reset_copy
delete_theorem SatisfiabilitySpqrLaws.lean LawPop_is pins
rebuild "law-bridge-deleted" && expect_fail "law-bridge-deleted" "\`Tacenta.SpqrT1.RemoveSkippedAtTotal\`"

reset_copy
delete_theorem SatisfiabilitySpqrLaws.lean pop_satisfiable pins
rebuild "existence-deleted" && expect_fail "existence-deleted" "\`Tacenta.SpqrT3.VecRetainAgrees\`"

reset_copy
python3 - "$trans/Translation/SatisfiabilitySpqrLaws.lean" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
t = path.read_text()
def sub(old, new):
    global t
    assert t.count(old) == 1, (old, t.count(old))
    t = t.replace(old, new)
sub("""theorem vecRetainAgreesOfLaws (hCap : LawCapacity) (hVZ : LawVecZeroize)
    (hZ : Tacenta.SpqrT1.ZeroizeTotal) (hA : LawAsMut) (hP : LawPop) :
    Tacenta.SpqrT3.VecRetainAgrees :=
  ⟨setChainsAgrees (vecRetainTotal hCap hVZ hZ hA hP) hZ hA hP,
   clearOldEpochsAgrees hZ hA hP⟩
""", """theorem vecRetainAgreesOfLawsCore (hCap : LawCapacity) (hVZ : LawVecZeroize)
    (hZ : Tacenta.SpqrT1.ZeroizeTotal) (hA : LawAsMut) (hP : LawPop) :
    Tacenta.SpqrT3.VecRetainAgrees :=
  ⟨setChainsAgrees (vecRetainTotal hCap hVZ hZ hA hP) hZ hA hP,
   clearOldEpochsAgrees hZ hA hP⟩

theorem vecRetainAgreesOfLaws (hCap : LawCapacity) (hVZ : LawVecZeroize)
    (hZ : Tacenta.SpqrT1.ZeroizeTotal) (hA : LawAsMut) (hP : LawPop) (n : Nat) (hn : n < 0) :
    Tacenta.SpqrT3.VecRetainAgrees :=
  vecRetainAgreesOfLawsCore hCap hVZ hZ hA hP
""")
sub("  vecRetainAgreesOfLaws L.capacity L.vecZeroize L.arrayZeroize L.asMut L.pop",
    "  vecRetainAgreesOfLawsCore L.capacity L.vecZeroize L.arrayZeroize L.asMut L.pop")
pin = re.compile(r"/--\s*\ninfo: Tacenta\.SatisfiabilitySpqrLaws\.vecRetainAgreesOfLaws \(.*?-/\n#guard_msgs in\n#check Tacenta\.SatisfiabilitySpqrLaws\.vecRetainAgreesOfLaws\n\n?", re.S)
t, k = pin.subn("", t)
assert k == 1, k
path.write_text(t)
PY
rebuild "derivation-dead-hypothesis" && expect_fail "derivation-dead-hypothesis" "\`Tacenta.SpqrT3.VecRetainAgrees\`"

reset_copy
python3 - "$pkg/manifests/verification-manifest.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
drop = {"Tacenta.SatisfiabilitySpqrLaws.spqrRemoveSkippedAtTotal",
        "Tacenta.SatisfiabilitySpqrLaws.defined_hyps_from_axiom_hyps",
        "Tacenta.SatisfiabilitySpqrLaws.defined_fields_hold"}
before = len(data["claims"])
data["claims"] = [c for c in data["claims"] if (c.get("resolved") or c["theorem"]) not in drop]
assert before - len(data["claims"]) == len(drop), before - len(data["claims"])
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "ledger-derivation-removed" "has only a void bridge"

reset_copy
python3 - "$pkg/manifests/verification-manifest.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
n = 0
for c in data["claims"]:
    if "tier T3, the sparse post-quantum ratchet's translated code refines the model" in c["section"]:
        c["section"] = c["section"].replace("tier T3, ", "")
        n += 1
assert n > 0, n
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "heading-reworded" "fewer than the 109 this gate requires"

if [ "$wrong" -ne 0 ]; then
  echo "check-hypothesis-witnesses-negatives: $wrong of $cases cases gave the wrong result" >&2
  exit 1
fi
echo "check-hypothesis-witnesses-negatives: all $cases cases gave the expected result"
