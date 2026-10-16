#!/usr/bin/env bash
# Generate the complete Session unit's copies of the four ratchet T1/T3 files,
# the composed Triple T1 file and the wire decoder's T1/T3 files.
#
# The source files are themselves deterministic copies made by
# port-unit-proofs.sh.  That gate is run first, so this second port remains a
# checked composition of the leaf proof and two explicit namespace rewrites,
# plus the named `unit_edit`s below.  Those restate two contract fields at the
# instances this unit uses, where the sources quantify over every `Zeroize`
# record: `SessionUnitSpqrT1.ZeroizeTotal` at `Array::zeroize` on 32-byte
# arrays with the blanket `u8` instance, and the `Vec::zeroize` conjunct of
# `SessionUnitSpqrT1.VecRetainTotal` at the chain table, the sparse skipped-key
# store and the classical skipped-key store; and they apply the restated fields
# where the proofs used the general ones.  Each edit names the text it changes
# and fails if the source no longer has exactly that text.  No other theorem
# statement or proof body is edited.  The three-leaf files keep their
# statements.
set -euo pipefail

cd "$(dirname "$0")/../.."

check=0
if [ "${1:-}" = "--check" ]; then
  check=1
elif [ $# -ne 0 ]; then
  echo "usage: port-session-unit-proofs.sh [--check]" >&2
  exit 1
fi

bash tacenta-proofs/scripts/port-unit-proofs.sh --check >/dev/null

src=tacenta-proofs/translation/Translation
out="$src"
tmp=""
cleanup() { [ -n "$tmp" ] && rm -rf "$tmp"; return 0; }
trap cleanup EXIT INT TERM
if [ "$check" -eq 1 ]; then
  tmp=$(mktemp -d)
  out="$tmp"
fi

python3 - "$src" "$out" <<'PY'
from pathlib import Path
import sys

src, out = map(Path, sys.argv[1:3])

jobs = [
    ("UnitT1.lean", "SessionUnitT1.lean", {
        "Tacenta.UnitT1": ("Tacenta.SessionUnitT1", 1),
    }),
    ("UnitSpqrT1.lean", "SessionUnitSpqrT1.lean", {
        "Translation.UnitT1": ("Translation.SessionUnitT1", 1),
        "Tacenta.UnitSpqrT1": ("Tacenta.SessionUnitSpqrT1", 2),
    }),
    ("UnitT3.lean", "SessionUnitT3.lean", {
        "Translation.UnitT1": ("Translation.SessionUnitT1", 1),
        "Tacenta.UnitT1": ("Tacenta.SessionUnitT1", 72),
        "Tacenta.UnitT3": ("Tacenta.SessionUnitT3", 2),
    }),
    ("UnitSpqrT3.lean", "SessionUnitSpqrT3.lean", {
        "Translation.UnitSpqrT1": ("Translation.SessionUnitSpqrT1", 1),
        "Tacenta.UnitT1": ("Tacenta.SessionUnitT1", 1),
        "Tacenta.UnitSpqrT1": ("Tacenta.SessionUnitSpqrT1", 48),
        "Tacenta.UnitSpqrT3": ("Tacenta.SessionUnitSpqrT3", 2),
        "port-unit-proofs.sh": ("port-session-unit-proofs.sh", 1),
    }),
]

# The general `ZeroizeTotal` and `Vec::zeroize` conjunct of the sources say the two operations
# return for every `Zeroize` record, including one whose `zeroize` fails.  The real functions call
# the record's `zeroize` on each element and propagate its failure, so in this unit the fields are
# stated at the instances the translation passes (`UnitSatisfiabilityZeroizeScope.lean`).
BLANKET_U8 = "(zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) "
PAIR_CHAINS = ("(Pair.Insts.ZeroizeZeroize (zeroize.Zeroize.Blanket U64.Insts.ZeroizeDefaultIsZeroes)\n"
               "      Chains.Insts.ZeroizeZeroize)")
UNIT_EDITS = {
    "SessionUnitSpqrT1.lean": [
        ("ZeroizeTotal at the unit's instance",
         """under secret deletion. -/
def ZeroizeTotal : Prop :=
  ∀ {Z : Type} {N : Usize} (inst : zeroize.Zeroize Z) (a : Array Z N),
    ∃ r, Array.Insts.ZeroizeZeroize.zeroize inst a = ok r
""",
         """under secret deletion.

In this unit the statement is made at the one instance and width the translation passes to
`Array::zeroize`: the blanket `Zeroize` for `u8`, on a 32-byte array.  The source of this file,
`UnitSpqrT1.lean`, states it for every element type, width and `Zeroize` record, including a record
whose `zeroize` fails; the real function propagates that failure, so the general form is stronger
than the crate supports (`UnitSatisfiabilityZeroizeScope.zeroize_failure_propagation_conflicts`). -/
def ZeroizeTotal : Prop :=
  ∀ (a : Array U8 32#usize),
    ∃ r, Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a = ok r
""", 1),
        ("VecRetainTotal's Vec::zeroize conjunct at the unit's instances",
         """def VecRetainTotal : Prop :=
  (∀ {T : Type} (A : Type) (v : alloc.vec.Vec T),
    ∃ r, alloc.vec.Vec.capacity A v = ok r) ∧
  (∀ {T : Type} (inst : zeroize.Zeroize T) (v : alloc.vec.Vec T),
    ∃ r, alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst v = ok r) ∧
""",
         """/-- `Vec::capacity` returns, `Vec::zeroize` returns at the instances the unit passes to it, and the
three loop contracts above.  In this unit the second conjunct is stated at the three instances the
translation passes to `Vec::zeroize`: the chain table (`Vec<(u64, Chains)>`), the sparse ratchet's
skipped-key store (`Vec<Skipped>`) and the classical ratchet's (`Vec<SkippedKey>`), in that order.
The source of this file, `UnitSpqrT1.lean`, states it for every `Zeroize` record, including one
whose `zeroize` fails, which the real function does not support. -/
def VecRetainTotal : Prop :=
  (∀ {T : Type} (A : Type) (v : alloc.vec.Vec T),
    ∃ r, alloc.vec.Vec.capacity A v = ok r) ∧
  ((∀ v : alloc.vec.Vec (U64 × Chains),
      ∃ r, alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
        (Pair.Insts.ZeroizeZeroize (zeroize.Zeroize.Blanket U64.Insts.ZeroizeDefaultIsZeroes)
          Chains.Insts.ZeroizeZeroize) v = ok r) ∧
    (∀ v : alloc.vec.Vec Skipped,
      ∃ r, alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize Skipped.Insts.ZeroizeZeroize v = ok r) ∧
    (∀ v : alloc.vec.Vec tacenta_session_unit.tacenta_ratchet.SkippedKey,
      ∃ r, alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
        tacenta_session_unit.tacenta_ratchet.SkippedKey.Insts.ZeroizeZeroize v = ok r)) ∧
""", 1),
        ("ZeroizeTotal applied at its one instance", "hz " + BLANKET_U8, "hz ", 3),
        ("the chain-table conjunct", "hcap.2.1\n    " + PAIR_CHAINS + " st.chains",
         "hcap.2.1.1 st.chains", 1),
        ("the skipped-store conjunct", "hret.2.1 Skipped.Insts.ZeroizeZeroize st.skipped",
         "hret.2.1.2.1 st.skipped", 1),
    ],
    "SessionUnitSpqrT3.lean": [
        ("ZeroizeTotal applied at its one instance", "hz " + BLANKET_U8, "hz ", 4),
        ("the chain-table conjunct", "hcap.2.1\n    " + PAIR_CHAINS + " s.chains",
         "hcap.2.1.1 s.chains", 1),
        ("the skipped-store conjunct", "hret_total.2.1 Skipped.Insts.ZeroizeZeroize s.skipped",
         "hret_total.2.1.2.1 s.skipped", 1),
        ("the reused assumptions",
         "outright from `SpqrT1.lean` (`VecRetainTotal`, `ZeroizeTotal` and `OptionCloneTotal`).**",
         "outright from `SpqrT1.lean` (`VecRetainTotal`, `ZeroizeTotal` and `OptionCloneTotal`; in this "
         "unit `SessionUnitSpqrT1.lean` states the first two at the instances the unit uses).**", 1),
    ],
    "SessionUnitTripleT1.lean": [
        ("ZeroizeTotal applied at its one instance", "hz " + BLANKET_U8, "hz ", 4),
        ("the collapse of TripleT1's ZeroizeTotal",
         """its `ZeroizeTotal` is a narrowing of
  `SessionUnitSpqrT1.ZeroizeTotal` at one instance, which has to be written out at
  every use), and its two `@[step]` `zeroize.Zeroizing` helpers are duplicates
  of `SessionUnitT1`'s, so none of the five is redeclared. Two of the three collapses
  are exact and the third is not: the two constructor theorems below take
  `SessionUnitSpqrT1.ZeroizeTotal`, which quantifies over the element type, the width
  and the instance, where `TripleT1.ZeroizeTotal` fixed all three at
  `Array U8 32`. They assume strictly more than their twins did, which makes
  them strictly weaker theorems. The narrow form is what the two constructors
  need -- each wipes two 32-byte arrays and nothing else -- so the generality
  is a convenience of reusing the leaf's constant, not a requirement;
""",
         """its `ZeroizeTotal` is
  `SessionUnitSpqrT1.ZeroizeTotal`), and its two `@[step]` `zeroize.Zeroizing` helpers
  are duplicates of `SessionUnitT1`'s, so none of the five is redeclared. In this
  unit all three collapses are exact: `SessionUnitSpqrT1.ZeroizeTotal` is stated at
  `Array U8 32` and the blanket `u8` instance, as `TripleT1.ZeroizeTotal` was. The
  source of this file, `UnitTripleT1.lean`, takes the three-leaf unit's general
  form, which quantifies over the element type, the width and the instance;
""", 1),
        ("zeroize_step at the unit's instance",
         """/-- Wiping a byte buffer returns, as a stepping rule. Written out with the
instance argument because `SessionUnitSpqrT1.ZeroizeTotal` quantifies over it and the
stepping tactic has nothing to infer it from. -/
@[step]
theorem zeroize_step (hz : SessionUnitSpqrT1.ZeroizeTotal) {Z : Type} {N : Usize}
    (inst : zeroize.Zeroize Z) (a : Array Z N) :
    Array.Insts.ZeroizeZeroize.zeroize inst a ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := hz inst a; simp [hr]
""",
         """/-- Wiping a 32-byte buffer returns, as a stepping rule, at the one instance
`SessionUnitSpqrT1.ZeroizeTotal` is stated at in this unit: the blanket `u8` one. -/
@[step]
theorem zeroize_step (hz : SessionUnitSpqrT1.ZeroizeTotal) (a : Array U8 32#usize) :
    Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := hz a; simp [hr]
""", 1),
    ],
    "SessionUnitTripleT3.lean": [
        ("ZeroizeTotal applied at its one instance", "hzs _ a", "hzs a", 3),
        ("the boundary the bundles take",
         "`DerivedKeysModel`, `OptionCloneTotal` and the general `ZeroizeTotal`.",
         "`DerivedKeysModel`, `OptionCloneTotal` and `ZeroizeTotal` (in this unit\n"
         "`SessionUnitSpqrT1.ZeroizeTotal` is stated at the one instance the unit uses).", 1),
        ("the ZeroizeTotal collapse",
         """accepts one for all three. And the general `UnitSpqrT1.ZeroizeTotal` the sparse
ratchet needs gives this file's narrow `ZeroizeTotal` at its one instance.
""",
         """accepts one for all three. And the general `UnitSpqrT1.ZeroizeTotal` the sparse
ratchet needs gives this file's narrow `ZeroizeTotal` at its one instance. In this
unit `SessionUnitSpqrT1.ZeroizeTotal` is stated at that instance, so the two are
the same proposition.
""", 1),
    ],
}


def unit_edit(text, dest, label, old, new, expected):
    found = text.count(old)
    if found != expected:
        raise SystemExit(
            f"port-session-unit-proofs: {dest}: unit edit {label!r}: text occurs {found} "
            f"time(s), expected {expected}; inspect the source before changing this edit")
    return text.replace(old, new)


def apply_unit_edits(text, dest):
    for label, old, new, expected in UNIT_EDITS.get(dest, []):
        text = unit_edit(text, dest, label, old, new, expected)
    return text


def replace_exact(text, old, new, expected, origin):
    found = text.count(old)
    if found != expected:
        raise SystemExit(
            f"port-session-unit-proofs: {origin}: {old!r} occurs {found} "
            f"time(s), expected {expected}; inspect the source port before "
            "changing this count")
    return text.replace(old, new)

for origin, dest, substitutions in jobs:
    text = (src / origin).read_text()
    marker = "\n\nimport "
    if not text.startswith("-- Generated by tacenta-proofs/scripts/port-unit-proofs.sh"):
        raise SystemExit(f"port-session-unit-proofs: {origin} lost its generated header")
    split = text.find(marker)
    if split < 0:
        raise SystemExit(f"port-session-unit-proofs: {origin} has no import after its header")
    text = text[split + 2:]
    text = replace_exact(text, "Translation.TacentaTripleUnit",
                         "Translation.TacentaSessionUnit", 1, origin)
    text = replace_exact(text, "tacenta_triple_unit", "tacenta_session_unit", 2, origin)
    three_leaf = text.count("three-leaf translation unit")
    text = text.replace("three-leaf translation unit", "eight-leaf Session translation unit")
    for old, (new, expected) in substitutions.items():
        text = replace_exact(text, old, new, expected, origin)
    text = apply_unit_edits(text, dest)
    edits = UNIT_EDITS.get(dest, [])
    changes = ("-- changes only imports and the generated unit/proof namespaces.\n" if not edits else
               "-- changes imports and the generated unit/proof namespaces, and applies\n"
               f"-- {len(edits)} named unit edits that restate the general zeroize fields at\n"
               "-- the instances this unit uses (see the script).\n")
    note = (
        "-- Generated by tacenta-proofs/scripts/port-session-unit-proofs.sh from\n"
        f"-- Translation/{origin}. Do not edit: `port-session-unit-proofs.sh --check`\n"
        "-- regenerates this file and fails on any difference. The source is itself\n"
        "-- held byte-for-byte to its leaf proof by port-unit-proofs.sh. This port\n"
        + changes +
        f"-- Reworded {three_leaf} explanatory reference(s) to name this unit.\n\n"
    )
    (out / dest).write_text(note + text)
print(f"port-session-unit-proofs: {dest} (from {origin})")

# UnitTripleT1 is already a hand-written composition proof over the three-leaf
# unit.  The complete Session unit embeds those same three leaves, so its proof
# body is reusable after exact generated/proof namespace rewrites.  Unlike the
# four jobs above, this source is not itself generated by port-unit-proofs.sh.
origin = "UnitTripleT1.lean"
dest = "SessionUnitTripleT1.lean"
text = (src / origin).read_text()
for old, new, expected in [
    ("Translation.TacentaTripleUnit", "Translation.TacentaSessionUnit", 1),
    ("tacenta_triple_unit", "tacenta_session_unit", 3),
    ("UnitTripleT1", "SessionUnitTripleT1", 2),
    ("UnitSpqrT1", "SessionUnitSpqrT1", 45),
    ("UnitT1", "SessionUnitT1", 39),
    ("three-leaf translation unit", "eight-leaf Session translation unit", 1),
    ("Translation/TacentaTripleUnit.lean", "Translation/TacentaSessionUnit.lean", 1),
    ("tacenta-core/triple-unit", "tacenta-core/session-unit", 1),
]:
    text = replace_exact(text, old, new, expected, origin)
text = apply_unit_edits(text, dest)
note = (
    "-- Generated by tacenta-proofs/scripts/port-session-unit-proofs.sh from\n"
    f"-- Translation/{origin}. Do not edit: `port-session-unit-proofs.sh --check`\n"
    "-- regenerates this file and fails on any difference. This port changes\n"
    "-- the generated unit and proof namespaces, and applies\n"
    f"-- {len(UNIT_EDITS[dest])} named unit edits that restate the general zeroize fields at\n"
    "-- the instances this unit uses (see the script).\n\n"
)
(out / dest).write_text(note + text)
print(f"port-session-unit-proofs: {dest} (from {origin})")

# UnitTripleT3 is the hand-written composition of the classical and sparse
# refinement proofs over UnitTripleT1.  The Session unit embeds the same three
# leaves, so keep a count-checked namespace-only port beside its T1 twin.
origin = "UnitTripleT3.lean"
dest = "SessionUnitTripleT3.lean"
text = (src / origin).read_text()
for old, new, expected in [
    ("Translation.TacentaTripleUnit", "Translation.TacentaSessionUnit", 1),
    ("Translation.UnitTripleT1", "Translation.SessionUnitTripleT1", 1),
    ("Translation.UnitT3", "Translation.SessionUnitT3", 1),
    ("Translation.UnitSpqrT3", "Translation.SessionUnitSpqrT3", 1),
    ("tacenta_triple_unit", "tacenta_session_unit", 2),
    ("Tacenta.UnitTripleT3", "Tacenta.SessionUnitTripleT3", 3),
    ("Tacenta.UnitTripleT1", "Tacenta.SessionUnitTripleT1", 6),
    ("Tacenta.UnitT3", "Tacenta.SessionUnitT3", 43),
    ("Tacenta.UnitSpqrT3", "Tacenta.SessionUnitSpqrT3", 54),
    ("Tacenta.UnitT1", "Tacenta.SessionUnitT1", 11),
    ("Tacenta.UnitSpqrT1", "Tacenta.SessionUnitSpqrT1", 13),
    ("three-leaf translation unit", "eight-leaf Session translation unit", 1),
]:
    text = replace_exact(text, old, new, expected, origin)
text = apply_unit_edits(text, dest)
note = (
    "-- Generated by tacenta-proofs/scripts/port-session-unit-proofs.sh from\n"
    f"-- Translation/{origin}. Do not edit: `port-session-unit-proofs.sh --check`\n"
    "-- regenerates this file and fails on any difference. This port changes\n"
    "-- the generated unit and proof namespaces, and applies\n"
    f"-- {len(UNIT_EDITS[dest])} named unit edits that restate the general zeroize fields at\n"
    "-- the instances this unit uses (see the script).\n\n"
)
(out / dest).write_text(note + text)
print(f"port-session-unit-proofs: {dest} (from {origin})")

# WireT1 is a hand-written leaf proof rather than a generated three-leaf port.
# Its proof body is still reusable byte-for-byte because the Session unit
# embeds the same wire source.  Keep the three namespace rewrites exact.
origin = "WireT1.lean"
dest = "SessionUnitWireT1.lean"
text = (src / origin).read_text()
text = replace_exact(text, "Translation.TacentaWire",
                     "Translation.TacentaSessionUnit", 1, origin)
text = replace_exact(text, "Tacenta.WireT1",
                     "Tacenta.SessionUnitWireT1", 10, origin)
text = replace_exact(text, "open tacenta_wire",
                     "open tacenta_session_unit.tacenta_wire", 1, origin)
note = (
    "-- Generated by tacenta-proofs/scripts/port-session-unit-proofs.sh from\n"
    f"-- Translation/{origin}. Do not edit: `port-session-unit-proofs.sh --check`\n"
    "-- regenerates this file and fails on any difference. This port changes\n"
    "-- only the generated unit and proof namespaces.\n\n"
)
(out / dest).write_text(note + text)
print(f"port-session-unit-proofs: {dest} (from {origin})")

# WireT3 proves exact decoder behaviour over the same generated wire source.
# Port it with the T1 dependency so lifecycle receive can reuse the canonical
# decoder relation without hand-copying any proof.
origin = "WireT3.lean"
dest = "SessionUnitWireT3.lean"
text = (src / origin).read_text()
for old, new, expected in [
    ("Translation.TacentaWire", "Translation.TacentaSessionUnit", 1),
    ("Translation.WireT1", "Translation.SessionUnitWireT1", 1),
    ("Tacenta.WireT3", "Tacenta.SessionUnitWireT3", 6),
    ("Tacenta.WireT1", "Tacenta.SessionUnitWireT1", 7),
    ("open tacenta_wire", "open tacenta_session_unit.tacenta_wire", 1),
]:
    text = replace_exact(text, old, new, expected, origin)
note = (
    "-- Generated by tacenta-proofs/scripts/port-session-unit-proofs.sh from\n"
    f"-- Translation/{origin}. Do not edit: `port-session-unit-proofs.sh --check`\n"
    "-- regenerates this file and fails on any difference. This port changes\n"
    "-- only imports and the generated unit/proof namespaces.\n\n"
)
(out / dest).write_text(note + text)
print(f"port-session-unit-proofs: {dest} (from {origin})")

# WireInitialT3 reuses WireT3's arithmetic and canonical-key lemmas to prove
# exact successful initial-message decoding.  The Session unit embeds the same
# wire source, so this is another namespace-only, count-checked port.
origin = "WireInitialT3.lean"
dest = "SessionUnitWireInitialT3.lean"
text = (src / origin).read_text()
for old, new, expected in [
    ("Translation.WireT3", "Translation.SessionUnitWireT3", 1),
    ("Tacenta.WireInitialT3", "Tacenta.SessionUnitWireInitialT3", 4),
    ("Tacenta.WireT3", "Tacenta.SessionUnitWireT3", 3),
    ("Tacenta.WireT1", "Tacenta.SessionUnitWireT1", 4),
    ("tacenta_wire", "tacenta_session_unit.tacenta_wire", 2),
]:
    text = replace_exact(text, old, new, expected, origin)
note = (
    "-- Generated by tacenta-proofs/scripts/port-session-unit-proofs.sh from\n"
    f"-- Translation/{origin}. Do not edit: `port-session-unit-proofs.sh --check`\n"
    "-- regenerates this file and fails on any difference. This port changes\n"
    "-- only imports and the generated unit/proof namespaces.\n\n"
)
(out / dest).write_text(note + text)
print(f"port-session-unit-proofs: {dest} (from {origin})")
PY

files=(SessionUnitT1.lean SessionUnitSpqrT1.lean SessionUnitT3.lean SessionUnitSpqrT3.lean SessionUnitTripleT1.lean SessionUnitTripleT3.lean SessionUnitWireT1.lean SessionUnitWireT3.lean SessionUnitWireInitialT3.lean)
if [ "$check" -eq 0 ]; then
  echo "port-session-unit-proofs: wrote the Session unit ratchet proof copies"
  exit 0
fi

fail=0
for file in "${files[@]}"; do
  if ! diff -u "$src/$file" "$tmp/$file" >/dev/null; then
    fail=1
    diff -u "$src/$file" "$tmp/$file" | head -40 >&2 || true
  fi
done
if [ "$fail" -ne 0 ]; then
  echo "port-session-unit-proofs: committed copies differ; regenerate and rebuild" >&2
  exit 1
fi
echo "port-session-unit-proofs: the committed copies are deterministic"
