#!/usr/bin/env bash
# Generate the three-leaf unit's copies of the leaf panic-freedom and
# refinement proofs.
#
# `Translation/T1.lean` proves the Double Ratchet panic-free and
# `Translation/SpqrT1.lean` the sparse ratchet; `Translation/T3.lean` and
# `Translation/SpqrT3.lean` prove the two refine their models. All four are
# about the constants in `Translation/TacentaRatchet.lean` and
# `Translation/TacentaSpqr.lean` -- the translations of those crates on their
# own. The three-leaf unit (`Translation/TacentaTripleUnit.lean`, assembled by
# `assemble-triple-unit.sh`) translates the same Rust as one crate, so it
# declares different constants with the same shape, one namespace deeper. A
# theorem about `tacenta_ratchet.State.send` says nothing about
# `tacenta_triple_unit.tacenta_ratchet.State.send`; Lean has no reason to
# connect them, and there is no import that would let one stand for the other.
# The proofs have to exist twice.
#
# That is a duplication we cannot remove, so this script makes it one that
# cannot drift instead. The copies are derived, not maintained: every
# difference between a leaf proof and its unit copy is one of the rewrites
# below, and `--check` regenerates and diffs so that an edit to either side
# fails CI.
#
# ## What the rewrites are
#
# Fewer than the duplication suggests. The leaf proofs rarely write a
# translated name in qualified form -- they `open` the crate's namespace and
# use short names -- so pointing them at the unit is:
#
#   1. the imports: the leaf translation becomes the unit's, and an imported
#      leaf proof file becomes its unit copy;
#   2. the namespace: `Tacenta.T1` becomes `Tacenta.UnitT1`, and likewise for
#      the other three, so leaf and copy can be built in one package without
#      colliding;
#   3. the `open`: the crate namespace becomes the unit's outer namespace plus
#      the crate namespace inside it. The outer one is needed on its own too,
#      for the trusted key-derivation names, which sit beside the leaves rather
#      than inside either;
#   4. qualified references to the four leaf proof namespaces
#      (`Tacenta.T1.` and so on) become references to the unit's copies. These
#      do reach statements and proof bodies -- 45 in `T3.lean`, 24 in
#      `SpqrT3.lean`: a hypothesis's type, a lemma a body cites, the rules an
#      `attribute [-step]` removes. The others fall inside pins and go with them;
#   5. in `SpqrT3.lean` only, one inserted stepping-rule erasure, explained
#      where the job below inserts it, and again in the copy.
#
# Every rewrite asserts how many times it matches, zero included, so a
# reference added to, removed from or respelled in a leaf fails here rather
# than being carried or missed quietly. Beyond these rewrites a statement or a
# proof body is copied as written. That is the point: if a body needed
# changing, the two translations would not be of the same Rust, and the whole
# exercise would be unsound.
#
# ## What is deliberately not copied
#
# The `#print axioms` pins. Their expected text names the leaves' constants,
# and the wrapping of a pinned axiom list is Lean's pretty-printer's business,
# not something to reproduce with a substitution. The unit's pins are written
# by hand in `Translation/UnitPins.lean`, which is where the claim that the
# port preserved each theorem's trust base is made and checked. How many pins
# each leaf file carries is asserted here, so that adding one to a leaf and not
# to the unit fails rather than passing quietly.
#
# A pin is recognised only in the shape the leaf files write it: a docstring
# beginning `info:` that ends at its own first `-/`, then `#guard_msgs in` and
# `#print axioms <name>` on lines of their own, all starting at the start of a
# line, followed by a blank line or the end of the file, and with nothing
# before it ending in `in` (a `set_option ... in` above a pin would be left
# applying to whatever came next). Anything else that mentions either command
# is refused rather than guessed at: once the pins are gone, every remaining
# line that mentions `#guard_msgs` or `#print axioms` must be one of the prose
# lines listed for its file, exactly as many times as listed.
#
# An earlier version matched pins loosely. A `#guard_msgs` test that was not a
# pin could lead it to delete everything up to the next pin while still
# counting one pin, and a pin written on one line was copied rather than
# stripped. The self-test below feeds the stripper those shapes and the others
# found alongside them, and fails if any is accepted. It runs before every
# generation, so the refusing side is exercised on every run and not only the
# accepting one.
#
# ## Usage
#
#   port-unit-proofs.sh            regenerate the copies
#   port-unit-proofs.sh --check    regenerate into a temporary directory and
#                                  diff; exit non-zero on any difference
#
# ## That `--check` can fail
#
# Checked rather than assumed, three ways: a hand edit appended to a generated
# copy, an edit appended to a leaf proof with the copy left alone, and a
# rewrite target moved in a leaf so that its pattern matches nothing. All three
# exit non-zero, the third naming the rewrite and telling the reader to update
# the rule rather than the count. Last redone on 2026-09-10, after the pin
# matching was tightened; redo it after changing the script.
#
# Run from any directory. Needs no toolchain.
set -euo pipefail

cd "$(dirname "$0")/../.."

check=0
if [ "${1:-}" = "--check" ]; then
  check=1
elif [ $# -ne 0 ]; then
  echo "port-unit-proofs: unknown argument: $1" >&2
  echo "usage: port-unit-proofs.sh [--check]" >&2
  exit 1
fi

src=tacenta-proofs/translation/Translation
out="$src"
tmp=""
cleanup() { [ -n "$tmp" ] && rm -rf "$tmp"; return 0; }
trap cleanup EXIT INT TERM
if [ "$check" -eq 1 ]; then
  tmp=$(mktemp -d)
  out="$tmp"
fi

python3 - "$src" "$out" <<'PYEOF'
import sys, os, re

src, out = sys.argv[1:3]


class PortError(Exception):
    pass


NOTE = """\
-- Generated by tacenta-proofs/scripts/port-unit-proofs.sh from
-- Translation/{origin}. Do not edit: `port-unit-proofs.sh --check`
-- regenerates this file and fails on any difference.
--
-- This is {origin} restated about the three-leaf translation unit, whose
-- constants are different constants from the ones {origin} is about. What
-- differs is the imports, the namespace, the `open`, qualified references to
-- the leaf proofs' own namespaces, and any stepping-rule erasure this script
-- inserts and explains beside it. No other text in a statement or a proof body
-- changes.
-- {pins}

"""


def rewrite(text, subs, origin):
    """Apply each (pattern, replacement, expected count). A rewrite that
    matches a different number of times than expected is a failure, not
    something to paper over: it means the leaf proof moved in a way this
    script does not understand, and the copy would silently stop being the
    same theorem."""
    for pattern, repl, expected in subs:
        text, n = re.subn(pattern, repl, text, flags=re.M)
        if n != expected:
            raise PortError(
                f"in {origin}, the rewrite {pattern!r} matched {n} time(s), "
                f"expected {expected}. The leaf proof has changed in a way "
                f"this script does not understand; read it and update the "
                f"rewrite rather than the count.")
    return text


def renames(t1, spqr_t1, t3, spqr_t3):
    """Qualified references to the four leaf proof namespaces, with how many
    of each the file holds. None of the four patterns matches inside another,
    nor inside `Tacenta.TripleT1.` or `Tacenta.TripleT3.`."""
    return [
        (r"(?<![\w.])Tacenta\.T1\.", "Tacenta.UnitT1.", t1),
        (r"(?<![\w.])Tacenta\.SpqrT1\.", "Tacenta.UnitSpqrT1.", spqr_t1),
        (r"(?<![\w.])Tacenta\.T3\.", "Tacenta.UnitT3.", t3),
        (r"(?<![\w.])Tacenta\.SpqrT3\.", "Tacenta.UnitSpqrT3.", spqr_t3),
    ]


# A pin, in exactly the shape the leaf files write. The docstring cannot run
# past its own first `-/`, which is what stops a match from starting at some
# other `info:` docstring and swallowing everything up to a real pin.
PIN = re.compile(
    r"^/--[ \t]*\n?info:(?:(?!-/)[\s\S])*-/\n"
    r"#guard_msgs in\n"
    r"#print axioms \S+\n"
    r"(?=\n|\Z)",
    re.M)


def ends_in_in(before):
    """Whether the last code before a pin is the keyword `in`, skipping blank
    space, line comments and (nested) block comments. Not a Lean parser: it
    reads the shapes that put a command in front of a pin, and the self-test
    holds it to them."""
    t = before
    while True:
        t = t.rstrip()
        if t.endswith("-/"):
            depth, i = 0, len(t)
            while i >= 2:
                pair = t[i - 2:i]
                if pair == "-/":
                    depth += 1
                    i -= 2
                elif pair == "/-":
                    depth -= 1
                    i -= 2
                    if depth == 0:
                        break
                else:
                    i -= 1
            if depth != 0:
                raise PortError("a block comment before a pin does not close "
                                "where this script expects")
            t = t[:i]
            continue
        nl = t.rfind("\n")
        line = t[nl + 1:]
        k = line.find("--")
        if k != -1:
            t = t[:nl + 1] + line[:k]
            continue
        return re.search(r"(?<![\w.'])in\Z", t) is not None


def strip_pins(text, origin, expected, prose):
    """Remove the `#print axioms` pins. They are re-stated by hand in
    UnitPins.lean, against the unit's own names.

    `expected` is how many this file carries. `T1.lean` and `T3.lean` pin
    three headline theorems each; `SpqrT1.lean` and `SpqrT3.lean` pin none of
    their own. Either number changing is a change to what the repository
    treats as load-bearing, so it fails here and the author decides where the
    unit's version of the new pin belongs.

    `prose` maps each line that may still mention `#guard_msgs` or
    `#print axioms` once the pins are gone to how many times it occurs."""
    if "\r" in text:
        raise PortError(f"{origin} contains a carriage return. The pin "
                        f"patterns read lines ending in a newline only, so a "
                        f"pin separated otherwise would not be recognised.")
    if "\x00" in text:
        raise PortError(f"{origin} contains a NUL byte, which this script "
                        f"uses internally.")
    pins = list(PIN.finditer(text))
    for m in pins:
        if ends_in_in(text[:m.start()]):
            line = text.count("\n", 0, m.start()) + 1
            raise PortError(
                f"{origin}:{line}: the pin here follows a command ending in "
                f"`in`, which applies to the pin; removing the pin would leave "
                f"it applying to whatever comes next. Move the pin clear of it.")
    if len(pins) != expected:
        raise PortError(
            f"{origin} carries {len(pins)} `#print axioms` pin(s) in the "
            f"recognised shape, expected {expected}. A pin added or removed "
            f"changes what is claimed; UnitPins.lean has to be updated to "
            f"match, and then this count.")
    text = PIN.sub("\x00", text)
    # Removing a pin leaves the blank lines around it; collapse only the runs
    # that span a removal, to at most one blank line, and leave every other
    # run of newlines in the file as the leaf wrote it.
    text = re.sub(r"\n*(?:\x00\n*)+",
                  lambda m: "\n" * min(m.group(0).count("\n"), 2), text)
    found = {}
    for line in text.split("\n"):
        if "#guard_msgs" in line or "#print axioms" in line:
            found[line] = found.get(line, 0) + 1
    if found != prose:
        unexpected = sorted(l for l in found if found[l] != prose.get(l, 0))
        missing = sorted(l for l in prose if l not in found)
        raise PortError(
            f"{origin}: once the pins were removed, the lines mentioning "
            f"`#guard_msgs` or `#print axioms` are not the prose lines this "
            f"script expects. Not expected, or not as many times: "
            f"{unexpected!r}. Expected and absent: {missing!r}. A pin in a "
            f"shape other than the recognised one, or a `#guard_msgs` test "
            f"that is not a pin, is refused rather than guessed at.")
    return text


def self_test():
    """Hold the stripper to the shapes it must accept and the ones it must
    refuse, before it touches a real file. A refusal must name the check meant
    for it, so a case refused for some other reason is caught rather than
    counted."""
    pin = ("/-- info: 'X.a' depends on axioms: [propext] -/\n"
           "#guard_msgs in\n#print axioms X.a\n")
    long_pin = ("/--\ninfo: 'X.b' depends on axioms: [propext,\n Quot.sound]\n"
                "-/\n#guard_msgs in\n#print axioms X.b\n")
    body = "theorem keep : True := trivial\n"
    prose = "/-- Check it with `#print axioms` by hand. -/"
    accept = [
        ("a pin after a line comment",
         f"-- why\n{pin}\n{body}", 1, {}, f"-- why\n\n{body}"),
        ("two pins after a module docstring, then `end`",
         f"/-! doc -/\n\n{pin}\n{long_pin}\nend X\n", 2, {},
         "/-! doc -/\n\nend X\n"),
        ("listed prose that names the command",
         f"{prose}\n{body}\n{pin}", 1, {prose: 1}, f"{prose}\n{body}\n"),
        ("runs of blank lines away from a pin are kept",
         f"{body}\n\n\n{body}\n{pin}", 1, {}, f"{body}\n\n\n{body}\n"),
        # The loose pattern this replaced started at the first `info:` docstring
        # and ran on to the pin, taking the declarations in between with it.
        ("an ordinary `info:` docstring ahead of a pin keeps what follows it",
         f"/--\ninfo: not a pin\n-/\n{body}\n{body}\n{pin}", 1, {},
         f"/--\ninfo: not a pin\n-/\n{body}\n{body}\n"),
    ]
    refuse = [
        ("a pin written on one line",
         "/-- info: 'X.a' depends on axioms: [propext] -/ #guard_msgs in "
         "#print axioms X.a\n", 0, {}, "not the prose lines"),
        ("a one-line pin behind `set_option ... in`",
         "set_option pp.fullNames false in /-- info: 'X.a' depends on axioms: "
         "[propext] -/ #guard_msgs in #print axioms X.a\n", 0, {}, "not the prose lines"),
        ("an indented pin inside a section",
         "section P\n  /--\n  info: 'X.a' depends on axioms: [propext]\n  -/\n"
         "  #guard_msgs in\n  #print axioms X.a\nend P\n", 0, {}, "not the prose lines"),
        ("a `(whitespace := lax)` pin ahead of a real one",
         "/--\ninfo: 'X.c' depends on axioms: [propext]\n-/\n"
         f"#guard_msgs (whitespace := lax) in\n#print axioms X.c\n\n{pin}\n{body}",
         1, {}, "not the prose lines"),
        ("a `#guard_msgs` test that is not a pin, ahead of a real pin",
         f"/--\ninfo: 2\n-/\n#guard_msgs in\n#eval (1 + 1 : Nat)\n\n{body}\n{pin}",
         1, {}, "not the prose lines"),
        ("a pin behind `set_option ... in`",
         f"set_option maxRecDepth 4096 in\n{pin}\n{body}", 1, {}, "ending in `in`"),
        ("a pin behind `set_option ... in` and a trailing comment",
         f"set_option maxRecDepth 4096 in -- why\n{pin}\n{body}", 1, {}, "ending in `in`"),
        ("a pin behind `set_option ... in` and a comment line",
         f"set_option maxRecDepth 4096 in\n-- why\n{pin}\n{body}", 1, {}, "ending in `in`"),
        ("a pin behind `open ... in` and a block comment",
         f"open Foo in\n/- why -/\n\n{pin}\n{body}", 1, {}, "ending in `in`"),
        ("`#guard_msgs(drop info)` with no docstring",
         "#guard_msgs(drop info) in\n#print axioms X.a\n", 0, {}, "not the prose lines"),
        ("the two commands on one line after the docstring",
         "/-- info: 'X.a' depends on axioms: [propext] -/\n"
         "#guard_msgs in #print axioms X.a\n", 0, {}, "not the prose lines"),
        ("a pin separated by carriage returns",
         "/-- info: 'X.a' depends on axioms: [propext] -/\r#guard_msgs in\r"
         "#print axioms X.a\n", 0, {}, "carriage return"),
        ("prose naming the command that is not listed",
         f"{prose}\n{body}", 0, {}, "not the prose lines"),
        ("listed prose that has gone",
         body, 0, {prose: 1}, "not the prose lines"),
    ]
    for name, text, expected, lines, want in accept:
        try:
            got = strip_pins(text, f"self-test fixture '{name}'", expected, lines)
        except PortError as e:
            raise PortError(f"self-test: the stripper refused '{name}', which "
                            f"it must accept: {e}")
        if got != want:
            raise PortError(f"self-test: for '{name}' the stripper produced "
                            f"{got!r}, expected {want!r}")
    for name, text, expected, lines, why in refuse:
        try:
            strip_pins(text, f"self-test fixture '{name}'", expected, lines)
        except PortError as e:
            if why in str(e):
                continue
            raise PortError(f"self-test: the stripper refused '{name}', but "
                            f"not with the check meant for it ({why!r}): {e}")
        raise PortError(f"self-test: the stripper accepted '{name}', which it "
                        f"must refuse")
    try:
        rewrite("Tacenta.T1.a Tacenta.T1.b\n", renames(1, 0, 0, 0), "fixture")
    except PortError:
        pass
    else:
        raise PortError("self-test: a rename matching more often than "
                        "asserted was accepted")


UNIT_PINS = "The `#print axioms` pins are restated in Translation/UnitPins.lean."

JOBS = [
    # `T1.lean` opens `Tacenta.T1` at the top and never closes it, so there is
    # no `end` to rewrite. Its six references to `Tacenta.T1.` are all inside
    # its three pins.
    dict(
        origin="T1.lean",
        dest="UnitT1.lean",
        pins=3,
        prose={},
        note=UNIT_PINS,
        subs=[
            (r"^import Translation\.TacentaRatchet$",
             "import Translation.TacentaTripleUnit", 1),
            (r"^namespace Tacenta\.T1$", "namespace Tacenta.UnitT1", 1),
            (r"^open tacenta_ratchet$",
             "open tacenta_triple_unit tacenta_triple_unit.tacenta_ratchet", 1),
        ] + renames(6, 0, 0, 0),
    ),
    dict(
        origin="SpqrT1.lean",
        dest="UnitSpqrT1.lean",
        pins=0,
        prose={},
        note="SpqrT1.lean pins nothing of its own; Translation/UnitPins.lean "
             "pins this\n-- copy's `receive_no_panic`.",
        subs=[
            (r"^import Translation\.TacentaSpqr$",
             "import Translation.TacentaTripleUnit", 1),
            (r"^import Translation\.T1$", "import Translation.UnitT1", 1),
            (r"^namespace Tacenta\.SpqrT1$", "namespace Tacenta.UnitSpqrT1", 1),
            (r"^end Tacenta\.SpqrT1$", "end Tacenta.UnitSpqrT1", 1),
            (r"^open tacenta_spqr$",
             "open tacenta_triple_unit tacenta_triple_unit.tacenta_spqr", 1),
        ] + renames(0, 0, 0, 0),
    ),
    # `T3.lean` is the classical ratchet's refinement of the model. It opens one
    # name from the panic-freedom namespace, which moves with it. Its other 45
    # references to `Tacenta.T1.` are in statements, proof bodies and prose,
    # and seven of them name rules `UnitT1.lean` also registers, in
    # `attribute [-step]` erasures on six lines. Its six references to
    # `Tacenta.T3.` are inside its three pins, which are restated in
    # `UnitPins.lean`.
    dict(
        origin="T3.lean",
        dest="UnitT3.lean",
        pins=3,
        prose={
            "being noticed by whoever next runs `#print axioms` by hand. "
            "Everything each": 1,
        },
        note=UNIT_PINS,
        subs=[
            (r"^import Translation\.TacentaRatchet$",
             "import Translation.TacentaTripleUnit", 1),
            (r"^import Translation\.T1$", "import Translation.UnitT1", 1),
            (r"^namespace Tacenta\.T3$", "namespace Tacenta.UnitT3", 1),
            (r"^end Tacenta\.T3$", "end Tacenta.UnitT3", 1),
            (r"^open tacenta_ratchet$",
             "open tacenta_triple_unit tacenta_triple_unit.tacenta_ratchet", 1),
            (r"^open Tacenta\.T1 \(DerivedKeysModel\)$",
             "open Tacenta.UnitT1 (DerivedKeysModel)", 1),
        ] + renames(45, 0, 6, 0),
    ),
    # `SpqrT3.lean` is the sparse ratchet's refinement. It pins nothing of its
    # own. Its eleven qualified `tacenta_spqr.*` references, to six names, are
    # left as written: under `open tacenta_triple_unit` they resolve to the
    # unit's constants, as the qualified names in `UnitTripleT1.lean` do.
    #
    # The erasure inserted after its `open` is the one piece of text in any copy
    # that is neither the leaf's nor a rename. On the unit, `UnitT1.lean`'s rule
    # for dereferencing a `Zeroizing` wrapper reaches a goal in `kdf_ck_refines`
    # that it cannot reach in the leaf island, and the proof then stops on
    # `UnitT1.ZeroizingTotal`. Measured on 2026-09-10 by removing each candidate
    # rule alone: that rule is the only one whose removal matters. Removing
    # `UnitT1.zeroizing_new_step` and `UnitT1.hkdf_step` as well, which also sit
    # on constants the unit shares, changes no proof term in the file, because
    # this file registers its own rules for those calls later and `step` tries
    # the newest rule first; so they are left.
    dict(
        origin="SpqrT3.lean",
        dest="UnitSpqrT3.lean",
        pins=0,
        prose={
            "neither `lake build` nor `#print axioms` can flag. "
            "`ChainCounterBounded`,": 1,
        },
        note="SpqrT3.lean pins nothing, and nothing pins this copy; the unit's "
             "axiom\n-- audit walks it.",
        subs=[
            (r"^import Translation\.TacentaSpqr$",
             "import Translation.TacentaTripleUnit", 1),
            (r"^import Translation\.SpqrT1$", "import Translation.UnitSpqrT1", 1),
            (r"^namespace Tacenta\.SpqrT3$", "namespace Tacenta.UnitSpqrT3", 1),
            (r"^end Tacenta\.SpqrT3$", "end Tacenta.UnitSpqrT3", 1),
            (r"^open tacenta_spqr$",
             "open tacenta_triple_unit tacenta_triple_unit.tacenta_spqr\n"
             "\n"
             "-- Inserted by port-unit-proofs.sh; neither SpqrT3.lean's text nor a\n"
             "-- rename. On the unit the classical and sparse ratchets share one set\n"
             "-- of `zeroize` constants, so `UnitT1.zeroizing_deref_step`, a stepping\n"
             "-- rule UnitT1.lean registers for the classical ratchet, reaches a goal\n"
             "-- in `kdf_ck_refines` below that it cannot reach in the leaf island.\n"
             "-- It demands `UnitT1.ZeroizingTotal`, which no hypothesis here provides,\n"
             "-- and says only that the call returned; T3.lean removes its own copy\n"
             "-- of the rule for the same reason. Two more UnitT1.lean rules sit on\n"
             "-- constants the unit shares, `zeroizing_new_step` and `hkdf_step`, but\n"
             "-- this file registers its own rules for those calls later and `step`\n"
             "-- tries the newest rule first, so removing them changes no proof here\n"
             "-- and they are left. The removal is local to this file: a module that\n"
             "-- imports it has the rule back.\n"
             "attribute [-step] Tacenta.UnitT1.zeroizing_deref_step", 1),
        ] + renames(0, 24, 0, 0),
    ),
]

# Every copy is generated before any is written, so a refusal part-way through
# leaves all four committed copies as they were rather than some regenerated.
try:
    self_test()
    results = []
    for job in JOBS:
        origin, dest = job["origin"], job["dest"]
        # newline="" keeps a carriage return as written, so the check for one
        # in strip_pins sees it rather than a newline Python translated it to.
        text = open(os.path.join(src, origin), newline="").read()
        text = rewrite(text, job["subs"], origin)
        text = strip_pins(text, origin, job["pins"], job["prose"])
        results.append((origin, dest, NOTE.format(origin=origin, pins=job["note"]) + text))
except PortError as e:
    sys.stderr.write(f"port-unit-proofs: ERROR: {e}\n")
    sys.exit(1)
for origin, dest, text in results:
    open(os.path.join(out, dest), "w", newline="").write(text)
    print(f"port-unit-proofs: {dest} (from {origin})")
PYEOF

if [ "$check" -eq 0 ]; then
  echo "port-unit-proofs: wrote the unit's copies of the leaf proofs"
  echo "port-unit-proofs: next, build the translation package; UnitPins.lean holds"
  echo "port-unit-proofs: the axiom pins and will fail if a pinned trust base moved"
  exit 0
fi

fail=0
for f in UnitT1.lean UnitSpqrT1.lean UnitT3.lean UnitSpqrT3.lean; do
  if ! diff -u "$src/$f" "$tmp/$f" > /dev/null; then
    if [ "$fail" -eq 0 ]; then
      echo "port-unit-proofs: ERROR: the committed copies are not what the leaf" >&2
      echo "  proofs port to. Either a copy was edited by hand, or a leaf proof" >&2
      echo "  changed and nobody re-ported. Regenerate with" >&2
      echo "  tacenta-proofs/scripts/port-unit-proofs.sh and rebuild." >&2
    fi
    fail=1
    diff -u "$src/$f" "$tmp/$f" | head -40 >&2
  fi
done
if [ "$fail" -ne 0 ]; then
  exit 1
fi
echo "port-unit-proofs: the committed copies are what the leaf proofs port to"
