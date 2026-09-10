#!/usr/bin/env python3
"""The assumption bundles in `TripleT3.lean` still say what their leaf theorems say.

    python3 tooling/check-bundle-drift.py
    python3 tooling/check-bundle-drift.py --translation-dir DIR

`tacenta-proofs/translation/Translation/TripleT3.lean` composes the classical
ratchet's and the sparse ratchet's refinement results but cannot cite them:
Charon translates each crate on its own, so `T3.lean`'s and `SpqrT3.lean`'s
leaf theorems are about declarations that only share a name with the ones the
triple's translation emits. In place of citing them the file declares two
hand-written bundles, `RatchetAgreesFor α` and `SpqrAgreesFor β`, whose
clauses are meant to restate exactly what a leaf theorem requires and
concludes, transported through an assumed abstraction.

A bundle clause is a `def ... : Prop`, never an application of the leaf
theorem, so **Lean has nothing to compare** and the agreement is maintained by
eye. It has drifted twice; both times a leaf's counter bound tightened by a
step and the bundle kept the older, weaker one, through a green build. This
script is the missing comparison. It needs no Lean toolchain and costs
milliseconds, so it can run in the `checks` job beside the other text checks.

## How it works

Each top-level `∧`-clause of a bundle must carry a provenance comment on the
line above it, in one of two forms:

    -- mirrors: Tacenta.T3.receive_refines in T3.lean
    -- mirrors: nothing -- <why there is no leaf theorem for this clause>

For a clause that names a leaf theorem, the script extracts both sides'
hypotheses and conclusion, rewrites both into one canonical form using the
substitution table declared below, and compares the hypotheses as a multiset
and the conclusion as a normalised string. A difference is reported with both
sides printed.

The substitution table is what makes the two comparable across the transport,
and it is small and explicit on purpose:

  * the abstraction itself -- `(α s)` on the bundle side, and on the leaf side
    *both* the model binder `m` and the real state's own field reads
    (`s.events.val`), since a leaf theorem states some hypotheses over the
    model state and some over the real one and `StateR`/`StateRefines` is what
    ties them;
  * the constants -- `Model.State.maxSkippedStore` against
    `MAX_SKIPPED_STORE.val`, and `Model.SparseRatchet.maxSkip` against
    `MAX_SKIP.val`. Each such bridge names the leaf lemma that justifies it,
    and the script fails if that lemma is no longer in the file it names, or
    if its statement no longer mentions both spellings;
  * the element maps -- `p.1.val` against `p.1` and `sk.epoch.val` against
    `sk.1` inside a quantifier over a transported list, likewise named --
    but named for the *transport*, not for a lemma justifying it. No
    top-level declaration states either equality: `chainsEntryOf` and
    `skippedOf` are `def`s, and what makes the two sides equal is a field of
    `StateRefines` (`chains`, `skipped`), which is not a declaration this
    check can look for. So those bridges' guard says only that the transport
    is still there, and the one written as `StateRefines` says less than
    that, since the relation is the state relation the whole comparison is
    already built on and cannot go missing while anything else works. The
    bridge table below says so on each of them;
  * the definitional restatements -- `matchesHeader mh` against the projection
    lambda the bundle writes out;
  * plain renaming -- the crate namespace, `Std.`, `RatchetHeaderR` against
    `HeaderR`, and the two sides' differing binder names.

## What it does NOT see, and will not pretend to

This is a *textual* check with a declared rewrite table. It is not a proof
checker and it does not evaluate Lean.

  1. It cannot tell you the bridges are true. `matchesHeader_eta`,
     `max_skipped_store_agrees`, `max_skip_agrees` and
     `chainCounterBounded_of_real` are checked to *exist*, not to say what the
     table claims they say. A bridge whose lemma is reworded to mean something
     else still passes. Two of the sparse ratchet's bridges are weaker again:
     they name a transport (`chainsEntryOf`, `StateRefines`) rather than any
     lemma, because nothing states their equality at the top level, so the
     guard checks that the transport is still defined and nothing more.
  2. It cannot see a clause whose leaf theorem is not named. A clause marked
     `mirrors: nothing` is taken at its word -- the two `clone`s, the four
     accessors and `tacenta_spqr`'s initialisers genuinely have no leaf
     theorem, and this script cannot tell that case from a marker written to
     silence it. What it does enforce is that every leaf theorem in the
     bundle's `requires` list below is mirrored by some clause, so a whole
     mirrored clause cannot be deleted quietly.
  3. It does not check that the bundle's boundary assumptions are complete.
     A leaf theorem's crate-boundary hypotheses (`HmacAgrees`, `HkdfAgrees`,
     the `Zeroizing` round trips, `DerivedKeysModel`, the `Vec` agreements)
     are deliberately absent from the bundles -- that is the third thing the
     file's header warns about, and it is a design decision, not drift. The
     script drops them by an explicit list and *prints what it dropped* on
     every run, so the omission stays visible; it cannot judge whether
     dropping them is still sound.
  4. It compares statements, not proofs. A leaf theorem restated identically
     but proved from a weaker lemma is invisible here.
  5. It is defeated by reformatting it cannot parse. That is why every failure
     mode below is a FAIL and never a skip: an unparseable clause, an
     unrecognised binder, a leftover `α`/`β`, a state field with no transport
     entry, or a constant bridge whose lemma has gone all report "cannot
     compare" and exit non-zero. An unanalysable clause is a problem to fix,
     not a hole to pass through.

Nothing here is skipped when a tool is missing, because nothing here needs a
tool: it is `python3` and the files.
"""

import argparse
import os
import re
import sys
from collections import Counter

# --------------------------------------------------------------------------
# The declared tables.
#
# Everything the script is allowed to treat as "the same thing written two
# ways" is listed here. Anything it meets that is not listed is a failure, not
# a pass -- so widening the check is an edit to this section, in the diff,
# rather than a regex quietly matching more than it used to.
# --------------------------------------------------------------------------

# Crate namespaces the triple's translation prefixes its names with, and the
# leaf files do not (they are inside their own crate's translation).
CRATE_PREFIXES = ["tacenta_ratchet.", "tacenta_spqr."]

# Binder types that carry a value rather than a hypothesis. A binder whose
# normalised type is not one of these, not a boundary assumption, and not
# recognisably a proposition, stops the comparison.
VALUE_TYPES = {
    "State", "Header", "LabelSet", "Output", "Chain", "Chains",
    "Model.State.State", "Model.State.Header", "Model.State.Key",
    "Model.SparseRatchet.State", "Model.SparseRatchet.Output",
    "Model.SparseRatchet.Chain",
    "U8", "U16", "U32", "U64", "Usize", "Nat", "Bool",
}
VALUE_TYPE_HEADS = ("Array ", "Option ", "Slice ", "List ", "Vec ")

# Symbols that make a binder's type a proposition worth comparing.
PROP_MARKERS = ("≤", "<", ">", "≥", "=", "∈", "∀", "∃", "→", "∨", "∧", "¬")

# Propositions that are relations between a real state and a model state. The
# abstraction `α`/`β` *is* this relation, so a leaf hypothesis of this shape is
# the transport itself and has no bundle counterpart. Dropped, and reported.
STATE_RELATIONS = ["StateR", "StateRefines"]


class Bridge:
    """One declared equivalence, anchored to a declaration in the leaf file.

    Usually that declaration is the lemma proving the two sides equal. Where
    no top-level declaration states the equality it is the transport itself,
    a `def` or the refinement `structure`; the bridge's `note` says which,
    because the guard is only as strong as what it names.
    """

    def __init__(self, leaf, bundle, canon, lemma, lemma_file, note,
                 anchor_states=False):
        self.leaf = leaf            # regex, leaf-side spelling
        self.bundle = bundle        # regex, bundle-side spelling
        self.canon = canon          # what both become
        # Whether the anchor's own statement must mention both spellings.
        # True for a bridge between two names for one constant, where the
        # anchor really is a lemma equating them and its statement can be
        # read. False where the anchor is a transport (a `def`, or the
        # refinement `structure`), whose statement says no such thing; the
        # `note` says which case a bridge is.
        self.anchor_states = anchor_states
        self.lemma = lemma          # the declaration this bridge is anchored to
        self.lemma_file = lemma_file
        self.note = note


class BundleSpec:
    def __init__(self, name, abstraction, leaf_file, leaf_namespace,
                 state_type, model_state_type, state_relation,
                 fields, bridges, boundary, requires):
        self.name = name
        self.abstraction = abstraction
        self.leaf_file = leaf_file
        self.leaf_namespace = leaf_namespace
        self.state_type = state_type
        self.model_state_type = model_state_type
        self.state_relation = state_relation
        # canonical field name -> the real state's own path to it. The model
        # side is `m.<field>`, the bundle side `(α s).<field>`; all three
        # become `⟦s⟧.<field>`. A state field read with no entry here is
        # "cannot compare".
        self.fields = fields
        self.bridges = bridges
        self.boundary = boundary    # leaf hypotheses deliberately not carried
        self.requires = requires    # leaf theorems some clause must mirror


RATCHET = BundleSpec(
    name="RatchetAgreesFor",
    abstraction="α",
    leaf_file="T3.lean",
    leaf_namespace="Tacenta.T3",
    state_type="State",
    model_state_type="Model.State.State",
    state_relation="StateR",
    fields={"skipped": "skipped.val", "events": "events.val",
            "ns": "ns.val", "nr": "nr.val", "dhsPub": "dhs_pub"},
    bridges=[
        Bridge(
            leaf=r"\bMAX_SKIPPED_STORE\.val\b",
            bundle=r"\bModel\.State\.maxSkippedStore\b",
            canon="MAX_SKIPPED_STORE",
            lemma="max_skipped_store_agrees", lemma_file="T3.lean",
            anchor_states=True,
            note="the store bound is one constant written two ways"),
        Bridge(
            leaf=r"\bMAX_SKIP\.val\b",
            bundle=r"\bModel\.State\.maxSkip\b",
            canon="MAX_SKIP",
            lemma="max_skip_agrees", lemma_file="T3.lean",
            anchor_states=True,
            note="the skip bound is one constant written two ways"),
        Bridge(
            leaf=r"\bmatchesHeader (?P<mh>\w+)\b",
            bundle=r"\(fun (?P<v>[\w♯']+) => (?P=v)\.1 == (?P<mh>\w+)\.dh"
                   r" && (?P=v)\.2\.1 == (?P=mh)\.n\)",
            canon=r"⟨matchesHeader \g<mh>⟩",
            lemma="matchesHeader_eta", lemma_file="T3.lean",
            note="the bundle writes the model's predicate out with "
                 "projections where the leaf names it"),
    ],
    boundary=["HmacAgrees", "HkdfAgrees", "ZeroizingRoundTrips",
              "ZeroizingRoundTrips80", "Tacenta.T1.VecRemoveTotal",
              "DerivedKeysModel"],
    requires=["send_refines", "receive_refines",
              "init_sender_refines", "init_receiver_refines"],
)

SPQR = BundleSpec(
    name="SpqrAgreesFor",
    abstraction="β",
    leaf_file="SpqrT3.lean",
    leaf_namespace="Tacenta.SpqrT3",
    state_type="State",
    model_state_type="Model.SparseRatchet.State",
    state_relation="StateRefines",
    fields={"skipped": "skipped.val", "chains": "chains.val",
            "epoch": "epoch.val"},
    bridges=[
        Bridge(
            leaf=r"\bMAX_SKIP\.val\b",
            bundle=r"\bModel\.SparseRatchet\.maxSkip\b",
            canon="MAX_SKIP",
            lemma="max_skip_agrees", lemma_file="SpqrT3.lean",
            anchor_states=True,
            note="the skip bound is one constant written two ways"),
        Bridge(
            leaf=r"\b(\w+)\.1\.val\b",
            bundle=r"\b(\w+)\.1\.val\b",
            canon=r"\1.1",
            lemma="chainsEntryOf", lemma_file="SpqrT3.lean",
            note="a chain-table entry's epoch: the model table is the real "
                 "one's image under `chainsEntryOf`. Anchored to that "
                 "transport, a `def`; the equality is `StateRefines.chains`, "
                 "a field and not a declaration this check can look for"),
        Bridge(
            leaf=r"\b(\w+)\.epoch\.val\b",
            bundle=r"\b(\w+)\.1\b(?!\.val)",
            canon=r"\1.1",
            lemma="StateRefines", lemma_file="SpqrT3.lean",
            note="a stored key's epoch: the model list is the real one's "
                 "image under `skippedOf`, which is `StateRefines.skipped`. "
                 "Anchored to the relation itself, so this one is a pointer "
                 "rather than a check: it cannot fire while the comparison "
                 "it belongs to runs at all"),
        Bridge(
            leaf=r"\b(\w+)\.n\.val\b",
            bundle=r"\b(\w+)\.n\b(?!\.val)",
            canon=r"\1.n",
            lemma="chainCounterBounded_of_real", lemma_file="SpqrT3.lean",
            note="a chain's counter, stated over the model table here and "
                 "over the real one in the leaf"),
        Bridge(
            leaf=r"\bChain\b",
            bundle=r"\bModel\.SparseRatchet\.Chain\b",
            canon="Chain",
            lemma="chainsEntryOf", lemma_file="SpqrT3.lean",
            note="the counter bound quantifies over the model's chain type "
                 "here and the real one in the leaf. Anchored to the same "
                 "transport as the entry bridge, and weak the same way; the "
                 "bound itself travels by `chainCounterBounded_of_real`"),
    ],
    boundary=["SpqrHkdfAgrees", "ZeroizingRoundTrips96", "ZeroizingRoundTrips64",
              "VecRetainAgrees", "VecAppendAgrees", "VecRemoveAgrees",
              "Tacenta.SpqrT1.ZeroizeTotal", "Tacenta.SpqrT1.OptionCloneTotal"],
    requires=["send_refines", "receive_refines"],
)

BUNDLE_FILE = "TripleT3.lean"
BUNDLES = [RATCHET, SPQR]

# Plain renames with no mathematical content: the triple's own names for
# things the leaf files name differently. Applied to both sides.
PLAIN_RENAMES = [
    (r"\bRatchetHeaderR\b", "HeaderR"),
    (r"\bratchetLabelsOf\b", "labelsOf"),
    (r"\bspqrOutputOf\b", "outputOf"),
]

MARKER_RE = re.compile(r"^\s*--\s*mirrors:\s*(.+?)\s*$")
MIRRORS_THM_RE = re.compile(r"^([A-Za-z_][\w.]*)\s+in\s+([\w./-]+)$")
MIRRORS_NONE_RE = re.compile(r"^nothing\b")

CONVENTION = """the provenance convention: every top-level clause of a bundle
    carries, on the line above it, exactly one of

        -- mirrors: <Namespace>.<theorem> in <file>.lean
        -- mirrors: nothing -- <why no leaf theorem states this>

    naming the leaf theorem the clause restates, or saying there is none."""


# --------------------------------------------------------------------------
# Small Lean-shaped text utilities.
# --------------------------------------------------------------------------

OPENERS = {"(": ")", "{": "}", "[": "]", "⦃": "⦄", "⟨": "⟩"}
CLOSERS = {v: k for k, v in OPENERS.items()}


def strip_line_comment(line):
    """Drop a `--` comment. The statements here contain no string literals."""
    i = line.find("--")
    return line if i < 0 else line[:i]


def collapse(text):
    return re.sub(r"\s+", " ", text).strip()


def find_depth0(text, needle, start=0):
    depth = 0
    for i, ch in enumerate(text):
        if i >= start and depth == 0 and text.startswith(needle, i):
            return i
        if ch in OPENERS:
            depth += 1
        elif ch in CLOSERS:
            depth -= 1
    return -1


def strip_outer_parens(text):
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        for i, ch in enumerate(text):
            if ch in OPENERS:
                depth += 1
            elif ch in CLOSERS:
                depth -= 1
                if depth == 0 and i != len(text) - 1:
                    return text
        text = text[1:-1].strip()
    return text


def read_group(text, i):
    """Read a bracketed group starting at `text[i]`; return (text, end)."""
    close = OPENERS[text[i]]
    depth, j = 0, i
    while j < len(text):
        if text[j] in OPENERS:
            depth += 1
        elif text[j] in CLOSERS:
            depth -= 1
            if depth == 0:
                return text[i:j + 1], j + 1
        j += 1
    raise Unanalysable("unbalanced %r" % text[i:i + 40])


def read_term(text, i):
    """Read one argument: a bracketed group, or a run of term characters."""
    while i < len(text) and text[i] == " ":
        i += 1
    if i >= len(text):
        return "", i
    if text[i] in OPENERS:
        return read_group(text, i)
    j = i
    while j < len(text) and (text[j].isalnum() or text[j] in "_.'#♯"):
        j += 1
    return text[i:j], j


def read_rhs(text, i):
    """Read the right-hand side of an `=`, up to a depth-zero `∧`, `,`, or
    the end of the enclosing group."""
    while i < len(text) and text[i] == " ":
        i += 1
    depth, j = 0, i
    while j < len(text):
        ch = text[j]
        if ch in OPENERS:
            depth += 1
        elif ch in CLOSERS:
            if depth == 0:
                break
            depth -= 1
        elif depth == 0 and (ch == "∧" or ch == ","):
            break
        j += 1
    return text[i:j].strip(), j


class Unanalysable(Exception):
    """Raised where normalisation cannot decide. Always a FAIL, never a pass."""


# --------------------------------------------------------------------------
# Reading the two sides.
# --------------------------------------------------------------------------

class Binder:
    def __init__(self, names, type_text, kind):
        self.names = names
        self.type = type_text
        self.kind = kind        # "explicit" | "implicit" | "instance"

    def __repr__(self):
        return "%s : %s" % (" ".join(self.names) or "_", self.type)


def parse_binder_groups(text, i):
    """Parse `(a b : T) {c : U} [I]` from `text[i:]`; return (binders, end)."""
    binders = []
    while True:
        while i < len(text) and text[i] == " ":
            i += 1
        if i >= len(text) or text[i] not in "({[":
            return binders, i
        kind = {"(": "explicit", "{": "implicit", "[": "instance"}[text[i]]
        group, i = read_group(text, i)
        inner = group[1:-1].strip()
        colon = find_depth0(inner, " : ")
        if colon < 0:
            if kind == "instance":
                binders.append(Binder([], inner, kind))
                continue
            raise Unanalysable("binder group %r has no `:`" % group)
        names = inner[:colon].split()
        binders.append(Binder(names, inner[colon + 3:].strip(), kind))


def read_theorem(path, short_name):
    """Return the statement text of `theorem <short_name>` in `path`."""
    with open(path, encoding="utf-8") as fh:
        lines = fh.readlines()
    start = None
    for n, line in enumerate(lines):
        if re.match(r"^(private\s+)?theorem\s+%s\b" % re.escape(short_name), line):
            start = n
            break
    if start is None:
        return None
    buf, depth = [], 0
    for line in lines[start:]:
        text = strip_line_comment(line)
        for i, ch in enumerate(text):
            if ch in OPENERS:
                depth += 1
            elif ch in CLOSERS:
                depth -= 1
            elif depth == 0 and text.startswith(":=", i):
                buf.append(text[:i])
                return collapse("".join(buf))
        buf.append(text)
    raise Unanalysable("theorem %s has no `:=`" % short_name)


def read_def_body(path, def_name):
    """Return [(lineno, raw)] for the body of `def <def_name> ... :=`."""
    with open(path, encoding="utf-8") as fh:
        lines = fh.readlines()
    start = None
    for n, line in enumerate(lines):
        if re.match(r"^def\s+%s\b" % re.escape(def_name), line):
            start = n
            break
    if start is None:
        return None, None
    header = lines[start]
    body = []
    for n in range(start + 1, len(lines)):
        line = lines[n]
        if line.strip() and not line[0].isspace():
            break
        body.append((n + 1, line.rstrip("\n")))
    return header, body


def split_clauses(body):
    """Split a bundle body into top-level `∧`-clauses, each with the
    `-- mirrors:` marker on the line above it."""
    clauses = []
    pending = None
    cur, cur_line, cur_marker = [], None, None
    depth = 0
    for lineno, raw in body:
        m = MARKER_RE.match(raw)
        if m:
            if pending is not None:
                raise Unanalysable(
                    "two `-- mirrors:` comments in a row, at lines %d and %d; "
                    "one of them belongs to no clause" % (pending[0], lineno))
            pending = (lineno, m.group(1))
            continue
        line = strip_line_comment(raw)
        if not line.strip():
            continue
        for ch in line:
            if ch in OPENERS:
                depth += 1
            elif ch in CLOSERS:
                depth -= 1
            if depth == 0 and ch == "∧":
                clauses.append((cur_line, cur_marker, collapse("".join(cur))))
                cur, cur_line, cur_marker = [], None, None
                continue
            if cur_line is None and not ch.isspace():
                cur_line = lineno
                cur_marker = pending
                pending = None
            cur.append(ch)
        cur.append(" ")
    if "".join(cur).strip():
        clauses.append((cur_line, cur_marker, collapse("".join(cur))))
    return clauses


def parse_clause(text):
    """A bundle clause: alternating `∀`-binder groups and `H →` hypotheses,
    ending in the body `∃ r, CALL = ok r ∧ POST`."""
    text = strip_outer_parens(text)
    binders, hyps = [], []
    while True:
        text = text.strip()
        if text.startswith("∀ "):
            comma = find_depth0(text, ",")
            if comma < 0:
                raise Unanalysable("`∀` with no `,`: %r" % text[:60])
            head = text[2:comma].strip()
            if head.startswith(("(", "{", "[")):
                got, end = parse_binder_groups(head, 0)
                if head[end:].strip():
                    raise Unanalysable("binder group tail %r" % head[end:])
                binders.extend(got)
            elif find_depth0(head, " : ") >= 0:
                # `∀ sk : Slice U8,`: typed, but with no brackets.
                at = find_depth0(head, " : ")
                binders.append(Binder(head[:at].split(), head[at + 3:].strip(),
                                      "explicit"))
            else:
                # `∀ s,` / `∀ N salt ikm info,`: no types given.
                binders.extend([Binder([n], None, "explicit") for n in head.split()])
            text = text[comma + 1:]
            continue
        if text.startswith("∃ "):
            return binders, hyps, text
        arrow = find_depth0(text, "→")
        if arrow < 0:
            return binders, hyps, text
        hyps.append(strip_outer_parens(text[:arrow]))
        text = text[arrow + 1:]


def parse_leaf(statement, short_name):
    """A leaf theorem: binder groups, then `: CALL ⦃ fun r => POST ⦄`."""
    head = re.match(r"^(private\s+)?theorem\s+\S+", statement)
    binders, i = parse_binder_groups(statement, head.end())
    rest = statement[i:].strip()
    if not rest.startswith(":"):
        raise Unanalysable("%s: expected `:` before the statement, saw %r"
                           % (short_name, rest[:40]))
    return binders, rest[1:].strip()


def split_leaf_conclusion(conclusion, name):
    """`CALL ⦃ fun r => POST ⦄` -> (call, result binder, post)."""
    open_at = find_depth0(conclusion, "⦃")
    if open_at < 0:
        raise Unanalysable("%s: conclusion is not a `⦃ ⦄` triple" % name)
    call = conclusion[:open_at].strip()
    group, end = read_group(conclusion, open_at)
    if conclusion[end:].strip():
        raise Unanalysable("%s: text after the `⦃ ⦄` triple" % name)
    inner = group[1:-1].strip()
    m = re.match(r"^fun\s+(\w+)\s*=>", inner)
    if not m:
        raise Unanalysable("%s: triple's postcondition is not `fun r => ...`"
                           % name)
    return call, m.group(1), inner[m.end():].strip()


def split_bundle_body(body, name):
    """`∃ r, CALL = ok r ∧ POST` -> (call, result binder, post)."""
    m = re.match(r"^∃\s+(\w+)\s*,", body)
    if not m:
        raise Unanalysable("%s: clause body is not `∃ r, ... = ok r ∧ ...`"
                           % name)
    res = m.group(1)
    rest = body[m.end():].strip()
    marker = "= ok %s" % res
    at = find_depth0(rest, marker)
    if at < 0:
        raise Unanalysable("%s: clause body has no `= ok %s` at the top level"
                           % (name, res))
    call = rest[:at].strip()
    tail = rest[at + len(marker):].strip()
    if not tail.startswith("∧"):
        raise Unanalysable("%s: nothing conjoined after `= ok %s`" % (name, res))
    return call, res, tail[1:].strip()


# --------------------------------------------------------------------------
# Normalisation.
# --------------------------------------------------------------------------

LOCAL_BINDER_RE = re.compile(
    r"(?:(?:∀|∃)\s+(?P<ns>[A-Za-z_][\w']*(?:\s+[A-Za-z_][\w']*)*)\s*(?=[,∈:])"
    r"|fun\s+(?P<f>[A-Za-z_][\w']*)\s*(?==>))")


def alpha_locals(text, forbidden):
    """Rename `∀`/`∃`/`fun` binders to positional names.

    Two purposes, both load-bearing. It lets the two sides differ in what they
    call a bound variable (`∀ e` in the leaf against `∀ err` in the clause)
    without that reading as drift. And it runs *before* the value binders are
    renamed onto the clause's spelling, so a rename cannot capture a local of
    the same name -- which would otherwise happen in `SpqrT3.send_refines`,
    whose failure branch binds `e` while its `sending_epoch` is called `e` in
    the clause. A local that shadows a value binder is not renamed away, it is
    refused: that is a statement this check cannot read.
    """
    counter, pos = 0, 0
    while True:
        m = LOCAL_BINDER_RE.search(text, pos)
        if not m:
            return text
        names = (m.group("ns") or m.group("f")).split()
        head, tail = text[:m.start()], text[m.start():]
        for name in names:
            if name in forbidden:
                raise Unanalysable(
                    "the bound variable `%s` shadows a binder of the same "
                    "name" % name)
            tail = re.sub(r"(?<![\w'])%s(?![\w'])" % re.escape(name),
                          "♯%d" % counter, tail)
            counter += 1
        text = head + tail
        pos = m.start() + 1


class Side:
    """One side of a comparison, with the names normalisation needs."""

    def __init__(self, spec, state_var, model_var, renames,
                 is_bundle, bound=()):
        self.spec = spec
        self.bound = set(bound)
        self.state_var = state_var
        self.model_var = model_var
        self.renames = renames
        self.is_bundle = is_bundle


def apply_renames(text, renames):
    if not renames:
        return text
    pattern = r"\b(%s)\b(?!')" % "|".join(re.escape(k) for k in sorted(
        renames, key=len, reverse=True))
    return re.sub(pattern, lambda m: renames[m.group(1)], text)


def canon_relation(text, spec, is_bundle):
    """`StateR A B` / `α A = B` -> `≈(A, B)`."""
    for head in STATE_RELATIONS:
        while True:
            m = re.search(r"\b%s\b" % head, text)
            if not m:
                break
            a, i = read_term(text, m.end())
            b, j = read_term(text, i)
            if not a or not b:
                raise Unanalysable("`%s` without two arguments" % head)
            text = (text[:m.start()] + "≈(%s, %s)"
                    % (strip_outer_parens(a), strip_outer_parens(b)) + text[j:])
    if is_bundle:
        alpha = spec.abstraction
        while True:
            m = re.search(r"(?<![\w'])%s\s" % re.escape(alpha), text)
            if not m:
                break
            a, i = read_term(text, m.end() - 1)
            rest = text[i:].lstrip()
            if not rest.startswith("="):
                raise Unanalysable(
                    "`%s %s` is not an equation, so the transport cannot be "
                    "read as the state relation" % (alpha, a))
            eq_at = text.index("=", i)
            b, j = read_rhs(text, eq_at + 1)
            text = (text[:m.start()] + "≈(%s, %s)"
                    % (strip_outer_parens(a), strip_outer_parens(b)) + text[j:])
    return text


def normalise(text, side):
    spec = side.spec
    t = collapse(text)

    # 1. Plain namespace differences, no content.
    for prefix in CRATE_PREFIXES:
        t = t.replace(prefix, "")
    t = t.replace("Std.", "")
    for pat, repl in PLAIN_RENAMES:
        t = re.sub(pat, repl, t)

    # 2. Locally bound names first, so a value rename cannot capture one.
    t = alpha_locals(t, side.bound)

    # 3. Binder names: bring the leaf onto the bundle's spelling, and both
    #    result binders onto `RES`.
    t = apply_renames(t, side.renames)

    # 4. The transport, in this order: the real state's own field reads first
    #    (so `s.epoch.val` cannot be mistaken for a list element's `.epoch`),
    #    then the bundle's `(α s)`, then the leaf's model binder.
    if side.state_var:
        for field, real_path in spec.fields.items():
            t = re.sub(r"(?<![\w'])%s\.%s\b" % (re.escape(side.state_var),
                                                re.escape(real_path)),
                       "⟦%s⟧.%s" % (side.state_var, field), t)
        t = re.sub(r"\(\s*%s\s+%s\s*\)" % (re.escape(spec.abstraction),
                                           re.escape(side.state_var)),
                   "⟦%s⟧" % side.state_var, t)
    t = canon_relation(t, spec, side.is_bundle)
    if side.model_var and side.state_var:
        t = re.sub(r"(?<![\w'])%s(?![\w'])" % re.escape(side.model_var),
                   "⟦%s⟧" % side.state_var, t)
        for field in spec.fields:
            t = t.replace("⟦%s⟧.%s" % (side.state_var, field),
                          "⟦%s⟧.%s" % (side.state_var, field))

    # 5. The declared bridges.
    for bridge in spec.bridges:
        pattern = bridge.bundle if side.is_bundle else bridge.leaf
        t = re.sub(pattern, bridge.canon, t)

    # 6. Spacing and parentheses that carry no meaning: one side writes
    #    `(matchesHeader mh)` where the other's lambda already brought its own.
    t = re.sub(r"\(\s*(⟨[^⟩]*⟩)\s*\)", r"\1", t)
    t = re.sub(r"\s*∧\s*", " ∧ ", t)
    t = collapse(t)
    return t


def residue(text, side):
    """What normalisation could not account for. Non-empty means FAIL."""
    spec = side.spec
    problems = []
    if re.search(r"(?<![\w'])%s(?![\w'])" % re.escape(spec.abstraction), text):
        problems.append("the abstraction `%s` survives normalisation"
                        % spec.abstraction)
    if side.state_var and re.search(
            r"(?<![\w'])%s\.\w" % re.escape(side.state_var), text):
        bad = re.findall(r"(?<![\w'])%s\.[\w.]+" % re.escape(side.state_var), text)
        problems.append(
            "real-state field read with no transport entry: %s (known fields: %s)"
            % (", ".join(sorted(set(bad))), ", ".join(sorted(spec.fields))))
    if side.model_var and re.search(
            r"(?<![\w'])%s\.\w" % re.escape(side.model_var), text):
        bad = re.findall(r"(?<![\w'])%s\.[\w.]+" % re.escape(side.model_var), text)
        problems.append("model-state field read with no transport entry: %s"
                        % ", ".join(sorted(set(bad))))
    unknown = [f for f in re.findall(r"⟦\w+⟧\.(\w+)", text)
               if f not in spec.fields]
    if unknown:
        problems.append(
            "state field with no transport entry: %s (declared: %s). Until "
            "this field's real-side path is added to the table there is no "
            "saying whether the two sides speak of the same thing"
            % (", ".join(sorted(set(unknown))), ", ".join(sorted(spec.fields))))
    leftover = re.findall(r"\bModel\.(?:State|SparseRatchet)\.(max\w+)\b", text)
    if leftover:
        problems.append("model constant with no declared bridge: %s"
                        % ", ".join(sorted(set(leftover))))
    leftover = re.findall(r"\b(MAX_\w+)\.val\b", text)
    if leftover:
        problems.append("crate constant with no declared bridge: %s"
                        % ", ".join(sorted(set(leftover))))
    return problems


# --------------------------------------------------------------------------
# Numeric bounds. This is what drifted, both times.
# --------------------------------------------------------------------------

BOUND_RE = re.compile(r"^(?P<lhs>.+?)\s*(?P<op>≤|<|≥|>)\s*(?P<rhs>\S+)$")
OFFSET_RE = re.compile(r"^(?P<base>.+?)\s*\+\s*(?P<k>\d+)$")


def bound_signature(hypothesis):
    """`x + 1 < U32.max` -> (('x', '<', 'U32.max'), 1). None if not a bound."""
    m = BOUND_RE.match(hypothesis.strip())
    if not m:
        return None
    lhs = m.group("lhs").strip()
    off = OFFSET_RE.match(lhs)
    if off:
        return ((off.group("base").strip(), m.group("op"), m.group("rhs")),
                int(off.group("k")))
    return ((lhs, m.group("op"), m.group("rhs")), 0)


def bound_drift(leaf_only, bundle_only):
    """Pair up hypotheses that are the same bound at different headroom."""
    pairs, used_l, used_b = [], set(), set()
    leaf_sigs = [(i, bound_signature(h)) for i, h in enumerate(leaf_only)]
    bundle_sigs = [(i, bound_signature(h)) for i, h in enumerate(bundle_only)]
    for li, lsig in leaf_sigs:
        if lsig is None:
            continue
        for bi, bsig in bundle_sigs:
            if bsig is None or bi in used_b or li in used_l:
                continue
            if lsig[0] == bsig[0] and lsig[1] != bsig[1]:
                pairs.append((leaf_only[li], bundle_only[bi], lsig[1], bsig[1]))
                used_l.add(li)
                used_b.add(bi)
    return pairs, [h for i, h in enumerate(leaf_only) if i not in used_l], \
        [h for i, h in enumerate(bundle_only) if i not in used_b]


# --------------------------------------------------------------------------
# The comparison.
# --------------------------------------------------------------------------

def classify(binder, spec):
    """"value" | "model-state" | "boundary" | "hypothesis"."""
    if binder.kind == "instance":
        return "boundary"
    ty = binder.type
    if ty is None:
        return "value"
    ty = collapse(ty)
    for prefix in CRATE_PREFIXES:
        ty = ty.replace(prefix, "")
    ty = ty.replace("Std.", "")
    if ty == spec.model_state_type:
        return "model-state"
    if ty in VALUE_TYPES or ty.startswith(VALUE_TYPE_HEADS):
        return "value"
    if any(b.split(".")[-1] == ty.split(".")[-1] for b in spec.boundary):
        return "boundary"
    head = ty.split()[0] if ty.split() else ty
    if head in STATE_RELATIONS or head in ("HeaderR", "RatchetHeaderR"):
        return "hypothesis"
    if any(sym in ty for sym in PROP_MARKERS):
        return "hypothesis"
    raise Unanalysable(
        "cannot classify the binder `%s : %s` -- it is not a declared value "
        "type, not a declared boundary assumption of %s, and has no relational "
        "symbol that would make it a hypothesis"
        % (" ".join(binder.names) or "_", ty, spec.leaf_file))


def normal_type(ty):
    if ty is None:
        return None
    ty = collapse(ty)
    for prefix in CRATE_PREFIXES:
        ty = ty.replace(prefix, "")
    return ty.replace("Std.", "")


def compare_clause(spec, clause_text, thm_short, leaf_path, report):
    statement = read_theorem(leaf_path, thm_short)
    if statement is None:
        raise Unanalysable(
            "no `theorem %s` in %s -- the clause names a leaf theorem that is "
            "not there" % (thm_short, os.path.basename(leaf_path)))

    leaf_binders, leaf_conclusion = parse_leaf(statement, thm_short)
    b_binders, b_hyps_raw, b_body = parse_clause(clause_text)

    leaf_values, leaf_hyps, dropped = [], [], []
    model_var = None
    for binder in leaf_binders:
        kind = classify(binder, spec)
        if kind == "boundary":
            label = " ".join(binder.names)
            dropped.append(normal_type(binder.type) if not label
                           else "%s : %s" % (label, normal_type(binder.type)))
        elif kind == "model-state":
            if len(binder.names) != 1:
                raise Unanalysable("more than one name in a model-state binder")
            model_var = binder.names[0]
        elif kind == "value":
            for n in binder.names:
                leaf_values.append((n, normal_type(binder.type)))
        else:
            leaf_hyps.append(binder.type)

    bundle_values = []
    for binder in b_binders:
        kind = classify(binder, spec)
        if kind != "value":
            raise Unanalysable(
                "the bundle clause binds `%s`, which is not a plain value "
                "binder; a bundle carries no boundary assumptions" % binder)
        for n in binder.names:
            bundle_values.append((n, normal_type(binder.type)))

    if len(leaf_values) != len(bundle_values):
        raise Unanalysable(
            "cannot compare: the leaf theorem binds %d value(s) [%s] and the "
            "clause binds %d [%s]"
            % (len(leaf_values), ", ".join(n for n, _ in leaf_values),
               len(bundle_values), ", ".join(n for n, _ in bundle_values)))
    renames = {}
    for (ln, lt), (bn, bt) in zip(leaf_values, bundle_values):
        if lt is not None and bt is not None and lt != bt:
            raise Unanalysable(
                "cannot compare: binder `%s : %s` in the leaf theorem against "
                "`%s : %s` in the clause" % (ln, lt, bn, bt))
        if ln != bn:
            renames[ln] = bn

    state_var = None
    for bn, bt in bundle_values:
        if bt is None or bt == spec.state_type:
            state_var = bn
            break

    # The state relation is the transport itself; it has no clause counterpart.
    kept_leaf_hyps = []
    for hyp in leaf_hyps:
        head = collapse(hyp).split()[0] if collapse(hyp).split() else ""
        if head == spec.state_relation:
            dropped.append("%s (this is what `%s` is)"
                           % (collapse(hyp), spec.abstraction))
        else:
            kept_leaf_hyps.append(hyp)

    leaf_call, leaf_res, leaf_post = split_leaf_conclusion(leaf_conclusion, thm_short)
    b_call, b_res, b_post = split_bundle_body(b_body, thm_short)

    for name, res, values in ((thm_short, leaf_res, leaf_values),
                              (thm_short, b_res, bundle_values)):
        if any(v == res for v, _ in values):
            raise Unanalysable(
                "cannot compare: the result binder `%s` shadows a value binder"
                % res)

    leaf_renames = dict(renames)
    leaf_renames[leaf_res] = "RES"
    leaf_side = Side(spec, state_var, model_var, leaf_renames, False,
                     bound=[n for n, _ in leaf_values] + [leaf_res]
                     + ([model_var] if model_var else []))
    bundle_side = Side(spec, state_var, None, {b_res: "RES"}, True,
                       bound=[n for n, _ in bundle_values] + [b_res])

    leaf_norm = [normalise(h, leaf_side) for h in kept_leaf_hyps]
    bundle_norm = [normalise(h, bundle_side) for h in b_hyps_raw]

    problems = []
    for label, texts, side in (("leaf", leaf_norm, leaf_side),
                               ("bundle", bundle_norm, bundle_side)):
        for text in texts:
            for problem in residue(text, side):
                problems.append("%s hypothesis `%s`: %s" % (label, text, problem))

    leaf_call_n = normalise(leaf_call, leaf_side)
    bundle_call_n = normalise(b_call, bundle_side)
    leaf_post_n = normalise(leaf_post, leaf_side)
    bundle_post_n = normalise(b_post, bundle_side)
    for label, text, side in (("leaf", leaf_post_n, leaf_side),
                              ("bundle", bundle_post_n, bundle_side)):
        for problem in residue(text, side):
            problems.append("%s conclusion: %s" % (label, problem))
    if problems:
        raise Unanalysable("cannot compare:\n      " + "\n      ".join(problems))

    failures = []
    shared = Counter(leaf_norm) & Counter(bundle_norm)
    leaf_only = list((Counter(leaf_norm) - shared).elements())
    bundle_only = list((Counter(bundle_norm) - shared).elements())

    drifted, leaf_only, bundle_only = bound_drift(leaf_only, bundle_only)
    for leaf_h, bundle_h, lk, bk in drifted:
        direction = ("the bundle is WEAKER than what the leaf proves: it "
                     "asserts the refinement under a hypothesis the leaf "
                     "theorem does not grant"
                     if bk < lk else
                     "the bundle is STRONGER than the leaf needs: sound, but "
                     "its callers must discharge more than was proved")
        failures.append(
            "BOUND DRIFT (headroom %d in the leaf, %d in the clause)\n"
            "        leaf   %s\n        clause %s\n        %s"
            % (lk, bk, leaf_h, bundle_h, direction))
    for hyp in leaf_only:
        failures.append(
            "MISSING from the clause -- the leaf theorem requires it:\n"
            "        %s" % hyp)
    for hyp in bundle_only:
        failures.append(
            "EXTRA in the clause -- no leaf hypothesis matches it:\n"
            "        %s" % hyp)
    if leaf_call_n != bundle_call_n:
        failures.append("CALL differs\n        leaf   %s\n        clause %s"
                        % (leaf_call_n, bundle_call_n))
    if leaf_post_n != bundle_post_n:
        failures.append("CONCLUSION differs\n        leaf   %s\n        clause %s"
                        % (leaf_post_n, bundle_post_n))

    report.append("      %d hypothes%s compared, %d difference(s)"
                  % (len(leaf_norm), "is" if len(leaf_norm) == 1 else "es",
                     len(failures)))
    if dropped:
        report.append("      not carried by the bundle, by design: %s"
                      % "; ".join(dropped))
    return failures


def check_bridges(spec, translation_dir, errors):
    for bridge in spec.bridges:
        path = os.path.join(translation_dir, bridge.lemma_file)
        if not os.path.exists(path):
            errors.append("%s: bridge `%s` names %s, which is not there"
                          % (spec.name, bridge.canon, bridge.lemma_file))
            continue
        with open(path, encoding="utf-8") as fh:
            source = fh.read()
        m = re.search(
            r"^(private\s+)?(theorem|def|structure|abbrev)\s+%s\b(?P<sig>.*?)"
            r"(?=:=|\Z)" % re.escape(bridge.lemma), source, re.M | re.S)
        if not m:
            errors.append(
                "%s: the bridge that lets `%s` be compared is anchored to "
                "`%s` in %s, and there is no such declaration any more -- the "
                "bridge cannot be trusted until this is resolved"
                % (spec.name, bridge.canon, bridge.lemma, bridge.lemma_file))
            continue
        if not bridge.anchor_states:
            continue
        # The anchor exists. For a constant bridge it must also *say* what the
        # bridge claims: a lemma with the right name and a statement that
        # mentions only one of the two spellings, or neither, justifies
        # nothing. Without this the name alone is the guard, and a lemma
        # rewritten to `True` would pass.
        sig = m.group("sig")
        missing = [side for side, pat in (("leaf", bridge.leaf),
                                          ("bundle", bridge.bundle))
                   if not re.search(pat, sig)]
        if missing:
            errors.append(
                "%s: the bridge that lets `%s` be compared is anchored to "
                "`%s` in %s, and that declaration's statement does not mention "
                "the %s spelling. An anchor has to state the equality it "
                "stands for; matching its name alone would let a lemma "
                "reworded to say nothing keep the bridge alive"
                % (spec.name, bridge.canon, bridge.lemma, bridge.lemma_file,
                   " or the ".join(missing)))


def check_bundle(spec, translation_dir, out, need_convention):
    errors = []
    check_bridges(spec, translation_dir, errors)

    bundle_path = os.path.join(translation_dir, BUNDLE_FILE)
    if not os.path.exists(bundle_path):
        return ["%s: %s is not there" % (spec.name, BUNDLE_FILE)]
    header, body = read_def_body(bundle_path, spec.name)
    if header is None:
        return ["%s: no `def %s` in %s" % (spec.name, spec.name, BUNDLE_FILE)]

    leaf_path = os.path.join(translation_dir, spec.leaf_file)
    if not os.path.exists(leaf_path):
        return ["%s: the leaf file %s is not there" % (spec.name, spec.leaf_file)]

    try:
        clauses = split_clauses(body)
    except Unanalysable as exc:
        return ["%s: %s" % (spec.name, exc)]
    out.append("  %s (%d clause(s), against %s)"
               % (spec.name, len(clauses), spec.leaf_file))
    out.append("    compared across these declared equivalences:")
    for bridge in spec.bridges:
        out.append("      %s -- %s" % (bridge.lemma, bridge.note))
    mirrored = set()
    for lineno, marker, text in clauses:
        where = "%s:%s" % (BUNDLE_FILE, lineno)
        if marker is None:
            errors.append(
                "%s: the clause at %s carries no `-- mirrors:` comment, so "
                "there is nothing to compare it against." % (spec.name, where))
            need_convention.append(True)
            continue
        _, note = marker
        if MIRRORS_NONE_RE.match(note):
            if note.strip() == "nothing":
                errors.append(
                    "%s: the clause at %s says `mirrors: nothing` without "
                    "saying why. Write `-- mirrors: nothing -- <reason>`; a "
                    "clause assumed here for the first time has to say so."
                    % (spec.name, where))
                continue
            out.append("    %s  assumed here, no leaf theorem (%s)"
                       % (where, note[len("nothing"):].lstrip(" -")))
            continue
        m = MIRRORS_THM_RE.match(note)
        if not m:
            errors.append(
                "%s: the clause at %s has an unreadable marker `mirrors: %s`."
                % (spec.name, where, note))
            need_convention.append(True)
            continue
        qualified, filename = m.group(1), m.group(2)
        if filename != spec.leaf_file:
            errors.append("%s: the clause at %s names %s; this bundle mirrors "
                          "%s" % (spec.name, where, filename, spec.leaf_file))
            continue
        if not qualified.startswith(spec.leaf_namespace + "."):
            errors.append("%s: the clause at %s names `%s`, which is not in "
                          "namespace `%s`"
                          % (spec.name, where, qualified, spec.leaf_namespace))
            continue
        short = qualified[len(spec.leaf_namespace) + 1:]
        mirrored.add(short)
        out.append("    %s  mirrors %s" % (where, qualified))
        try:
            failures = compare_clause(spec, text, short, leaf_path, out)
        except Unanalysable as exc:
            errors.append("%s: the clause at %s mirrors `%s` and %s"
                          % (spec.name, where, qualified, exc))
            continue
        for failure in failures:
            errors.append("%s: the clause at %s has drifted from `%s`.\n      %s"
                          % (spec.name, where, qualified, failure))

    for required in spec.requires:
        if required not in mirrored:
            errors.append(
                "%s: no clause mirrors `%s.%s`, and the bundle is declared to "
                "restate it. Either a clause was dropped or its marker was."
                % (spec.name, spec.leaf_namespace, required))
    return errors


LIMITS = """
What this check does not see, stated so it is not mistaken for more:
  * where a bridge is anchored to a *transport* -- a `def`, or the refinement
    `structure` -- this checks only that the declaration is still there. Such
    an anchor states no equality, so there is nothing to read. Four of the
    sparse ratchet's five bridges are of that kind, and their notes say so.
    A bridge between two names for one constant is anchored to a lemma that
    does state the equality, and for those three the lemma's statement is read
    and must mention both spellings, so an anchor reworded to say nothing
    fails here rather than passing on its name;
  * a clause marked `mirrors: nothing` is taken at its word;
  * the crate-boundary assumptions listed above as not carried are dropped by
    an explicit list, and whether dropping them is still sound is a judgement
    no text check can make;
  * it compares statements, not proofs.
It never skips: anything it cannot normalise is reported as a failure.
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    here = os.path.dirname(os.path.abspath(__file__))
    default = os.path.join(os.path.dirname(here), "tacenta-proofs",
                           "translation", "Translation")
    parser.add_argument("--translation-dir", default=default,
                        help="directory holding TripleT3.lean and the leaf files")
    args = parser.parse_args()

    out, errors, need_convention = [], [], []
    for spec in BUNDLES:
        errors.extend(check_bundle(spec, args.translation_dir, out,
                                   need_convention))

    for line in out:
        print(line)
    if errors:
        print("")
        for error in errors:
            print("  FAIL  %s" % error, file=sys.stderr)
        if need_convention:
            print("\n  This check needs %s" % CONVENTION, file=sys.stderr)
        print("\ncheck-bundle-drift: %d problem(s); the bundles in %s cannot be "
              "shown to restate their leaf theorems."
              % (len(errors), BUNDLE_FILE), file=sys.stderr)
        return 1
    print(LIMITS.rstrip())
    print("check-bundle-drift: every mirrored clause matches its leaf theorem.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
