#!/usr/bin/env python3
"""Check a lifecycle proof module for the findings fresh reviews kept making, before it is handed over.

    python3 tooling/check-proof-module-preflight.py <UnitLifecycleModule>... [--strict] [--base REF]
    python3 tooling/check-proof-module-preflight.py --all [--baseline FILE] [--strict]

For each module `tacenta-proofs/translation/Translation/<Module>.lean`, its section of `tacenta-proofs/CLAIMS.md`
(the `## Proved` section whose `Location:` line names the module) and the negatives scripts that name it
(`tacenta-proofs/scripts/check-*-negatives.py`); a module with no such section, or no such script, is an error,
since the checks below would then have nothing to read:

  (a) not-shown      every item of the section's not-shown list (the paragraph that begins **Not shown**,
                     **Not shown here** or **What it does not show**, split at `;`) has its words in the
                     module docstring's `## What it does not show` list. A heuristic (an item counts as present
                     when most of its content words are), so a miss is a WARNING; `--strict` makes it an error.
  (b) mechanism      each negatives script has the names and call sites of the hardened mechanism, read from its
                     syntax tree (it is not run, so this is a structural check, not a test of what the script does:
                     a stub that defines the names and calls them only in dead code passes it):
                     the `COMPOSING`, `INSIDE`, `PROJECTED` and `STATEMENT_SHAPE` labels and a `check_labels` that
                     reads them and raises; `guard_self_test()` and `check_labels()` called as statements of `main`
                     before Lean runs; a not-a-refusal guard holding `unknown identifier` and `unknown constant` and
                     matched through `.lower()`, called by `check_refused` and by the self-test, whose samples hold
                     `Unknown identifier`, the kernel's `unknown constant` and a heartbeat timeout; a non-empty
                     `TIMEOUT` read by `is_timeout`; the two baselines (`module`, `pinned`); and the `sorry` probe
                     (`gutted`, `check_inside`, checking `declaration uses \`sorry\``) called from `main`. An error.
  (c) counts         the numbers the prose gives match what they count: in the section, "each of the N results"
                     (the module's axiom pins), "each of the N definitions" (its `#print` pins), "of the other N
                     results, A rest on ... alone ... and B on" (the pins other than the results the section's
                     **Compiler trust and pins.** paragraph names before its verb; then kernel only and opaque among
                     them, A + B = N, none of them compiler-trusted, every named result pinned and of the trust the
                     paragraph's first sentence gives it; with no such names, the pins `attest.py` labels other
                     than compiler trust), and "plants N faults" or "N changes refused" (the script's
                     controls); in the script's own docstring, "N controls are labelled inside" and "N ...
                     statement-shape"; in `ASSURANCE-OBLIGATIONS.md`, the script's "(two unmodified copies
                     accepted and N changes refused". An error.
  (d) text           no `SCAFFOLD-TODO:` marker left in any tracked file, and no plan identifier, path into the
                     planning directory or attribution line in the module's prose, its scripts' docstrings and its
                     section. With `--base REF`, also in every line added since REF (where a plan identifier is a
                     warning, since in other files the same letters name other things) and in the messages of the
                     commits since REF. An error.
  (e) private terms  only when the environment names a list: `TACENTA_PRIVATE_TERMS_FILE` is the path of a file
                     outside the tree with one term per line (`#` starts a comment). The same places as (d) are
                     searched for each term, with hyphens, underscores, dots, slashes and white space all taken as one
                     separator, and again with every separator removed from both. The list is never in the tree;
                     without it this part says it was skipped, and CI does not set it. A finding names the list's
                     line, not the term. An error. It is a convenience, not a guarantee: it reads only the places
                     above, and an encoded or reworded term passes; the check made before publishing is the safety
                     net.

`--all` checks every `UnitLifecycle*.lean` module. `--baseline FILE` reads the finding keys known when the check
was introduced (`findings`): those are reported as known and do not fail. A count finding's key carries the
number said and the number found, so a baselined count is known only at that value. With `--all`, a listed key
that no longer occurs is reported as a stale key to delete (an error with `--strict` or `--baseline-base`).
`--baseline-base REF` compares the baseline with the one at REF: a key added since REF fails unless it occurs now
and the file's `reasons` gives it a reason of at least 40 characters and six different words (not a
placeholder), so the list does not grow unseen; a new finding is fixed rather than listed, and a reasoned key is a
reviewed exception. A REF that is empty or does not resolve to a commit is an error; a base with no baseline file
(the commit that introduces it) is only noted. Warnings never
fail the run, which is how CI runs it (`--all --baseline-base origin/main`, step `checks_42`): errors only.
Exit 0 when no error is left, 1 otherwise.

Test seam: with `PREFLIGHT_SEAM=tests-only`, `PREFLIGHT_PLAN_ID=<regex>` adds a plan-identifier pattern and
`PREFLIGHT_PRIVATE_PATH=<prefix>` a private path prefix, for the controls to plant faults that spell nothing real.
Each only adds to what is refused.

What it does not do: judge the prose. A not-shown item reworded beyond recognition is a warning, and a count the
patterns above do not match is not checked.
"""
import argparse
import ast
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TRANSLATION = ROOT / "tacenta-proofs" / "translation" / "Translation"
SCRIPTS = ROOT / "tacenta-proofs" / "scripts"
CLAIMS = ROOT / "tacenta-proofs" / "CLAIMS.md"
OBLIGATIONS = ROOT / "ASSURANCE-OBLIGATIONS.md"
TODO = "SCAFFOLD-" + "TODO"
MARK = TODO + ":"  # what the scaffold writes; a mention of the word in prose is not a marker
TODO_HOMES = {"tacenta-proofs/scripts/new-lifecycle-module.py", "tooling/check-proof-module-preflight.py",
              "tacenta-proofs/scripts/templates/lifecycle-module.lean.in",
              "tacenta-proofs/scripts/templates/lifecycle-negatives.py.in",
              "tooling/tests/run-new-lifecycle-module-cases.sh",
              "tooling/tests/run-check-proof-module-preflight-cases.sh"}

# A plan identifier, alone or joined to others by hyphens; a gap identifier that holds one between words, or
# the end-to-end gap identifiers, are not one.
PLAN_PARTS = [r"O(?:1[0-6]|[1-9])", r"R[1-3]", r"E[12]", r"S[1-4]"]
TOKEN = re.compile(r"(?<![\w.])[A-Za-z0-9]+(?:-[A-Za-z0-9]+)*(?![\w])")
PATH_PREFIXES = ["planning/"]
ATTRIBUTION = re.compile(r"(?im)^\s*co-authored-by:|generated with \[|\U0001F916")
TERMS_VARIABLE = "TACENTA_PRIVATE_TERMS_FILE"
WORD = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
if os.environ.get("PREFLIGHT_SEAM") == "tests-only":
    PLAN_PARTS += [os.environ["PREFLIGHT_PLAN_ID"]] if os.environ.get("PREFLIGHT_PLAN_ID") else []
    PATH_PREFIXES += [os.environ["PREFLIGHT_PRIVATE_PATH"]] if os.environ.get("PREFLIGHT_PRIVATE_PATH") else []
elif os.environ.get("PREFLIGHT_PLAN_ID") or os.environ.get("PREFLIGHT_PRIVATE_PATH"):
    sys.exit("check-proof-module-preflight: PREFLIGHT_PLAN_ID and PREFLIGHT_PRIVATE_PATH are a test seam; they are "
             "read only with PREFLIGHT_SEAM=tests-only")
PLAN_PART = re.compile("|".join(f"(?:{p})" for p in PLAN_PARTS))
PRIVATE_PATH = re.compile(r"(?<![\w/])(?:" + "|".join(re.escape(p) for p in PATH_PREFIXES) + r")[\w./-]+")


def separated(text):
    """`text` in lower case with every run of characters other than letters and digits made one space."""
    return " " + re.sub(r"[^a-z0-9]+", " ", text.lower()).strip() + " "


def private_terms():
    """[(line number, term as `separated` gives it)] of the list the environment names, or None."""
    path = os.environ.get(TERMS_VARIABLE)
    if not path:
        return None
    out = []
    for number, line in enumerate(Path(path).read_text(encoding="utf-8").split("\n"), 1):
        if line.strip() and not line.lstrip().startswith("#"):
            out.append((number, separated(line)))
    return out


TERMS = None  # read in main


NUMBERS = {w: n for n, w in enumerate(
    "zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen sixteen "
    "seventeen eighteen nineteen".split())}
TENS = {"twenty": 20, "thirty": 30, "forty": 40, "fifty": 50, "sixty": 60, "seventy": 70, "eighty": 80,
        "ninety": 90}
NUMBER = r"(\d+|(?:twenty|thirty|forty|fifty|sixty|seventy|eighty|ninety)(?:-[a-z]+)?|[a-z]+teen|zero|one|two|three|four|five|six|seven|eight|nine|ten|eleven|twelve)"


def number(text):
    text = text.lower()
    if text.isdigit():
        return int(text)
    if text in NUMBERS:
        return NUMBERS[text]
    head, _, tail = text.partition("-")
    if head in TENS and (not tail or tail in NUMBERS):
        return TENS[head] + (NUMBERS[tail] if tail else 0)
    return None


class Report:
    def __init__(self):
        self.items = []  # (level, key, message)

    def add(self, level, key, message):
        self.items.append((level, key, message))


def load_attest():
    spec = importlib.util.spec_from_file_location("attest_for_preflight", SCRIPTS / "attest.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def tracked():
    out = subprocess.run(["git", "ls-files"], cwd=ROOT, capture_output=True, text=True, check=True).stdout
    return [line for line in out.split("\n") if line]


# ---- reading the module, its section and its scripts ---------------------------------------------------

def docstring_section(text, heading):
    """The text of the `## <heading>` part of the module's first `/-! ... -/` block."""
    m = re.search(r"/-!(.*?)-/", text, re.S)
    if not m:
        return None
    doc = m.group(1)
    h = re.search(rf"^## {re.escape(heading)}\s*$", doc, re.M | re.I)
    if not h:
        return None
    rest = doc[h.end():]
    nxt = re.search(r"^## ", rest, re.M)
    return rest[:nxt.start()] if nxt else rest


def claims_section(module):
    text = CLAIMS.read_text(encoding="utf-8")
    sections = [(m.start(), m.group(1)) for m in re.finditer(r"^## (.+)$", text, re.M)] + [(len(text), None)]
    found = []
    for (start, title), (end, _) in zip(sections, sections[1:]):
        body = text[start:end]
        loc = re.search(r"Location:(.+?)(?:\n\n|\n-)", body, re.S)
        if title.lower().startswith("proved") and loc and f"Translation/{module}.lean" in loc.group(1):
            found.append((title, body))
    return found


def location_modules(body):
    """The translation modules a section's `Location:` line names."""
    loc = re.search(r"Location:(.+?)(?:\n\n|\n-)", body, re.S)
    return re.findall(r"Translation/(\w+)\.lean", loc.group(1)) if loc else []


NOT_SHOWN_LEAD = re.compile(r"\*\*(?:Not shown(?: here)?[:.]|What it does not show[.:]|What is not shown[.:])\*\*")


def not_shown_items(body):
    m = NOT_SHOWN_LEAD.search(body)
    if not m:
        return None
    rest = body[m.end():]
    end = re.search(r"\n\n", rest)
    paragraph = rest[:end.start()] if end else rest
    # The paragraph's first sentence after the lead that is not the list: stop at a sentence that begins a new
    # topic (`The reach ...`) is not attempted; the items are what `;` separates up to the paragraph's end.
    flat = re.sub(r"\([^()]*\)", " ", re.sub(r"\([^()]*\)", " ", paragraph))
    return [i.strip() for i in re.split(r";", flat) if i.strip()]


STOP = set("""a an the and or of to in on at by for from with without its it is are be not that this these those
as any which what when whose than then there their them they his her our we you all each every other one two
first last both either no nor shown show shows here above below section next previous so also only does do is
was were been being has have had can may must would should such same into onto over under about between per""".split())


def content_words(text):
    return {w for w in WORD.findall(text.lower().replace("`", " ")) if w not in STOP and len(w) > 2}


def negatives_scripts(module):
    out = []
    for path in sorted(SCRIPTS.glob("check-*-negatives.py")):
        if f"Translation/{module}.lean" in path.read_text(encoding="utf-8"):
            out.append(path)
    return out


# ---- (a) ------------------------------------------------------------------------------------------------

def check_not_shown(report, module, text, sections, strict):
    for title, body in sections:
        if title in check_not_shown.done:
            continue
        check_not_shown.done.add(title)
        # A section over several modules is held to the union of their lists.
        docs = []
        for name in location_modules(body) or [module]:
            path = TRANSLATION / f"{name}.lean"
            if path.exists():
                doc = docstring_section(path.read_text(encoding="utf-8"), "What it does not show")
                if doc is not None:
                    docs.append(doc)
        items = not_shown_items(body)
        if items is None or not docs:
            continue
        module = "+".join(location_modules(body)) or module
        have = content_words("\n".join(docs))
        for item in items:
            words = content_words(item)
            if len(words) < 2:
                continue
            present = len(words & have) / len(words)
            if present < 0.5:
                short = " ".join(item.split())[:90]
                key = f"{module}|not-shown|{hashlib.sha256(' '.join(sorted(words)).encode()).hexdigest()[:12]}"
                report.add("error" if strict else "warning", key,
                           f"{module}: CLAIMS.md lists as not shown \"{short}\", and the module docstring's "
                           f"`What it does not show` list does not ({len(words & have)} of {len(words)} words)")


# ---- (b) ------------------------------------------------------------------------------------------------

def assigned(tree):
    out = {}
    for node in tree.body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    out[target.id] = node.value
    return out


def strings(node):
    return [n.value for n in ast.walk(node) if isinstance(n, ast.Constant) and isinstance(n.value, str)]


def called(node):
    """The names `node` calls (a plain name or the last part of an attribute), with the line of each call."""
    out = []
    for n in ast.walk(node):
        if isinstance(n, ast.Call):
            if isinstance(n.func, ast.Name):
                out.append((n.func.id, n.lineno))
            elif isinstance(n.func, ast.Attribute):
                out.append((n.func.attr, n.lineno))
    return out


def names(node):
    return {n.id for n in ast.walk(node) if isinstance(n, ast.Name)}


def check_mechanism(report, path):
    """The names and call sites of the hardened mechanism; each missing one is a short code in the finding."""
    rel = path.relative_to(ROOT)
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"))
    except SyntaxError as error:
        report.add("error", f"{path.name}|mechanism|syntax", f"{rel}: does not parse: {error}")
        return None
    values = assigned(tree)
    functions = {n.name: n for n in tree.body if isinstance(n, ast.FunctionDef)}
    missing = []  # (code, what)

    def need(ok, code, what):
        if not ok:
            missing.append((code, what))

    for name in ("COMPOSING", "INSIDE", "PROJECTED", "STATEMENT_SHAPE", "NOT_A_REFUSAL", "TIMEOUT"):
        need(name in values, name, f"the `{name}` assignment")
    guard = set(strings(values["NOT_A_REFUSAL"])) if "NOT_A_REFUSAL" in values else set()
    need("unknown identifier" in guard, "guard-identifier", "`unknown identifier` in NOT_A_REFUSAL")
    need("unknown constant" in guard, "guard-constant", "`unknown constant` in NOT_A_REFUSAL")
    timeout = values.get("TIMEOUT")
    need(isinstance(timeout, (ast.Tuple, ast.List)) and len(timeout.elts) > 0, "timeout-list",
         "a non-empty `TIMEOUT`")
    for name in ("check_labels", "guard_self_test", "not_a_refusal", "is_timeout", "gutted", "check_inside",
                 "check_refused", "main"):
        need(name in functions, f"fn-{name}", f"the function `{name}`")
    fn = functions.get
    if fn("check_labels"):
        need({"INSIDE", "STATEMENT_SHAPE", "COMPOSING", "PROJECTED"} <= names(fn("check_labels"))
             and any(isinstance(n, ast.Raise) for n in ast.walk(fn("check_labels"))),
             "labels-read", "a `check_labels` that reads the four labels and raises")
    if fn("not_a_refusal"):
        need(any(c == "lower" for c, _ in called(fn("not_a_refusal"))), "lower",
             "the guard matched in lower case (`.lower()` called in `not_a_refusal`)")
    if fn("is_timeout"):
        need("TIMEOUT" in names(fn("is_timeout")), "timeout-read", "`TIMEOUT` read by `is_timeout`")
    if fn("check_refused"):
        need({"not_a_refusal", "is_timeout"} <= {c for c, _ in called(fn("check_refused"))}, "refused-calls",
             "`check_refused` calling `not_a_refusal` and `is_timeout`")
    if fn("guard_self_test"):
        test = fn("guard_self_test")
        calls = [c for c, _ in called(test)]
        need(calls.count("not_a_refusal") >= 3 and "is_timeout" in calls and "error_blocks" in calls,
             "self-test-calls", "a self-test that calls the guard, `error_blocks` and `is_timeout`")
        samples = " ".join(strings(test))
        for needed, code, what in (("Unknown identifier", "sample-identifier", "the toolchain's `Unknown identifier`"),
                                   ("(kernel) unknown constant", "sample-constant", "the kernel's `unknown constant`"),
                                   ("(deterministic) timeout", "sample-timeout", "a heartbeat timeout")):
            need(needed in samples, code, f"a start-up sample of {what}")
    if fn("check_inside"):
        need("declaration uses `sorry`" in " ".join(strings(fn("check_inside"))), "sorry-probe",
             "the sorry probe's check that the emptied copy elaborated to `sorry`")
    main = fn("main")
    if main:
        top = [(s.value.func.id, s.lineno) for s in main.body if isinstance(s, ast.Expr)
               and isinstance(s.value, ast.Call) and isinstance(s.value.func, ast.Name)]
        first_run = min([line for c, line in called(main) if c in ("run_lean", "parse_args")] or [10 ** 9])
        startup = {c for c, line in top if line < first_run}
        need({"guard_self_test", "check_labels"} <= startup, "startup",
             "`guard_self_test()` and `check_labels()` called as statements of `main` before Lean runs")
        keys = {k.value for n in ast.walk(main) if isinstance(n, ast.Dict) for k in n.keys
                if isinstance(k, ast.Constant)}
        need({"module", "pinned"} <= keys, "baselines", "the two baselines (`module` and `pinned`)")
        need({"INSIDE", "STATEMENT_SHAPE"} <= names(main), "runtime-labels", "the run-time check of the labels")
        need({"gutted", "check_inside", "check_refused"} <= {c for c, _ in called(main)}, "probe-calls",
             "`main` calling `check_refused`, `gutted` and `check_inside`")
    if missing:
        codes = ",".join(sorted(code for code, _ in missing))
        report.add("error", f"{path.name}|mechanism|{codes}",
                   f"{rel}: lacks the hardened mechanism (a structural check of names and call sites; it does not "
                   "show the script works): " + "; ".join(w for _, w in missing))
    return values


# ---- (c) ------------------------------------------------------------------------------------------------

def pins_of(text, attest):
    cut = text.find("\n/-! ## Pins")
    pins = text[cut:] if cut >= 0 else ""
    if not pins:
        return None
    externals = attest.opaque_externals()
    trust = [attest.classify([x.strip() for x in m.group("axioms").split(",") if x.strip()], externals)
             for m in attest.AXIOM_PIN.finditer(pins)]
    printed = len(re.findall(r"#guard_msgs in\n#print (?!axioms )\S+\n", pins))
    return {"axiom": len(trust), "print": printed, "kernel": trust.count("kernel"),
            "opaque": trust.count("opaque-external"), "compiler": trust.count("compiler")}


def pin_trust(text, attest):
    """[(name, trust)] of a module's axiom pins, trust as `attest.classify` gives it."""
    cut = text.find("\n/-! ## Pins")
    if cut < 0:
        return []
    externals = attest.opaque_externals()
    return [(m.group("name"), attest.classify([x.strip() for x in m.group("axioms").split(",") if x.strip()],
                                              externals))
            for m in attest.AXIOM_PIN.finditer(text[cut:])]


NAMED_FIRST = re.compile(r"\*\*Compiler trust and pins\.\*\*\s+((?:`[^`]+`(?:,\s+|\s+and\s+))*`[^`]+`)\s+"
                         r"(?:apply|applies|list|lists|rest|rests)\b")


def pin_names(pin, name):
    """Whether the pinned constant `pin` (a full name) is the result `name` (a full name, or its last parts)."""
    return pin == name or pin.endswith("." + name)


TRUST_WORDS = {"kernel": "the kernel's axioms alone", "opaque-external": "opaque constants",
               "compiler": "a compiler-trust axiom"}


def other_results(report, module, where, flat, body, attest):
    """The trust of each result the section's "Of the other N results" counts, or None.

    The results counted are the pins of the section's modules other than the ones its **Compiler trust and pins.**
    paragraph names before its verb. Until 2026-10-21 those were the compiler-trusted results; since the
    `native_decide` constants became kernel proofs they are named results with no compiler trust, so the
    exclusion is by name, and what the old rule implied is checked here instead: a named result with no pin is
    an error (by full name or by its last parts after a dot, never by a substring); every named result has the
    trust the paragraph's first sentence gives it (none of them compiler-trusted where it says "no
    compiler-trust axiom", each on opaque constants where it says they list opaque constants); and no result
    among the others is compiler-trusted, since the sentence counts them as resting on the kernel's axioms or on
    opaque constants. With no names before the verb, None (the count is of the results other than the
    compiler-trusted).
    """
    lead = NAMED_FIRST.search(flat)
    if not lead:
        return None
    named = re.findall(r"`([^`]+)`", lead.group(1))
    trust = []
    for name in location_modules(body):
        path = TRANSLATION / f"{name}.lean"
        if path.exists():
            trust += pin_trust(path.read_text(encoding="utf-8"), attest)
    rest = flat[lead.end():]
    end = re.search(r"\. (?=[A-Z])", rest)
    clause = rest[:end.start()] if end else rest
    no_compiler = "no compiler-trust axiom" in clause
    on_opaque = re.search(r"\bopaque constants\b", clause) is not None
    for n in named:
        pins = [t for pin, t in trust if pin_names(pin, n)]
        if not pins:
            report.add("error", f"{module}|count|named-unpinned|{n}",
                       f"{where}: names `{n}` first, which has no pin in the section's modules")
            continue
        for t in pins:
            if no_compiler and t == "compiler":
                report.add("error", f"{module}|count|named-trust|{n}",
                           f"{where}: names `{n}` first as listing no compiler-trust axiom; its pin lists one")
            elif on_opaque and t != "opaque-external":
                report.add("error", f"{module}|count|named-trust|{n}",
                           f"{where}: names `{n}` first as resting on opaque constants; its pin rests on "
                           f"{TRUST_WORDS[t]}")
    other = [(pin, t) for pin, t in trust if not any(pin_names(pin, n) for n in named)]
    for pin, t in other:
        if t == "compiler":
            report.add("error", f"{module}|count|other-compiler|{pin.split('.')[-1]}",
                       f"{where}: `{pin.split('.')[-1]}` is compiler-trusted, and is not among the results named "
                       f"first, so the other results' count does not state it")
    return [t for _, t in other]


def controls_of(values):
    if values and isinstance(values.get("MUTANTS"), ast.List):
        return len(values["MUTANTS"].elts)
    return None


def count_mismatch(report, key, where, what, said, actual):
    # The key carries both numbers, so a baselined count is known only at the value it was baselined at.
    if said is not None and actual is not None and said != actual:
        report.add("error", f"{key}|{said}|{actual}", f"{where}: says {said} {what}; there are {actual}")


PLACEHOLDER = re.compile(r"(?i)\W*(?:x+|todo|tbd|fixme|reason|n/?a|none|placeholder|ok|fine|known|\.+)\W*")


def trivial_reason(reason):
    """Whether a baseline reason is too short or too empty to be reviewed: under 40 characters, fewer than six
    different words of two letters or more, or a placeholder."""
    text = str(reason or "").strip()
    words = {w.lower() for w in re.findall(r"[A-Za-z]{2,}", text)}
    return len(text) < 40 or len(words) < 6 or PLACEHOLDER.fullmatch(text) is not None


def section_pins(body, attest):
    """The pin counts of every module the section's `Location:` line names, added up."""
    total = None
    for name in location_modules(body):
        path = TRANSLATION / f"{name}.lean"
        if not path.exists():
            continue
        pins = pins_of(path.read_text(encoding="utf-8"), attest)
        if pins:
            total = pins if total is None else {k: total[k] + pins[k] for k in total}
    return total


def single_module(path):
    """Whether a negatives script holds one module (a script over several plants per-module faults)."""
    return len(set(re.findall(r"translation/Translation/(\w+)\.lean", path.read_text(encoding="utf-8")))) == 1


def check_counts(report, module, text, sections, scripts, attest):
    script_values = {p: check_mechanism.cache.get(p) for p in scripts}
    for title, body in sections:
        if title in check_counts.done:
            continue
        check_counts.done.add(title)
        pins = section_pins(body, attest)
        module = "+".join(location_modules(body)) or module
        where = f"CLAIMS.md section `{title[:70]}`"
        flat = " ".join(body.split())
        if pins:
            for m in re.finditer(rf"[Ee]ach of the {NUMBER} results carries an axiom pin", flat):
                count_mismatch(report, f"{module}|count|results", where, "results with an axiom pin",
                               number(m.group(1)), pins["axiom"])
            for m in re.finditer(rf"each of the {NUMBER} definitions", flat):
                count_mismatch(report, f"{module}|count|definitions", where, "definitions with a `#print` pin",
                               number(m.group(1)), pins["print"])
            for m in re.finditer(rf"Of the other {NUMBER} results, {NUMBER} rest(?:s)? on `propext`, "
                                 rf"`Classical\.choice` and `Quot\.sound` alone(?:[^.]*?)and {NUMBER} on", flat):
                other = other_results(report, module, where, flat, body, attest)
                if other is None:
                    what, total = "results other than the compiler-trusted", pins["kernel"] + pins["opaque"]
                    kernel, opaque = pins["kernel"], pins["opaque"]
                else:
                    what, total = "results other than the ones named first", len(other)
                    kernel, opaque = other.count("kernel"), other.count("opaque-external")
                    said = [number(m.group(i)) for i in (1, 2, 3)]
                    if None not in said and said[0] != said[1] + said[2]:
                        report.add("error", f"{module}|count|sum|{said[0]}|{said[1]}|{said[2]}",
                                   f"{where}: says {said[1]} and {said[2]} of the other {said[0]} results, which "
                                   f"do not add up")
                count_mismatch(report, f"{module}|count|other", where, what, number(m.group(1)), total)
                count_mismatch(report, f"{module}|count|kernel", where, "results on the kernel's axioms alone",
                               number(m.group(2)), kernel)
                count_mismatch(report, f"{module}|count|opaque", where, "results on opaque constants",
                               number(m.group(3)), opaque)
        for path in scripts:
            if not single_module(path):
                continue
            n = controls_of(script_values[path])
            name = re.escape(path.name)
            for m in re.finditer(rf"`{name}` plants {NUMBER}(?: \w+)? faults", flat):
                count_mismatch(report, f"{module}|count|faults|{path.name}", where, f"faults planted by {path.name}",
                               number(m.group(1)), n)
    for path in scripts:
        values = script_values[path]
        n = controls_of(values)
        doc = ""
        try:
            doc = ast.get_docstring(ast.parse(path.read_text(encoding="utf-8"))) or ""
        except SyntaxError:
            pass
        flat = " ".join(doc.split())
        if values is not None:
            for label, pattern in (("INSIDE", rf"\b{NUMBER} controls are labelled inside"),
                                   ("STATEMENT_SHAPE", rf"\b{NUMBER} (?:is|are) (?:a )?statement-shape check")):
                node = values.get(label)
                actual = len(node.keys) if isinstance(node, ast.Dict) else None
                for m in re.finditer(pattern, flat, re.I):
                    count_mismatch(report, f"{path.name}|count|{label}", f"{path.relative_to(ROOT)} docstring",
                                   f"controls labelled {label}", number(m.group(1)), actual)
        if not single_module(path):
            continue
        obligations = " ".join(OBLIGATIONS.read_text(encoding="utf-8").split())
        for m in re.finditer(rf"`{re.escape(path.name)}` \({NUMBER} unmodified (?:copies|inputs|proofs?) accepted "
                             rf"and {NUMBER} changes refused", obligations):
            count_mismatch(report, f"{path.name}|count|obligations", "ASSURANCE-OBLIGATIONS.md",
                           f"changes refused by {path.name}", number(m.group(2)), n)


check_mechanism.cache = {}
check_not_shown.done = set()
check_counts.done = set()


# ---- (d) ------------------------------------------------------------------------------------------------

def a(kind):
    return ("an " if kind[0] in "aeiou" else "a ") + kind


def forbidden_in(text):
    """[(kind, detail)] of what `text` holds that the repository keeps out of its text."""
    found = []
    for m in TOKEN.finditer(text):
        if all(PLAN_PART.fullmatch(part) for part in m.group(0).split("-")):
            found.append(("plan identifier", m.group(0)))
    for m in PRIVATE_PATH.finditer(text):
        found.append(("private path", m.group(0).split("/")[0] + "/..."))
    if ATTRIBUTION.search(text):
        found.append(("attribution", "an attribution line"))
    if TERMS:
        flat = separated(text)
        joined = flat.replace(" ", "")
        for number, term in TERMS:
            # Separated, and also with every separator removed from both, which catches a term written as one
            # word or split inside a word (at the price of matching across word boundaries).
            if term in flat or term.replace(" ", "") in joined:
                found.append(("private term", f"line {number} of the list"))
    return sorted(set(found))


def prose_of_lean(text):
    """The comments and docstrings of a Lean file, where prose is written."""
    parts = re.findall(r"/-.*?-/", text, re.S) + re.findall(r"--[^\n]*", text)
    return "\n".join(parts)


def check_terms(report, module, text, sections, scripts):
    pieces = [(f"{module}.lean", prose_of_lean(text))]
    pieces += [(p.name, ast.get_docstring(ast.parse(p.read_text(encoding="utf-8"))) or "") for p in scripts]
    pieces += [(f"the CLAIMS.md section of {module}", body) for _, body in sections]
    for where, piece in pieces:
        for kind, detail in forbidden_in(piece):
            # A private term's key does not depend on where the term sits in the local list.
            report.add("error", f"{module}|terms|{where}|{kind}" + ("" if kind == "private term" else f"|{detail}"),
                       f"{where}: holds {a(kind)} the repository keeps out of its text ({detail})")


def check_todo(report, files):
    for rel in files:
        if rel in TODO_HOMES:
            continue
        path = ROOT / rel
        try:
            text = path.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        if MARK in text:
            report.add("error", f"todo|{rel}", f"{rel}: holds {text.count(MARK)} {TODO} marker(s) to replace")


def check_added(report, base):
    diff = subprocess.run(["git", "diff", "--no-ext-diff", "-U0", base, "--"], cwd=ROOT, capture_output=True,
                          text=True, check=True).stdout
    current = None
    added = {}
    for line in diff.split("\n"):
        if line.startswith("+++ b/"):
            current = line[6:]
        elif line.startswith("+") and not line.startswith("+++") and current:
            added.setdefault(current, []).append(line[1:])
    for rel, lines in added.items():
        if rel in TODO_HOMES or rel.startswith("tacenta-proofs/manifests/"):
            continue
        for kind, detail in forbidden_in("\n".join(lines)):
            # In any added line a plan identifier may be something else (a storage service, a mutation
            # identifier), so there it is a warning; in a module's own text, an error.
            level = "warning" if kind == "plan identifier" else "error"
            report.add(level, f"added|{rel}|{kind}|{detail}",
                       f"{rel}: a line added since {base} holds {a(kind)} the repository keeps out ({detail})")
    log = subprocess.run(["git", "log", "--format=%H%n%B%n--end--", f"{base}..HEAD"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout
    for chunk in log.split("--end--"):
        chunk = chunk.strip()
        if not chunk:
            continue
        sha, _, message = chunk.partition("\n")
        for kind, detail in forbidden_in(message):
            report.add("error", f"commit|{sha[:12]}|{kind}|{detail}",
                       f"commit {sha[:12]}: its message holds {a(kind)} the repository keeps out ({detail})")


# ---- running it --------------------------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("modules", nargs="*")
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--strict", action="store_true")
    parser.add_argument("--base")
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--baseline-base")
    args = parser.parse_args()
    global TERMS
    TERMS = private_terms()
    print("note     the mechanism check is structural: it reads names and call sites; a stub that defines them and "
          "calls them only in dead code passes it")
    if TERMS is None:
        print(f"note     private-term scan skipped: no list ({TERMS_VARIABLE} is not set)")
    if args.all == bool(args.modules):
        parser.error("name modules, or give --all")
    if args.baseline_base is not None and (not args.baseline_base.strip() or not args.baseline):
        parser.error("--baseline-base needs a non-empty REF and --baseline")
    modules = sorted(p.stem for p in TRANSLATION.glob("UnitLifecycle*.lean")) if args.all else args.modules
    attest = load_attest()
    report = Report()
    for module in modules:
        path = TRANSLATION / f"{module}.lean"
        if not path.exists():
            report.add("error", f"{module}|missing", f"{module}: no file {path.relative_to(ROOT)}")
            continue
        text = path.read_text(encoding="utf-8")
        sections = claims_section(module)
        scripts = negatives_scripts(module)
        # Without a section or a script, (a) to (c) have nothing to read: that is a finding, not a pass.
        if not sections:
            report.add("error", f"{module}|no-section",
                       f"{module}: no `## Proved` section of tacenta-proofs/CLAIMS.md names it in its `Location:` "
                       f"line, so its not-shown list and counts are not checked")
        if not scripts:
            report.add("error", f"{module}|no-negatives-script",
                       f"{module}: no tacenta-proofs/scripts/check-*-negatives.py names it, so no control's "
                       f"mechanism is checked")
        for script in scripts:
            if script not in check_mechanism.cache:
                check_mechanism.cache[script] = check_mechanism(report, script)
        check_not_shown(report, module, text, sections, args.strict)
        check_counts(report, module, text, sections, scripts, attest)
        check_terms(report, module, text, sections, scripts)
    check_todo(report, tracked())
    if args.base:
        check_added(report, args.base)
    seen, items = set(), []
    for level, key, message in report.items:
        if (key, message) not in seen:
            seen.add((key, message))
            items.append((level, key, message))
    known, reasons = set(), {}
    if args.baseline:
        document = json.loads(args.baseline.read_text(encoding="utf-8"))
        known, reasons = set(document["findings"]), document.get("reasons", {})
    errors = 0
    for level, key, message in items:
        if level == "error" and key in known:
            print(f"known    {message}")
        elif level == "error":
            print(f"ERROR    {message}  [{key}]")
            errors += 1
        else:
            print(f"warning  {message}")
    # A listed finding that no longer occurs is stale, which only a run over every module can tell.
    # A private-term key cannot be judged stale when the list was not read.
    stale = [k for k in sorted(known - {k for lvl, k, _ in items if lvl == "error"})
             if TERMS is not None or not k.endswith("|private term")] if args.all else []
    for key in stale:
        # With a base to compare with (as CI runs it), a key that no longer occurs must be deleted: the baseline
        # only shrinks.
        if args.strict or args.baseline_base:
            print(f"ERROR    stale key: delete it from {args.baseline}: {key}")
            errors += 1
        else:
            print(f"warning  stale key: delete it from {args.baseline}: {key}")
    if args.baseline and args.baseline_base:
        rel = str(args.baseline.resolve().relative_to(ROOT)) if args.baseline.resolve().is_relative_to(ROOT) \
            else str(args.baseline)
        resolves = subprocess.run(["git", "rev-parse", "--verify", "--quiet", f"{args.baseline_base}^{{commit}}"],
                                  cwd=ROOT, capture_output=True, text=True)
        old = subprocess.run(["git", "show", f"{args.baseline_base}:{rel}"], cwd=ROOT, capture_output=True, text=True)
        if resolves.returncode:
            # A base that does not resolve would let the baseline grow unseen: that is a failure, not a skip.
            print(f"ERROR    the base {args.baseline_base} does not resolve to a commit, so the baseline's growth "
                  f"cannot be checked: fetch it, or name another base")
            errors += 1
        elif old.returncode:
            print(f"note     no baseline at {args.baseline_base}; nothing to compare it with")
        else:
            # Once a base has a baseline, a key may be added only for a finding that occurs now, and only with a
            # reason a reviewer can read. (The commit that introduces the file is the one place keys come in
            # without one; each must still occur, or it is stale.)
            occurring = {k for lvl, k, _ in items if lvl == "error"}
            for key in sorted(known - set(json.loads(old.stdout)["findings"])):
                if key not in occurring and (TERMS is not None or not key.endswith("|private term")):
                    print(f"ERROR    the baseline gained {key} since {args.baseline_base}, which does not occur: "
                          f"a key is added only for a finding that occurs")
                    errors += 1
                elif trivial_reason(reasons.get(key)):
                    print(f"ERROR    the baseline gained {key} since {args.baseline_base} with no reason, or one too "
                          f"short to review (at least 40 characters and six different words): fix the finding, "
                          f"or give the key a reason under `reasons` for review")
                    errors += 1
                else:
                    print(f"note     the baseline gained {key} since {args.baseline_base}: {reasons[key]}")
    warnings = sum(1 for lvl, _, _ in items if lvl == "warning")
    print(f"proof-module-preflight: {len(modules)} module(s); {errors} error(s), "
          f"{sum(1 for lvl, k, _ in items if lvl == 'error' and k in known)} known, {warnings} warning(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
