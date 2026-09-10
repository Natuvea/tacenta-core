#!/usr/bin/env python3
"""Generate the verification and source-attestation manifests from the repository.

The attestation gate: the claims and the manifests must cover what actually
ships.

The rule this script exists to enforce: **nothing here is written by hand.**
Every field is read out of the repository, so the manifests cannot describe a
state the repository has left. Run with `--check` and it regenerates into memory
and fails if what is on disk differs, which is what CI runs.

## Where the axiom facts come from

Not from this script. `#print axioms` under `#guard_msgs` already pins them, and
the Lean build fails if a pin is wrong. So the docstrings this script parses are
build-verified before it reads them, and collecting them here adds no trust that
the build did not already establish. If a proof starts resting on something new,
the build breaks first and this never runs.

## The one manifest that is not regenerated on every run

`manifests/translation-attestation.json` records, for each generated
`Translation/Tacenta*.lean`, its SHA-256, the `axiom` names it declares, the
SHA-256 of the Rust verified zone it was generated from, and the SHA-256 of
the workspace inputs that shape what Charon extracts from every zone (the
workspace `Cargo.toml` and its profiles, `Cargo.lock`, `.cargo/`, and the
`kdf` and `kem` crates whose signatures become the opaque externals), with
the Aeneas pin. One zone is generated rather than written -- the three-leaf
translation unit `tacenta-core/triple-unit` -- and its record carries its
provenance as well as its bytes: the assembly script and all three leaf trees
it was assembled from, so that a leaf edited without re-assembling fails. It is written only by `--refresh-translation`, which is meant
to be run immediately after `scripts/run-aeneas.sh`, refuses a `Tacenta*.lean`
that `run-aeneas.sh` does not produce, and every other mode compares the
tree against it. That is what makes it provenance rather than self-description:
the other two manifests are recomputed from the tree they describe, so they can
only ever say the tree is consistent with itself; this one says the generated
files are the bytes somebody recorded after running the pinned toolchain, and
the Rust they were generated from is the Rust in the tree now. What it cannot
say is that the toolchain was run honestly, or run at all: a reader who wants
that runs `run-aeneas.sh` themselves and diffs, which `REPRODUCING.md` describes.

## What it deliberately does not claim

That the listed theorems are the *right* theorems, or that they add up to a
secure protocol. This records what was proved, on what, and against which
sources. `LIMITATIONS.md` is where what is not proved lives, and it is prose
because that part needs an argument rather than a field.
"""

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MANIFESTS = ROOT / "tacenta-proofs" / "manifests"
TRANSLATION_MANIFEST = MANIFESTS / "translation-attestation.json"
RUN_AENEAS = ROOT / "tacenta-proofs" / "scripts" / "run-aeneas.sh"

SCHEMA_VERSION = 1
# The translation attestation's own schema: 2 added `workspace_sha256` to every
# record, so a manifest without it is refused rather than read as complete;
# 3 added `assembly` to the records of zones that are generated rather than
# written, so a manifest without it cannot claim to have covered their sources.
TRANSLATION_SCHEMA_VERSION = 3

# The crates the proofs are about. A proof about translated Rust is a proof
# about *these* bytes, so their hashes belong in the attestation.
#
# The six `scripts/run-aeneas.sh` translates on their own, the three-leaf unit
# it translates, and `tacenta-core/triple`, which it translates only inside the
# unit: the Triple Ratchet's proofs are about the unit's translation, and the
# unit is generated from these bytes. If `run-aeneas.sh` gains a crate, this
# list must gain it too; the two are checked against each other below, counting
# an assembled zone's sources as translated with it.
#
# `triple-unit` is the three-leaf translation unit, generated rather than
# written, and hashing it is how a hand-edited generated crate is caught. Where its *sources* are hashed is
# `ASSEMBLED_ZONES`, immediately below, because hashing a generated tree says
# only that it is the tree somebody generated, not what it was generated from.
VERIFIED_ZONES = [
    "tacenta-core/ratchet",
    "tacenta-core/session",
    "tacenta-core/erasure",
    "tacenta-core/protobuf",
    "tacenta-core/wire",
    "tacenta-core/spqr",
    "tacenta-core/braid",
    "tacenta-core/triple",
    "tacenta-core/triple-unit",
]

# Verified zones that are *assembled*, and what from.
#
# An ordinary zone is written by hand, so `zone_sha256` is its provenance: the
# translation is stale exactly when the crate's bytes move. A generated zone's
# bytes are a consequence, not a cause. Its provenance is the script that wrote
# it and the trees the script read, so the record carries those too and
# `--check` fails when any of them moves without a regeneration -- which is the
# case that matters, since editing a leaf changes the unit's translation while
# leaving the unit crate in the tree looking untouched until somebody re-runs
# the assembly.
#
# This is stricter than it may look: the leaf trees here are already attested
# in their own right (all three are verified zones), so a leaf edit already
# fails the check for that leaf's own generated module. Naming them again here
# is what makes the *unit's* record fail too, independently and with a message
# that says to re-assemble and re-translate rather than only to re-translate.
ASSEMBLED_ZONES = {
    "tacenta-core/triple-unit": {
        "script": "tacenta-proofs/scripts/assemble-triple-unit.sh",
        "sources": [
            "tacenta-core/ratchet",
            "tacenta-core/spqr",
            "tacenta-core/triple",
        ],
    },
}

# The crates the verified zones bottom out in but that are NOT translated:
# every `HmacTotal`/`HkdfAgrees`/`Encapsulate2Total`-style hypothesis is a
# statement about *these* bytes, so a proof that names them as its boundary is
# a proof about a particular `kdf` and `kem`. Hashed so that the attestation
# can tell a reader which boundary a refinement was proved against. Listed
# apart from `VERIFIED_ZONES` because nothing in them is proved; they are what
# the proofs assume.
TRUSTED_PRIMITIVE_ZONES = [
    "tacenta-core/kdf",
    "tacenta-core/kem",
]

# The lockfile pins every third-party crate the zones above compile against
# (dalek, libcrux, RustCrypto, zeroize). A different lockfile is a different
# artefact; the manifest says which one the translation ran on.
LOCKFILES = [
    "tacenta-core/Cargo.lock",
]

# Everything outside a verified zone that changes what Charon extracts from
# it: the workspace manifest (its `[profile]` tables decide `overflow-checks`,
# and so whether an addition panics or wraps in the code being translated),
# the lockfile, any `.cargo/` configuration (rustflags, cfgs), and the two
# trusted primitive crates, whose signatures are the opaque externals every
# translation declares. Hashed together into one `workspace_sha256` that each
# translation record carries, so a change to any of them makes every recorded
# generation stale until the toolchain is run again.
WORKSPACE_INPUTS = [
    "tacenta-core/Cargo.toml",
    "tacenta-core/Cargo.lock",
    "tacenta-core/.cargo",
    "tacenta-core/kdf",
    "tacenta-core/kem",
]

# Axioms the Lean kernel itself introduces. A theorem whose `#print axioms`
# lists nothing outside this set was checked by the kernel alone.
KERNEL_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Axioms that mean a compiled program was trusted to have evaluated correctly:
# `Lean.ofReduceBool` and `Lean.trustCompiler` from `native_decide`, and the
# `._native.bv_decide.ax_*` family from `bv_decide`. Detected by name and by
# the two substrings the generated auxiliary names carry.
COMPILER_AXIOMS = {"Lean.ofReduceBool", "Lean.trustCompiler", "Lean.ofReduceNat"}


def compiler_axiom(name):
    return name in COMPILER_AXIOMS or "._native." in name or "bv_decide" in name


# The third kind: opaque externals. The Aeneas translation declares every
# operation it does not model (`tacenta_kdf.hmac_sha256`, `alloc.vec.Vec.remove`,
# `zeroize.Zeroizing.new`, ...) as an `axiom`, and a theorem about the
# translated Rust inherits them. They are the trusted boundary CLAIMS.md
# discloses, not compiler trust, and are classified apart from `native_decide`
# so that a T1 theorem with no compiler axiom among its dependencies is not
# reported as "compiler trusted". The set is read from the generated files
# rather than hand-listed, so a new external is classified the day it appears;
# and because it is read from the generated files, `--check` also holds those
# files to the axiom set recorded at generation time (see `check_translation`),
# so a new one fails there rather than being reclassified here.
GENERATED = ROOT / "tacenta-proofs" / "translation" / "Translation"


def lean_code(text):
    """`text` with `--` line comments, `/- ... -/` block comments (docstrings
    included, and nested blocks) and `"..."` string literals replaced by
    spaces, newlines kept, so that what remains is code and line numbers
    survive. Shared by every scan below: a keyword in prose or in a string is
    not a declaration, and a declaration is one wherever it sits on a line.
    The same stripper as `scripts/check-lean-constructs.sh`."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i:i + 2]
        if depth == 0 and two == "--":
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
            continue
        if two == "/-":
            depth += 1
            out.append("  ")
            i += 2
            continue
        if depth > 0 and two == "-/":
            depth -= 1
            out.append("  ")
            i += 2
            continue
        if depth == 0 and text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append("".join("\n" if ch == "\n" else " " for ch in text[i:j]))
            i = j
            continue
        out.append(text[i] if depth == 0 or text[i] == "\n" else " ")
        i += 1
    return "".join(out)


# The `axiom` keyword as a token, wherever it sits: at the start of a line as
# Aeneas writes it, behind an attribute or `private`, after `set_option ... in`
# or `namespace X` on the same line, or after another command's last token.
# `axiom` is a reserved word, so outside a comment or a string (which
# `lean_code` has removed) a token of that spelling is the keyword. The name
# is what follows it, as written: inside `namespace tacenta_braid` the file
# says `axiom tacenta_kdf.hkdf_sha256`, and that is what is recorded.
AXIOM_DECL = re.compile(r"(?<![\w.«])axiom\s+([^\s:({\[]+)")


def generated_files():
    return sorted(GENERATED.glob("Tacenta*.lean"))


def axioms_declared(path):
    return sorted(set(AXIOM_DECL.findall(lean_code(path.read_text()))))


def opaque_externals():
    names = set()
    for p in generated_files():
        names.update(axioms_declared(p))
    return names


def is_external(name, externals):
    """`#print axioms` prints an external fully qualified (`tacenta_triple.
    tacenta_kdf.hkdf_sha256`) where the generated file declares it inside a
    `namespace` (`axiom tacenta_kdf.hkdf_sha256`), so match on the declared
    name as a dotted suffix rather than on equality alone."""
    return any(name == e or name.endswith("." + e) for e in externals)


def classify(axioms, externals):
    """'kernel', 'opaque-external' or 'compiler'.

    Anything not recognised as kernel or as a declared external counts as
    compiler trust, which is the safe direction: an unknown axiom widens the
    trust base, and the manifest should say so rather than guess.
    """
    if all(a in KERNEL_AXIOMS for a in axioms):
        return "kernel"
    if any(compiler_axiom(a) for a in axioms):
        return "compiler"
    if all(a in KERNEL_AXIOMS or is_external(a, externals) for a in axioms):
        return "opaque-external"
    return "compiler"

# Where the machine-checked claims live. A directory is walked; the last entry
# is the translation package's root module, which sits beside its directory
# rather than in it and would otherwise be neither scanned nor hashed.
PROOF_TREES = [
    "tacenta-model",
    "tacenta-proofs/Proofs",
    "tacenta-proofs/translation/Translation",
    "tacenta-proofs/translation/Translation.lean",
]


def run(*args, cwd=ROOT):
    return subprocess.run(
        args, cwd=cwd, capture_output=True, text=True, check=True
    ).stdout.strip()


def git_commit():
    return run("git", "rev-parse", "HEAD")


# Fields that change every time these files are written, and so cannot take part
# in the staleness comparison.
#
# `generated_at_commit` is the obvious trap: the manifest is generated at commit
# X and lands in its child Y, so at Y a comparison including it always reports
# a difference, and the check that exists to catch drift would instead cry wolf
# on every commit. It is kept because a reader wants it and excluded because a
# comparison cannot use it. The content hashes below are the actual attestation:
# they say which bytes were proved, more precisely than a commit does, and they
# do not move when a commit does.
VOLATILE = ("generated_at_commit",)


def comparable(obj):
    return {k: v for k, v in obj.items() if k not in VOLATILE}


def file_hash(rel):
    """A content hash over one tracked file, for the lockfiles."""
    path = ROOT / rel
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_files(rel):
    """The files a content hash covers under `rel`: the file itself if `rel`
    names one, otherwise every file below the directory except Lake's build
    tree, a `target/` at the directory's top level (Cargo's, and only
    Cargo's: a source directory named `target` deeper down is source), and
    dotfiles. Sorted, so the hash is a function of content alone."""
    path = ROOT / rel
    if not path.exists():
        return []
    if path.is_file():
        return [path]
    return sorted(
        p for p in path.rglob("*")
        if p.is_file()
        and ".lake" not in p.parts
        and p.relative_to(path).parts[0] != "target"
        and not p.name.startswith(".")
    )


def hash_files(files):
    h = hashlib.sha256()
    for p in files:
        h.update(str(p.relative_to(ROOT)).encode())
        h.update(b"\0")
        h.update(p.read_bytes())
        h.update(b"\0")
    return h.hexdigest()


def tree_hash(rel):
    """A content hash over a directory's tracked source.

    `git rev-parse HEAD:<path>` would be shorter, but it names the committed
    tree, and this script also has to describe a working tree that has not been
    committed yet. Hashing the files gives the same answer for the same content
    either way.
    """
    if not (ROOT / rel).exists():
        return None
    files = source_files(rel)
    return {"sha256": hash_files(files), "files": len(files)}


def workspace_hash():
    """One hash over `WORKSPACE_INPUTS`, the inputs outside the verified zones
    that shape their translation. Absent entries (`.cargo/` today) contribute
    nothing, so adding one later changes the hash."""
    files = []
    for rel in WORKSPACE_INPUTS:
        files += source_files(rel)
    return {"sha256": hash_files(files), "files": len(files), "inputs": WORKSPACE_INPUTS}


def aeneas_commit():
    lakefile = ROOT / "tacenta-proofs/translation/lakefile.toml"
    if not lakefile.exists():
        return None
    m = re.search(r'name\s*=\s*"aeneas".*?rev\s*=\s*"([^"]+)"', lakefile.read_text(), re.S)
    return m.group(1) if m else None


def aeneas_release():
    """The release name `run-aeneas.sh` pins, which is also the name the
    verification workflow downloads and checksums."""
    if not RUN_AENEAS.exists():
        return None
    m = re.search(r'AENEAS_RELEASE="\$\{AENEAS_RELEASE:-([^}]+)\}"', RUN_AENEAS.read_text())
    return m.group(1) if m else None


def toolchains():
    """The versions a rebuild would need. Read from the pins, never typed."""
    out = {}
    for rel in [
        "tacenta-model/lean-toolchain",
        "tacenta-proofs/lean-toolchain",
        "tacenta-proofs/translation/lean-toolchain",
    ]:
        p = ROOT / rel
        if p.exists():
            out[rel] = p.read_text().strip()

    commit = aeneas_commit()
    if commit:
        out["aeneas"] = commit
    release = aeneas_release()
    if release:
        out["aeneas_release"] = release

    # The Aeneas archive digest lives in REPRODUCING.md and the verification
    # workflow and is not read here.
    return out


# Matches both the multi-line pin shape (`/--` on its own line, the info on the
# next) and the single-line shape (`/-- info: ... -/` on one line): `\s*`
# matches a newline or a space, so a pin laid out on one line counts, and
# `check_completeness` sees it.
#
# `RAW_PIN` is every pin, by its two commands alone, so that `AXIOM_PIN` can be
# checked against it (see `axiom_pins`).
RAW_PIN = re.compile(r"#guard_msgs in\s*\n\s*#print axioms\s+\S+")

AXIOM_PIN = re.compile(
    r"/--\s*"
    r"(?P<body>info: '(?P<name>[^']+)' depends on axioms: \[(?P<axioms>.*?)\])\s*"
    r"-/\s*\n"
    r"#guard_msgs in\s*\n"
    r"#print axioms\s+(?P<again>\S+)",
    re.S,
)


def proof_files():
    for rel in PROOF_TREES:
        for p in source_files(rel):
            if p.suffix == ".lean":
                yield p


def axiom_pins():
    """Collect every build-verified axiom pin in the repository.

    These are facts the Lean build already checks. If a pin were wrong the build
    would fail, so what this returns is as true as the build is.
    """
    pins = []
    externals = opaque_externals()
    for p in proof_files():
        text = p.read_text()
        # Every `#guard_msgs in` / `#print axioms` pair in the file must be
        # a match, or this stops: a pin whose docstring has a shape the
        # regex does not recognise would otherwise drop out of the count.
        raw_pairs = len(RAW_PIN.findall(text))
        matched = len(AXIOM_PIN.findall(text))
        if raw_pairs != matched:
            raise SystemExit(
                f"{p}: {raw_pairs} `#guard_msgs in`/`#print axioms` pairs but the pin "
                f"regex matched {matched}; a pin's docstring has a shape AXIOM_PIN "
                "does not recognise"
            )
        for m in AXIOM_PIN.finditer(text):
            name = m.group("name")
            if m.group("again") != name:
                raise SystemExit(
                    f"{p}: pin names {name} but prints {m.group('again')}"
                )
            axioms = [a.strip() for a in m.group("axioms").split(",")]
            axioms = [a for a in axioms if a]
            trust = classify(axioms, externals)
            pins.append(
                {
                    "theorem": name,
                    "file": str(p.relative_to(ROOT)),
                    "axioms": sorted(axioms),
                    # The distinctions that matter to a reader: a proof the
                    # kernel checked; one that assumes the translation's
                    # opaque externals (the disclosed trusted boundary);
                    # and one that trusts a compiled program to have
                    # evaluated correctly.
                    "trust": trust,
                    "kernel_only": trust == "kernel",
                }
            )
    return sorted(pins, key=lambda x: (x["file"], x["theorem"]))


# ---------------------------------------------------------------------------
# The claim ledger
#
# A "Proved" section of CLAIMS.md names its files on a `Location:` line and
# its theorems in bullets. A claim bullet opens with a run of backticked
# identifiers -- `` - `a`, `b` and `c`: ... `` -- and every identifier in that
# run is a claim; the run ends at the first token that is not a backticked
# identifier followed by a separator, so a name mentioned in passing further
# into the sentence (`` `MAX_SKIP` ``, `` `Nat` ``) is prose and not a claim.
# An identifier may carry its own location, `` `hkdf_length` (in
# `tacenta-model/Model/Kdf.lean`) ``, for the few theorems a section cites from
# a file its `Location:` line does not name.
# ---------------------------------------------------------------------------

CLAIM_SECTION = re.compile(r"^## (.+)$", re.M)
# A section may name more than one file: the wire-encoding section says the
# ratchet is in one place and the encoding in another, in one sentence. Read
# every path it names rather than the first, which is what a reader does.
CLAIM_LOCATION = re.compile(r"Location:(.+?)(?:\n\n|\n-)", re.S)
CLAIM_PATH = re.compile(r"`([^`]+\.lean)`")
CLAIM_BULLET = re.compile(r"^- (.*?)(?=\n- |\n\n|\Z)", re.M | re.S)
IDENT = r"[A-Za-z_][A-Za-z0-9_.']*"
CLAIM_TOKEN = re.compile(rf"`({IDENT})`(?:\s*\(in\s+`([^`]+\.lean)`\))?")
# What may follow a claimed identifier: a colon ending the run, a separator
# leading to the next identifier, or the end of the bullet's first clause.
CLAIM_SEP = re.compile(r"\s*(?::|,\s*(?:and\s+)?|\s+and\s+|$)")

# Where a `Location:` path is resolved from. CLAIMS.md is written from inside
# `tacenta-proofs/`, so paths are relative to it, to the translation package,
# or to the repository root, and each is tried in turn.
PATH_BASES = [
    ROOT / "tacenta-proofs",
    ROOT / "tacenta-proofs" / "translation",
    ROOT,
]


def resolve_claim_path(rel):
    rel = rel.lstrip("./")
    for base in PATH_BASES:
        p = base / rel
        if p.exists():
            return str(p.relative_to(ROOT))
    return None


def claim_names(bullet):
    """The leading run of backticked identifiers in a bullet, each with its
    own location override if it carries one."""
    out = []
    pos = 0
    while True:
        m = CLAIM_TOKEN.match(bullet, pos)
        if not m:
            break
        sep = CLAIM_SEP.match(bullet, m.end())
        if not sep:
            break
        out.append((m.group(1), m.group(2)))
        if sep.group(0).strip() in (":", ""):
            break
        pos = sep.end()
    return out


def claims():
    """Parse CLAIMS.md into the theorem names it asserts, with their files.

    Returns the claim list and any problems with the ledger's own shape: a
    `Location:` path that does not exist, or a per-bullet location that does
    not.
    """
    p = ROOT / "tacenta-proofs" / "CLAIMS.md"
    text = p.read_text()
    out = []
    problems = []
    bounds = [(m.start(), m.group(1)) for m in CLAIM_SECTION.finditer(text)]
    bounds.append((len(text), None))
    for i in range(len(bounds) - 1):
        start, title = bounds[i]
        end = bounds[i + 1][0]
        if not title.lower().startswith("proved"):
            continue
        body = text[start:end]
        loc = CLAIM_LOCATION.search(body)
        files = []
        if loc:
            for rel in CLAIM_PATH.findall(loc.group(1)):
                resolved = resolve_claim_path(rel)
                if resolved is None:
                    problems.append(
                        f"CLAIMS.md section `{title}` names `{rel}` on its Location "
                        "line, and no such file exists"
                    )
                else:
                    files.append(resolved)
        else:
            problems.append(f"CLAIMS.md section `{title}` has no Location: line")
        for b in CLAIM_BULLET.finditer(body):
            for name, override in claim_names(b.group(1)):
                claimed_files = files
                if override:
                    resolved = resolve_claim_path(override)
                    if resolved is None:
                        problems.append(
                            f"CLAIMS.md places `{name}` in `{override}`, and no such "
                            "file exists"
                        )
                        continue
                    claimed_files = [resolved]
                out.append(
                    {
                        "section": title,
                        "theorem": name,
                        "claimed_files": claimed_files,
                    }
                )
    return out, problems


# A declaration and the `namespace` nesting it sits in, so that the name the
# build knows (`Tacenta.T3.send_refines`) is what the ledger is checked
# against, rather than the bare last segment (`send_refines`), which several
# files share.
#
# Matched on the comment-stripped text (`lean_code`), as a token wherever it
# sits, so that the word in a docstring ("the theorem above relates ...") is
# not a declaration and a declaration after `set_option ... in` is one.
DECL = re.compile(r"(?<![\w.«])theorem\s+([A-Za-z_][A-Za-z0-9_.']*)")
NAMESPACE = re.compile(r"^(namespace|end|section)\b\s*(\S*)", re.M)


def declared_theorems():
    """Every theorem declared in the first-party proof trees, fully qualified
    by the `namespace` blocks around it, with the file it is in."""
    found = []
    for p in proof_files():
        text = lean_code(p.read_text())
        events = []
        for m in NAMESPACE.finditer(text):
            events.append((m.start(), "ns", m.group(1), m.group(2)))
        for m in DECL.finditer(text):
            events.append((m.start(), "decl", m.group(1), None))
        events.sort(key=lambda e: e[0])
        stack = []  # (kind, name)
        for _, kind, a, b in events:
            if kind == "ns":
                if a == "namespace":
                    stack.append(("namespace", b))
                elif a == "section":
                    stack.append(("section", b))
                elif stack:
                    stack.pop()
            else:
                prefix = ".".join(n for k, n in stack if k == "namespace" and n)
                fq = f"{prefix}.{a}" if prefix else a
                found.append((fq, str(p.relative_to(ROOT))))
    return found


def resolve_claim(claim, declared):
    """The fully-qualified theorem a claim names, in the file its section
    names, or a problem string."""
    name = claim["theorem"]
    matches = [(fq, f) for fq, f in declared if fq == name or fq.endswith("." + name)]
    if not matches:
        return None, f"CLAIMS.md claims `{name}` but no such theorem is declared"
    wants = claim["claimed_files"]
    if wants:
        located = [(fq, f) for fq, f in matches if f in wants]
        if not located:
            return None, (
                f"CLAIMS.md places `{name}` in {' or '.join(wants)}, "
                f"found in {', '.join(sorted({f for _, f in matches}))}"
            )
        matches = located
    names = sorted({fq for fq, _ in matches})
    if len(names) > 1:
        return None, (
            f"CLAIMS.md claims `{name}` and it is ambiguous between "
            f"{', '.join(names)}; qualify it"
        )
    return names[0], None


def check_claims(claim_list, declared):
    """Every claim must name a theorem that exists, in the file it says. Fills
    in each claim's resolved fully-qualified name as a side effect."""
    problems = []
    for c in claim_list:
        fq, problem = resolve_claim(c, declared)
        if problem:
            problems.append(problem)
        c["resolved"] = fq
    return problems


def check_completeness(claim_list, pins):
    """Every axiom-pinned theorem must appear in the ledger.

    Not every theorem belongs in a claims document; most are lemmas. A pin is
    the repository's own mark that a result is load-bearing, so "pinned but not
    claimed" is exactly the drift worth failing on: a ledger calling itself
    exact while a proof area that has landed is missing from it. Compared on
    fully-qualified names, so a `send_refines` claim in one section does not
    cover a pinned `send_refines` in another.
    """
    claimed = {c.get("resolved") for c in claim_list} - {None}
    return [
        f"`{p['theorem']}` is axiom-pinned in {p['file']} but absent from CLAIMS.md"
        for p in pins
        if p["theorem"] not in claimed
    ]


def translated_modules():
    """`translate <leaf dir> <package> <llbc> <module>` lines in run-aeneas.sh:
    which generated module comes from which crate."""
    script = RUN_AENEAS.read_text()
    return {
        module: f"tacenta-core/{leaf}"
        for leaf, _pkg, _llbc, module in re.findall(
            r"^translate\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)", script, re.M
        )
    }


def check_zones_match_translation():
    """`VERIFIED_ZONES` and `run-aeneas.sh` name the same crates.

    The attestation is only worth reading if it hashes every crate the proofs
    are about, and the translation script is the authority on which those are.
    """
    translated = set(translated_modules().values())
    # A crate translated only as a source of an assembled zone -- the Triple,
    # inside the three-leaf unit -- is translated with that zone.
    for zone, spec in ASSEMBLED_ZONES.items():
        if zone in translated:
            translated.update(spec["sources"])
    attested = set(VERIFIED_ZONES)
    return [
        f"run-aeneas.sh translates `{c}` but VERIFIED_ZONES does not attest it"
        for c in sorted(translated - attested)
    ] + [
        f"VERIFIED_ZONES attests `{c}` but run-aeneas.sh does not translate it"
        for c in sorted(attested - translated)
    ]


# How an assembly script names the leaf trees it reads: the `#[path]` lines it
# writes into the unit's root module, and the leaf file it copies.
ASSEMBLY_SOURCE_RES = (
    re.compile(r'#\[path = "\.\./\.\./([a-z0-9-]+)/src/lib\.rs"\]'),
    re.compile(r"\$core/([a-z0-9-]+)/src/lib\.rs"),
)


def check_assembly_sources():
    """`ASSEMBLED_ZONES` names each assembled zone's sources by hand, and
    `check_zones_match_translation` counts those sources as translated. Read
    the same list out of the assembly script, so that a source named there that
    the script never reads -- which would let an attested zone nothing
    translates pass -- or one the script reads that is not named, fails."""
    problems = []
    for zone, spec in ASSEMBLED_ZONES.items():
        text = (ROOT / spec["script"]).read_text()
        read = {f"tacenta-core/{leaf}" for rx in ASSEMBLY_SOURCE_RES for leaf in rx.findall(text)}
        named = set(spec["sources"])
        problems += [
            f"ASSEMBLED_ZONES names `{src}` as a source of `{zone}`, but "
            f"{spec['script']} never reads it"
            for src in sorted(named - read)
        ] + [
            f"{spec['script']} reads `{src}` for `{zone}`, but ASSEMBLED_ZONES "
            "does not name it as a source"
            for src in sorted(read - named)
        ]
    return problems


# ---------------------------------------------------------------------------
# The translation attestation
# ---------------------------------------------------------------------------

def assembly_record(zone):
    """For a zone that is assembled rather than written, what it was assembled
    from: the script, and each source tree it reads. `None` for an ordinary
    zone, whose own hash is already its provenance."""
    spec = ASSEMBLED_ZONES.get(zone)
    if spec is None:
        return None
    return {
        "script": spec["script"],
        "script_sha256": file_hash(spec["script"]),
        "sources": {
            src: tree_hash(src)["sha256"] for src in spec["sources"]
        },
    }


def translation_attestation():
    """What the generated translation is, right now: per file, its hash, the
    axioms it declares, and the hash of the Rust it stands for -- plus, where
    that Rust is itself generated, what it was generated from."""
    zones = translated_modules()
    workspace = workspace_hash()["sha256"]
    files = {}
    for p in generated_files():
        module = p.stem
        zone = zones.get(module)
        record = {
            "module": module,
            "sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
            "axioms": axioms_declared(p),
            "zone": zone,
            "zone_sha256": tree_hash(zone)["sha256"] if zone else None,
            "workspace_sha256": workspace,
        }
        assembly = assembly_record(zone) if zone else None
        if assembly is not None:
            record["assembly"] = assembly
        files[str(p.relative_to(ROOT))] = record
    return {
        "schema_version": TRANSLATION_SCHEMA_VERSION,
        "_note": (
            "Written only by `tacenta-proofs/scripts/attest.py --refresh-translation`, "
            "immediately after `scripts/run-aeneas.sh` on the pinned toolchain, and "
            "compared against by every other mode. A green `attest.py --check` "
            "establishes that each generated Translation/Tacenta*.lean is a module "
            "run-aeneas.sh produces, is byte for byte the file recorded here, declares "
            "exactly the axioms recorded here (as text; no-sorry.sh compares the same "
            "record with what the axiom audit saw in the built environment), and that "
            "the Rust verified zone it was generated from, and the workspace inputs "
            "that shape every zone's extraction (Cargo.toml and its profiles, "
            "Cargo.lock, .cargo/, the kdf and kem crates), hash to what they hashed "
            "to when this was written, as recorded by whoever ran the toolchain. "
            "Where the zone is assembled rather than written (tacenta-core/triple-unit, "
            "the three-leaf translation unit), the record carries an `assembly` "
            "field naming the script and the three leaf trees it was assembled from, "
            "with their hashes, and --check fails if any of them has moved since; "
            "assemble-triple-unit.sh --check is the separate question of whether the "
            "unit crate in the tree is what those leaves assemble to. It "
            "does not establish that the toolchain was run, or run honestly: that is "
            "checked by regenerating with run-aeneas.sh and diffing, which "
            "REPRODUCING.md describes."
        ),
        "generated_at_commit": git_commit(),
        "aeneas": {
            "release": aeneas_release(),
            "commit": aeneas_commit(),
        },
        "generated_files": files,
    }


def check_translation(current):
    """The tree against the recorded translation attestation.

    Six questions, each its own failure: is every file named like a
    generated one a module `run-aeneas.sh` produces; is every generated file
    the bytes that were recorded; does each declare exactly the axioms that
    were recorded (compared as sets, so a removed axiom fails as an added one
    does); is the Rust each was generated from still the Rust in the tree; for
    a zone that is assembled rather than written, are the assembly script and
    all three leaf trees still what they were; and are the workspace inputs
    that shape every zone's extraction still what they were. The last three are
    the ones that go stale by ordinary work, and their messages say what to do.
    """
    problems = []
    for rel, w in current["generated_files"].items():
        if w["zone"] is None:
            problems.append(
                f"{rel} is named like a generated file but scripts/run-aeneas.sh "
                f"produces no module {w['module']}: nothing attests it, so it may not "
                "sit under Translation/ with that name"
            )
    if not TRANSLATION_MANIFEST.exists():
        return problems + [
            f"{TRANSLATION_MANIFEST.relative_to(ROOT)} is missing: run "
            "scripts/run-aeneas.sh on the pinned toolchain, then "
            "`attest.py --refresh-translation`"
        ]
    recorded = json.loads(TRANSLATION_MANIFEST.read_text())
    if recorded.get("schema_version") != TRANSLATION_SCHEMA_VERSION:
        problems.append(
            f"translation-attestation.json has schema_version "
            f"{recorded.get('schema_version')!r}, and this script reads "
            f"{TRANSLATION_SCHEMA_VERSION}: regenerate with scripts/run-aeneas.sh on "
            "the pinned toolchain and re-run attest.py --refresh-translation"
        )
    if recorded.get("aeneas") != current["aeneas"]:
        problems.append(
            f"the Aeneas pin changed since the translation was recorded "
            f"({recorded.get('aeneas')} recorded, {current['aeneas']} now): regenerate "
            "with scripts/run-aeneas.sh on the new pin and re-run attest.py "
            "--refresh-translation"
        )
    have = recorded.get("generated_files", {})
    want = current["generated_files"]
    for rel in sorted(set(have) - set(want)):
        problems.append(f"{rel} is recorded in translation-attestation.json but is not in the tree")
    for rel in sorted(set(want) - set(have)):
        problems.append(
            f"{rel} is a generated file with no record in translation-attestation.json: "
            "if it came from scripts/run-aeneas.sh on the pinned toolchain, run "
            "attest.py --refresh-translation"
        )
    for rel in sorted(set(want) & set(have)):
        r, w = have[rel], want[rel]
        if r.get("zone") is None:
            problems.append(
                f"{rel} is recorded with no zone: the record was written for a file "
                "run-aeneas.sh does not produce, which --refresh-translation now refuses"
            )
        if r.get("sha256") != w["sha256"]:
            problems.append(
                f"{rel} differs from the recorded generation (sha256 {r.get('sha256')} "
                f"recorded, {w['sha256']} now): a generated file may only change by "
                "running scripts/run-aeneas.sh on the pinned toolchain, followed by "
                "attest.py --refresh-translation"
            )
        added = sorted(set(w["axioms"]) - set(r.get("axioms", [])))
        removed = sorted(set(r.get("axioms", [])) - set(w["axioms"]))
        if added or removed:
            problems.append(
                f"{rel} declares a different axiom set from the recorded one "
                f"(added: {', '.join(added) or 'none'}; removed: {', '.join(removed) or 'none'}): "
                "an opaque external appears only through scripts/run-aeneas.sh, "
                "followed by attest.py --refresh-translation"
            )
        if r.get("zone") != w["zone"]:
            problems.append(f"{rel} is recorded as generated from {r.get('zone')} but run-aeneas.sh now maps it to {w['zone']}")
        elif w["zone"] and r.get("zone_sha256") != w["zone_sha256"]:
            problems.append(
                f"translation is stale for {w['zone']}: the crate hashes to "
                f"{w['zone_sha256'][:12]}... now and hashed to "
                f"{str(r.get('zone_sha256'))[:12]}... when {rel} was generated; "
                "regenerate with scripts/run-aeneas.sh on the pinned toolchain and "
                "re-run attest.py --refresh-translation"
            )
        # The assembled zone's provenance. Compared field by field rather than
        # as one blob so the message can name what moved: an edited assembly
        # script and an edited leaf are different mistakes with different
        # fixes, and "the record differs" would send a reader looking through
        # four trees.
        r_asm, w_asm = r.get("assembly"), w.get("assembly")
        if (r_asm is None) != (w_asm is None):
            problems.append(
                f"{rel} is recorded "
                f"{'with' if r_asm else 'without'} an assembly record and the tree "
                f"now says it is {'assembled' if w_asm else 'written by hand'}: "
                "ASSEMBLED_ZONES and the recorded manifest disagree about how this "
                "zone comes to exist; regenerate with scripts/run-aeneas.sh and "
                "re-run attest.py --refresh-translation"
            )
        elif w_asm is not None:
            if r_asm.get("script") != w_asm["script"]:
                problems.append(
                    f"{rel} is recorded as assembled by {r_asm.get('script')} and "
                    f"ASSEMBLED_ZONES now names {w_asm['script']}"
                )
            elif r_asm.get("script_sha256") != w_asm["script_sha256"]:
                problems.append(
                    f"the translation is stale for {rel}: its assembly script "
                    f"{w_asm['script']} hashes to {w_asm['script_sha256'][:12]}... now "
                    f"and hashed to {str(r_asm.get('script_sha256'))[:12]}... when the "
                    "unit was generated; re-assemble and re-translate with "
                    "scripts/run-aeneas.sh, then re-run attest.py "
                    "--refresh-translation"
                )
            r_src, w_src = r_asm.get("sources", {}), w_asm["sources"]
            for src in sorted(set(r_src) ^ set(w_src)):
                problems.append(
                    f"{rel} is recorded as assembled from "
                    f"{', '.join(sorted(r_src)) or 'nothing'} and ASSEMBLED_ZONES now "
                    f"names {', '.join(sorted(w_src))}"
                )
            for src in sorted(set(r_src) & set(w_src)):
                if r_src[src] != w_src[src]:
                    problems.append(
                        f"the translation is stale for {rel}: it was assembled from "
                        f"{src}, which hashes to {w_src[src][:12]}... now and hashed "
                        f"to {str(r_src[src])[:12]}... when the unit was generated. "
                        "A leaf edit changes the unit's translation even though the "
                        "unit crate in the tree still looks untouched; re-assemble "
                        "and re-translate with scripts/run-aeneas.sh, then re-run "
                        "attest.py --refresh-translation"
                    )
        if r.get("workspace_sha256") != w["workspace_sha256"]:
            problems.append(
                f"translation is stale for {rel}: the workspace inputs "
                f"({', '.join(WORKSPACE_INPUTS)}) hash to {w['workspace_sha256'][:12]}... "
                f"now and hashed to {str(r.get('workspace_sha256'))[:12]}... when it was "
                "generated; a profile, lockfile, cargo configuration or primitive-crate "
                "change shapes what Charon extracts, so regenerate with "
                "scripts/run-aeneas.sh on the pinned toolchain and re-run attest.py "
                "--refresh-translation"
            )
    return problems


# ---------------------------------------------------------------------------
# The environment's view of the generated axioms
# ---------------------------------------------------------------------------

# What `Model.AxiomAudit.run` prints for every axiom it finds in a generated
# module, fully qualified: `audit-axiom: Translation.TacentaBraid
# tacenta_braid.tacenta_kdf.hkdf_sha256`. The file records the name as
# declared (`tacenta_kdf.hkdf_sha256`, inside `namespace tacenta_braid`), so
# the two are matched as a declared name against a qualified one.
# Not anchored at the line start: Lake prefixes the first line of a message
# with `info: <file>:<line>:<col>: `, and the rest follow verbatim.
AUDIT_LINE = re.compile(r"\baudit-axiom:\s+(\S+)\s+(\S+)\s*$", re.M)
# The compiler-trust axioms the audit found in generated modules (Aeneas's
# `toStr` discharges its length bound `by decide +native`, so every generated
# `Debug` `fmt` body carries some). Not opaque externals and not in the
# manifest; counted, so the log says how many there are.
AUDIT_NATIVE_LINE = re.compile(r"\baudit-native:\s+(\S+)\s+(\S+)\s*$", re.M)


def compare_audit(log_path):
    """The axiom audit's list of generated axioms, read from a `lake build` log
    of the translation package, against the recorded per-file sets.

    `axioms_declared` reads the text; the audit reads the environment the text
    elaborated to. A declaration the text scan does not recognise as an axiom
    (one produced by a macro, or added by a command) is an axiom to the audit,
    and a recorded axiom the environment no longer holds is missing to it. Both
    audit modules' output must be in the log: `Translation.AxiomAudit` covers
    six generated modules and `AxiomAuditTripleUnit` the three-leaf translation
    unit, which cannot share an environment with it.
    """
    problems = []
    log = Path(log_path).read_text(errors="replace")
    seen = {}
    for module, name in AUDIT_LINE.findall(log):
        seen.setdefault(module, set()).add(name)
    native = {(m, n) for m, n in AUDIT_NATIVE_LINE.findall(log)}
    if not TRANSLATION_MANIFEST.exists():
        return [f"{TRANSLATION_MANIFEST.relative_to(ROOT)} is missing"], 0
    recorded = json.loads(TRANSLATION_MANIFEST.read_text()).get("generated_files", {})
    by_module = {r["module"]: (rel, set(r.get("axioms", []))) for rel, r in recorded.items()}
    expected_modules = {f"Translation.{m}" for m in by_module}
    for module in sorted(expected_modules - set(seen)):
        # A module recorded with no axioms (the wire parser translates with
        # none) prints no lines; one recorded with some and printing none
        # was not audited, or its output was not captured.
        if by_module[module.split(".", 1)[1]][1]:
            problems.append(
                f"the build log carries no audit-axiom lines for {module}: the axiom "
                "audit did not run over it, or its output was not captured"
            )
    for module in sorted(set(seen) - expected_modules):
        problems.append(
            f"the axiom audit reports axioms in {module}, which has no record in "
            "translation-attestation.json"
        )
    for module in sorted(set(seen) & expected_modules):
        rel, declared = by_module[module.split(".", 1)[1]]
        qualified = seen[module]
        unrecorded = sorted(
            q for q in qualified
            if not any(q == d or q.endswith("." + d) for d in declared)
        )
        missing = sorted(
            d for d in declared
            if not any(q == d or q.endswith("." + d) for q in qualified)
        )
        if unrecorded or missing:
            problems.append(
                f"{rel}: the axiom audit saw a different axiom set in the built "
                f"environment from the recorded one (in the environment but not "
                f"recorded: {', '.join(unrecorded) or 'none'}; recorded but not in the "
                f"environment: {', '.join(missing) or 'none'})"
            )
    return problems, len(native)


def build():
    commit = git_commit()
    pins = axiom_pins()
    claim_list, problems = claims()
    declared = declared_theorems()
    problems += check_claims(claim_list, declared)
    problems += check_completeness(claim_list, pins)
    problems += check_zones_match_translation()
    problems += check_assembly_sources()

    verification = {
        "schema_version": SCHEMA_VERSION,
        "_note": (
            "Generated by tacenta-proofs/scripts/attest.py. Do not edit: run the "
            "script. Every field is read out of the repository so this cannot "
            "describe a state the repository has left."
        ),
        "generated_at_commit": commit,
        "toolchains": toolchains(),
        "axiom_pins": pins,
        "counts": {
            "pinned_theorems": len(pins),
            "kernel_only": sum(1 for p in pins if p["trust"] == "kernel"),
            "opaque_external": sum(1 for p in pins if p["trust"] == "opaque-external"),
            "compiler_trusted": sum(1 for p in pins if p["trust"] == "compiler"),
            "declared_theorems": len(declared),
            "claimed_in_ledger": len(claim_list),
        },
        "claims": claim_list,
    }

    attestation = {
        "schema_version": SCHEMA_VERSION,
        "_note": (
            "Which sources the proofs correspond to. A proof about translated "
            "Rust is a proof about particular bytes; these hashes are those "
            "bytes. Generated by tacenta-proofs/scripts/attest.py. This is a "
            "consistency record, not tamper evidence: it is produced from the "
            "same working tree it describes, by an unsigned script, so it can "
            "tell you whether the proofs and the sources in a checkout still "
            "match each other, and nothing about whether either was altered "
            "before you obtained it. Verify the checkout against a signed tag "
            "for that. Whether the generated translation is the one produced "
            "from these sources is the separate question "
            "translation-attestation.json answers."
        ),
        "generated_at_commit": commit,
        "verified_zones": {z: tree_hash(z) for z in VERIFIED_ZONES},
        "trusted_primitive_zones": {z: tree_hash(z) for z in TRUSTED_PRIMITIVE_ZONES},
        "lockfiles": {f: file_hash(f) for f in LOCKFILES},
        "workspace": workspace_hash(),
        "proof_trees": {t: tree_hash(t) for t in PROOF_TREES},
    }
    return verification, attestation, problems


def write(obj, path):
    path.write_text(json.dumps(obj, indent=2, sort_keys=False) + "\n")


def report(problems, heading):
    print(f"attest: {heading}", file=sys.stderr)
    for p in problems:
        print(f"  {p}", file=sys.stderr)


USAGE = """usage: attest.py [--check | --check-translation | --refresh-translation
                 | --compare-audit <lake build log>]

  (no flag)              regenerate verification-manifest.json and
                         source-commit-attestation.json; verify the generated
                         translation against translation-attestation.json
  --check                verify all three manifests against the tree (CI)
  --check-translation    verify only the generated translation against
                         translation-attestation.json
  --refresh-translation  rewrite translation-attestation.json from the tree,
                         then regenerate the other two. Run this only right
                         after scripts/run-aeneas.sh on the pinned toolchain:
                         it records whatever the generated files are, and its
                         value is that nobody runs it at any other time. It
                         refuses a Tacenta*.lean that run-aeneas.sh does not
                         produce.
  --compare-audit <log>  compare the `audit-axiom:` lines the axiom audit
                         printed into a translation-package build log with the
                         per-file axiom sets recorded in
                         translation-attestation.json (no-sorry.sh runs this)
"""


def main():
    argv = sys.argv[1:]
    if argv[:1] == ["--compare-audit"]:
        if len(argv) != 2:
            print(USAGE, file=sys.stderr)
            return 2
        problems, native = compare_audit(argv[1])
        if problems:
            report(problems, "the axiom audit and translation-attestation.json disagree")
            return 1
        n = len(json.loads(TRANSLATION_MANIFEST.read_text()).get("generated_files", {}))
        print(
            f"attest: the axiom audit's opaque-external list matches "
            f"translation-attestation.json for {n} generated modules ({native} "
            "compiler-trust axioms in them, from Aeneas's toStr bound, are not externals "
            "and are listed in the build log)"
        )
        return 0
    args = set(argv)
    known = {"--check", "--check-translation", "--refresh-translation"}
    if args - known or len(args) > 1:
        print(USAGE, file=sys.stderr)
        return 2
    check = "--check" in args
    check_only_translation = "--check-translation" in args
    refresh = "--refresh-translation" in args

    current = translation_attestation()
    if refresh:
        unmapped = sorted(
            rel for rel, w in current["generated_files"].items() if w["zone"] is None
        )
        if unmapped:
            report(
                [
                    f"{rel} is named like a generated file but scripts/run-aeneas.sh "
                    "produces no such module; remove it or add it to run-aeneas.sh first"
                    for rel in unmapped
                ],
                "refusing to record a file the translation script does not produce",
            )
            return 1
        MANIFESTS.mkdir(parents=True, exist_ok=True)
        write(current, TRANSLATION_MANIFEST)
        print(f"attest: wrote {TRANSLATION_MANIFEST.relative_to(ROOT)}")
    translation_problems = check_translation(current)
    if check_only_translation:
        if translation_problems:
            report(translation_problems, "the generated translation does not match its attestation")
            return 1
        n = len(current["generated_files"])
        print(f"attest: {n} generated files match translation-attestation.json")
        return 0

    verification, attestation, problems = build()
    if problems:
        report(problems, "the claim ledger does not match the proofs")
        return 1

    targets = [
        (verification, MANIFESTS / "verification-manifest.json"),
        (attestation, MANIFESTS / "source-commit-attestation.json"),
    ]

    if check:
        stale = False
        for obj, path in targets:
            if not path.exists():
                print(f"attest: {path.relative_to(ROOT)} is missing", file=sys.stderr)
                stale = True
                continue
            have = json.loads(path.read_text())
            if comparable(obj) != comparable(have):
                print(f"attest: {path.relative_to(ROOT)} is stale", file=sys.stderr)
                stale = True
        if stale:
            print(
                "attest: run `python3 tacenta-proofs/scripts/attest.py` and commit",
                file=sys.stderr,
            )
        if translation_problems:
            report(translation_problems, "the generated translation does not match its attestation")
        if stale or translation_problems:
            return 1
        print(
            f"attest: manifests current "
            f"({verification['counts']['pinned_theorems']} pinned theorems, "
            f"{verification['counts']['kernel_only']} on the kernel alone; "
            f"{len(current['generated_files'])} generated files match their attestation)"
        )
        return 0

    MANIFESTS.mkdir(parents=True, exist_ok=True)
    for obj, path in targets:
        write(obj, path)
        print(f"attest: wrote {path.relative_to(ROOT)}")
    if translation_problems:
        report(translation_problems, "the generated translation does not match its attestation")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
