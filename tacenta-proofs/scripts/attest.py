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
the Aeneas pin. Three zones are assembled rather than written -- the Triple,
Braid-and-erasure, and complete Session translation units -- and each record
carries its provenance as well as its bytes: the assembly script and every
leaf tree it was assembled from, so that a leaf edited without re-assembling
fails. It is written only by `--refresh-translation`, which is meant
to be run immediately after `scripts/run-aeneas.sh`, refuses a `Tacenta*.lean`
that `run-aeneas.sh` does not produce, and every other mode compares the
tree against it. That is what makes it provenance rather than self-description:
the other two manifests are recomputed from the tree they describe, so they can
only ever say the tree is consistent with itself; this one says the generated
files are the bytes somebody recorded after running the pinned toolchain, and
the Rust they were generated from is the Rust in the tree now. What it cannot
say is that the toolchain was run honestly, or run at all: a reader who wants
that runs `run-aeneas.sh` themselves and diffs, which `REPRODUCING.md` describes.

The generated axioms also have a second record in
`manifests/translation-axiom-allowlist.json`: for each generated file, every
`axiom` it declares, by fully qualified name (the enclosing `namespace`
applied) and by the text of its type, one entry per declaration. `--check`
compares the text scan with it as a multiset, so a second declaration under a
name that is already listed, a declaration in another namespace, or a changed
type is a difference. Refreshing the translation attestation does not write
that file, and `--refresh-translation` refuses to record a tree the file does
not describe. The only writer is `--write-axiom-allowlist`, which prints what
it added and removed and refuses to run in CI. What this does not do: it does
not make a change to the file reviewed (there is no CODEOWNERS file, so
nothing in this tree routes a change to it to a named reviewer and the diff is
the only visibility), and it reads the text of the generated files, so it is not a
check of the elaborated environment; `no-sorry.sh` compares that environment
with the recorded names, and the type text is not compared there.

## What it deliberately does not claim

That the listed theorems are the *right* theorems, or that they add up to a
secure protocol. This records what was proved, on what, and against which
sources. `LIMITATIONS.md` is where what is not proved lives, and it is prose
because that part needs an argument rather than a field.
"""

import hashlib
import json
import os
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MANIFESTS = ROOT / "tacenta-proofs" / "manifests"
TRANSLATION_MANIFEST = MANIFESTS / "translation-attestation.json"
TRANSLATION_AXIOM_ALLOWLIST = MANIFESTS / "translation-axiom-allowlist.json"
RUN_AENEAS = ROOT / "tacenta-proofs" / "scripts" / "run-aeneas.sh"

SCHEMA_VERSION = 1
# The translation attestation's own schema: 2 added `workspace_sha256` to every
# record, so a manifest without it is refused rather than read as complete;
# 3 added `assembly` to the records of zones that are generated rather than
# written, so a manifest without it cannot claim to have covered their sources;
# 4 records each axiom by its fully qualified name, one entry per declaration,
# where 3 recorded the name as written and collapsed repeats.
TRANSLATION_SCHEMA_VERSION = 4
# The axiom allowlist's schema: 2 lists each declaration as a name and a type.
AXIOM_ALLOWLIST_SCHEMA_VERSION = 2

# The crates the proofs are about. A proof about translated Rust is a proof
# about *these* bytes, so their hashes belong in the attestation.
#
# The leaf crates `scripts/run-aeneas.sh` translates on their own, the assembled
# units it translates, and `tacenta-core/triple`, which it translates only
# inside a unit: the Triple Ratchet's proofs are about the unit's translation,
# and the unit is generated from these bytes. If `run-aeneas.sh` gains a crate, this
# list must gain it too; the two are checked against each other below, counting
# an assembled zone's sources as translated with it.
#
# The `*-unit` zones are generated rather than written, and hashing them is how
# a hand-edited generated crate is caught. Where their *sources* are hashed is
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
    "tacenta-core/lifecycle",
    "tacenta-core/triple",
    "tacenta-core/triple-unit",
    "tacenta-core/braid-unit",
    "tacenta-core/session-unit",
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
    "tacenta-core/braid-unit": {
        "script": "tacenta-proofs/scripts/assemble-braid-unit.sh",
        "sources": [
            "tacenta-core/braid",
            "tacenta-core/erasure",
        ],
    },
    "tacenta-core/session-unit": {
        "script": "tacenta-proofs/scripts/assemble-session-unit.sh",
        "sources": [
            "tacenta-core/ratchet",
            "tacenta-core/spqr",
            "tacenta-core/triple",
            "tacenta-core/erasure",
            "tacenta-core/braid",
            "tacenta-core/session",
            "tacenta-core/wire",
            "tacenta-core/lifecycle",
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
    "tacenta-core/boundary",
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
    "tacenta-core/boundary",
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


# A Lean character literal: `'a'`, `'"'`, `'\n'`, `'\x41'`, `'\u{1F600}'`.
_CHAR_LITERAL = re.compile(r"'(?:\\(?:x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f]+\}|.)|[^\\'\n])'")
# The characters that can continue an identifier, for telling `r"..."`, `'a'`
# and `«...»` at the start of a token from the same characters inside one.
_IDENT_CHARS = re.compile(r"[\w'!?«»]")


def lean_code(text, keep_names=False):
    """`text` with `--` line comments, `/- ... -/` block comments (docstrings
    included, and nested blocks), `"..."` and raw `r#"..."#` string literals
    and `'x'` character literals replaced by spaces, newlines kept, so that
    what remains is code and line numbers and offsets survive. Shared by every
    scan below: a keyword in prose or in a string is not a declaration, and a
    declaration is one wherever it sits on a line.

    An identifier written in guillemets (`«a b»`) is one token whatever it
    contains: a comment opener, a quote or a keyword inside it is part of the
    name. Its contents are replaced by `_` so a keyword scan does not see
    them, or kept as written when `keep_names` is set so the name can be read
    back. The output is the same length as the input, character for
    character, so an offset in one is an offset in the other.

    The same stripper as `scripts/check-lean-constructs.sh`, which keeps its
    own copy."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        ch = text[i]
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
        if depth > 0:
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        prev = text[i - 1] if i else " "
        if ch == "«":
            j = text.find("»", i)
            j = n if j < 0 else j + 1
            inner = text[i:j]
            out.append(inner if keep_names else "".join(
                c if c in "«»\n" else "_" for c in inner))
            i = j
            continue
        if ch == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append("".join("\n" if c == "\n" else " " for c in text[i:j]))
            i = j
            continue
        if ch == "r" and not _IDENT_CHARS.match(prev):
            raw = re.compile(r'r(#*)"').match(text, i)
            if raw:
                close = '"' + raw.group(1)
                j = text.find(close, raw.end())
                j = n if j < 0 else j + len(close)
                out.append("".join("\n" if c == "\n" else " " for c in text[i:j]))
                i = j
                continue
        if ch == "'" and not _IDENT_CHARS.match(prev):
            lit = _CHAR_LITERAL.match(text, i)
            if lit:
                out.append(" " * (lit.end() - i))
                i = lit.end()
                continue
        out.append(ch)
        i += 1
    return "".join(out)


# The keywords that decide what an `axiom` is called and where it ends. Read
# from the comment-stripped text, so a keyword in prose or in a string is not
# one. `axiom` is a reserved word, so outside a comment, a string or a
# guillemet identifier a token of that spelling is the keyword; it is one
# wherever it sits on a line (at the start as Aeneas writes it, behind an
# attribute or `private`, after `set_option ... in`, after another command's
# last token) and it needs no whitespace after it (`axiom«x»`).
_SCOPE_TOKEN = re.compile(r"(?<![\w.«'])(?P<kw>namespace|section|end|axiom)(?![\w.'])")
# A name as written: dotted components, each plain or in guillemets.
_NAME = r"(?:«[^»\n]*»|[^\s:({\[«»])+"
_INLINE_NAME = re.compile(r"[ \t]*(" + _NAME + r")")
_ANY_NAME = re.compile(r"\s*(" + _NAME + r")")


def axiom_declarations(path):
    """`[(qualified name, type text)]` for every `axiom` the file declares,
    one entry per declaration and in source order.

    The qualified name is the name as written with the enclosing `namespace`
    applied (an `axiom tacenta_kdf.hkdf_sha256` inside `namespace tacenta_braid`
    is `tacenta_braid.tacenta_kdf.hkdf_sha256`, which is what the elaborated
    environment calls it), or as written after `_root_.`. A `private` axiom is
    marked, so it cannot be mistaken for a public one of the same name. The
    type text is everything after the name up to the end of the declaration
    (the next keyword below, or the next line that starts in column 0), with
    whitespace collapsed. Nothing is merged: two declarations of one name are
    two entries.

    A file this reading cannot follow (an `end` that closes nothing, a
    `namespace` with no name, an `axiom` with no name) yields an entry whose
    name starts with `<unreadable:`, which no record or allowlist contains, so
    the file fails the comparison rather than passing on what was understood.
    """
    text = path.read_text()
    words = lean_code(text)
    names = lean_code(text, keep_names=True)
    tokens = list(_SCOPE_TOKEN.finditer(words))
    frames = []  # (kind, name) for every open `namespace` and `section`
    declarations = []

    def unreadable(why):
        declarations.append(("<unreadable: %s>" % why, ""))

    for index, token in enumerate(tokens):
        kind, after = token.group("kw"), token.end()
        if kind == "namespace":
            match = _INLINE_NAME.match(names, after)
            if match is None:
                unreadable("namespace without a name at offset %d" % token.start())
                continue
            frames.append(("namespace", match.group(1)))
        elif kind == "section":
            match = _INLINE_NAME.match(names, after)
            frames.append(("section", match.group(1) if match else ""))
        elif kind == "end":
            match = _INLINE_NAME.match(names, after)
            name = match.group(1) if match else ""
            if not frames or frames[-1][1] != name:
                unreadable("end %s does not close the innermost scope at offset %d"
                           % (name or "(anonymous)", token.start()))
            if frames:
                frames.pop()
        else:
            match = _ANY_NAME.match(names, after)
            if match is None:
                unreadable("axiom without a name at offset %d" % token.start())
                continue
            name = match.group(1)
            prefix = ".".join(n for k, n in frames if k == "namespace")
            if name.startswith("_root_."):
                qualified = name[len("_root_."):]
            else:
                qualified = prefix + "." + name if prefix else name
            if re.search(r"\bprivate\s*$", words[max(0, token.start() - 40):token.start()]):
                qualified = "private " + qualified
            limit = tokens[index + 1].start() if index + 1 < len(tokens) else len(words)
            column_zero = re.compile(r"\n(?=\S)").search(words, match.end(), limit)
            stop = column_zero.start() if column_zero else limit
            declarations.append((qualified, " ".join(names[match.end():stop].split())))
    return declarations


def generated_files():
    return sorted(GENERATED.glob("Tacenta*.lean"))


def axioms_declared(path):
    """The qualified names `axiom_declarations` finds, sorted, repeats kept."""
    return sorted(name for name, _ in axiom_declarations(path))


def opaque_externals():
    names = set()
    for p in generated_files():
        names.update(axioms_declared(p))
    return names


def is_external(name, externals):
    """Whether a name a pin prints is one of the declared externals.

    Only for the trust label a pin gets. `#print axioms` shortens a name by the
    namespaces the proof file has open (`zeroize.Zeroizing.new` for
    `tacenta_ratchet.zeroize.Zeroizing.new`), so a pin's name is the declared
    qualified name or the tail of one. Nothing that decides whether an axiom is
    allowed uses this: the allowlist and the audit comparison use the qualified
    names, exactly."""
    return any(name == e or e.endswith("." + name) for e in externals)


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


def committed_tree_hash(commit, rel):
    """Hash a source tree as it existed at ``commit``.

    The normal zone hash is computed from the working tree so a refresh can be
    prepared before the manifest is committed. The recorded generation commit
    gives the check one consistency fact: the recorded source hash must be the
    hash of that source at the named revision. This does not prove that Aeneas
    ran or that the generated bytes came from that source; only regeneration
    and diffing can establish that.
    """
    try:
        names = run("git", "ls-tree", "-r", "--name-only", commit, "--", rel).splitlines()
    except subprocess.CalledProcessError:
        return None
    if not names:
        return None
    h = hashlib.sha256()
    for name in names:
        try:
            data = subprocess.run(
                ["git", "show", f"{commit}:{name}"],
                cwd=ROOT,
                capture_output=True,
                check=True,
            ).stdout
        except subprocess.CalledProcessError:
            return None
        h.update(name.encode())
        h.update(b"\0")
        h.update(data)
        h.update(b"\0")
    return h.hexdigest()


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
    Cargo's: a source directory named `target` deeper down is source).
    Dotfiles are included so this working-tree hash matches the committed-tree
    hash. Sorted, so the hash is a function of content alone."""
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


# Pins that may not be deleted, and pins that may be compiler-trusted. The
# manifest is regenerated from the source, so a pin block that is deleted leaves
# a smaller manifest that `--check` accepts, and a pin edited to list a
# compiler-trust axiom is recorded with the label `compiler` and accepted. These
# two lists are the part a regeneration cannot change: editing either is a
# change to this script, which shows in the diff.
REQUIRED_PINS = frozenset(
    ["Tacenta.UnitLifecycleT1." + n for n in (
        "encrypt_no_panic",
        "decrypt_no_panic",
        "decrypt_ratchet_no_panic",
        "establish_initiator_for_no_panic",
        "establish_responder_no_panic",
        "invariant_gives_preconditions",
    )]
    + ["Tacenta.SessionBraidReceiveVacuity." + n for n in (
        "decoderMessage_not_total",
        "braidReceiveContractsUnbounded_false",
        "decryptRatchetContractsUnbounded_false",
        "establishResponderContractsUnbounded_empty",
        "message_eq_messageP",
        "all_tr_refute",
    )]
    + ["Tacenta.SessionBraidReceiveRepair." + n for n in (
        "old_witness",
        "boundary_gt_max_codewords",
        "divCeilValue_shape_satisfiable",
        "decoderMessageTotal_is",
        "DivCeilValue_is",
        "old_witness_fails_bounded_premise",
        "old_witness_rejected_by_invariant",
        "decoderMessageTotal_of_truncate",
        "bounded_holds_unbounded_fails",
        "message_total_of_invariant",
        "boundary_exact",
        "mutant_premise_at_boundary_refuted",
    )]
    + ["Tacenta.SessionUnitDecoderBound." + n for n in (
        "add_chunk_keeps_needed",
        "clone_keeps_needed",
        "invariant_true_needed_le",
        "new_needed_le",
    )]
    + [
        "Tacenta.SessionUnitBraidImportInv.Braid.invariant_true_gives_decoders_bounded",
    ]
    # The Braid agreements of the Session unit: the witnesses that the six KEM and KDF agreements and
    # the laws have a model, the erasure halves that need no compiler-trust axiom, the state-level
    # witnesses, and the entry points with five defined-function hypotheses discharged.
    + ["Tacenta.UnitSatisfiabilityBraidAgreements." + n for n in (
        "braid_agreement_shapes_are_predicates",
        "braid_agreements_have_a_model",
    )]
    + ["Tacenta.UnitSatisfiabilityErasureAgrees." + n for n in (
        "erasureCloneAgrees",
        "erasureAgrees_iff_clauses",
        "erasureAgrees_encoder",
    )]
    + ["Tacenta.UnitSatisfiabilityBraidStates." + n for n in (
        "ingredients",
        "twelve_states",
        "six_receive_witnesses",
        "initiator_refines",
        "responder_refines",
    )]
    + ["Tacenta.UnitBraidEntryPoints." + n for n in (
        "defined_hypotheses_given_erasure",
        "Braid.receive_refines_given_erasure",
        "Braid.send_refines_given_erasure",
        "defined_hypotheses_of_laws",
        "Braid.receive_refines_of_laws",
        "Braid.send_refines_of_laws",
        "twelve_states_of_laws",
        "six_receive_witnesses_of_laws",
    )]
    # The Reed-Solomon proof that the translated erasure coder of the Session unit refines the model:
    # the nine statements of the plan and the two results of the glue. None rests on a compiler-trust
    # axiom.
    + ["Tacenta.UnitErasureRs." + n for n in (
        "K_weights",
        "K_coefficients",
        "K_evaluate",
        "K_algebra",
        "E_new",
        "E_next",
        "D_add",
        "D_message",
        "M_recover",
    )]
    + ["Tacenta.UnitErasureRs.Glue." + n for n in (
        "erasureAgrees_decoder",
        "erasureAgrees",
    )]
    # The field, kernel-only since the model's field lemmas stopped using `bv_decide` and
    # `native_decide`: the pins that hold that, so that deleting one is refused. None is on
    # COMPILER_TRUSTED_PINS below, so a compiler-trust axiom under one is refused too.
    + ["Model.Gf65536." + n for n in ("mul_assoc", "mul_inv_cancel")]
    + ["Model.Polynomial.interp_eq", "Tacenta.ErasureT3.mul_refines"]
    # The inhabitation results: every axiom pin of the six UnitSatisfiability modules. They
    # are the four records from an axiom base, the base's model, the erasure and ratchet fields
    # proved from named laws, the shapes bound to the real predicates, the faithful-`pop`
    # results, the controls and the evidence about the three zeroize fields. A pin outside this
    # list can be deleted with its claim and the manifest regenerated without a refusal.
    + ["Tacenta.UnitSatisfiabilityRecords." + n for n in (
        "stdLaws_real_iff",
        "ratchetLaws_of_base",
        "encrypt_contracts_of_axiom_base",
        "decrypt_contracts_of_axiom_base",
        "initiator_contracts_of_axiom_base",
        "responder_contracts_of_axiom_base",
        "records_of_axiom_base",
        "axiom_base_satisfiable",
        "axiom_base_satisfiable_for_total_rng",
    )]
    + ["Tacenta.UnitSatisfiabilityJoint." + n for n in (
        "all_shapes_are_predicates",
        "model_satisfies_all_axiom_shapes",
        "stdLaws_of_faithful",
        "model_Faithful",
        "model_StdLaws",
        "encrypt_iff_parts",
        "decrypt_iff_parts",
        "initiator_toParts_ofParts",
        "responder_toParts_ofParts",
        "encrypt_axiom_part_satisfiable",
        "decrypt_axiom_part_satisfiable",
        "initiator_axiom_part_satisfiable",
        "responder_axiom_part_satisfiable",
        "DecoderNewTotal_is",
        "decoderNewShape_of_stdLaws",
        "model_DecoderNew",
        "badRange_refutes",
        "badDeref_refutes_array",
        "badDeref_refutes_message_key",
        "badOptionClone_refutes",
        "badCap_refutes",
        "badSeal_refutes",
        "model_pop_empty",
        "model_capacity_ge",
        "model_truncate_is_take",
    )]
    + ["Tacenta.UnitSatisfiabilityErasure." + n for n in (
        "decoderAddChunk_total",
        "encoderNextChunk_total",
        "encoderClone_total",
        "decoderClone_total",
        "decoderNew_iff",
        "encoderNew_iff",
        "divCeil32_of_value",
        "decoderNew_of_divCeilValue",
        "encoderNew_of_divCeilValue",
    )]
    + ["Tacenta.UnitSatisfiabilityRatchet." + n for n in (
        "kdfRkTotal",
        "kdfCkTotal",
        "kdfInitTotal",
        "spqrRemoveSkippedAtTotal",
        "ratchetRemoveSkippedAtTotal",
        "setChainsLoopTotal",
        "clearChainsLoop0Total",
        "clearSkippedLoopTotal",
        "vecRetainTotal",
        "defined_fields_hold",
        "spqrRemoveSkippedAtTotal_false_of_noop_pop",
        "ratchetRemoveSkippedAtTotal_false_of_noop_pop",
        "ratchetRemoveSkippedAtTotal_forces_blanketU32",
        "setChainsLoopTotal_forces_asMut",
    )]
    + ["Tacenta.UnitSatisfiabilitySession." + n for n in (
        "vec_pop_satisfiable",
        "noop_pop_not_faithful",
        "VecPopLaw_is",
        "all_thirteen_contracts_satisfiable",
    )]
    + ["Tacenta.UnitSatisfiabilityZeroizeScope." + n for n in (
        "zeroize_failure_propagation_conflicts",
        "faithful_propagates",
        "faithful_refutes_unscoped",
        "faithful_satisfies_rest",
        "ArrayZeroizeU8Total_of_spqr",
        "ArrayZeroizeU8Total_of_braid",
        "VecZeroizeChainsTotal_of_vecRetain",
        "arrayZeroizeScoped_of_total",
        "VecZeroizeSkippedTotal_of_vecRetain",
    )]
    # The refutations of the dispatch layer's evidence hypotheses (`DispatchEvidenceVacuity`):
    # every axiom pin of the module. A pin outside this list can be deleted with its claim and
    # the manifest regenerated without a refusal.
    + ["Tacenta.DispatchEvidenceVacuity." + n for n in (
        "same_ephemeral_agreement_empty",
        "initialSameEphemeralEvidence_false",
        "codewordViewOf_false",
        "codewordViewOf_false_of_encoderNewTotal",
        "record_empty_of_nonempty_decoder",
        "record_empty_headerSent",
        "record_empty_ekSentCt1Received",
        "record_empty_noHeaderReceived",
        "record_empty_ct1Sampled_ek",
        "record_empty_ct1Sampled_ekCt1Ack",
        "record_empty_ct1Acknowledged",
        "keysSampled_receive_ct1_holds_chunk",
        "tripleConcreteEvidence_forces_constant_dhPublic",
        "aeadConcreteEvidence_forces_constant_dhPublic",
        "constant_dhPublic_false_of_publicKeyNotConstant",
        "tripleConcreteEvidence_false_of_publicKeyNotConstant",
        "aeadConcreteEvidence_false_of_publicKeyNotConstant",
        "oracleOf_kem_oracle_never_refuses",
        "oracleOf_kem_call_never_errs",
    )]
    # The Braid's preservation results: every axiom pin of the six BraidPreserve modules that have
    # one. They are the preservation theorems for the standalone Braid translation and, as a
    # count-checked port, for the session unit, the one law they add and its model, the unit's
    # decoder lemmas and decoded-Braid results, and the two receive corollaries. A pin outside this
    # list can be deleted with its claim and the manifest regenerated without a refusal. The
    # statement and definition pins in the same modules are not on any list.
    + ["Tacenta.BraidPreserve." + n for n in (
        "Braid.step_send_sized",
        "Braid.step_receive_sized",
        "State.clone_sized",
        "Braid.send_sized",
        "Braid.receive_sized",
        "Braid.commit_sized",
        "Braid.initiator_sized",
        "Braid.responder_sized",
        "Braid.Run.sized",
        "Braid.Constructed.sized",
        "State.sized_ct1_bounded",
        "Braid.Run.exists_initiator",
        "Braid.Run.exists_responder",
        "Braid.Run.exists_send",
    )]
    + ["Tacenta.SessionUnitBraidPreserve." + n for n in (
        "Braid.step_send_sized",
        "Braid.step_receive_sized",
        "State.clone_sized",
        "Braid.send_sized",
        "Braid.receive_sized",
        "Braid.commit_sized",
        "Braid.initiator_sized",
        "Braid.responder_sized",
        "Braid.Run.sized",
        "Braid.Constructed.sized",
        "State.sized_ct1_bounded",
        "Braid.Run.exists_initiator",
        "Braid.Run.exists_responder",
        "Braid.Run.exists_send",
    )]
    + ["Tacenta.BraidPreserveWitness." + n for n in (
        "newMsgLen_iff",
        "api_newMsgLen",
        "erasure_laws_satisfiable",
        "model_for_both_widths",
    )]
    + ["Tacenta.BraidPreserveCorollary." + n for n in (
        "Braid.Run.receive_no_panic",
        "Braid.Run.receive_refines",
    )]
    + ["Tacenta.SessionUnitBraidPreserveDecoder." + n for n in (
        "message_length_le",
        "Good.new",
        "Good.msg",
        "Good.add",
        "Good.clone",
    )]
    + ["Tacenta.SessionUnitBraidPreserveFacts." + n for n in (
        "sized_decoders_bounded",
        "invariant_true_gives_sized",
        "from_bytes_sized",
        "Braid.Run.sized_of_start",
        "Braid.Run.inv",
        "Braid.Run.receive_no_panic",
        "Braid.Run.receive_refines",
        "inv_not_sized",
        "TruncateLen_is",
        "truncateLen_model",
        "laws_model",
    )]
    # The headroom results: every axiom pin of the two UnitHeadroom modules.  They show the four headroom
    # records satisfiable, the exact numeric conditions they impose, what `Session::invariant` gives for
    # every session, and a session over fresh states that passes it.  A pin outside this list can be
    # deleted with its claim and the manifest regenerated without a refusal.
    + ["Tacenta.UnitHeadroomSatisfiable." + n for n in (
        "usize_max_ge",
        "plaintext_bound_at_widths",
        "freshTriple_headroom",
        "freshBraid_bounds",
        "decryptHeadroom_sessionOf_iff",
        "invariantPreconditions_sessionOf",
        "encryptHeadroom_sessionOf_iff",
        "initiatorHeadroom_iff",
        "responderHeadroom_iff",
        "decryptHeadroom_satisfiable",
        "encryptHeadroom_satisfiable",
        "encryptHeadroom_satisfiable_pending",
        "initiatorHeadroom_satisfiable",
        "responderHeadroom_satisfiable",
        "initiatorHeadroom_not_trivial",
        "responderHeadroom_not_trivial",
        "decryptHeadroom_not_trivial",
        "encryptHeadroom_not_trivial",
        "nonempty_privateKey_of_dhCodec",
        "nonempty_publicKey_of_dhCodec",
        "nonempty_derivedZeroizing",
        "encrypt_headroom_of_contracts",
        "decrypt_headroom_of_contracts",
        "initiator_headroom_of_contracts",
        "responder_headroom_of_contracts",
        "headroomInhabitants_is",
        "model_headroomInhabitants",
        "axiom_base_model",
        "headroom_of_axiom_base",
        "headroom_hypotheses_satisfiable",
    )]
    + ["Tacenta.UnitHeadroomInvariant." + n for n in (
        "validKeyShape_is",
        "model_validKeyShape",
        "optionEqU64Shape_is",
        "optionEqImpl_shape",
        "structural_sessionOf",
        "freshTriple_invariant",
        "freshBraid_invariant",
        "sessionOf_invariant",
        "emptyChainTable_fails_invariant",
        "epochZero_braid_fails_invariant",
        "emptyChain_headroom",
        "epochZero_bounds",
        "session_emptyChainTable_fails_invariant",
        "session_epochZero_fails_invariant",
        "structural_gives_ad",
        "invariant_gives_ad_length",
        "decryptHeadroom_of_invariant",
        "encryptHeadroom_iff_of_invariant",
        "invariant_session_meets_both",
        "invariant_session_of_axiom_base",
        "invariant_hypotheses_satisfiable",
    )]
    # The numeric-precondition modules: every axiom pin of the witnesses, the discharge theorems and the boundary
    # arithmetic. `scripts/check-precondition-witnesses.sh` holds the statements of the `sat_` and discharge theorems
    # to the signatures of the theorems they are about, and its table is the other half of this list.
    + ["Tacenta.NumericBoundary." + n for n in (
        "both_widths",
        "classical_store_cap_fits",
        "classical_skip_cap_fits",
        "spqr_chain_cap_fits",
        "spqr_skip_cap_fits",
        "ratchet_codec_cap_fits",
        "spqr_codec_cap_fits",
        "erasure_cap_fits",
        "erasure_room_exact_at_32",
        "clock_ceiling_excludes_only_parked",
        "epoch_ceiling_excludes_only_top",
    )]
    + ["Tacenta.NumericBoundaryLeaf." + n for n in (
        "ratchet_constants",
        "spqr_constants",
        "erasure_constants",
        "protobuf_constants",
        "code_matches_model",
        "max_events_is_parked",
        "clock_ceiling_summary",
    )]
    + ["Tacenta.NumericBoundaryTriple." + n for n in (
        "unit_ratchet_constants",
        "unit_spqr_constants",
        "unit_code_matches_model",
    )]
    + ["Tacenta.NumericBoundarySession." + n for n in (
        "session_unit_ratchet_constants",
        "session_unit_spqr_constants",
        "session_unit_erasure_constants",
        "session_unit_code_matches_model",
    )]
    + ["Tacenta.NumericShapeWitness." + n for n in (
        "usize_max_cases",
        "every_shape_is_satisfiable",
    )]
    + ["Tacenta.NumericWitnessLeaf." + n for n in (
        "sat_T1_receive_no_panic",
        "sat_T3_receive_refines",
        "sat_ImportInv_Ratchet_decoded_receive_refines",
        "sat_SpqrT1_receive_no_panic",
        "sat_SpqrT1_send_no_panic",
        "sat_SpqrT3_receive_refines",
        "sat_SpqrT3_send_refines",
        "sat_BraidT1_Braid_receive_no_panic",
        "sat_BraidT1_Braid_step_receive_no_panic",
        "sat_BraidT3_Braid_receive_refines",
        "sat_BraidT3_step_receive_refines",
        "sat_BraidT3_Braid_send_refines",
        "sat_BraidT3_step_send_refines",
        "spqrS_inv",
        "ratS_inv",
        "spqr_receive_premises_at_witness",
        "spqr_send_premises_at_witness",
        "spqr_advance_premises_at_witness",
        "spqr_maybe_advance_premises_at_witness",
        "spqr_clear_old_epochs_premises_at_witness",
        "ratchet_receive_premises_at_witness",
        "braid_receive_premises_at_witness",
        "braid_step_receive_premises_at_witness",
    )]
    + ["Tacenta.NumericWitnessTriple." + n for n in (
        "sat_UnitT1_receive_no_panic",
        "sat_UnitT3_receive_refines",
        "sat_UnitSpqrT1_receive_no_panic",
        "sat_UnitSpqrT1_send_no_panic",
        "sat_UnitSpqrT3_receive_refines",
        "sat_UnitSpqrT3_send_refines",
        "sat_UnitTripleT1_State_receive_no_panic",
        "sat_UnitTripleT1_State_send_no_panic",
        "sat_UnitTripleT3_receive_refines",
        "sat_UnitTripleT3_receive_refines_discharged",
        "sat_UnitTripleT3_send_refines",
        "sat_UnitTripleT3_send_refines_discharged",
    )]
    + ["Tacenta.NumericWitnessSession." + n for n in (
        "sat_SessionUnitT1_receive_no_panic",
        "sat_SessionUnitT3_receive_refines",
        "sat_SessionUnitRatchetImportInv_Ratchet_decoded_receive_refines",
        "sat_SessionUnitSpqrT1_receive_no_panic",
        "sat_SessionUnitSpqrT1_send_no_panic",
        "sat_SessionUnitSpqrT3_receive_refines",
        "sat_SessionUnitSpqrT3_send_refines",
        "sat_SessionUnitTripleT1_State_receive_no_panic",
        "sat_SessionUnitTripleT1_State_send_no_panic",
        "sat_SessionUnitTripleT3_receive_refines",
        "sat_SessionUnitTripleT3_receive_refines_discharged",
        "sat_SessionUnitTripleT3_send_refines",
        "sat_SessionUnitTripleT3_send_refines_discharged",
        "sat_SessionUnitBraidT1_Braid_receive_no_panic",
        "sat_SessionUnitBraidT1_Braid_step_receive_no_panic",
        "sat_SessionUnitBraidT3_Braid_receive_refines",
        "sat_SessionUnitBraidT3_step_receive_refines",
        "sat_SessionUnitBraidT3_Braid_send_refines",
        "sat_SessionUnitBraidT3_step_send_refines",
        "session_unit_spqrS_inv",
        "session_unit_ratS_inv",
        "session_unit_spqr_receive_premises_at_witness",
        "session_unit_spqr_send_premises_at_witness",
        "session_unit_spqr_advance_premises_at_witness",
        "session_unit_spqr_maybe_advance_premises_at_witness",
        "session_unit_spqr_clear_old_epochs_premises_at_witness",
        "session_unit_ratchet_receive_premises_at_witness",
        "session_unit_braid_receive_premises_at_witness",
        "session_unit_braid_step_receive_premises_at_witness",
        "triple_receive_premises_at_witness",
        "triple_send_premises_at_witness",
    )]
    + ["Tacenta.DecodedStateDischarge." + n for n in (
        "spqr_epoch_family",
        "spqr_receive_premises",
        "spqr_send_premises",
        "spqr_advance_premises",
        "spqr_maybe_advance_premises",
        "spqr_clear_old_epochs_premises",
        "ratchet_receive_premises",
        "braid_receive_premises",
        "braid_step_receive_premises",
    )]
    + ["Tacenta.SessionUnitDecodedStateDischarge." + n for n in (
        "session_unit_spqr_epoch_family",
        "session_unit_spqr_receive_premises",
        "session_unit_spqr_send_premises",
        "session_unit_spqr_advance_premises",
        "session_unit_spqr_maybe_advance_premises",
        "session_unit_spqr_clear_old_epochs_premises",
        "session_unit_ratchet_receive_premises",
        "session_unit_braid_receive_premises",
        "session_unit_braid_step_receive_premises",
        "triple_receive_premises",
        "triple_send_premises",
        "decrypt_headroom_of_invariant",
        "decrypt_ratchet_no_panic_of_invariant",
        "decrypt_no_panic_of_invariant",
    )]
    # The hypotheses of the leaf and three-leaf-unit theorems that are statements about translated
    # functions, proved from named laws about opaque constants, and the decoder acceptance witnesses.
    # Every axiom pin of the eight modules below.
    + ["Tacenta.SatisfiabilitySpqrLaws." + n for n in (
        "kdfRkTotal",
        "kdfCkTotal",
        "spqrRemoveSkippedAtTotal",
        "setChainsLoopTotal",
        "clearChainsLoop0Total",
        "clearSkippedLoopTotal",
        "vecRetainTotal",
        "defined_fields_hold",
        "removeSkippedAtAgrees",
        "setChainsAgrees",
        "clearOldEpochsAgrees",
        "vecRetainAgreesOfLaws",
        "vecRetainAgrees",
        "LawPop_is",
        "LawAsMut_is",
        "LawCapacity_is",
        "LawVecZeroize_is",
        "LawHkdf_is",
        "SpqrCodec_ZeroizingVecTotal_is",
        "zeroizing_vec_satisfiable",
        "laws_jointly_satisfiable",
        "defined_hyps_from_axiom_hyps",
        "spqr_zeroizeTotal_conflicts",
        "laws_of_shape",
        "hkdf_total_satisfiable",
        "pop_satisfiable",
        "capacity_satisfiable",
        "vec_zeroize_satisfiable",
        "vec_zeroize_conflicts",
    )]
    + ["Tacenta.SatisfiabilityRatchetLaws." + n for n in (
        "ratchetRemoveSkippedAtTotal",
        "LawPop_is",
        "LawBlanketU32_is",
        "ArrZU8_is",
        "RatchetCodec_ZeroizingVecTotal_is",
        "zeroizing_vec_satisfiable",
        "pop_satisfiable",
        "blanket_satisfiable",
        "arrZU8_satisfiable",
        "ratchet_laws_jointly_satisfiable",
    )]
    + ["Tacenta.SatisfiabilityBraidZeroize." + n for n in (
        "braid_arrayZeroizeTotal_conflicts",
    )]
    + ["Tacenta.UnitSatisfiabilityTripleLaws." + n for n in (
        "kdfRkTotal",
        "kdfCkTotal",
        "kdfInitTotal",
        "spqrRemoveSkippedAtTotal",
        "ratchetRemoveSkippedAtTotal",
        "setChainsLoopTotal",
        "clearChainsLoop0Total",
        "clearSkippedLoopTotal",
        "vecRetainTotal",
        "defined_fields_hold",
        "removeSkippedAtAgrees",
        "setChainsAgrees",
        "clearOldEpochsAgrees",
        "vecRetainAgreesOfLaws",
        "vecRetainAgrees",
        "LawPop_is",
        "LawAsMut_is",
        "LawCapacity_is",
        "LawVecZeroize_is",
        "LawBlanketU32_is",
        "LawHkdf_is",
        "laws_jointly_satisfiable",
        "laws_of_shape",
        "defined_hyps_from_axiom_hyps",
        "RoundTrips80_is",
        "roundTrips80_satisfiable",
        "TripleZeroizeTotal_is",
        "arrZ32_satisfiable",
        "arrZ32_of_general",
        "spqrZeroizeTotal_conflicts",
        "hkdf_total_satisfiable",
        "pop_satisfiable",
        "capacity_satisfiable",
        "vec_zeroize_satisfiable",
        "blanket_satisfiable",
        "vec_zeroize_conflicts",
    )]
    + ["Tacenta.SpqrFromBytesWitness." + n for n in (
        "spqr_from_bytes_accepts_witness",
        "spqr_from_bytes_establishes_inv_nonvacuous",
    )]
    + ["Tacenta.BraidFromBytesWitness." + n for n in (
        "braid_from_bytes_accepts_witness",
        "braid_from_bytes_establishes_inv_nonvacuous",
    )]
    + ["Tacenta.SessionUnitBraidFromBytesWitness." + n for n in (
        "braid_from_bytes_accepts_witness",
        "braid_from_bytes_establishes_inv_nonvacuous",
    )]
    + ["Tacenta.RatchetDecodedWitness." + n for n in (
        "ratchet_witness_events",
        "decoded_receive_refines_premises_satisfiable",
    )]
    # What a refused lifecycle call leaves behind (`UnitLifecycleAtomicity.lean`): the seven frame
    # results, each pinned by its axiom list and by its statement. They take no hypothesis about
    # any opaque operation, so a weaker statement is the only way one could become empty.
    + ["Tacenta.UnitLifecycleAtomicity." + n for n in (
        "decrypt_ratchet_err_leaves_state",
        "decrypt_ratchet_ok_writes",
        "decrypt_err_leaves_state",
        "decrypt_ok_writes",
        "establish_responder_err_leaves_store",
        "encrypt_err_leaves_state",
        "encrypt_ok_writes",
    )]
)
COMPILER_TRUSTED_PINS = frozenset(
    {
        "Proofs.Serialization.decode_encode_composite",
        "Tacenta.SessionT3.shared_secret_refines_some",
        "Tacenta.SpqrT3.receive_refines",
        "Tacenta.SpqrT3.send_refines",
        "Tacenta.UnitSpqrT3.receive_refines",
        "Tacenta.UnitSpqrT3.send_refines",
        "Tacenta.UnitTripleT3.receive_refines_discharged",
        "Tacenta.UnitTripleT3.send_refines_discharged",
        "Tacenta.UnitTripleT3.spqr_agrees_for",
    }
)

# The statement-pin floor: declarations whose STATEMENT is pinned by
# `#guard_msgs in #check @name`, and whose pin may not be deleted, commented out,
# left without its `#guard_msgs`, or given an option that makes it compare nothing.
# `REQUIRED_PINS` is the same floor for the `#print axioms` pins; a statement pin
# was held by the Lean build only, so deleting every one of them, or weakening a
# statement while keeping its axiom list, was accepted by every gate. The names
# are fully qualified, written as the pin writes them, in blocks keyed by module
# (one block per module, so a branch appends its own block and two branches do not
# touch the same lines). `check_statement_pins` states what counts as a pin.
# Removing a name is a change to this script and, because the verification manifest
# records the floor, to the manifest as well (`check_statement_floor_recorded`).
REQUIRED_STATEMENT_PINS = frozenset(
    ["Tacenta.DispatchEvidenceVacuity." + n for n in (
        "same_ephemeral_agreement_empty",
        "initialSameEphemeralEvidence_false",
        "codewordViewOf_false",
        "codewordViewOf_false_of_encoderNewTotal",
        "record_empty_of_nonempty_decoder",
        "record_empty_headerSent",
        "record_empty_ekSentCt1Received",
        "record_empty_noHeaderReceived",
        "record_empty_ct1Sampled_ek",
        "record_empty_ct1Sampled_ekCt1Ack",
        "record_empty_ct1Acknowledged",
        "keysSampled_receive_ct1_holds_chunk",
        "tripleConcreteEvidence_forces_constant_dhPublic",
        "aeadConcreteEvidence_forces_constant_dhPublic",
        "constant_dhPublic_false_of_publicKeyNotConstant",
        "tripleConcreteEvidence_false_of_publicKeyNotConstant",
        "aeadConcreteEvidence_false_of_publicKeyNotConstant",
        "oracleOf_kem_oracle_never_refuses",
        "oracleOf_kem_call_never_errs",
    )]
    + ["Tacenta.UnitSatisfiabilityRecords." + n for n in (
        "axiom_base_satisfiable",
        "axiom_base_satisfiable_for_total_rng",
        "records_of_axiom_base",
    )]
    + ["Tacenta.UnitSatisfiabilitySession." + n for n in (
        "vec_pop_satisfiable",
    )]
    # Every statement pin of the Braid preservation, shape-witness and other modules that were
    # on the tree when the floor was first applied to them; each branch adds its own block below.
    + ["Tacenta.BraidPreserve." + n for n in (
        "Braid.Constructed",
        "Braid.Constructed.sized",
        "Braid.Run",
        "Braid.Run.exists_initiator",
        "Braid.Run.exists_responder",
        "Braid.Run.exists_send",
        "Braid.Run.sized",
        "Braid.commit_sized",
        "Braid.initiator_sized",
        "Braid.receive_sized",
        "Braid.responder_sized",
        "Braid.send_sized",
        "Braid.sized",
        "Braid.step_receive_sized",
        "Braid.step_send_sized",
        "State.clone_sized",
        "State.sized",
        "State.sized_ct1_bounded",
    )]
    + ["Tacenta.BraidPreserveCorollary." + n for n in (
        "Braid.Run.receive_no_panic",
        "Braid.Run.receive_refines",
    )]
    + ["Tacenta.BraidPreserveDecoder." + n for n in (
        "Good",
        "Laws",
        "NewMsgLen",
        "Reach",
    )]
    + ["Tacenta.BraidPreserveWitness." + n for n in (
        "erasure_laws_satisfiable",
        "newMsgLen_iff",
    )]
    + ["Tacenta.NumericShapeWitness." + n for n in (
        "S01",
        "S02",
        "S03",
        "S04",
        "S05",
        "S06",
        "S07",
        "S08",
        "S09",
        "S10",
        "S11",
        "S12",
        "S13",
        "S14",
        "S15",
        "S16",
        "S17",
        "S18",
        "S19",
        "S20",
        "S21",
        "S22",
        "S23",
        "S24",
        "S25",
        "S26",
        "S27",
        "S28",
        "S29",
        "S30",
        "S31",
        "S32",
        "S33",
        "S34",
        "S35",
        "S36",
        "S37",
        "S38",
        "S39",
        "S40",
        "S41",
        "S42",
        "S43",
        "S44",
        "S45",
        "S46",
        "S47",
        "S48",
        "S49",
        "S50",
        "S51",
        "S52",
        "S53",
        "S54",
        "S55",
        "S56",
        "S57",
        "S58",
        "S59",
        "S60",
        "S61",
        "every_shape_is_satisfiable",
        "usize_max_cases",
    )]
    + ["Tacenta.SessionUnitBraidPreserve." + n for n in (
        "Braid.Constructed",
        "Braid.Constructed.sized",
        "Braid.Run",
        "Braid.Run.exists_initiator",
        "Braid.Run.exists_responder",
        "Braid.Run.exists_send",
        "Braid.Run.sized",
        "Braid.commit_sized",
        "Braid.initiator_sized",
        "Braid.receive_sized",
        "Braid.responder_sized",
        "Braid.send_sized",
        "Braid.sized",
        "Braid.step_receive_sized",
        "Braid.step_send_sized",
        "State.clone_sized",
        "State.sized",
        "State.sized_ct1_bounded",
    )]
    + ["Tacenta.SessionUnitBraidPreserveDecoder." + n for n in (
        "Good",
        "Good.new",
        "Laws",
        "TruncateLen",
    )]
    + ["Tacenta.SessionUnitBraidPreserveFacts." + n for n in (
        "Braid.Decoded",
        "Braid.Run.inv",
        "Braid.Run.receive_no_panic",
        "Braid.Run.receive_refines",
        "Braid.Run.sized_of_start",
        "Braid.Start",
        "TruncateLenShape",
        "TruncateLen_is",
        "from_bytes_sized",
        "inv_not_sized",
        "invariant_true_gives_sized",
        "laws_model",
        "sized_decoders_bounded",
        "truncateLen_model",
    )]
    # Statement pins added by the headroom and hypothesis-witness modules.
    + ["Tacenta.BraidFromBytesWitness." + n for n in (
        "braid_from_bytes_accepts_witness",
        "braid_from_bytes_establishes_inv_nonvacuous",
    )]
    + ["Tacenta.RatchetDecodedWitness." + n for n in (
        "decoded_receive_refines_premises_satisfiable",
        "ratchet_witness_events",
    )]
    + ["Tacenta.SatisfiabilityBraidZeroize." + n for n in (
        "PropagatesFailureBraid",
        "braid_arrayZeroizeTotal_conflicts",
    )]
    + ["Tacenta.SatisfiabilityRatchetLaws." + n for n in (
        "ArrZU8",
        "ArrZU8_is",
        "LawBlanketU32",
        "LawBlanketU32_is",
        "LawPop",
        "LawPop_is",
        "RatchetCodec_ZeroizingVecTotal_is",
        "arrZU8_satisfiable",
        "blanket_satisfiable",
        "pop_satisfiable",
        "ratchetRemoveSkippedAtTotal",
        "ratchet_laws_jointly_satisfiable",
        "zeroizing_vec_satisfiable",
    )]
    + ["Tacenta.SatisfiabilitySpqrLaws." + n for n in (
        "AsMutShape",
        "CapacityShape",
        "HkdfTotalShape",
        "LawAsMut",
        "LawAsMut_is",
        "LawCapacity",
        "LawCapacity_is",
        "LawHkdf",
        "LawHkdf_is",
        "LawPop",
        "LawPop_is",
        "LawVecZeroize",
        "LawVecZeroize_is",
        "LawZeroizing",
        "Laws",
        "LawsShape",
        "PopShape",
        "PropagatesFailure",
        "PropagatesFailureVec",
        "SpqrCodec_ZeroizingVecTotal_is",
        "VecZeroizeShape",
        "as_mut_satisfiable",
        "capacity_satisfiable",
        "clearChainsLoop0Total",
        "clearOldEpochsAgrees",
        "clearSkippedLoopTotal",
        "defined_fields_hold",
        "defined_hyps_from_axiom_hyps",
        "hkdf_total_satisfiable",
        "kdfCkTotal",
        "kdfRkTotal",
        "laws_jointly_satisfiable",
        "laws_of_shape",
        "pop_satisfiable",
        "removeSkippedAtAgrees",
        "setChainsAgrees",
        "setChainsLoopTotal",
        "spqrRemoveSkippedAtTotal",
        "spqr_zeroizeTotal_conflicts",
        "vecRetainAgrees",
        "vecRetainAgreesOfLaws",
        "vecRetainTotal",
        "vec_zeroize_conflicts",
        "vec_zeroize_satisfiable",
        "zeroizing_vec_satisfiable",
    )]
    + ["Tacenta.SessionUnitBraidFromBytesWitness." + n for n in (
        "braid_from_bytes_accepts_witness",
        "braid_from_bytes_establishes_inv_nonvacuous",
    )]
    + ["Tacenta.SpqrFromBytesWitness." + n for n in (
        "spqr_from_bytes_accepts_witness",
        "spqr_from_bytes_establishes_inv_nonvacuous",
    )]
    + ["Tacenta.UnitHeadroomInvariant." + n for n in (
        "decryptHeadroom_of_invariant",
        "emptyChain_headroom",
        "encryptHeadroom_iff_of_invariant",
        "epochZero_bounds",
        "invariant_hypotheses_satisfiable",
        "invariant_session_meets_both",
        "invariant_session_of_axiom_base",
        "sessionOf_invariant",
        "session_emptyChainTable_fails_invariant",
        "session_epochZero_fails_invariant",
    )]
    + ["Tacenta.UnitHeadroomSatisfiable." + n for n in (
        "decrypt_headroom_of_contracts",
        "encryptHeadroom_sessionOf_iff",
        "encrypt_headroom_of_contracts",
        "headroom_hypotheses_satisfiable",
        "headroom_of_axiom_base",
        "initiatorHeadroom_iff",
        "initiator_headroom_of_contracts",
        "responderHeadroom_iff",
        "responder_headroom_of_contracts",
    )]
    + ["Tacenta.UnitSatisfiabilityTripleLaws." + n for n in (
        "AsMutShape",
        "BlanketU32Shape",
        "CapacityShape",
        "HkdfTotalShape",
        "LawAsMut",
        "LawAsMut_is",
        "LawBlanketU32",
        "LawBlanketU32_is",
        "LawCapacity",
        "LawCapacity_is",
        "LawHkdf",
        "LawHkdf_is",
        "LawPop",
        "LawPop_is",
        "LawVecZeroize",
        "LawVecZeroize_is",
        "LawZeroizing",
        "Laws",
        "LawsShape",
        "PopShape",
        "PropagatesFailure",
        "PropagatesFailureVec",
        "RoundTrips80_is",
        "TripleZeroizeTotal_is",
        "VecZeroizeShape",
        "arrZ32_of_general",
        "arrZ32_satisfiable",
        "as_mut_satisfiable",
        "blanket_satisfiable",
        "capacity_satisfiable",
        "clearChainsLoop0Total",
        "clearOldEpochsAgrees",
        "clearSkippedLoopTotal",
        "defined_fields_hold",
        "defined_hyps_from_axiom_hyps",
        "hkdf_total_satisfiable",
        "kdfCkTotal",
        "kdfInitTotal",
        "kdfRkTotal",
        "laws_jointly_satisfiable",
        "laws_of_shape",
        "pop_satisfiable",
        "ratchetRemoveSkippedAtTotal",
        "removeSkippedAtAgrees",
        "roundTrips80_satisfiable",
        "setChainsAgrees",
        "setChainsLoopTotal",
        "spqrRemoveSkippedAtTotal",
        "spqrZeroizeTotal_conflicts",
        "vecRetainAgrees",
        "vecRetainAgreesOfLaws",
        "vecRetainTotal",
        "vec_zeroize_conflicts",
        "vec_zeroize_satisfiable",
    )]
)


def check_pin_lists(pins):
    """Refuse a lost required pin, an unlisted compiler-trusted pin and a repeat."""
    have = {p["theorem"] for p in pins}
    # `pinned_theorems` counts pin blocks, so a block copied under another
    # theorem's pin would keep the count while losing a pin.
    repeated = sorted(t for t, n in Counter(p["theorem"] for p in pins).items() if n > 1)
    problems = (
        ["theorems pinned more than once: " + ", ".join(repeated)] if repeated else []
    )
    problems += [
        f"`{t}` is on REQUIRED_PINS and has no axiom pin"
        for t in sorted(REQUIRED_PINS - have)
    ]
    problems += [
        f"`{p['theorem']}` is pinned as compiler-trusted and is not on "
        "COMPILER_TRUSTED_PINS"
        for p in pins
        if p["trust"] == "compiler" and p["theorem"] not in COMPILER_TRUSTED_PINS
    ]
    return problems


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
        # A pin block left inside a block comment or a string is still in the
        # file, but Lean never elaborates it, so it would count as a pin the
        # build does not hold.
        live_pairs = len(RAW_PIN.findall(lean_code(text)))
        if live_pairs != raw_pairs:
            raise SystemExit(
                f"{p}: {raw_pairs - live_pairs} `#guard_msgs in`/`#print axioms` "
                "pair(s) sit inside a comment or a string, where Lean does not "
                "check them"
            )
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
# The statement pins
#
# A statement pin is `#guard_msgs in` immediately followed by `#check @name` (or
# `#check name`, or `#print name`), with the expected message in the docstring
# above it. Lean's build compares the message, so the pin ties a claimed result to
# the statement it was written with. Nothing in the build requires the pin to
# exist: a deleted pin is a smaller file that builds. `REQUIRED_STATEMENT_PINS` is
# what requires it, and `check_statement_pins` is what decides a pin counts.
#
# What it reads, on the comment-, string- and character-literal-stripped text
# (`lean_code`, so `--` in a string, `/-` nested in a block comment and a pin inside
# a docstring are read the way Lean reads them):
#
#   * `#guard_msgs`, optionally `( options )`, then `in`, then a command that is
#     `#check` or `#print` followed by an optional `@` and exactly one name and
#     nothing else before the next command at column 0 (a `#check` of an
#     application or a term is not a pin of a name);
#   * the name must equal the floor name character for character, and the pin must
#     sit outside every `namespace`, `section` and `mutual` block, so no name
#     resolution is guessed at: the pins are written after the namespace's `end`,
#     with the full name;
#   * the `#guard_msgs` must be the whole command: when it is the argument of an
#     earlier `... in` (`#guard_msgs (drop error) in`, `set_option ... in`,
#     `open ... in`) the outer command can swallow the pin's mismatch or change what
#     the pin prints, so the pin is refused and is written as its own command;
#   * the options must still compare the `info` message `#check` prints. `#guard_msgs`
#     takes the first option that covers a message kind: `check` compares it, `drop`
#     discards it and `pass` prints it without comparing, and when options are given
#     and none covers `info` the message passes through unchecked. So `(drop info)`,
#     `(drop all)`, `(pass info)`, `(drop warning)` alone and `(drop all, check info)`
#     leave a pin that fails only if its docstring is non-empty, which is to say
#     they accept the pin with its docstring removed. `(check info, drop warning)`
#     and `(whitespace := normalized)` are accepted. `whitespace := lax` is refused:
#     it compares the message with its whitespace removed, so it is not the text the
#     build is claimed to compare. An option this reading does not know is refused,
#     so a new Lean option fails closed;
#   * the pin's module must be reachable by imports from an audit module (a file
#     named `AxiomAudit*.lean` that holds a `run_cmd Model.AxiomAudit.run` line), which
#     is `check-audit-reach.sh`'s rule read from the header text instead of
#     `lean --deps`. Lake builds every file under a library's globs whether or not
#     anything imports it, so a pin file outside the import closure is built; what
#     the reach rule refuses is a pin in a file that is in a scanned tree but built
#     by no library (and so never checked), and the one place that decides whether
#     an audit sees the module at all.
#
# What it cannot see: it reads text, not the elaborated environment. It does not
# know that the name resolves to a declaration of the shape the claim describes (the
# build does: the docstring holds the printed statement); it does not run Lean, so a
# pin that elaborates to a message that matches a docstring written to match it is
# as good as the build says; it does not read what a pin says, so a statement weakened
# together with its pin's expected message is accepted (the build compares the text;
# the diff of the pin shows the change); it does not follow `open`, a file-level
# `set_option` that elides the printed statement, a macro that expands to
# `#guard_msgs`, `#guard_msgs` written inside a `run_cmd`, or a header that is more
# than 20,000 characters long; a definition changed under an unchanged name changes
# no pin that mentions it by name; it reads the first-party trees in `PROOF_TREES`
# only; and it never decides that a pinned statement is the right one.
# ---------------------------------------------------------------------------

# `mutual` is closed by an `end` like a namespace and a section, so it is a frame too; without it
# the `end` of a `mutual` block would pop a `namespace` that is still open.
_FRAME_TOKEN = re.compile(r"(?<![\w.«'])(?P<kw>namespace|section|mutual|end)(?![\w.'])")
_PIN_HEAD = re.compile(r"(?<![\w.'«])#guard_msgs(?![\w.'!?])")
_WORD_IN = re.compile(r"in(?![\w.'!?])")
_PIN_NAME = re.compile(r"(?:«[^»\n]*»|[\w'!?.])+")
# A command ends at the end of the file or at the next command, which starts in column 0.
_COMMAND_END = re.compile(r"[ \t]*(?:\Z|\n(?:[ \t]*\n)*(?:[ \t]*\Z|\S))")
_SPEC_KIND = re.compile(r"(?:(drop|check|pass)\s+)?(info|warning|error|all)")
_SPEC_WHITESPACE = re.compile(r"whitespace\s*:=\s*(exact|normalized|lax)")
_SPEC_ORDERING = re.compile(r"ordering\s*:=\s*(exact|sorted)")
_AUDIT_CALL = re.compile(r"^run_cmd Model\.AxiomAudit\.run\b", re.M)


def _skip_space(text, i):
    while i < len(text) and text[i].isspace():
        i += 1
    return i


def _named_command(words, names, j, lenient=False):
    """Read `#check [@]name` or `#print [axioms] name` at `j`, a command that
    must end after the name (unless `lenient`, for the search of comments, where
    what follows is a comment's own text). `(command, name)`; `("other", None)`
    for any other command or a name followed by more text."""
    for keyword in ("#check", "#print"):
        if not words.startswith(keyword, j) or re.match(r"[\w'!?]", words[j + len(keyword):j + len(keyword) + 1]):
            continue
        k = _skip_space(words, j + len(keyword))
        command = "check" if keyword == "#check" else "print"
        if command == "check" and words.startswith("@", k):
            k = _skip_space(words, k + 1)
        elif command == "print":
            axioms = re.compile(r"axioms(?![\w.'!?])").match(words, k)
            if axioms:
                command = "print-axioms"
                k = _skip_space(words, axioms.end())
        name = _PIN_NAME.match(names, k)
        if name and (lenient or _COMMAND_END.match(words, name.end())):
            return command, name.group(0)
        return "other", None
    return "other", None


def guard_option_problem(options):
    """Why a `#guard_msgs` option list leaves a `#check` message uncompared, or
    None when it still compares it. See the block comment above."""
    if options is None:
        return None
    covers_info, any_filter = None, False
    for element in (e.strip() for e in options.split(",")):
        kind = _SPEC_KIND.fullmatch(element)
        if kind:
            any_filter = True
            if kind.group(2) in ("info", "all") and covers_info is None:
                covers_info = (kind.group(1) or "check", element)
            continue
        whitespace = _SPEC_WHITESPACE.fullmatch(element)
        if whitespace:
            if whitespace.group(1) == "lax":
                return ("`whitespace := lax` compares the message with its whitespace "
                        "removed, which is not the text the pin is claimed to hold")
            continue
        if _SPEC_ORDERING.fullmatch(element):
            continue
        return f"the option `{element}` is not one this gate reads, so it cannot say what is compared"
    if not any_filter:
        return None
    if covers_info is None:
        return ("no option covers `info`, so the message `#check` prints passes "
                "through without being compared")
    if covers_info[0] != "check":
        return (f"`{covers_info[1]}` is the first option that covers `info` and it does "
                f"not compare it, so the pin holds nothing")
    return None


def scan_statement_pins(words, names, scoped):
    """Every `#guard_msgs [options] in <command>` in `words` (`lean_code` of the
    file, or, with `scoped` false, the text with its comment markers blanked, to
    find pins that sit in comments), as dicts: `pos`, `command` (`check`, `print`, `print-axioms`, `other`), `name`,
    `options`, `frames` (the open `namespace`/`section` scopes, when `scoped`) and
    `cmd_pos`, where the command starts."""
    out = []
    tokens = list(_FRAME_TOKEN.finditer(words)) if scoped else []
    frames, ti = [], 0
    for head in _PIN_HEAD.finditer(words):
        while ti < len(tokens) and tokens[ti].start() < head.start():
            token, ti = tokens[ti], ti + 1
            if token.group("kw") == "end":
                if frames:
                    frames.pop()
            else:
                found = _INLINE_NAME.match(names, token.end())
                frames.append((token.group("kw"), found.group(1) if found and token.group("kw") != "mutual" else ""))
        j = _skip_space(words, head.end())
        options = None
        if words.startswith("(", j):
            close = words.find(")", j)
            if close < 0:
                continue
            options = " ".join(words[j + 1:close].split())
            j = _skip_space(words, close + 1)
        keyword = _WORD_IN.match(words, j)
        if keyword is None:
            continue
        j = _skip_space(words, keyword.end())
        command, name = _named_command(words, names, j, lenient=not scoped)
        # A pin that is the argument of an earlier `... in` (`#guard_msgs (drop error) in`,
        # `set_option pp... in`, `open ... in`) is not the outermost command: the outer one can
        # swallow the pin's own mismatch or change what the pin prints.
        k = head.start()
        while k > 0 and words[k - 1].isspace():
            k -= 1
        wrapped = words[max(0, k - 2):k] == "in" and not re.match(r"[\w.'!?]", words[k - 3:k - 2])
        out.append({"pos": head.start(), "command": command, "name": name,
                    "options": options, "frames": list(frames), "cmd_pos": j, "wrapped": wrapped})
    return out


def statement_pin_survey():
    """Every statement pin in the first-party Lean trees: `live` (Lean elaborates
    it), `raw_only` (the same shape inside a comment, docstring or string) and
    `unguarded` (a `#check name` or `#print name` that no `#guard_msgs` governs), each with its file
    and line; and `guards`, the count of every live `#guard_msgs ... in` command."""
    survey = {"live": [], "raw_only": [], "unguarded": [], "guards": 0}
    for p in proof_files():
        text = p.read_text()
        if "#guard_msgs" not in text and "#check" not in text:
            continue
        rel = str(p.relative_to(ROOT))
        words, names = lean_code(text), lean_code(text, keep_names=True)

        def located(d):
            return dict(d, file=rel, line=text.count("\n", 0, d["pos"]) + 1)

        live = scan_statement_pins(words, names, True)
        survey["guards"] += len(live)
        survey["live"] += [located(d) for d in live]
        seen = {d["pos"] for d in live}
        # The same text with the comment markers (`--`, `/-`, `/--`, `-/`) blanked, so a
        # pin that sits in a comment reads as a pin; offsets are unchanged.
        bare = re.sub(r"/-+|-+/|--+", lambda m: " " * len(m.group()), text)
        survey["raw_only"] += [located(d) for d in scan_statement_pins(bare, bare, False)
                               if d["pos"] not in seen]
        governed = {d["cmd_pos"] for d in live}
        for m in re.finditer(r"(?<![\w.'«])#(?:check|print)(?![\w'!?])", words):
            if m.start() in governed:
                continue
            command, name = _named_command(words, names, m.start())
            if command in ("check", "print"):
                survey["unguarded"].append(located({"pos": m.start(), "name": name,
                                                    "command": command}))
    return survey


def module_name(rel):
    """`tacenta-proofs/translation/Translation/X.lean` -> `Translation.X`."""
    for package in ("tacenta-proofs/translation/", "tacenta-proofs/", "tacenta-model/"):
        if rel.startswith(package):
            return rel[len(package):-len(".lean")].replace("/", ".")
    return None


def _module_path(module):
    package = {"Model": "tacenta-model", "Properties": "tacenta-model",
               "Proofs": "tacenta-proofs", "Translation": "tacenta-proofs/translation"
               }.get(module.split(".")[0])
    if package is None:
        return None
    path = ROOT / package / (module.replace(".", "/") + ".lean")
    return path if path.exists() else None


def lean_imports(path):
    """The modules a file's header imports, read from its first 20,000 characters."""
    with open(path, encoding="utf-8", errors="replace") as handle:
        head = lean_code(handle.read(20000))
    pos = 0
    keyword = re.compile(r"\s*(?:module|prelude)(?![\w.'])").match(head)
    if keyword:
        pos = keyword.end()
    found = []
    pattern = re.compile(r"\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?(\S+)")
    while True:
        match = pattern.match(head, pos)
        if match is None:
            return found
        found.append(match.group(1))
        pos = match.end()


def audit_reach():
    """The first-party modules the audit modules import, directly or not: a file
    named `AxiomAudit*.lean` holding a `run_cmd Model.AxiomAudit.run` line is an
    audit module. The Lean-backed `check-audit-reach.sh` fixes the audit modules by
    name and asks Lean for the imports; this reads the same graph from the header."""
    todo = [module_name(str(p.relative_to(ROOT))) for p in proof_files()
            if p.name.startswith("AxiomAudit") and _AUDIT_CALL.search(lean_code(p.read_text()))]
    reached = set()
    while todo:
        module = todo.pop()
        if module is None or module in reached:
            continue
        reached.add(module)
        path = _module_path(module)
        if path is not None:
            todo.extend(lean_imports(path))
    return reached


def check_statement_pins(survey=None, reached=None):
    """Refuse a statement pin on `REQUIRED_STATEMENT_PINS` that is absent, inside a
    comment or a string, not under `#guard_msgs`, given options that compare
    nothing, the argument of an earlier `... in`, written inside a `namespace`,
    a `section` or a `mutual` block, or in a module no audit module imports.
    One message per floor name, naming it."""
    survey = survey or statement_pin_survey()
    if reached is None:
        reached = audit_reach()
    problems = []
    for name in sorted(REQUIRED_STATEMENT_PINS):
        head = f"`{name}` is on REQUIRED_STATEMENT_PINS and"
        candidates = [d for d in survey["live"]
                      if d["name"] == name and d["command"] in ("check", "print")]
        reasons = []
        for d in candidates:
            where, why = f"{d['file']}:{d['line']}", None
            if guard_option_problem(d["options"]):
                why = (f"its `#guard_msgs ({d['options']})` at {where} is vacuous: "
                       + guard_option_problem(d["options"]))
            elif d.get("wrapped"):
                why = (f"its `#guard_msgs` at {where} is the argument of an earlier `... in`, which "
                       "can swallow its mismatch or change what it prints; write the pin as its own command")
            elif d["frames"]:
                scope = ".".join(n for _, n in d["frames"] if n) or "section"
                why = (f"its statement pin at {where} sits inside `{scope}`; write it after "
                       "`end` with the full name, so no name resolution is guessed")
            elif module_name(d["file"]) not in reached:
                why = (f"its statement pin is in {d['file']}, which no audit module imports "
                       "(check-audit-reach.sh holds the same rule)")
            else:
                reasons = None
                break
            reasons.append(why)
        if reasons is None:
            continue
        if reasons:
            problems += [f"{head} {r}" for r in reasons]
            continue
        commented = [d for d in survey["raw_only"]
                     if d["name"] == name and d["command"] in ("check", "print")]
        loose = [d for d in survey["unguarded"] if d["name"] == name]
        if commented:
            problems.append(
                f"{head} its statement pin at {commented[0]['file']}:{commented[0]['line']} sits "
                "inside a comment, a docstring or a string, where Lean does not check it")
        elif loose:
            problems.append(
                f"{head} `#{loose[0]['command']} {name}` at {loose[0]['file']}:{loose[0]['line']} is not "
                "under `#guard_msgs in`, so the build compares nothing")
        else:
            problems.append(
                f"{head} has no statement pin: no active `#guard_msgs in` followed by "
                f"`#check @{name}` or `#print {name}` exists in the first-party Lean trees")
    return problems


def check_statement_floor_recorded():
    """Refuse a floor that is shorter than the one the committed verification
    manifest records, and refuse to run without that record. Regenerating the
    manifest after deleting a pin and its floor entry would otherwise write the
    smaller floor and pass; this makes the removal a hand edit of the manifest's
    `statement_pin_floor`, which a diff of a generated file shows. The check fails
    closed: a manifest that is missing, unreadable or without a floor list, a
    recorded floor that is empty and a script floor that is empty are each a
    problem, because each would otherwise leave nothing to compare with. What it
    cannot see is an edit of the script and of the manifest's list together, or the
    whole floor removed in those two edits; it does not compare with the base branch."""
    rel = (MANIFESTS / "verification-manifest.json").relative_to(ROOT)
    if not REQUIRED_STATEMENT_PINS:
        return ["REQUIRED_STATEMENT_PINS is empty, so no statement pin is required to exist"]
    path = ROOT / rel
    keep = f"; restore {rel} from git instead of regenerating without it"
    if not path.exists():
        return [f"{rel} is missing, so the statement-pin floor it records cannot be "
                "compared with REQUIRED_STATEMENT_PINS" + keep]
    try:
        document = json.loads(path.read_text())
    except (OSError, ValueError) as error:
        return [f"{rel} cannot be read ({type(error).__name__}), so the statement-pin floor "
                "it records cannot be compared with REQUIRED_STATEMENT_PINS" + keep]
    recorded = document.get("statement_pin_floor") if isinstance(document, dict) else None
    if not isinstance(recorded, list) or not all(isinstance(n, str) for n in recorded):
        return [f"{rel} has no `statement_pin_floor` list, so the statement-pin floor it records "
                "cannot be compared with REQUIRED_STATEMENT_PINS" + keep]
    if not recorded:
        return [f"{rel} records an empty `statement_pin_floor`, so it holds no floor to compare "
                "with REQUIRED_STATEMENT_PINS" + keep]
    return [
        f"`{n}` is on the statement-pin floor that verification-manifest.json records and "
        "is not on REQUIRED_STATEMENT_PINS: a floor entry is removed by editing both, and "
        "regenerating does not do it"
        for n in sorted(set(recorded) - REQUIRED_STATEMENT_PINS)
    ]


def statement_pin_inventory():
    """Print what the statement-pin survey found, for the report and for a reader
    who asks how many pins there are and which are not held."""
    survey, pins = statement_pin_survey(), axiom_pins()
    live = [d for d in survey["live"] if d["command"] in ("check", "print")]
    named = Counter(d["name"] for d in live)
    axiom = {p["theorem"] for p in pins}
    files = Counter(d["file"] for d in live)
    others = [d for d in survey["live"] if d["command"] == "other"]
    print(f"{survey['guards']} live `#guard_msgs ... in` commands: "
          f"{sum(1 for d in survey['live'] if d['command'] == 'print-axioms')} axiom pins, "
          f"{len(live)} statement pins, {len(others)} of another shape")
    print(f"statement pins by command: check {sum(1 for d in live if d['command'] == 'check')}, "
          f"print {sum(1 for d in live if d['command'] == 'print')}")
    print(f"statement pins with options: {sum(1 for d in live if d['options'])}; "
          f"inside a namespace or section: {sum(1 for d in live if d['frames'])}")
    print(f"shapes in a comment, docstring or string (not counted): "
          f"{sum(1 for d in survey['raw_only'] if d['command'] != 'other')}")
    print(f"`#check name` or `#print name` under no `#guard_msgs`: {len(survey['unguarded'])}")
    print(f"on REQUIRED_STATEMENT_PINS: {len(REQUIRED_STATEMENT_PINS)}; "
          f"statement pins not on it: {sorted(set(named) - REQUIRED_STATEMENT_PINS) or 'none'}; "
          f"floor names with no statement pin: {sorted(REQUIRED_STATEMENT_PINS - set(named)) or 'none'}")
    print(f"statement pins with no axiom pin: {sorted(set(named) - axiom) or 'none'}")
    print(f"axiom pins with no statement pin: {len(axiom - set(named))} of {len(axiom)}")
    print(f"statement pinned more than once: {sorted(n for n, c in named.items() if c > 1) or 'none'}")
    for file, count in sorted(files.items()):
        print(f"  {count:3d}  {file}")
    return 0


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
    re.compile(r"assembly-source: ([a-z0-9-]+)"),
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
            "Written only by `tacenta-proofs/scripts/attest.py --refresh-translation` "
            "after the source tree is committed and `scripts/run-aeneas.sh` has run "
            "on the pinned toolchain, and "
            "compared against by every other mode. A green `attest.py --check` "
            "establishes that each generated Translation/Tacenta*.lean is a module "
            "run-aeneas.sh produces, is byte for byte the file recorded here, declares "
            "exactly the axioms recorded here (fully qualified names read from the "
            "text, one per declaration; no-sorry.sh compares the same record with "
            "what the axiom audit saw in the built environment), and that "
            "the Rust verified zone it was generated from, and the workspace inputs "
            "that shape every zone's extraction (Cargo.toml and its profiles, "
            "Cargo.lock, .cargo/, the kdf and kem crates), hash to what they hashed "
            "to when this was written, as recorded by whoever ran the toolchain. "
            "Where a zone is assembled rather than written (the Triple, Braid-and-erasure, "
            "and complete Session units), the record carries an `assembly` "
            "field naming the script and every leaf tree it was assembled from, "
            "with their hashes, and --check fails if any of them has moved since; "
            "each assembly script's --check mode is the separate question of whether "
            "the unit crate in the tree is what those leaves assemble to. It "
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


def _reject_duplicate_keys(pairs):
    seen = {}
    for key, value in pairs:
        if key in seen:
            raise ValueError("duplicate key %r" % key)
        seen[key] = value
    return seen


ALLOWLIST_NAME = re.compile(r"[A-Za-z0-9_.']+")
ALLOWLIST_RELATIVE = TRANSLATION_AXIOM_ALLOWLIST.relative_to(ROOT)


def translation_axiom_allowlist():
    """Read the recorded set of generated axioms: `{file: [(name, type)]}`,
    with the problems found in the file itself.

    ``translation-attestation.json`` is refreshable after a toolchain run, so
    it cannot on its own tell a newly emitted external from an axiom planted
    in a generated file before that refresh. This file is the second record:
    refreshing a translation never writes it, so a new declaration has to
    appear in a change to this file, which shows in the diff as a name and a
    type. Each entry is one declaration; two entries with the same name and
    type are two declarations.
    """
    if not TRANSLATION_AXIOM_ALLOWLIST.exists():
        return None, [
            f"{ALLOWLIST_RELATIVE} is missing: create it from the generated "
            "translation with `attest.py --write-axiom-allowlist`, then rerun the "
            "attestation gate"
        ]
    try:
        data = json.loads(
            TRANSLATION_AXIOM_ALLOWLIST.read_text(),
            object_pairs_hook=_reject_duplicate_keys,
        )
    except (OSError, ValueError) as exc:
        return None, [f"{ALLOWLIST_RELATIVE} is not valid JSON: {exc}"]
    if not isinstance(data, dict) or data.get("schema_version") != AXIOM_ALLOWLIST_SCHEMA_VERSION:
        return None, [
            f"{ALLOWLIST_RELATIVE} has unsupported schema_version "
            f"{data.get('schema_version') if isinstance(data, dict) else None!r}; "
            f"this script reads {AXIOM_ALLOWLIST_SCHEMA_VERSION}"
        ]
    files = data.get("generated_files")
    if not isinstance(files, dict):
        return None, [f"{ALLOWLIST_RELATIVE} has no generated_files object"]
    problems, entries = [], {}
    for rel, items in files.items():
        if not isinstance(items, list):
            problems.append(f"{rel} is not a list of declarations in the allowlist")
            continue
        pairs = []
        for item in items:
            if (not isinstance(item, dict) or set(item) != {"name", "type"}
                    or not isinstance(item["name"], str) or not isinstance(item["type"], str)):
                problems.append(f"{rel} has an allowlist entry that is not a name and a type")
                break
            if not ALLOWLIST_NAME.fullmatch(item["name"]):
                problems.append(
                    f"{rel} has an allowlist name with characters outside "
                    f"[A-Za-z0-9_.']: {item['name']!r}"
                )
            pairs.append((item["name"], item["type"]))
        else:
            if pairs != sorted(pairs):
                problems.append(f"{rel} has unsorted declarations in the allowlist")
            entries[rel] = pairs
    return entries, problems


def typed_declarations(path):
    return sorted(axiom_declarations(path))


def describe_declaration(pair):
    name, type_text = pair
    return name if not type_text else f"{name} {type_text[:110]}" + ("..." if len(type_text) > 110 else "")


def check_axiom_allowlist(current):
    """The generated files' declarations against the allowlist, as multisets of
    (qualified name, type text): what a file declares that the allowlist does
    not list, and what the allowlist lists that the file no longer declares."""
    allowlist, problems = translation_axiom_allowlist()
    if allowlist is None:
        return problems
    want_files = set(current["generated_files"])
    allowed_files = set(allowlist)
    for rel in sorted(allowed_files - want_files):
        problems.append(f"{rel} is in translation-axiom-allowlist.json but is not a generated file")
    for rel in sorted(want_files - allowed_files):
        problems.append(f"{rel} is a generated file with no entry in translation-axiom-allowlist.json")
    for rel in sorted(want_files & allowed_files):
        actual = Counter(typed_declarations(ROOT / rel))
        expected = Counter(allowlist[rel])
        added = sorted((actual - expected).elements())
        removed = sorted((expected - actual).elements())
        if added or removed:
            problems.append(
                f"{rel} declares axioms that differ from the allowlist "
                f"(added: {'; '.join(describe_declaration(a) for a in added) or 'none'}; "
                f"removed: {'; '.join(describe_declaration(r) for r in removed) or 'none'}): "
                "a change to the generated axioms needs a change to "
                "translation-axiom-allowlist.json (attest.py --write-axiom-allowlist), "
                "and refreshing translation-attestation.json does not supply one"
            )
    return problems


def write_axiom_allowlist():
    """Rewrite the allowlist from the generated files' text and say what
    changed. Refused in CI, where nothing may write a baseline."""
    if os.environ.get("GITHUB_ACTIONS") == "true":
        print("attest: --write-axiom-allowlist does not run in CI", file=sys.stderr)
        return 2
    previous, _ = translation_axiom_allowlist()
    files = {}
    for path in generated_files():
        files[str(path.relative_to(ROOT))] = [
            {"name": name, "type": type_text} for name, type_text in typed_declarations(path)
        ]
    unreadable = sorted(
        f"{rel}: {item['name']}" for rel, items in files.items()
        for item in items if item["name"].startswith("<unreadable")
    )
    if unreadable:
        report(unreadable, "refusing to record a file whose axioms cannot be read")
        return 1
    document = {
        "schema_version": AXIOM_ALLOWLIST_SCHEMA_VERSION,
        "_note": (
            "Every axiom the generated Translation/Tacenta*.lean files declare, one "
            "entry per declaration, by fully qualified name and type text. Written "
            "only by `attest.py --write-axiom-allowlist`, which prints what it added "
            "and removed; `attest.py --check` compares the generated files with it "
            "as a multiset, and neither --refresh-translation nor any other mode "
            "writes it. A change to this file is a change to the generated "
            "translation's trust boundary and is meant to be its own commit."
        ),
        "generated_files": files,
    }
    changed = False
    for rel, items in files.items():
        old = Counter((previous or {}).get(rel, []))
        new = Counter((i["name"], i["type"]) for i in items)
        for pair in sorted((new - old).elements()):
            print(f"attest: allowlist + {rel.rsplit('/', 1)[-1]}: {describe_declaration(pair)}")
            changed = True
        for pair in sorted((old - new).elements()):
            print(f"attest: allowlist - {rel.rsplit('/', 1)[-1]}: {describe_declaration(pair)}")
            changed = True
    TRANSLATION_AXIOM_ALLOWLIST.write_text(json.dumps(document, indent=2) + "\n")
    print(f"attest: wrote {ALLOWLIST_RELATIVE} ({'changed' if changed else 'unchanged'})")
    return 0


def check_translation(current):
    """The tree against the recorded translation attestation.

    Each question is its own failure: does each generated file declare exactly
    the axioms the allowlist lists, by qualified name and type; is every file
    named like a generated one a module `run-aeneas.sh` produces; is every
    generated file the bytes that were recorded; does each declare exactly the
    axioms that were recorded (compared as multisets of qualified names, so a
    removed axiom fails as an added one does); is the Rust each was generated
    from still the Rust in the tree; for a zone that is assembled rather than
    written, are the assembly script and all its leaf trees still what they
    were; and are the workspace inputs that shape every zone's extraction still
    what they were. The last three are the ones that go stale by ordinary work,
    and their messages say what to do.
    """
    problems = check_axiom_allowlist(current)
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
    generated_at = recorded.get("generated_at_commit")
    if not generated_at:
        problems.append(
            "translation-attestation.json has no generated_at_commit; regenerate "
            "with scripts/run-aeneas.sh and re-run attest.py --refresh-translation"
        )
    if recorded.get("schema_version") != TRANSLATION_SCHEMA_VERSION:
        problems.append(
            f"translation-attestation.json has schema_version "
            f"{recorded.get('schema_version')!r}, and this script reads "
            f"{TRANSLATION_SCHEMA_VERSION}: regenerate with scripts/run-aeneas.sh on "
            "the pinned toolchain and re-run attest.py --refresh-translation"
        )
    generation_commit_problem = None
    if generated_at:
        commit_check = subprocess.run(
            ["git", "rev-parse", "--verify", f"{generated_at}^{{commit}}"],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        if commit_check.returncode != 0:
            generation_commit_problem = (
                f"translation-attestation.json names generation revision {generated_at}, "
                "which is not an available commit; fetch the repository's full history "
                "before running attest.py --check"
            )
        else:
            ancestor = subprocess.run(
                ["git", "merge-base", "--is-ancestor", generated_at, git_commit()],
                cwd=ROOT,
            )
            if ancestor.returncode != 0:
                generation_commit_problem = (
                    f"translation-attestation.json names generation commit {generated_at}, "
                    "which is not an ancestor of the current HEAD; regenerate from the "
                    "current history"
                )
    if generation_commit_problem:
        problems.append(generation_commit_problem)
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
        added = sorted((Counter(w["axioms"]) - Counter(r.get("axioms", []))).elements())
        removed = sorted((Counter(r.get("axioms", [])) - Counter(w["axioms"])).elements())
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
        if generated_at and w["zone"] and not generation_commit_problem:
            # An assembled unit is generated from its leaf trees, not from the
            # unit directory itself. Compare the recorded leaf provenance in
            # that case; ordinary zones compare their own source tree.
            source_hashes = (
                r.get("assembly", {}).get("sources", {})
                if w.get("assembly") is not None
                else {w["zone"]: r.get("zone_sha256")}
            )
            for source, recorded_hash in source_hashes.items():
                committed = committed_tree_hash(generated_at, source)
                if committed is None:
                    problems.append(
                        f"translation-attestation.json names generation commit "
                        f"{generated_at}, but it does not contain {source}; "
                        "regenerate after committing the source tree and re-run "
                        "attest.py --refresh-translation"
                    )
                elif committed != recorded_hash:
                    problems.append(
                        f"translation for {w['zone']} was recorded from source hash "
                        f"{str(recorded_hash)[:12]}... but generation commit "
                        f"{generated_at[:12]}... contains {committed[:12]}... for "
                        f"{source}; commit the source tree before refreshing the "
                        "translation attestation"
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
# tacenta_braid.tacenta_kdf.hkdf_sha256`. The record holds the same thing (the
# name as declared, `tacenta_kdf.hkdf_sha256`, with its `namespace` applied),
# so the two are compared for equality, as multisets.
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
    of the translation package, against the recorded per-file lists and the
    allowlist.

    `axiom_declarations` reads the text; the audit reads the environment the
    text elaborated to. A declaration the text scan does not recognise as an
    axiom (one produced by a macro, or added by a command) is an axiom to the
    audit, and a recorded axiom the environment no longer holds is missing to
    it. Names are compared for equality, fully qualified, and as multisets: a
    name in another namespace, or one that merely ends in a recorded name, is
    a different axiom. Both audit modules' output must be in the log:
    `Translation.AxiomAudit` covers the compatible generated modules; the
    Triple, Braid, Session, and lifecycle translations each have a separate
    audit because their generated names cannot share an environment with the
    other modules. The type of an axiom is not in the audit's output, so it is
    not compared here.
    """
    problems = []
    log = Path(log_path).read_text(errors="replace")
    seen = {}
    for module, name in AUDIT_LINE.findall(log):
        seen.setdefault(module, Counter())[name] += 1
    native = {(m, n) for m, n in AUDIT_NATIVE_LINE.findall(log)}
    if not TRANSLATION_MANIFEST.exists():
        return [f"{TRANSLATION_MANIFEST.relative_to(ROOT)} is missing"], 0
    recorded = json.loads(TRANSLATION_MANIFEST.read_text()).get("generated_files", {})
    allowlist, allowlist_problems = translation_axiom_allowlist()
    problems.extend(allowlist_problems)
    by_module = {
        r["module"]: (rel, {"recorded": Counter(r.get("axioms", [])),
                            "allowlist": Counter(
                                name for name, _ in (allowlist or {}).get(rel, []))
                            if allowlist is not None else None})
        for rel, r in recorded.items()
    }
    expected_modules = {f"Translation.{m}" for m in by_module}
    for module in sorted(expected_modules - set(seen)):
        # A module recorded with no axioms (the wire parser translates with
        # none) prints no lines; one recorded with some and printing none
        # was not audited, or its output was not captured.
        if sum(by_module[module.split(".", 1)[1]][1]["recorded"].values()):
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
        rel, baselines = by_module[module.split(".", 1)[1]]
        environment = seen[module]
        for label, baseline in baselines.items():
            if baseline is None:
                continue
            unrecorded = sorted((environment - baseline).elements())
            missing = sorted((baseline - environment).elements())
            if unrecorded or missing:
                problems.append(
                    f"{rel}: the axiom audit saw a different axiom list in the built "
                    f"environment from the {label} one (in the environment but not in "
                    f"the {label} list: {', '.join(unrecorded) or 'none'}; in the "
                    f"{label} list but not in the environment: {', '.join(missing) or 'none'})"
                )
    return problems, len(native)


def build():
    commit = git_commit()
    pins = axiom_pins()
    claim_list, problems = claims()
    declared = declared_theorems()
    problems += check_claims(claim_list, declared)
    problems += check_completeness(claim_list, pins)
    problems += check_pin_lists(pins)
    survey = statement_pin_survey()
    problems += check_statement_pins(survey)
    problems += check_statement_floor_recorded()
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
        # Every active statement pin, and the floor that may not shrink. The floor is
        # recorded so that removing a name from it shows in this file, and so that
        # `check_statement_floor_recorded` can refuse a regeneration that shortens it.
        "statement_pins": sorted(
            ({"theorem": d["name"], "file": d["file"], "command": d["command"]}
             for d in survey["live"] if d["command"] in ("check", "print")),
            key=lambda x: (x["file"], x["theorem"])),
        "statement_pin_floor": sorted(REQUIRED_STATEMENT_PINS),
        "counts": {
            "pinned_theorems": len(pins),
            "kernel_only": sum(1 for p in pins if p["trust"] == "kernel"),
            "statement_pins": sum(1 for d in survey["live"] if d["command"] in ("check", "print")),
            "statement_pin_floor": len(REQUIRED_STATEMENT_PINS),
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
                 | --write-axiom-allowlist | --compare-audit <lake build log>
                 | --statement-pin-inventory]

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
                         produce, and one whose axioms the allowlist does not
                         list, in which case it writes nothing.
  --write-axiom-allowlist
                         rewrite manifests/translation-axiom-allowlist.json
                         from the generated files and print each declaration
                         it added or removed. Not for CI; run it after
                         --refresh-translation when a regeneration changed
                         the axioms, and commit the result on its own.
  --statement-pin-inventory
                         print how many statement pins (`#guard_msgs in #check
                         @name`) the Lean trees hold, which are on the floor
                         REQUIRED_STATEMENT_PINS, and which are not held; reads
                         only, gates nothing
  --compare-audit <log>  compare the `audit-axiom:` lines the axiom audit
                         printed into a translation-package build log with the
                         per-file axiom lists recorded in
                         translation-attestation.json and the allowlist
                         (no-sorry.sh runs this)
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
    known = {"--check", "--check-translation", "--refresh-translation",
             "--write-axiom-allowlist", "--statement-pin-inventory"}
    if args - known or len(args) > 1:
        print(USAGE, file=sys.stderr)
        return 2
    if "--write-axiom-allowlist" in args:
        return write_axiom_allowlist()
    if "--statement-pin-inventory" in args:
        return statement_pin_inventory()
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
        # Decide before writing: a record is never written from a tree the
        # allowlist refuses, so a refused refresh leaves the last good record.
        refused = check_axiom_allowlist(current)
        if refused:
            report(refused, "refusing to record a translation the allowlist does not describe")
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
            f"{verification['counts']['statement_pins']} statement pins, "
            f"{verification['counts']['statement_pin_floor']} on the floor; "
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
