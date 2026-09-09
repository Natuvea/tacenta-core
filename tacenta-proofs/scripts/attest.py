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
`Translation/Tacenta*.lean`, its SHA-256, the `axiom` names it declares, and
the SHA-256 of the Rust verified zone it was generated from, with the Aeneas
pin. It is written only by `--refresh-translation`, which is meant to be run
immediately after `scripts/run-aeneas.sh`, and every other mode compares the
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

# The crates Charon and Aeneas translate. A proof about translated Rust is a
# proof about *these* bytes, so their hashes belong in the attestation.
#
# All seven, matching `scripts/run-aeneas.sh`, so that the attestation records
# bytes for every crate `CLAIMS.md` carries T1 and T3 for. If `run-aeneas.sh`
# gains a crate, this list must gain it too; the two are checked against each
# other below.
VERIFIED_ZONES = [
    "tacenta-core/ratchet",
    "tacenta-core/session",
    "tacenta-core/erasure",
    "tacenta-core/protobuf",
    "tacenta-core/spqr",
    "tacenta-core/braid",
    "tacenta-core/triple",
]

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
# An `axiom` line as Aeneas writes it, at any indentation and behind any
# attribute, so that a declaration moved inside a namespace block or given an
# attribute is still counted.
AXIOM_DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?axiom\s+(\S+)", re.M)


def generated_files():
    return sorted(GENERATED.glob("Tacenta*.lean"))


def axioms_declared(path):
    return sorted(set(AXIOM_DECL.findall(path.read_text())))


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

# Where the machine-checked claims live.
PROOF_TREES = [
    "tacenta-model",
    "tacenta-proofs/Proofs",
    "tacenta-proofs/translation/Translation",
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


def tree_hash(rel):
    """A content hash over a directory's tracked source.

    `git rev-parse HEAD:<path>` would be shorter, but it names the committed
    tree, and this script also has to describe a working tree that has not been
    committed yet. Hashing the files gives the same answer for the same content
    either way.
    """
    path = ROOT / rel
    if not path.exists():
        return None
    files = sorted(
        p for p in path.rglob("*")
        if p.is_file()
        and ".lake" not in p.parts
        and "target" not in p.parts
        and not p.name.startswith(".")
    )
    h = hashlib.sha256()
    for p in files:
        h.update(str(p.relative_to(ROOT)).encode())
        h.update(b"\0")
        h.update(p.read_bytes())
        h.update(b"\0")
    return {"sha256": h.hexdigest(), "files": len(files)}


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
        base = ROOT / rel
        if not base.exists():
            continue
        for p in sorted(base.rglob("*.lean")):
            if ".lake" in p.parts:
                continue
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
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*theorem\s+([A-Za-z_][A-Za-z0-9_.']*)",
    re.M,
)
NAMESPACE = re.compile(r"^(namespace|end|section)\b\s*(\S*)", re.M)


def declared_theorems():
    """Every theorem declared in the first-party proof trees, fully qualified
    by the `namespace` blocks around it, with the file it is in."""
    found = []
    for p in proof_files():
        text = p.read_text()
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
    attested = set(VERIFIED_ZONES)
    return [
        f"run-aeneas.sh translates `{c}` but VERIFIED_ZONES does not attest it"
        for c in sorted(translated - attested)
    ] + [
        f"VERIFIED_ZONES attests `{c}` but run-aeneas.sh does not translate it"
        for c in sorted(attested - translated)
    ]


# ---------------------------------------------------------------------------
# The translation attestation
# ---------------------------------------------------------------------------

def translation_attestation():
    """What the generated translation is, right now: per file, its hash, the
    axioms it declares, and the hash of the Rust it stands for."""
    zones = translated_modules()
    files = {}
    for p in generated_files():
        module = p.stem
        zone = zones.get(module)
        files[str(p.relative_to(ROOT))] = {
            "module": module,
            "sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
            "axioms": axioms_declared(p),
            "zone": zone,
            "zone_sha256": tree_hash(zone)["sha256"] if zone else None,
        }
    return {
        "schema_version": SCHEMA_VERSION,
        "_note": (
            "Written only by `tacenta-proofs/scripts/attest.py --refresh-translation`, "
            "immediately after `scripts/run-aeneas.sh` on the pinned toolchain, and "
            "compared against by every other mode. A green `attest.py --check` "
            "establishes that each generated Translation/Tacenta*.lean is byte for "
            "byte the file recorded here, declares exactly the axioms recorded here, "
            "and that the Rust verified zone it was generated from hashes to what it "
            "hashed to when this was written, as recorded by whoever ran the "
            "toolchain. It does not establish that the toolchain was run, or run "
            "honestly: that is checked by regenerating with run-aeneas.sh and "
            "diffing, which REPRODUCING.md describes."
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

    Three questions, each its own failure: is every generated file the bytes
    that were recorded; does each declare exactly the axioms that were
    recorded; and is the Rust each was generated from still the Rust in the
    tree. The last is the one that goes stale by ordinary work, and its
    message says what to do.
    """
    problems = []
    if not TRANSLATION_MANIFEST.exists():
        return [
            f"{TRANSLATION_MANIFEST.relative_to(ROOT)} is missing: run "
            "scripts/run-aeneas.sh on the pinned toolchain, then "
            "`attest.py --refresh-translation`"
        ]
    recorded = json.loads(TRANSLATION_MANIFEST.read_text())
    if recorded.get("schema_version") != SCHEMA_VERSION:
        problems.append("translation-attestation.json has an unrecognised schema_version")
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
    return problems


def build():
    commit = git_commit()
    pins = axiom_pins()
    claim_list, problems = claims()
    declared = declared_theorems()
    problems += check_claims(claim_list, declared)
    problems += check_completeness(claim_list, pins)
    problems += check_zones_match_translation()

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
        "proof_trees": {t: tree_hash(t) for t in PROOF_TREES},
    }
    return verification, attestation, problems


def write(obj, path):
    path.write_text(json.dumps(obj, indent=2, sort_keys=False) + "\n")


def report(problems, heading):
    print(f"attest: {heading}", file=sys.stderr)
    for p in problems:
        print(f"  {p}", file=sys.stderr)


USAGE = """usage: attest.py [--check | --check-translation | --refresh-translation]

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
                         value is that nobody runs it at any other time.
"""


def main():
    args = set(sys.argv[1:])
    known = {"--check", "--check-translation", "--refresh-translation"}
    if args - known or len(args) > 1:
        print(USAGE, file=sys.stderr)
        return 2
    check = "--check" in args
    check_only_translation = "--check-translation" in args
    refresh = "--refresh-translation" in args

    current = translation_attestation()
    if refresh:
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
