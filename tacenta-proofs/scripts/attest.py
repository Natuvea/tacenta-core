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
# rather than hand-listed, so a new external is classified the day it appears.
GENERATED = ROOT / "tacenta-proofs" / "translation" / "Translation"
AXIOM_DECL = re.compile(r"^axiom\s+(\S+)", re.M)


def opaque_externals():
    names = set()
    for p in sorted(GENERATED.glob("Tacenta*.lean")):
        names.update(AXIOM_DECL.findall(p.read_text()))
    return names


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
    if all(a in KERNEL_AXIOMS or a in externals for a in axioms):
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

    lakefile = ROOT / "tacenta-proofs/translation/lakefile.toml"
    if lakefile.exists():
        text = lakefile.read_text()
        m = re.search(r'name\s*=\s*"aeneas".*?rev\s*=\s*"([^"]+)"', text, re.S)
        if m:
            out["aeneas"] = m.group(1)

    # The Aeneas archive pin lives in the verification workflow and is
    # not read here.
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


def axiom_pins():
    """Collect every build-verified axiom pin in the repository.

    These are facts the Lean build already checks. If a pin were wrong the build
    would fail, so what this returns is as true as the build is.
    """
    pins = []
    externals = opaque_externals()
    for rel in PROOF_TREES:
        base = ROOT / rel
        if not base.exists():
            continue
        for p in sorted(base.rglob("*.lean")):
            if ".lake" in p.parts:
                continue
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


CLAIM_SECTION = re.compile(r"^## (.+)$", re.M)
# A section may name more than one file: the wire-encoding section says the
# ratchet is in one place and the encoding in another, in one sentence. Read
# every path it names rather than the first, which is what a reader does.
CLAIM_LOCATION = re.compile(r"Location:(.+?)(?:\n\n|\n-)", re.S)
CLAIM_PATH = re.compile(r"`([^`]+\.lean)`")
CLAIM_ITEM = re.compile(r"^- `([A-Za-z_][A-Za-z0-9_.']*)`", re.M)


def claims():
    """Parse CLAIMS.md into the theorem names it asserts, with their files."""
    p = ROOT / "tacenta-proofs" / "CLAIMS.md"
    text = p.read_text()
    out = []
    bounds = [(m.start(), m.group(1)) for m in CLAIM_SECTION.finditer(text)]
    bounds.append((len(text), None))
    for i in range(len(bounds) - 1):
        start, title = bounds[i]
        end = bounds[i + 1][0]
        if not title.lower().startswith("proved"):
            continue
        body = text[start:end]
        loc = CLAIM_LOCATION.search(body)
        files = CLAIM_PATH.findall(loc.group(1)) if loc else []
        for m in CLAIM_ITEM.finditer(body):
            out.append(
                {
                    "section": title,
                    "theorem": m.group(1),
                    "claimed_files": files,
                }
            )
    return out


def declared_theorems():
    """Every theorem name declared in the first-party proof trees."""
    decl = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?theorem\s+([A-Za-z_][A-Za-z0-9_.']*)", re.M)
    found = {}
    for rel in PROOF_TREES:
        base = ROOT / rel
        if not base.exists():
            continue
        for p in sorted(base.rglob("*.lean")):
            if ".lake" in p.parts:
                continue
            for m in decl.finditer(p.read_text()):
                found.setdefault(m.group(1), []).append(str(p.relative_to(ROOT)))
    return found


def check_claims(claim_list, declared):
    """Every claim must name a theorem that exists, in the file it says."""
    problems = []
    for c in claim_list:
        name = c["theorem"]
        where = declared.get(name)
        if not where:
            problems.append(
                f"CLAIMS.md claims `{name}` but no such theorem is declared"
            )
            continue
        wants = [f.lstrip("./") for f in c["claimed_files"]]
        if wants and not any(w.endswith(want) for want in wants for w in where):
            problems.append(
                f"CLAIMS.md places `{name}` in {' or '.join(wants)}, "
                f"found in {', '.join(where)}"
            )
    return problems


def check_completeness(claim_list, pins):
    """Every axiom-pinned theorem must appear in the ledger.

    Not every theorem belongs in a claims document; most are lemmas. A pin is
    the repository's own mark that a result is load-bearing, so "pinned but not
    claimed" is exactly the drift worth failing on: a ledger calling itself
    exact while a proof area that has landed is missing from it.
    """
    claimed = {c["theorem"] for c in claim_list}
    return [
        f"`{p['theorem']}` is axiom-pinned in {p['file']} but absent from CLAIMS.md"
        for p in pins
        if p["theorem"].split(".")[-1] not in claimed and p["theorem"] not in claimed
    ]


def check_zones_match_translation():
    """`VERIFIED_ZONES` and `run-aeneas.sh` name the same crates.

    The attestation is only worth reading if it hashes every crate the proofs
    are about, and the translation script is the authority on which those are.
    """
    script = (ROOT / "tacenta-proofs" / "scripts" / "run-aeneas.sh").read_text()
    # One `translate <leaf dir> <package> <llbc> <module>` line per zone.
    translated = set(re.findall(r"^translate\s+([a-z]+)\s", script, re.M))
    attested = {z.split("/")[-1] for z in VERIFIED_ZONES}
    return [
        f"run-aeneas.sh translates `tacenta-core/{c}` but VERIFIED_ZONES does not attest it"
        for c in sorted(translated - attested)
    ] + [
        f"VERIFIED_ZONES attests `tacenta-core/{c}` but run-aeneas.sh does not translate it"
        for c in sorted(attested - translated)
    ]


def build():
    commit = git_commit()
    pins = axiom_pins()
    claim_list = claims()
    declared = declared_theorems()
    problems = check_claims(claim_list, declared)
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
            "for that."
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


def main():
    check = "--check" in sys.argv
    verification, attestation, problems = build()

    if problems:
        print("attest: the claim ledger does not match the proofs", file=sys.stderr)
        for p in problems:
            print(f"  {p}", file=sys.stderr)
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
            return 1
        print(
            f"attest: manifests current "
            f"({verification['counts']['pinned_theorems']} pinned theorems, "
            f"{verification['counts']['kernel_only']} on the kernel alone)"
        )
        return 0

    MANIFESTS.mkdir(parents=True, exist_ok=True)
    for obj, path in targets:
        write(obj, path)
        print(f"attest: wrote {path.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
