#!/usr/bin/env bash
# Fail if any first-party Lean module is outside the import closure of the
# audit modules that walk it.
#
# `Model.AxiomAudit` refuses an axiom, an opaque, an unsafe or partial
# declaration, an `implemented_by`/`extern`, or a compiler-namespace name
# outside the compiler's shape -- but only in the environment it is run in,
# which is whatever the invoking module imports. Each package carries one
# such module (`Properties/AxiomAudit.lean`, `Proofs/AxiomAudit.lean`,
# `Translation/AxiomAudit.lean`, and, for the three-leaf unit, which cannot
# share an environment with the rest, `Translation/AxiomAuditTripleUnit.lean`),
# each with a hand-maintained import
# list. A module missing from every list is built,
# has its `sorry`s scanned, is replayed by `leanchecker`, and is never
# walked: an axiom declared in it, or a planted compiler-trust axiom the
# text scan did not see, would reach every theorem importing it without the
# audit noticing. The generated `Translation/Tacenta*.lean` must be reached
# too, since the audit's `audit-axiom:` lines, which `no-sorry.sh` compares
# with the recorded manifest, are printed for the generated modules the
# audit sees and no others.
#
# This script asks Lean for each module's direct imports (`lean --deps`,
# which parses the header and prints the olean each import resolves to),
# computes the transitive closure from each package's audit modules over the
# first-party modules, and fails if any first-party source file in the
# package is not in it. `Vectors.lean`, the model package's vector-generator
# executable, is not a library module, imports nothing that proves anything
# and is imported by nothing; it is scanned textually by
# `check-lean-constructs.sh` and is outside this check.
#
# It also checks the other half of the audit's scope: that every audit is
# given the same first-party prefixes. `Model.AxiomAudit` decides what counts
# as a first-party module from the `prefixes` argument at its call site, and
# the waiver for an unmentioned compiler-trust axiom asks whether any
# first-party declaration mentions it. If one audit's prefixes named fewer
# namespaces than another's, a use could sit in a module that audit does not
# count as first-party, and the axiom would look unmentioned to the audit that
# declares it while never being walked by the audit that uses it. Reachability
# alone does not rule that out. Requiring one prefix list everywhere does.
#
# Run after the three builds (`no-sorry.sh` does), from any directory.
set -euo pipefail

cd "$(dirname "$0")/../.."

python3 - <<'PY'
import os, re, subprocess, sys

# The one prefix list every audit must be given.
PREFIXES = "#[`Model, `Properties, `Proofs, `Translation]"

# package directory -> (audit modules, source directories whose every .lean
# must be reached, root modules that must be reached)
PACKAGES = [
    ("tacenta-model", ["Properties/AxiomAudit.lean"], ["Model", "Properties"], []),
    ("tacenta-proofs", ["Proofs/AxiomAudit.lean"], ["Proofs"], []),
    ("tacenta-proofs/translation",
     ["Translation/AxiomAudit.lean", "Translation/AxiomAuditTripleUnit.lean",
      "Translation/AxiomAuditBraidUnit.lean"],
     ["Translation"], ["Translation.lean"]),
]
FIRST_PARTY = ("Model", "Properties", "Proofs", "Translation")

def module_of(path):
    """`Translation/BraidT3.lean` -> `Translation.BraidT3`."""
    return path[:-len(".lean")].replace("/", ".")

def sources(pkg, subdirs, roots):
    out = []
    for sub in subdirs:
        for name in sorted(os.listdir(os.path.join(pkg, sub))):
            if name.endswith(".lean"):
                out.append(f"{sub}/{name}")
    out.extend(r for r in roots if os.path.exists(os.path.join(pkg, r)))
    return out

def direct_imports(pkg, files):
    """Module -> its first-party direct imports, from `lean --deps` run once
    per file inside one `lake env` (the search path is set once per package)."""
    script = "\n".join(
        f'printf "@@ %s\\n" "{f}"; lean --deps "{f}" || exit 1' for f in files)
    res = subprocess.run(["lake", "env", "sh", "-c", script], cwd=pkg,
                         capture_output=True, text=True)
    if res.returncode != 0:
        sys.stderr.write(f"::error::lean --deps failed in {pkg}:\n{res.stderr}\n")
        sys.exit(1)
    deps, current = {}, None
    for line in res.stdout.splitlines():
        if line.startswith("@@ "):
            current = module_of(line[3:])
            deps[current] = set()
            continue
        # `.../lib/lean/Translation/BraidT3.olean` -> `Translation.BraidT3`
        m = re.search(r"/lib/lean/(.+)\.olean$", line.strip())
        if not m:
            continue
        mod = m.group(1).replace("/", ".")
        if mod.split(".")[0] in FIRST_PARTY:
            deps[current].add(mod)
    return deps

fail = False
total_reached = 0
summary = []
audit_call = re.compile(r"^run_cmd Model\.AxiomAudit\.run (.*)$", re.M)
n_calls = 0
for pkg, audits, _, _ in PACKAGES:
    for a in audits:
        path = os.path.join(pkg, a)
        if not os.path.exists(path):
            continue
        text = open(path).read()
        calls = audit_call.findall(text)
        # Any other way of writing the call -- parenthesised, indented, on the
        # end of another line -- is not matched by the pattern above and would
        # otherwise be invisible here. `check-lean-constructs.sh` refuses such
        # a line outright, and this counts it so that neither script is the
        # only thing standing between a second invocation and the tree.
        mentions = text.count("Model.AxiomAudit.run")
        if mentions != len(calls):
            fail = True
            sys.stderr.write(
                f"::error::{path}: mentions Model.AxiomAudit.run {mentions} "
                f"time(s) but only {len(calls)} are a plain `run_cmd "
                f"Model.AxiomAudit.run ...` line. An invocation written any "
                f"other way is not checked here.\n")
            continue
        if len(calls) != 1:
            fail = True
            sys.stderr.write(
                f"::error::{path}: expected exactly one `run_cmd "
                f"Model.AxiomAudit.run` line, found {len(calls)}\n")
            continue
        n_calls += 1
        if calls[0].strip() != PREFIXES:
            fail = True
            sys.stderr.write(
                f"::error::{path}: the audit runs with prefixes {calls[0].strip()}, "
                f"not {PREFIXES}. Every audit must be given the same first-party "
                f"prefixes, or a declaration one audit counts as first-party is "
                f"invisible to another and the unmentioned-axiom waiver can be "
                f"satisfied by a split rather than by disuse.\n")

for pkg, audits, subdirs, roots in PACKAGES:
    files = sources(pkg, subdirs, roots)
    required = {module_of(f) for f in files}
    deps = direct_imports(pkg, files)
    # Modules from another package (the model, imported into the proofs and
    # translation packages) are in the closure but not in this package's
    # required set; they need no `--deps` of their own here because their
    # own package's audit is what must reach them.
    reached, todo = set(), [module_of(a) for a in audits]
    for a in audits:
        if not os.path.exists(os.path.join(pkg, a)):
            sys.stderr.write(f"::error::{pkg}/{a} does not exist\n")
            fail = True
    while todo:
        m = todo.pop()
        if m in reached:
            continue
        reached.add(m)
        todo.extend(deps.get(m, ()))
    missing = sorted(required - reached)
    if missing:
        fail = True
        sys.stderr.write(
            f"::error::{pkg}: {len(missing)} first-party module(s) outside the import "
            f"closure of {', '.join(audits)}; the axiom audit never walks them:\n")
        for m in missing:
            sys.stderr.write(f"    {m}\n")
        sys.stderr.write(
            "  Add each to the audit module's imports (or, for the three-leaf unit, "
            "to Translation/AxiomAuditTripleUnit.lean).\n")
    n = len(required & reached)
    total_reached += n
    summary.append(f"{pkg} {n}")

if not fail:
    print(f"audit-reach: the {n_calls} audit modules, all with the same first-party "
          f"prefixes, reach all {total_reached} first-party modules "
          f"({', '.join(summary)})")
sys.exit(1 if fail else 0)
PY
