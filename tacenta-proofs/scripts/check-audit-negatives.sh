#!/usr/bin/env bash
# Fail if `Model.AxiomAudit` accepts a planted declaration it should refuse,
# or refuses the one shape it is meant to allow.
#
# The audit is a gate, and a gate that has never been shown to close is a
# comment. Every other check here reports what the audit found in the real
# tree; this one asks whether the audit would find anything at all. It plants
# a declaration in a throwaway first-party module, runs the audit over it, and
# compares the outcome with what the rule says should happen.
#
# It plants one case for each of the seven kinds the audit refuses -- `axiom`,
# `opaque`, `unsafe`, `partial`, `implemented_by`, `extern` and
# `compiler-namespace` -- with the compiler-trust conditions covered case by
# case, plus the one shape the rule allows.
#
# It exists because the rule has been wrong before. `compilerTrust` waives its
# "the parent applies it" requirement for a compiler-trust axiom no first-party
# declaration mentions, since `decide +native` caches by statement and leaves
# the later duplicates declared and unreached. That waiver is only sound while
# "mentions" means what `#print axioms` means. An earlier version read values
# and not statements, so an axiom named in a theorem's *type* counted as
# unmentioned here and as a dependency there -- accepted by the gate while a
# theorem rested on it. Case `type-only-mention` is that exact declaration.
#
# The cases share one throwaway module path outside the package tree, rewritten
# and run in a fresh `lean` process for each, so a
# failed run leaves nothing behind that a later build or `check-audit-reach.sh`
# could pick up. The module name is what makes a probe first-party, so the
# probes live at `Translation/AuditProbe.lean` under a temporary root and are
# run from there; `lake env` supplies the toolchain and the import path.
#
# A test of a gate is itself a gate, so it was validated the same way: by
# breaking `Model/AxiomAudit.lean` one rule at a time, rebuilding, and checking
# that the intended case, and no other, came out red. Every rule below was
# unplanted at some point, and deleting it left this script reporting every
# case correct. The matrix, last run 2026-09-10:
#
#   rule removed from Model/AxiomAudit.lean   case that goes red
#   ---------------------------------------   ------------------
#   the `.opaqueInfo` arm                     opaque-definition
#   the `implementedByAttr` test              implemented-by
#   the `isExtern` test                       extern-attribute
#   `c.isPartial`                             partial-definition
#   `c.isUnsafe`                              unsafe-definition
#   the `.axiomInfo` arm                      plain-axiom
#   `c.type.getUsedConstants` in the          type-only-mention
#     mention set
#   the `compilerNamed n` test                the five compiler-namespace cases
#
# Redo it after changing either file. Each case must be red for its own reason:
# `partial def` also elaborates to an `opaque`, so a case that accepted any
# refusal would stay green when the rule it exists for was deleted. That is why
# the expectation names the reason and the match is against the audit's
# per-declaration line.
#
# Run from any directory. Needs the model package built.
set -euo pipefail

cd "$(dirname "$0")/../.."

root=$(mktemp -d)
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/Translation"
probe="$root/Translation/AuditProbe.lean"

pass=0
fail=0

# run <name> <expectation> -- the case's Lean is read from stdin.
# <expectation> is `accept`, or `refuse:<reason>` naming the reason the audit
# must give. Requiring the reason keeps a case from passing because the audit
# refused it for something incidental.
#
# The reason is matched against the audit's per-declaration lines, which read
# `  <name> (<module>): <reason>`, and not against the whole output. The
# closing blurb of a refusal names every reason the audit knows, so any
# refusal whatsoever contains the word `axiom`, and matching the whole output
# would turn `refuse:axiom` into a bare exit-status check.
#
# The match is a shell pattern rather than a pipe into `grep`. Under
# `pipefail`, `grep -q` exits at the first match and can leave the writer with
# SIGPIPE, which is a 141 the pipeline reports as failure -- a green case read
# as red on a large enough output.
run() {
  local name=$1 expect=$2 out status
  {
    echo "import Model.AxiomAudit"
    cat
    echo 'run_cmd Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation]'
  } > "$probe"

  set +e
  out=$(cd tacenta-proofs/translation \
        && lake env sh -c "cd '$root' && lean Translation/AuditProbe.lean" 2>&1)
  status=$?
  set -e

  if [ "$expect" = accept ]; then
    if [ $status -eq 0 ]; then
      pass=$((pass + 1)); return
    fi
    fail=$((fail + 1))
    echo "::error::audit-negatives: case '$name' should be accepted, and was refused:"
    echo "$out" | sed 's/^/    /'
    return
  fi

  local reason=${expect#refuse:}
  if [ $status -eq 0 ]; then
    fail=$((fail + 1))
    echo "::error::audit-negatives: case '$name' should be refused ($reason), and the audit accepted it."
    echo "$out" | sed 's/^/    /'
    return
  fi
  if [[ "$out" != *"(Translation.AuditProbe): $reason"* ]]; then
    fail=$((fail + 1))
    echo "::error::audit-negatives: case '$name' was refused, but not for '$reason':"
    echo "$out" | sed 's/^/    /'
    return
  fi
  pass=$((pass + 1))
}

# The one shape a hand-written module may declare, in the form the waiver
# exists for: named off a real parent in the same module, stating that a
# compiled Boolean evaluation returned true, and mentioned by nothing. If this
# case ever starts failing, the ten real orphans in the three-leaf unit are
# being refused and the build is broken, not tightened.
run orphan-is-waived accept <<'EOF'
theorem P : True := trivial
axiom P._native.decide.ax_1 : Decidable.decide True = true
EOF

# The same axiom, mentioned in a first-party declaration's statement rather
# than in its value. `#print axioms` reports it, so the waiver must not apply.
run type-only-mention refuse:compiler-namespace <<'EOF'
theorem P : True := trivial
axiom P._native.decide.ax_1 : Decidable.decide False = true
def Marker (_h : Decidable.decide False = true) : Prop := True
theorem Ref : Marker P._native.decide.ax_1 := trivial
EOF

# Mentioned in a value, by something other than its own parent. This is the
# case the requirement was written for, and the waiver must not reach it.
run value-mention-by-a-stranger refuse:compiler-namespace <<'EOF'
theorem P : True := trivial
axiom P._native.decide.ax_1 : Decidable.decide False = true
theorem Ref : Decidable.decide False = true := P._native.decide.ax_1
EOF

# An orphan is waived from the parent requirement, and from nothing else. Its
# name must still hang off a declaration that exists in the same module.
run orphan-without-a-parent refuse:compiler-namespace <<'EOF'
axiom NoSuchDeclaration._native.decide.ax_1 : Decidable.decide True = true
EOF

# ... and must still state that a compiled Boolean evaluation returned true.
# An axiom that merely wears the name is not a compiler-trust axiom.
run orphan-with-a-free-statement refuse:compiler-namespace <<'EOF'
theorem P : True := trivial
axiom P._native.decide.ax_1 : (2 : Nat) = 3
EOF

# `_unsafe_rec` is held to the compiler's shape and has no waiver of its own --
# `compilerAuxiliary` is not given the mention set at all, which is what "the
# waiver is not extended to `_unsafe_rec`" means. The code generator calls one
# by name whether or not anything mentions it, so an unreached one is not
# inert. This plants one beside a non-recursive `g`, which fails the shape on
# three counts, and would still be refused if the waiver were widened.
run unsafe-rec-shape refuse:compiler-namespace <<'EOF'
def g : Nat := 0
unsafe def g._unsafe_rec : Nat := 0
EOF

# The ordinary case, and the one the gate is mostly there for.
run plain-axiom refuse:axiom <<'EOF'
axiom Bad : True
EOF

# The audit refuses seven kinds of declaration and the five below are the rest
# of them. Each was unplanted once, and deleting its rule from
# `Model/AxiomAudit.lean` left this script reporting every case correct.

# A constant the kernel cannot unfold. `partial def` elaborates to one of
# these, which is why both are refused.
run opaque-definition refuse:opaque <<'EOF'
opaque Hidden : Nat := 0
EOF

# The compiled program is a different definition from the one the kernel
# reasons about, which is the textbook route to proving `False` by evaluation.
run implemented-by refuse:implemented_by <<'EOF'
def Real : Nat := 0
@[implemented_by Real] def Fake : Nat := 1
EOF

# The same, with the other definition outside Lean altogether.
run extern-attribute refuse:extern <<'EOF'
@[extern "probe_c_function"] def Outside : Nat := 0
EOF

# Opts out of termination checking.
run partial-definition refuse:partial <<'EOF'
partial def Spin (n : Nat) : Nat := Spin n
EOF

# Opts out of everything.
run unsafe-definition refuse:unsafe <<'EOF'
unsafe def Reckless : Nat := 0
EOF

if [ $fail -ne 0 ]; then
  echo "::error::audit-negatives: $fail of $((pass + fail)) planted cases came out wrong; Model.AxiomAudit is not refusing what it says it refuses."
  exit 1
fi
echo "audit-negatives: the audit called all $pass planted cases correctly"
