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
# It exists because the rule has been wrong before. `compilerTrust` waives its
# "the parent applies it" requirement for a compiler-trust axiom no first-party
# declaration mentions, since `decide +native` caches by statement and leaves
# the later duplicates declared and unreached. That waiver is only sound while
# "mentions" means what `#print axioms` means. An earlier version read values
# and not statements, so an axiom named in a theorem's *type* counted as
# unmentioned here and as a dependency there -- accepted by the gate while a
# theorem rested on it. Case `type-only-mention` is that exact declaration.
#
# Each case runs in its own throwaway module outside the package tree, so a
# failed run leaves nothing behind that a later build or `check-audit-reach.sh`
# could pick up. The module name is what makes a probe first-party, so the
# probes live at `Translation/AuditProbe.lean` under a temporary root and are
# run from there; `lake env` supplies the toolchain and the import path.
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
# <expectation> is `accept`, or `refuse:<substring>` naming the reason the
# audit must give. Requiring the reason keeps a case from passing because the
# audit refused it for something incidental.
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
  if ! echo "$out" | grep -q "$reason"; then
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

# The waiver is not extended to `_unsafe_rec`: the code generator calls one by
# name whether or not anything mentions it, so an unreached one is not inert.
run unsafe-rec-orphan refuse:compiler-namespace <<'EOF'
def g : Nat := 0
unsafe def g._unsafe_rec : Nat := 0
EOF

# The ordinary case, and the one the gate is mostly there for.
run plain-axiom refuse:axiom <<'EOF'
axiom Bad : True
EOF

if [ $fail -ne 0 ]; then
  echo "::error::audit-negatives: $fail of $((pass + fail)) planted cases came out wrong; Model.AxiomAudit is not refusing what it says it refuses."
  exit 1
fi
echo "audit-negatives: the audit called all $pass planted cases correctly"
