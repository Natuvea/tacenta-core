#!/usr/bin/env bash
# Refuse the Lean constructs that widen a proof's trust base without a warning.
#
# `no-sorry.sh` asks the compiler for incomplete declarations, and the
# `#print axioms` pins catch a theorem that starts resting on something new.
# Neither sees a *declaration* that is itself the new thing:
#
#   - `axiom`: a proposition assumed rather than proved, which `#print axioms`
#     reports only for the theorems that are pinned, and most are not.
#   - `@[implemented_by]` / `@[extern]`: the compiled program `native_decide`
#     runs is a different definition from the one the kernel reasons about.
#     This is the textbook route to proving `False` with `native_decide`.
#   - `partial def`: opts out of termination checking; `unsafe`: opts out of
#     everything.
#
# None is present in first-party Lean today, and the generated translation
# legitimately carries `axiom` declarations for the opaque externals (`opaque`
# in Aeneas's output), so the generated files are excluded and everything
# hand-written is scanned.
set -euo pipefail

cd "$(dirname "$0")/../.."

# Hand-written first-party Lean: the model, the property theorems, the
# model-layer proofs, and every translation-package file that is not a
# generated `Tacenta*.lean`.
files=$(
  {
    find tacenta-model/Model tacenta-model/Properties tacenta-proofs/Proofs \
      -name '*.lean' 2>/dev/null
    find tacenta-proofs/translation/Translation -name '*.lean' \
      -not -name 'Tacenta*.lean' 2>/dev/null
  } | sort
)

if [ -z "$files" ]; then
  echo "check-lean-constructs: no first-party Lean found" >&2
  exit 1
fi

status=0
# Leading whitespace allowed; a `--` comment mentioning the word is not a
# declaration, so require the keyword at the start of the statement.
pattern='^[[:space:]]*(axiom[[:space:]]|partial[[:space:]]+def[[:space:]]|unsafe[[:space:]]|@\[[^]]*(implemented_by|extern)[^]]*\])'
# `grep` exits 1 when nothing matches, which is the outcome wanted here.
found=$(echo "$files" | xargs grep -nE "$pattern" 2>/dev/null || true)
if [ -n "$found" ]; then
  echo "" >&2
  echo "REFUSING: hand-written Lean declares something the proof gates cannot see:" >&2
  echo "$found" | sed 's/^/    /' >&2
  echo "" >&2
  echo "An axiom, an implemented_by/extern attribute, a partial def or an unsafe" >&2
  echo "declaration widens the trust base of every theorem downstream of it" >&2
  echo "without a compiler warning. If one is genuinely needed, record it in" >&2
  echo "LIMITATIONS.md and add it to the allow-list in this script with the reason." >&2
  status=1
fi

count=$(echo "$files" | wc -l | tr -d ' ')
if [ "$status" -eq 0 ]; then
  echo "check-lean-constructs: $count first-party Lean files declare no axiom, implemented_by, extern, partial or unsafe"
fi
exit "$status"
