#!/usr/bin/env bash
# A hand-written proof may not name a symbol the translator invented.
#
# Charon and Aeneas emit auxiliary constants for side conditions --
# `kdf_ck._proof_3`, `kdf_ck._proof_5` and so on. Their names are the
# translator's to choose and to stop choosing: they are numbered by position, so
# an unrelated edit renumbers them, and they vanish entirely when the translator
# changes how a side condition is discharged.
#
# A hand-written proof that names one of them by name stops meaning anything
# the moment the translator stops emitting it: the reference becomes an unknown
# constant, elaboration fails, and Lean falls back to `sorryAx`, so the theorem
# proves nothing and only the `#guard_msgs` axiom pins say so.
#
# So the rule is structural rather than advisory: side conditions are supplied
# by the auto-param or proved in place, never borrowed from the generated
# module by name. This check costs nothing and runs anywhere, unlike the
# translation itself.
#
# Scope: the hand-written files only. `Tacenta*.lean` are generated and are
# expected to be full of these.
set -euo pipefail

here="$(cd "$(dirname "$0")/.." && pwd)"
cd "$here/tacenta-proofs/translation/Translation"

# `_proof_<n>` is Aeneas's auxiliary-constant shape. Deliberately narrow: other
# generated names -- `.induct`, `.eq_def` -- are stable parts of the surface
# Lean itself provides and are legitimate to use.
# Line comments are stripped before matching, so that prose *about* this rule
# -- including any note in `T1.lean` about these names -- does not trip the
# rule it describes. The code on a `code -- comment` line is still
# checked.
hits=""
for f in *.lean; do
  case "$f" in
    Tacenta*.lean) continue ;;
  esac
  match="$(awk '{ line = $0; sub(/--.*/, "", line); if (line ~ /_proof_[0-9]/) printf "%d:%s\n", NR, $0 }' "$f")"
  [ -n "$match" ] && hits="${hits}${f}:\n${match}\n"
done

if [ -n "$hits" ]; then
  echo "ERROR: a hand-written proof names a generated auxiliary constant." >&2
  echo "" >&2
  printf "%b" "$hits" >&2
  echo "" >&2
  echo "These names belong to the translator. It renumbers them on unrelated" >&2
  echo "edits and drops them when it changes how a side condition is" >&2
  echo "discharged, at which point the proof silently becomes \`sorry\`." >&2
  echo "Supply the side condition by auto-param or prove it in place." >&2
  exit 1
fi

echo "proof hygiene: no hand-written proof names a generated constant"
