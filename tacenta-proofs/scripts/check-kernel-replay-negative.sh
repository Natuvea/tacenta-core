#!/usr/bin/env bash
# Show that the kernel replay `no-sorry.sh` runs refuses a declaration the kernel would refuse.
#
# `no-sorry.sh` replays every first-party module through the kernel with `leanchecker`, "the direct defence
# against environment hacking": `set_option debug.skipKernelTC true` adds a declaration on the elaborator's
# word alone, and nothing in the environment, no axiom audit and no pin, records that afterwards. The
# script's own verdict handling is held by `tooling/tests/run-proof-script-cases.sh` against a stub
# `leanchecker`; nothing showed that the real one, on the pinned toolchain, refuses such a module. This does.
#
# Two one-line modules are compiled in a temporary directory with the model package's toolchain:
#
#   Good   `theorem gateControlGood : True := trivial`; `leanchecker` must accept it
#   Bad    `False` "proved" by `True.intro`, added with the kernel check switched off. The elaborator accepts it,
#          so the module compiles; `leanchecker` must refuse it, naming the declaration and the kernel's
#          type mismatch
#
# It needs only the pinned Lean toolchain (no Mathlib, no build), and takes a few seconds.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/src/Probe" "$work/out/Probe"

cat >"$work/src/Probe/Good.lean" <<'LEAN'
theorem gateControlGood : True := trivial
LEAN
cat >"$work/src/Probe/Bad.lean" <<'LEAN'
import Lean
open Lean Elab Command

set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl (Declaration.thmDecl { name := `gateControlBad, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })
LEAN

cd "$root/tacenta-model"
for module in Good Bad; do
  lake env lean --root="$work/src" -o "$work/out/Probe/$module.olean" "$work/src/Probe/$module.lean"
done

LEAN_PATH="$work/out" lake env leanchecker Probe.Good >/dev/null 2>&1 \
  || { echo "kernel-replay negative: leanchecker refused a module that holds no bad declaration" >&2; exit 1; }

set +e
out="$(LEAN_PATH="$work/out" lake env leanchecker Probe.Bad 2>&1)"
rc=$?
set -e
if [ "$rc" -eq 0 ] || ! grep -qF "gateControlBad" <<<"$out" || ! grep -qF "declaration type mismatch" <<<"$out"; then
  echo "kernel-replay negative: leanchecker did not refuse a declaration added under debug.skipKernelTC (exit $rc)" >&2
  printf '%s\n' "$out" | head -10 >&2
  exit 1
fi
echo "kernel-replay negative: leanchecker accepts a sound module and refuses a declaration added with the kernel check off"
