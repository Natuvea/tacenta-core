#!/usr/bin/env bash
# Refuse to start a gate whose tools are not all present and runnable, before it runs anything.
#
#   bash tooling/check-gate-prerequisites.sh "<the gate's name>" <tool>...
#
# Each tool must be on PATH and must answer `<tool> --version` with exit 0, so a rustup proxy with no toolchain
# behind it, or a cargo whose rustfmt or clippy component is missing (`cargo-fmt`, `cargo-clippy`), counts as
# absent. `lake` is asked in `tacenta-model`, a directory whose `lean-toolchain` file chooses its Lean, because
# elan installed as `tooling/install-elan.sh` installs it has no default toolchain and answers nowhere else (the
# repository root has no `lean-toolchain`). If that pinned toolchain is not installed yet, elan fetches it during
# the check, the download the first `lake build` would make anyway; the probe runs under
# `tooling/retry-download.sh`, so a dropped connection is tried again as it is everywhere else. When elan says
# no default toolchain is configured, the message says so, rather than naming lake as missing. Every missing tool is named with how to provide it, and the script exits 1; nothing is skipped. With
# all present it prints one line naming them and exits 0.
#
# Why. A gate that reaches its last step before finding a tool missing has spent its time for nothing, and a
# step that skips when its tool is absent (the offline lockfile check does, in `tooling/ci.sh --fast`) would let
# a full run end green without having run it. `tooling/ci.sh` without `--fast` and
# `tooling/tests/run-gate-controls.sh` call this first, so on a machine without cargo the full gate fails at its
# first line, naming cargo. `tooling/ci.sh --fast` and `tooling/fast.sh` do not: they are the reduced checks,
# they say so, and they skip what they cannot run.
#
# The cases are in tooling/tests/run-check-fast-cases.sh (prereq-*).
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"

if [ "$#" -lt 2 ]; then
  echo "check-gate-prerequisites: give the gate's name and at least one tool" >&2
  exit 2
fi
gate="$1"
shift

how() {
  case "$1" in
    cargo) echo "install a stable Rust toolchain with rustup (https://rustup.rs) and put cargo on PATH; under 'env -i', set HOME so the rustup proxies find their toolchain, or put the toolchain's own bin directory (\$(rustc --print sysroot)/bin) on PATH" ;;
    cargo-fmt) echo "add the rustfmt component: rustup component add rustfmt" ;;
    cargo-clippy) echo "add the clippy component: rustup component add clippy" ;;
    lake) echo "install elan (tooling/install-elan.sh, or elan's own installer) and put ~/.elan/bin on PATH; lake is chosen per package by its lean-toolchain file, so no default toolchain is needed (the check asks lake in tacenta-model, which may fetch the toolchain its lean-toolchain file pins)" ;;
    python3) echo "install Python 3 and put python3 on PATH" ;;
    git) echo "install git and put it on PATH" ;;
    *) echo "install $1 and put it on PATH" ;;
  esac
}

# Ask a tool its version, output to the file named. lake is asked where a lean-toolchain file chooses its Lean.
probe() {  # tool, output file
  case "$1" in
    lake) (cd -- "$root/tacenta-model" && bash "$root/tooling/retry-download.sh" -- lake --version) >"$2" 2>&1 ;;
    *) "$1" --version >"$2" 2>&1 ;;
  esac
}

out="$(mktemp)"
trap 'rm -f "$out"' EXIT
missing=0
present=()
for tool in "$@"; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "check-gate-prerequisites: $gate needs $tool, which is not on PATH: $(how "$tool")" >&2
    missing=$((missing + 1))
  elif ! probe "$tool" "$out"; then
    if grep -qi 'no default toolchain' "$out"; then
      echo "check-gate-prerequisites: $gate needs $tool, which is on PATH but elan reports no default toolchain configured where it was asked: the check asks lake in tacenta-model, whose lean-toolchain file should choose Lean; restore tacenta-model/lean-toolchain (lake needs no default toolchain)" >&2
    else
      echo "check-gate-prerequisites: $gate needs $tool, which is on PATH but does not run ('$tool --version' failed): $(how "$tool")" >&2
    fi
    sed 's/^/  | /' "$out" | tail -n 5 >&2
    missing=$((missing + 1))
  else
    present+=("$tool")
  fi
done

if [ "$missing" -gt 0 ]; then
  echo "check-gate-prerequisites: $gate cannot run: $missing prerequisite(s) missing (above). This is a failure, not a skip; nothing was run." >&2
  exit 1
fi
echo "check-gate-prerequisites: $gate: ${present[*]} present"
