#!/usr/bin/env bash
# Regenerate the Lean translation on Linux x86_64, in a container, and require it to equal the committed tree.
#
#   regenerate-in-container.sh --check [--archive FILE] [--keep DIR]
#   regenerate-in-container.sh --compare DIR
#
# `scripts/run-aeneas.sh` has so far been run on a macOS arm64 build of the pinned Charon and Aeneas release. This
# script runs the same script with the release's own linux-x86_64 archive, in a container whose image is pinned by
# digest, on a copy of the tracked files, and then compares everything in the copy with the committed tree, byte
# for byte: the eleven generated `Translation/Tacenta*.lean`, the three assembled unit crates, `Cargo.lock` and
# every other tracked file. Any difference, missing file or file the run added exits nonzero. It never writes into
# the checkout, and it does not refresh any manifest: a difference is a finding to read, not something to
# overwrite.
#
# Run by hand. Hosted CI has no step that regenerates (the private verification workflow does, on its own
# runner), so this script is in no workflow and not in `tooling/required-steps.json`.
#
# What it pins, and where each pin is checked.
#   * The image, by digest: the ubuntu:24.04 index below, resolved to its linux/amd64 manifest. Docker verifies
#     the content against the digest on pull. Ubuntu 24.04 is used because the `charon` binary needs glibc 2.39.
#   * The release archive `aeneas-linux-x86_64.tar.gz` of `nightly-2026.07.22-b1214ca`, by SHA-256: the value
#     `REPRODUCING.md` states. It is checked on the host before the container starts, and again inside the
#     container before extraction, so nothing from the archive runs unchecked. A digest this script holds that
#     `REPRODUCING.md` or `run-aeneas.sh` does not hold is refused before either is used.
#   * rustup by version and SHA-256, and the Rust toolchain the archive's own `rust-toolchain` file names by the
#     SHA-256 of its dated channel manifest (the manifest lists the hash of every component).
#
# What it does not pin. The container fetches over the network: Ubuntu packages (ca-certificates, curl, gcc,
# libc6-dev, python3, from the archive of the day), the rustup and toolchain downloads above, and the crates in
# `Cargo.lock` (cargo verifies their checksums). The packages and the toolchain downloads are the parts a later
# date can change; the crates are fixed by the lockfile. The run records the installed package versions.
#
# Emulation. On an Apple-silicon Mac the container is a linux/amd64 container under Docker Desktop's emulation.
# The binaries are genuine x86_64 ELF, and the run is slow. Under Docker Desktop's QEMU user-mode emulation
# `rustc` faulted at start-up (every invocation, `rustc --version` included): QEMU placed the emulated process at
# addresses above 2^47, which a real x86_64 kernel does not do, and a guest base of 2^47 avoids the fault. The
# cause is inferred from the fault address, not established. So the container sets QEMU_GUEST_BASE=0x800000000000
# for every process in it. QEMU reads that variable and nothing else does, so it is inert on a native x86_64
# host and under Rosetta.
# If `docker pull` hangs waiting for a credential helper, point DOCKER_CONFIG at a directory holding `{}` as its
# `config.json`: the image is public.
#
# What a pass establishes. That `run-aeneas.sh`, with the release's linux-x86_64 binaries, produces from the
# tracked Rust the bytes that are committed. That is a run by whoever runs this, with the image and archive
# above; it is not a hosted-CI job and not, unless someone independent of the maintainer ran it, an independent
# one. It does not change what `SC-08-TRANSLATION-CHECKSUM` says: the recorded checksum cannot establish that a
# toolchain regenerated a file, and this script is how a reader establishes it for themselves.
#
# Modes.
#   --check         fetch (or take with --archive) the archive, check it, run the container, compare. Exit 0 only
#                   if the regenerated tree equals the tracked one.
#   --compare DIR   compare an already regenerated tree DIR with the tracked files and run nothing else. This is
#                   the comparison `--check` ends with, and what the negative control plants changes against.
#   --archive FILE  use FILE as the release archive instead of downloading it (its SHA-256 is still checked).
#   --keep DIR      keep the regenerated tree, the container log and the recorded versions under DIR.
#
# On a difference the regenerated tree is kept (its path is printed) so the hunks can be read.
set -euo pipefail

IMAGE="ubuntu@sha256:a853f94d226358a79c740cfc7bce0c289748f3fe3488d921d038ccd752c61b60"
# The linux/amd64 manifest the index above resolves to is sha256:f610ab94648195aa356059f5b41d6085c9d4d903c072430cdd1af7bdb646106b
# (recorded for the reader; Docker checks the index digest on pull).
AENEAS_RELEASE="nightly-2026.07.22-b1214ca"
ARCHIVE_NAME="aeneas-linux-x86_64.tar.gz"
ARCHIVE_URL="https://github.com/AeneasVerif/aeneas/releases/download/${AENEAS_RELEASE}/${ARCHIVE_NAME}"
ARCHIVE_SHA256="bc26c30daf92679b57c264c630710096bd9d4428e28795fe0638afdb0c2df65f"
RUSTUP_VERSION="1.29.1"
RUSTUP_INIT_SHA256="dda7234360b7f578ca8b0ddcb80145646fa61a67c1720a5abc7051b35c9fcb71"
RUST_CHANNEL="nightly-2026-06-01"
RUST_MANIFEST_SHA256="aaf1cb59b5996dd51831c9114b6e3a4a176e197851de91194b473117e142b935"
RUSTC_VERSION_LINE="rustc 1.98.0-nightly (14210df0e 2026-05-31)"

usage() {
  echo "usage: regenerate-in-container.sh --check [--archive FILE] [--keep DIR]" >&2
  echo "       regenerate-in-container.sh --compare DIR" >&2
  exit 2
}

mode=""
archive=""
keep=""
compare_dir=""
while [ $# -gt 0 ]; do
  case "$1" in
    --check) mode=check; shift ;;
    --compare) [ $# -ge 2 ] || usage; mode=compare; compare_dir="$2"; shift 2 ;;
    --archive) [ $# -ge 2 ] || usage; archive="$2"; shift 2 ;;
    --keep) [ $# -ge 2 ] || usage; keep="$2"; shift 2 ;;
    *) usage ;;
  esac
done
[ -n "$mode" ] || usage
if [ "$mode" = compare ] && { [ -n "$archive" ] || [ -n "$keep" ]; }; then usage; fi

root="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
work="$(mktemp -d)"
container="tacenta-regen-$$"
keep_work=0
started=0
cleanup() {
  if [ "$started" -eq 1 ]; then docker rm -f "$container" >/dev/null 2>&1 || true; fi
  if [ "$keep_work" -eq 0 ]; then rm -rf "$work"; else echo "regenerate-in-container: kept $work" >&2; fi
}
trap cleanup EXIT

sha256() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d' ' -f1; else shasum -a 256 "$1" | cut -d' ' -f1; fi
}

# The pins this script holds must be the ones the repository states, so that the two cannot drift apart.
check_pins() {
  grep -qF -- "$ARCHIVE_SHA256" "$root/tacenta-proofs/REPRODUCING.md" || {
    echo "regenerate-in-container: the archive digest $ARCHIVE_SHA256 is not the one REPRODUCING.md states" >&2
    return 1
  }
  grep -qF -- "AENEAS_RELEASE=\"\${AENEAS_RELEASE:-${AENEAS_RELEASE}}\"" "$root/tacenta-proofs/scripts/run-aeneas.sh" || {
    echo "regenerate-in-container: run-aeneas.sh does not pin ${AENEAS_RELEASE}" >&2
    return 1
  }
}

# compare_tree DIR REF TRACKED: DIR is a regenerated tree; it must hold exactly the files listed in TRACKED (one
# path per line), byte for byte equal to the same paths under REF. Files the run writes outside the tracked set by
# design (cargo's target directory, the LLBC files, the scratch output of run-aeneas.sh, Python caches) are not
# extras. `--compare` uses the checkout as REF; `--check` uses the snapshot it ran the container on, so an edit made
# to the checkout while the run is in progress cannot change the verdict.
compare_tree() {
  local dir="$1" ref="$2" tracked="$3" f total bad extra rc=0 shown=0
  local actual="$work/actual.txt" diffs="$work/diffs.txt" extras="$work/extras.txt"
  [ -d "$dir" ] || { echo "regenerate-in-container: $dir is not a directory" >&2; return 2; }
  (cd "$dir" && find . \( -path './tacenta-core/target' -o -path './tacenta-proofs/Generated' -o -name __pycache__ \) -prune -o \
    \( -type f -o -type l \) ! -name '*.llbc' -print | sed 's|^\./||' | LC_ALL=C sort) >"$actual"
  LC_ALL=C comm -13 "$tracked" "$actual" >"$extras"
  extra=$(wc -l <"$extras" | tr -d ' ')
  total=$(wc -l <"$tracked" | tr -d ' ')

  # Byte-for-byte comparison of every tracked file; the generated translation files are listed one by one.
  python3 - "$ref" "$dir" "$tracked" "$diffs" <<'PY'
import hashlib
import os
import sys

root, other, listing, diffs = sys.argv[1:5]
GENERATED = "tacenta-proofs/translation/Translation/Tacenta"


def digest(path):
    with open(path, "rb") as handle:
        return hashlib.sha256(handle.read()).hexdigest()


def read(path):
    with open(path, "rb") as handle:
        return handle.read()


print("%-34s %-14s %-14s %s" % ("generated file", "committed", "regenerated", "result"))
bad = []
for path in open(listing, encoding="utf-8").read().split("\n"):
    if not path:
        continue
    committed, regenerated = os.path.join(root, path), os.path.join(other, path)
    if not os.path.lexists(regenerated):
        state, theirs = "missing", "-"
    elif read(committed) != read(regenerated):
        state, theirs = "differs", digest(regenerated)[:12]
    else:
        state, theirs = "identical", None
    if state != "identical":
        bad.append("%s: %s" % (state, path))
    if path.startswith(GENERATED) and path.endswith(".lean"):
        mine = digest(committed)[:12]
        print("%-34s %-14s %-14s %s" % (os.path.basename(path), mine, theirs or mine, state.upper() if state != "identical" else state))
with open(diffs, "w", encoding="utf-8") as handle:
    handle.write("".join(line + "\n" for line in bad))
PY
  bad=$(wc -l <"$diffs" | tr -d ' ')

  if [ "$bad" -ne 0 ] || [ "$extra" -ne 0 ]; then
    rc=1
    echo "regenerate-in-container: FAIL: $bad of $total tracked files differ or are missing, $extra file(s) are not in the tree" >&2
    { sed 's/^/  /' "$diffs" | head -60 >&2; } || true
    if [ "$extra" -ne 0 ]; then
      echo "  not in the tree:" >&2
      { sed 's/^/    /' "$extras" | head -30 >&2; } || true
    fi
    while IFS= read -r f; do
      case "$f" in
        differs:*)
          f="${f#differs: }"
          [ "$shown" -lt 3 ] || continue
          shown=$((shown + 1))
          echo "--- first hunks of $f (committed, then regenerated)" >&2
          { diff -u "$ref/$f" "$dir/$f" 2>&1 | head -40 >&2; } || true ;;
      esac
    done <"$diffs"
  else
    echo "regenerate-in-container: PASS: all $total tracked files are equal to the regenerated tree, the generated translation files among them"
  fi
  return "$rc"
}

if [ "$mode" = compare ]; then
  git -C "$root" ls-files | LC_ALL=C sort >"$work/tracked.txt"
  compare_tree "$compare_dir" "$root" "$work/tracked.txt"
  exit $?
fi

# ---- --check ----
check_pins

# 1. The archive, checked before anything from it is used.
if [ -z "$archive" ]; then
  command -v curl >/dev/null 2>&1 || { echo "regenerate-in-container: curl is needed to fetch the archive" >&2; exit 1; }
  archive="$work/$ARCHIVE_NAME"
  echo "regenerate-in-container: fetching $ARCHIVE_URL"
  curl -fL --retry 3 -sS -o "$archive" "$ARCHIVE_URL"
fi
got="$(sha256 "$archive")"
if [ "$got" != "$ARCHIVE_SHA256" ]; then
  echo "regenerate-in-container: archive SHA-256 is $got, not $ARCHIVE_SHA256; refusing to use it" >&2
  exit 1
fi
echo "regenerate-in-container: archive SHA-256 $got"

command -v docker >/dev/null 2>&1 || { echo "regenerate-in-container: docker is needed" >&2; exit 1; }
if ! docker image inspect "$IMAGE" >/dev/null 2>&1; then
  echo "regenerate-in-container: pulling $IMAGE (linux/amd64)"
  docker pull --platform linux/amd64 "$IMAGE" >/dev/null
fi

# 2. The tracked files as they are on disk now, in a directory the container mounts read-only.
mkdir -p "$work/src" "$work/out"
git -C "$root" ls-files | LC_ALL=C sort >"$work/tracked.txt"
(cd "$root" && git ls-files -z | tar --null -T - -cf -) | tar -xf - -C "$work/src"
echo "regenerate-in-container: tree $(git -C "$root" rev-parse HEAD), $(wc -l <"$work/tracked.txt" | tr -d ' ') tracked files, $(git -C "$root" status --porcelain | wc -l | tr -d ' ') path(s) changed or untracked in the working tree"
echo "regenerate-in-container: host $(uname -sm), docker $(docker version --format '{{.Server.Version}} {{.Server.Os}}/{{.Server.Arch}}' 2>/dev/null || echo unknown)"

read -r -d '' inner <<'INNER' || true
set -eu
say() { printf 'regen: %s\n' "$*"; }
export QEMU_GUEST_BASE=0x800000000000
export DEBIAN_FRONTEND=noninteractive
[ "$(uname -m)" = x86_64 ] || { say "this container is not x86_64: $(uname -m)"; exit 1; }

echo "$ARCHIVE_SHA256  /in/aeneas.tar.gz" | sha256sum -c - >/dev/null || { say "archive digest mismatch inside the container"; exit 1; }
say "archive digest checked inside the container"

apt-get update -qq >/dev/null
apt-get install -y -qq --no-install-recommends ca-certificates curl gcc libc6-dev python3 >/dev/null
mkdir -p /opt/aeneas
tar -xzf /in/aeneas.tar.gz -C /opt/aeneas
[ -x /opt/aeneas/charon ] && [ -x /opt/aeneas/charon-driver ] && [ -x /opt/aeneas/aeneas ] || { say "the archive lacks a tool"; exit 1; }

channel=$(sed -n 's/^channel *= *"\(.*\)"/\1/p' /opt/aeneas/rust-toolchain)
[ "$channel" = "$RUST_CHANNEL" ] || { say "the archive names toolchain '$channel', not '$RUST_CHANNEL'"; exit 1; }
curl -fsSL -o /tmp/rustup-init "https://static.rust-lang.org/rustup/archive/$RUSTUP_VERSION/x86_64-unknown-linux-gnu/rustup-init"
echo "$RUSTUP_INIT_SHA256  /tmp/rustup-init" | sha256sum -c - >/dev/null || { say "rustup-init digest mismatch"; exit 1; }
chmod +x /tmp/rustup-init
/tmp/rustup-init -y --default-toolchain none --profile minimal --no-modify-path >/tmp/rustup-init.log 2>&1 || { tail -20 /tmp/rustup-init.log; exit 1; }
export PATH=/root/.cargo/bin:$PATH
curl -fsSL -o /tmp/channel.toml "https://static.rust-lang.org/dist/${channel#nightly-}/channel-rust-nightly.toml"
echo "$RUST_MANIFEST_SHA256  /tmp/channel.toml" | sha256sum -c - >/dev/null || { say "toolchain manifest digest mismatch"; exit 1; }
(cd /opt/aeneas && rustup toolchain install >/tmp/toolchain.log 2>&1 || { tail -20 /tmp/toolchain.log; exit 1; })
actual=$(cd /opt/aeneas && rustc --version)
[ "$actual" = "$RUSTC_VERSION_LINE" ] || { say "rustc is '$actual', not '$RUSTC_VERSION_LINE'"; exit 1; }

{
  echo "image: $(. /etc/os-release; echo "$PRETTY_NAME") $(uname -m), $(ldd --version | head -1)"
  echo "packages: $(dpkg-query -W -f='${Package}=${Version} ' ca-certificates curl gcc libc6-dev python3)"
  echo "gcc: $(gcc --version | head -1)"
  echo "python3: $(python3 --version)"
  echo "rustup: $(rustup --version 2>/dev/null | head -1)"
  echo "rustc: $actual"
  (cd /opt/aeneas && rustc -vV | sed 's/^/rustc -vV: /')
  echo "cargo: $(cd /opt/aeneas && cargo --version)"
  echo "charon: $(/opt/aeneas/charon version)"
  echo "aeneas: $(/opt/aeneas/aeneas -version)"
  echo "archive sha256: $ARCHIVE_SHA256"
  echo "toolchain manifest sha256: $RUST_MANIFEST_SHA256"
  for b in aeneas charon charon-driver; do echo "$b sha256: $(sha256sum /opt/aeneas/$b | cut -d' ' -f1)"; done
} >/out/versions.txt
cat /out/versions.txt

mkdir -p /work
cp -a /in/src /work/core
cd /work/core
say "run-aeneas.sh starts $(date -u +%FT%TZ)"
AENEAS_TOOLS=/opt/aeneas sh tacenta-proofs/scripts/run-aeneas.sh
say "run-aeneas.sh ends $(date -u +%FT%TZ)"
mkdir -p /out/tree
tar -C /work/core --exclude=./tacenta-core/target --exclude='*.llbc' --exclude=./tacenta-proofs/Generated -cf - . | tar -C /out/tree -xf -
say "regenerated tree written"
chown -R "$HOST_UID:$HOST_GID" /out
INNER

# 3. The run.
echo "regenerate-in-container: running run-aeneas.sh in a linux/amd64 container (slow when emulated)"
set +e
started=1
docker run --rm --name "$container" --platform linux/amd64 \
  -v "$archive:/in/aeneas.tar.gz:ro" -v "$work/src:/in/src:ro" -v "$work/out:/out" \
  -e HOST_UID="$(id -u)" -e HOST_GID="$(id -g)" \
  -e ARCHIVE_SHA256="$ARCHIVE_SHA256" -e RUSTUP_VERSION="$RUSTUP_VERSION" -e RUSTUP_INIT_SHA256="$RUSTUP_INIT_SHA256" \
  -e RUST_CHANNEL="$RUST_CHANNEL" -e RUST_MANIFEST_SHA256="$RUST_MANIFEST_SHA256" -e RUSTC_VERSION_LINE="$RUSTC_VERSION_LINE" \
  "$IMAGE" sh -c "$inner" regen 2>&1 | tee "$work/container.log"
status=${PIPESTATUS[0]}
set -e
if [ "$status" -ne 0 ]; then
  echo "regenerate-in-container: the container run failed (exit $status); nothing was compared" >&2
  keep_work=1
  exit 1
fi

# 4. The comparison.
rc=0
compare_tree "$work/out/tree" "$work/src" "$work/tracked.txt" || rc=$?
if [ -n "$keep" ]; then
  mkdir -p "$keep"
  cp -R "$work/out/." "$keep/"
  cp "$work/container.log" "$keep/container.log"
  echo "regenerate-in-container: kept the regenerated tree, versions.txt and container.log under $keep"
fi
if [ "$rc" -ne 0 ]; then keep_work=1; fi
exit "$rc"
