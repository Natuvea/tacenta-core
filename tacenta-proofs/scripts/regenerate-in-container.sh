#!/usr/bin/env bash
# Regenerate the Lean translation on Linux x86_64, in a container, and require it to equal the tracked files.
#
#   regenerate-in-container.sh --check [--archive FILE] [--keep DIR]
#   regenerate-in-container.sh --compare DIR
#
# `scripts/run-aeneas.sh` has so far been run on a macOS arm64 build of the pinned Charon and Aeneas release. This
# script runs the same script with the release's own linux-x86_64 archive, in a container whose image is pinned by
# digest, on a copy of the tracked files, and then compares the tracked files with the copy, byte for byte and by
# executable bit. The run rewrites 29 of them: the eleven generated `Translation/Tacenta*.lean` and the 18 files of
# the three assembled unit crates. Those are the reproduction. The other tracked files, `Cargo.lock` among them, pass
# through the run; their equality shows that the run changed nothing else, not that anything regenerated them. Any
# difference, missing file, symlink or file the run added exits nonzero, and so does a comparison that could not be
# made. The script never writes into the checkout and refreshes no manifest: a difference is a finding to read, not
# something to overwrite.
#
# What the comparison is against. The tracked files as they are on disk, not as they are in HEAD: a working tree
# edited after HEAD is compared as edited. Both modes print how many tracked paths differ from HEAD, and a run on a
# tree where that is not zero says so in its PASS line.
#
# Run by hand. Hosted CI has no step that regenerates (the private verification workflow does, on its own runner),
# so this script is in no workflow and not in `tooling/required-steps.json`. Its control,
# `tooling/tests/run-regenerate-in-container-cases.sh`, starts no container and is run by `run-gate-controls.sh`.
#
# What it pins, and what is cross-checked. The image by digest (the ubuntu:24.04 index below; Docker verifies the
# content against the digest on pull; Ubuntu 24.04 because the `charon` binary needs glibc 2.39). The release archive
# `aeneas-linux-x86_64.tar.gz` of `nightly-2026.07.22-b1214ca` by SHA-256, checked on the host before the container
# starts and again inside it before extraction, so nothing from the archive runs unchecked. rustup by version and
# SHA-256. The script holds every one of these values and requires `REPRODUCING.md` to state the same image digest,
# archive digest, rustup-init digest, channel manifest digest and compiler version line, and `run-aeneas.sh` to
# pin the same release; a value that the repository does not state is refused before docker is used.
#
# What is not pinned. The Rust toolchain is installed by rustup from static.rust-lang.org, and its components are not
# pinned by digest. The script downloads the dated channel manifest a second time and checks its SHA-256, which shows
# what the server served at that moment; rustup installs from its own download of the manifest and not from the
# checked copy, so the check is a canary and does not bind the components. The installed compiler's version line is
# checked afterwards. The Ubuntu packages (ca-certificates, curl, gcc, libc6-dev, python3) come from the archive of
# the day, and so does the libc that `libc6-dev` requires; the crates are fixed by `Cargo.lock` (cargo verifies their
# checksums). The run records the installed package versions and the hash of the manifest rustup kept.
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
#                   if the regenerated tree equals the tracked files. Exit 1 on a difference or a failed run, 2 if the
#                   comparison could not be made.
#   --compare DIR   compare a tree DIR with the tracked files and run nothing else. This is the comparison `--check`
#                   ends with, and what the control plants changes against. The script cannot know that DIR was
#                   regenerated.
#   --archive FILE  use FILE as the release archive instead of downloading it (its SHA-256 is still checked).
#   --keep DIR      keep the regenerated tree, the container log and the recorded versions under DIR.
#
# Nothing is kept unless --keep is given. The work directory (the archive, a copy of the tracked files and the
# regenerated tree) is created under $TMPDIR and removed on exit, on success and on failure; on a difference the
# first hunks are printed, and --keep DIR keeps the whole regenerated tree for reading.
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
work="$(mktemp -d "${TMPDIR:-/tmp}/tacenta-regen.XXXXXX")"
# A name no other run on a shared daemon can share, and the id of the container this run started, if it started
# one: cleanup removes that container and nothing else.
container="tacenta-regen-$$-$RANDOM"
cidfile="$work/container.id"
cleanup() {
  if [ -s "$cidfile" ]; then docker rm -f "$(cat "$cidfile")" >/dev/null 2>&1 || true; fi
  case "$work" in */tacenta-regen.*) rm -rf "$work" ;; esac
}
trap cleanup EXIT

sha256() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d' ' -f1; else shasum -a 256 "$1" | cut -d' ' -f1; fi
}

# The values this script holds must be the ones the repository states, so that the two cannot drift apart.
check_pins() {
  local doc="$root/tacenta-proofs/REPRODUCING.md" what value
  case "$IMAGE" in
    *@sha256:*) ;;
    *) echo "regenerate-in-container: the image $IMAGE is not pinned by digest" >&2; return 1 ;;
  esac
  for pair in "image digest|${IMAGE##*@}" "archive digest|$ARCHIVE_SHA256" "rustup-init digest|$RUSTUP_INIT_SHA256" \
    "channel manifest digest|$RUST_MANIFEST_SHA256" "compiler version line|$RUSTC_VERSION_LINE" "channel|$RUST_CHANNEL"; do
    what="${pair%%|*}"
    value="${pair#*|}"
    grep -qF -- "$value" "$doc" || {
      echo "regenerate-in-container: the $what $value is not the one REPRODUCING.md states" >&2
      return 1
    }
  done
  grep -qF -- "AENEAS_RELEASE=\"\${AENEAS_RELEASE:-${AENEAS_RELEASE}}\"" "$root/tacenta-proofs/scripts/run-aeneas.sh" || {
    echo "regenerate-in-container: run-aeneas.sh does not pin ${AENEAS_RELEASE}" >&2
    return 1
  }
}

# dirty_count: how many tracked paths differ from HEAD.
dirty_count() { git -C "$root" status --porcelain --untracked-files=no | wc -l | tr -d ' '; }

# compare_tree DIR REF TRACKED LABEL: DIR must hold exactly the files listed in TRACKED (one path per line), each a
# regular file (not a link, not a directory) with the bytes and the executable bits of the same path under REF.
# Files the run writes outside the tracked set by design (cargo's target directory, the LLBC files, the scratch
# output of run-aeneas.sh, Python caches) are not extras. `--compare` uses the checkout as REF; `--check` uses the
# snapshot it ran the container on, so an edit made to the checkout while the run is in progress cannot change the
# verdict. Returns 0 if equal, 1 if they differ, 2 if the comparison could not be made. It is called under `||`,
# which suspends `set -e`, so every command that can fail says what then happens.
compare_tree() {
  local dir="$1" ref="$2" tracked="$3" label="$4" f total bad extra counted rc=0 shown=0
  local actual="$work/actual.txt" diffs="$work/diffs.txt" extras="$work/extras.txt"
  local unmade="regenerate-in-container: the comparison could not be made; nothing was compared"
  [ -d "$dir" ] || { echo "regenerate-in-container: $dir is not a directory; nothing was compared" >&2; return 2; }
  rm -f "$actual" "$diffs" "$extras"
  (cd "$dir" && find . \( -path './tacenta-core/target' -o -path './tacenta-proofs/Generated' -o -name __pycache__ \) -prune -o \
    \( -type f -o -type l \) ! -name '*.llbc' -print | sed 's|^\./||' | LC_ALL=C sort) >"$actual" || { echo "$unmade" >&2; return 2; }
  LC_ALL=C comm -13 "$tracked" "$actual" >"$extras" || { echo "$unmade" >&2; return 2; }
  extra=$(wc -l <"$extras" | tr -d ' ')
  total=$(wc -l <"$tracked" | tr -d ' ')

  # Byte and mode comparison of every tracked file; the generated translation files are listed one by one. The
  # result file is written last and starts with the number of paths compared.
  python3 - "$ref" "$dir" "$tracked" "$diffs" <<'PY' || { echo "regenerate-in-container: the comparison did not run to the end; nothing was compared" >&2; return 2; }
import hashlib
import os
import sys

root, other, listing, diffs = sys.argv[1:5]
GENERATED = "tacenta-proofs/translation/Translation/Tacenta"


def read(path):
    with open(path, "rb") as handle:
        return handle.read()


def digest(data):
    return hashlib.sha256(data).hexdigest()[:12]


def classify(committed, regenerated):
    """(state, digest of the regenerated file or '-')"""
    if not os.path.lexists(regenerated):
        return "missing", "-"
    if os.path.islink(regenerated) and not os.path.islink(committed):
        return "symlink", "-"
    if not os.path.isfile(regenerated):
        return "not-a-file", "-"
    try:
        theirs, mine = read(regenerated), read(committed)
    except OSError:
        return "unreadable", "-"
    if theirs != mine:
        return "differs", digest(theirs)
    if (os.stat(committed).st_mode ^ os.stat(regenerated).st_mode) & 0o111:
        return "mode", digest(theirs)
    return "identical", digest(theirs)


print("%-34s %-14s %-14s %s" % ("generated file", "committed", "regenerated", "result"))
bad = []
counted = 0
for path in open(listing, encoding="utf-8").read().split("\n"):
    if not path:
        continue
    counted += 1
    committed, regenerated = os.path.join(root, path), os.path.join(other, path)
    state, theirs = classify(committed, regenerated)
    if state != "identical":
        bad.append("%s: %s" % (state, path))
    if path.startswith(GENERATED) and path.endswith(".lean"):
        print("%-34s %-14s %-14s %s" % (os.path.basename(path), digest(read(committed)), theirs, state))
with open(diffs, "w", encoding="utf-8") as handle:
    handle.write("compared %d\n" % counted)
    handle.write("".join(line + "\n" for line in bad))
PY
  [ -f "$diffs" ] || { echo "regenerate-in-container: the comparison left no result; nothing was compared" >&2; return 2; }
  counted=$(sed -n '1s/^compared //p' "$diffs")
  if [ "$counted" != "$total" ]; then
    echo "regenerate-in-container: the comparison covered ${counted:-no} of $total tracked files; nothing was compared" >&2
    return 2
  fi
  bad=$(($(wc -l <"$diffs" | tr -d ' ') - 1))

  if [ "$bad" -ne 0 ] || [ "$extra" -ne 0 ]; then
    rc=1
    echo "regenerate-in-container: FAIL: $bad of $total tracked files differ or are missing, $extra file(s) are not in the tree" >&2
    { sed '1d; s/^/  /' "$diffs" | head -60 >&2; } || true
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
          echo "--- first hunks of $f (tracked, then $label)" >&2
          { diff -u "$ref/$f" "$dir/$f" 2>&1 | head -40 >&2; } || true ;;
      esac
    done <"$diffs"
  else
    echo "regenerate-in-container: PASS: all $total tracked files, as they are on disk, are equal to $label (the generated translation files among them); $(dirty_count) tracked path(s) differ from HEAD"
  fi
  return "$rc"
}

if [ "$mode" = compare ]; then
  git -C "$root" ls-files | LC_ALL=C sort >"$work/tracked.txt"
  echo "regenerate-in-container: comparing $(wc -l <"$work/tracked.txt" | tr -d ' ') tracked files of $(git -C "$root" rev-parse HEAD), $(dirty_count) tracked path(s) differ from HEAD, with $compare_dir"
  rc=0
  compare_tree "$compare_dir" "$root" "$work/tracked.txt" "$compare_dir" || rc=$?
  exit "$rc"
fi

# ---- --check ----
check_pins

# 1. The archive, checked before anything from it is used. An absolute path, so that docker reads it as a file.
if [ -z "$archive" ]; then
  command -v curl >/dev/null 2>&1 || { echo "regenerate-in-container: curl is needed to fetch the archive" >&2; exit 1; }
  archive="$work/$ARCHIVE_NAME"
  echo "regenerate-in-container: fetching $ARCHIVE_URL"
  curl -fL --retry 3 -sS -o "$archive" "$ARCHIVE_URL"
else
  [ -f "$archive" ] || { echo "regenerate-in-container: --archive $archive is not a file" >&2; exit 1; }
  archive="$(cd "$(dirname "$archive")" && pwd -P)/$(basename "$archive")"
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
echo "regenerate-in-container: tree $(git -C "$root" rev-parse HEAD), $(wc -l <"$work/tracked.txt" | tr -d ' ') tracked files as they are on disk, $(dirty_count) tracked path(s) differ from HEAD"
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
# A canary, not a pin: rustup below installs from its own download of this manifest, not from this copy.
curl -fsSL -o /tmp/channel.toml "https://static.rust-lang.org/dist/${channel#nightly-}/channel-rust-nightly.toml"
echo "$RUST_MANIFEST_SHA256  /tmp/channel.toml" | sha256sum -c - >/dev/null || { say "toolchain manifest digest mismatch"; exit 1; }
(cd /opt/aeneas && rustup toolchain install >/tmp/toolchain.log 2>&1 || { tail -20 /tmp/toolchain.log; exit 1; })
actual=$(cd /opt/aeneas && rustc --version)
[ "$actual" = "$RUSTC_VERSION_LINE" ] || { say "rustc is '$actual', not '$RUSTC_VERSION_LINE'"; exit 1; }

{
  echo "image: $(. /etc/os-release; echo "$PRETTY_NAME") $(uname -m), $(ldd --version | head -1)"
  echo "packages: $(dpkg-query -W -f='${Package}=${Version} ' ca-certificates curl gcc libc6-dev libc6 python3)"
  echo "gcc: $(gcc --version | head -1)"
  echo "python3: $(python3 --version)"
  echo "rustup: $(rustup --version 2>/dev/null | head -1)"
  echo "rustc: $actual"
  (cd /opt/aeneas && rustc -vV | sed 's/^/rustc -vV: /')
  echo "cargo: $(cd /opt/aeneas && cargo --version)"
  echo "charon: $(/opt/aeneas/charon version)"
  echo "aeneas: $(/opt/aeneas/aeneas -version)"
  echo "archive sha256: $ARCHIVE_SHA256"
  echo "toolchain manifest sha256 (downloaded copy, canary): $RUST_MANIFEST_SHA256"
  echo "toolchain manifest sha256 (kept by rustup, not pinned): $(sha256sum /root/.rustup/toolchains/*/lib/rustlib/multirust-channel-manifest.toml | cut -d' ' -f1)"
  for b in aeneas charon charon-driver; do echo "$b sha256: $(sha256sum /opt/aeneas/$b | cut -d' ' -f1)"; done
} >/out/versions.txt
cat /out/versions.txt

mkdir -p /work
cp -a /in/src /work/core
cd /work/core
touch /work/stamp
sleep 1
say "run-aeneas.sh starts $(date -u +%FT%TZ)"
AENEAS_TOOLS=/opt/aeneas sh tacenta-proofs/scripts/run-aeneas.sh
say "run-aeneas.sh ends $(date -u +%FT%TZ)"
# The tracked files the run wrote: everything newer than the stamp outside the scratch locations.
find . \( -path ./tacenta-core/target -o -path ./tacenta-proofs/Generated -o -name __pycache__ \) -prune -o -type f ! -name '*.llbc' -newer /work/stamp -print | sed 's|^\./||' | LC_ALL=C sort >/out/rewritten.txt
say "run-aeneas.sh rewrote $(wc -l </out/rewritten.txt | tr -d ' ') files of the tree (listed in rewritten.txt)"
mkdir -p /out/tree
tar -C /work/core --exclude=./tacenta-core/target --exclude='*.llbc' --exclude=./tacenta-proofs/Generated -cf - . | tar -C /out/tree -xf -
say "regenerated tree written"
chown -R "$HOST_UID:$HOST_GID" /out
INNER

# keep_results: copy what --keep asked for, and say what is kept (nothing otherwise).
keep_results() {
  if [ -n "$keep" ]; then
    mkdir -p "$keep"
    cp -R "$work/out/." "$keep/"
    cp "$work/container.log" "$keep/container.log" 2>/dev/null || true
    echo "regenerate-in-container: kept under $keep: $(ls "$keep" | tr '\n' ' ')($(du -sk "$keep" | cut -f1) KiB)"
  else
    echo "regenerate-in-container: nothing is kept; re-run with --keep DIR to keep the regenerated tree, versions.txt and the container log"
  fi
}

# 3. The run.
echo "regenerate-in-container: running run-aeneas.sh in a linux/amd64 container (slow when emulated)"
set +e
docker run --rm --name "$container" --cidfile "$cidfile" --platform linux/amd64 \
  -v "$archive:/in/aeneas.tar.gz:ro" -v "$work/src:/in/src:ro" -v "$work/out:/out" \
  -e HOST_UID="$(id -u)" -e HOST_GID="$(id -g)" \
  -e ARCHIVE_SHA256="$ARCHIVE_SHA256" -e RUSTUP_VERSION="$RUSTUP_VERSION" -e RUSTUP_INIT_SHA256="$RUSTUP_INIT_SHA256" \
  -e RUST_CHANNEL="$RUST_CHANNEL" -e RUST_MANIFEST_SHA256="$RUST_MANIFEST_SHA256" -e RUSTC_VERSION_LINE="$RUSTC_VERSION_LINE" \
  "$IMAGE" sh -c "$inner" regen 2>&1 | tee "$work/container.log"
status=${PIPESTATUS[0]}
set -e
if [ "$status" -ne 0 ]; then
  echo "regenerate-in-container: the container run failed (exit $status); nothing was compared" >&2
  keep_results
  exit 1
fi

# 4. The comparison.
rc=0
compare_tree "$work/out/tree" "$work/src" "$work/tracked.txt" "the regenerated tree" || rc=$?
keep_results
exit "$rc"
