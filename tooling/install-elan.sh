#!/usr/bin/env bash
# Install a fixed elan release on a Linux x86_64 runner, checking the archive
# against a pinned sha256 before anything from it runs.
#
#   ELAN_VERSION=v4.2.4 ELAN_SHA256=<hex> bash tooling/install-elan.sh
#
# The usual `curl elan-init.sh | sh` fetches whatever the script's host serves
# today and runs it unread, and `tooling/check-workflows.sh` refuses that
# shape. This downloads one named release archive, compares its digest with
# the one the workflow pins, and only then runs the installer inside it. The
# pin is the release tag and the digest together: bumping one without the
# other fails here rather than installing something else.
#
# The toolchain itself is not chosen here. `--default-toolchain none` leaves
# that to the `lean-toolchain` file in each Lake package, so the version the
# repository pins is the version that builds. This script installs each
# toolchain those files name (`elan toolchain install`, a release of the
# form `leanprover/lean4:vX.Y.Z`; any other form, such as a moving channel,
# is refused) so that the download happens here, under the bounded retry of
# `tooling/retry-download.sh`, and not inside the first `lake` command, where
# one dropped connection failed a whole build step. A toolchain elan already
# lists is not fetched again. The archive download of elan itself goes through
# the same retry; its digest check runs once, afterwards, on what was fetched,
# and a mismatch is never retried.
#
# On the self-hosted runner, two jobs run at once under one account and share
# its `~/.elan`. The installer is not run twice at once (the second waits on a
# lock), and not at all when that `~/.elan` already holds the pinned release,
# which this script put there after checking its digest: replacing the binary
# while the other job's `lake` runs from it could fail that job.
#
# CI-only: it assumes a Linux runner with `sha256sum` and writes to
# `$GITHUB_PATH`. A developer installs elan however they like; the README's
# prerequisites table says what version of Lean the packages need.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/.." && pwd)"

: "${ELAN_VERSION:?set ELAN_VERSION to the elan release tag, e.g. v4.2.4}"
: "${ELAN_SHA256:?set ELAN_SHA256 to the sha256 of the x86_64-unknown-linux-gnu archive}"

mkdir -p "$HOME/.cache"
exec 9> "$HOME/.cache/install-elan.lock"
flock 9

installed="$("$HOME/.elan/bin/elan" --version 2>/dev/null | awk '{print $2}')" || true
if [ "$installed" = "${ELAN_VERSION#v}" ]; then
  echo "install-elan: elan $ELAN_VERSION is already installed in $HOME/.elan"
else
  archive_name="elan-x86_64-unknown-linux-gnu.tar.gz"
  url="https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/${archive_name}"
  work="$(mktemp -d)"
  archive="$work/$archive_name"

  echo "install-elan: fetching elan $ELAN_VERSION"
  bash "$here/retry-download.sh" -- curl -sSfL --retry 3 -o "$archive" "$url"

  if ! echo "${ELAN_SHA256}  ${archive}" | sha256sum -c -; then
    echo "install-elan: the archive did not match ELAN_SHA256; refusing to run it" >&2
    exit 1
  fi

  tar xzf "$archive" -C "$work"
  "$work/elan-init" -y --no-modify-path --default-toolchain none
  rm -rf "$work"
  echo "install-elan: elan $ELAN_VERSION installed"
fi

# The Lean toolchains the packages pin, fetched now (see the header), still under the lock.
elan="$HOME/.elan/bin/elan"
toolchains=""
while IFS= read -r -d '' file; do
  name="$(head -n 1 "$root/$file" | tr -d '[:space:]')"
  if ! [[ "$name" =~ ^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$ ]]; then
    echo "install-elan: $file names '$name', not a pinned Lean release (leanprover/lean4:vX.Y.Z); refusing to fetch it" >&2
    exit 1
  fi
  case " $toolchains " in *" $name "*) ;; *) toolchains="${toolchains}${toolchains:+ }$name" ;; esac
done < <(git -C "$root" ls-files -z -- '*lean-toolchain')
if [ -z "$toolchains" ]; then
  echo "install-elan: no lean-toolchain file in the checkout; nothing would choose the toolchain" >&2
  exit 1
fi
listed="$("$elan" toolchain list 2>/dev/null || true)"
for name in $toolchains; do
  if grep -qE -- "^${name//./\\.}( |\$)" <<<"$listed"; then
    echo "install-elan: Lean toolchain $name is already installed"
  else
    echo "install-elan: fetching Lean toolchain $name"
    bash "$here/retry-download.sh" -- "$elan" toolchain install "$name"
  fi
done

if [ -n "${GITHUB_PATH:-}" ]; then
  echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
fi
