#!/usr/bin/env bash
# Clone a Lake package's git dependencies from local mirrors, at the revisions
# its manifest pins, so that Lake finds them already present.
#
#   bash tooling/seed-lake-packages.sh <lake package dir> [<mirror root>]
#
# For the self-hosted runner. That machine keeps its disk between jobs, but
# `actions/checkout` deletes every ignored file first, `.lake/packages`
# included, so without this each job clones Mathlib and the Aeneas library
# again over the machine's own connection. This keeps one bare mirror per
# dependency under the mirror root (`$HOME/.cache/lake-mirrors` by default),
# fetches a pinned revision from the dependency's own URL only when its mirror
# lacks it, and clones each dependency into `.lake/packages/<name>` with
# `origin` set to the manifest's URL and the pinned revision checked out.
#
# Lake then clones nothing itself: for a dependency already checked out at the
# manifest's revision it neither fetches nor compares URLs
# (`Lake/Load/Materialize.lean` in the pinned toolchain). What is built is what
# the manifest pins, read from a local copy of the same repository. A revision
# the mirror still lacks after fetching fails here, and a dependency directory
# that already exists is left for Lake to check under its own rules.
set -euo pipefail

pkg_dir="${1:?usage: seed-lake-packages.sh <lake package dir> [<mirror root>]}"
root="${2:-$HOME/.cache/lake-mirrors}"
manifest="$pkg_dir/lake-manifest.json"
packages="$pkg_dir/.lake/packages"

mkdir -p "$root" "$packages"
# One job at a time updates the mirrors.
exec 9> "$root/.lock"
flock 9

entries="$(python3 - "$manifest" <<'PY'
import json, sys
for p in json.load(open(sys.argv[1]))["packages"]:
    if p.get("type") == "git":
        print(p["name"], p["url"], p["rev"])
PY
)"

while read -r name url rev; do
  [ -n "$name" ] || continue
  mirror="$root/$name.git"
  dest="$packages/$name"
  if [ -e "$dest" ]; then
    echo "seed-lake-packages: $name: already present, left to Lake"
    continue
  fi
  if [ ! -d "$mirror" ]; then
    echo "seed-lake-packages: $name: no mirror yet, cloning $url"
    git clone -q --bare "$url" "$mirror"
  fi
  if ! git -C "$mirror" cat-file -e "$rev^{commit}" 2>/dev/null; then
    echo "seed-lake-packages: $name: fetching $rev from $url"
    git -C "$mirror" fetch -q "$url" "$rev"
    # A named ref, so the mirror's own housekeeping never prunes the revision.
    git -C "$mirror" update-ref "refs/pinned/$rev" "$rev"
  fi
  if ! git -C "$mirror" cat-file -e "$rev^{commit}" 2>/dev/null; then
    echo "seed-lake-packages: $name: $rev is not in $url" >&2
    exit 1
  fi
  git clone -q --no-checkout "$mirror" "$dest"
  git -C "$dest" remote set-url origin "$url"
  git -C "$dest" checkout -q --detach "$rev"
  echo "seed-lake-packages: $name: $rev, cloned from the mirror"
done <<< "$entries"
