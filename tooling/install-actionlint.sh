#!/usr/bin/env bash
# Download the pinned actionlint release and verify its published SHA-256.
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: $0 <destination-directory>" >&2
  exit 2
fi

destination="$1"
version="1.7.12"
case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)
    archive="actionlint_${version}_darwin_arm64.tar.gz"
    digest="aba9ced2dee8d27fecca3dc7feb1a7f9a52caefa1eb46f3271ea66b6e0e6953f"
    ;;
  Linux-x86_64)
    archive="actionlint_${version}_linux_amd64.tar.gz"
    digest="8aca8db96f1b94770f1b0d72b6dddcb1ebb8123cb3712530b08cc387b349a3d8"
    ;;
  *)
    echo "install-actionlint: unsupported platform $(uname -s)-$(uname -m)" >&2
    exit 1
    ;;
esac

mkdir -p "$destination"
archive_path="$(mktemp)"
cleanup() { rm -f "$archive_path"; }
trap cleanup EXIT

url="https://github.com/rhysd/actionlint/releases/download/v${version}/${archive}"
curl -fsSL --retry 3 -o "$archive_path" "$url"
actual="$(shasum -a 256 "$archive_path" | awk '{print $1}')"
if [ "$actual" != "$digest" ]; then
  echo "install-actionlint: SHA-256 mismatch for $archive" >&2
  echo "  expected: $digest" >&2
  echo "  actual:   $actual" >&2
  exit 1
fi
tar -xzf "$archive_path" -C "$destination"
if [ ! -x "$destination/actionlint" ]; then
  echo "install-actionlint: release archive did not contain an executable actionlint" >&2
  exit 1
fi
"$destination/actionlint" -version
