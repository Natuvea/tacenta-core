#!/usr/bin/env bash
# Negative control for `tooling/check-lockfiles.sh`: every lockfile of a checkout is the one its manifests resolve
# to offline, a stale one is refused naming its directory, and a lockfile the cache cannot resolve is a skip that
# says so (a failure in CI), never a silent pass.
#
# The cases run the real cargo (`cargo metadata --locked --offline`) against small workspaces in a throwaway git
# repository, with CARGO_HOME pointing at an empty directory, so nothing from this machine's cargo cache is read
# and nothing is fetched. The fixture's `.cargo/config.toml` replaces crates.io with a directory of vendored
# crates (`vendor/regleaf`, `vendor/regextra`), so its registry dependencies resolve with no network, and their
# lockfile entries carry crates.io as their source, as the real ones do. The base tree has two workspaces, `ws`
# and `tools/runner`, each depending on the path crate `dep`, which depends on the registry crate `regleaf`.
# A registry entry matters: cargo's `--locked` does not refuse a lockfile whose only stale entries are path
# packages (the case `path-only-stale` records that, and the hosted `--locked` builds behave the same).
#
#   unmodified          the base tree is accepted, both lockfiles named ok
#   stale-path-dep      `dep` drops its dependency on `regleaf` while both lockfiles still list it: both refused,
#                       each by directory (the shape of the hosted failure of 2026-10-23, where tacenta-kdf
#                       dropped dependencies that the vectors runner's and the fuzz lockfiles still listed)
#   stale-dropped-dep   `ws` drops `dep` from its own manifest: `ws` refused, `tools/runner` still ok
#   missing-new-dep     `ws` gains a registry dependency its lockfile does not list: refused
#   broken-manifest     `ws/Cargo.toml` does not parse: refused as a manifest error, not skipped
#   new-directory       a workspace in a directory no list names, staged with git: found and refused by name;
#                       the same untracked (new, not ignored) is found too, and an ignored one is not read
#   orphan-lockfile     a Cargo.lock with no Cargo.toml beside it (cargo would resolve a parent): refused
#   deleted-lockfile    a tracked lockfile missing from the working tree: refused
#   no-lockfile         a checkout with no lockfile at all: refused (nothing found is nothing checked)
#   corrupt-lockfile    a Cargo.lock that is not a lockfile: refused (an error the gate does not classify fails)
#   cache-missing       registry dependencies with an empty cargo cache and no vendored replacement: a SKIP line
#                       naming each directory, exit 0, the "WITH SKIPS" line and a line in FAST_SKIP_LOG; with
#                       GITHUB_ACTIONS=true, a failure
#   no-cargo            no cargo on PATH: every lockfile a SKIP locally, a failure with GITHUB_ACTIONS=true
#   cargo-not-runnable  a `cargo` that fails `cargo --version` (a rustup proxy with no toolchain): a SKIP, not a
#                       FAIL of `cargo metadata`
#   no-auto-install     the gate runs cargo with RUSTUP_AUTO_INSTALL=0, so a rustup proxy cannot download a
#                       toolchain a directory names (a stand-in `cargo` records what it was given)
#   quoted-names        corrupt lockfiles in directories whose names git quotes (`ws é`, `ws "q"`): each found,
#                       refused by name and counted, not dropped
#   path-only-stale     the known limit, recorded: a lockfile whose only stale entries are path packages is
#                       accepted, because cargo's `--locked` accepts it (so do the hosted builds)
#
# A case that goes wrong prints a line that starts `WRONG  `; the runner runs every case and exits 1 at the end if
# any did. It reads the gate as it stands in this tree. It needs cargo, and fails rather than skips without it:
# a control that cannot run has shown nothing.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
checker="$root/tooling/check-lockfiles.sh"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

fail=0
cases=0
wrong() { fail=$((fail + 1)); echo "WRONG  $1: $2" >&2; }

if ! command -v cargo >/dev/null 2>&1 || ! cargo --version >/dev/null 2>&1; then
  echo "run-lockfile-check-cases: cargo is not runnable here; these cases need it, and a control that cannot run fails" >&2
  exit 1
fi
real_bash="$(command -v bash)"
empty_cargo_home="$work/cargo-home"
mkdir -p "$empty_cargo_home"

repo="$work/repo"
crate() {  # dir name deps-toml [workspace]
  mkdir -p "$repo/$1/src"
  : > "$repo/$1/src/lib.rs"
  {
    [ "${4:-}" = workspace ] && printf '[workspace]\n\n'
    printf '[package]\nname = "%s"\nversion = "0.1.0"\nedition = "2021"\n\n[dependencies]\n%s' "$2" "$3"
  } > "$repo/$1/Cargo.toml"
}
lock() {  # dir: generate its lockfile offline from path dependencies only
  (cd "$repo/$1" && CARGO_HOME="$empty_cargo_home" cargo generate-lockfile --offline --quiet)
}
vendored() {  # name: a crate in the fixture's vendored crates.io replacement
  mkdir -p "$repo/vendor/$1/src"
  : > "$repo/vendor/$1/src/lib.rs"
  printf '[package]\nname = "%s"\nversion = "1.0.0"\nedition = "2021"\n' "$1" > "$repo/vendor/$1/Cargo.toml"
  printf '{"files":{},"package":"%s"}' "$(printf '%064d' 1)" > "$repo/vendor/$1/.cargo-checksum.json"
}
new_repo() {
  rm -rf "$repo"
  mkdir -p "$repo/.cargo"
  git init -q "$repo"
  printf 'ignored/\ntarget/\n' > "$repo/.gitignore"
  printf '[source.crates-io]\nreplace-with = "fixture"\n\n[source.fixture]\ndirectory = "vendor"\n' \
    > "$repo/.cargo/config.toml"
  vendored regleaf
  vendored regextra
  crate leaf leaf ''
  crate dep dep 'regleaf = "1"
'
  crate ws ws 'dep = { path = "../dep" }
' workspace
  crate tools/runner runner 'dep = { path = "../../dep" }
' workspace
  lock ws
  lock tools/runner
  git -C "$repo" add -A
}

OUT=""
RC=0
run_gate() {  # [env assignments...]
  set +e
  OUT="$(cd "$repo" && env -u GITHUB_ACTIONS -u FAST_SKIP_LOG -u RUSTUP_AUTO_INSTALL CARGO_HOME="$empty_cargo_home" "$@" \
    "$real_bash" "$checker" 2>&1)"
  RC=$?
  set -e
}
has() { cases=$((cases + 1)); grep -qF -- "$2" <<<"$OUT" || { wrong "$1" "output lacks '$2'"; printf '%s\n' "$OUT" >&2; }; }
lacks() { cases=$((cases + 1)); ! grep -qF -- "$2" <<<"$OUT" || { wrong "$1" "output has '$2'"; printf '%s\n' "$OUT" >&2; }; }
rc_is() { cases=$((cases + 1)); [ "$RC" -eq "$2" ] || { wrong "$1" "exit $RC, expected $2"; printf '%s\n' "$OUT" >&2; }; }

STALE="the lockfile would have to change to match the manifests"

# unmodified
new_repo
run_gate
rc_is unmodified 0
has unmodified "lockfiles: ok ws"
has unmodified "lockfiles: ok tools/runner"
has unmodified "2 lockfile(s): 2 ok, 0 failed, 0 skipped"
lacks unmodified "SKIP"

# stale-path-dep: the hosted failure's shape; the manifest that changed is not in either lockfile's directory.
new_repo
crate dep dep ''
run_gate
rc_is stale-path-dep 1
has stale-path-dep "lockfiles: FAIL ws: $STALE"
has stale-path-dep "lockfiles: FAIL tools/runner: $STALE"
has stale-path-dep "2 failed"

# stale-dropped-dep
new_repo
crate ws ws '' workspace
run_gate
rc_is stale-dropped-dep 1
has stale-dropped-dep "lockfiles: FAIL ws: $STALE"
has stale-dropped-dep "lockfiles: ok tools/runner"

# missing-new-dep
new_repo
crate ws ws 'dep = { path = "../dep" }
regextra = "1"
' workspace
run_gate
rc_is missing-new-dep 1
has missing-new-dep "lockfiles: FAIL ws: $STALE"
has missing-new-dep "lockfiles: ok tools/runner"

# broken-manifest
new_repo
printf '[package\nname = "ws"\n' > "$repo/ws/Cargo.toml"
run_gate
rc_is broken-manifest 1
has broken-manifest "lockfiles: FAIL ws: a manifest does not parse"
lacks broken-manifest "SKIP ws"

# new-directory: staged, untracked, ignored.
new_repo
crate brand/new/place place 'dep = { path = "../../../dep" }
' workspace
lock brand/new/place
crate brand/new/place place '' workspace
git -C "$repo" add brand
run_gate
rc_is new-directory 1
has new-directory "lockfiles: FAIL brand/new/place: $STALE"
has new-directory "3 lockfile(s)"
git -C "$repo" rm -q -r --cached brand
run_gate
rc_is new-directory-untracked 1
has new-directory-untracked "lockfiles: FAIL brand/new/place: $STALE"
mkdir -p "$repo/ignored"
mv "$repo/brand" "$repo/ignored/brand"
run_gate
rc_is new-directory-ignored 0
lacks new-directory-ignored "ignored/brand"
has new-directory-ignored "2 lockfile(s): 2 ok"

# orphan-lockfile: inside ws, with no manifest of its own; cargo would resolve ws/Cargo.toml and pass.
new_repo
mkdir -p "$repo/ws/orphan"
cp "$repo/ws/Cargo.lock" "$repo/ws/orphan/Cargo.lock"
git -C "$repo" add ws/orphan/Cargo.lock
run_gate
rc_is orphan-lockfile 1
has orphan-lockfile "lockfiles: FAIL ws/orphan: a Cargo.lock with no Cargo.toml beside it"

# corrupt-lockfile
new_repo
printf 'this is not a lockfile [[\n' > "$repo/ws/Cargo.lock"
run_gate
rc_is corrupt-lockfile 1
has corrupt-lockfile "lockfiles: FAIL ws: cargo metadata failed"
lacks corrupt-lockfile "SKIP"

# deleted-lockfile
new_repo
rm "$repo/tools/runner/Cargo.lock"
run_gate
rc_is deleted-lockfile 1
has deleted-lockfile "lockfiles: FAIL tools/runner: git lists tools/runner/Cargo.lock but the working tree has no such file"

# no-lockfile
new_repo
git -C "$repo" rm -q --cached ws/Cargo.lock tools/runner/Cargo.lock
rm "$repo/ws/Cargo.lock" "$repo/tools/runner/Cargo.lock"
run_gate
rc_is no-lockfile 1
has no-lockfile "no Cargo.lock in this checkout"

# cache-missing: registry dependencies the empty cache cannot resolve offline (crates.io itself: the fixture's
# vendored replacement is removed for this case, so every workspace of the tree is a skip).
new_repo
rm -rf "$repo/.cargo"
crate reg reg 'itoa = "1"
' workspace
cat > "$repo/reg/Cargo.lock" <<'EOF'
# This file is automatically @generated by Cargo.
# It is not intended for manual editing.
version = 4

[[package]]
name = "itoa"
version = "1.0.0"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "0000000000000000000000000000000000000000000000000000000000000000"

[[package]]
name = "reg"
version = "0.1.0"
dependencies = [
 "itoa",
]
EOF
git -C "$repo" add reg
skiplog="$work/skips"
: > "$skiplog"
run_gate FAST_SKIP_LOG="$skiplog"
rc_is cache-missing 0
has cache-missing "lockfiles: SKIP reg: --offline cannot resolve it from the local cargo cache"
has cache-missing "(not checked)"
has cache-missing "lockfiles: SKIP ws: --offline cannot resolve it"
has cache-missing "0 ok, 0 failed, 3 skipped"
has cache-missing "lockfiles: passed WITH SKIPS"
cases=$((cases + 1))
grep -qF 'lockfile check of reg:' "$skiplog" || wrong cache-missing-skip-log "FAST_SKIP_LOG has no line for reg: $(cat "$skiplog")"
run_gate GITHUB_ACTIONS=true
rc_is cache-missing-in-ci 1
has cache-missing-in-ci "lockfiles: SKIP reg:"
has cache-missing-in-ci "a check that cannot run is a failure"

# no-cargo: a PATH of the tools the gate needs and no cargo.
mkdir -p "$work/tools"
for tool in bash git sort basename dirname mktemp rm grep head sed cat env; do
  found="$(command -v "$tool" 2>/dev/null || true)"
  case "$found" in
    /*) ln -sf "$found" "$work/tools/$tool" ;;
  esac
done
new_repo
run_gate PATH="$work/tools"
rc_is no-cargo 0
has no-cargo "lockfiles: SKIP ws: cargo not found"
has no-cargo "lockfiles: SKIP tools/runner: cargo not found"
lacks no-cargo "lockfiles: ok"
run_gate PATH="$work/tools" GITHUB_ACTIONS=true
rc_is no-cargo-in-ci 1

# cargo-not-runnable and no-auto-install: stand-in `cargo` commands in front of the tools above.
mkdir -p "$work/broken-cargo" "$work/recording-cargo"
printf '#!/bin/sh\nexit 1\n' > "$work/broken-cargo/cargo"
cat > "$work/recording-cargo/cargo" <<'EOF'
#!/bin/sh
echo "${RUSTUP_AUTO_INSTALL-unset} $*" >> "$CARGO_RECORD"
exit 0
EOF
chmod +x "$work/broken-cargo/cargo" "$work/recording-cargo/cargo"
new_repo
run_gate PATH="$work/broken-cargo:$work/tools"
rc_is cargo-not-runnable 0
has cargo-not-runnable "lockfiles: SKIP ws: cargo not found or not runnable"
lacks cargo-not-runnable "cargo metadata failed"
record="$work/cargo-record"
: > "$record"
run_gate PATH="$work/recording-cargo:$work/tools" CARGO_RECORD="$record"
rc_is no-auto-install 0
cases=$((cases + 1))
grep -qx '0 metadata --locked --offline --format-version 1' "$record" \
  || wrong no-auto-install "cargo metadata did not run with RUSTUP_AUTO_INSTALL=0: $(tr '\n' ';' < "$record")"
cases=$((cases + 1))
! grep -qv '^0 ' "$record" || wrong no-auto-install-every-call "a cargo call ran without RUSTUP_AUTO_INSTALL=0: $(tr '\n' ';' < "$record")"

# quoted-names: directories whose names git prints quoted unless told not to.
new_repo
for name in 'ws é' 'ws "q"'; do
  crate "$name" quoted '' workspace
  printf 'this is not a lockfile [[\n' > "$repo/$name/Cargo.lock"
done
git -C "$repo" add -A
run_gate
rc_is quoted-names 1
has quoted-names 'lockfiles: FAIL ws é: cargo metadata failed'
has quoted-names 'lockfiles: FAIL ws "q": cargo metadata failed'
has quoted-names "4 lockfile(s): 2 ok, 2 failed"

# path-only-stale: `dep` drops a path dependency that both lockfiles still list. Recorded as accepted, the
# behaviour of cargo's --locked; if a cargo release starts refusing it, this case says so and the limit in the
# gate's header is to be revised.
new_repo
crate dep dep 'regleaf = "1"
leaf = { path = "../leaf" }
'
lock ws
lock tools/runner
git -C "$repo" add -A
crate dep dep 'regleaf = "1"
'
run_gate
rc_is path-only-stale 0
has path-only-stale "2 lockfile(s): 2 ok"

if [ "$fail" -ne 0 ]; then
  echo "run-lockfile-check-cases: $fail check(s) went wrong" >&2
  exit 1
fi
echo "run-lockfile-check-cases: $cases checks (an unmodified tree, a stale lockfile by a path dependency, a dropped and a missing dependency, a broken manifest, a new directory staged, untracked and ignored, an orphan, a corrupt, a deleted and no lockfile, a missing cache, no cargo and a cargo that does not run, locally and in CI, RUSTUP_AUTO_INSTALL=0, directories whose names git quotes, and the recorded path-only limit) gave the expected result"
