#!/usr/bin/env bash
# Run a command with git as a hosted runner sees it: no global or system configuration (so no identity, no
# init.defaultBranch, no hooks path, no aliases), no identity in the environment, and git refusing to guess one
# from the machine's account (user.useConfigOnly), where a Linux runner's account has no name to guess from. A
# fixture that commits must therefore give its own identity, as the hosted job requires.
#
#   bash tooling/tests/with-no-git-identity.sh <command> [args...]
#
# It checks first that git resolves no identity in a fresh repository here, and fails otherwise, so a version of
# this script that stopped stripping the identity cannot pass. run-gate-controls.sh runs itself through it.
set -euo pipefail
if [ "$#" -eq 0 ]; then
  echo "with-no-git-identity: give a command to run" >&2
  exit 2
fi
unset GIT_AUTHOR_NAME GIT_AUTHOR_EMAIL GIT_AUTHOR_DATE GIT_COMMITTER_NAME GIT_COMMITTER_EMAIL GIT_COMMITTER_DATE \
  EMAIL GIT_DIR GIT_WORK_TREE
export GIT_CONFIG_NOSYSTEM=1
export GIT_CONFIG_GLOBAL=/dev/null
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=user.useConfigOnly GIT_CONFIG_VALUE_0=true
export GATE_NO_GIT_IDENTITY=1
probe="$(mktemp -d "${TMPDIR:-/tmp}/no-git-identity.XXXXXX")"
git init -q "$probe" 2>/dev/null
if ident="$(git -C "$probe" var GIT_COMMITTER_IDENT 2>/dev/null)"; then
  rm -rf "$probe"
  echo "with-no-git-identity: git still resolves an identity here ($ident); a fixture that commits would pass" \
    "here and fail on a hosted runner" >&2
  exit 1
fi
rm -rf "$probe"
exec "$@"
