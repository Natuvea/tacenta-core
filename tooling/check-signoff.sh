#!/usr/bin/env bash
# Refuse a change whose commits are not signed off by their authors.
#
#   check-signoff.sh [BASE]        (BASE defaults to origin/main)
#
# CONTRIBUTING.md asks every commit to carry a `Signed-off-by:` trailer under
# the Developer Certificate of Origin 1.1. For a long time nothing checked it,
# and the history on main from before this check carries no sign-off at all:
# a rule that no gate enforces is a sentence, not a rule. So this checks the
# commits a change adds, `BASE..HEAD`, and nothing already on BASE.
#
# What counts: every commit in the range has a `Signed-off-by:` trailer whose
# value is exactly its author, `Name <email>`. That includes merge commits. The
# protected branch requires linear history, so a branch should rebase instead
# of introducing an unsigned merge of its base.
#
# In CI the pull request's base branch is BASE. Locally, `tooling/ci.sh` runs
# it against origin/main, so a branch is checked before it is pushed. With no
# BASE to compare against is a missing prerequisite and fails closed.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

base="${1:-origin/main}"
if ! git rev-parse --verify --quiet "${base}^{commit}" >/dev/null; then
  echo "check-signoff: required base ${base} is missing; fetch it before checking" >&2
  exit 1
fi

status=0
count=0
while read -r sha; do
  [ -n "$sha" ] || continue
  count=$((count + 1))
  author=$(git show -s --format='%an <%ae>' "$sha")
  if ! git show -s --format='%(trailers:key=Signed-off-by,valueonly)' "$sha" | grep -qxF -- "$author"; then
    printf 'check-signoff: %s is not signed off by its author, %s\n' \
      "$(git log -1 --format='%h %s' "$sha")" "$author" >&2
    status=1
  fi
done < <(git rev-list "${base}..HEAD")

if [ "$status" -eq 0 ]; then
  echo "check-signoff: ${count} commit(s) on top of ${base}, each signed off by its author"
else
  echo "" >&2
  echo "check-signoff: sign off with 'git commit -s' (CONTRIBUTING.md, Developer Certificate of Origin)." >&2
  echo "  For commits already made: git rebase --signoff ${base}" >&2
fi
exit "$status"
