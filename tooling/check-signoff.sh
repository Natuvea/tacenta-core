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
# What counts: every non-merge commit in the range has a `Signed-off-by:`
# trailer whose value is exactly its author, `Name <email>`. Merge commits are
# skipped. GitHub writes the merge that lands a pull request itself, and a
# merge of main into a branch adds no authored change of its own.
#
# In CI the pull request's base branch is BASE. Locally, `tooling/ci.sh` runs
# it against origin/main, so a branch is checked before it is pushed. With no
# BASE to compare against, as in a clone without that ref, there is nothing to
# check, and it says so and succeeds.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

base="${1:-origin/main}"
if ! git rev-parse --verify --quiet "${base}^{commit}" >/dev/null; then
  echo "check-signoff: no ${base} in this clone, so no commits to check"
  exit 0
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
done < <(git rev-list --no-merges "${base}..HEAD")

if [ "$status" -eq 0 ]; then
  echo "check-signoff: ${count} commit(s) on top of ${base}, each signed off by its author"
else
  echo "" >&2
  echo "check-signoff: sign off with 'git commit -s' (CONTRIBUTING.md, Developer Certificate of Origin)." >&2
  echo "  For commits already made: git rebase --signoff ${base}" >&2
fi
exit "$status"
