#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
checker="$root/tooling/check-signoff.sh"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
repo="$work/repo"

git init -q -b main "$repo"
git -C "$repo" config user.name 'Control Author'
git -C "$repo" config user.email 'control@example.invalid'
printf 'base\n' > "$repo/file"
git -C "$repo" add file
git -C "$repo" commit -q -s -m base
git -C "$repo" tag base

expect_fail() {
  local name="$1" needle="$2" base="$3" out rc
  set +e
  out="$(cd "$repo" && bash "$checker" "$base" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $name: expected refusal containing '$needle', was accepted" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
  if ! printf '%s' "$out" | grep -qF -- "$needle"; then
    echo "WRONG  $name: refused, but without '$needle'" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
}

printf 'signed\n' >> "$repo/file"
git -C "$repo" commit -q -s -am signed
(cd "$repo" && bash "$checker" base) >/dev/null

expect_fail missing-base 'required base absent is missing' absent

printf 'unsigned\n' >> "$repo/file"
git -C "$repo" commit -q -am unsigned
expect_fail unsigned-commit 'is not signed off by its author' base

git -C "$repo" reset -q --hard HEAD^
git -C "$repo" switch -q -c side base
printf 'side\n' > "$repo/side"
git -C "$repo" add side
git -C "$repo" commit -q -s -m side
git -C "$repo" switch -q main
git -C "$repo" merge -q --no-ff side -m 'unsigned merge'
expect_fail unsigned-merge 'is not signed off by its author' base

# Single-edit survivors of the mutation record (S2, S4, S5): the checker must read every commit of the
# range and not only the tip, accept only a trailer that equals the author exactly, and accept only
# the author's own name. Each case builds a fresh repository so that one case cannot hide another.
author='Control Author <control@example.invalid>'
new_repo() {
  rm -rf "$repo"
  git init -q -b main "$repo"
  git -C "$repo" config user.name 'Control Author'
  git -C "$repo" config user.email 'control@example.invalid'
  printf 'base\n' > "$repo/file"
  git -C "$repo" add file
  git -C "$repo" commit -q -s -m base
  git -C "$repo" tag -f base >/dev/null
}
add_commit() {  # message paragraphs...
  local args=() m
  for m in "$@"; do args+=(-m "$m"); done
  printf 'change %s\n' "$RANDOM" >> "$repo/file"
  git -C "$repo" commit -q -a "${args[@]}"
}
expect_pass() {
  local name="$1" out
  if ! out="$(cd "$repo" && bash "$checker" base 2>&1)"; then
    echo "WRONG  $name: expected acceptance" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
}

new_repo
add_commit 'unsigned below'
add_commit 'signed tip' "Signed-off-by: $author"
expect_fail unsigned-below-signed-tip 'unsigned below is not signed off by its author' base

new_repo
add_commit 'signed below' "Signed-off-by: $author"
add_commit 'unsigned tip'
expect_fail unsigned-above-signed-base 'unsigned tip is not signed off by its author' base

new_repo
add_commit 'someone else signs' 'Signed-off-by: Someone Else <someone@example.invalid>'
expect_fail trailer-names-another-person 'someone else signs is not signed off by its author' base

new_repo
add_commit 'near miss suffix' "Signed-off-by: $author (rebased)"
expect_fail trailer-with-suffix 'near miss suffix is not signed off by its author' base

new_repo
add_commit 'near miss prefix' "Signed-off-by: Not $author"
expect_fail trailer-with-prefix 'near miss prefix is not signed off by its author' base

new_repo
add_commit 'sign-off outside the trailer block' "Signed-off-by: $author" 'A closing paragraph, so the line above is not a trailer.'
expect_fail signoff-line-not-in-trailer-block 'sign-off outside the trailer block is not signed off by its author' base

new_repo
add_commit 'signed with a following trailer' "Signed-off-by: $author
Reviewed-by: Someone Else <someone@example.invalid>"
add_commit 'signed with a preceding trailer' "Co-authored-by: Someone Else <someone@example.invalid>
Signed-off-by: $author"
expect_pass signed-with-other-trailers

# Edits to the checker that every case above accepted: a trailer of another kind that carries the author's
# string, a signer who is the committer and not the author, and a signed merge that hides an unsigned commit.
new_repo
add_commit 'coauthor only' "Co-authored-by: $author"
expect_fail trailer-of-another-kind 'coauthor only is not signed off by its author' base

new_repo
printf 'change\n' >> "$repo/file"
GIT_AUTHOR_NAME='Alice Author' GIT_AUTHOR_EMAIL='alice@example.invalid' \
  git -C "$repo" commit -q -a -m 'authored by alice' -m "Signed-off-by: $author"
expect_fail author-is-not-the-committer 'authored by alice is not signed off by its author, Alice Author' base

new_repo
git -C "$repo" switch -q -c side base
printf 'side\n' > "$repo/side"
git -C "$repo" add side
git -C "$repo" commit -q -m 'side unsigned'
git -C "$repo" switch -q main
add_commit 'main signed' "Signed-off-by: $author"
git -C "$repo" merge -q --no-ff --signoff side -m 'signed merge'
expect_fail signed-merge-of-an-unsigned-commit 'side unsigned is not signed off by its author' base

echo 'check-signoff-cases: pass plus missing-base, unsigned-commit and unsigned-merge refusals gave the expected result'
echo 'check-signoff-cases: an unsigned commit below a signed tip, another person as signer, a near-miss trailer (suffix, prefix, outside the trailer block), another kind of trailer, a committer who is not the author and a signed merge of an unsigned commit were each refused; a sign-off beside other trailers was accepted'
