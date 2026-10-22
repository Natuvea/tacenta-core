#!/usr/bin/env bash
# Regenerate every generated file after a merge, and refuse while anything else is unresolved.
#
#   bash tooling/regenerate-generated.sh            regenerate, then run the checks that hold each file
#   bash tooling/regenerate-generated.sh --count    also recount the attestation negatives' cases (minutes)
#
# A merge of two proof branches conflicts in files that nobody writes by hand: the two attestation manifests,
# the generated gate inventory and the CI step record. Resolving them by hand is error-prone and pointless,
# since each is a function of the tree. This script takes either side of each such file and writes it again
# from the merged tree, in the order the generators read each other:
#
#   tooling/required-steps.json                 bash tooling/check-workflows.sh --write-required-steps
#   ASSURANCE-OBLIGATIONS.md and the lists      python3 tooling/reflow-shared-lists.py --write (the one-entry-
#     a new module edits                          per-line form; it rewrites the form, never an entry)
#   tacenta-proofs/manifests/verification-manifest.json,
#   tacenta-proofs/manifests/source-commit-attestation.json   python3 tacenta-proofs/scripts/attest.py
#   tacenta-proofs/GATE-INVENTORY.md            python3 tooling/gate-inventory.py --write
#   tacenta-proofs/scripts/attest-negatives-case-count.txt    only with --count: the count the attestation
#                                                              negatives print with ATTEST_NEGATIVES_COUNT=1
#
# Before that it resolves, with tooling/resolve-insertion-conflicts.py, the conflicts in the shared wiring files
# that are two insertions at one place (two modules whose entries sort after the same existing entry), and only
# those; when one of them is anything else it stops there, having written nothing. After it, it runs
# `attest.py --check`, `gate-inventory.py --check`, `check-workflows.sh`, `reflow-shared-lists.py --check` and the
# structural checks of `resolve-insertion-conflicts.py --verify` (the JSON loads, attest.py parses, `bash -n`, every
# part resolves against the phases no-sorry.sh lists, no entry a module adds appears twice), then
# `tooling/check-landing.sh` (the rows and the section the tooling change added are still there), and stages the
# generated files that were unmerged.
#
# It refuses, and writes nothing more, when a path other than those is unmerged or a tracked file other than those
# holds a conflict marker (resolve those first: they hold someone's text), and when the case count is unmerged
# and --count is not given. The translation attestation and the axiom allowlist are not regenerated here:
# they record a run of the pinned toolchain (`attest.py --refresh-translation`, `--write-axiom-allowlist`), and
# an unmerged one is refused like any hand-written file.
#
# What it does not do: check that the merge of the hand-written files is right. `tooling/check-merge-exactness.sh`
# compares a committed merge with its two sides.
set -euo pipefail

count=0
for argument in "$@"; do
  case "$argument" in
    --count) count=1 ;;
    *) echo "usage: regenerate-generated.sh [--count]" >&2; exit 2 ;;
  esac
done

cd "$(git rev-parse --show-toplevel)"

generated="tooling/required-steps.json
tacenta-proofs/manifests/verification-manifest.json
tacenta-proofs/manifests/source-commit-attestation.json
tacenta-proofs/GATE-INVENTORY.md
tacenta-proofs/scripts/attest-negatives-case-count.txt"

is_generated() {
  grep -qxF -- "$1" <<<"$generated"
}

# Two modules whose entries sort after the same existing entry insert lines at one place of a shared list; those
# conflicts, and only those, are resolved first (both insertions, this side's first).
python3 tooling/resolve-insertion-conflicts.py

unmerged="$(git diff --name-only --diff-filter=U | sort -u)"
others=""
for path in $unmerged; do
  is_generated "$path" || others="$others $path"
done
if [ -n "$others" ]; then
  echo "regenerate-generated: REFUSED: unmerged files that are not generated:$others" >&2
  echo "regenerate-generated: resolve them first; nothing was written" >&2
  exit 1
fi
case " $(printf '%s ' $unmerged)" in
  *" tacenta-proofs/scripts/attest-negatives-case-count.txt "*)
    if [ "$count" -ne 1 ]; then
      echo "regenerate-generated: REFUSED: the attestation negatives' case count is unmerged; run with --count" \
        "to recount it (minutes), or resolve it by hand; nothing was written" >&2
      exit 1
    fi ;;
esac

markers="$(git grep -I -l -E '^(<<<<<<<|=======|>>>>>>>)' -- . ':!*.patch' || true)"
bad=""
for path in $markers; do
  is_generated "$path" || bad="$bad $path"
  if [ "$path" = tacenta-proofs/scripts/attest-negatives-case-count.txt ] && [ "$count" -ne 1 ]; then
    bad="$bad $path (the case count: run with --count)"
  fi
done
if [ -n "$bad" ]; then
  echo "regenerate-generated: REFUSED: conflict markers in files that are not generated:$bad" >&2
  echo "regenerate-generated: resolve them first; nothing was written" >&2
  exit 1
fi

# An unmerged generated file is taken from this side, so that no generator reads a file with conflict markers;
# it is then written again from the tree.
for path in $unmerged; do
  git checkout --ours -- "$path"
done

echo "regenerate-generated: required-steps.json from the workflow"
bash tooling/check-workflows.sh --write-required-steps
echo "regenerate-generated: the one-entry-per-line form"
python3 tooling/reflow-shared-lists.py --write
echo "regenerate-generated: the attestation manifests"
python3 tacenta-proofs/scripts/attest.py
echo "regenerate-generated: the gate inventory"
python3 tooling/gate-inventory.py --write
if [ "$count" -eq 1 ]; then
  echo "regenerate-generated: recounting the attestation negatives' cases"
  n="$(ATTEST_NEGATIVES_COUNT=1 bash tacenta-proofs/scripts/check-attest-negatives.sh)"
  [[ "$n" =~ ^[0-9]+$ ]] || { echo "regenerate-generated: the count run printed '$n', not a number" >&2; exit 1; }
  printf '%s\n' "$n" > tacenta-proofs/scripts/attest-negatives-case-count.txt
fi

echo "regenerate-generated: checking"
python3 tacenta-proofs/scripts/attest.py --check
python3 tooling/gate-inventory.py --check
bash tooling/check-workflows.sh
python3 tooling/reflow-shared-lists.py --check
python3 tooling/resolve-insertion-conflicts.py --verify
bash tooling/check-landing.sh

for path in $unmerged; do
  git add -- "$path"
done
changed="$(git status --porcelain --untracked-files=no -- $generated ASSURANCE-OBLIGATIONS.md \
  tacenta-proofs/scripts/no-sorry-parts.txt tooling/tests/run-proof-script-cases.sh tooling/gate-inventory.json)"
echo "regenerate-generated: done; generated and reflowed files changed against the index or HEAD:"
printf '%s\n' "${changed:-  (none)}"
