#!/usr/bin/env bash
# Run the pinned workflow-expression and schema lint over every live workflow.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
cd "$root"
actionlint="${ACTIONLINT_BIN:-}"
if [ -z "$actionlint" ]; then
  actionlint="$(command -v actionlint || true)"
fi
if [ -z "$actionlint" ] || [ ! -x "$actionlint" ]; then
  echo "check-actionlint: actionlint is not installed" >&2
  exit 1
fi

files=()
while IFS= read -r file; do
  files+=("$file")
done < <(find . -path '*/.github/workflows/*.yml' -o -path '*/.github/workflows/*.yaml' | \
  grep -vE '/(\.lake|target|node_modules)/')
if [ "${#files[@]}" -eq 0 ]; then
  echo "check-actionlint: no workflow files found" >&2
  exit 1
fi

"$actionlint" -color=false "${files[@]}"
echo "check-actionlint: ${#files[@]} workflow file(s) pass actionlint"
