#!/usr/bin/env bash
# Hold the label registry check to its two P9 negative controls.
#
#   bash tooling/tests/run-check-labels-cases.sh
#
# The production checker intentionally finds labels by scanning the source tree.
# Each case below builds a minimal source tree holding precisely the current
# label literals, then changes one relation.  It runs the real checker from
# that temporary root, so a loosened extraction, registry comparison, or
# prefix check makes this runner fail in the same CI job as the production
# check.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
checker="$root/tooling/check-labels.sh"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

collect_labels() {
  local dirs=()
  local d
  for d in "$root"/tacenta-core/src "$root"/tacenta-core/*/src; do
    case "$d" in
      "$root"/tacenta-core/triple-unit/src|"$root"/tacenta-core/braid-unit/src) continue ;;
    esac
    [ -d "$d" ] && dirs+=("$d")
  done
  grep -rhoE '^[[:space:]]*(pub(\([^)]*\))?[[:space:]]+)?(const|static)[[:space:]]+[A-Z_]*(INFO|LABEL):[[:space:]]*&('\''static[[:space:]]+)?\[u8\][[:space:]]*=[[:space:]]*b"[^"]*"' \
    --include='*.rs' "${dirs[@]}" 2>/dev/null | sed 's/.*b"//; s/"$//'
}

make_case() {
  local name="$1"
  local dst="$work/$name"
  local label
  mkdir -p "$dst/tacenta-core/src" "$dst/tooling"
  cp "$root/tacenta-core/LABELS.md" "$dst/tacenta-core/LABELS.md"
  cp "$checker" "$dst/tooling/check-labels.sh"
  while IFS= read -r label; do
    # The checker reads source text, so a repeated syntactic name is sufficient
    # for the fixture and keeps the name inside its `[A-Z_]*...LABEL` scope.
    printf 'const CASE_LABEL: &[u8] = b"%s";\n' "$label"
  done < <(collect_labels) > "$dst/tacenta-core/src/labels.rs"
}

expect_fail() {
  local name="$1"
  local expect="$2"
  local out rc
  set +e
  out="$(bash "$work/$name/tooling/check-labels.sh" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $name: expected refusal ($expect), was accepted" >&2
    return 1
  fi
  if ! printf '%s' "$out" | grep -qF -- "$expect"; then
    echo "WRONG  $name: refused, but not for '$expect':" >&2
    printf '  %s\n' "$out" >&2
    return 1
  fi
}

make_case pass
bash "$work/pass/tooling/check-labels.sh"

make_case unregistered-label
printf 'const P_NINE_UNREGISTERED_LABEL: &[u8] = b"P9 unregistered label";\n' \
  >> "$work/unregistered-label/tacenta-core/src/labels.rs"
expect_fail unregistered-label 'REFUSING: tacenta-core/LABELS.md and the source disagree.'

make_case forbidden-prefix
cat >> "$work/forbidden-prefix/tacenta-core/src/labels.rs" <<'EOF'
const P_NINE_PREFIX_LABEL: &[u8] = b"P9 prefix";
const P_NINE_PREFIX_EXTENDED_LABEL: &[u8] = b"P9 prefix extended";
EOF
cat >> "$work/forbidden-prefix/tacenta-core/LABELS.md" <<'EOF'
| `tacenta-core` | `P_NINE_PREFIX_LABEL` | `P9 prefix` |
| `tacenta-core` | `P_NINE_PREFIX_EXTENDED_LABEL` | `P9 prefix extended` |
EOF
expect_fail forbidden-prefix 'REFUSING: a label is a strict prefix of another, and is not a pair'

echo 'check-labels-cases: pass case and 2 refusal cases gave the expected result'
