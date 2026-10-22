#!/usr/bin/env bash
# Negative controls for tooling/reflow-shared-lists.py, the one-entry-per-line form of the lists every new proof
# module edits.
#
# A fixture holds copies of the four files it rewrites (and the parts parser it reads the parts file with). The
# committed files must pass `--check`. Then each case packs one list back onto one line, or adds a table row
# longer than the limit, and requires `--check` to fail naming the file, `--write` to rewrite it, the rewrite to
# be stable (`--check` passes after it) and to hold the same entries. A list that cannot be rewritten without
# changing what it holds (an unterminated quote) must be refused, with nothing written.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
tool="$root/tooling/reflow-shared-lists.py"
work="$(mktemp -d "${TMPDIR:-/tmp}/reflow-cases.XXXXXX")"
trap 'rm -rf "$work"' EXIT
cases=0

fail_case() {
  echo "WRONG  reflow $1" >&2
  shift
  [ $# -eq 0 ] || printf '%s\n' "$@" >&2
  exit 1
}

files="tacenta-proofs/scripts/no-sorry-parts.txt tacenta-proofs/scripts/no-sorry-parts.py tooling/tests/run-proof-script-cases.sh tooling/gate-inventory.json ASSURANCE-OBLIGATIONS.md"
fresh() {
  rm -rf "$work/fx"
  for f in $files; do
    mkdir -p "$work/fx/$(dirname "$f")"
    cp "$root/$f" "$work/fx/$f"
  done
}
run() {  # name want-exit needle mode
  local name="$1" want="$2" needle="$3" mode="$4" out rc
  set +e
  out="$(python3 "$tool" "$mode" --root "$work/fx" 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -ne "$want" ] || ! grep -qF -- "$needle" <<<"$out"; then
    fail_case "$name: expected exit $want and '$needle' from $mode, got exit $rc" "$out"
  fi
}
edit() {  # file python-program-over-text(t)
  python3 - "$work/fx/$1" "$2" <<'PY'
import sys
path, program = sys.argv[1:]
t = open(path).read()
exec(program)
open(path, "w").write(t)
PY
}
# repack <name> <file> <program> <words-program>: the packed file fails --check, --write rewrites it, the rewrite
# passes --check and holds the same words as the packed form (<words-program> prints them from file `p`).
repack() {
  local name="$1" file="$2" program="$3" words="$4"
  fresh
  edit "$file" "$program"
  python3 -c "$words" "$work/fx/$file" > "$work/words-before"
  run "$name (packed)" 1 "$file" --check
  run "$name (rewritten)" 0 "rewrote" --write
  run "$name (stable)" 0 "every list is one entry per line" --check
  python3 -c "$words" "$work/fx/$file" > "$work/words-after"
  cases=$((cases + 1))
  cmp -s "$work/words-before" "$work/words-after" \
    || fail_case "$name: the rewrite holds other entries" "$(diff "$work/words-before" "$work/words-after" || true)"
}

fresh
run committed 0 "every list is one entry per line" --check

# The parts file: a part's phases packed back onto its header line.
repack parts-packed tacenta-proofs/scripts/no-sorry-parts.txt \
  "import re; t = re.sub(r':\n((?:  \S+\n)+)', lambda m: ': ' + ' '.join(x.strip() for x in m.group(1).split('\n') if x) + '\n', t)" \
  "import sys; print(open(sys.argv[1]).read().split())"
grep -q '^  repair$' "$work/fx/tacenta-proofs/scripts/no-sorry-parts.txt" || fail_case "parts-packed: repair is not on a line of its own"

# The control arrays and the loop's list of the proof-script cases.
repack arrays-packed tooling/tests/run-proof-script-cases.sh \
  "import re; t = re.sub(r'py_controls=\(\n((?:  \S+\n)+)\)', lambda m: 'py_controls=(' + ' '.join(m.group(1).split()) + ')', t)" \
  "import sys, re; print(re.search(r'py_controls=\(([^)]*)\)', open(sys.argv[1]).read()).group(1).split())"
repack loop-packed tooling/tests/run-proof-script-cases.sh \
  "t = t.replace('  check-refuted-records.sh \\\\\n  check-refuted-records-negatives.sh \\\\\n', '  check-refuted-records.sh check-refuted-records-negatives.sh \\\\\n')" \
  "import sys, re; print(re.search(r'for called in ((?:[^;])*); do', open(sys.argv[1]).read()).group(1).replace(chr(92), ' ').split())"

# A row of the gate inventory with more than three controls, packed onto one line.
repack inventory-packed tooling/gate-inventory.json \
  "import re; t = re.sub(r'\"controls\": \[\n((?:    .*\n)+?)  \]', lambda m: '\"controls\": [' + ' '.join(x.strip() for x in m.group(1).split('\n') if x) + ']', t, count=1)" \
  "import sys, json; print(json.load(open(sys.argv[1])))"

# A table of the obligations file with a row over the limit: rewritten as a list, the cells kept.
repack table-long-row ASSURANCE-OBLIGATIONS.md \
  "t = t.replace('| P3 | Contract decisions before fixture generation |', '| P3 | Contract decisions before fixture generation. ' + 'A clause that is long. ' * 60 + '|', 1)" \
  "import sys, re; t = open(sys.argv[1]).read(); print(t.count('A clause that is long.'), [x in t for x in ('Contract decisions before fixture generation.', 'Requirement evidence index', 'BLOCKING for current ambiguity in refusal, vector and public-decoder contracts.')])"
grep -q '^  Contract decisions before fixture generation\.$' "$work/fx/ASSURANCE-OBLIGATIONS.md" \
  || fail_case "table-long-row: the long row's first sentence is not on a line of its own"
# The short tables stay tables.
grep -q '^| Item | Current risk | Package |$' "$work/fx/ASSURANCE-OBLIGATIONS.md" \
  || fail_case "table-long-row: a table with no long row was rewritten"

# A list that cannot be rewritten without changing it is refused, and nothing is written.
fresh
edit tooling/tests/run-proof-script-cases.sh \
  "t = t.replace('py_controls=(\n  check-lifecycle-translation-coverage.py\n', 'py_controls=(\"check-lifecycle-translation-coverage.py check-atomicity-negatives.py\n', 1)"
cp "$work/fx/tooling/tests/run-proof-script-cases.sh" "$work/before"
run unterminated-quote 2 "an unterminated quote" --write
cases=$((cases + 1))
cmp -s "$work/before" "$work/fx/tooling/tests/run-proof-script-cases.sh" || fail_case "unterminated-quote: the file was written"

# A table whose rows do not have the header's number of cells is refused rather than guessed at.
fresh
edit ASSURANCE-OBLIGATIONS.md \
  "t = t.replace('| P3 | Contract decisions before fixture generation |', '| P3 | Contract decisions | ' + 'x ' * 600 + '| extra |', 1)"
run ragged-row 2 "cells under" --write

echo "reflow-shared-lists-cases: $cases cases (the committed files in the form; each list packed back refused by --check, rewritten by --write with the same entries and stable; a long table row rewritten as a list with the short tables kept; an unterminated quote and a ragged row refused with nothing written) gave the expected result"
