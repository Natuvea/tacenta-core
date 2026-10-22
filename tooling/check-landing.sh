#!/usr/bin/env bash
# Check that what the tooling for new proof modules added to the shared files is still there.
#
#   bash tooling/check-landing.sh
#
# A merge or a rebase that resolves a conflict in tooling/gate-inventory.json or ASSURANCE-OBLIGATIONS.md by taking
# one side whole drops the other side's additions, and the generated inventory is then written without them, so no
# other check sees the loss. tooling/landing-rows.txt lists those additions: each `row <gate>` must be a row of
# tooling/gate-inventory.json whose gate is a file in the tree and is named in tacenta-proofs/GATE-INVENTORY.md,
# and each `section <file> <heading>` a line of that file. It prints what is missing and exits 1, or exits 0.
# tooling/regenerate-generated.sh runs it last, and so does the gate controls' step.
#
# What it does not check: that a row's text is the one this change wrote, or anything not on the list.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
python3 - <<'PY'
import json, sys
from pathlib import Path

missing = []
rows = {r["gate"] for r in json.loads(Path("tooling/gate-inventory.json").read_text())["rows"]}
table = Path("tacenta-proofs/GATE-INVENTORY.md").read_text()
for number, line in enumerate(Path("tooling/landing-rows.txt").read_text().split("\n"), 1):
    if not line.strip() or line.startswith("#"):
        continue
    kind, _, rest = line.partition(" ")
    if kind == "row":
        if rest not in rows:
            missing.append(f"tooling/gate-inventory.json has no row for {rest}")
        elif f"`{rest}`" not in table:
            missing.append(f"tacenta-proofs/GATE-INVENTORY.md does not name {rest}")
        if not Path(rest).is_file():
            missing.append(f"{rest} is not a file")
    elif kind == "section":
        name, _, heading = rest.partition(" ")
        if not Path(name).is_file() or heading not in Path(name).read_text().split("\n"):
            missing.append(f"{name} has no line `{heading}`")
    else:
        missing.append(f"tooling/landing-rows.txt:{number} is not `row <gate>` or `section <file> <heading>`")
for m in missing:
    print(f"check-landing: MISSING: {m}", file=sys.stderr)
if missing:
    print(f"check-landing: {len(missing)} addition(s) of the tooling change are missing; restore them "
          "(git diff the change's commits for the file) and run the generators again", file=sys.stderr)
    sys.exit(1)
print("check-landing: every listed row and section is present")
PY
