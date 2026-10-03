#!/usr/bin/env bash
# Run the negative controls for gates that had none, in one CI step:
#
#   run-source-gate-cases.sh     conflict markers, proof hygiene, the authentication-boundary registry
#   run-proof-script-cases.sh    no-sorry.sh, verify.sh, check-translation-coverage.sh (stubbed Lean)
#   run-build-evidence-pack-build-cases.sh  the build direction of the evidence-pack builder
#   run-install-script-cases.sh  the digest and revision checks of the elan, actionlint and Lake installers
#   check-generation-negatives.sh  the --check mode of the eleven assemble and port scripts
#   run-regenerate-in-container-cases.sh  the comparison and the --check verdict of regenerate-in-container.sh, with a stub docker
#   run-gate-inventory-cases.sh and run-mutate-gates-cases.sh  the inventory generator and the mutation harness
#   gate-inventory.py --check    the inventory of gates and controls is current and every CI step has a row
#
# Each runner plants its changes in a disposable worktree of the commit under test and needs no Lean
# toolchain. They are run one after another; the first failure stops the run.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"

bash "$here/run-source-gate-cases.sh"
bash "$here/run-proof-script-cases.sh"
bash "$here/run-install-script-cases.sh"
bash "$here/run-build-evidence-pack-build-cases.sh"
bash "$root/tacenta-proofs/scripts/check-generation-negatives.sh"
bash "$here/run-gate-inventory-cases.sh"
bash "$here/run-mutate-gates-cases.sh"
bash "$here/run-regenerate-in-container-cases.sh"
python3 "$root/tooling/gate-inventory.py" --check
