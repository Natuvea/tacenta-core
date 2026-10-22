#!/usr/bin/env bash
# Run the negative controls for gates that had none, in one CI step:
#
#   run-source-gate-cases.sh     conflict markers, proof hygiene, the authentication-boundary registry
#   run-proof-script-cases.sh    no-sorry.sh, verify.sh, check-translation-coverage.sh (stubbed Lean)
#   run-lean-code-differential-cases.sh  attest.py's Lean stripper against the character loop it replaced
#   run-build-evidence-pack-build-cases.sh  the build direction of the evidence-pack builder
#   run-install-script-cases.sh  the digest and revision checks of the elan, actionlint and Lake installers
#   check-generation-negatives.sh  the --check mode of the eleven assemble and port scripts
#   run-regenerate-in-container-cases.sh  the comparison and the --check verdict of regenerate-in-container.sh, with a stub docker
#   run-attest-negatives-shard-cases.sh  the sharding of check-attest-negatives.sh: a slice that is skipped, run
#                                  twice or lost, a shard that fails or is killed, and the seam that cannot reach CI
#   run-attest-negatives-slice-cases.sh  the slices of that run in CI and their combiner: a slice missing, repeated,
#                                  relabelled, of another commit or script, cut short, or with shards that do not add up
#   run-no-sorry-parts-cases.sh  the parts of no-sorry.sh in CI and their combiner: a part missing, repeated,
#                                  relabelled, of another commit, tree, script or cache, failed, or with a phase in
#                                  no part or two; the dispatcher's slices; the committed parts file against the script
#   run-gate-inventory-cases.sh and run-mutate-gates-cases.sh  the inventory generator and the mutation harness
#   run-reflow-shared-lists-cases.sh, reflow-shared-lists.py --check  the lists every new proof module edits are
#                                  one entry per line (a packed list refused, the rewrite keeps every entry)
#   run-new-lifecycle-module-cases.sh  the module scaffold and pin generator: refused anchors, the files and lines
#                                  a scaffold writes, the pins step's lists and count, with no Lean
#   run-check-proof-module-preflight-cases.sh, check-proof-module-preflight.py --all  the preflight of a lifecycle
#                                  module (not-shown lists, the controls' mechanism, counts in the prose, terms
#                                  kept out of the text) against planted faults, and every module against its
#                                  baseline of known findings
#   run-check-merge-exactness-cases.sh, run-regenerate-generated-cases.sh  the merge-exactness check and the
#                                  regeneration of generated files after a merge
#   run-check-landing-cases.sh, check-landing.sh  the additions of the tooling change survive a merge or a rebase
#   gate-inventory.py --check    the inventory of gates and controls is current and every CI step has a row
#
# Each runner plants its changes in a disposable worktree of the commit under test (the lean-code one
# only reads the tree) and needs no Lean toolchain. They are run one after another; the first failure stops the run. The shard runner runs
# check-attest-negatives.sh itself on a few of its cases, with the real attest.py, so it and the slice runner
# are the ones that take a minute or more.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"

bash "$here/run-source-gate-cases.sh"
bash "$here/run-proof-script-cases.sh"
bash "$here/run-lean-constructs-cases.sh"
bash "$here/run-lean-code-differential-cases.sh"
bash "$here/run-check-refuted-records-cases.sh"
bash "$here/run-install-script-cases.sh"
bash "$here/run-build-evidence-pack-build-cases.sh"
bash "$root/tacenta-proofs/scripts/check-generation-negatives.sh"
bash "$here/run-attest-negatives-shard-cases.sh"
bash "$here/run-attest-negatives-slice-cases.sh"
bash "$here/run-no-sorry-parts-cases.sh"
bash "$here/run-gate-inventory-cases.sh"
bash "$here/run-mutate-gates-cases.sh"
bash "$here/run-regenerate-in-container-cases.sh"
bash "$here/run-reflow-shared-lists-cases.sh"
python3 "$root/tooling/reflow-shared-lists.py" --check
bash "$here/run-new-lifecycle-module-cases.sh"
bash "$here/run-check-proof-module-preflight-cases.sh"
# The baseline may not grow unseen: where the checkout has origin/main, a key added since then needs a reason.
if git -C "$root" rev-parse --verify --quiet origin/main >/dev/null; then
  python3 "$root/tooling/check-proof-module-preflight.py" --all --baseline "$root/tooling/proof-module-preflight-baseline.json" \
    --baseline-base origin/main
else
  python3 "$root/tooling/check-proof-module-preflight.py" --all --baseline "$root/tooling/proof-module-preflight-baseline.json"
fi
bash "$here/run-check-merge-exactness-cases.sh"
bash "$here/run-regenerate-generated-cases.sh"
bash "$here/run-check-landing-cases.sh"
bash "$root/tooling/check-landing.sh"
python3 "$root/tooling/gate-inventory.py" --check
