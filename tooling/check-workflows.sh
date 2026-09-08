#!/usr/bin/env bash
# Reject a workflow file that GitHub cannot parse.
#
# A trailing colon in an unquoted YAML scalar is a mapping indicator, so a
# `run:` step that ends in a test filter such as `crypto::` stops the file
# parsing. A push then goes out with no CI behind it: a run that cannot parse
# its workflow fails in zero seconds, and neither the run list nor the commit
# status distinguishes that from a real break.
#
# The check cannot live inside the workflow it protects: if the file does not
# parse, nothing in it runs, including this. So it belongs in the pre-push hook,
# where it fails on the machine that wrote the change.
#
# Scope is deliberately narrow. This is a parse check and a few invariants, not
# a schema validator. `actionlint` does the fuller job and is worth adding when
# it can be pinned by digest; parsing is the failure this guards against.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

# A missing tool is a skip locally and a failure in CI, the same rule the
# verification gate follows: a gate that cannot run must not report
# green on the runner, which is where the pin check is load-bearing.
cannot_run() {
  echo "check-workflows: $1" >&2
  if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    echo "check-workflows: this is CI -- a check that cannot run is a failure, not a skip" >&2
    exit 1
  fi
  exit 0
}

if ! command -v python3 >/dev/null 2>&1; then
  cannot_run "python3 not found, skipping"
fi
if ! python3 -c 'import yaml' >/dev/null 2>&1; then
  cannot_run "pyyaml not installed, skipping (pip install pyyaml)"
fi

# **Every workflow directory in the tree, not only the root.** GitHub runs
# only the root `.github/workflows`, but a component that is lifted into its
# own repository takes its nested one with it, live:
# `tacenta-proofs/.github/workflows/verify.yml` is one such, and is held to
# the same pins as the root workflows.
python3 - <<'PY'
import re
import sys, os, glob
import yaml

bad = 0
files = sorted(
    f for f in glob.glob("**/.github/workflows/*.y*ml", recursive=True)
    if "/.lake/" not in f and "/target/" not in f and "/node_modules/" not in f
)
if not files:
    print("check-workflows: no workflow files found")
    sys.exit(0)

for f in files:
    try:
        doc = yaml.safe_load(open(f))
    except yaml.YAMLError as e:
        print("check-workflows: %s does not parse as YAML" % f, file=sys.stderr)
        print("  %s" % str(e).replace("\n", "\n  "), file=sys.stderr)
        bad = 1
        continue

    if not isinstance(doc, dict):
        print("check-workflows: %s is not a mapping" % f, file=sys.stderr)
        bad = 1
        continue

    # `on:` is the YAML 1.1 boolean True once parsed, which is a trap worth
    # naming rather than rediscovering.
    if True not in doc and "on" not in doc:
        print("check-workflows: %s has no trigger (`on:`)" % f, file=sys.stderr)
        bad = 1

    jobs = doc.get("jobs")
    if not isinstance(jobs, dict) or not jobs:
        print("check-workflows: %s defines no jobs" % f, file=sys.stderr)
        bad = 1
        continue

    for name, job in jobs.items():
        if not isinstance(job, dict):
            print("check-workflows: %s job '%s' is not a mapping" % (f, name), file=sys.stderr)
            bad = 1
            continue
        if "runs-on" not in job and "uses" not in job:
            print("check-workflows: %s job '%s' has neither runs-on nor uses"
                  % (f, name), file=sys.stderr)
            bad = 1

        # Third-party actions must be pinned by commit digest, not by tag.
        # A tag is movable: whoever controls the action repository can change
        # what `@v4` means after review and before the next run, and a
        # workflow runs with credentials. A machine check
        # keeps every workflow at the same standard, rather than some pinned
        # and some not.
        for step in job.get("steps") or []:
            if not isinstance(step, dict):
                continue
            uses = step.get("uses")
            if not isinstance(uses, str) or "@" not in uses:
                continue
            ref = uses.rsplit("@", 1)[1]
            if not re.fullmatch(r"[0-9a-f]{40}", ref):
                print("check-workflows: %s job '%s' uses '%s' -- pin by 40-char "
                      "commit digest, with the tag in a trailing comment"
                      % (f, name, uses), file=sys.stderr)
                bad = 1

print("check-workflows: %d workflow file(s) parse" % len(files))
sys.exit(bad)
PY
