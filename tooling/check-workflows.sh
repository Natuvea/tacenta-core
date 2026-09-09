#!/usr/bin/env bash
# Reject a workflow file that GitHub cannot parse, or that breaks one of the
# invariants every workflow in this tree is held to.
#
# A trailing colon in an unquoted YAML scalar is a mapping indicator, so a
# `run:` step that ends in a test filter such as `crypto::` stops the file
# parsing. A push then goes out with no CI behind it: a run that cannot parse
# its workflow fails in zero seconds, and neither the run list nor the commit
# status distinguishes that from a real break.
#
# The parse check cannot live only inside the workflow it protects: if the
# file does not parse, nothing in it runs, including this. So the `checks` job
# runs it for every *other* workflow, and the pre-push hook in `.githooks/`
# (CONTRIBUTING.md says how to enable it) runs it for all of them on the
# machine that wrote the change.
#
# Scope is deliberately narrow. This is a parse check and a few invariants, not
# a schema validator. `actionlint` does the fuller job and is worth adding when
# it can be pinned by digest; parsing is the failure this guards against.
#
# The invariants, each stated here because the message that fires names it:
#
# 1. Every third-party action is pinned by a 40-character commit digest, with
#    the tag in a trailing comment. A tag is movable. The same rule covers a
#    job-level `uses:`, which calls a reusable workflow by ref, and a
#    container step (`uses: docker://`), which is pinned by the image's
#    `@sha256:` digest rather than its tag.
# 2. Every workflow declares a top-level `permissions:` block, so the token a
#    job holds is what the file says and not the repository default.
# 3. Every `actions/checkout` step sets `persist-credentials: false`, so the
#    token is not left in `.git/config` for a later step to read.
# 4. No `run:` script pipes `curl` or `wget` output into an interpreter.
#    Downloading to a file, checking its sha256 against a digest the workflow
#    pins, and then running it is fine, and is the pattern the elan install
#    uses; what is refused is executing whatever a URL serves today, unread.
#    The rule is textual: a line (after joining backslash continuations, and
#    joining a line that ends in a pipe with the one after it) in which `curl`
#    or `wget` is followed by a pipe into `sh`, `bash`, `zsh`, `python`,
#    `perl`, `ruby` or `node`, with or without `sudo` or `env`; or a process
#    substitution `<(curl ...)`, which is the same download handed to
#    whatever reads it as a file (`bash <(curl ...)`).
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

# Rule 4's shape. `sha256sum` is not matched by `sh\b`, which is what lets
# the download-then-check pattern through.
INTERPRETER = r"(sh|bash|zsh|dash|ksh|python[0-9.]*|perl|ruby|node)"
PIPE_TO_SHELL = re.compile(
    r"\b(curl|wget)\b[^|\n]*\|\s*(sudo\s+(-\S+\s+)*)?(env\s+(\S+=\S+\s+)*)?"
    + INTERPRETER + r"\b"
)
SUBST_DOWNLOAD = re.compile(r"<\(\s*(sudo\s+(-\S+\s+)*)?(curl|wget)\b")

def pipeline_lines(script):
    """The script's lines with two joins applied first, so that a pipeline
    split across lines is still seen as one: a backslash-newline continuation,
    and a line that ends in a pipe, whose command is the next line (`curl ... |`
    then `sh -s -- -y`)."""
    lines = []
    for line in script.replace("\\\n", " ").splitlines():
        if lines and lines[-1].rstrip().endswith("|"):
            lines[-1] = lines[-1].rstrip() + " " + line.lstrip()
        else:
            lines.append(line)
    return lines

def complain(msg):
    global bad
    print("check-workflows: " + msg, file=sys.stderr)
    bad = 1

def check_pin(f, name, what, uses):
    """Rule 1 for one `uses:` value: a step's action, a job's reusable
    workflow, or a container image."""
    if uses.startswith("./"):
        return  # a path in this repository, at the commit already checked out
    if uses.startswith("docker://"):
        if not re.search(r"@sha256:[0-9a-f]{64}$", uses):
            complain("%s job '%s' %s '%s' -- pin a container image by its "
                     "`@sha256:` digest, not by tag" % (f, name, what, uses))
        return
    ref = uses.rsplit("@", 1)[1] if "@" in uses else ""
    if not re.fullmatch(r"[0-9a-f]{40}", ref):
        complain("%s job '%s' %s '%s' -- pin by 40-char commit digest, with "
                 "the tag in a trailing comment" % (f, name, what, uses))

for f in files:
    try:
        doc = yaml.safe_load(open(f))
    except yaml.YAMLError as e:
        complain("%s does not parse as YAML" % f)
        print("  %s" % str(e).replace("\n", "\n  "), file=sys.stderr)
        continue

    if not isinstance(doc, dict):
        complain("%s is not a mapping" % f)
        continue

    # `on:` is the YAML 1.1 boolean True once parsed, which is a trap worth
    # naming rather than rediscovering.
    if True not in doc and "on" not in doc:
        complain("%s has no trigger (`on:`)" % f)

    # Rule 2. A mapping or the string forms GitHub accepts (`read-all`,
    # `write-all`); anything else, or nothing, fails.
    perms = doc.get("permissions")
    if not isinstance(perms, (dict, str)) or perms == {}:
        complain("%s has no top-level `permissions:` block -- declare the "
                 "token scope the jobs hold (usually `contents: read`)" % f)

    jobs = doc.get("jobs")
    if not isinstance(jobs, dict) or not jobs:
        complain("%s defines no jobs" % f)
        continue

    for name, job in jobs.items():
        if not isinstance(job, dict):
            complain("%s job '%s' is not a mapping" % (f, name))
            continue
        if "runs-on" not in job and "uses" not in job:
            complain("%s job '%s' has neither runs-on nor uses" % (f, name))

        # Rule 1 at the job level. A reusable workflow is called by ref, and
        # that ref is as movable as an action's tag; it runs with this
        # workflow's token.
        if isinstance(job.get("uses"), str):
            check_pin(f, name, "calls reusable workflow", job["uses"])

        for step in job.get("steps") or []:
            if not isinstance(step, dict):
                continue

            # Rule 1. Third-party actions must be pinned by commit digest,
            # not by tag. A tag is movable: whoever controls the action
            # repository can change what `@v4` means after review and before
            # the next run, and a workflow runs with credentials. A machine
            # check keeps every workflow at the same standard, rather than
            # some pinned and some not.
            uses = step.get("uses")
            if isinstance(uses, str):
                check_pin(f, name, "uses", uses)

                # Rule 3. The checkout action writes the job token into the
                # checked-out repository's git config unless told not to.
                if uses.startswith("actions/checkout@"):
                    with_ = step.get("with") or {}
                    if not isinstance(with_, dict) \
                            or with_.get("persist-credentials") is not False:
                        complain("%s job '%s' checks out without "
                                 "`persist-credentials: false`" % (f, name))

            # Rule 4.
            run = step.get("run")
            if isinstance(run, str):
                for line in pipeline_lines(run):
                    if PIPE_TO_SHELL.search(line) or SUBST_DOWNLOAD.search(line):
                        complain("%s job '%s' pipes a download into an "
                                 "interpreter: %s -- download to a file, check "
                                 "its sha256 against a pinned digest, then run "
                                 "it" % (f, name, line.strip()))

print("check-workflows: %d workflow file(s) parse" % len(files))
sys.exit(bad)
PY
