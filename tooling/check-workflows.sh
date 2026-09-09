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
# 4. No `run:` script hands `curl` or `wget` output to an interpreter unread.
#    Downloading to a file, checking its sha256 against a digest the workflow
#    pins, and then running it is fine, and is the pattern the elan install
#    uses; what is refused is executing whatever a URL serves today. The rule
#    is textual, over each line after joining backslash continuations and
#    joining a line that ends in a pipe with the one after it. Refused: a
#    line in which `curl` or `wget` is followed, anywhere later on the line,
#    by a pipe into `sh`, `bash`, `zsh`, `dash`, `ksh`, `python`, `perl`,
#    `ruby` or `node`, with any words between the pipe and the interpreter
#    (`sudo -u root -E env A=1 bash`) and through any intermediate pipe stage
#    (`curl ... | tee log | sh`); and, anywhere on a line, a download inside
#    a command substitution (`sh -c "$(curl ...)"`, `eval "$(curl ...)"`, or
#    the backtick form) or a process substitution (`bash <(curl ...)`), which
#    is the same download handed to whatever reads it.
# 5. A job-level `container:` image and every `services.<name>.image` is
#    pinned by `@sha256:` digest, the same rule as a `docker://` step. A tag
#    names whatever the registry serves under it today.
# 6. A `run:` script that mentions `curl` or `wget` and also runs an
#    interpreter on a path (`bash something`, `python3 something`) or marks a
#    file executable (`chmod +x`, a numeric mode) must also mention `sha256sum`,
#    `shasum` or `sha256` somewhere in the same script: the download-then-run
#    shape without the check between is a download executed unread, one step
#    slower than a pipe. Textual, as rule 4 is; a script that mentions the
#    checksum tool without running it passes this and should not pass review.
#
# The cases each rule is held to, passing and failing, are the files under
# `tooling/tests/check-workflows-cases/`, which
# `tooling/tests/run-check-workflows-cases.sh` runs against this script.
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

# Rules 4 and 6 share the interpreter list. `sha256sum` is not matched by
# `sh\b`, which is what lets the download-then-check pattern through.
INTERPRETER = r"(sh|bash|zsh|dash|ksh|python[0-9.]*|perl|ruby|node)"
DOWNLOAD = r"\b(curl|wget)\b"
# A shell word that does not end the command: no pipe, no `;`, no `&`. The
# words between a pipe and the interpreter may be anything of that shape
# (`sudo`, `-u`, `root`, `env`, `A=1`), and the pipe may be any pipe after
# the download, not only the first, so an intermediate `tee` does not hide
# the shell at the end. A `||` is not a pipe.
WORD = r"[^|;&\s]+"
PIPE_TO_SHELL = re.compile(
    DOWNLOAD + r".*(?<!\|)\|(?!\|)\s*(?:" + WORD + r"\s+)*?" + INTERPRETER + r"\b"
)
# A download inside `$( )`, backticks or `<( )`, with any leading words
# (`$(sudo -E curl ...)`). Where the result goes does not matter: `sh -c`,
# `eval`, `source`, or a variable read later all run it unread.
SUBST_DOWNLOAD = re.compile(
    r"(\$\(|`|<\()\s*(?:[^|;&()`\s]+\s+)*?" + DOWNLOAD
)
# Rule 6's two halves. The interpreter must start a word (`x.sh arg` is a
# script path, not `sh arg`) and take an argument on the same line.
RUNS_A_PATH = re.compile(r"(?<![\w.-])" + INTERPRETER + r"[ \t]+\S+")
MARKS_EXECUTABLE = re.compile(r"\bchmod\b[^;&|\n]*(\+[a-zA-Z]*x|\b[0-7]{3,4}\b)")
CHECKSUM = re.compile(r"sha256|shasum", re.I)
IMAGE_DIGEST = re.compile(r"@sha256:[0-9a-f]{64}$")

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

def check_image(f, name, what, image):
    """Rules 1 and 5 for a container image, wherever it is named."""
    if not isinstance(image, str) or not IMAGE_DIGEST.search(image):
        complain("%s job '%s' %s '%s' -- pin a container image by its "
                 "`@sha256:` digest, not by tag" % (f, name, what, image))

def check_pin(f, name, what, uses):
    """Rule 1 for one `uses:` value: a step's action, a job's reusable
    workflow, or a container image."""
    if uses.startswith("./"):
        return  # a path in this repository, at the commit already checked out
    if uses.startswith("docker://"):
        check_image(f, name, what, uses)
        return
    ref = uses.rsplit("@", 1)[1] if "@" in uses else ""
    if not re.fullmatch(r"[0-9a-f]{40}", ref):
        complain("%s job '%s' %s '%s' -- pin by 40-char commit digest, with "
                 "the tag in a trailing comment" % (f, name, what, uses))

def check_run(f, name, run):
    """Rules 4 and 6 for one `run:` script."""
    for line in pipeline_lines(run):
        if PIPE_TO_SHELL.search(line) or SUBST_DOWNLOAD.search(line):
            complain("%s job '%s' runs a download unread: %s -- download to "
                     "a file, check its sha256 against a pinned digest, then "
                     "run it" % (f, name, line.strip()))
    joined = "\n".join(pipeline_lines(run))
    if re.search(DOWNLOAD, joined) and not CHECKSUM.search(joined) \
            and (RUNS_A_PATH.search(joined) or MARKS_EXECUTABLE.search(joined)):
        complain("%s job '%s' has a `run:` script in which something is "
                 "downloaded then executed without a checksum -- check the "
                 "file's sha256 against a pinned digest between the two"
                 % (f, name))

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

        # Rule 5. The job's own container, as a bare image string or a
        # mapping with `image:`, and each service container.
        container = job.get("container")
        if isinstance(container, dict):
            container = container.get("image")
        if container is not None:
            check_image(f, name, "runs in container", container)
        services = job.get("services")
        if isinstance(services, dict):
            for svc, spec in services.items():
                image = spec.get("image") if isinstance(spec, dict) else spec
                check_image(f, name, "service '%s' image" % svc, image)

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

            # Rules 4 and 6.
            run = step.get("run")
            if isinstance(run, str):
                check_run(f, name, run)

print("check-workflows: %d workflow file(s) parse" % len(files))
sys.exit(bad)
PY
