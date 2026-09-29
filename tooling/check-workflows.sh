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
# 7. A job's `runs-on` names `self-hosted` only inside an expression that also
#    requires `github.event_name == 'push'` and
#    `github.ref == 'refs/heads/main'`. This rule is not the boundary: a pull
#    request runs its own copy of the workflow, and what keeps it off the
#    self-hosted runner is the runner group, which GitHub lets only this
#    repository's workflow, as it is on main, use. The rule keeps the file
#    saying the same thing, so a pull request is not queued for a runner it
#    cannot have. Textual, as rules 4 and 6 are.
# 8. No job is unconditionally disabled by a statically false `if` value. A
#    required check that can be turned off in the workflow being reviewed can
#    report green without running its command. A job that uses the receipt
#    action with a `required` or `conditional` classification may therefore
#    have no job-level `if` or `continue-on-error` at all, with two named
#    exceptions: the PR-only sign-off job and the collector's exact
#    `always()` condition. `fromJSON('false')` and `fromJSON('true')` are
#    constants too, even though they are expressions.
# 9. A step is the receipt action when its `uses` resolves to
#    `.github/actions/assurance-receipt` once the path is normalised, however
#    it is spelled. Its `id`, `classification` and `command` are literals (no
#    `${{ }}`), its `required-outcomes` names exactly the job's `run` steps,
#    each bound to that step's own `steps.<id>.outcome`, and no other action
#    calls it (a wrapper would hide the call from the job that makes it).
#    In such a job a step may not run another local action, may not set a
#    `shell` other than `bash`, and may carry an `if` only where the step's id,
#    `if` and `run` text all match an entry in `ALLOWED_REQUIRED_STEP_IF`.
#    `defaults.run.shell` is `bash` or absent, at the workflow and job level.
#    Every workflow and action file is read with a loader that refuses a
#    repeated mapping key, so this script and the runner read the same value.
#    Local composite actions are found by following `uses: ./` from the
#    workflows, not only by their location.
# 10. The expected form of the required workflow is a file.
#    `tooling/required-steps.json` holds `.github/workflows/ci.yml` and the
#    receipt action as data: every key of every job and step except the
#    `name:` labels. A workflow named there must equal it, so a change to a
#    command, its shell, environment, working directory, `if`,
#    `continue-on-error`, timeout, position, the job it belongs to, or the
#    inputs to the receipt is a difference from that file, and is made by
#    editing that file in the same change. `--write-required-steps` rewrites
#    the file from the tree; the diff of the file is what a reader reviews.
#
# What this script does not do, said plainly. It runs from the tree it is
# checking. A pull request runs its own copy of the workflow, of this script and
# of the manifest above, so a change that edits all three is judged by its own
# edit; nothing here routes such a change to a reviewer (there is no CODEOWNERS
# file), and whether a review is required is a repository setting this script
# cannot see. The checks that read shell text (rules 4 and 6, and the refusal
# of a `run` that is only `true`, `:` or `exit 0`) are tripwires for a careless
# edit, not a definition of every command that succeeds without doing its
# work. For the files the manifest pins the command text is compared whole, so
# those tripwires matter only for the workflows it does not name.
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
python3 - "$@" <<'PY'
import re
import sys, os, glob, json, posixpath
import yaml

# The receipt action, as a repository path. A step is that action when its
# `uses` resolves to this once the path is normalised.
RECEIPT_ACTION = ".github/actions/assurance-receipt"
# The expected form of the required workflow and of the receipt action.
REQUIRED_STEPS_FILE = "tooling/required-steps.json"
REQUIRED_WORKFLOWS = [".github/workflows/ci.yml"]
REQUIRED_ACTIONS = [RECEIPT_ACTION + "/action.yml"]

WRITE_REQUIRED_STEPS = False
for argument in sys.argv[1:]:
    if argument == "--write-required-steps":
        WRITE_REQUIRED_STEPS = True
    else:
        print("usage: check-workflows.sh [--write-required-steps]", file=sys.stderr)
        sys.exit(2)

bad = 0


class StrictLoader(yaml.SafeLoader):
    """`yaml.safe_load` that refuses a mapping with a repeated key, which
    PyYAML would read as its last value and another reader might not."""


def _mapping_without_repeats(loader, node, deep=False):
    seen = set()
    for key_node, _ in node.value:
        if key_node.tag == "tag:yaml.org,2002:merge":
            continue
        key = loader.construct_object(key_node, deep=deep)
        if key in seen:
            raise yaml.constructor.ConstructorError(
                None, None, "the key %r is repeated in one mapping" % (key,),
                key_node.start_mark)
        seen.add(key)
    return yaml.SafeLoader.construct_mapping(loader, node, deep)


StrictLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, _mapping_without_repeats)


def load_yaml(path):
    with open(path) as handle:
        return yaml.load(handle, Loader=StrictLoader)


def excluded(f):
    return "/.lake/" in f or "/target/" in f or "/node_modules/" in f


# **Every workflow directory in the tree, not only the root.** GitHub runs
# only the root `.github/workflows`, but a component that is lifted into its
# own repository takes its nested one with it, live:
# `tacenta-proofs/.github/workflows/verify.yml` is one such, and is held to
# the same pins as the root workflows.
files = sorted(
    f for f in glob.glob("**/.github/workflows/*.y*ml", recursive=True)
    if not excluded(f)
)
# Composite actions under a `.github/actions` directory; the ones a workflow
# reaches by `uses: ./path` are added to this as they are found, so an action
# outside that directory or inside a dot-directory is read too.
action_files = sorted(
    f for f in glob.glob("**/.github/actions/**/action.y*ml", recursive=True)
    if not excluded(f)
)
if not files:
    print("check-workflows: no workflow files found", file=sys.stderr)
    sys.exit(1)

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

def strip_outer_parentheses(expr):
    while expr.startswith("(") and expr.endswith(")"):
        depth = 0
        enclosed = True
        for i, char in enumerate(expr):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0 and i != len(expr) - 1:
                    enclosed = False
                    break
        if not enclosed or depth != 0:
            break
        expr = expr[1:-1]
    return expr

def split_top_level(expr, operator):
    depth = 0
    for i, char in enumerate(expr):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif depth == 0 and expr.startswith(operator, i):
            return expr[:i], expr[i + len(operator):]
    return None

def constant_truth(value):
    """Return True/False for a static GitHub expression, else None."""
    if value is True:
        return True
    if value is False:
        return False
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        return value != 0
    if not isinstance(value, str):
        return None
    expr = re.sub(r"\s+", "", value).lower()
    if expr.startswith("${{") and expr.endswith("}}"):
        expr = expr[3:-2]
    expr = strip_outer_parentheses(expr)
    if expr in ("false", "0", "null", "''", '""'):
        return False
    if expr in ("true", "1"):
        return True
    # GitHub's expression evaluator coerces these JSON literals to booleans;
    # treating them as opaque text lets a disabled required job evade Rule 8.
    if expr in ("fromjson('false')", 'fromjson("false")'):
        return False
    if expr in ("fromjson('true')", 'fromjson("true")'):
        return True
    if expr.startswith("!"):
        result = constant_truth(expr[1:])
        return None if result is None else not result
    # `&&` binds more tightly than `||`; recurse in that order.
    split = split_top_level(expr, "||")
    if split is not None:
        left, right = (constant_truth(part) for part in split)
        if left is True or right is True:
            return True
        if left is False and right is False:
            return False
        return None
    split = split_top_level(expr, "&&")
    if split is not None:
        left, right = (constant_truth(part) for part in split)
        if left is False or right is False:
            return False
        if left is True and right is True:
            return True
        return None
    return None

def is_disabled_condition(value):
    return constant_truth(value) is False

def is_truthy_continue_on_error(value):
    return constant_truth(value) is True

def is_noop_run(value):
    """Return True for a step whose entire script can only succeed, in the
    three spellings this looks for.

    A required workflow step containing only `true`, `:`, or `exit 0` is not
    evidence of the check it names.  `set -e`/`set -u` are shell options, not
    work, so they are ignored when deciding whether the script is hollow. This
    is a tripwire for a careless edit and nothing more: it does not decide what
    a script does, and another spelling of a command that does nothing is not
    refused here (a workflow the manifest pins is compared as text instead).
    """
    if not isinstance(value, str):
        return False
    commands = []
    for line in value.splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        commands.extend(part.strip() for part in line.split(";") if part.strip())
    if not commands:
        return True
    for command in commands:
        if re.fullmatch(r"set\s+[-+][A-Za-z]+", command):
            continue
        if command not in ("true", ":", "exit 0"):
            return False
    return True

def normalized_expression(value):
    if not isinstance(value, str):
        return None
    return re.sub(r"\s+", "", value).lower()

def uses_local_path(uses):
    """The repository path a `./` reference names, normalised the way the
    runner resolves it (`./a/./b/`, `./a/x/../b` and `./a/b` are one path),
    else None. A path that leaves the repository is not one."""
    if not isinstance(uses, str) or not uses.startswith("./"):
        return None
    path = posixpath.normpath(uses)
    return None if path.startswith("..") else path

def is_literal(value):
    return isinstance(value, str) and "${{" not in value

def required_outcome_ids(value, f, name):
    """Parse a receipt's declared command IDs and reject malformed sets."""
    if not isinstance(value, str) or not value.strip():
        complain("%s job '%s' emits a required receipt without required "
                 "command outcomes" % (f, name))
        return set()
    ids = set()
    for item in value.split(","):
        item = item.strip()
        if not item or "=" not in item:
            complain("%s job '%s' has a malformed required command outcome "
                     "'%s'" % (f, name, item))
            continue
        step_id, outcome = (part.strip() for part in item.split("=", 1))
        expression = re.fullmatch(r"\$\{\{\s*steps\.([A-Za-z0-9_-]+)\.outcome\s*\}\}", outcome)
        if not step_id or expression is None or expression.group(1) != step_id:
            complain("%s job '%s' has a required command outcome that must "
                     "bind to the step's GitHub outcome: '%s'" % (f, name, item))
            continue
        if step_id in ids:
            complain("%s job '%s' lists required command step '%s' more than "
                     "once" % (f, name, step_id))
        ids.add(step_id)
    return ids

ALLOWED_JOB_IF = {
    "sign-off": "github.event_name=='pull_request'",
    "assurance-receipts": "always()",
}

# A job that uses the receipt action may have a conditional setup or action
# step (a cache restore, say), but a command step may not be conditionally
# skipped. This is the whole list of exceptions, keyed by job and step id and
# holding the exact `if` and the exact command, so a different command under
# the same id, or the same command under another id, is not excepted. A step
# named here is left out of the pull-request receipt when its condition cannot
# hold there.
ALLOWED_REQUIRED_STEP_IF = {
    ("translation", "translation_seed"): (
        "runner.environment=='self-hosted'",
        "bash tooling/seed-lake-packages.sh tacenta-proofs/translation",
    ),
    ("checks", "checks_39"): (
        "github.event_name=='push'",
        'bash tooling/check-signoff.sh "$BASE_SHA"',
    ),
}

def allowed_step_if(job_name, step):
    """Whether this step's `if` is one of `ALLOWED_REQUIRED_STEP_IF`."""
    entry = ALLOWED_REQUIRED_STEP_IF.get((job_name, step.get("id")))
    return (entry is not None
            and normalized_expression(step.get("if")) == entry[0]
            and step.get("run") == entry[1])

def receipt_steps(steps):
    """The steps that call the receipt action, however the path is spelled."""
    return [s for s in steps
            if isinstance(s, dict) and uses_local_path(s.get("uses")) == RECEIPT_ACTION]

# Rule 9 for a shell: `bash`, which the runner starts with its own options, or
# nothing. A `shell:` naming a command template changes what runs the script.
def check_shell(f, name, where, shell):
    if shell is not None and shell != "bash":
        complain("%s job '%s' sets `shell` to %r%s -- a required command runs "
                 "under the runner's own bash" % (f, name, shell, where))

def check_default_shell(f, name, defaults, where):
    run = defaults.get("run") if isinstance(defaults, dict) else None
    if isinstance(run, dict) and "shell" in run:
        check_shell(f, name, where, run["shell"])

# ---- the required workflow, as data -------------------------------------

def plain(value):
    """A parsed document as plain data. PyYAML reads the key `on` as the
    boolean True, and a date as a date; neither is JSON."""
    if isinstance(value, dict):
        return {("on" if key is True else str(key)): plain(item)
                for key, item in value.items()}
    if isinstance(value, list):
        return [plain(item) for item in value]
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    return str(value)

def pinned_view(doc):
    """The form the manifest holds: the whole document, less the `name:` label
    of each step, which nothing reads."""
    view = plain(doc)
    def unlabel(steps):
        if isinstance(steps, list):
            for step in steps:
                if isinstance(step, dict):
                    step.pop("name", None)
    jobs = view.get("jobs") if isinstance(view, dict) else None
    if isinstance(jobs, dict):
        for job in jobs.values():
            if isinstance(job, dict):
                unlabel(job.get("steps"))
    runs = view.get("runs") if isinstance(view, dict) else None
    if isinstance(runs, dict):
        unlabel(runs.get("steps"))
    return view

MISSING = object()

def show(value):
    text = "(absent)" if value is MISSING else json.dumps(value, ensure_ascii=False)
    return text if len(text) <= 120 else text[:117] + "..."

def step_label(step):
    if isinstance(step, dict):
        return str(step.get("id") or step.get("uses") or "(unlabelled)")
    return "(not a mapping)"

def differences(expected, actual, where):
    """(where, expected, actual) for each place two pinned views differ."""
    if isinstance(expected, dict) and isinstance(actual, dict):
        for key in expected:
            here = where + "." + key if where else key
            if key not in actual:
                yield here, expected[key], MISSING
            else:
                yield from differences(expected[key], actual[key], here)
        for key in actual:
            if key not in expected:
                yield (where + "." + key if where else key), MISSING, actual[key]
    elif (isinstance(expected, list) and isinstance(actual, list)
            and where.endswith(".steps")):
        labels_expected = [step_label(s) for s in expected]
        labels_actual = [step_label(s) for s in actual]
        if labels_expected != labels_actual:
            yield where, labels_expected, labels_actual
        else:
            for index, (label, e, a) in enumerate(zip(labels_expected, expected, actual)):
                yield from differences(e, a, "%s[%d:%s]" % (where, index, label))
    elif json.dumps(expected, sort_keys=True) != json.dumps(actual, sort_keys=True):
        yield where, expected, actual

def load_required_steps():
    """The manifest as data, or None with the complaint already made."""
    try:
        with open(REQUIRED_STEPS_FILE) as handle:
            def no_repeats(pairs):
                seen = {}
                for key, value in pairs:
                    if key in seen:
                        raise ValueError("the key %r is repeated" % key)
                    seen[key] = value
                return seen
            data = json.load(handle, object_pairs_hook=no_repeats)
    except (OSError, ValueError) as exc:
        complain("%s cannot be read: %s" % (REQUIRED_STEPS_FILE, exc))
        return None
    if (not isinstance(data, dict) or data.get("schema_version") != 1
            or not isinstance(data.get("files"), dict)):
        complain("%s is not a schema 1 manifest with a `files` object"
                 % REQUIRED_STEPS_FILE)
        return None
    return data

def write_required_steps():
    files_out = {}
    for path in REQUIRED_WORKFLOWS + REQUIRED_ACTIONS:
        if os.path.isfile(path):
            files_out[path] = pinned_view(load_yaml(path))
    document = {
        "schema_version": 1,
        "_note": (
            "The expected form of the required workflow and of the receipt "
            "action: every key of every job and step, except the step `name:` "
            "labels. tooling/check-workflows.sh fails when a file named here "
            "differs from it. Rewritten by `bash tooling/check-workflows.sh "
            "--write-required-steps`; the change to this file is the record "
            "of a change to a required command, and is meant to be read."
        ),
        "files": files_out,
    }
    with open(REQUIRED_STEPS_FILE, "w") as handle:
        handle.write(json.dumps(document, indent=2, ensure_ascii=False) + "\n")
    print("check-workflows: wrote %s for %d file(s)" % (REQUIRED_STEPS_FILE, len(files_out)))

def check_required_steps():
    present = [f for f in REQUIRED_WORKFLOWS + REQUIRED_ACTIONS if os.path.isfile(f)]
    if not os.path.exists(REQUIRED_STEPS_FILE):
        if present:
            complain("%s is missing: %s must be described there (run "
                     "`bash tooling/check-workflows.sh --write-required-steps` "
                     "and review the result)" % (REQUIRED_STEPS_FILE, ", ".join(present)))
        return
    data = load_required_steps()
    if data is None:
        return
    for path in present:
        if path not in data["files"]:
            complain("%s does not describe %s" % (REQUIRED_STEPS_FILE, path))
    for path, expected in data["files"].items():
        if not os.path.isfile(path):
            complain("%s describes %s, which is not in the tree" % (REQUIRED_STEPS_FILE, path))
            continue
        try:
            actual = pinned_view(load_yaml(path))
        except yaml.YAMLError:
            continue  # reported where the file is read
        found = list(differences(expected, actual, ""))
        for where, e, a in found[:12]:
            complain("%s differs from %s at %s: expected %s, found %s"
                     % (path, REQUIRED_STEPS_FILE, where, show(e), show(a)))
        if len(found) > 12:
            complain("%s differs from %s in %d more place(s)"
                     % (path, REQUIRED_STEPS_FILE, len(found) - 12))
        if found:
            complain("if the change to %s is intended, run `bash tooling/"
                     "check-workflows.sh --write-required-steps` and review the "
                     "diff of %s in the same change" % (path, REQUIRED_STEPS_FILE))

if WRITE_REQUIRED_STEPS:
    write_required_steps()
    sys.exit(0)

# ---- the workflows ------------------------------------------------------

local_actions = []   # every `uses: ./path` a workflow makes, to be followed

for f in files:
    try:
        doc = load_yaml(f)
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

    check_default_shell(f, "(workflow)", doc.get("defaults"), " in `defaults.run`")

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

        check_default_shell(f, name, job.get("defaults"), " in `defaults.run`")

        steps = job.get("steps") or []

        # Rules 8 and 9. A disabled job is indistinguishable from a passing
        # required check to a caller that only sees the workflow's check name.
        # A step that uses the receipt action, however its path is spelled,
        # puts the job under these rules; the classification is a literal, so
        # it cannot be decided at run time. Removing the receipt is caught by
        # the collector's missing-receipt check.
        required_receipt = False
        required_receipts = []
        for step in receipt_steps(steps):
            inputs = step.get("with") or {}
            if not isinstance(inputs, dict):
                inputs = {}
            for key in ("id", "classification", "command"):
                if not is_literal(inputs.get(key)):
                    complain("%s job '%s': the receipt action's `%s` input is "
                             "not a literal string" % (f, name, key))
            classification = inputs.get("classification")
            if classification in ("required", "conditional"):
                required_receipt = True
                required_receipts.append((step, required_outcome_ids(
                    inputs.get("required-outcomes"), f, name)))
        if "if" in job:
            actual_if = normalized_expression(job.get("if"))
            expected_if = ALLOWED_JOB_IF.get(name)
            if expected_if is None:
                if required_receipt:
                    complain("%s job '%s' emits a required receipt but has a job-level `if` -- "
                             "required jobs must run unconditionally" % (f, name))
                else:
                    complain("%s job '%s' has a job-level `if` -- required jobs "
                             "must run unconditionally" % (f, name))
            elif actual_if != expected_if:
                complain("%s job '%s' has an unapproved job-level `if`; use "
                         "the exact repository exception or remove it" % (f, name))
        if required_receipt and "continue-on-error" in job:
            complain("%s job '%s' emits a required receipt but has job-level "
                     "`continue-on-error` -- required commands must fail the job" % (f, name))
        if is_disabled_condition(job.get("if")):
            complain("%s job '%s' is unconditionally disabled by `if: false`"
                     % (f, name))
        if is_truthy_continue_on_error(job.get("continue-on-error")):
            complain("%s job '%s' enables job-level `continue-on-error` -- "
                     "required commands must fail the job" % (f, name))

        # Rule 7.
        runs_on = job.get("runs-on")
        if runs_on is not None and "self-hosted" in str(runs_on).lower():
            if not (isinstance(runs_on, str)
                    and "github.event_name == 'push'" in runs_on
                    and "github.ref == 'refs/heads/main'" in runs_on):
                complain("%s job '%s' can be scheduled on a self-hosted runner "
                         "outside a push to main -- name it only in a `runs-on` "
                         "expression that requires github.event_name == 'push' "
                         "and github.ref == 'refs/heads/main'" % (f, name))

        # Rule 1 at the job level. A reusable workflow is called by ref, and
        # that ref is as movable as an action's tag; it runs with this
        # workflow's token.
        if isinstance(job.get("uses"), str):
            check_pin(f, name, "calls reusable workflow", job["uses"])
            if uses_local_path(job["uses"]) is not None:
                local_actions.append(job["uses"])

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

        run_steps = {}
        for step in steps:
            if not isinstance(step, dict):
                continue

            if isinstance(step.get("uses"), str) and uses_local_path(step["uses"]) is not None:
                local_actions.append(step["uses"])
                if required_receipt and uses_local_path(step["uses"]) != RECEIPT_ACTION:
                    complain("%s job '%s' runs the local action '%s' -- its "
                             "commands would not be listed in the receipt; put "
                             "them in `run` steps of the job" % (f, name, step["uses"]))

            if required_receipt and "run" in step:
                step_id = step.get("id")
                if not isinstance(step_id, str) or not step_id.strip():
                    complain("%s job '%s' has a required command step without "
                             "an id" % (f, name))
                else:
                    if step_id in run_steps:
                        complain("%s job '%s' reuses required command step id "
                                 "'%s'" % (f, name, step_id))
                    run_steps[step_id] = step

            # A step-level skip or error mask is the step analogue of the
            # forbidden job-level switch above.  Static false conditions and
            # static true `continue-on-error` values are never useful evidence;
            # a dynamic mask is also forbidden on a job that emits a required
            # receipt, except the listed steps.
            if "if" in step and is_disabled_condition(step.get("if")):
                complain("%s job '%s' has a step unconditionally disabled by "
                         "`if: false`" % (f, name))
            if required_receipt and "run" in step and "if" in step:
                if not allowed_step_if(name, step):
                    complain("%s job '%s' has required command step '%s' with "
                             "an unapproved step-level `if` -- required "
                             "commands must run" % (f, name, step.get("id") or "(no id)"))
            if "continue-on-error" in step:
                if required_receipt or is_truthy_continue_on_error(step.get("continue-on-error")):
                    complain("%s job '%s' has a step-level `continue-on-error` "
                             "that can mask a required command" % (f, name))
            if required_receipt and "run" in step:
                check_shell(f, name, " on a step", step.get("shell"))
            if "run" in step:
                run_value = step.get("run")
                if not isinstance(run_value, str):
                    complain("%s job '%s' has a non-string `run` step -- a "
                             "command must be an explicit shell script" % (f, name))
                elif is_noop_run(run_value):
                    complain("%s job '%s' has a hollow `run` step -- a check "
                             "must execute a substantive command" % (f, name))

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

        # A receipt must account for every command step that can run for the
        # event that receipt represents, and for nothing else. The rule is that
        # the receipt is the list of what ran, so a command added to the job
        # without a line in the receipt, or a line for a command the job does
        # not have, is a difference. The two steps `ALLOWED_REQUIRED_STEP_IF`
        # names are the one intentional omission from a pull-request receipt:
        # each is guarded by its own condition and cannot run there.
        for receipt_step, declared in required_receipts:
            receipt_if = normalized_expression(receipt_step.get("if"))
            receipt_event = None
            if receipt_if == "github.event_name=='pull_request'":
                receipt_event = "pull_request"
            elif receipt_if == "github.event_name=='push'":
                receipt_event = "push"
            for step_id, command_step in run_steps.items():
                if ("if" in command_step and allowed_step_if(name, command_step)
                        and receipt_event == "pull_request"):
                    if step_id in declared:
                        complain("%s job '%s' pull-request receipt lists command "
                                 "step '%s', which cannot run there" % (f, name, step_id))
                    continue
                if step_id not in declared:
                    complain("%s job '%s' required receipt omits command step "
                             "'%s'" % (f, name, step_id))
            unknown = sorted(set(declared) - set(run_steps))
            for step_id in unknown:
                complain("%s job '%s' required receipt names unknown command "
                         "step '%s'" % (f, name, step_id))

# Composite actions execute with their caller's token and runner. They have no
# workflow trigger or permissions block, but their `uses:` and `run:` steps
# carry the same pinning and download-execution risks as workflow steps. The
# actions a workflow reaches with `uses: ./path` are read as well as the ones
# under a `.github/actions` directory, and the ones they reach in turn.
def local_action_file(uses):
    path = uses_local_path(uses)
    if path is None:
        return None
    for leaf in ("action.yml", "action.yaml"):
        candidate = leaf if path == "." else path + "/" + leaf
        if os.path.isfile(candidate):
            return candidate
    return None

known = set(action_files)
for reference in local_actions:
    found = local_action_file(reference)
    if found is not None and found not in known:
        known.add(found)
        action_files.append(found)

index = 0
while index < len(action_files):
    f = action_files[index]
    index += 1
    try:
        doc = load_yaml(f)
    except yaml.YAMLError as e:
        complain("%s does not parse as YAML" % f)
        print("  %s" % str(e).replace("\n", "\n  "), file=sys.stderr)
        continue
    if not isinstance(doc, dict):
        complain("%s is not a mapping" % f)
        continue
    runs = doc.get("runs")
    if not isinstance(runs, dict) or runs.get("using") != "composite":
        complain("%s is not a composite action" % f)
        continue
    steps = runs.get("steps")
    if not isinstance(steps, list) or not steps:
        complain("%s defines no composite-action steps" % f)
        continue
    for step in steps:
        if not isinstance(step, dict):
            continue
        if "if" in step and is_disabled_condition(step.get("if")):
            complain("%s composite action has a step unconditionally disabled "
                     "by `if: false`" % f)
        if "continue-on-error" in step and is_truthy_continue_on_error(step.get("continue-on-error")):
            complain("%s composite action has a step-level `continue-on-error` "
                     "that can mask a command" % f)
        if "run" in step:
            run_value = step.get("run")
            if not isinstance(run_value, str):
                complain("%s composite action has a non-string `run` step" % f)
            elif is_noop_run(run_value):
                complain("%s composite action has a hollow `run` step" % f)
        uses = step.get("uses")
        if isinstance(uses, str):
            check_pin(f, "composite action", "uses", uses)
            if uses_local_path(uses) == RECEIPT_ACTION:
                complain("%s composite action calls the receipt action -- "
                         "only a workflow job step may, so that the job that "
                         "makes the call is the job the checks above read" % f)
            nested = local_action_file(uses)
            if nested is not None and nested not in known:
                known.add(nested)
                action_files.append(nested)
            if uses.startswith("actions/checkout@"):
                with_ = step.get("with") or {}
                if not isinstance(with_, dict) \
                        or with_.get("persist-credentials") is not False:
                    complain("%s composite action checks out without "
                             "`persist-credentials: false`" % f)
        run = step.get("run")
        if isinstance(run, str):
            check_run(f, "composite action", run)

check_required_steps()

print("check-workflows: %d workflow file(s) and %d composite action file(s) parse" % (len(files), len(action_files)))
sys.exit(bad)
PY
