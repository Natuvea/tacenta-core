#!/usr/bin/env bash
# Refuse a pipeline that ends in a quiet grep in a tracked shell script.
#
#   bash tooling/check-shell-portability.sh                 # every tracked shell script and workflow
#   bash tooling/check-shell-portability.sh --files F...    # exactly these files (the case runner uses this)
#
# The shape refused is `producer | grep -q pattern` (also -qF, -Eq, --quiet, --silent, and egrep, fgrep,
# ugrep and rg in the same position), with any number of stages before it, wherever it appears: a command,
# an `if` or `while` condition, `! producer | grep -q`, inside `$( )`, backticks, `{ }` or `( )`, across a
# backslash continuation or a trailing pipe, and in the `run:` text of a workflow or action file.
#
# Why. `grep -q` exits at its first match. The producer is still writing, takes SIGPIPE, and under
# `set -o pipefail` the pipeline's status is the producer's 141, not grep's 0. Whether that happens depends
# on how much the producer writes and how fast grep gets scheduled, so the same script passes on one
# machine and fails on another, and passes again on a re-run. It is a race and not a defect in what the
# script checks. It showed up here on a Mac (a 16 KiB pipe, a different grep) in
# `run-check-traceability-cases.sh`, which pipes a whole run's output into `grep -qF`. A producer that
# writes less than a pipe buffer in one write is safe in practice, but a script cannot see how big its
# producer will become, so the rule is the pipe and not the size.
#
# What to write instead, each of which keeps the same verdict and has no pipe to break:
#
#     grep -qF -- "$needle" <<<"$out"       # a variable: a here-string
#     case $out in *"$needle"*) ... ;; esac  # a fixed string, no process at all
#     last="$(tail -n 1 <<<"$out")"; grep -qF -- "$x" <<<"$last"   # a producer that is a command: capture first
#     grep -q -- "$x" file                  # a file: name it
#     grep -q . < <(producer)               # a stream: a process substitution
#
# A pipeline into `grep -c`, `grep -v` or a grep that reads to the end is not refused, because grep does
# not stop reading early.
#
# What it does not see, said plainly. It is a textual tokenizer, not a shell parser. It reads the command
# word of the last stage after skipping `!`, `command`, `builtin`, `exec`, `env`, `sudo`, `nice`, `time`
# and `NAME=value`, so `xargs grep -q`, a variable that holds the command (`$GREP -q`), `eval` and a
# quiet grep built from a function are not seen. A heredoc body is read as shell, so a fixture that has to
# contain the refused text must live in a file this gate does not scan (the cases use `.case` files and
# `--files`). Other early-exit consumers (`head -n 1`, `sed q`, `grep -m1`) race the same way and are not
# refused here; the diagnostic `| head -20 >&2` forms are not worth the churn.
#
# The cases are the files under tooling/tests/check-shell-portability-cases/, run by
# tooling/tests/run-check-shell-portability-cases.sh.
set -euo pipefail

if ! command -v python3 >/dev/null 2>&1; then
  echo "check-shell-portability: python3 not found; a gate that cannot run is a failure, not a skip" >&2
  exit 1
fi
cd "$(git rev-parse --show-toplevel)"
exec python3 -I - "$@" <<'PY_SCANNER'
import os
import re
import subprocess
import sys

GREPS = {"grep", "egrep", "fgrep", "ugrep", "ug", "rg"}
# Words that may stand in front of the command word of a stage.
PREFIX = {"!", "command", "builtin", "exec", "env", "sudo", "nice", "time", "{", "}"}
# Single-letter grep options that take an argument: the letters after one are not options.
TAKES_ARG = set("efmABCdD")
ASSIGN = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*=")
SHEBANG = re.compile(r"^#!\s*\S*(?:/env\s+)?(?:ba|z|da|k)?sh\b")


def scan_text(text):
    """Return the stage lists of every pipeline in `text`, recursing into substitutions."""
    pipelines = []
    stages = [[]]
    word = []
    have_word = False
    i = 0
    n = len(text)
    dq = False

    def end_word():
        nonlocal word, have_word
        if have_word:
            stages[-1].append("".join(word))
        word = []
        have_word = False

    def end_pipeline():
        nonlocal stages
        end_word()
        if len(stages) > 1:
            pipelines.append(stages)
        stages = [[]]

    def matching(start):
        """Index just past the `)` closing a `(` whose body begins at `start`."""
        depth = 1
        j = start
        while j < n:
            c = text[j]
            if c == "\\":
                j += 2
                continue
            if c == "'":
                k = text.find("'", j + 1)
                j = n if k < 0 else k + 1
                continue
            if c == '"':
                k = j + 1
                while k < n and text[k] != '"':
                    k += 2 if text[k] == "\\" else 1
                j = k + 1
                continue
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0:
                    return j + 1
            j += 1
        return n

    while i < n:
        c = text[i]
        if c == "\\" and i + 1 < n:
            word.append(text[i + 1])
            have_word = True
            i += 2
            continue
        if not dq and c == "'":
            k = text.find("'", i + 1)
            k = n if k < 0 else k
            word.append(text[i + 1:k])
            have_word = True
            i = k + 1
            continue
        if c == '"':
            dq = not dq
            have_word = True
            i += 1
            continue
        if c == "$" and text.startswith("$(", i) and not text.startswith("$((", i):
            end = matching(i + 2)
            pipelines.extend(scan_text(text[i + 2:end - 1]))
            word.append("SUBST")
            have_word = True
            i = end
            continue
        if c == "`":
            k = i + 1
            while k < n and text[k] != "`":
                k += 2 if text[k] == "\\" else 1
            pipelines.extend(scan_text(text[i + 1:k]))
            word.append("SUBST")
            have_word = True
            i = k + 1
            continue
        if dq:
            word.append(c)
            i += 1
            continue
        if c in "<>" and text.startswith("(", i + 1):
            end = matching(i + 2)
            pipelines.extend(scan_text(text[i + 2:end - 1]))
            word.append("PROCSUBST")
            have_word = True
            i = end
            continue
        if c == "#" and not have_word:
            k = text.find("\n", i)
            i = n if k < 0 else k
            continue
        if c in " \t":
            end_word()
            i += 1
            continue
        if c in "\n;()":
            end_pipeline()
            i += 1
            continue
        if c == "&":
            prev = text[i - 1] if i else ""
            nxt = text[i + 1] if i + 1 < n else ""
            if prev in "<>" or nxt == ">":
                word.append(c)
                have_word = True
            else:
                end_pipeline()
                if nxt == "&":
                    i += 1
            i += 1
            continue
        if c == "|":
            if text.startswith("||", i):
                end_pipeline()
                i += 2
                continue
            end_word()
            stages.append([])
            i += 2 if text.startswith("|&", i) else 1
            continue
        word.append(c)
        have_word = True
        i += 1
    end_pipeline()
    return pipelines


def command_word_and_args(stage):
    j = 0
    while j < len(stage) and (stage[j] in PREFIX or ASSIGN.match(stage[j])):
        j += 1
    if j >= len(stage):
        return None, []
    return stage[j], stage[j + 1:]


def is_quiet_grep(stage):
    cmd, args = command_word_and_args(stage)
    if cmd is None or cmd.rsplit("/", 1)[-1] not in GREPS:
        return False
    k = 0
    while k < len(args):
        a = args[k]
        if a == "--":
            return False
        if a.startswith("--"):
            if a in ("--quiet", "--silent"):
                return True
        elif a.startswith("-") and len(a) > 1:
            for pos, ch in enumerate(a[1:], 1):
                if ch == "q":
                    return True
                if ch in TAKES_ARG:
                    if pos == len(a) - 1:
                        k += 1  # the next word is this option's argument
                    break
        else:
            return False  # the pattern: options are over
        k += 1
    return False


def logical_lines(raw):
    """Yield (first physical line number, text) after joining continuations and trailing pipes."""
    lines = raw.split("\n")
    out = []
    i = 0
    while i < len(lines):
        start = i + 1
        cur = lines[i]
        while i + 1 < len(lines):
            stripped = cur.rstrip()
            if stripped.endswith("\\"):
                cur = stripped[:-1] + " " + lines[i + 1]
            elif re.search(r"(?<![|])\|\s*(?:#.*)?$", stripped) and not stripped.lstrip().startswith("#"):
                cur = re.sub(r"\s*#[^|]*$", "", stripped) + " " + lines[i + 1]
            else:
                break
            i += 1
        out.append((start, cur))
        i += 1
    return out


def scan_file(path):
    with open(path, encoding="utf-8", errors="replace") as handle:
        raw = handle.read()
    hits = []
    for number, line in logical_lines(raw):
        if any(is_quiet_grep(stages[-1]) for stages in scan_text(line)):
            hits.append((number, line.strip()))
    return hits


def is_shell(path):
    if os.path.islink(path) or not os.path.isfile(path):
        return False  # a symlink, or a tracked file deleted from the working tree: nothing to read
    if path.endswith((".sh", ".bash", ".zsh")) or path.startswith(".githooks/"):
        return True
    if (".github/" in path or path.startswith(".github/")) and path.endswith((".yml", ".yaml")):
        return True
    try:
        with open(path, "rb") as fh:
            first = fh.readline(200).decode("utf-8", "replace")
    except OSError:
        return False
    return bool(SHEBANG.match(first))


def main(argv):
    if argv[:1] == ["--files"]:
        files = argv[1:]
        if not files:
            print("check-shell-portability: --files needs at least one file", file=sys.stderr)
            return 2
    elif argv:
        print("check-shell-portability: unknown argument %r" % argv[0], file=sys.stderr)
        return 2
    else:
        listed = subprocess.run(["git", "ls-files", "-z"], check=True, capture_output=True).stdout
        files = [p for p in listed.decode("utf-8", "replace").split("\0") if p and is_shell(p)]
        if not files:
            print("check-shell-portability: no tracked shell scripts found; this gate would check nothing", file=sys.stderr)
            return 1
    bad = 0
    for path in files:
        try:
            hits = scan_file(path)
        except OSError as err:
            print("check-shell-portability: cannot read %s: %s" % (path, err.strerror or err), file=sys.stderr)
            return 2
        for number, line in hits:
            bad += 1
            print("%s:%d: a pipeline ends in a quiet grep: %s" % (path, number, line[:160]), file=sys.stderr)
    if bad:
        print(
            "check-shell-portability: %d site(s). A producer piped into a quiet grep races under pipefail: grep "
            "exits at its first match and the producer takes SIGPIPE. Capture the producer's output and read it "
            "with a here-string, or use case, or name the file. See the header of this script." % bad,
            file=sys.stderr,
        )
        return 1
    print("check-shell-portability: %d file(s) scanned, no pipeline ends in a quiet grep" % len(files))
    return 0


sys.exit(main(sys.argv[1:]))
PY_SCANNER
