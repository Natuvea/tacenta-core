#!/usr/bin/env python3
"""Show, one edit at a time, that a negative control notices when its gate is broken.

    python3 tooling/mutate-gates.py                run every edit in tooling/gate-mutations.json
    python3 tooling/mutate-gates.py -v             also show the failing output of each edit
    python3 tooling/mutate-gates.py --only ID...   run the named edits (and the baselines they need)
    python3 tooling/mutate-gates.py --list         print the edits and what each is expected to break
    python3 tooling/mutate-gates.py --json FILE    also write the results as JSON
    python3 tooling/mutate-gates.py --guards FILE...   remove each failure guard of a gate in turn (see below)
    python3 tooling/mutate-gates.py --guards FILE... --verdict --link PATH...

A negative control is only worth what it has been seen to catch. `GATE-MUTATION-RECORD.md` records a run of
single edits to the gates; the harness that applied the 2026-09-30 edits was not kept. This is a harness, so
the record can be repeated and extended.

Method. For each runner named in the file, the harness first checks out the commit under test (`HEAD`) into a
disposable `git worktree` and requires the runner to pass there (the baseline); a red baseline stops the run,
because it would make every edit look caught. Then, for each edit, in a fresh worktree:

  1. the file named by `file` has the string `old` replaced by `new`. `old` must occur exactly `count` times
     (default once), so an edit cannot silently miss or hit the wrong place;
  2. the edit is committed in the worktree (a control that builds its own worktree from `HEAD`, as
     `check-port-negatives.sh` does, then sees the edit);
  3. the runner is run there, with the mutated gate.

What the runner's failure means is not the same in every case, and the harness says which. An edit is

  accepted      a case saw the gate accept an input it must refuse (`got exit 0`, `was accepted`)
  behaviour     a case saw another wrong verdict: an honest input refused, a count or a call wrong, an
                assertion failed
  message only  the gate still refuses every input the cases give it and only the words changed: every
                failing line is a refusal whose diagnostic no longer matches. The runner is run to its end
                (with its stop-on-failure switched off) to see whether any other case fails for more than
                words, so a message-only result is the result for the whole runner
  survived      the runner stayed green

`accepted` and `behaviour` are caught. `message only` and `survived` fail the run unless the edit carries an
`equivalent` reason (its verdict cannot change: a later check refuses the same inputs) or an `uncovered`
reason (a known gap, named). A listed edit that a case sees as accepted or behaviour is stale and fails the
run. The edit must also make the runner print `expect`, the name of a case or a diagnostic, or it is reported
as WRONG-REASON: the runner failed for something else, so it did not show it holds this edit.

The harness reads the commit, not the working tree: commit the control, then run it. A mutation may name
`link`, paths whose build output is symlinked into the worktree from this checkout (a `.lake` directory), for
a control that needs a built Lean workspace.

Guard removal. `--guards FILE...` does not read `tooling/gate-mutations.json`. For each gate file it finds
every guard (an `if` or `elif` whose next line fails: `fail(`, `return 1`, `raise`, `sys.exit(1)`, `exit 1`,
an `ERROR` or a message to stderr), makes one mutant per guard whose condition is `False` (`false` in a shell
script), and runs the controls the inventory (`tooling/gate-inventory.json`) names for the gate, one after
another, until one fails. By exit status a guard is a survivor when every control stays green. With
`--verdict` the same classification as above is applied: a guard whose removal changes only a diagnostic is a
survivor too, and the result gives both columns. `--link PATH...` links build output into the worktrees, for
the controls that need a built Lean workspace. Mutants whose guard line is not unique in the file are skipped
and counted.

This is a local tool. Nothing in CI runs it; it takes a long time and some edits build.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                      check=True).stdout.strip()
FILE = os.path.join(ROOT, "tooling", "gate-mutations.json")
GIT = ["git", "-c", "user.name=mutate-gates", "-c", "user.email=mutate-gates@example.invalid"]

# A failing line that is a refusal with the wrong words, in the forms the case runners print. Everything else
# that a runner reports as wrong is a verdict: the gate accepted what it must refuse, or refused what it must
# accept, or a count or a call was wrong.
MESSAGE_ONLY = re.compile(
    r"refused, but|missing diagnostic|reported \d+ problem|the refusal does not name|no report at"
    r"|expected (?:a )?refusal .*got exit [1-9]|expected exit (?:nonzero|1) .*got exit [1-9]")
ACCEPTED = re.compile(r"got exit 0|was accepted|accepted|did not refuse|not refused|expected refusal$"
                      r"|expected validation refusal|did not fail|accepted it")
# The lines on which the runners report a case that went wrong. Anchored at the start of the line: the gate's own
# diagnostics, which a runner prints beneath its report, say "expected" and "refused" too and are not reports.
FAILURE_LINE = re.compile(r"^(?:WRONG|generation negative |audit-reach negative |pin negative "
                          r"|kernel-replay negative: leanchecker (?:did not|refused)|constant-time asm control[ :]"
                          r"|boundary-surface case: |::error::lifecycle coverage gate)")


def run(cmd, cwd, timeout, env=None):
    started = time.time()
    try:
        proc = subprocess.run(cmd, shell=True, cwd=cwd, capture_output=True, text=True,
                              timeout=timeout, env=env)
        return proc.returncode, proc.stdout + proc.stderr, time.time() - started
    except subprocess.TimeoutExpired:
        return 124, "(timed out)", time.time() - started


class Worktree:
    """A disposable worktree of HEAD, removed on exit."""

    def __init__(self, links=()):
        self.path = tempfile.mkdtemp(prefix="mutate-gates-")
        subprocess.run(["git", "-C", ROOT, "worktree", "add", "-q", "--detach", self.path, "HEAD"],
                       check=True, capture_output=True)
        for link in links:
            src = os.path.join(ROOT, link)
            dst = os.path.join(self.path, link)
            if not os.path.exists(src):
                raise SystemExit(f"mutate-gates: cannot link {link}: not built in this checkout")
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            os.symlink(src, dst)

    def __enter__(self):
        return self.path

    def __exit__(self, *exc):
        subprocess.run(["git", "-C", ROOT, "worktree", "remove", "--force", self.path],
                       capture_output=True)
        shutil.rmtree(self.path, ignore_errors=True)


def apply_edit(wt, mutation):
    path = os.path.join(wt, mutation["file"])
    with open(path, encoding="utf-8") as handle:
        text = handle.read()
    want = mutation.get("count", 1)
    have = text.count(mutation["old"])
    if have != want:
        raise SystemExit(f"mutate-gates: {mutation['id']}: {mutation['file']} holds the edit's `old` "
                         f"text {have} time(s), expected {want}")
    with open(path, "w", encoding="utf-8") as handle:
        handle.write(text.replace(mutation["old"], mutation["new"]))
    subprocess.run(GIT + ["-C", wt, "commit", "-q", "-a", "--no-verify", "-m", "mutation " + mutation["id"]],
                   check=True, capture_output=True)


def failure_lines(output):
    return [line for line in output.splitlines() if FAILURE_LINE.search(line)]


def keep_going(wt, runner, timeout):
    """Run a `bash SCRIPT` runner to its end with its stop-on-failure switched off, so that every case prints
    its own failure line. Returns the output, or None for a runner this cannot be done for."""
    parts = runner.split()
    if len(parts) < 2 or parts[0] != "bash" or not os.path.isfile(os.path.join(wt, parts[1])):
        return None
    script = os.path.join(wt, parts[1])
    with open(script, encoding="utf-8") as handle:
        text = handle.read()
    text = text.replace("set -euo pipefail", "set -uo pipefail", 1)
    text = re.sub(r"(?m)^(\s*)set -e\s*$", r"\1:", text)
    text = re.sub(r"\bexit 1\b", ":", text)
    copy = script[:-3] + "-keep-going.sh"
    with open(copy, "w", encoding="utf-8") as handle:
        handle.write(text)
    _, output, _ = run(" ".join(["bash", copy] + parts[2:]), wt, timeout)
    return output


def classify(wt, runner, output, timeout):
    """(kind, line): accepted, behaviour or message, for a runner that failed with `output`."""
    lines = failure_lines(output)
    if not lines:
        return "behaviour", "an assertion or a step that must pass failed"
    verdicts = [line for line in lines if not MESSAGE_ONLY.search(line)]
    if not verdicts:
        # Only words so far: run to the end to see whether any later case fails for more.
        everything = keep_going(wt, runner, timeout)
        if everything is not None:
            verdicts = [line for line in failure_lines(everything) if not MESSAGE_ONLY.search(line)]
    if not verdicts:
        return "message", lines[0]
    return ("accepted" if any(ACCEPTED.search(line) for line in verdicts) else "behaviour"), verdicts[0]


GUARD_PY = re.compile(r"^(\s*)(if|elif) (.+):\s*$")
GUARD_SH = re.compile(r"^(\s*)(if|elif) (.+); then\s*$")
FAILS = re.compile(r"fail\(|return 1|raise |sys\.exit\(1\)|exit 1|ERROR|file=sys\.stderr|>&2|SystemExit")


def guard_mutants(path):
    """([(line number, old text, new text)], skipped) for each guard of the file whose old text is unique."""
    with open(os.path.join(ROOT, path), encoding="utf-8") as handle:
        text = handle.read()
    lines = text.split("\n")
    shell = path.endswith(".sh")
    pattern = GUARD_SH if shell else GUARD_PY
    out, skipped = [], 0
    for i, line in enumerate(lines[:-1]):
        match = pattern.match(line)
        if not match or not FAILS.search(lines[i + 1]):
            continue
        indent, keyword = match.group(1), match.group(2)
        old = line + "\n" + lines[i + 1]
        if text.count(old) != 1:
            skipped += 1
            continue
        new = f"{indent}{keyword} {'false' if shell else 'False'}{'; then' if shell else ':'}\n" + lines[i + 1]
        out.append((i + 1, old, new))
    return out, skipped


def run_guards(files, timeout, verdict, links):
    with open(os.path.join(ROOT, "tooling", "gate-inventory.json"), encoding="utf-8") as handle:
        rows = json.load(handle)["rows"]
    status = 0
    for path in files:
        runners = []
        for row in rows:
            if row["gate"] == path:
                for control in row.get("controls", []):
                    name = control if isinstance(control, str) else control["path"]
                    if name.endswith(".sh") and ("/tests/run-" in name or name.endswith("-negatives.sh")):
                        runners.append("bash " + name)
        if not runners:
            print(f"{path}: no case runner in tooling/gate-inventory.json; skipped")
            status = 1
            continue
        mutants, skipped = guard_mutants(path)
        with Worktree(links) as wt:
            rc, out, took = run(" && ".join(runners), wt, timeout)
        if rc != 0:
            print(f"{path}: the baseline fails; skipped\n"
                  + "\n".join("    " + l for l in out.strip().splitlines()[-6:]))
            status = 1
            continue
        by_verdict, message_only, survivors = [], [], []
        for line, old, new in mutants:
            mutation = {"id": f"{path}:{line}", "file": path, "old": old, "new": new}
            kind = None
            for one in runners:
                with Worktree(links) as wt:
                    apply_edit(wt, mutation)
                    rc, out, took = run(one, wt, timeout)
                    if rc != 0:
                        kind = classify(wt, one, out, timeout)[0] if verdict else "refused"
                        break
            text = old.split("\n")[0].strip()
            if kind is None:
                survivors.append((line, text))
            elif kind == "message":
                message_only.append((line, text))
            else:
                by_verdict.append(line)
        names = " and ".join(runners)
        if verdict:
            print(f"{path}: {len(mutants)} guard(s) removed one at a time through `{names}`: "
                  f"{len(by_verdict)} changed a verdict, {len(message_only)} changed only a diagnostic, "
                  f"{len(survivors)} survived, {skipped} skipped as not unique")
        else:
            print(f"{path}: {len(mutants)} guard(s) removed one at a time through `{names}`, "
                  f"{len(mutants) - len(survivors)} refused, {len(survivors)} survived, "
                  f"{skipped} skipped as not unique")
        for line, text in message_only:
            print(f"    MESSAGE ONLY line {line}: {text}")
        for line, text in survivors:
            print(f"    SURVIVED line {line}: {text}")
        if survivors or message_only:
            status = 1
    return status


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--only", nargs="+", metavar="ID")
    parser.add_argument("--guards", nargs="+", metavar="FILE")
    parser.add_argument("--verdict", action="store_true",
                        help="with --guards: a guard whose removal changes only a diagnostic is a survivor too")
    parser.add_argument("--link", nargs="+", metavar="PATH", default=[],
                        help="with --guards: build output to symlink into each worktree")
    parser.add_argument("--json", metavar="FILE", help="also write the results as JSON")
    parser.add_argument("-v", "--verbose", action="store_true",
                        help="print the end of the runner's output for each caught edit too")
    parser.add_argument("--timeout", type=int, default=900, help="seconds per runner (default 900)")
    args = parser.parse_args()

    if args.guards:
        return run_guards(args.guards, args.timeout, args.verdict, args.link)

    with open(FILE, encoding="utf-8") as handle:
        spec = json.load(handle)
    mutations = spec["mutations"]
    ids = [m["id"] for m in mutations]
    if len(set(ids)) != len(ids):
        raise SystemExit("mutate-gates: duplicate mutation id")
    if args.only:
        unknown = [i for i in args.only if i not in ids]
        if unknown:
            raise SystemExit(f"mutate-gates: unknown id(s): {', '.join(unknown)}")
        mutations = [m for m in mutations if m["id"] in args.only]

    if args.list:
        for m in mutations:
            note = (f"\n{'':12} equivalent: {m['equivalent']}" if m.get("equivalent") else
                    f"\n{'':12} uncovered: {m['uncovered']}" if m.get("uncovered") else "")
            print(f"{m['id']:12} {m['file']}\n{'':12} {m['what']}\n{'':12} runner: {m['runner']}\n"
                  f"{'':12} expects: {m['expect']!r}{note}")
        return 0

    status = 0
    baselines = {}
    for m in mutations:
        key = (m["runner"], tuple(m.get("link", ())))
        if key in baselines:
            continue
        with Worktree(m.get("link", ())) as wt:
            rc, out, took = run(m["runner"], wt, args.timeout)
        baselines[key] = rc
        print(f"baseline  {'pass' if rc == 0 else 'baseline FAIL'}  {took:6.1f}s  {m['runner']}")
        if rc != 0:
            status = 1
            print("\n".join("    " + line for line in out.strip().splitlines()[-12:]))
    if status:
        print("\nmutate-gates: a baseline is red, so no edit would mean anything; stopping")
        return 1

    results = []
    for m in mutations:
        key = (m["runner"], tuple(m.get("link", ())))
        reason = m.get("equivalent") or m.get("uncovered")
        with Worktree(m.get("link", ())) as wt:
            apply_edit(wt, m)
            rc, out, took = run(m["runner"], wt, args.timeout)
            if rc == 0:
                kind, line = "survived", ""
            elif m["expect"] not in out:
                kind, line = "wrong-reason", ""
            else:
                kind, line = classify(wt, m["runner"], out, args.timeout)
        if kind in ("accepted", "behaviour"):
            verdict = "stale" if reason else "caught"
        elif kind == "wrong-reason":
            verdict = "wrong-reason"
        else:
            verdict = "listed" if reason else "NOT CAUGHT"
        label = {"accepted": "accepted", "behaviour": "behaviour", "message": "message only",
                 "survived": "survived", "wrong-reason": "WRONG-REASON"}[kind]
        mark = {"caught": "", "listed": "  [listed: " + ("equivalent" if m.get("equivalent") else "uncovered") + "]",
                "stale": "  [STALE: listed, but a case sees it]", "NOT CAUGHT": "  [NOT CAUGHT]",
                "wrong-reason": ""}[verdict]
        results.append({"id": m["id"], "kind": kind, "verdict": verdict, "seconds": round(took, 1),
                        "line": line, "reason": reason or ""})
        print(f"{label:13} {m['id']:14} {took:6.1f}s  {m['what']}{mark}")
        if verdict in ("NOT CAUGHT", "stale", "wrong-reason") or args.verbose:
            if line:
                print("    " + line.strip())
            for text in out.strip().splitlines()[-8:]:
                print("    " + text)
        if verdict in ("NOT CAUGHT", "stale", "wrong-reason"):
            status = 1

    counts = {k: sum(1 for r in results if r["kind"] == k)
              for k in ("accepted", "behaviour", "message", "survived", "wrong-reason")}
    print(f"\nmutate-gates: {len(results)} edits: {counts['accepted']} seen as accepted, {counts['behaviour']} as "
          f"another wrong verdict, {counts['message']} as a message only, {counts['survived']} survived, "
          f"{counts['wrong-reason']} red for another reason; "
          f"{sum(1 for r in results if r['verdict'] == 'listed')} of the last three listed as equivalent or "
          f"uncovered, {sum(1 for r in results if r['verdict'] in ('NOT CAUGHT', 'stale', 'wrong-reason'))} "
          f"not accounted for")
    if args.json:
        with open(args.json, "w", encoding="utf-8") as handle:
            json.dump(results, handle, indent=1)
    return 1 if status else 0


if __name__ == "__main__":
    sys.exit(main())
