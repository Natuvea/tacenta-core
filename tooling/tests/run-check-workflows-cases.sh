#!/usr/bin/env bash
# Hold `tooling/check-workflows.sh` to its cases.
#
#   bash tooling/tests/run-check-workflows-cases.sh
#
# Each file under `check-workflows-cases/` is one small workflow. A `pass-*`
# file must be accepted; a `fail-*` file must be refused, and refused for the
# stated reason: its first line is `# expect: <text>`, and that text must
# appear in the checker's output, so a case that fails for some other reason
# (a typo that stops it parsing, say) is caught rather than counted. Each
# case is copied into a fresh temporary git repository as its only workflow,
# because the checker walks the tree it is run in from `git rev-parse`.
#
# Two optional lines after `# expect:` shape the repository a case runs in.
# `# manifest: <name>` makes the case the repository's `ci.yml` and copies
# `check-workflows-cases/manifests/<name>` to `tooling/required-steps.json`
# (`none` copies nothing), which is how the comparison with the expected form of
# the required workflow is held. A directory `<case>.tree/` beside a case is
# copied over the repository root, for the files a case reaches by `uses: ./`;
# a directory in it named `dot-github` becomes `.github` there.
#
# The last group are the real thing: the repository's own `ci.yml`, receipt
# action and `tooling/required-steps.json`, copied into a temporary repository
# and changed one way at a time by name (a job, a step id). Each must be
# refused. They fail loudly when the name they change is gone, so they cannot
# fall silent when the workflow is edited.
#
# The checker itself is not changed to run these: it checks the tree it is
# in, and this script is what `tooling/ci.sh` and the workflow's `checks` job
# run right after it, so a regex loosened by mistake fails the gate the same
# push. The cases live here and not under any `.github/workflows` path so the
# real checker never picks them up as workflows of this repository.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
checker="$root/tooling/check-workflows.sh"
cases="$here/check-workflows-cases"

# The same rule as the checker: without PyYAML the checker skips locally and
# every case would pass, which is not a result. Skip here for the same
# reason, and fail in CI for the same reason the checker does.
if ! command -v python3 >/dev/null 2>&1 || ! python3 -c 'import yaml' >/dev/null 2>&1; then
  echo "check-workflows-cases: python3 with pyyaml not found, skipping (pip install pyyaml)" >&2
  if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    echo "check-workflows-cases: this is CI -- a check that cannot run is a failure, not a skip" >&2
    exit 1
  fi
  exit 0
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

wrong=0
total=0
for case in "$cases"/pass-*.yml "$cases"/fail-*.yml "$cases"/action-pass-*.yml "$cases"/action-fail-*.yml; do
  [ -e "$case" ] || continue
  total=$((total + 1))
  name="$(basename "$case" .yml)"
  repo="$work/$name"
  mkdir -p "$repo/.github/workflows"
  git -C "$repo" init -q
  manifest="$(sed -n '1,2s/^# manifest: //p' "$case")"
  if [ -d "${case%.yml}.tree" ]; then
    cp -R "${case%.yml}.tree/." "$repo/"
    # A `.github` directory under `check-workflows-cases/` would be read as a
    # workflow directory of this repository, so a case stores it as
    # `dot-github`, deepest first.
    while IFS= read -r renamed; do
      mkdir -p "$(dirname "$renamed")/.github"
      cp -R "$renamed/." "$(dirname "$renamed")/.github/"
      rm -rf "$renamed"
    done < <(find "$repo" -type d -name dot-github | sort -r)
  fi
  case "$name" in
    action-*)
      mkdir -p "$repo/.github/actions/probe"
      cp "$case" "$repo/.github/actions/probe/action.yml"
      # The checker requires a workflow directory to exist, so the fixture
      # action gets one minimal valid caller.
      cat > "$repo/.github/workflows/t.yml" <<'EOF'
name: t
on: push
permissions:
  contents: read
jobs:
  j:
    runs-on: ubuntu-latest
    steps:
      - uses: ./.github/actions/probe
EOF
      ;;
    *)
      if [ -n "$manifest" ]; then
        cp "$case" "$repo/.github/workflows/ci.yml"
        if [ "$manifest" != none ]; then
          mkdir -p "$repo/tooling"
          cp "$cases/manifests/$manifest" "$repo/tooling/required-steps.json"
        fi
      else
        cp "$case" "$repo/.github/workflows/t.yml"
      fi
      ;;
  esac
  set +e
  # Not `GITHUB_ACTIONS`: the checker's own skip-or-fail rule is not under
  # test, and a case must see the same checker a developer's machine does.
  out="$(cd "$repo" && env -u GITHUB_ACTIONS bash "$checker" 2>&1)"
  rc=$?
  set -e
  case "$name" in
    pass-*|action-pass-*)
      if [ "$rc" -ne 0 ]; then
        echo "WRONG  $name: expected accepted, was refused:" >&2
        printf '  %s\n' "$out" >&2
        wrong=$((wrong + 1))
      fi
      ;;
    fail-*|action-fail-*)
      expect="$(sed -n '1s/^# expect: //p' "$case")"
      if [ -z "$expect" ]; then
        echo "WRONG  $name: a fail case's first line must be '# expect: <text>'" >&2
        wrong=$((wrong + 1))
      elif [ "$rc" -eq 0 ]; then
        echo "WRONG  $name: expected refused ($expect), was accepted" >&2
        wrong=$((wrong + 1))
      elif ! printf '%s' "$out" | grep -qF -- "$expect"; then
        echo "WRONG  $name: refused, but not for '$expect':" >&2
        printf '  %s\n' "$out" >&2
        wrong=$((wrong + 1))
      fi
      ;;
  esac
done

if [ "$total" -eq 0 ]; then
  echo "check-workflows-cases: no cases found" >&2
  exit 1
fi
if [ "$wrong" -ne 0 ]; then
  echo "check-workflows-cases: $wrong of $total case(s) gave the wrong result" >&2
  exit 1
fi

empty_repo="$work/empty-tree"
mkdir -p "$empty_repo"
git -C "$empty_repo" init -q
set +e
empty_out="$(cd "$empty_repo" && env -u GITHUB_ACTIONS bash "$checker" 2>&1)"
empty_rc=$?
set -e
if [ "$empty_rc" -eq 0 ] || ! printf '%s' "$empty_out" | grep -qF -- 'no workflow files found'; then
  echo 'WRONG  empty-tree: missing workflows did not fail closed' >&2
  printf '%s\n' "$empty_out" >&2
  exit 1
fi

# The repository's own workflow, changed one way at a time. Each change is
# made to the parsed workflow by job and step id, so it says what it changes
# and stops if that is gone. The unchanged copy, after the same round trip
# through the parser, must be accepted: otherwise a refusal below could be the
# round trip and not the change.
# The program is written to a file and run, rather than read from a heredoc
# inside $( ): a shell that scans a command substitution as shell text (bash
# 3.2 does) would pair the quotes in it.
cat > "$work/real-tree-cases.py" <<'PY'
import copy, os, pathlib, shutil, subprocess, sys
import yaml

root, work, checker = (pathlib.Path(a) for a in sys.argv[1:4])


def step(workflow, job, ident):
    for candidate in workflow["jobs"][job]["steps"]:
        if candidate.get("id") == ident:
            return candidate
    raise SystemExit("real-tree case: no step %s in job %s" % (ident, job))


def step_index(workflow, job, ident):
    for index, candidate in enumerate(workflow["jobs"][job]["steps"]):
        if candidate.get("id") == ident:
            return index
    raise SystemExit("real-tree case: no step %s in job %s" % (ident, job))


def receipt(workflow, job, position=0):
    found = [s for s in workflow["jobs"][job]["steps"] if str(s.get("uses", "")).endswith("assurance-receipt")]
    return found[position]


def drop_outcome(text, ident):
    parts = [p for p in text.split(",") if not p.startswith(ident + "=")]
    if len(parts) == len(text.split(",")):
        raise SystemExit("real-tree case: no outcome %s" % ident)
    return ",".join(parts)


def m01(w): step(w, "rust", "rust_test")["run"] += " || true"
def m02(w): step(w, "rust", "rust_fmt")["run"] = "echo " + step(w, "rust", "rust_fmt")["run"]
def m03(w): step(w, "vectors", "vectors_test")["run"] = "exit 0\n" + step(w, "vectors", "vectors_test")["run"]
def m04(w): step(w, "rust", "rust_ct_asm")["shell"] = "true {0}"
def m05(w): step(w, "rust", "rust_clippy")["if"] = "github.event_name == 'never'"
def m06(w): step(w, "rust", "rust_test")["continue-on-error"] = "${{ github.run_id > 0 }}"
def m07(w): w["jobs"]["audit"]["defaults"] = {"run": {"shell": "true {0}"}}
def m08(w): w["jobs"]["sign-off"]["continue-on-error"] = "${{ github.run_id > 0 }}"
def m09(w):
    for s in w["jobs"]["assurance-receipts"]["steps"]:
        if str(s.get("run", "")).startswith("python3 tooling/collect-assurance-receipts.py"):
            s["run"] += " || true"; return
    raise SystemExit("real-tree case: no collector step")
def m10(w):
    for s in w["jobs"]["assurance-receipts"]["steps"]:
        if "--validate" in str(s.get("run", "")):
            s["if"] = "github.event_name == 'never'"; return
    raise SystemExit("real-tree case: no validate step")
def m11(w):
    del w["jobs"]["rust"]["steps"][step_index(w, "rust", "rust_clippy")]
    r = receipt(w, "rust")["with"]; r["required-outcomes"] = drop_outcome(r["required-outcomes"], "rust_clippy")
def m12(w): receipt(w, "rust")["with"]["classification"] = "${{ 'required' }}"
def m13(w):
    s = step(w, "translation", "translation_no_sorry")
    s["name"] = "Clone the Lake dependencies from local mirrors (self-hosted only)"
    s["if"] = "runner.environment == 'self-hosted'"
    r = receipt(w, "translation", 0)["with"]; r["required-outcomes"] = drop_outcome(r["required-outcomes"], "translation_no_sorry")
def m14(w): w["jobs"]["rust"]["steps"][0]["with"]["ref"] = "refs/heads/main"
def m15(w): w["env"]["EXTRA"] = "1"
def m16(w):
    w["jobs"]["vectors"]["steps"].insert(step_index(w, "vectors", "vectors_test"), {"id": "vectors_extra", "run": "true && make"})
def m17(w):
    steps = w["jobs"]["rust"]["steps"]
    a, b = step_index(w, "rust", "rust_fmt"), step_index(w, "rust", "rust_clippy")
    steps[a], steps[b] = steps[b], steps[a]
def m18(w): step(w, "rust", "rust_test").setdefault("env", {})["BASH_ENV"] = "./tooling/x"
def m19(w): step(w, "rust", "rust_fmt")["working-directory"] = "."
def m20(w): step(w, "sign-off", "signoff_check")["run"] += " || true"
def m21(w): del w[True]["pull_request"]
def m22(w): w["jobs"]["msrv"]["steps"][step_index(w, "msrv", "msrv_check")]["timeout-minutes"] = 1
def m23(w): w["jobs"]["checks"]["steps"][step_index(w, "checks", "checks_02")]["env"] = {"GITHUB_ACTIONS": "false"}
def m24(w): w["jobs"]["proofs"]["runs-on"] = "ubuntu-latest"; w["jobs"]["proofs"]["steps"][0]["with"]["persist-credentials"] = True

def a01(action): action["runs"]["steps"][0]["run"] = action["runs"]["steps"][0]["run"].replace("python3 -I", "python3")
def a02(action): action["runs"]["steps"][0]["env"]["RECEIPT_ID"] = "fixed"

# Changes that must be accepted: a step's `name:` is a label, and is not part
# of the expected form.
def l01(w): step(w, "rust", "rust_fmt")["name"] = "Check formatting"
def l02(w): w["jobs"]["rust"]["steps"][0]["name"] = "Check the sources out"
def l03(action): action["runs"]["steps"][0]["name"] = "Write the receipt"

accepted = [("workflow-label-01", l01, False), ("workflow-label-02", l02, False), ("action-label-01", l03, True)]

cases = [("workflow-form-%02d" % i, fn) for i, fn in enumerate(
    [m01, m02, m03, m04, m05, m06, m07, m08, m09, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24], 1)]
cases += [("action-form-%02d" % i, fn) for i, fn in enumerate([a01, a02], 1)]


def build(name, change, is_action):
    repo = work / ("real-" + name)
    repo.mkdir()
    subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
    shutil.copytree(root / ".github", repo / ".github")
    (repo / "tooling").mkdir()
    shutil.copy(root / "tooling/required-steps.json", repo / "tooling/required-steps.json")
    path = repo / (".github/actions/assurance-receipt/action.yml" if is_action else ".github/workflows/ci.yml")
    document = yaml.safe_load(path.read_text())
    if change is not None:
        change(document)
    path.write_text(yaml.safe_dump(document, sort_keys=False, width=100000))
    return repo


def check(repo):
    env = {k: v for k, v in os.environ.items() if k != "GITHUB_ACTIONS"}
    result = subprocess.run(["bash", str(checker)], cwd=repo, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return result.returncode, result.stdout


wrong = 0
for name, change, is_action in accepted:
    rc, out = check(build(name, change, is_action))
    if rc != 0:
        print("WRONG  real-tree %s: a relabelled step was refused:\n%s" % (name, out), file=sys.stderr)
        wrong += 1
rc, out = check(build("control", None, False))
if rc != 0:
    print("WRONG  real-tree control: the unchanged workflow was refused:\n" + out, file=sys.stderr)
    wrong += 1
for name, change in cases:
    repo = build(name, change, name.startswith("action"))
    rc, out = check(repo)
    if rc == 0:
        print("WRONG  real-tree %s: expected refused, was accepted" % name, file=sys.stderr)
        wrong += 1
    elif "differs from tooling/required-steps.json" not in out:
        print("WRONG  real-tree %s: refused, but not as a difference from the expected form:\n%s" % (name, out), file=sys.stderr)
        wrong += 1
if wrong:
    sys.exit(1)
print(len(cases) + len(accepted))
PY
real_total="$(python3 "$work/real-tree-cases.py" "$root" "$work" "$checker")" || {
  echo "check-workflows-cases: the changes to the repository's own workflow gave the wrong result" >&2
  exit 1
}

echo "check-workflows-cases: $total file cases, $real_total changes to the repository's own workflow and the empty-tree refusal gave the expected result"
