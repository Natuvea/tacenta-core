#!/usr/bin/env python3
"""Require the sparse skip's store-full conjunct to rest on its proof and on the survivor bound.

`Tacenta.SpqrT3.skip_message_keys_refines` has two conjuncts. The second, that a
`SkippedStoreFull` result is the detailed model refusal `skippedStoreFull`, is
proved in the store-full branch of the proof, which reads the store a skip leaves
(`skipSurvivors`, the total bound) through the hypothesis `hC`. This is a
proof-dependency control, not a protocol or runtime mutation test. It compiles
disposable copies of `SpqrT3.lean`: the unmodified copy must elaborate, a copy
whose second conjunct names a different refusal must be refused, and a copy whose
store-full branch no longer uses `hC` must be refused.

Dependencies must already be built (`lake build Translation.SpqrT3`). No source,
olean or git worktree is changed by this script.
"""

from pathlib import Path
import argparse
import os
import re
import signal
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "translation/Translation/SpqrT3.lean"

STATEMENT = """          .error .skippedStoreFull) ⦄ := by
  unfold State.skip_message_keys
"""
BRANCH = """          simp [Model.SparseRatchet.skipMessageKeys, ← o_post, chainsOf,
            hcsr, hnotA, hnotB, hC]
"""
# The store-full branch opens here; both mutants must be refused at this line, as an
# unsolved goal, so a failure elsewhere (a syntax error, a consumer) does not count.
BRANCH_HEAD = """        · intro _
          unfold Model.SparseRatchet.skipMessageKeysDetailed
          simp [Model.SparseRatchet.skipMessageKeys, ← o_post, chainsOf,
"""

MUTANTS = (
    (
        "WrongDetailedRefusal.lean",
        "wrong-detailed-refusal.log",
        STATEMENT,
        STATEMENT.replace(".skippedStoreFull", ".tooManySkipped"),
        "a second conjunct that names `tooManySkipped`",
    ),
    (
        "NoSurvivorBound.lean",
        "no-survivor-bound.log",
        BRANCH,
        BRANCH.replace(", hC]", "]"),
        "the store-full branch without the survivor bound `hC`",
    ),
)


def run_lean(path: Path, log: Path, timeout: int) -> tuple[int, str]:
    with log.open("w") as output:
        try:
            process = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=ROOT / "translation",
                stdout=output,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
        except OSError as error:
            raise SystemExit(f"COMPILER LAUNCH FAILED (not a passing control): {error}")
        try:
            status = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            process.wait()
            raise SystemExit(f"TIMEOUT (not a passing control): {path.name}; see {log}")
    return status, log.read_text()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log-dir", type=Path)
    parser.add_argument("--timeout", type=int, default=900)
    args = parser.parse_args()

    logs = args.log_dir or Path(tempfile.mkdtemp(prefix="sparse-store-full-logs-"))
    logs.mkdir(parents=True, exist_ok=True)
    source = SOURCE.read_text()

    # A harmless rewrite of the branch (a renamed hypothesis, a reflowed `simp`) moves an anchor,
    # and the control then fails closed, naming the anchor to update with the proof edit.
    stale = [name for name, anchor in (("STATEMENT", STATEMENT), ("BRANCH", BRANCH),
                                       ("BRANCH_HEAD", BRANCH_HEAD))
             if source.count(anchor) != 1]
    if stale:
        raise SystemExit("Target changed: not exactly once in SpqrT3.lean: " + ", ".join(stale)
                         + "; update the anchor with the proof edit")

    branch_line = source[:source.find(BRANCH_HEAD)].count("\n") + 1
    expected = re.compile(rf":{branch_line}:\d+: error: unsolved goals")

    with tempfile.TemporaryDirectory(prefix="sparse-store-full-controls-") as tmp_name:
        tmp = Path(tmp_name)

        baseline = tmp / "Baseline.lean"
        baseline.write_text(source)
        status, output = run_lean(baseline, logs / "baseline.log", args.timeout)
        if status or "declaration uses `sorry`" in output:
            raise SystemExit(f"BASELINE FAILED; no mutation evidence: {logs / 'baseline.log'}")
        print("PASS: unmodified sparse T3 proof elaborates", flush=True)

        for filename, log_name, before, after, description in MUTANTS:
            mutant = tmp / filename
            mutant.write_text(source.replace(before, after, 1))
            log = logs / log_name
            status, output = run_lean(mutant, log, args.timeout)
            if status == 0:
                raise SystemExit(f"CONTROL FAILED: {description} still elaborates")
            if not expected.search(output):
                raise SystemExit(
                    "CONTROL INVALID: mutation failed for an unexpected reason; "
                    f"see {log}"
                )
            print(f"PASS: {description} is rejected", flush=True)


if __name__ == "__main__":
    main()
