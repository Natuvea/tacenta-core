#!/usr/bin/env python3
"""Require Triple send to preserve both leafs' exact refusal reasons.

This is a proof-dependency control, not a protocol/runtime mutation test.
Dependencies must already be built (`lake build Translation.UnitTripleT3`).
No source, olean, or git worktree is changed by this script.
"""

from pathlib import Path
import argparse
import os
import re
import signal
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "translation/Translation/UnitTripleT3.lean"

BEFORE = """def sendRefusalOfReal : TripleError → Option Model.Triple.SendRefusal
  | .Classical reason => (Tacenta.UnitT3.sendRefusalOfReal reason).map .classical
  | .PostQuantum reason => (Tacenta.UnitSpqrT3.sendRefusalOfReal reason).map .postQuantum
"""

MUTANTS = (
    (
        "ClassicalWrongReason.lean",
        "classical-wrong-reason.log",
        """def sendRefusalOfReal : TripleError → Option Model.Triple.SendRefusal
  | .Classical _ => some (.classical .noSendingChain)
  | .PostQuantum reason => (Tacenta.UnitSpqrT3.sendRefusalOfReal reason).map .postQuantum
""",
        re.compile(
            r"unsolved goals.+?Model\.Ratchet\.SendRefusal\.noSendingChain = modelReason",
            re.S,
        ),
        "collapsing the classical refusal map",
    ),
    (
        "SparseWrongReason.lean",
        "sparse-wrong-reason.log",
        """def sendRefusalOfReal : TripleError → Option Model.Triple.SendRefusal
  | .Classical reason => (Tacenta.UnitT3.sendRefusalOfReal reason).map .classical
  | .PostQuantum _ => some (.postQuantum .noChain)
""",
        re.compile(
            r"unsolved goals.+?Model\.SparseRatchet\.SendRefusal\.noChain = modelReason",
            re.S,
        ),
        "collapsing the sparse refusal map",
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
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()

    logs = args.log_dir or Path(tempfile.mkdtemp(prefix="send-refusal-logs-"))
    logs.mkdir(parents=True, exist_ok=True)
    source = SOURCE.read_text()

    target = source.find(BEFORE)
    if target < 0 or source.find(BEFORE, target + 1) >= 0:
        raise SystemExit("Target changed: exact Triple send-refusal map is missing or duplicated")

    with tempfile.TemporaryDirectory(prefix="send-refusal-controls-") as tmp_name:
        tmp = Path(tmp_name)

        baseline = tmp / "Baseline.lean"
        baseline.write_text(source)
        status, output = run_lean(baseline, logs / "baseline.log", args.timeout)
        if status or "declaration uses `sorry`" in output:
            raise SystemExit(f"BASELINE FAILED; no mutation evidence: {logs / 'baseline.log'}")
        print("PASS: unmodified Triple send proof elaborates", flush=True)

        for filename, log_name, replacement, expected, description in MUTANTS:
            mutant = tmp / filename
            mutant.write_text(source.replace(BEFORE, replacement, 1))
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
