#!/usr/bin/env python3
"""Require the Triple send proof to consume the exhaustive classical refusal contract.

This is a proof-dependency control, not a protocol/runtime mutation test.
Dependencies must already be built (`lake build Translation.UnitLifecycleInitialDispatch`).
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

BEFORE = """    (∀ e, r.1 = core.result.Result.Err e →
      (e = tacenta_ratchet.RatchetError.NoSendingChain ∨
        e = tacenta_ratchet.RatchetError.ChainExhausted) ∧
      Model.Ratchet.send (α s) = none)) ∧
"""

AFTER = """    (r.1 = core.result.Result.Err tacenta_ratchet.RatchetError.NoSendingChain →
      Model.Ratchet.send (α s) = none)) ∧
"""


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

    marker = "def RatchetAgreesFor"
    start = source.find(marker)
    target = source.find(BEFORE, start)
    if start < 0 or target < 0 or source.find(BEFORE, target + 1) >= 0:
        raise SystemExit("Target changed: exhaustive classical send-refusal contract is missing or duplicated")

    with tempfile.TemporaryDirectory(prefix="send-refusal-controls-") as tmp_name:
        tmp = Path(tmp_name)

        baseline = tmp / "Baseline.lean"
        baseline.write_text(source)
        status, output = run_lean(baseline, logs / "baseline.log", args.timeout)
        if status or "declaration uses `sorry`" in output:
            raise SystemExit(f"BASELINE FAILED; no mutation evidence: {logs / 'baseline.log'}")
        print("PASS: unmodified Triple send proof elaborates", flush=True)

        mutant = tmp / "NoChainExhaustedContract.lean"
        mutant.write_text(source[:target] + source[target:].replace(BEFORE, AFTER, 1))
        status, output = run_lean(mutant, logs / "no-chain-exhausted-contract.log", args.timeout)
        expected = re.search(
            r"Application type mismatch: The argument\s+e\s+has type\s+"
            r"tacenta_ratchet\.RatchetError.+?but is expected to have type\s+"
            r".+?Err tacenta_ratchet\.RatchetError\.NoSendingChain.+?"
            r"in the application\s+hrPost\.right e",
            output,
            re.S,
        )
        if status == 0:
            raise SystemExit("CONTROL FAILED: weakening the classical refusal contract still elaborates")
        if not expected:
            raise SystemExit(
                "CONTROL INVALID: mutation failed for an unexpected reason; "
                f"see {logs / 'no-chain-exhausted-contract.log'}"
            )
        print("PASS: omitting ChainExhausted from the leaf refusal contract is rejected")


if __name__ == "__main__":
    main()
