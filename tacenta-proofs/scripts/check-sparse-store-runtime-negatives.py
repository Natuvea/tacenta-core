#!/usr/bin/env python3
"""Require the sparse replacement boundary tests to reject two regressions.

The control runs the ratchet tests in disposable copies of the workspace.  One
mutant checks the old store length before purging keys that will be replaced;
the exact-2,000 acceptance test must reject that mutant.  The other mutant
commits the purge to the live state before checking the resulting bound; the
2,001 refusal test must reject that mutant.  A compiler or dependency failure
is not mutation evidence: the named test must pass unmodified and fail in the
mutated copy.

The repository is never modified.
"""

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
WORKSPACE = ROOT / "tacenta-core"
PACKAGE = "tacenta-ratchet"
REJECT_TEST = "tests::skipped_store_absolute_bound_rejects_2001_atomically"
ACCEPT_TEST = "tests::skipped_store_absolute_bound_accepts_exactly_2000_after_replacement"

PURGE = "                purge_chain_range(&mut skipped, dhr, state.nr, upto);\n"
PURGE_MUTANT = (
    "                purge_chain_range(&mut skipped, dhr, state.nr, upto);\n"
    "                state.skipped = skipped.clone();\n"
)
CHECK = "                if skipped.len() + count > MAX_SKIPPED_STORE {\n"
PRECHECK_MUTANT = (
    "                if state.skipped.len() + count > MAX_SKIPPED_STORE {\n"
    "                    return Err(RatchetError::SkippedStoreFull);\n"
    "                }\n"
    "                purge_chain_range(&mut skipped, dhr, state.nr, upto);\n"
)


def run(workspace: Path, test: str) -> tuple[int, str]:
    result = subprocess.run(
        ["cargo", "test", "--locked", "-p", PACKAGE, "--lib", test, "--", "--exact"],
        cwd=workspace,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=300,
    )
    return result.returncode, result.stdout


def require_pass(workspace: Path, test: str, label: str) -> None:
    status, output = run(workspace, test)
    if status or f"1 passed" not in output:
        print(output, file=sys.stderr)
        raise SystemExit(f"sparse runtime control {label} baseline failed")
    print(f"PASS: unmodified {test}")


def require_mutant_failure(workspace: Path, test: str, label: str) -> None:
    status, output = run(workspace, test)
    if status == 0 or f"test {test} ... FAILED" not in output or "test result: FAILED" not in output:
        print(output, file=sys.stderr)
        raise SystemExit(f"sparse runtime control {label} mutant did not fail the named test")
    print(f"PASS: mutant rejected by {test}")


def main() -> int:
    source_path = WORKSPACE / "ratchet/src/lib.rs"
    source = source_path.read_text()
    if source.count(PURGE) != 1:
        raise SystemExit("sparse runtime purge mutation target changed")
    if source.count(CHECK) != 1:
        raise SystemExit("sparse runtime store-bound mutation target changed")

    with tempfile.TemporaryDirectory(prefix="tacenta-sparse-store-runtime-") as raw:
        base = Path(raw) / "tacenta-core"
        shutil.copytree(WORKSPACE, base, ignore=shutil.ignore_patterns("target", ".git"))

        require_pass(base, REJECT_TEST, "atomic refusal")
        mutant_source = base / "ratchet/src/lib.rs"
        mutant_text = mutant_source.read_text().replace(PURGE, PURGE_MUTANT, 1)
        mutant_source.write_text(mutant_text)
        require_mutant_failure(base, REJECT_TEST, "commit-before-refusal")

        shutil.copytree(WORKSPACE, base / "fresh", ignore=shutil.ignore_patterns("target", ".git"))
        precheck = base / "fresh/ratchet/src/lib.rs"
        precheck_text = precheck.read_text()
        if precheck_text.count(PURGE) != 1:
            raise SystemExit("sparse runtime pre-check mutation target changed")
        require_pass(base / "fresh", ACCEPT_TEST, "resulting-bound acceptance")
        precheck.write_text(precheck_text.replace(PURGE, PRECHECK_MUTANT, 1))
        require_mutant_failure(base / "fresh", ACCEPT_TEST, "pre-replacement-bound")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
