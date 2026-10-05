#!/usr/bin/env python3
"""Require the mixed responder transaction test to reject an early curve-key commit.

This is a runtime mutation control for the public responder boundary.  It runs
the unmodified test in a disposable copy of ``tacenta-core``, then mutates the
curve one-time removal so it is skipped on the last-resort path.  The mixed
success test must fail in that copy: the replay record may still be appended,
but publishing again must not expose the same curve one-time identifier.

The repository is never modified.  A compiler or dependency failure is not
counted as mutation evidence; the mutant must compile far enough to run the
named test and that test must report failure.
"""

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
CRATE = ROOT / "tacenta-core"
TEST = "a_failed_mixed_initial_message_commits_neither_store_effect"
MUTATION_BEFORE = "    if decoded.one_time_prekey_id != ABSENT_ID {\n"
MUTATION_AFTER = "    if decoded.one_time_prekey_id != ABSENT_ID && !last_resort {\n"


def run(crate: Path) -> tuple[int, str]:
    result = subprocess.run(
        [
            "cargo",
            "test",
            "--locked",
            "--test",
            "failed_decrypt_changes_nothing",
            TEST,
            "--",
            "--exact",
        ],
        cwd=crate,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=300,
    )
    return result.returncode, result.stdout


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="tacenta-runtime-transaction-") as raw:
        copy = Path(raw) / "tacenta-core"
        shutil.copytree(
            CRATE,
            copy,
            ignore=shutil.ignore_patterns("target", ".git"),
        )

        status, output = run(copy)
        if status != 0:
            print(output, file=sys.stderr)
            raise SystemExit("runtime transaction control baseline failed")
        print(f"PASS: unmodified {TEST}")

        source = copy / "lifecycle/src/lifecycle.rs"
        text = source.read_text()
        if text.count(MUTATION_BEFORE) != 1:
            raise SystemExit("runtime transaction mutation target changed")
        source.write_text(text.replace(MUTATION_BEFORE, MUTATION_AFTER, 1))

        status, output = run(copy)
        observed_failure = (
            status != 0
            and f"test {TEST} ... FAILED" in output
            and "test result: FAILED" in output
        )
        if not observed_failure:
            print(output, file=sys.stderr)
            raise SystemExit(
                "runtime transaction mutant did not produce the expected test failure"
            )
        print(f"PASS: mutant rejected by {TEST}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
