#!/usr/bin/env python3
"""Require public transaction tests to reject two state-commit mutations.

This is a runtime mutation control for the public responder and session-send
boundaries.  It runs the unmodified tests in a disposable copy of
``tacenta-core``, then mutates (1) the curve one-time removal so it is skipped
on the last-resort path and (2) the terminal failed-agreement guard so it
changes persisted session state before returning.  The tests must fail in both
copies.

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
MIXED_TEST = "a_failed_mixed_initial_message_commits_neither_store_effect"
FAILED_SEND_TEST = "the_message_that_fails_the_agreement_still_returns_its_plaintext"
MUTATION_BEFORE = "    if decoded.one_time_prekey_id != ABSENT_ID {\n"
MUTATION_AFTER = "    if decoded.one_time_prekey_id != ABSENT_ID && !last_resort {\n"
FAILED_SEND_BEFORE = "        if self.braid.failed() {\n            return Err(Error::AgreementFailed);\n        }\n"
FAILED_SEND_AFTER = "        if self.braid.failed() {\n            self.established_ephemeral = Some(Vec::new());\n            return Err(Error::AgreementFailed);\n        }\n"


def run(crate: Path, test_file: str, test: str) -> tuple[int, str]:
    result = subprocess.run(
        [
            "cargo",
            "test",
            "--locked",
            "--test",
            test_file,
            test,
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

        status, output = run(copy, "failed_decrypt_changes_nothing", MIXED_TEST)
        if status != 0:
            print(output, file=sys.stderr)
            raise SystemExit("runtime transaction control mixed-case baseline failed")
        print(f"PASS: unmodified {MIXED_TEST}")

        source = copy / "lifecycle/src/lifecycle.rs"
        text = source.read_text()
        if text.count(MUTATION_BEFORE) != 1:
            raise SystemExit("runtime transaction mutation target changed")
        source.write_text(text.replace(MUTATION_BEFORE, MUTATION_AFTER, 1))

        status, output = run(copy, "failed_decrypt_changes_nothing", MIXED_TEST)
        observed_failure = (
            status != 0
            and f"test {MIXED_TEST} ... FAILED" in output
            and "test result: FAILED" in output
        )
        if not observed_failure:
            print(output, file=sys.stderr)
            raise SystemExit(
                "runtime transaction mixed-case mutant did not produce the expected test failure"
            )
        print(f"PASS: mutant rejected by {MIXED_TEST}")

        status, output = run(copy, "full_session", FAILED_SEND_TEST)
        if status != 0:
            print(output, file=sys.stderr)
            raise SystemExit("runtime transaction failed-send baseline failed")
        print(f"PASS: unmodified {FAILED_SEND_TEST}")

        source = copy / "lifecycle/src/lifecycle.rs"
        text = source.read_text()
        encrypt_start = text.index("    pub fn encrypt<R: RngCore + CryptoRng>(")
        decrypt_start = text.index("    pub fn decrypt<R: RngCore + CryptoRng>(", encrypt_start)
        region = text[encrypt_start:decrypt_start]
        if region.count(FAILED_SEND_BEFORE) != 1:
            raise SystemExit("runtime transaction failed-send mutation target changed")
        source.write_text(
            text[:encrypt_start]
            + region.replace(FAILED_SEND_BEFORE, FAILED_SEND_AFTER, 1)
            + text[decrypt_start:]
        )

        status, output = run(copy, "full_session", FAILED_SEND_TEST)
        observed_failure = (
            status != 0
            and f"test {FAILED_SEND_TEST} ... FAILED" in output
            and "test result: FAILED" in output
        )
        if not observed_failure:
            print(output, file=sys.stderr)
            raise SystemExit(
                "runtime transaction failed-send mutant did not produce the expected test failure"
            )
        print(f"PASS: mutant rejected by {FAILED_SEND_TEST}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
