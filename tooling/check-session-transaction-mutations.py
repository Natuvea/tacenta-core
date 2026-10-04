#!/usr/bin/env python3
"""Run disposable mutations against the session transaction boundaries.

The production source is restored byte-for-byte after every case. A mutation
passes only when the focused Rust suite rejects it; a compiler failure or a
green suite is evidence failure, not a passing control.
"""

from pathlib import Path
import hashlib
import json
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tacenta-core/lifecycle/src/lifecycle.rs"


def run(command):
    return subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT)


def main():
    original = SOURCE.read_bytes()
    if run(["git", "diff", "--quiet", "--", str(SOURCE)]).returncode != 0:
        raise SystemExit("lifecycle source is already modified; refusing to mutate it")

    baseline = run([
        "cargo", "test", "--manifest-path", "tacenta-core/Cargo.toml",
        "--test", "failed_decrypt_changes_nothing",
    ])
    if baseline.returncode != 0:
        raise SystemExit("baseline transaction suite failed; no mutation evidence")

    source_text = original.decode()
    mutations = [
        (
            "mixed-initial-curve-removal-before-authentication",
            "if decoded.one_time_prekey_id != ABSENT_ID {",
            "if decoded.one_time_prekey_id != ABSENT_ID && !last_resort {",
            ["cargo", "test", "--manifest-path", "tacenta-core/Cargo.toml",
             "--test", "failed_decrypt_changes_nothing"],
            "a_failed_mixed_initial_message_commits_neither_store_effect",
        ),
        (
            "last-resort-replay-record-before-authentication",
            "    // This authenticates the initial ciphertext. Nothing above it may have\n"
            "    // changed the store, and nothing below it runs unless this succeeded.\n"
            "    let plaintext = session.decrypt_ratchet(&decoded.message, rng)?;",
            "    if let Some(fp) = fingerprint {\n"
            "        our_prekeys.last_resort_seen.push((decoded.kem_prekey_id, fp));\n"
            "    }\n"
            "    // This authenticates the initial ciphertext. Nothing above it may have\n"
            "    // changed the store, and nothing below it runs unless this succeeded.\n"
            "    let plaintext = session.decrypt_ratchet(&decoded.message, rng)?;",
            ["cargo", "test", "--manifest-path", "tacenta-core/Cargo.toml",
             "--test", "failed_decrypt_changes_nothing"],
            "a_failed_last_resort_message_does_not_record_a_replay_identity",
        ),
        (
            "agreement-commit-before-triple-send",
            "        let (candidate, sent) = send_candidate(&self.triple, sending_epoch, spqr_output);",
            "        self.braid = braid_next.clone();\n"
            "        let (candidate, sent) = send_candidate(&self.triple, sending_epoch, spqr_output);",
            ["cargo", "test", "--manifest-path", "tacenta-core/Cargo.toml",
             "-p", "tacenta-lifecycle"],
            "a_failed_triple_send_does_not_commit_the_agreement",
        ),
    ]

    results = {
        "source_sha256": hashlib.sha256(original).hexdigest(),
        "baseline_exit": baseline.returncode,
        "mutations": {},
    }
    with tempfile.TemporaryDirectory(prefix="session-transaction-mutations-") as logs:
        logs = Path(logs)
        try:
            for name, before, after, command, test_name in mutations:
                if before not in source_text:
                    raise SystemExit(f"mutation target changed: {name}")
                SOURCE.write_text(source_text.replace(before, after, 1))
                outcome = run(command)
                log = logs / f"{name}.log"
                log.write_text(outcome.stdout)
                if outcome.returncode == 0 or test_name not in outcome.stdout:
                    raise SystemExit(
                        f"mutation was not caught: {name}; exit={outcome.returncode}; log={log}"
                    )
                results["mutations"][name] = {
                    "exit": outcome.returncode,
                    "caught_by": test_name,
                }
        finally:
            SOURCE.write_bytes(original)

    print(json.dumps(results, indent=2))
    print(f"{len(results['mutations'])} session transaction-boundary mutations rejected")


if __name__ == "__main__":
    main()
