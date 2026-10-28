# Contributing

Thank you for your interest. A few things keep contributions clean to accept.

## Developer Certificate of Origin

Every commit must be signed off under the Developer Certificate of Origin (DCO)
version 1.1 (https://developercertificate.org). Signing off certifies that you
wrote the change or otherwise have the right to submit it under the project's
licence. Add a line to each commit message:

    Signed-off-by: Your Name <you@example.com>

`git commit -s` adds it for you, and `git rebase --signoff origin/main` adds it
to commits already made. The trailer must name the commit's author exactly.

`tooling/check-signoff.sh` enforces this. It runs as the `sign-off` job on
every pull request, which fails if any commit the pull request adds is not
signed off by its author, and as a step of `tooling/ci.sh` against
`origin/main`. Merge commits in the pull-request range are checked too; protected
`main` requires linear history, so a branch should rebase rather than introduce an
unsigned merge of its base. Pull requests whose commits are not signed off cannot
be merged. The check covers only commits added on top of `main`, and commits on
`main` from before it was introduced carry no sign-off.

## Proof modules and merges

A new lifecycle proof module starts with
`python3 tacenta-proofs/scripts/new-lifecycle-module.py scaffold` and gets its pins with `... pins --lean` once
the proof is written; both print what is left to write by hand. Before handing a module over, run
`python3 tooling/check-proof-module-preflight.py <Module> --base origin/main` (with `TACENTA_PRIVATE_TERMS_FILE`
naming your local list of terms to keep out, if you keep one). After merging a branch that touches
the generated files, run `bash tooling/regenerate-generated.sh` rather than resolving them by hand, and check a
merge you resolved with `bash tooling/check-merge-exactness.sh HEAD`; put edits that adapt the merged tree in a
commit after the merge, not in it. When a conflict in `tooling/gate-inventory.json` or `ASSURANCE-OBLIGATIONS.md`
is settled by taking one side, re-apply the other side's additions; `bash tooling/check-landing.sh` fails while
the rows and the section it lists are missing. The "Building and checking" section of
`README.md` says what each of these holds.

## Licence of contributions

This project is licensed under the Apache License, Version 2.0 (see `LICENSE`).
By contributing, you agree that your contributions are licensed under the same
terms. The Apache-2.0 licence includes an express patent grant (section 3).

## Provenance

Do not paste code, interface definitions, or other material from third-party
implementations of the protocols this project targets. Work from the published
specifications. See the clean-room boundary recorded in the decision records.

## Specification first

The specification in `tacenta-spec` is the product, and `tacenta-core` is one
implementation of it
(`tacenta-spec/decisions/ADR-0006-specification-is-normative.md`). So:

- A change to anything the specification defines -- bytes emitted or
  accepted, a refusal, a constant, a derivation, a bound, a rule over
  persisted state -- changes the specification first. Its commit comes
  before the code's in the same pull request, with an entry in
  `tacenta-spec/CHANGELOG.md`, and the model and vectors follow it.
- Code that disagrees with the specification is a bug in the code. If it is
  the specification that should change, change it first, as above; do not
  change the code and describe it afterwards.
- Behaviour the specification does not define is a finding: specify it, or
  remove it.
- A pull request says which specification text its change implements. The
  pull-request template asks.

## Building and checking

The README's "Building and checking" section lists the prerequisites and the
one command, `bash tooling/ci.sh`, that runs the gate. Run it before opening
a pull request. Before each commit, run the quick check, `bash tooling/fast.sh`:
the cheap part of the gate (`bash tooling/ci.sh --fast`) and, for the files your
change touches, `cargo fmt`, `cargo clippy` and `cargo test` on the affected
Rust packages, `lake env lean` on each changed Lean module and, for a change
under `tooling/` or `.github/`, the gate-inventory check. It takes a few
minutes, says at the end what it did not run, and is not a substitute for the
gate or the hosted CI. Its cheap part includes the offline lockfile check
(`tooling/check-lockfiles.sh`), which needs `cargo` and a cargo registry cache
holding the locked packages, fetches nothing, and prints a SKIP for a lockfile
it cannot resolve offline. The default pre-push hook does not run it;
`FAST_PRE_PUSH=1` does. Seven slow case files of the tooling run in it only with
`--deep`, which a change under `tooling/` or `.github/` selects for you.
The full gate (`bash tooling/ci.sh`) and the gate controls (`bash
tooling/tests/run-gate-controls.sh`) check their tools first and fail at once,
naming any that is missing: both need git, python3 and cargo, and the full
gate also rustfmt, clippy and lake. If you run the controls in a clean
environment with `env -i`, keep cargo on PATH (the README shows the command).
The quick check is the reduced form for a machine without them; it says what it
skipped and is not the gate. The public CI runs the same steps, split into jobs, and the
README states the two ways they differ: the steps the workflow always runs
that the script skips when their tooling is absent (it prints a line for
each), and the three the script runs that the workflow does not. Any other
difference between the two is a bug in one of them.

A pre-push hook is provided that runs the cheap part of that gate, the
workflow-file check, on the machine that wrote the change. It is not enabled
by cloning; enable it once per clone with

    git config core.hooksPath .githooks

`.githooks/pre-push` says why the check has to run somewhere other than
inside the workflow it protects.

The hook also runs the quick check before a push if you ask it to: set
`FAST_PRE_PUSH=1` in your environment (or for one push, `FAST_PRE_PUSH=1 git
push`). Without that variable the hook is unchanged.
