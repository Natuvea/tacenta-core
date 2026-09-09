# Contributing

Thank you for your interest. A few things keep contributions clean to accept.

## Developer Certificate of Origin

Every commit must be signed off under the Developer Certificate of Origin (DCO)
version 1.1 (https://developercertificate.org). Signing off certifies that you
wrote the change or otherwise have the right to submit it under the project's
licence. Add a line to each commit message:

    Signed-off-by: Your Name <you@example.com>

`git commit -s` adds it for you. Pull requests whose commits are not signed off
cannot be merged.

## Licence of contributions

This project is licensed under the Apache License, Version 2.0 (see `LICENSE`).
By contributing, you agree that your contributions are licensed under the same
terms. The Apache-2.0 licence includes an express patent grant (section 3).

## Provenance

Do not paste code, interface definitions, or other material from third-party
implementations of the protocols this project targets. Work from the published
specifications. See the clean-room boundary recorded in the decision records.

## Building and checking

The README's "Building and checking" section lists the prerequisites and the
one command, `bash tooling/ci.sh`, that runs the gate. Run it before opening
a pull request. The public CI runs the same steps, split into jobs, and the
README states the two ways they differ: the steps the workflow always runs
that the script skips when their tooling is absent (it prints a line for
each), and the two the script runs that the workflow does not. Any other
difference between the two is a bug in one of them.

A pre-push hook is provided that runs the cheap part of that gate, the
workflow-file check, on the machine that wrote the change. It is not enabled
by cloning; enable it once per clone with

    git config core.hooksPath .githooks

`.githooks/pre-push` says why the check has to run somewhere other than
inside the workflow it protects.
