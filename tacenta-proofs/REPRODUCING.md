# Reproducing the verification

Toolchain, steps, and expected output to reproduce every proof.

Two gates run here, in two different workflows, and the difference matters if
you are checking a claim: the light one runs on every push, the heavy one
translates the Rust and proves things about it. Reproducing "the proofs" means
running both.

## Toolchain

| Component | Pin | Where |
| --- | --- | --- |
| Lean | `leanprover/lean4:v4.31.0` | `lean-toolchain` (and `translation/lean-toolchain`) |
| Lean dependencies, model layer | exact revisions | `lake-manifest.json` |
| Lean dependencies, translation (Aeneas library, Mathlib, Batteries, Aesop) | exact revisions | `translation/lake-manifest.json`, with the Aeneas library `rev` pinned by commit in `translation/lakefile.toml` |
| Charon and Aeneas | release `nightly-2026.07.22-b1214ca`, archive `aeneas-linux-x86_64.tar.gz` with SHA-256 `bc26c30daf92679b57c264c630710096bd9d4428e28795fe0638afdb0c2df65f`. The digest is checked by the private verification workflow before it extracts the archive (that workflow is not in this tree) and by `scripts/regenerate-in-container.sh`, and stated here so a reader elsewhere can confirm they hold the same binaries. What the public tree checks is the recorded manifest: the release name and the library commit are read by `attest.py` into `manifests/verification-manifest.json`, and the generated files that release produced are held, byte for byte, to `manifests/translation-attestation.json` by `attest.py --check`. The macOS arm64 archive `aeneas-macos-aarch64.tar.gz` of the same release (SHA-256 `9c3c76c0be6abc28b7ec8d2847ae8bd9c0d8eae7c4233c4b16724f267d9a7873`, the digest the release page lists for it) was used for the local regeneration recorded under `HL-R1-SPARSE-TRANSLATION` in `GAP-REGISTER.md`; the workflow does not check it | `scripts/run-aeneas.sh` and `translation/lakefile.toml` carry the pins; the verification workflow and `scripts/regenerate-in-container.sh` carry the digest |
| Mathlib build artifacts | **not pinned**: `lake exe cache get` fetches prebuilt oleans for the manifest's Mathlib commit from Mathlib's cache over HTTPS, and Lean loads them without re-checking against source | trusted, see `LIMITATIONS.md` |
| Rust, for Charon | whatever the Aeneas release's `rust-toolchain` names | resolved at run time, not pinned here; `scripts/regenerate-in-container.sh` requires the channel `nightly-2026-06-01` and checks the SHA-256 of a download of its manifest |

The last row is a real dependency edge and not an omission: Charon is a `rustc`
driver, so it must be built against the compiler version its release was built
for. Pinning a second Rust version here would let the two disagree with nothing
to notice.

## The light gate: model and model-layer proofs

```sh
cd tacenta-proofs && ./scripts/verify.sh
```

Builds the Lean proofs on the pinned toolchain and greps `Proofs/` for `sorry`
and `admit`. `tooling/ci.sh` runs it, and it needs nothing but `lake`.

**Its `sorry` check is the weaker of the two, deliberately.** It greps one
directory and matches the word wherever it appears, including in prose that
explains there is no `sorry`. It covers `Proofs/`, not `translation/`. The
authoritative check is below; this one exists so that an every-push gate can
stay cheap.

Expected tail:

```
verify: proofs built clean
```

## The heavy gate: translation, T1, and T3

Run by the verification workflow on every push, nightly, and on demand.
Locally it is three steps, and the first needs Charon and Aeneas on `PATH`:

```sh
bash tacenta-proofs/scripts/run-aeneas.sh
```

Translates the verified zones -- ratchet, session, erasure, protobuf, spqr,
braid, and lifecycle -- plus three assembled units: the three-leaf
`triple-unit`, which is the only translation of the Triple crate; the
Braid-and-erasure `braid-unit`; and the eight-leaf `session-unit` used to put
the complete session call graph in one generated namespace. It writes into `translation/Translation/`
alongside the hand-written proofs. Commit the source changes before recording
the output: `--refresh-translation` records the current `HEAD`, and the
attestation check requires that commit to be available in the current history.
Then record what it produced:

```sh
python3 tacenta-proofs/scripts/attest.py --refresh-translation
```

This rewrites `manifests/translation-attestation.json`: for each generated
`Translation/Tacenta*.lean`, its SHA-256, the axioms it declares (each by fully
qualified name, the enclosing `namespace` applied, read from the
comment-stripped text wherever the keyword sits, one entry per declaration), the
SHA-256 of the Rust crate it was generated from, and the SHA-256 of the
workspace inputs that shape what Charon extracts from every crate -- the
workspace `Cargo.toml` and its `[profile]` tables, `Cargo.lock`, `.cargo/`
if present, and the `kdf` and `kem` crates -- with the Aeneas pin. It
refuses to record a `Tacenta*.lean` that `run-aeneas.sh` does not produce.
The attestation check also verifies that `generated_at_commit` is a commit
available in the checkout and an ancestor of the current `HEAD`; use a full
clone or run `git fetch --unshallow` before reproducing it. A shallow checkout
therefore fails closed with a history-availability message, rather than
providing provenance it cannot inspect.
Every other `attest.py` mode, and `scripts/check-generated-files.sh` (which
runs `attest.py --check-translation` and nothing else), compares the tree
against that record and fails on a file named like a generated one that the
script does not produce, on a generated file that differs from the record,
on an axiom list that gained or lost a declaration, or on a Rust crate or a
workspace input whose hash has moved since the translation was made -- the
message names the crate and says to regenerate. Running
`--refresh-translation` before committing the source changes fails closed,
because the recorded generation commit would not contain them. Commit the
generated files and manifests after the refresh. Running the command at any
other time would record whatever the files happen to be, which is why its
whole value is in when it is run. The drift
step in the private verification workflow is the stronger check: it
regenerates with the pinned toolchain and fails on any difference, which
also catches a recorded generation the toolchain would no longer produce.
The recorded manifest is what the public tree holds in its place. A reader
with Docker can run the same regeneration and comparison by hand with
`scripts/regenerate-in-container.sh`, described below.

`manifests/translation-axiom-allowlist.json` is a second record of the same
declarations, with the type text of each. `attest.py --check` compares every
generated file's `axiom` declarations with it, by qualified name and type, as a
multiset, so a declaration in another namespace, a repeated one, or one with a
different type is a difference. `--refresh-translation` never writes it and
refuses to record a tree it does not describe. When a regeneration changes the
generated axioms, the order is: run `scripts/run-aeneas.sh`, then
`python3 tacenta-proofs/scripts/attest.py --write-axiom-allowlist`, which
prints each declaration it added or removed (read them), then
`--refresh-translation`. Commit the allowlist on its own, with the added and
removed declarations in the commit message. Nothing in the tree makes that
commit reviewed: there is no CODEOWNERS file, and the tool only shows the
difference.

```sh
cd tacenta-proofs/translation && lake exe cache get && lake build
```

Builds the generated Lean and every T1 (panic-freedom) and T3 (refinement)
proof against the Aeneas library, at the dependency commits recorded in
`translation/lake-manifest.json`. **Not `lake update`**: that re-resolves every
dependency and rewrites the manifest, which is the right thing to do
deliberately when moving the pins and the wrong thing to do while reproducing a
claim. `lake exe cache get` fetches Mathlib rather than building it; skipping
it works and costs hours.

```sh
bash tacenta-proofs/scripts/no-sorry.sh
```

**This is the authoritative completeness check.** It asks the compiler instead
of grepping the source: Lean emits "declaration uses `sorry`" for every
incomplete declaration it elaborates, so a build log is exhaustive where a grep
is not. It runs three builds -- `translation/`, the model-layer proofs, and
the model package on its own terms so that `Properties/` is elaborated -- and
it filters *positively* by our own directories, so a third-party `sorry`
(Aeneas's own library ships four) is not ours and is not failed on, while
anything it does not recognise is treated as third-party rather than quietly as
first-party. Each of those builds also runs the package's `AxiomAudit`
module (`tacenta-model/Model/AxiomAudit.lean`), which walks the elaborated
environment and fails the build if any hand-written declaration is an axiom,
opaque, unsafe or partial, carries `implemented_by`/`extern`, or is named
into the compiler's `_native`/`_unsafe_rec` namespace outside the exact
shape the compiler produces (a `native_decide`/`bv_decide` axiom is accepted
only as `<decl>._native.<tactic>.ax_*`, off a declaration in the same
module, stating that a compiled Boolean evaluation returned `true`; a
`<f>._unsafe_rec` only as the partial definition the compiler makes for a
recursive `<f>` in the same module, because the code generator would call a
hand-written one in place of `<f>`). The generated `Translation/Tacenta*.lean`
are exempt from the axiom rule only: `attest.py` holds their axiom declarations
to the recorded manifest and the allowlist from the text, and the audit prints every axiom it
finds in them in the built environment (`audit-axiom:` lines, with the
compiler-trust ones Aeneas's `toStr` introduces apart as `audit-native:`),
which `no-sorry.sh` hands to `attest.py --compare-audit` to check against
the same manifest and the allowlist, name for name and fully qualified. After the builds it runs four checks --
`check-translation-coverage.sh`, that every `Translation/*.lean` produced an
olean; that comparison; `check-lean-constructs.sh`, the textual second
line of the audit, which strips comments and strings, refuses the keywords
wherever they sit on a line in every hand-written module (the package roots
and `Vectors.lean` included), refuses a lakefile that sets any Lean option,
is the only one that sees `set_option debug.skipKernelTC`, and refuses
every elaboration-time construct (`run_cmd`, `#eval`, `elab`, `macro`,
`syntax`, `initialize`, `addDecl`, any reference to the `Lean` namespace)
outside `Model/AxiomAudit.lean`'s own implementation and the seven `run_cmd
Model.AxiomAudit.run` lines, which it allow-lists by file path and exact
line content, because such code could plant an axiom in the one shape the
audit accepts; `check-audit-reach.sh`, which asks Lean for every
first-party module's imports and fails if any module (the generated
`Tacenta*.lean` included) is outside the seven audit modules' import
closure, since the audit walks only what its invoking module imports, and
which also requires all seven to run with the same first-party prefixes, so
that no declaration is first-party to the audit that declares an axiom and
foreign to the audit that uses it; and `check-audit-negatives.sh`, which
plants declarations the audit's rule says to refuse, and the one shape it
says to allow -- thirteen in all, one per refusal kind and one per
compiler-trust condition -- in a throwaway first-party module, and fails if
the audit calls any of them wrongly -- and then replays every first-party module
through the kernel with `leanchecker` (below).

The session lifecycle leaf (`tacenta-core/lifecycle`) is translated from its
public items only: `run-aeneas.sh` passes Charon `--start-from-pub`, because
extracting every private and test-only item of that crate produced an LLBC
file three orders of magnitude larger. Private helpers reachable from a
public item are still translated; `scripts/check-lifecycle-translation-coverage.py`
fails the run if any of the thirty public operations has no generated
definition, and its negative control shows that it can.

Expected tail (the file counts below were read from a tree at `dea57eaf`; the
`attest`, `audit-reach`, `audit-negatives` and replay lines are from the log of the
`translation` job of run 36629026947, which ran on the project's self-hosted
runner; every count moves with the tree):

```
no-sorry: the translation and its T1/T3 proofs is complete
translation-coverage: all 68 Translation/*.lean modules are in the build target and built
lifecycle-translation-coverage: all 30 public operations generated
lifecycle-translation-coverage-negatives: missing-root mutation refused
attest: the axiom audit's opaque-external list matches translation-attestation.json for 11 generated modules (346 compiler-trust axioms in them, from Aeneas's toStr bound, are not externals and are listed in the build log)
no-sorry: the model-layer proofs is complete
no-sorry: the model and its property theorems is complete
check-lean-constructs: 106 first-party Lean files declare no axiom, opaque, implemented_by, extern, partial, unsafe, compiler-namespace name or debug option, and carry no elaboration-time code outside the audit's 7 allow-listed invocations and its implementation; 3 lakefiles set no Lean option
audit-reach: the 7 audit modules, all with the same first-party prefixes, reach all 116 first-party modules (tacenta-model 36, tacenta-proofs 11, tacenta-proofs/translation 69)
audit-negatives: the audit called all 13 planted cases correctly
no-sorry: replaying the translation and its T1/T3 proofs through the kernel (leanchecker)
no-sorry: the translation and its T1/T3 proofs replays clean (68 modules)
no-sorry: replaying the model-layer proofs through the kernel (leanchecker)
no-sorry: the model-layer proofs replays clean (11 modules)
no-sorry: replaying the model and its property theorems through the kernel (leanchecker)
no-sorry: the model and its property theorems replays clean (36 modules)
```

The transcript was taken before three further controls were added to the script, so it does not show their
lines: `check-audit-reach-negatives.sh` (an unwalked module and a wrong audit call, each refused), then
`check-pin-negatives.sh` (Lean refuses a changed `#guard_msgs` pin) after the audit-reach line, and
`check-kernel-replay-negative.sh` (`leanchecker` refuses a declaration added under
`debug.skipKernelTC`) after the replays. Each prints one summary line beginning with its own name.

## Regenerating the translation on Linux x86_64, by hand

```sh
bash tacenta-proofs/scripts/regenerate-in-container.sh --check
```

This is the drift step of the private verification workflow, done by hand by
anyone with Docker. It copies the tracked files as they are on disk, starts a
`linux/amd64` container from an image pinned by digest, installs the pinned
toolchain, extracts the release's `aeneas-linux-x86_64.tar.gz` after checking
its SHA-256, runs `scripts/run-aeneas.sh` on the copy and compares the tracked
files with the result, by bytes and by executable bit. A changed, missing, extra
or linked file, and a comparison that could not be made, exit nonzero. It
writes nothing into the checkout and refreshes no manifest, so a difference is
something to read and not something to overwrite; nothing is kept unless
`--keep DIR` is given. The script is in no workflow; hosted CI has no step that
regenerates.

Its header says what it pins and what it does not. The image, archive,
rustup-init and channel manifest digests and the compiler version line that it
holds must be stated in this file, and the release it holds must be the one
`run-aeneas.sh` pins; it refuses to start otherwise. The Rust toolchain is
installed by rustup from static.rust-lang.org. A separate download of its dated
channel manifest is checked by hash, which is a canary: rustup installs from its
own download, and the components are not pinned. The Ubuntu packages come from
the archive of the day, and so does the libc that `libc6-dev` requires, so the
libc the tools ran under is not fixed by the image digest alone; the crates are
fixed by `Cargo.lock`. `tooling/tests/run-regenerate-in-container-cases.sh`,
which `tooling/tests/run-gate-controls.sh` runs in CI, holds the comparison, the
exit status of `--check` and the refusals that come before docker to planted
changes, with a stub docker; it starts no container. On an Apple-silicon Mac the
container is emulated, and the script's header explains the one QEMU setting it
needs.

**The run recorded here** is of the committed script.

| | |
| --- | --- |
| Run | 2026-10-03, 21:13Z to 21:37Z (24 min 1 s; `run-aeneas.sh` 19 min 33 s) |
| Script | `tacenta-proofs/scripts/regenerate-in-container.sh`, git blob `5d32f0c72d7a252156fa8750f4fa6935cecbfbf5` |
| Tree | `6b6a48a1581d2db2b659c4902855eddfde7b95ae`, a clean tree (the run counted 0 tracked paths differing from HEAD): `1cabffba85219029cd85f129a81f627f911b06b5` (`main`, 5,132 tracked files) with this change's script and control added, 5,134 tracked files in all, and the documents of this change. After the run, this section and two register rows were changed (`HL-R1-SPARSE-TRANSLATION`, which names the run, and one sentence of `READER-OPEN-GAPS`), and the control `tooling/tests/run-regenerate-in-container-cases.sh`, which the run does not use, was extended; no other file differs, and the script is the blob above. No Rust, Lean, model, specification or vector file differed from `main`. |
| Host | Apple-silicon Mac (Darwin arm64, macOS 26.5.1), Docker Desktop 4.78.0 on Apple's virtualization framework, engine 29.5.3. The `linux/amd64` container ran under QEMU user-mode emulation; the machine is not x86_64 and the run is not native. |
| Image | `ubuntu@sha256:a853f94d226358a79c740cfc7bce0c289748f3fe3488d921d038ccd752c61b60` (the `ubuntu:24.04` index; its `linux/amd64` manifest is `sha256:f610ab94648195aa356059f5b41d6085c9d4d903c072430cdd1af7bdb646106b`), Ubuntu 24.04.5 LTS, glibc 2.39 |
| Archive | `aeneas-linux-x86_64.tar.gz`, 123,515,708 bytes, SHA-256 `bc26c30daf92679b57c264c630710096bd9d4428e28795fe0638afdb0c2df65f`, the digest above and the one the release page lists; checked on the host and again in the container before extraction |
| Binaries | `aeneas` `0c58f05b2d9941b76e29155235069915afd5302e8fcff49be501775c3e3c7f97`, `charon` `573198ce7e7d94d74cf0c9c27febeacc29c6aeee70ef1dad3cb4fdee5c4924b1`, `charon-driver` `73da048703631d5069a8f63fe136ce344b79682804606b5bd7fe86b7dd97af59` (SHA-256, read after extraction); all x86-64 ELF |
| Versions | Aeneas `nightly-2026.07.22-b1214ca`; Charon 0.1.223; `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with LLVM 22.1.6, from rustup 1.29.1 (`rustup-init` SHA-256 `dda7234360b7f578ca8b0ddcb80145646fa61a67c1720a5abc7051b35c9fcb71`) and the channel `nightly-2026-06-01`, whose dated manifest has SHA-256 `aaf1cb59b5996dd51831c9114b6e3a4a176e197851de91194b473117e142b935` (a canary, as above; the manifest rustup kept for the installed toolchain has SHA-256 `accac0633b1299e08f681c24d9ea0f701bc726983c58a59580675bf49d9ce794`, recorded and not pinned), with the components and targets the archive's `rust-toolchain` names; `cargo 1.98.0-nightly (fbb61be30 2026-05-26)`; gcc 13.3.0; Python 3.12.3. Ubuntu packages installed on the day: ca-certificates 20260601~24.04.1, curl 8.5.0-2ubuntu10.15, gcc 4:13.2.0-7ubuntu1, libc6 2.39-0ubuntu8.9, libc6-dev 2.39-0ubuntu8.9, python3 3.12.3-0ubuntu2.1. |
| Compared | All 5,134 tracked files of the tree. The run rewrites 29 of them (the run lists them in `rewritten.txt`): the eleven generated `Translation/Tacenta*.lean` and the 18 files of the three assembled unit crates (`tacenta-core/triple-unit`, `braid-unit`, `session-unit`); those are the reproduction. The other 5,105, `Cargo.lock` among them, pass through the run and show that it changed nothing else. All were equal by bytes and executable bit. `run-aeneas.sh` staged all eleven generated files, and its lifecycle coverage check found all 30 public operations generated. |
| Result | Every file equal. The eleven generated files and their SHA-256 (each also the digest `manifests/translation-attestation.json` records): |

```
e374be8e8302259159ae3b493a0aba1a21e60c544a763b14ad17c03f00327be6  TacentaBraid.lean
0ce8035516476746ed7ea232b713a228993d43939339e1fbed213755504a44a9  TacentaBraidUnit.lean
038508a176672c827cde5d7ced0ec8fca003ea3a8e4c1e840e698ef111a20d88  TacentaErasure.lean
a99625035a24607655603769ff7ae6ca74f098b69965f27ae3226c351c706599  TacentaLifecycle.lean
9b8f031d4d495cf1805f0bffd0ea580b7ffce5b7479a15008b79a6ff2ea97410  TacentaProtobuf.lean
46a1d8944208e0359c69e0847336add2f2d7262f42c82b0d3f690749ec153839  TacentaRatchet.lean
025aa0b9dec3da6a17e84a9ff3fb51f70989552e34e9b72dcd14c8a7fe8848b2  TacentaSession.lean
531b572f42a6406418793979f7e5efb181659e69554a86e3958de8eff537d0e0  TacentaSessionUnit.lean
fb7976957f7fd80fea3a7216d0c5c0d851f99fc357c157c38f9ef17eb9d3e26a  TacentaSpqr.lean
65e9818ad345c58f5d1a565bae04ff443ecd30c4f6772912baf5d558187270b0  TacentaTripleUnit.lean
646bce56a8fcbac1068e3e64aa407e7e51d83be436c876fe2208c749fa4f6db8  TacentaWire.lean
```

The four files `HL-R1-SPARSE-TRANSLATION` named (`TacentaSpqr.lean`,
`TacentaTripleUnit.lean`, `TacentaSessionUnit.lean`, `TacentaLifecycle.lean`)
are among them. Earlier runs passed on earlier versions of the script and are
not tabulated: one by hand in a container, and two runs of the script on
2026-10-03 (19:11Z to 19:30Z, and 19:37Z to 20:13Z on a clean tree, the second
of git blob `34fa4fdefec035525653d0d9fa7d88c1ef6eb95f`, which has a different
comparison and cleanup from the script above). A first attempt of the script
stopped on a missing directory in the container before it compared anything.
If `docker pull` hangs on the keychain credential helper, set `DOCKER_CONFIG`
to a directory whose `config.json` is `{}`; the image is public, and the runs
above used that.

**What this is evidence of.** That `run-aeneas.sh`, with the release's
linux-x86_64 binaries, produces from the tracked Rust the bytes that are
committed for the files it rewrites, on the date and with the tools above. It
is one run of the committed script by the maintainer's tool-assisted session in
an emulated container, repeatable with the script. It is not a hosted-CI job, it
did not run on the project's runner, and it was not made by anyone independent
of the maintainer. The logs of the run are not kept in this repository. It does
not change `SC-08-TRANSLATION-CHECKSUM` in `GAP-REGISTER.md`: the recorded
checksum still cannot establish that a toolchain regenerated a file, and nothing
in this tree regenerates on its own. It does not show that the translation is
the same on every platform; it adds a second platform (Linux x86_64) to the first
(macOS arm64) on which the committed bytes were reproduced.

## Replaying through the kernel

`lake build` checks a declaration with the kernel when it adds it, unless the
file asked it not to: `set_option debug.skipKernelTC true in` adds the next
declaration on the elaborator's word alone, and nothing in the resulting
environment records that it happened. The `#print axioms` pins do not see
it, the axiom audit does not see it, and `no-sorry.sh`'s log scan does not
see it. What does is `leanchecker`, which ships with the pinned toolchain
(it is the former `lean4checker`, merged into Lean from v4.28.0): it loads a
module's imports from their oleans and re-adds each of the module's own
declarations through the kernel, so a declaration the kernel would have
refused fails there. `no-sorry.sh` runs it over every first-party module of
all three packages; by hand, from the package directory:

```sh
cd tacenta-proofs/translation && lake env leanchecker Translation.T3
cd tacenta-proofs && lake env leanchecker Proofs.TrustedBase
cd tacenta-model && lake env leanchecker Properties.ForwardSecrecy
```

A module that replays prints nothing and exits zero. `lake env leanchecker
--fresh Translation.T3` replays every imported constant as well, from an
empty environment; that covers Mathlib and Aeneas too and takes far longer,
and is the form to use if the question is whether an *import* was tampered
with rather than a first-party file. Neither form is an independent
verifier: `leanchecker` is Lean's own kernel, run again over the oleans. It
is the direct defence against environment hacking, not against a bug in the
kernel itself.

## What a green run does and does not establish

`CLAIMS.md` is the ledger and `LIMITATIONS.md` is its counterpart; read both
rather than inferring scope from a green check. Two things worth knowing before
you do:

- **The claims are checked against the proofs, not maintained beside them.**
  `scripts/attest.py --check` runs in the every-push gate and fails if the
  ledger and the attestation manifests drift from the pins.

  **But it reads the pins as written, not as built.** The axiom facts come from
  the `#guard_msgs` docstrings in the source; the script hashes and
  cross-references those, and delegates *checking that they are true* to the
  build. So a green `attest` says the ledger is consistent with what the files
  claim; only a green heavy gate says the files are telling the truth. The one
  place the two meet is the generated files' axioms: `attest.py --check`
  reads them from the text, and `no-sorry.sh` reads the names out of the
  built environment and fails if they differ (the type of an axiom is compared
  with the allowlist from the text and not with the environment).

  The script also holds two lists that a regeneration cannot change. A theorem
  on `REQUIRED_PINS` must have a pin, so deleting its pin block fails both
  `attest.py` and `attest.py --check`, as does a pin block left inside a
  comment, and a pin that lists a compiler-trust axiom
  fails unless `COMPILER_TRUSTED_PINS` names its theorem. A theorem pinned twice
  fails as well. Editing either list is a change to `attest.py`.

  The ledger check is exact by name. Every theorem a claim bullet names --
  every backticked identifier in the bullet's leading run, not only the
  first -- must exist, fully qualified by its `namespace`, in a file the
  section's `Location:` line names (or the bullet's own `(in ...)`
  annotation, for the few theorems a section cites from the model); every
  `Location:` path must exist; and every theorem pinned under `#guard_msgs`
  anywhere must be claimed, matched on its full name so that a claim in one
  section cannot cover a pin in another.

  **And it holds the generated translation to a recorded generation.** A
  green `attest` says every `Translation/Tacenta*.lean` is the file recorded
  in `manifests/translation-attestation.json` at the last
  `--refresh-translation`, declares exactly the axioms recorded then, and
  that the Rust it was generated from is the Rust in the tree now. It does
  not say the recorded generation was produced by the pinned toolchain, or
  honestly: that is the heavy gate's drift step, described above.
- **The axiom audit recognises compiler trust by shape, and the shape is
  forgeable at elaboration time.** `Model.AxiomAudit` accepts a
  `<t>._native.<tactic>.ax_*` axiom, or a `<f>._unsafe_rec` auxiliary, only
  in the shape `native_decide`, `bv_decide` and the compiler produce. A
  `run_cmd` calling `addDecl` can produce that shape, with the name
  assembled from string literals, and `leanchecker` accepts the result,
  since an axiom is a kernel-valid declaration; the audit cannot tell a
  planted one from a real one. A green run therefore establishes three
  things *together*: every compiler-namespace declaration the audit saw has
  the compiler's shape; no hand-written first-party module contains
  elaboration-time code (`check-lean-constructs.sh`, which allow-lists only
  the audit's own implementation and its seven invocations, by path and
  exact line); and every first-party module is in an audit's import closure
  (`check-audit-reach.sh`). The first alone excludes nothing planted, and
  the second is a grep: a construct its stripper mishandles would be a hole
  in the rule, not something the audit would catch. A fourth check,
  `check-audit-negatives.sh`, asks the separate question of whether the rule
  still refuses what it says it refuses, by planting each case and
  comparing. `LIMITATIONS.md` records this under "Trusted, not verified".
- **T1 and T3 are about the Aeneas model of the Rust**, not the machine code
  `rustc` produces. The Charon and Aeneas translation, the Lean kernel, and the
  Rust compiler are all trusted. That trust is the point of writing the pins
  above down.
