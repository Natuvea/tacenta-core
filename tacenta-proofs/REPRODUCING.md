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
| Charon and Aeneas | release `nightly-2026.07.22-b1214ca`, archive `aeneas-linux-x86_64.tar.gz` with SHA-256 `bc26c30daf92679b57c264c630710096bd9d4428e28795fe0638afdb0c2df65f`. The digest is checked by the private verification workflow before it extracts the archive (that workflow is not in this tree), and stated here so a reader elsewhere can confirm they hold the same binaries. What the public tree checks is the recorded manifest: the release name and the library commit are read by `attest.py` into `manifests/verification-manifest.json`, and the generated files that release produced are held, byte for byte, to `manifests/translation-attestation.json` by `attest.py --check` | `scripts/run-aeneas.sh` and `translation/lakefile.toml` carry the pins; the verification workflow carries the digest |
| Mathlib build artifacts | **not pinned**: `lake exe cache get` fetches prebuilt oleans for the manifest's Mathlib commit from Mathlib's cache over HTTPS, and Lean loads them without re-checking against source | trusted, see `LIMITATIONS.md` |
| Rust, for Charon | whatever the Aeneas release's `rust-toolchain` names | resolved at run time, not pinned here |

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

Translates the verified zone -- the leaf crates only: ratchet, session, erasure,
protobuf, spqr, braid, triple. It writes into `translation/Translation/`
alongside the hand-written proofs. Immediately afterwards, and at no other
time, record what it produced:

```sh
python3 tacenta-proofs/scripts/attest.py --refresh-translation
```

This rewrites `manifests/translation-attestation.json`: for each generated
`Translation/Tacenta*.lean`, its SHA-256, the `axiom` names it declares (the
keyword read from the comment-stripped text wherever it sits on a line), the
SHA-256 of the Rust crate it was generated from, and the SHA-256 of the
workspace inputs that shape what Charon extracts from every crate -- the
workspace `Cargo.toml` and its `[profile]` tables, `Cargo.lock`, `.cargo/`
if present, and the `kdf` and `kem` crates -- with the Aeneas pin. It
refuses to record a `Tacenta*.lean` that `run-aeneas.sh` does not produce.
Every other `attest.py` mode, and `scripts/check-generated-files.sh` (which
runs `attest.py --check-translation` and nothing else), compares the tree
against that record and fails on a file named like a generated one that the
script does not produce, on a generated file that differs from the record,
on an axiom set that gained or lost a name, or on a Rust crate or a
workspace input whose hash has moved since the translation was made -- the
message names the crate and says to regenerate. Running
`--refresh-translation` at any other time would record whatever the files
happen to be, which is why its whole value is in when it is run. The drift
step in the private verification workflow is the stronger check: it
regenerates with the pinned toolchain and fails on any difference, which
also catches a recorded generation the toolchain would no longer produce.
The recorded manifest is what the public tree holds in its place.

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
are exempt from the axiom rule only: `attest.py` holds their axiom sets to
the recorded manifest from the text, and the audit prints every axiom it
finds in them in the built environment (`audit-axiom:` lines, with the
compiler-trust ones Aeneas's `toStr` introduces apart as `audit-native:`),
which `no-sorry.sh` hands to `attest.py --compare-audit` to check against
the same manifest. After the builds it runs four checks --
`check-translation-coverage.sh`, that every `Translation/*.lean` produced an
olean; that comparison; `check-lean-constructs.sh`, the textual second
line of the audit, which strips comments and strings, refuses the keywords
wherever they sit on a line in every hand-written module (the package roots
and `Vectors.lean` included), refuses a lakefile that sets any Lean option,
is the only one that sees `set_option debug.skipKernelTC`, and refuses
every elaboration-time construct (`run_cmd`, `#eval`, `elab`, `macro`,
`syntax`, `initialize`, `addDecl`, any reference to the `Lean` namespace)
outside `Model/AxiomAudit.lean`'s own implementation and the five `run_cmd
Model.AxiomAudit.run` lines, which it allow-lists by file path and exact
line content, because such code could plant an axiom in the one shape the
audit accepts; `check-audit-reach.sh`, which asks Lean for every
first-party module's imports and fails if any module (the generated
`Tacenta*.lean` included) is outside the five audit modules' import
closure, since the audit walks only what its invoking module imports, and
which also requires all five to run with the same first-party prefixes, so
that no declaration is first-party to the audit that declares an axiom and
foreign to the audit that uses it; and `check-audit-negatives.sh`, which
plants declarations the audit's rule says to refuse, and the one shape it
says to allow -- twelve in all, one per refusal kind and one per
compiler-trust condition -- in a throwaway first-party module, and fails if
the audit calls any of them wrongly -- and then replays every first-party module
through the kernel with `leanchecker` (below).

Expected tail:

```
no-sorry: the translation and its T1/T3 proofs is complete
translation-coverage: all 34 Translation/*.lean modules are in the build target and built
attest: the axiom audit's opaque-external list matches translation-attestation.json for 8 generated modules (102 compiler-trust axioms in them, from Aeneas's toStr bound, are not externals and are listed in the build log)
no-sorry: the model-layer proofs is complete
no-sorry: the model and its property theorems is complete
check-lean-constructs: 63 first-party Lean files declare no axiom, opaque, implemented_by, extern, partial, unsafe, compiler-namespace name or debug option, and carry no elaboration-time code outside the audit's 5 allow-listed invocations and its implementation; 3 lakefiles set no Lean option
audit-reach: the 5 audit modules, all with the same first-party prefixes, reach all 70 first-party modules (tacenta-model 25, tacenta-proofs 10, tacenta-proofs/translation 35)
audit-negatives: the audit called all 12 planted cases correctly
no-sorry: replaying the translation and its T1/T3 proofs through the kernel (leanchecker)
no-sorry: the translation and its T1/T3 proofs replays clean (34 modules)
no-sorry: replaying the model-layer proofs through the kernel (leanchecker)
no-sorry: the model-layer proofs replays clean (10 modules)
no-sorry: replaying the model and its property theorems through the kernel (leanchecker)
no-sorry: the model and its property theorems replays clean (25 modules)
```

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
  place the two meet is the generated files' axiom sets: `attest.py --check`
  reads them from the text, and `no-sorry.sh` reads the same sets out of the
  built environment and fails if they differ.

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
  the audit's own implementation and its five invocations, by path and
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
