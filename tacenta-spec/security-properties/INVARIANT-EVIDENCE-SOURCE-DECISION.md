# Invariant evidence-source decision

## Decision

The version-2 invariant catalogue records live implementation symbols, model
properties, proofs and test functions. Its schema does not yet represent a
vector case or a reader's document as a first-class invariant
evidence item.

The semantic review at candidate `1f00fe86bc9bf469f342c62f30de64d4b15dbfa1`
found that this limits how precisely several persisted-format invariants can
name their strongest bounded evidence. The evidence itself remains recorded in
the conformance manifest, the P6 L2 decision, the P6 operation reader's evidence (`tacenta-test-vectors/runners/independent/P6-OPERATION-READER-EVIDENCE.md`, related-party evidence) and the pass records of the specification-only, project-controlled reader; this
is a representational limit of the catalogue, not an assertion that the vectors
or reader prove an invariant.

The current target keeps the schema at version 2. The semantic review record
must name any vector or reader evidence it relied on, while the catalogue cites
the corresponding live tests and the declared limitations. This disposition is
nonblocking for Practice 5 because it is explicit and does not promote the
omitted evidence to proof.

## Reopen trigger

Before treating a vector or a reader as primary invariant evidence,
or before adding a new invariant whose only suitable evidence is a vector or
reader record, introduce a versioned schema extension with structural
validation and mutation controls for those evidence kinds.
