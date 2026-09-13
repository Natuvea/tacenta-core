# Erasure decoder refinement: P7 design note

This note records the first bounded P7 result. It does not raise the erasure
component's assurance level or discharge a translation assumption.

The current engagement's L3 target and the conditions that reopen L4 are
recorded separately in [ERASURE-CODEC-TARGET-DECISION.md](ERASURE-CODEC-TARGET-DECISION.md).

## What exists

`Translation/BraidT3.lean` already defines `DecoderRefines`: a real decoder
simulates a `Model.Braid.Decoder` for a common source and carries that relation
over each honest codeword. `Translation/ErasureWitness.lean` restates the same
shape for the concrete API. Both are useful interfaces, but both occur inside
the assumed `ErasureAgrees` relation. They are not a proof that
`tacenta_erasure::Decoder` establishes that relation.

The model itself specifies that a decoder retains the first codeword at an
index and ignores later duplicates, and ignores every offer after it is
complete. `Model.Erasure.Decoder.add_eq_self_of_duplicate` and
`Model.Erasure.Decoder.add_eq_self_of_complete` now prove those two model-side
rejection transitions. The real decoder exposes an `advanced` verdict from
`add_chunk`.

`Tacenta.ErasureT3.decoder_add_chunk_rejects_complete` also proves the full
decoder's concrete leaf transition: the translated `tacenta-erasure` entry
point returns `ok (false, self)`. Braid currently refers to a separately
translated opaque erasure dependency, so this leaf theorem is not yet usable as
a Braid `DecoderRefines` preservation theorem.

## First proof target

Prove a rejection-preservation lemma at the translated API boundary:

```
DecoderRefines real model ->
add_chunk real duplicate = ok (false, real') ->
real' = real /\ DecoderRefines real' model
```

Then prove the equivalent already-complete case. The statement must use the
real decoder's observable `advanced = false` result and preserve the model
state, rather than assuming every rejected input has the same internal form.

## Prerequisites and limits

The theorem needs a translated representation relation strong enough to state
whether an offered codeword duplicates a retained index and whether the real
decoder is complete. The current opaque decoder boundary lacks both facts, so
the next implementation slice must expose or prove only those observations;
it must not expand the trusted API with an arbitrary decoder layout.

An honest-codeword carry lemma already exists. It does not establish malformed,
duplicate, inconsistent or completed-decoder behaviour. The model lemmas and
the full leaf-decoder theorem above pin one rejection effect, but completing
the duplicate and other real cases and discharging `ErasureAgrees` for the
concrete decoder remains required for the L4 target.
