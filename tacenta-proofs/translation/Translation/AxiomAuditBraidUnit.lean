import Model.AxiomAudit
import Translation.TacentaBraidUnit

/-!
The Braid-and-erasure translation unit's part of the translation package's axiom
audit. See `Translation/AxiomAudit.lean` for the rule.

`Translation.TacentaBraidUnit` is the translation of `tacenta-core/braid-unit`,
the ML-KEM Braid and its erasure codec compiled as one crate
(`tacenta-proofs/scripts/assemble-braid-unit.sh` assembles it, and its header
says what the unit is and is not). It has an audit module of its own rather
than a line in `AxiomAudit.lean`, as the three-leaf unit does, because the
unit's translation re-declares names that the standalone Braid and erasure
translations also declare, and Lean refuses to import two modules declaring
the same name into one environment.

No theorem is stated about the unit yet. This module walks its translation so
that the unit's axioms are audited from the commit that introduces it.
-/

run_cmd Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation]
