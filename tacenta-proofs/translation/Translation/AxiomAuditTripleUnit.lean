import Model.AxiomAudit
import Translation.TacentaTripleUnit
import Translation.UnitPins
import Translation.UnitSpqrT3
import Translation.UnitSatisfiabilityTriple

/-!
The three-leaf translation unit's half of the translation package's axiom
audit. See `Translation/AxiomAudit.lean` for the rule.

`Translation.TacentaTripleUnit` is the translation of `tacenta-core/triple-unit`,
the Triple Ratchet and both inner ratchets compiled as one crate
(`tacenta-proofs/scripts/assemble-triple-unit.sh` assembles it, and its header
says what the unit is and is not). It needs an audit module of its own: it
declares `instDiscriminantRatchetErrorIsize` and
`instDiscriminantSpqrErrorIsize`, as `TacentaRatchet`/`TacentaSpqr` do, and Lean
refuses to import two modules declaring the same name into one environment. So
it cannot share an environment with `Translation/AxiomAudit.lean`.

It also imports `Translation.UnitPins`, and through it the unit's copies of
the two leaf panic-freedom proofs and the classical ratchet's refinement, the
Triple's panic-freedom on the unit, `Translation.UnitTripleT1`, and the Triple's
refinement on the unit, `Translation.UnitTripleT3`. It imports two modules
directly because nothing else does: `Translation.UnitSpqrT3`, the sparse
ratchet's refinement, which nothing pins, and
`Translation.UnitSatisfiabilityTriple`, the satisfiability witnesses for the
Triple's refinement on the unit. Those are the only proofs in this island,
and this is the only module that reaches them, so the audit walks them here or
nowhere: `scripts/no-sorry.sh` compares the `audit-axiom:` lines with the
recorded manifest, and a module nothing imports would be built, scanned and
never audited.
-/

run_cmd Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation]
