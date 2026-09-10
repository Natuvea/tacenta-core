import Model.AxiomAudit
import Translation.TacentaTripleUnit
import Translation.UnitPins

/-!
The three-leaf translation unit's half of the translation package's axiom
audit. See `Translation/AxiomAudit.lean` for the rule.

`Translation.TacentaTripleUnit` is the translation of `tacenta-core/triple-unit`,
the Triple Ratchet and both inner ratchets compiled as one crate
(`tacenta-proofs/scripts/assemble-triple-unit.sh` assembles it, and its header
says what the unit is and is not). It needs an audit module of its own for the
same reason `AxiomAuditTriple.lean` does, and against both of the others: it
declares `instDiscriminantRatchetErrorIsize` and
`instDiscriminantSpqrErrorIsize`, as `TacentaRatchet`/`TacentaSpqr` do and as
`TacentaTriple`'s re-emitted copies do, and Lean refuses to import two modules
declaring the same name into one environment. So it can share an environment
with neither audit that already exists.

It also imports `Translation.UnitPins`, and through it the unit's copies of
the two leaf panic-freedom proofs. Those are the only proofs in this island,
and this is the only module that reaches them, so the audit walks them here or
nowhere: `scripts/no-sorry.sh` compares the `audit-axiom:` lines with the
recorded manifest, and a module nothing imports would be built, scanned and
never audited.
-/

run_cmd Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation]
