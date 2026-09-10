import Model.AxiomAudit
import Model.Adversary
import Model.Braid
import Model.CompositeHeader
import Model.Gf65536
import Model.Kdf
import Model.Messages
import Model.MultiDevice
import Model.Polynomial
import Model.Protobuf
import Model.Ratchet
import Model.SessionEstablishment
import Model.Sha256
import Model.SparseRatchet
import Model.State
import Model.Triple
import Model.TripleRatchet
import Model.Types
import Properties.Authentication
import Properties.ForwardSecrecy
import Properties.Invariants
import Properties.PostCompromise
import Properties.Secrecy
import Properties.StateConsistency

/-!
The model package's axiom audit: every `Model.*` and `Properties.*` module,
imported here so that the walk in `Model.AxiomAudit` sees all of them. It sits
under `Properties/` because that library's glob builds every submodule, so
`lake build` in `tacenta-model` (and `no-sorry.sh`'s third build) runs it. A
new module under `Model/` or `Properties/` must be added to the imports above
to be audited; the model's own `native_decide` field proofs pass under the
compiler-trust allowance the audit documents.
-/

run_cmd Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation]
