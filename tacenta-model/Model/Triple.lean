/-
Model.Triple: the Triple Ratchet's own state machine, composing
`Model.Ratchet` and `Model.SparseRatchet` the way `tacenta-triple` composes
the two crates it wraps. Written from `tacenta-spec/protocol/triple-ratchet.md`
and from `tacenta-core/triple/src/lib.rs` directly, since the specification
page describes the algorithm but the clone-candidate-commit shape (a
send/receive that never partially applies one ratchet's step without the
other's) is an implementation decision recorded there, not in the spec.

`Model.TripleRatchet` already had `splitSecret`/`combine`, the two opaque-KDF
calls this composition makes on its own; this file is the state machine that
was missing around them -- `State`, `Header`, `send`, `receive`, `commit`,
and the two initialisers.

## What is here and what is not

`send`/`receive` do not decide which ratchet's output to trust: both must
succeed, in order (classical first, matching the real code), or the whole
call fails. Their compact forms collapse failures to `none`; the corresponding
`sendDetailed`/`receiveDetailed` forms retain the public leaf and refusal kind
for session refinement, and equivalence theorems keep the accepted states
identical.

`receive` does not mutate its input, mirroring the real `&self`-only method:
it returns a candidate state and a key, and `commit` is a separate step, a
bare projection. A model that folded `receive` and `commit` into one function
would say something the real code does not guarantee -- that receiving a
message advances the session before its authenticator is checked, which is
exactly what the separate `commit` step exists to prevent.
-/
import Model.Ratchet
import Model.SparseRatchet
import Model.TripleRatchet

namespace Model.Triple

open Model.State (Key)

/-! ## State and header -/

/-- The composed header: the classical ratchet's own header, carried
    unchanged, alongside the two fields the sparse ratchet's own `receive`
    needs (`epoch`, and `pqN` in place of its own `n`). No wire encoding is
    modelled here -- that is `Model.CompositeHeader`'s own, separately
    tracked concern. -/
structure Header where
  dr    : Model.State.Header
  epoch : Nat
  pqN   : Nat
  deriving Repr, Inhabited

/-- The composed state: a classical ratchet state and a sparse post-quantum
    ratchet state, side by side and independent, exactly as
    `tacenta_triple::State` holds them. -/
structure State where
  classical   : Model.State.State
  postQuantum : Model.SparseRatchet.State
  deriving Repr, Inhabited

/-! ## Initialisation

Both parties split the handshake secret into two, and feed one half to each
inner ratchet's own initialiser. -/

def initAlice (sk ourPub peerPub dhOut : Key) (labels : Model.State.LabelSet) : State :=
  let (ec, pq) := Model.TripleRatchet.splitSecret sk
  { classical   := Model.Ratchet.initSender ec ourPub peerPub dhOut labels,
    postQuantum := Model.SparseRatchet.initAlice pq }

def initBob (sk ourPub : Key) (labels : Model.State.LabelSet) : State :=
  let (ec, pq) := Model.TripleRatchet.splitSecret sk
  { classical   := Model.Ratchet.initReceiver ec ourPub labels,
    postQuantum := Model.SparseRatchet.initBob pq }

/-! ## Sending

Both ratchets must produce a key or the call fails; the encryption key is
the two message keys combined per §7.2. -/

def send (st : State) (sendingEpoch : Nat) (out : Option Model.SparseRatchet.Output) :
    Option (State × Header × Key) :=
  match Model.Ratchet.send st.classical with
  | none => none
  | some (s, dr, mkEc) =>
    match Model.SparseRatchet.send st.postQuantum sendingEpoch out with
    | none => none
    | some (s1, pqN, mkPq) =>
      some ({ classical := s, postQuantum := s1 },
            { dr, epoch := sendingEpoch, pqN },
            Model.TripleRatchet.combine mkEc mkPq)

/-- Which contributing ratchet refused a send, retaining that ratchet's exact
    public reason for the session layer. -/
inductive SendRefusal where
  | classical (reason : Model.Ratchet.SendRefusal)
  | postQuantum (reason : Model.SparseRatchet.SendRefusal)
  deriving Repr, DecidableEq, Inhabited

def sendDetailed (st : State) (sendingEpoch : Nat)
    (out : Option Model.SparseRatchet.Output) :
    Except SendRefusal (State × Header × Key) :=
  match Model.Ratchet.sendDetailed st.classical with
  | .error reason => .error (.classical reason)
  | .ok (classical, dr, mkEc) =>
      match Model.SparseRatchet.sendDetailed st.postQuantum sendingEpoch out with
      | .error reason => .error (.postQuantum reason)
      | .ok (postQuantum, pqN, mkPq) =>
          .ok ({ classical, postQuantum }, { dr, epoch := sendingEpoch, pqN },
            Model.TripleRatchet.combine mkEc mkPq)

theorem sendDetailed_ok_iff (st : State) (sendingEpoch : Nat)
    (out : Option Model.SparseRatchet.Output) (result : State × Header × Key) :
    sendDetailed st sendingEpoch out = .ok result ↔
      send st sendingEpoch out = some result := by
  cases hc : Model.Ratchet.sendDetailed st.classical with
  | error reason =>
      have ho : Model.Ratchet.send st.classical = none := by
        cases h : Model.Ratchet.send st.classical with
        | none => rfl
        | some result =>
            have := (Model.Ratchet.sendDetailed_ok_iff st.classical result).2 h
            rw [hc] at this
            contradiction
      simp [sendDetailed, send, hc, ho]
  | ok classicalResult =>
      obtain ⟨classical, dr, mkEc⟩ := classicalResult
      have ho := (Model.Ratchet.sendDetailed_ok_iff st.classical
        (classical, dr, mkEc)).1 hc
      cases hp : Model.SparseRatchet.sendDetailed st.postQuantum sendingEpoch out with
      | error reason =>
          have hpo : Model.SparseRatchet.send st.postQuantum sendingEpoch out = none := by
            cases h : Model.SparseRatchet.send st.postQuantum sendingEpoch out with
            | none => rfl
            | some result =>
                have := (Model.SparseRatchet.sendDetailed_ok_iff st.postQuantum
                  sendingEpoch out result).2 h
                rw [hp] at this
                contradiction
          simp [sendDetailed, send, hc, ho, hp, hpo]
      | ok postQuantumResult =>
          obtain ⟨postQuantum, pqN, mkPq⟩ := postQuantumResult
          have hpo := (Model.SparseRatchet.sendDetailed_ok_iff st.postQuantum
            sendingEpoch out (postQuantum, pqN, mkPq)).1 hp
          simp [sendDetailed, send, hc, ho, hp, hpo]

/-! ## Receiving

Non-mutating: a candidate state and the key, mirroring the real `&self`-only
method. `dhOutRecv`/`dhOutSend`/`newDhsPub` are the classical DH ratchet's own
boundary inputs, threaded straight through as `Model.Ratchet.receive` already
asks for them. -/

def classicalSkippedLength (st : State) : Nat := st.classical.skipped.length

def receiveCount (st : State) : Nat := st.classical.nr

def postQuantumSkippedLength (st : State) : Nat := st.postQuantum.skipped.length

def postQuantumReceiveCount (st : State) (epoch : Nat) : Option Nat := do
  let chains ← Model.SparseRatchet.findChains st.postQuantum epoch
  let receive ← chains.receive
  some receive.n

def evictOldestClassical (st : State) (count : Nat) : State × Nat :=
  let result := Model.Ratchet.evictOldest st.classical count
  ({ st with classical := result.1 }, result.2)

def evictOldestPostQuantum (st : State) (count : Nat) : State × Nat :=
  let result := Model.SparseRatchet.evictOldest st.postQuantum count
  ({ st with postQuantum := result.1 }, result.2)

def receive (st : State) (header : Header) (dhOutRecv dhOutSend newDhsPub : Key)
    (out : Option Model.SparseRatchet.Output) : Option (State × Key) :=
  match Model.Ratchet.receive st.classical header.dr dhOutRecv dhOutSend newDhsPub with
  | none => none
  | some (s, mkEc) =>
    match Model.SparseRatchet.receive st.postQuantum header.epoch out header.pqN with
    | none => none
    | some (s1, mkPq) =>
      some ({ classical := s, postQuantum := s1 }, Model.TripleRatchet.combine mkEc mkPq)

/-- Which contributing ratchet refused a receive, retaining that ratchet's
    exact public reason for the session layer. -/
inductive ReceiveRefusal where
  | classical (reason : Model.Ratchet.ReceiveRefusal)
  | postQuantum (reason : Model.SparseRatchet.ReceiveRefusal)
  deriving Repr, DecidableEq, Inhabited

def receiveDetailed (st : State) (header : Header)
    (dhOutRecv dhOutSend newDhsPub : Key)
    (out : Option Model.SparseRatchet.Output) :
    Except ReceiveRefusal (State × Key) :=
  match Model.Ratchet.receiveDetailed st.classical header.dr
      dhOutRecv dhOutSend newDhsPub with
  | .error reason => .error (.classical reason)
  | .ok (classical, mkEc) =>
      match Model.SparseRatchet.receiveDetailed st.postQuantum
          header.epoch out header.pqN with
      | .error reason => .error (.postQuantum reason)
      | .ok (postQuantum, mkPq) =>
          .ok ({ classical, postQuantum }, Model.TripleRatchet.combine mkEc mkPq)

theorem receiveDetailed_classical_iff (st : State) (header : Header)
    (dhOutRecv dhOutSend newDhsPub : Key)
    (out : Option Model.SparseRatchet.Output)
    (reason : Model.Ratchet.ReceiveRefusal) :
    receiveDetailed st header dhOutRecv dhOutSend newDhsPub out =
        .error (.classical reason) ↔
      Model.Ratchet.receiveDetailed st.classical header.dr
        dhOutRecv dhOutSend newDhsPub = .error reason := by
  cases hc : Model.Ratchet.receiveDetailed st.classical header.dr
      dhOutRecv dhOutSend newDhsPub with
  | error actual => simp [receiveDetailed, hc]
  | ok result =>
      cases hp : Model.SparseRatchet.receiveDetailed st.postQuantum
          header.epoch out header.pqN <;>
        simp [receiveDetailed, hc, hp]

theorem receiveDetailed_post_quantum_iff (st : State) (header : Header)
    (dhOutRecv dhOutSend newDhsPub : Key)
    (out : Option Model.SparseRatchet.Output)
    (reason : Model.SparseRatchet.ReceiveRefusal) :
    receiveDetailed st header dhOutRecv dhOutSend newDhsPub out =
        .error (.postQuantum reason) ↔
      ∃ classical mkEc,
        Model.Ratchet.receiveDetailed st.classical header.dr
          dhOutRecv dhOutSend newDhsPub = .ok (classical, mkEc) ∧
        Model.SparseRatchet.receiveDetailed st.postQuantum
          header.epoch out header.pqN = .error reason := by
  cases hc : Model.Ratchet.receiveDetailed st.classical header.dr
      dhOutRecv dhOutSend newDhsPub with
  | error actual => simp [receiveDetailed, hc]
  | ok result =>
      obtain ⟨classical, mkEc⟩ := result
      cases hp : Model.SparseRatchet.receiveDetailed st.postQuantum
          header.epoch out header.pqN <;>
        simp [receiveDetailed, hc, hp]

theorem receiveDetailed_ok_iff (st : State) (header : Header)
    (dhOutRecv dhOutSend newDhsPub : Key)
    (out : Option Model.SparseRatchet.Output) (result : State × Key) :
    receiveDetailed st header dhOutRecv dhOutSend newDhsPub out = .ok result ↔
      receive st header dhOutRecv dhOutSend newDhsPub out = some result := by
  cases hc : Model.Ratchet.receiveDetailed st.classical header.dr
      dhOutRecv dhOutSend newDhsPub with
  | error reason =>
      have ho : Model.Ratchet.receive st.classical header.dr
          dhOutRecv dhOutSend newDhsPub = none := by
        cases h : Model.Ratchet.receive st.classical header.dr
            dhOutRecv dhOutSend newDhsPub with
        | none => rfl
        | some result =>
            have := (Model.Ratchet.receiveDetailed_ok_iff st.classical header.dr
              dhOutRecv dhOutSend newDhsPub result).2 h
            rw [hc] at this
            contradiction
      simp [receiveDetailed, receive, hc, ho]
  | ok classicalResult =>
      obtain ⟨classical, mkEc⟩ := classicalResult
      have ho := (Model.Ratchet.receiveDetailed_ok_iff st.classical header.dr
        dhOutRecv dhOutSend newDhsPub (classical, mkEc)).1 hc
      cases hp : Model.SparseRatchet.receiveDetailed st.postQuantum
          header.epoch out header.pqN with
      | error reason =>
          have hpo : Model.SparseRatchet.receive st.postQuantum
              header.epoch out header.pqN = none := by
            cases h : Model.SparseRatchet.receive st.postQuantum
                header.epoch out header.pqN with
            | none => rfl
            | some result =>
                have := (Model.SparseRatchet.receiveDetailed_ok_iff st.postQuantum
                  header.epoch out header.pqN result).2 h
                rw [hp] at this
                contradiction
          simp [receiveDetailed, receive, hc, ho, hp, hpo]
      | ok postQuantumResult =>
          obtain ⟨postQuantum, mkPq⟩ := postQuantumResult
          have hpo := (Model.SparseRatchet.receiveDetailed_ok_iff st.postQuantum
            header.epoch out header.pqN (postQuantum, mkPq)).1 hp
          simp [receiveDetailed, receive, hc, ho, hp, hpo]

/-! ## Committing

A bare projection: the caller calls this only once a received message's
authenticator has verified, and there is nothing left to decide by then. -/

def commit (_self next : State) : State := next

end Model.Triple
