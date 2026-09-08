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
call fails. Neither reports *which* side failed -- the real `TripleError`
tags it, but nothing downstream of this model needs to distinguish a
classical failure from a post-quantum one, the same way `Model.Ratchet.send`/
`Model.SparseRatchet.send` themselves collapse every failure mode to `none`.

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

/-! ## Receiving

Non-mutating: a candidate state and the key, mirroring the real `&self`-only
method. `dhOutRecv`/`dhOutSend`/`newDhsPub` are the classical DH ratchet's own
boundary inputs, threaded straight through as `Model.Ratchet.receive` already
asks for them. -/

def receive (st : State) (header : Header) (dhOutRecv dhOutSend newDhsPub : Key)
    (out : Option Model.SparseRatchet.Output) : Option (State × Key) :=
  match Model.Ratchet.receive st.classical header.dr dhOutRecv dhOutSend newDhsPub with
  | none => none
  | some (s, mkEc) =>
    match Model.SparseRatchet.receive st.postQuantum header.epoch out header.pqN with
    | none => none
    | some (s1, mkPq) =>
      some ({ classical := s, postQuantum := s1 }, Model.TripleRatchet.combine mkEc mkPq)

/-! ## Committing

A bare projection: the caller calls this only once a received message's
authenticator has verified, and there is nothing left to decide by then. -/

def commit (_self next : State) : State := next

end Model.Triple
