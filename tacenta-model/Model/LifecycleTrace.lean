import Model.Lifecycle
import Model.SessionTrace

/-!
# Executable two-party Session schedules

This layer runs the public lifecycle operations over a small network queue. It
does not decide which schedules are valid evidence: the differential runner
supplies actions and primitive-oracle answers. Keeping delivery, loss, replay,
reordering and byte forgery here makes those choices explicit and reusable by
the Phase 1 trace replay and the later Rust differential harness.
-/

namespace Model.LifecycleTrace

open Model.Lifecycle

inductive Side where
  | alice | bob
  deriving Repr, DecidableEq, Inhabited

def Side.other : Side → Side
  | .alice => .bob
  | .bob => .alice

structure Envelope where
  id : Nat
  sender : Side
  bytes : Bytes
  deriving Repr, DecidableEq

structure State where
  alice : Session
  bob : Session
  aliceOracle : Oracle
  bobOracle : Oracle
  queue : List Envelope
  history : List Envelope
  accepted : List (Side × Nat × Bytes)

inductive Action where
  | send (sender : Side) (id : Nat) (plaintext : Bytes)
  | receive (receiver : Side) (id : Nat)
  | drop (id : Nat)
  | replay (id : Nat)
  | reorderFirst (id : Nat)
  | forge (id offset : Nat) (value : UInt8)
  | failAgreement (side : Side)
  deriving Repr, DecidableEq

inductive Outcome where
  | sent (id : Nat) (bytes : Bytes)
  | delivered (id : Nat) (plaintext : Bytes)
  | refused (id : Nat) (reason : Refusal)
  | dropped (id : Nat)
  | replayed (id : Nat)
  | reordered (id : Nat)
  | forged (id : Nat)
  | missing (id : Nat)
  | agreementFailed (side : Side)
  deriving Repr, DecidableEq

/-- Remove the first envelope with `id`, retaining the order of every other
    envelope. This is delivery and drop's network effect. -/
def takeEnvelope (id : Nat) : List Envelope → Option (Envelope × List Envelope)
  | [] => none
  | envelope :: rest =>
      if envelope.id = id then some (envelope, rest)
      else (takeEnvelope id rest).map fun (found, tail) => (found, envelope :: tail)

def findEnvelope (id : Nat) (messages : List Envelope) : Option Envelope :=
  messages.find? (fun envelope => envelope.id = id)

def replaceByte (bytes : Bytes) (offset : Nat) (value : UInt8) : Bytes :=
  if offset < bytes.length then bytes.set offset value else bytes

def forgeEnvelope (id offset : Nat) (value : UInt8) : List Envelope → List Envelope
  | [] => []
  | envelope :: rest =>
      if envelope.id = id then
        { envelope with bytes := replaceByte envelope.bytes offset value } :: rest
      else envelope :: forgeEnvelope id offset value rest

def failSession (session : Session) : Session :=
  { session with braid := .failed }

/-- One scheduled action. A delivery leaves the queue even when decryption
    refuses; replay is an explicit later action from immutable history. -/
def step (view : CodewordView) (state : State) : Action → State × Outcome
  | .send .alice id plaintext =>
      let sent := encrypt view state.aliceOracle state.alice plaintext
      match sent.result with
      | .error reason =>
          ({ state with alice := sent.session, aliceOracle := sent.oracle },
            .refused id reason)
      | .ok bytes =>
          let envelope := { id, sender := .alice, bytes }
          ({ state with
              alice := sent.session
              aliceOracle := sent.oracle
              queue := state.queue ++ [envelope]
              history := state.history ++ [envelope] },
            .sent id bytes)
  | .send .bob id plaintext =>
      let sent := encrypt view state.bobOracle state.bob plaintext
      match sent.result with
      | .error reason =>
          ({ state with bob := sent.session, bobOracle := sent.oracle },
            .refused id reason)
      | .ok bytes =>
          let envelope := { id, sender := .bob, bytes }
          ({ state with
              bob := sent.session
              bobOracle := sent.oracle
              queue := state.queue ++ [envelope]
              history := state.history ++ [envelope] },
            .sent id bytes)
  | .receive .alice id =>
      match takeEnvelope id state.queue with
      | none => (state, .missing id)
      | some (envelope, rest) =>
          let received := decrypt view state.aliceOracle state.alice envelope.bytes
          match received.result with
          | .error reason =>
              ({ state with
                  alice := received.session
                  aliceOracle := received.oracle
                  queue := rest },
                .refused id reason)
          | .ok plaintext =>
              ({ state with
                  alice := received.session
                  aliceOracle := received.oracle
                  queue := rest
                  accepted := state.accepted ++ [(.alice, id, plaintext)] },
                .delivered id plaintext)
  | .receive .bob id =>
      match takeEnvelope id state.queue with
      | none => (state, .missing id)
      | some (envelope, rest) =>
          let received := decrypt view state.bobOracle state.bob envelope.bytes
          match received.result with
          | .error reason =>
              ({ state with
                  bob := received.session
                  bobOracle := received.oracle
                  queue := rest },
                .refused id reason)
          | .ok plaintext =>
              ({ state with
                  bob := received.session
                  bobOracle := received.oracle
                  queue := rest
                  accepted := state.accepted ++ [(.bob, id, plaintext)] },
                .delivered id plaintext)
  | .drop id =>
      match takeEnvelope id state.queue with
      | none => (state, .missing id)
      | some (_, rest) => ({ state with queue := rest }, .dropped id)
  | .replay id =>
      match findEnvelope id state.history with
      | none => (state, .missing id)
      | some envelope =>
          ({ state with queue := state.queue ++ [envelope] }, .replayed id)
  | .reorderFirst id =>
      match takeEnvelope id state.queue with
      | none => (state, .missing id)
      | some (envelope, rest) =>
          ({ state with queue := envelope :: rest }, .reordered id)
  | .forge id offset value =>
      match findEnvelope id state.queue with
      | none => (state, .missing id)
      | some _ =>
          ({ state with queue := forgeEnvelope id offset value state.queue }, .forged id)
  | .failAgreement .alice =>
      ({ state with alice := failSession state.alice }, .agreementFailed .alice)
  | .failAgreement .bob =>
      ({ state with bob := failSession state.bob }, .agreementFailed .bob)

def run (view : CodewordView) : State → List Action → State × List Outcome
  | state, [] => (state, [])
  | state, action :: rest =>
      let (next, outcome) := step view state action
      let (final, outcomes) := run view next rest
      (final, outcome :: outcomes)

/-! ## Executable schedule check -/

open Model.Lifecycle.Examples in
/-- An accepted message is delivered once. Re-inserting its original wire
    bytes and delivering them again produces a refusal and no second accepted
    plaintext. -/
example :
    let start : State :=
      { alice := toyAlice toySecret
        bob := toyBob toySecret
        aliceOracle := toyOracle [toyAgreementDraw]
        bobOracle := toyOracle [List.replicate 32 0x32, List.replicate 32 0x33]
        queue := []
        history := []
        accepted := [] }
    let result := run toyView start
      [.send .alice 1 [0xde, 0xad], .receive .bob 1, .replay 1, .receive .bob 1]
    (match result.2 with
      | [.sent 1 _, .delivered 1 plaintext, .replayed 1, .refused 1 _] =>
          plaintext == [0xde, 0xad]
            && result.1.accepted == [(.bob, 1, [0xde, 0xad])]
      | _ => false) = true := by
  native_decide

open Model.Lifecycle.Examples in
/-- Explicit out-of-order delivery of two honest queued messages accepts each
    plaintext once: the later message stores the skipped classical key and the
    earlier one consumes it. -/
example :
    let start : State :=
      { alice := toyAlice toySecret
        bob := toyBob toySecret
        aliceOracle := toyOracle [toyAgreementDraw]
        bobOracle := toyOracle [List.replicate 32 0x32, List.replicate 32 0x33]
        queue := []
        history := []
        accepted := [] }
    let result := run toyView start
      [.send .alice 1 [0x01], .send .alice 2 [0x02], .reorderFirst 2,
        .receive .bob 2, .receive .bob 1]
    (match result.2 with
      | [.sent 1 _, .sent 2 _, .reordered 2, .delivered 2 second,
          .delivered 1 first] =>
          second == [0x02] && first == [0x01]
            && result.1.accepted == [(.bob, 2, [0x02]), (.bob, 1, [0x01])]
      | _ => false) = true := by
  native_decide

open Model.Lifecycle.Examples in
/-- A forged frame is consumed by the network but cannot change the receiving
    Session or add an accepted plaintext. -/
example :
    let start : State :=
      { alice := toyAlice toySecret
        bob := toyBob toySecret
        aliceOracle := toyOracle [toyAgreementDraw]
        bobOracle := toyOracle [List.replicate 32 0x32]
        queue := []
        history := []
        accepted := [] }
    let result := run toyView start
      [.send .alice 1 [0xde, 0xad], .forge 1 0 0xff, .receive .bob 1]
    (match result.2 with
      | [.sent 1 _, .forged 1, .refused 1 _] =>
          result.1.accepted.isEmpty
      | _ => false) = true := by
  native_decide

open Model.Lifecycle.Examples in
/-- Once terminal failure is present, a later send is refused and the P6
    observation remains failed. -/
example :
    let start : State :=
      { alice := toyAlice toySecret
        bob := toyBob toySecret
        aliceOracle := toyOracle [toyAgreementDraw]
        bobOracle := toyOracle []
        queue := []
        history := []
        accepted := [] }
    let result := run toyView start
      [.failAgreement .alice, .send .alice 1 [0xde, 0xad]]
    result.2 = [.agreementFailed .alice, .refused 1 .agreementFailed]
      ∧ agreementFailed result.1.alice = true := by
  native_decide

/-! ## Projection to the earlier bounded trace

The P6 trace keeps only phase and message labels. This projection makes its
terminal phase a derived observation of the operational Session rather than a
separately declared fact. -/

def phaseOf (session : Session) : Model.SessionTrace.Phase :=
  if agreementFailed session then .failed else .active

def queuedIds (state : State) : List Nat := state.queue.map (·.id)

def acceptedIds (side : Side) (state : State) : List Nat :=
  (state.accepted.filter (fun accepted => accepted.1 = side)).map (fun accepted => accepted.2.1)

def observe (side : Side) (state : State) : Model.SessionTrace.State :=
  { phase := phaseOf (match side with | .alice => state.alice | .bob => state.bob)
    queued := queuedIds state
    accepted := acceptedIds side state }

end Model.LifecycleTrace
