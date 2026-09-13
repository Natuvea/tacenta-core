import Model.PersistedState

/-!
# Prekey-store operation checks

P6 models session/prekey orchestration at the operation boundary. The concrete
Rust code still performs signatures, KEM key generation and curve arithmetic;
this file checks the structural before/after facts that the Lean model can
state over persisted prekey-store states.
-/

namespace Model
namespace PrekeyOperations

open PersistedState
open PersistedState.PrekeyStoreState

/-- The id sequence `replenish` assigns to the new curve one-time prekeys. -/
def curveIds (next count : Nat) : List Nat :=
  List.range count |>.map (fun i => next + i)

/-- The id sequence `replenish` assigns to the new KEM one-time prekeys. -/
def kemIds (next count : Nat) : List Nat :=
  List.range count |>.map (fun i => next + count + i)

/-- All fields except the two one-time pools and `nextId` are unchanged by
    successful replenishment. The generated secrets and signatures are opaque;
    their lengths and global identifier invariants are checked by `invariant`. -/
def replenishOk (before after : Store) (count : Nat) : Bool :=
  let newCurve := after.oneTime.drop before.oneTime.length
  let newKem := after.kemOneTime.drop before.kemOneTime.length
  before.identityPublic == after.identityPublic
    && before.signedPrekeySecret == after.signedPrekeySecret
    && before.signedPrekeyId == after.signedPrekeyId
    && before.signedPrekeySig == after.signedPrekeySig
    && before.oneTime == after.oneTime.take before.oneTime.length
    && before.kemPair == after.kemPair
    && before.kemId == after.kemId
    && before.kemSig == after.kemSig
    && before.kemOneTime == after.kemOneTime.take before.kemOneTime.length
    && before.seen == after.seen
    && before.previousSigned == after.previousSigned
    && before.previousKem == after.previousKem
    && after.nextId == before.nextId + 2 * count
    && newCurve.length == count
    && newKem.length == count
    && newCurve.map Prod.fst == curveIds before.nextId count
    && newKem.map (fun e => e.1) == kemIds before.nextId count
    && invariant before
    && invariant after

/-- A refused replenishment is a no-op at the persisted-state boundary. -/
def noOpOk (before after : Store) : Bool :=
  before == after && invariant before

/-- Successful authenticated responder establishment using one-time curve and KEM
    prekeys deletes exactly the named one-time entries after authentication. The
    session output and plaintext are outside this store-only structural check. -/
def consumeOneTimeOk (before after : Store) (curveId kemId : Nat) : Bool :=
  before.identityPublic == after.identityPublic
    && before.signedPrekeySecret == after.signedPrekeySecret
    && before.signedPrekeyId == after.signedPrekeyId
    && before.signedPrekeySig == after.signedPrekeySig
    && after.oneTime == before.oneTime.filter (fun e => !(e.1 == curveId))
    && before.kemPair == after.kemPair
    && before.kemId == after.kemId
    && before.kemSig == after.kemSig
    && after.kemOneTime == before.kemOneTime.filter (fun e => !(e.1 == kemId))
    && before.nextId == after.nextId
    && before.seen == after.seen
    && before.previousSigned == after.previousSigned
    && before.previousKem == after.previousKem
    && before.oneTime.any (fun e => e.1 == curveId)
    && before.kemOneTime.any (fun e => e.1 == kemId)
    && invariant before
    && invariant after

/-- Successful authenticated responder establishment on the last-resort path
    leaves key material unchanged and appends one replay fingerprint tagged with
    the live last-resort key id. The fingerprint is computed by Rust over the
    decoded initial message; the model checks the durable shape and tag. -/
def recordLastResortOk (before after : Store) : Bool :=
  before.identityPublic == after.identityPublic
    && before.signedPrekeySecret == after.signedPrekeySecret
    && before.signedPrekeyId == after.signedPrekeyId
    && before.signedPrekeySig == after.signedPrekeySig
    && before.oneTime == after.oneTime
    && before.kemPair == after.kemPair
    && before.kemId == after.kemId
    && before.kemSig == after.kemSig
    && before.kemOneTime == after.kemOneTime
    && before.nextId == after.nextId
    && before.previousSigned == after.previousSigned
    && before.previousKem == after.previousKem
    && after.seen.take before.seen.length == before.seen
    && after.seen.length == before.seen.length + 1
    && (after.seen.drop before.seen.length).all (fun e => e.1 == before.kemId && e.2.length == 32)
    && invariant before
    && invariant after

/-- Successful signed-prekey rotation: the current signed prekey is retained as
    the one previous key, a fresh opaque prekey/signature pair is installed under
    the old `nextId`, and unrelated state is unchanged. -/
def rotateSignedOk (before after : Store) : Bool :=
  before.identityPublic == after.identityPublic
    && after.previousSigned == some (before.signedPrekeySecret, before.signedPrekeyId, before.signedPrekeySig)
    && before.oneTime == after.oneTime
    && before.kemPair == after.kemPair
    && before.kemId == after.kemId
    && before.kemSig == after.kemSig
    && before.kemOneTime == after.kemOneTime
    && before.seen == after.seen
    && before.previousKem == after.previousKem
    && after.signedPrekeyId == before.nextId
    && after.nextId == before.nextId + 1
    && after.signedPrekeySecret.length == 32
    && after.signedPrekeySig.length == 64
    && invariant before
    && invariant after

/-- The replay-record entries kept by `rotate_kem`: entries tagged with the key
    that was already previous are dropped because that key is wiped. -/
def seenAfterKemRotation (before : Store) : List (Nat × Bytes) :=
  match before.previousKem with
  | none => before.seen
  | some p => before.seen.filter (fun e => !(e.1 == p.2.1))

/-- Successful last-resort KEM rotation: the current key becomes the retained
    previous key, the older previous key's replay records are dropped, and a
    fresh opaque KEM key/signature pair is installed under the old `nextId`. -/
def rotateKemOk (before after : Store) : Bool :=
  before.identityPublic == after.identityPublic
    && before.signedPrekeySecret == after.signedPrekeySecret
    && before.signedPrekeyId == after.signedPrekeyId
    && before.signedPrekeySig == after.signedPrekeySig
    && before.oneTime == after.oneTime
    && after.previousKem == some (before.kemPair, before.kemId, before.kemSig)
    && before.kemOneTime == after.kemOneTime
    && after.seen == seenAfterKemRotation before
    && before.previousSigned == after.previousSigned
    && after.kemId == before.nextId
    && after.nextId == before.nextId + 1
    && after.kemPair.length == kemPairLen
    && after.kemSig.length == 64
    && invariant before
    && invariant after

/-- Operations the difftest executable can check from concrete before/after
    store bytes. -/
inductive Op where
  | noOp
  | publish
  | replenish (count : Nat)
  | rotateSigned
  | rotateKem
  | consumeOneTime (curveId kemId : Nat)
  | recordLastResort
  deriving Repr, DecidableEq

def check (op : Op) (before after : Store) : Bool :=
  match op with
  | .noOp => noOpOk before after
  | .publish => noOpOk before after
  | .replenish count => replenishOk before after count
  | .rotateSigned => rotateSignedOk before after
  | .rotateKem => rotateKemOk before after
  | .consumeOneTime curveId kemId => consumeOneTimeOk before after curveId kemId
  | .recordLastResort => recordLastResortOk before after

end PrekeyOperations
end Model
