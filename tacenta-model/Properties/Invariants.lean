/-
Properties.Invariants: state invariants.

Records the skipped-key store's representation invariant and the sequence that
breaks it in a store that accumulates rather than replaces. Both the model's
skipped-key lookup and the Rust core's rely on the store being a map, and the
sequence below is the one under which an accumulating store holds two entries
for one pair with different keys. It is kept as a regression test, because
nothing about the peer's behaviour in it is prevented and nothing else stops
the property being lost.
-/
import Model.Ratchet

namespace Properties.Invariants

open Model.State Model.Ratchet

/-- The skipped-key store holds at most one entry for a given ratchet public key
and message number.

`Model.State.State` documents `skipped` as *mapping* that pair to a message key,
keeping an association list only to stay in the provable subset, and ratchet.md
says a matching stored key is used and removed, singular. Both lookups depend on
it: `Model.Ratchet.trySkipped` deletes by filtering every match, the Rust core
removes the first match it scans to, and those are the same operation exactly
when this holds. -/
def storeIsMap (st : State) : Bool :=
  st.skipped.all fun e =>
    (st.skipped.filter fun f => f.1 == e.1 && f.2.1 == e.2.1).length == 1

/-! ## The sequence that breaks an accumulating store

A ratchet public key is carried in the header, so the peer chooses it, and
`receive` takes a Diffie-Hellman step whenever it differs from the one held.
Nothing requires it to be a key not seen before. A peer that leaves a key and
comes back to it gets a fresh chain under a ratchet key already in the store,
numbered from zero again, so the second batch lands on pairs the first already
occupies. Storing replaces those rather than appending beside them. -/

private def sk : Key := List.replicate 32 0x01
private def bPub : Key := List.replicate 32 0x0b
private def a1 : Key := List.replicate 32 0xa1
private def a2 : Key := List.replicate 32 0xa2
private def d1 : Key := List.replicate 32 0xd1
private def d2 : Key := List.replicate 32 0xd2
private def d3 : Key := List.replicate 32 0xd3

/-- A receiver taking three messages from a peer that returns to a ratchet key
it had left. Every step is accepted by `receive`. -/
def revisitingPeer : Option State := do
  let b0 := initReceiver sk bPub .tacenta
  let (b1, _) ← receive b0 { dh := a1, pn := 0, n := 2 } d1 d2 bPub
  let (b2, _) ← receive b1 { dh := a2, pn := 5, n := 0 } d2 d3 bPub
  let (b3, _) ← receive b2 { dh := a1, pn := 0, n := 2 } d1 d2 bPub
  pure b3

/-- The sequence is accepted and the store it leaves is a map; accumulating
would leave six entries over four pairs. -/
example : revisitingPeer.map storeIsMap = some true := by native_decide

/-- Four entries, one per pair, rather than the six that accumulating would
give. -/
example : revisitingPeer.map (fun st => st.skipped.length) = some 4 := by
  native_decide

/-- The pair the two chains collide on holds exactly one key. An accumulating
store would hold two with different values, and since both lookups return the
first match, the second would be unreachable: never found, never deleted,
holding a slot against `maxSkippedStore`, while a genuine later message on
that chain is answered with the wrong key. -/
example :
    revisitingPeer.map (fun st =>
      (st.skipped.filter fun e => e.2.1 == 0).length) = some 1 := by
  native_decide

/-! ## Expiry deletes, and deletes only what has expired

`maxSkippedStore` bounds how many skipped keys are held; it does nothing about
how long one is held. Without expiry, a key for a message that never arrives
sits in the store for the life of the session. `ageStore` is what deletes it,
and these pin
the boundary rather than merely that something is removed: one message short of
the cap the key is still there, and at the cap it is gone. -/

private def mkHeld : Key := List.replicate 32 0xe1
private def dhHeld : Key := List.replicate 32 0xd1

/-- A store holding one key, stored at event zero, with `events` set to `now`. -/
private def held (now : Nat) : State :=
  { initReceiver sk bPub .tacenta with
      skipped := [(dhHeld, 7, 0, mkHeld)], events := now }

/-- One received message short of the cap, the key survives. -/
example : (ageStore (held (maxSkippedAge - 2))).skipped.length = 1 := by native_decide

/-- At the cap it is deleted. -/
example : (ageStore (held (maxSkippedAge - 1))).skipped.length = 0 := by native_decide

/-- Ageing counts the message, whether or not anything expired. -/
example : (ageStore (held 41)).events = 42 := by native_decide

end Properties.Invariants
