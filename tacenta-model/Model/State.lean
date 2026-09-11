/-
Model.State: the Double Ratchet state and its key-schedule derivations, written
from tacenta-spec/protocol/ratchet.md. Diffie-Hellman agreement and the AEAD are
trusted-boundary primitives: the model consumes DH outputs as bytes and derives
message keys the AEAD would then use, so the model is a byte-exact oracle for the
ratchet's key schedule and state transitions, which is the ratchet's own
contribution. Concrete ciphertext bytes are out of the model by design (see
docs/abstraction-boundary.md).
-/
import Model.Kdf

namespace Model.State

/-- A protocol key or key-shaped byte string (32 bytes for chain, root, and
    message keys; the ratchet public key is an opaque identifier here since the
    curve is a boundary primitive). -/
abbrev Key := List UInt8

/-- A message header: the sender's current ratchet public key, the length of the
    previous sending chain, and the message number in the current chain. -/
structure Header where
  dh : Key
  pn : Nat
  n  : Nat
  deriving Repr, Inhabited

/-- Which set of `info` labels a session derives under. The labels are a choice
    rather than a computation, so the choice is named, carried in the state, and
    persisted with it: adding a second set later must not require reissuing
    sessions established before it. One set exists today. -/
inductive LabelSet where
  | tacenta
  deriving Repr, Inhabited, DecidableEq

/-- The ratchet state of one party (ratchet.md, State). `skipped` maps
    `(ratchet public key, message number)` to a stored message key, kept as an
    association list rather than a hash map so it stays in the translatable,
    provable subset. -/
structure State where
  dhsPub  : Key
  dhrPub  : Option Key
  rk      : Key
  cks     : Option Key
  ckr     : Option Key
  ns      : Nat
  nr      : Nat
  pn      : Nat
  /-- Skipped message keys, as a map from a ratchet public key and message
      number to the key, carrying the value of `events` when it was stored so
      that it can be expired. -/
  skipped : List (Key × Nat × Nat × Key)
  /-- Received messages counted since the session began. The store's clock:
      nothing inside the ratchet can read a wall clock, so the interval after
      which a skipped key is deleted is measured in received messages. -/
  events  : Nat
  labels  : LabelSet
  deriving Repr, Inhabited

/-- The derivation `info` labels. The published Double Ratchet specification
    leaves these application-specific. The wire values are recorded in
    `tacenta-spec/CONSTANTS.md`. These model labels make
    the model self-consistent, so its vectors are internally valid and the core
    is checked against them; wire interoperability is a separate, manifest-pinned
    concern. -/
def rkInfo : List UInt8 := [0x54,0x61,0x63,0x65,0x6e,0x74,0x61,0x20,0x52,0x4b]  -- "Tacenta RK"
def mkInfo : List UInt8 := [0x54,0x61,0x63,0x65,0x6e,0x74,0x61,0x20,0x4d,0x4b]  -- "Tacenta MK"

def LabelSet.rkInfo : LabelSet → List UInt8
  | .tacenta => Model.State.rkInfo

def LabelSet.mkInfo : LabelSet → List UInt8
  | .tacenta => Model.State.mkInfo

/-- The most keys that may be skipped in a single chain (ratchet.md, Skipped
    keys). -/
def maxSkip : Nat := 1000

/-- The most keys the skipped store may hold in total. A per-chain bound alone
    does not bound the store, since every Diffie-Hellman ratchet step starts a
    fresh chain; the specification requires the store itself to reject when too
    many elements are held. -/
def maxSkippedStore : Nat := 2000

/-- How many received messages a skipped key may outlive before it is deleted.

The published Double Ratchet specification names two risks in storing keys for
messages that have not arrived: a malicious sender inducing a recipient to store
many of them, and an attacker who records the messages and later compromises the
recipient. `maxSkippedStore` meets the first. This meets the second, which the
bound alone does not: without it a key for a message that never arrives is held
for the life of the session.

It is a policy choice, not something the specification fixes, and it is a
trade-off in both directions. Too small and a legitimate message delayed behind
many others cannot be decrypted. Too large and keys sit recoverable for longer
than they need to. It is also worth being plain that a peer who can drive
receives can age a store out deliberately; that peer can already fill it, and
the alternative is keys that never expire at all. -/
def maxSkippedAge : Nat := 1000

/-- `u32::MAX`, the ceiling of the ratchet's 32-bit counters. A send at
    `ns = u32Max` and a receive that would step past `nr = u32Max` are refused
    (ratchet.md, Sending and receiving: `ChainExhausted`), so message number
    `u32::MAX` is never used on a chain. -/
def u32Max : Nat := 2 ^ 32 - 1

/-- Where the received-message clock stops: `u32::MAX - 1`. `u32::MAX` is
    reserved, a value no operation gives the clock, which is what lets a stored
    state's reader refuse it (ratchet.md, Skipped keys; session-persistence.md,
    Principles). -/
def maxEvents : Nat := u32Max - 1

theorem u32Max_eq : u32Max = 4294967295 := rfl
theorem maxEvents_eq : maxEvents = 4294967294 := rfl

/-- KDF_CK (ratchet.md): advance a chain key one step, yielding
    (next chain key, message key). `HMAC(ck, 0x01)` is the message key and
    `HMAC(ck, 0x02)` the next chain key. -/
def kdfCk (ck : Key) : Key × Key :=
  let mk := Model.Kdf.hmac ck [0x01]
  let ck' := Model.Kdf.hmac ck [0x02]
  (ck', mk)

/-- KDF_RK (ratchet.md): fold a DH output into the root key with HKDF-SHA256,
    yielding (new root key, new chain key) from the 64-byte output. -/
def kdfRk (rk dhOut : Key) (labels : LabelSet) : Key × Key :=
  let out := Model.Kdf.hkdf rk dhOut labels.rkInfo 64
  (out.take 32, out.drop 32)

/-- Message-key expansion (ratchet.md): derive the AEAD material (AES-256 key,
    HMAC key, 16-byte IV) from a message key. The AEAD is a trusted-boundary
    primitive; this HKDF expansion is the pure part the model computes. -/
def messageKeys (mk : Key) (labels : LabelSet) : Key × Key × Key :=
  let out := Model.Kdf.hkdf (List.replicate 32 0) mk labels.mkInfo 80
  (out.take 32, (out.drop 32).take 32, out.drop 64)

/-- Advance a chain `count` steps from message number `startN`, returning the
    final chain key and each `(message number, message key)` produced. Structural
    recursion on `count`, so it terminates. -/
def deriveChain (ck : Key) (startN : Nat) : Nat → Key × List (Nat × Key)
  | 0 => (ck, [])
  | count + 1 =>
    let (ck', mk) := kdfCk ck
    let (ckFinal, rest) := deriveChain ck' (startN + 1) count
    (ckFinal, (startN, mk) :: rest)

/-- Store skipped message keys on the current receiving chain up to (but not
    including) `upto` (ratchet.md, Skipped keys). Returns `none` when the request
    would exceed `maxSkip` on this chain, or would push the store past
    `maxSkippedStore` in total, so a malicious header cannot exhaust memory. -/
def skipMessageKeys (st : State) (upto : Nat) : Option State :=
  match st.ckr, st.dhrPub with
  | some ck, some dhr =>
    if upto ≤ st.nr then
      some st
    else if upto > st.nr + maxSkip then
      none
    else if st.skipped.length + (upto - st.nr) > maxSkippedStore then
      none
    else
      -- Bound with projections rather than a destructuring `let`, so the
      -- stored list stays visibly `(deriveChain ...).2` for the proofs.
      let res := deriveChain ck st.nr (upto - st.nr)
      -- The store maps a ratchet key and message number to a key, so storing
      -- replaces rather than accumulates. It matters because the peer chooses
      -- the ratchet key and may return to one it left, which starts a fresh
      -- chain numbered from zero under a key already stored; without this the
      -- pair would hold two entries with different keys and the second could
      -- never be found (Properties.Invariants).
      let kept := st.skipped.filter fun e =>
        !(e.1 == dhr && decide (st.nr ≤ e.2.1) && decide (e.2.1 < upto))
      let stored := res.2.map (fun x => (dhr, x.1, st.events, x.2))
      some { st with ckr := some res.1, nr := upto, skipped := kept ++ stored }
  | _, _ => some st

/-- Count one received message and delete the skipped keys that have outlived
    `maxSkippedAge` (ratchet.md, Skipped keys; key-deletion.md).

    Applied once per accepted receive, at the end, so a key stored during that
    same receive is one message old rather than zero.

    The count stops at `maxEvents`, `u32::MAX - 1`: from there a receive leaves
    it where it is, and a key's age, measured against it, no longer grows. -/
def ageStore (st : State) : State :=
  let now := min (st.events + 1) maxEvents
  { st with
    events := now,
    skipped := st.skipped.filter fun e => decide (now - e.2.2.1 < maxSkippedAge) }

/-- Below its stop the clock counts one. -/
theorem ageStore_events_of_room (st : State) (h : st.events + 1 < u32Max) :
    (ageStore st).events = st.events + 1 :=
  Nat.min_eq_left (by unfold maxEvents; omega)

/-- At or past its stop the clock stays at `maxEvents`. -/
theorem ageStore_events_at_stop (st : State) (h : maxEvents ≤ st.events + 1) :
    (ageStore st).events = maxEvents :=
  Nat.min_eq_right h

/-- The clock never reaches `u32::MAX`, whatever it held before. -/
theorem ageStore_events_lt (st : State) : (ageStore st).events < u32Max :=
  Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)

/-- Storing skipped keys does not touch the store's clock. Needed where a later
step has to know the counter still has room: nothing between the two moves it,
but the proof cannot see that through a `match`. -/
theorem skipMessageKeys_events (st : State) (upto : Nat) (st' : State)
    (h : skipMessageKeys st upto = some st') : st'.events = st.events := by
  unfold skipMessageKeys at h
  split at h
  · split at h
    · injection h with h'; subst h'; rfl
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · injection h with h'; subst h'; rfl
  · injection h with h'; subst h'; rfl

end Model.State
