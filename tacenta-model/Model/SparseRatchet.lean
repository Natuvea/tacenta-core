/-
Model.SparseRatchet: the Sparse Post-Quantum Ratchet's state and key schedule,
written from tacenta-spec/protocol/sparse-pq-ratchet.md.

The sparse continuous key agreement is a trusted boundary, exactly as
Diffie-Hellman is for the Double Ratchet: what it produces enters this model as
values rather than being computed here. That keeps the model executable, which
is what makes it an oracle, and it keeps the agreement's own protocol -- a state
machine an order of magnitude larger than this file -- out of the ratchet's
specification, where the published document also keeps it.

What this model does compute, byte for byte, is the part the ratchet itself
contributes: the three derivations, the per-epoch chains, and the state
transitions that decide which chain a message key comes from.
-/
import Model.Kdf
import Model.State

namespace Model.SparseRatchet

open Model.State (Key)

/-! ## The agreement's boundary

Two operations, and this model consumes their results rather than producing
them. Sending yields the epoch the receiver is guaranteed to reach, and
*sometimes* a secret. Receiving yields the epoch the sender was in, and again
sometimes a secret. The opaque message the agreement exchanges is carried in the
header and is not interpreted here. -/

/-- A secret the agreement produced, with the epoch it belongs to. -/
structure Output where
  keyEpoch : Nat
  key      : Key
  deriving Repr, Inhabited, DecidableEq

/-! ## Derivations

Three, all HKDF over the model's own labels. The labels are wire-sensitive and
application-specific in the published document; these keep the model
self-consistent, the same arrangement as the Double Ratchet's. -/

/-- `PROTOCOL_INFO` for this ratchet, with the two suffixes the derivations use.
    "Tacenta SPQR" as bytes. -/
def protocolInfo : List UInt8 :=
  [0x54,0x61,0x63,0x65,0x6e,0x74,0x61,0x20,0x53,0x50,0x51,0x52]

/-- "Chain Start", the suffix the initialisation derivation uses. -/
def chainStart : List UInt8 :=
  [0x43,0x68,0x61,0x69,0x6e,0x20,0x53,0x74,0x61,0x72,0x74]

/-- "Root", the suffix the root step uses. -/
def rootLabel : List UInt8 := [0x52,0x6f,0x6f,0x74]

/-- "Chain", the suffix the chain step uses. -/
def chainLabel : List UInt8 := [0x43,0x68,0x61,0x69,0x6e]

/-- A counter as eight big-endian bytes. The published document recommends
    big-endian for epochs and leaves the chain counter's encoding to the same
    convention, so one encoding serves both and neither is ambiguous. -/
def be64 (n : Nat) : List UInt8 :=
  (List.range 8).map (fun i => UInt8.ofNat (n / (256 ^ (7 - i)) % 256))

/-- Split 96 bytes of derived output into a root key and two chain keys. -/
def split3 (out : List UInt8) : Key × Key × Key :=
  (out.take 32, (out.drop 32).take 32, (out.drop 64).take 32)

/-- `KDF_SCKA_INIT`: from the session's shared secret, a root key and both chain
    keys at once. -/
def kdfInit (sk : Key) : Key × Key × Key :=
  split3 (Model.Kdf.hkdf (List.replicate 32 0) sk (protocolInfo ++ chainStart) 96)

/-- `KDF_SCKA_RK`: fold a secret from the agreement into the root key, yielding
    a new root key and both chain keys. -/
def kdfRk (rk : Key) (k : Key) : Key × Key × Key :=
  split3 (Model.Kdf.hkdf rk k (protocolInfo ++ rootLabel) 96)

/-- `KDF_SCKA_CK`: advance a chain, yielding the next chain key and a message
    key.

    The message number is an input, where the Double Ratchet's chain step uses a
    fixed constant. That binds each message key to its position in the chain,
    and it is the reason this cannot simply reuse `Model.State.kdfCk`. -/
def kdfCk (ck : Key) (n : Nat) : Key × Key :=
  let out := Model.Kdf.hkdf ck (be64 n) (protocolInfo ++ chainLabel) 64
  (out.take 32, (out.drop 32).take 32)

/-! ## State -/

/-- One KDF chain: its key and how many message keys it has produced. -/
structure Chain where
  ck : Key
  n  : Nat
  deriving Repr, Inhabited, DecidableEq

/-- A chain is `none` only in an imported state: retiring an epoch removes its
    whole entry (sparse-pq-ratchet.md, session-persistence.md). -/
structure Chains where
  send    : Option Chain
  receive : Option Chain
  deriving Repr, Inhabited, DecidableEq

/-- Which side of the session a party is on. The two derive identical chain keys
    and must assign them oppositely, so the asymmetry is named rather than left
    implicit in the order of two variables. -/
inductive Direction where
  | a2b
  | b2a
  deriving Repr, Inhabited, DecidableEq

/-- The state (sparse-pq-ratchet.md, State).

    `chains` and `skipped` are association lists rather than maps, for the same
    reason the Double Ratchet's store is: it keeps them in the provable and
    translatable subset. Both are *maps* in the sense that matters, one entry
    per key, and that is a property to maintain rather than a shape to assume.

    `skipped` is flattened to `(epoch, number, key)` rather than nested, which
    is the same information and one fewer level to reason through. -/
structure State where
  rk        : Key
  epoch     : Nat
  chains    : List (Nat × Chains)
  skipped   : List (Nat × Nat × Key)
  direction : Direction
  deriving Repr, Inhabited

/-- How many chains a receiver may skip forward on one chain before the request
    is rejected. Shared with the Double Ratchet: the risk is the same one. -/
def maxSkip : Nat := Model.State.maxSkip

/-- The most skipped keys the store may hold, across every epoch in it.

    The total bound is this implementation's addition: the per-call bound
    (`maxSkip`) and epoch retirement are the specification's, and the total cap
    is added here so the store's size is bounded independently of how many
    messages are skipped within an epoch.

    The Double Ratchet is bounded the same way, with
    `Model.State.maxSkippedStore`; the same bound is used here. -/
def maxSkippedStore : Nat := Model.State.maxSkippedStore

/-- How many epochs' chains are kept. The specification's main text retires
    everything older, skipped keys included, which is what bounds the store
    without a separate policy. -/
def epochsKept : Nat := 2

/-- `u64::MAX`, the ceiling of the epoch and of every chain's counter. The
    epoch is reserved there: an advance onto it is refused. A chain's counter
    reaches it, and the send after that is refused (sparse-pq-ratchet.md,
    Sending; session-persistence.md, Principles). Both refusals are counter
    exhaustion (`ChainExhausted`). -/
def u64Max : Nat := 2 ^ 64 - 1

theorem u64Max_eq : u64Max = 18446744073709551615 := rfl

/-! ## Lookups

Named rather than inlined, because every operation below needs them and because
the refinement of a lookup is where an association list and a map have to be
shown to agree. -/

def findChains (st : State) (e : Nat) : Option Chains :=
  (st.chains.find? (fun p => p.1 == e)).map Prod.snd

def setChains (st : State) (e : Nat) (c : Chains) : State :=
  { st with chains := (st.chains.filter (fun p => !(p.1 == e))) ++ [(e, c)] }

/-! ## Initialisation -/

/-- Both parties derive the same root key and the same pair of chain keys, then
    assign them oppositely. -/
def init (sk : Key) (dir : Direction) : State :=
  let d := kdfInit sk
  let cks := match dir with | .a2b => d.2.1 | .b2a => d.2.2
  let ckr := match dir with | .a2b => d.2.2 | .b2a => d.2.1
  { rk := d.1, epoch := 0,
    chains := [(0, { send := some { ck := cks, n := 0 },
                     receive := some { ck := ckr, n := 0 } })],
    skipped := [], direction := dir }

def initAlice (sk : Key) : State := init sk .a2b
def initBob (sk : Key) : State := init sk .b2a

/-! ## Advancing on a new secret

Shared by sending and receiving: the specification does the same thing on both
sides, and writing it once is what makes that visible. -/

/-- Retire everything older than the epochs kept, chains and skipped keys alike.
    This is what bounds the skipped store, so it is not an optimisation. -/
def clearOldEpochs (st : State) (current : Nat) : State :=
  { st with
    chains := st.chains.filter (fun p => decide (current < p.1 + epochsKept)),
    skipped := st.skipped.filter (fun e => decide (current < e.1 + epochsKept)) }

/-- Fold a new secret into the root key and open a fresh pair of chains under
    its epoch.

    `none` when the epoch is not exactly one past the current one. The
    specification asserts that it is; an assertion in a specification is a
    rejection in an implementation, so it is one here.

    `none` too when the new epoch would be `u64::MAX`, which is reserved: the
    retention window, its sum saturating, reads that epoch as covering nothing
    and would retire the chains just opened. -/
def advance (st : State) (out : Output) : Option State :=
  if out.keyEpoch = st.epoch + 1 ∧ st.epoch + 1 < u64Max then
    let d := kdfRk st.rk out.key
    let cks := match st.direction with | .a2b => d.2.1 | .b2a => d.2.2
    let ckr := match st.direction with | .a2b => d.2.2 | .b2a => d.2.1
    some (clearOldEpochs
      (setChains { st with rk := d.1, epoch := out.keyEpoch } out.keyEpoch
        { send := some { ck := cks, n := 0 },
          receive := some { ck := ckr, n := 0 } })
      out.keyEpoch)
  else
    none

/-! ## Sending -/

/-- Produce the next message key on the sending chain of the epoch the agreement
    named.

    `none` when the agreement's secret does not follow the current epoch, or
    when there is no sending chain for that epoch, which happens if it has been
    retired, and when the chain's counter is already `u64::MAX`: message
    number `u64::MAX` is usable and the send after it is refused. -/
def send (st : State) (sendingEpoch : Nat) (out : Option Output) :
    Option (State × Nat × Key) :=
  match (match out with | none => some st | some o => advance st o) with
  | none => none
  | some st1 =>
    match findChains st1 sendingEpoch with
    | none => none
    | some cs =>
      match cs.send with
      | none => none
      | some ch =>
        if ch.n < u64Max then
          let stepped := kdfCk ch.ck (ch.n + 1)
          some (setChains st1 sendingEpoch
                  { cs with send := some { ck := stepped.1, n := ch.n + 1 } },
                ch.n + 1, stepped.2)
        else
          none

/-- An advance leaves the epoch below `u64::MAX`. -/
theorem advance_epoch_lt (st : State) (out : Output) (st' : State)
    (h : advance st out = some st') : st'.epoch < u64Max := by
  unfold advance at h
  split at h
  · rename_i hc
    injection h with h
    subst h
    simp only [clearOldEpochs, setChains]
    omega
  · simp at h

/-- A send's message number, which is the chain's new counter, is at most
    `u64::MAX`. -/
theorem send_number_le (st : State) (e : Nat) (out : Option Output)
    (r : State × Nat × Key) (h : send st e out = some r) : r.2.1 ≤ u64Max := by
  unfold send at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq] at h; subst h; simp only; omega)
    | simp at h

/-! ## Receiving -/

/-- Take a stored key for this epoch and number, removing it. Removing it is
    what makes a stored key one-use. -/
def trySkipped (st : State) (e n : Nat) : Option (State × Key) :=
  match st.skipped.find? (fun x => x.1 == e && x.2.1 == n) with
  | none => none
  | some x =>
    some ({ st with skipped := st.skipped.filter (fun y => !(y.1 == e && y.2.1 == n)) },
          x.2.2)

/-- Step the receiving chain forward to `upto`, storing every key passed.

    `none` when the request exceeds `maxSkip`, or when the chain has been
    retired. Storing replaces rather than accumulates, for the same reason the
    Double Ratchet's does: the store is a map on `(epoch, number)` and a peer
    must not be able to make one pair hold two keys. -/
def skipMessageKeys (st : State) (e : Nat) (upto : Nat) : Option State :=
  match findChains st e with
  | none => none
  | some cs =>
    match cs.receive with
    | none => none
    | some ch =>
      if upto ≤ ch.n then
        some st
      else if upto > ch.n + maxSkip then
        none
      else if st.skipped.length + (upto - ch.n) > maxSkippedStore then
        none
      else
        let res := deriveInto ch.ck ch.n (upto - ch.n)
        some (setChains
          { st with
            skipped := (st.skipped.filter
                          (fun x => !(x.1 == e && decide (ch.n < x.2.1)
                                      && decide (x.2.1 ≤ upto))))
                      ++ res.2.map (fun p => (e, p.1, p.2)) }
          e { cs with receive := some { ck := res.1, n := upto } })
where
  /-- Advance a chain `count` times from number `start`, returning the chain key
      reached and each `(number, message key)` passed. Numbers run from
      `start + 1`, because this chain step is keyed by the number it produces. -/
  deriveInto (ck : Key) (start count : Nat) : Key × List (Nat × Key) :=
    match count with
    | 0 => (ck, [])
    | c + 1 =>
      let stepped := kdfCk ck (start + 1)
      let rest := deriveInto stepped.1 (start + 1) c
      (rest.1, (start + 1, stepped.2) :: rest.2)

/-- Produce the message key for a received message.

    A stored key is tried first; only if there is none does the chain advance,
    and advancing stores every key it passes so that an out-of-order message can
    still be read later. -/
def receive (st : State) (receivingEpoch : Nat) (out : Option Output) (n : Nat) :
    Option (State × Key) :=
  match (match out with | none => some st | some o => advance st o) with
  | none => none
  | some st1 =>
    match trySkipped st1 receivingEpoch n with
    | some res => some res
    | none =>
      match skipMessageKeys st1 receivingEpoch (n - 1) with
      | none => none
      | some st2 =>
        match findChains st2 receivingEpoch with
        | none => none
        | some cs =>
          match cs.receive with
          | none => none
          | some ch =>
            if n = ch.n + 1 then
              let stepped := kdfCk ch.ck n
              some (setChains st2 receivingEpoch
                      { cs with receive := some { ck := stepped.1, n := n } },
                    stepped.2)
            else
              none

/-! ## Self-consistency checks

Fixed byte strings stand in for the shared secret and the agreement's outputs.
These elaborate at build time, so a wrong transition fails the build rather than
a test run. -/

private def sk : Key := List.replicate 32 0x01

/-- In order: the key Alice derives to send is the key Bob derives to receive.

    This is the check that the two sides assign the derived chain keys
    oppositely. If both used the same one, every derivation would still agree
    and this would be `false`. -/
example :
    (do
      let (_, n, mkSend) ← send (initAlice sk) 0 none
      let (_, mkRecv) ← receive (initBob sk) 0 none n
      pure (mkSend == mkRecv)) = some true := by
  native_decide

/-- Out of order: Alice sends two, Bob takes the second first and the first from
    the store afterwards. Both keys match what Alice produced. -/
example :
    (do
      let (a1, n1, mk1) ← send (initAlice sk) 0 none
      let (_, n2, mk2) ← send a1 0 none
      let (b1, r2) ← receive (initBob sk) 0 none n2
      let (_, r1) ← receive b1 0 none n1
      pure (mk1 == r1 && mk2 == r2)) = some true := by
  native_decide

private def secret1 : Output := { keyEpoch := 1, key := List.replicate 32 0xa1 }

/-- A new epoch: both sides fold the same secret in and still agree. -/
example :
    (do
      let (_, n, mkSend) ← send (initAlice sk) 1 (some secret1)
      let (_, mkRecv) ← receive (initBob sk) 1 (some secret1) n
      pure (mkSend == mkRecv)) = some true := by
  native_decide

/-- An epoch that does not follow the current one is rejected rather than
    accommodated, which is what the specification's assertion means here. -/
example : advance (initAlice sk) { keyEpoch := 2, key := List.replicate 32 0xff }
    = none := by
  native_decide

/-- Advancing keeps the new epoch's chains and drops what has aged out. With two
    epochs kept, epoch zero survives the step to epoch one. -/
example :
    (advance (initAlice sk) secret1).map (fun st => st.chains.length) = some 2 := by
  native_decide

private def secret2 : Output := { keyEpoch := 2, key := List.replicate 32 0xa2 }

/-- Stepping again drops epoch zero: the table does not grow with the session. -/
example :
    (do
      let s1 ← advance (initAlice sk) secret1
      let s2 ← advance s1 secret2
      pure (s2.chains.length, s2.chains.any (fun p => p.1 == 0)))
    = some (2, false) := by
  native_decide

/-- Retiring an epoch takes its stored keys with it. Bob skips two keys in epoch
    zero, then two epochs pass; the store is empty rather than holding keys for a
    chain that no longer exists. -/
example :
    (do
      let (b1, _) ← receive (initBob sk) 0 none 3
      let s1 ← advance b1 secret1
      let s2 ← advance s1 secret2
      pure (b1.skipped.length, s2.skipped.length)) = some (2, 0) := by
  native_decide

/-- A skipped key is one-use: taking it removes it, so the same number cannot be
    served twice. -/
example :
    (do
      let (b1, _) ← receive (initBob sk) 0 none 3
      let (b2, _) ← trySkipped b1 0 1
      pure (b1.skipped.length, b2.skipped.length, (trySkipped b2 0 1).isSome))
    = some (2, 1, false) := by
  native_decide

/-- Skipping beyond the per-call bound is rejected. -/
example : skipMessageKeys (initBob sk) 0 (maxSkip + 1) = none := by
  native_decide

/-- And so is a request that would push the store past its total bound, which
    is this model's own addition. Each of these calls is inside
    `maxSkip`; it is their accumulation the total bound catches. -/
example :
    (do
      let b1 ← skipMessageKeys (initBob sk) 0 900
      let b2 ← skipMessageKeys b1 0 1800
      pure (b2.skipped.length, (skipMessageKeys b2 0 2700).isSome))
    = some (1800, false) := by
  native_decide

/-- The ceilings: from epoch `u64::MAX - 2` the advance to `u64::MAX - 1` is
    taken and the one to `u64::MAX` refused; a chain at `u64::MAX - 1` sends
    message `u64::MAX`, and the send after it is refused. -/
example :
    let hi : State := { initAlice sk with epoch := u64Max - 2,
                                          chains := [(u64Max - 2, (initAlice sk).chains.head!.2)] }
    let full : State := { initAlice sk with
      chains := [(0, { send := some { ck := sk, n := u64Max - 1 }, receive := none })] }
    ((advance hi { keyEpoch := u64Max - 1, key := sk }).map (·.epoch) = some (u64Max - 1))
      ∧ ((advance hi { keyEpoch := u64Max - 1, key := sk }).bind
          (fun s => advance s { keyEpoch := u64Max, key := sk })).isNone
      ∧ ((send full 0 none).map (·.2.1) = some u64Max)
      ∧ ((send full 0 none).bind (fun r => send r.1 0 none)).isNone := by
  native_decide

end Model.SparseRatchet
