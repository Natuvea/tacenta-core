/-
Model.Ratchet: the Double Ratchet send and receive procedures, written from
tacenta-spec/protocol/ratchet.md. Diffie-Hellman outputs and the fresh sending
public key are supplied by the caller (the DH boundary): a step that reseeds a
chain takes the byte string `DH(priv, peer_pub)` as an argument rather than
computing the curve, and DH's own agreement is checked by the X25519 vectors.
The self-consistency checks at the bottom exploit DH symmetry
(`DH(a, B) = DH(b, A)`) by supplying the same shared output to both parties, and
elaborate at build time.
-/
import Model.State

namespace Model.Ratchet

open Model.State

/-- Initialise the party that sends first (ratchet.md; the sender already holds
    the peer's initial ratchet public key). `sk` is the shared root key from
    session establishment and `dhOut = DH(ourInitialPriv, peerPub)`. -/
def initSender (sk ourPub peerPub dhOut : Key) (labels : LabelSet) : State :=
  let (rk, cks) := kdfRk sk dhOut labels
  { dhsPub := ourPub, dhrPub := some peerPub, rk := rk,
    cks := some cks, ckr := none, ns := 0, nr := 0, pn := 0, skipped := [], events := 0,
    labels := labels }

/-- Initialise the party that receives first: it holds its own ratchet keypair
    but has not seen the peer's ratchet key, so it has the root key and no chains
    until the first message arrives. -/
def initReceiver (sk ourPub : Key) (labels : LabelSet) : State :=
  { dhsPub := ourPub, dhrPub := none, rk := sk,
    cks := none, ckr := none, ns := 0, nr := 0, pn := 0, skipped := [], events := 0,
    labels := labels }

/-- Send (ratchet.md): advance the sending chain and produce the header and the
    message key. `none` when there is no sending chain yet, and when `ns` is
    `u32::MAX` (`ChainExhausted`): the counter is 32 bits and message number
    `u32::MAX` is never used. -/
def send (st : State) : Option (State × Header × Key) :=
  match st.cks with
  | none => none
  | some ck =>
    if st.ns < u32Max then
      let (ck', mk) := kdfCk ck
      let header : Header := { dh := st.dhsPub, pn := st.pn, n := st.ns }
      some ({ st with cks := some ck', ns := st.ns + 1 }, header, mk)
    else
      none

/-- A Diffie-Hellman ratchet step (ratchet.md). `dhOutRecv = DH(DHs.priv,
    header.dh)` seeds the new receiving chain; `dhOutSend = DH(newDhs.priv,
    header.dh)` seeds the new sending chain under the fresh public key
    `newDhsPub`. Skipping on the prior receiving chain happens before this. -/
def dhRatchet (st : State) (header : Header) (dhOutRecv dhOutSend newDhsPub : Key) : State :=
  let (rk1, ckr') := kdfRk st.rk dhOutRecv st.labels
  let (rk2, cks') := kdfRk rk1 dhOutSend st.labels
  { st with
    pn := st.ns, ns := 0, nr := 0,
    dhrPub := some header.dh,
    rk := rk2, ckr := some ckr', cks := some cks', dhsPub := newDhsPub }

/-- Look for a stored skipped key matching the header and, if found, remove and
    return it (ratchet.md, Receive: use a stored skipped key). -/
def trySkipped (st : State) (header : Header) : Option (State × Key) :=
  match st.skipped.find? (fun (dh, n, _, _) => dh == header.dh && n == header.n) with
  | some (_, _, _, mk) =>
    let rest := st.skipped.filter (fun (dh, n, _, _) => !(dh == header.dh && n == header.n))
    some ({ st with skipped := rest }, mk)
  | none => none

/-- Taking a stored skipped key does not touch the store's clock: it removes an
entry and leaves every other field alone. Needed where a later step has to know
the counter still has room. -/
theorem trySkipped_events (st : State) (header : Header) (r : State × Key)
    (h : trySkipped st header = some r) : r.1.events = st.events := by
  unfold trySkipped at h
  split at h
  · injection h with h'; subst h'; rfl
  · exact absurd h (by simp)

/-- Receive (ratchet.md): try a stored skipped key; otherwise, on a ratchet key
    other than `DHr` (or no `DHr`), skip the old receiving chain up to `header.pn`
    and take a DH ratchet step; then skip up to `header.n` on the current chain
    and derive the message key at `header.n`. DH outputs and the fresh sending
    key are supplied by the caller; they are ignored on a same-chain message.

    A message on the current chain numbered below `nr` whose key is not stored
    is refused: its key has already been used, expired or evicted, and deriving
    the key at `nr` in its place would advance the chain on a message that
    cannot be the one at `nr`. The skip before the check leaves the state alone
    in that case, since it has nothing to skip, and after a DH step `nr` is
    zero, so the check can only fire on a same-chain message.

    A receive that would step the chain with `nr` already at `u32::MAX` is
    refused too (`ChainExhausted`), so `nr` never passes `u32::MAX`. -/
def receive (st : State) (header : Header) (dhOutRecv dhOutSend newDhsPub : Key) :
    Option (State × Key) :=
  match trySkipped st header with
  | some (st', mk) => some (ageStore st', mk)
  | none =>
    -- Inlined rather than bound to a name. A `let` with a type ascription
    -- elaborates to an opaque `have`, which a proof cannot see through, and the
    -- refinement of this function has to.
    match (if st.dhrPub == some header.dh then
             some st
           else
             (skipMessageKeys st header.pn).map
               (fun st' => dhRatchet st' header dhOutRecv dhOutSend newDhsPub)) with
    | none => none
    | some st1 =>
      match skipMessageKeys st1 header.n with
      | none => none
      | some st2 =>
        if header.n < st2.nr then
          none
        else
          match st2.ckr with
          | none => none
          | some ck =>
            if st2.nr < u32Max then
              let (ck', mk) := kdfCk ck
              some (ageStore { st2 with ckr := some ck', nr := st2.nr + 1 }, mk)
            else
              none

/-! ## The counters stay inside their 32 bits

What the ceilings buy: no state the operations produce holds a counter its
stored format cannot write or its reader refuses. -/

/-- A send leaves `ns` at most `u32::MAX`. -/
theorem send_ns_le (st : State) (r : State × Header × Key) (h : send st = some r) :
    r.1.ns ≤ u32Max := by
  unfold send at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq] at h; subst h; simp only; omega)
    | simp at h

/-- A send at `ns = u32::MAX` is refused. -/
theorem send_at_ceiling (st : State) (h : u32Max ≤ st.ns) : send st = none := by
  unfold send
  split
  · rfl
  · rw [if_neg (by omega)]

/-- Every accepted receive leaves the clock below `u32::MAX`: it ends by ageing
    the store, and ageing stops the clock at `u32::MAX - 1`. -/
theorem receive_events_lt (st : State) (header : Header) (a b c : Key) (r : State × Key)
    (h : receive st header a b c = some r) : r.1.events < u32Max := by
  unfold receive at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq] at h; subst h; exact ageStore_events_lt _)
    | simp at h

-- Self-consistency checks. Fixed byte strings stand in for the keys and DH
-- outputs; DH symmetry is honoured by giving both parties the same shared
-- output. These elaborate at build time.

private def sk : Key := List.replicate 32 0x01
private def aPub : Key := List.replicate 32 0x0a
private def bPub : Key := List.replicate 32 0x0b
private def b2Pub : Key := List.replicate 32 0x2b
private def dhAB : Key := List.replicate 32 0xab   -- DH(a, B) = DH(b, A)
private def dhB2A : Key := List.replicate 32 0xba  -- DH(b2, A)

/-- In order: the first message A sends is recovered with the same message key by
    B, whose first receive takes the opening DH ratchet step. -/
example :
    (do
      let stA := initSender sk aPub bPub dhAB .tacenta
      let (_, header, mkSend) ← send stA
      let stB := initReceiver sk bPub .tacenta
      let (_, mkRecv) ← receive stB header dhAB dhB2A b2Pub
      pure (mkSend == mkRecv)) = some true := by
  native_decide

/-- Out of order: A sends two messages on one chain; B receives the second
    first (storing the skipped key for the first), then the first from its store.
    Both message keys match what A produced. -/
example :
    (do
      let stA := initSender sk aPub bPub dhAB .tacenta
      let (stA1, header0, mk0Send) ← send stA
      let (_, header1, mk1Send) ← send stA1
      let stB := initReceiver sk bPub .tacenta
      let (stB1, mk1Recv) ← receive stB header1 dhAB dhB2A b2Pub
      let (_, mk0Recv) ← receive stB1 header0 dhAB dhB2A b2Pub
      pure (mk0Send == mk0Recv && mk1Send == mk1Recv)) = some true := by
  native_decide

/-- A duplicate is refused: B receives A's first message, then the same message
    again. Its ratchet key is the one B holds, its number is below `nr`, and its
    key is not stored, so the second delivery is not accepted rather than taken
    as the message at `nr` (ratchet.md, Sending and receiving). -/
example :
    (do
      let stA := initSender sk aPub bPub dhAB .tacenta
      let (_, header0, _) ← send stA
      let stB := initReceiver sk bPub .tacenta
      let (stB1, _) ← receive stB header0 dhAB dhB2A b2Pub
      pure (receive stB1 header0 dhAB dhB2A b2Pub).isNone) = some true := by
  native_decide

/-- A duplicate of a message taken from the store is refused too: once its key
    has been used and removed, the message is below `nr` with nothing stored. -/
example :
    (do
      let stA := initSender sk aPub bPub dhAB .tacenta
      let (stA1, header0, _) ← send stA
      let (_, header1, _) ← send stA1
      let stB := initReceiver sk bPub .tacenta
      let (stB1, _) ← receive stB header1 dhAB dhB2A b2Pub
      let (stB2, _) ← receive stB1 header0 dhAB dhB2A b2Pub
      pure (receive stB2 header0 dhAB dhB2A b2Pub).isNone) = some true := by
  native_decide

/-- The refusal costs the chain nothing: after a duplicate of the first message is
    refused, A's next message, numbered exactly `nr`, is still received with A's
    key. -/
example :
    (do
      let stA := initSender sk aPub bPub dhAB .tacenta
      let (stA1, header0, _) ← send stA
      let (_, header1, mk1Send) ← send stA1
      let stB := initReceiver sk bPub .tacenta
      let (stB1, _) ← receive stB header0 dhAB dhB2A b2Pub
      let refused := (receive stB1 header0 dhAB dhB2A b2Pub).isNone
      let (_, mk1Recv) ← receive stB1 header1 dhAB dhB2A b2Pub
      pure (refused && mk1Send == mk1Recv)) = some true := by
  native_decide

private def aPub2 : Key := List.replicate 32 0x1a
private def bPub3 : Key := List.replicate 32 0x3b
private def dhAB2 : Key := List.replicate 32 0xa2   -- DH(a, b2) = DH(b2, a)
private def dhA2B2 : Key := List.replicate 32 0xc2  -- DH(a2, b2)
private def dhB3A2 : Key := List.replicate 32 0xd2  -- DH(b3, a2)

/-- Bidirectional: A sends, B receives and replies, A receives the reply and
    sends again, B receives that. Each side takes a DH ratchet step on the
    other's new ratchet key, and every message is recovered with the sender's
    key. The same DH-output constant is reused wherever the same key pair occurs,
    which is the DH-symmetry the real curve provides. -/
example :
    (do
      let sa0 := initSender sk aPub bPub dhAB .tacenta
      let (sa1, h0, ak0) ← send sa0
      let sb0 := initReceiver sk bPub .tacenta
      let (sb1, bk0) ← receive sb0 h0 dhAB dhAB2 b2Pub
      let (sb2, hr0, br0) ← send sb1
      let (sa2, ar0) ← receive sa1 hr0 dhAB2 dhA2B2 aPub2
      let (_, h1, ak1) ← send sa2
      let (_, bk1) ← receive sb2 h1 dhA2B2 dhB3A2 bPub3
      pure (ak0 == bk0 && br0 == ar0 && ak1 == bk1)) = some true := by
  native_decide

/-- The ceilings (ratchet.md, Sending and receiving; Skipped keys): a send at
    `ns = u32::MAX - 1` is taken and the one at `u32::MAX` refused; a receive
    that would step past `nr = u32::MAX` is refused; and from the clock's stop,
    `u32::MAX - 1`, an accepted receive leaves the clock where it is. -/
example :
    (do
      let stA := initSender sk aPub bPub dhAB .tacenta
      let (stA1, _, _) ← send { stA with ns := u32Max - 1 }
      let stB := initReceiver sk bPub .tacenta
      let (_, header0, _) ← send stA
      let (stB1, _) ← receive stB header0 dhAB dhB2A b2Pub
      let atStop ← receive { stB1 with events := maxEvents }
        { dh := aPub, pn := 0, n := 1 } dhAB dhB2A b2Pub
      pure (stA1.ns == u32Max, (send stA1).isNone,
        (receive { stB1 with nr := u32Max } { dh := aPub, pn := 0, n := u32Max }
          dhAB dhB2A b2Pub).isNone,
        atStop.1.events == maxEvents)) = some (true, true, true, true) := by
  native_decide

end Model.Ratchet
