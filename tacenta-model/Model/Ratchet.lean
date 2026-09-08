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
    message key. `none` when there is no sending chain yet. -/
def send (st : State) : Option (State × Header × Key) :=
  match st.cks with
  | none => none
  | some ck =>
    let (ck', mk) := kdfCk ck
    let header : Header := { dh := st.dhsPub, pn := st.pn, n := st.ns }
    some ({ st with cks := some ck', ns := st.ns + 1 }, header, mk)

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

/-- Receive (ratchet.md): try a stored skipped key; otherwise, on an unseen
    ratchet key, skip the remainder of the old receiving chain up to `header.pn`
    and take a DH ratchet step; then skip up to `header.n` on the current chain
    and derive the message key at `header.n`. DH outputs and the fresh sending
    key are supplied by the caller; they are ignored on a same-chain message. -/
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
        match st2.ckr with
        | none => none
        | some ck =>
          let (ck', mk) := kdfCk ck
          some (ageStore { st2 with ckr := some ck', nr := st2.nr + 1 }, mk)

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

end Model.Ratchet
