/-
Model.Braid: the ML-KEM Braid state machine, written from
tacenta-spec/protocol/mlkem-braid.md.

Two boundaries, and the model consumes them rather than computing them.

The KEM is a record of operations with one law: decapsulating what the two
encapsulation halves produced returns the secret they encapsulated. ML-KEM is not
computable here and would not be worth computing if it were, because nothing in
the state machine depends on how it works.

The erasure code is a decoder that succeeds once it holds enough codewords from
one encoder. That is the contract, and Model.Polynomial is where it is earned:
the delta property proved there is what says enough codewords determine the
message.

What this model does compute is everything else, which is the part with eleven
states, thirteen transitions, and an epoch accounting subtle enough to be worth
proving: the Ratcheted Authenticator byte for byte, and every transition.
-/
import Model.Kdf
import Model.State

namespace Model.Braid

open Model.State (Key)

abbrev Bytes := List UInt8

/-! ## Chunking

A chunk carries the message it was encoded from. That is a modelling device: on
the wire a chunk is opaque bytes and carries nothing of the sort. What it stands
for here is the erasure code's contract, that enough codewords from one encoder
determine that encoder's message, and mixing encoders determines nothing. -/

/-- The chunk size in bytes. The published document leaves this to the
    implementer and notes that larger chunks heal faster. -/
def chunkBytes : Nat := 32

structure Chunk where
  source : Bytes
  index  : Nat
  deriving Repr, DecidableEq, Inhabited

structure Encoder where
  source : Bytes
  next   : Nat
  deriving Repr, DecidableEq, Inhabited

def encode (m : Bytes) : Encoder := ⟨m, 0⟩

def Encoder.nextChunk (e : Encoder) : Chunk × Encoder :=
  (⟨e.source, e.next⟩, ⟨e.source, e.next + 1⟩)

structure Decoder where
  size   : Nat
  chunks : List Chunk
  deriving Repr, DecidableEq, Inhabited

def Decoder.new (n : Nat) : Decoder := ⟨n, []⟩

/-- Duplicate codewords do not advance a decoder, which is why the index is
    tracked at all. -/
def Decoder.addChunk (d : Decoder) (c : Chunk) : Decoder :=
  if d.chunks.any (fun x => x.index == c.index) then d
  else ⟨d.size, c :: d.chunks⟩

def Decoder.hasMessage (d : Decoder) : Bool :=
  d.chunks.length * chunkBytes ≥ d.size

/-- Enough codewords from a single encoder reconstruct its message. Codewords
    from more than one reconstruct nothing, which is what stops a decoder from
    being walked into accepting a spliced message. -/
def Decoder.message (d : Decoder) : Option Bytes :=
  if d.hasMessage then
    match d.chunks with
    -- `hasMessage` with no chunks means the decoder was sized for zero
    -- bytes, and the real decoder returns the empty message there; no real
    -- decoder returns `none` for it.
    | []      => some []
    | c :: rest =>
      -- The reconstructed message is exactly as long as the decoder was
      -- sized for: the real decoder can produce nothing else, and without
      -- this check the model could (a chunk whose `source` is not `size`
      -- bytes long would "decode" to it). Stating the length here is what
      -- makes `Decoder.message_length` a theorem rather than a hypothesis
      -- of the refinement proofs.
      if rest.all (fun x => x.source == c.source) && c.source.length == d.size
      then some c.source else none
  else none

/-- A completed decode is exactly as long as the decoder was sized for. -/
theorem Decoder.message_length (d : Decoder) (bytes : Bytes)
    (h : d.message = some bytes) : bytes.length = d.size := by
  unfold Decoder.message at h
  split at h
  · rename_i hhas
    split at h
    · rename_i hnil
      cases h
      simp only [Decoder.hasMessage, hnil, List.length_nil, Nat.zero_mul, ge_iff_le,
        decide_eq_true_eq] at hhas
      simp; omega
    · split at h
      · rename_i hcond
        cases h
        simpa using (Bool.and_eq_true _ _ |>.mp hcond).2
      · cases h
  · cases h

/-! ## The KEM boundary -/

structure Kem where
  /-- Randomness in, `(dk, ek_seed, ek_vector)` out. -/
  keyGen  : Nat → Bytes × Bytes × Bytes
  /-- The header hash: FIPS 203 `H(ek)`, which is `SHA3-256(ek_vector || ek_seed)`,
      taken here as `hashEk ek_seed ek_vector`. The published Braid document writes
      its input as `ek_seed || ek_vector` (mlkem-braid.md, The KEM split). -/
  hashEk  : Bytes → Bytes → Bytes
  /-- Randomness in, then from the header alone:
      `(encaps_secret, ct1, shared_secret)`. Encapsulation draws fresh
      randomness, as key generation does (ML-KEM's encapsulation samples a
      32-byte message), so it is a function of that randomness and the header,
      not of the header alone. -/
  encaps1 : Nat → Bytes → Bytes → Bytes × Bytes × Bytes
  /-- From the rest of the key: `ct2`. -/
  encaps2 : Bytes → Bytes → Bytes → Bytes
  decaps  : Bytes → Bytes → Bytes → Bytes
  ekSize  : Nat
  ct1Size : Nat
  ct2Size : Nat

/-- The one law the state machine rests on, for every choice of the two
    parties' randomness. Everything else about ML-KEM is the KEM's business,
    not this protocol's. -/
def Kem.Correct (K : Kem) : Prop :=
  ∀ r r' : Nat,
    let (dk, seed, vec) := K.keyGen r
    let hek := K.hashEk seed vec
    let (es, ct1, ss) := K.encaps1 r' seed hek
    K.decaps dk ct1 (K.encaps2 es seed vec) = ss

def headerSize : Nat := 64
def macSize : Nat := 32

/-! ## Messages -/

inductive MsgType where
  | none | hdr | ek | ekCt1Ack | ct1Ack | ct1 | ct2
  deriving Repr, DecidableEq, Inhabited

structure Msg where
  epoch : Nat
  type  : MsgType
  data  : Option Chunk
  deriving Repr, DecidableEq, Inhabited

/-! ## The Ratcheted Authenticator

Computed, not abstracted. It is HKDF and HMAC over labels, both of which the
model already has, and it is where the protocol's internal authenticity lives. -/

/-- `PROTOCOL_INFO`, which the published document defines as a protocol
    identifier, the KEM, and the MAC joined by underscores. So
    "Tacenta_MLKEM1024_SHA-256" as bytes.

    Wire-sensitive: a label that differs between the model and the
    implementation changes every MAC and every epoch key. Recorded in the
    conformance manifest. -/
def protocolInfo : Bytes :=
  [0x54,0x61,0x63,0x65,0x6e,0x74,0x61,0x5f,0x4d,0x4c,
   0x4b,0x45,0x4d,0x31,0x30,0x32,0x34,0x5f,0x53,0x48,
   0x41,0x2d,0x32,0x35,0x36]

/-- ":Authenticator Update" -/
def authUpdateLabel : Bytes :=
  [0x3a,0x41,0x75,0x74,0x68,0x65,0x6e,0x74,0x69,0x63,0x61,0x74,0x6f,0x72,
   0x20,0x55,0x70,0x64,0x61,0x74,0x65]

/-- ":SCKA Key" -/
def sckaKeyLabel : Bytes :=
  [0x3a,0x53,0x43,0x4b,0x41,0x20,0x4b,0x65,0x79]

/-- ":ekheader" -/
def ekHeaderLabel : Bytes :=
  [0x3a,0x65,0x6b,0x68,0x65,0x61,0x64,0x65,0x72]

/-- ":ciphertext" -/
def ciphertextLabel : Bytes :=
  [0x3a,0x63,0x69,0x70,0x68,0x65,0x72,0x74,0x65,0x78,0x74]

/-- An epoch as eight big-endian bytes, as the document recommends. -/
def epochBytes (e : Nat) : Bytes :=
  (List.range 8).map (fun i => UInt8.ofNat (e >>> (8 * (7 - i))))

structure Auth where
  rootKey : Key
  macKey  : Key
  deriving Repr, DecidableEq, Inhabited

def Auth.update (a : Auth) (epoch : Nat) (key : Bytes) : Auth :=
  let out := Model.Kdf.hkdf a.rootKey key
    (protocolInfo ++ authUpdateLabel ++ epochBytes epoch) 64
  ⟨out.take 32, out.drop 32⟩

def Auth.init (epoch : Nat) (key : Bytes) : Auth :=
  Auth.update ⟨List.replicate 32 0, []⟩ epoch key

def Auth.macHdr (a : Auth) (epoch : Nat) (hdr : Bytes) : Bytes :=
  Model.Kdf.hmac a.macKey (protocolInfo ++ ekHeaderLabel ++ epochBytes epoch ++ hdr)

def Auth.macCt (a : Auth) (epoch : Nat) (ct : Bytes) : Bytes :=
  Model.Kdf.hmac a.macKey (protocolInfo ++ ciphertextLabel ++ epochBytes epoch ++ ct)

/-- The epoch key, derived from the raw shared secret before anything uses it. -/
def kdfOk (ss : Bytes) (epoch : Nat) : Key :=
  Model.Kdf.hkdf (List.replicate 32 0) ss
    (protocolInfo ++ sckaKeyLabel ++ epochBytes epoch) 32

/-! ## State

Eleven states, plus one this model adds. A MAC that does not verify, or an
`ek_vector` that does not match the header's hash, leaves the session
unrecoverable: the published document says to abandon it and negotiate a new one,
and `failed` is that instruction made unrepresentable-otherwise rather than left
to a caller's discipline. See the implementation decisions on the
specification page. -/

inductive BraidState where
  | keysUnsampled (epoch : Nat) (auth : Auth)
  | keysSampled (epoch : Nat) (auth : Auth) (dk ekVector : Bytes) (hdrEnc : Encoder)
  | headerSent (epoch : Nat) (auth : Auth) (dk : Bytes) (ct1Dec : Decoder) (ekEnc : Encoder)
  | ct1Received (epoch : Nat) (auth : Auth) (dk ct1 : Bytes) (ekEnc : Encoder)
  | ekSentCt1Received (epoch : Nat) (auth : Auth) (dk ct1 : Bytes) (ct2Dec : Decoder)
  | noHeaderReceived (epoch : Nat) (auth : Auth) (hdrDec : Decoder)
  | headerReceived (epoch : Nat) (auth : Auth) (ekSeed hek : Bytes) (ekDec : Decoder)
  | ct1Sampled (epoch : Nat) (auth : Auth) (ekSeed hek encapsSecret ct1 : Bytes)
      (ct1Enc : Encoder) (ekDec : Decoder)
  | ekReceivedCt1Sampled (epoch : Nat) (auth : Auth)
      (encapsSecret ct1 ekSeed ekVector : Bytes) (ct1Enc : Encoder)
  | ct1Acknowledged (epoch : Nat) (auth : Auth) (ekSeed hek encapsSecret ct1 : Bytes)
      (ekDec : Decoder)
  | ct2Sampled (epoch : Nat) (auth : Auth) (ct2Enc : Encoder)
  | failed
  deriving Repr, Inhabited

def BraidState.epoch : BraidState → Nat
  | keysUnsampled e _ | keysSampled e _ _ _ _ | headerSent e _ _ _ _
  | ct1Received e _ _ _ _ | ekSentCt1Received e _ _ _ _ | noHeaderReceived e _ _
  | headerReceived e _ _ _ _ | ct1Sampled e _ _ _ _ _ _ _
  | ekReceivedCt1Sampled e _ _ _ _ _ _ | ct1Acknowledged e _ _ _ _ _ _
  | ct2Sampled e _ _ => e
  | failed => 0

/-- A key the agreement produced, with the epoch it belongs to. Matches
    `Model.SparseRatchet.Output`, which is what consumes it. -/
structure Output where
  keyEpoch : Nat
  key      : Key
  deriving Repr, DecidableEq, Inhabited

/-! ## Sending

Every `Send` reports `sending_epoch`, the latest epoch both parties are known to
hold. It is read as `epoch - 1` **after** any transition, which is what makes it
name a completed epoch rather than the one being negotiated. Nat subtraction
saturates, and epochs start at 1, so before the first agreement it is 0. -/

def send (K : Kem) (rand : Nat) : BraidState → Option Msg × Nat × Option Output × BraidState
  | .keysUnsampled epoch auth =>
    -- Transition (1)
    let (dk, ekSeed, ekVector) := K.keyGen rand
    let hek := K.hashEk ekSeed ekVector
    let header := ekSeed ++ hek
    let mac := auth.macHdr epoch header
    let enc := encode (header ++ mac)
    let (chunk, enc') := enc.nextChunk
    let st := BraidState.keysSampled epoch auth dk ekVector enc'
    (some ⟨epoch, .hdr, some chunk⟩, st.epoch - 1, none, st)
  | .keysSampled epoch auth dk ekVector enc =>
    let (chunk, enc') := enc.nextChunk
    let st := BraidState.keysSampled epoch auth dk ekVector enc'
    (some ⟨epoch, .hdr, some chunk⟩, st.epoch - 1, none, st)
  | .headerSent epoch auth dk ct1Dec enc =>
    let (chunk, enc') := enc.nextChunk
    let st := BraidState.headerSent epoch auth dk ct1Dec enc'
    (some ⟨epoch, .ek, some chunk⟩, st.epoch - 1, none, st)
  | .ct1Received epoch auth dk ct1 enc =>
    let (chunk, enc') := enc.nextChunk
    let st := BraidState.ct1Received epoch auth dk ct1 enc'
    (some ⟨epoch, .ekCt1Ack, some chunk⟩, st.epoch - 1, none, st)
  | st@(.ekSentCt1Received epoch _ _ _ _) =>
    (some ⟨epoch, .none, Option.none⟩, st.epoch - 1, none, st)
  | st@(.noHeaderReceived epoch _ _) =>
    (some ⟨epoch, .none, Option.none⟩, st.epoch - 1, none, st)
  | .headerReceived epoch auth ekSeed hek ekDec =>
    -- Transition (7): the responder learns the epoch key here, well before the
    -- initiator does. That gap is what `sending_epoch` exists to report. This
    -- is the second of the two transitions that draw randomness (the first
    -- is transition (1)), and `rand` is that randomness.
    let (encapsSecret, ct1, ssRaw) := K.encaps1 rand ekSeed hek
    let ss := kdfOk ssRaw epoch
    let auth' := auth.update epoch ss
    let enc := encode ct1
    let (chunk, enc') := enc.nextChunk
    let st := BraidState.ct1Sampled epoch auth' ekSeed hek encapsSecret ct1 enc' ekDec
    (some ⟨epoch, .ct1, some chunk⟩, st.epoch - 1, some ⟨epoch, ss⟩, st)
  | .ct1Sampled epoch auth ekSeed hek es ct1 enc ekDec =>
    let (chunk, enc') := enc.nextChunk
    let st := BraidState.ct1Sampled epoch auth ekSeed hek es ct1 enc' ekDec
    (some ⟨epoch, .ct1, some chunk⟩, st.epoch - 1, none, st)
  | .ekReceivedCt1Sampled epoch auth es ct1 ekSeed ekVector enc =>
    let (chunk, enc') := enc.nextChunk
    let st := BraidState.ekReceivedCt1Sampled epoch auth es ct1 ekSeed ekVector enc'
    (some ⟨epoch, .ct1, some chunk⟩, st.epoch - 1, none, st)
  | st@(.ct1Acknowledged epoch _ _ _ _ _ _) =>
    (some ⟨epoch, .none, Option.none⟩, st.epoch - 1, none, st)
  | .ct2Sampled epoch auth enc =>
    let (chunk, enc') := enc.nextChunk
    let st := BraidState.ct2Sampled epoch auth enc'
    (some ⟨epoch, .ct2, some chunk⟩, st.epoch - 1, none, st)
  | .failed => (none, 0, none, .failed)

/-! ## Receiving -/

/-- Completing an encapsulation, which three states do identically. -/
private def finishEncaps (K : Kem) (epoch : Nat) (auth : Auth)
    (es ct1 ekSeed ekVector : Bytes) : BraidState :=
  let ct2 := K.encaps2 es ekSeed ekVector
  let mac := auth.macCt epoch (ct1 ++ ct2)
  BraidState.ct2Sampled epoch auth (encode (ct2 ++ mac))

def receive (K : Kem) (st : BraidState) (msg : Msg) : Nat × Option Output × BraidState :=
  let stay := fun (s : BraidState) => (s.epoch - 1, (none : Option Output), s)
  match st with
  | .keysUnsampled _ _ => stay st
  | .keysSampled epoch auth dk ekVector _ =>
    if msg.epoch == epoch && msg.type == .ct1 then
      match msg.data with
      | some c =>
        -- Transition (2)
        let ct1Dec := (Decoder.new K.ct1Size).addChunk c
        stay (.headerSent epoch auth dk ct1Dec (encode ekVector))
      | Option.none => stay st
    else stay st
  | .headerSent epoch auth dk ct1Dec ekEnc =>
    if msg.epoch == epoch && msg.type == .ct1 then
      match msg.data with
      | some c =>
        let d := ct1Dec.addChunk c
        match d.message with
        -- Transition (3)
        | some ct1 => stay (.ct1Received epoch auth dk ct1 ekEnc)
        | Option.none => stay (.headerSent epoch auth dk d ekEnc)
      | Option.none => stay st
    else stay st
  | .ct1Received epoch auth dk ct1 _ =>
    if msg.epoch == epoch && msg.type == .ct2 then
      match msg.data with
      | some c =>
        -- Transition (4)
        let ct2Dec := (Decoder.new (K.ct2Size + macSize)).addChunk c
        stay (.ekSentCt1Received epoch auth dk ct1 ct2Dec)
      | Option.none => stay st
    else stay st
  | .ekSentCt1Received epoch auth dk ct1 ct2Dec =>
    if msg.epoch == epoch && msg.type == .ct2 then
      match msg.data with
      | some c =>
        let d := ct2Dec.addChunk c
        match d.message with
        | some ct2WithMac =>
          let ct2 := ct2WithMac.take K.ct2Size
          let mac := ct2WithMac.drop K.ct2Size
          let ss := kdfOk (K.decaps dk ct1 ct2) epoch
          -- The authenticator ratchets before the MAC is checked, because the
          -- MAC key is what the ratchet produces. A failure is terminal.
          let auth' := auth.update epoch ss
          if auth'.macCt epoch (ct1 ++ ct2) == mac then
            -- Transition (5)
            let st' := BraidState.noHeaderReceived (epoch + 1) auth'
              (Decoder.new (headerSize + macSize))
            (st'.epoch - 1, some ⟨st'.epoch - 1, ss⟩, st')
          else (epoch - 1, none, .failed)
        | Option.none => stay (.ekSentCt1Received epoch auth dk ct1 d)
      | Option.none => stay st
    else stay st
  | .noHeaderReceived epoch auth hdrDec =>
    if msg.epoch == epoch && msg.type == .hdr then
      match msg.data with
      | some c =>
        let d := hdrDec.addChunk c
        match d.message with
        | some hdrWithMac =>
          let hdr := hdrWithMac.take headerSize
          let mac := hdrWithMac.drop headerSize
          if auth.macHdr epoch hdr == mac then
            -- Transition (6)
            stay (.headerReceived epoch auth (hdr.take 32) (hdr.drop 32)
                   (Decoder.new K.ekSize))
          else (epoch - 1, none, .failed)
        | Option.none => stay (.noHeaderReceived epoch auth d)
      | Option.none => stay st
    else stay st
  | .headerReceived _ _ _ _ _ => stay st
  | .ct1Sampled epoch auth ekSeed hek es ct1 ct1Enc ekDec =>
    if msg.epoch == epoch && (msg.type == .ek || msg.type == .ekCt1Ack) then
      match msg.data with
      | some c =>
        let d := ekDec.addChunk c
        let acked := msg.type == .ekCt1Ack
        match d.message with
        | some ekVector =>
          if K.hashEk ekSeed ekVector != hek then (epoch - 1, none, .failed)
          else if acked then
            -- Transition (9): both events in one message
            stay (finishEncaps K epoch auth es ct1 ekSeed ekVector)
          else
            -- Transition (10)
            stay (.ekReceivedCt1Sampled epoch auth es ct1 ekSeed ekVector ct1Enc)
        | Option.none =>
          if acked then
            -- Transition (8)
            stay (.ct1Acknowledged epoch auth ekSeed hek es ct1 d)
          else stay (.ct1Sampled epoch auth ekSeed hek es ct1 ct1Enc d)
      | Option.none => stay st
    else stay st
  | .ekReceivedCt1Sampled epoch auth es ct1 ekSeed ekVector _ =>
    if msg.epoch == epoch && msg.type == .ekCt1Ack then
      -- Transition (12)
      stay (finishEncaps K epoch auth es ct1 ekSeed ekVector)
    else stay st
  | .ct1Acknowledged epoch auth ekSeed hek es ct1 ekDec =>
    if msg.epoch == epoch && msg.type == .ekCt1Ack then
      match msg.data with
      | some c =>
        let d := ekDec.addChunk c
        match d.message with
        | some ekVector =>
          if K.hashEk ekSeed ekVector != hek then (epoch - 1, none, .failed)
          else
            -- Transition (11)
            stay (finishEncaps K epoch auth es ct1 ekSeed ekVector)
        | Option.none => stay (.ct1Acknowledged epoch auth ekSeed hek es ct1 d)
      | Option.none => stay st
    else stay st
  | .ct2Sampled epoch auth _ =>
    if msg.epoch == epoch + 1 then
      -- Transition (13)
      stay (.keysUnsampled (epoch + 1) auth)
    else stay st
  | .failed => (0, none, .failed)

/-! ## Initialisation -/

def initAlice (secret : Bytes) : BraidState :=
  .keysUnsampled 1 (Auth.init 1 secret)

def initBob (secret : Bytes) : BraidState :=
  .noHeaderReceived 1 (Auth.init 1 secret) (Decoder.new (headerSize + macSize))

/-! ## Properties

The epoch accounting reads `state.epoch - 1` after any transition, so that
both sides label the same key with the same number. If they did not, the
ratchet above would read one key as two.

These say it is right. -/

/-- Sending never advances the epoch. Only receiving does, at transitions 5 and
13, and both are the moment the other side is known to have caught up. -/
theorem send_epoch (K : Kem) (r : Nat) (st : BraidState) :
    (send K r st).2.2.2.epoch = st.epoch := by
  cases st <;> simp [send, BraidState.epoch]

/-- The epoch a `Send` reports is the one before the state's: the last epoch both
parties are known to hold, not the one being negotiated. -/
theorem send_reports (K : Kem) (r : Nat) (st : BraidState) :
    (send K r st).2.1 = st.epoch - 1 := by
  cases st <;> simp [send, BraidState.epoch]

/-- Receiving advances the epoch by at most one. -/
theorem receive_epoch_le (K : Kem) (st : BraidState) (msg : Msg) :
    (receive K st msg).2.2.epoch ≤ st.epoch + 1 := by
  cases st <;> simp only [receive] <;> repeat' split
  all_goals (simp [BraidState.epoch, finishEncaps]; try omega)

/-- **A key is labelled with the epoch it was negotiated in, on the sending
side.** The responder emits at transition 7, when it samples `ct1`. -/
theorem send_output_epoch (K : Kem) (r : Nat) (st : BraidState) (o : Output) :
    (send K r st).2.2.1 = some o → o.keyEpoch = st.epoch := by
  cases st <;> simp +zetaDelta [send, BraidState.epoch] <;> rintro rfl <;> rfl

/-- **And with the same epoch on the receiving side.** The initiator emits at
transition 5, after advancing, and reads the label back off the advanced state.
That the two agree is what makes the epoch a shared name for a shared key. -/
theorem receive_output_epoch (K : Kem) (st : BraidState) (msg : Msg) (o : Output) :
    (receive K st msg).2.1 = some o → o.keyEpoch = st.epoch := by
  cases st <;> simp only [receive] <;> repeat' split
  all_goals (simp +zetaDelta [BraidState.epoch]; try omega)
  all_goals (rintro rfl; rfl)

/-- The epoch a `Receive` reports is never one the state has not reached. -/
theorem receive_reports_le (K : Kem) (st : BraidState) (msg : Msg) :
    (receive K st msg).1 ≤ st.epoch := by
  cases st <;> simp only [receive] <;> repeat' split
  all_goals (simp [BraidState.epoch, finishEncaps]; try omega)

/-- Failure is terminal: nothing leaves it and it emits nothing. -/
theorem failed_send (K : Kem) (r : Nat) :
    send K r .failed = (none, 0, none, .failed) := rfl

theorem failed_receive (K : Kem) (msg : Msg) :
    receive K .failed msg = (0, none, .failed) := rfl

/-! ## Running it

The theorems above constrain the epoch accounting and say nothing about whether
the thirteen transitions are wired to each other correctly. A state machine can
satisfy every one of them and still deadlock in round three.

So this drives both parties through a full epoch against a toy KEM, and checks
that they arrive at the same key with the same label. It is the cheapest possible
answer to "does it actually run", and it is worth more than it looks: reaching
agreement requires transitions 1, 2, 3, 4, 5, 6, 7 and 9 to all fire in the right
order, and any one of them misdirected stalls the exchange forever. -/

/-- A KEM that satisfies the one law and nothing else. Its sizes are shrunk so a
value needs two or three codewords rather than fifty. -/
def toyKem : Kem where
  keyGen r  := (List.replicate 32 (UInt8.ofNat r),
                List.replicate 32 (UInt8.ofNat r),
                List.replicate 64 (UInt8.ofNat r))
  hashEk s v := List.replicate 32 (v.foldl (· + ·) (s.foldl (· + ·) 0))
  encaps1 _ seed _ := (seed, List.replicate 64 7, seed)
  encaps2 _ _ _  := List.replicate 32 9
  decaps dk _ _  := dk
  ekSize  := 64
  ct1Size := 64
  ct2Size := 32

theorem toyKem_correct : toyKem.Correct := by
  intro r r'; rfl

structure Sim where
  alice : BraidState
  bob   : BraidState
  aOut  : List Output
  bOut  : List Output

def Sim.start (secret : Bytes) : Sim :=
  ⟨initAlice secret, initBob secret, [], []⟩

/-- One round: Alice speaks and Bob hears her, then Bob speaks and Alice hears
him. Strictly alternating, which is the hardest schedule for a protocol whose
whole point is sending in parallel. -/
def Sim.round (K : Kem) (r : Nat) (s : Sim) : Sim :=
  let (mA, _, oA, alice₁) := send K r s.alice
  let (_, oB₁, bob₁) :=
    match mA with
    | some m => receive K s.bob m
    | Option.none => (0, Option.none, s.bob)
  let (mB, _, oB₂, bob₂) := send K r bob₁
  let (_, oA₂, alice₂) :=
    match mB with
    | some m => receive K alice₁ m
    | Option.none => (0, Option.none, alice₁)
  { alice := alice₂, bob := bob₂,
    aOut := s.aOut ++ oA.toList ++ oA₂.toList,
    bOut := s.bOut ++ oB₁.toList ++ oB₂.toList }

def runSim (K : Kem) (n : Nat) (secret : Bytes) : Sim :=
  (List.range n).foldl (fun s i => Sim.round K i s) (Sim.start secret)

/-- Both parties produced a key, both labelled it epoch 1, and it is the same
key. -/
def agreed (s : Sim) : Bool :=
  match s.aOut.head?, s.bOut.head? with
  | some a, some b => a.keyEpoch == 1 && b.keyEpoch == 1 && a.key == b.key
  | _, _ => false

/-- Eight rounds of strict alternation reach agreement on the first epoch. -/
example : agreed (runSim toyKem 8 (List.replicate 32 42)) = true := by native_decide

/-- And neither party ends in the failed state, so nothing was abandoned on the
way there. -/
example :
    let s := runSim toyKem 8 (List.replicate 32 42)
    (match s.alice with | .failed => false | _ => true) &&
    (match s.bob with | .failed => false | _ => true) = true := by
  native_decide

end Model.Braid
