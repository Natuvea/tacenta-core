import Translation.TacentaBraid
import Translation.BraidT1
import Model.Braid
import Aeneas.Data.BitVec

/-!
# T3 for the ML-KEM Braid: refinement against `Model.Braid`

T1 says `step_send`/`step_receive` cannot panic. That says nothing about
whether they compute what the published protocol document says, which is
what `Model.Braid` states and what this file connects the translated code to.

## Two boundaries, two different kinds of assumption

`Model.Braid.Kem` is a record of **uninterpreted** functions constrained by
one law, `Kem.Correct`. There is no concrete reference computation for any
of its fields (including `hashEk`), so the right assumption is a single
bundled existential: some `Kem` witness satisfying `Kem.Correct` whose fields
the real `IncrementalKeyPair`/`EncapsState` operations equal. See `KemAgrees`.

`Model.Braid.Encoder`/`Decoder` are concrete, but deliberately not a
byte-level reimplementation of the real Reed-Solomon code (a modelled
`Chunk` "carries the message it was encoded from... on the wire a chunk is
opaque bytes and carries nothing of the sort," the model doc's own words).
So the erasure boundary needs a relation, not a flat value equality:
`ErasureAgrees` states a simulation invariant carried across `new`/
`next_chunk`/`add_chunk`, plus agreement on what `message` returns. It is
stated directly against `Model.Braid`, not chained through the erasure
crate's own (separately translated, still-partial) T3. Charon translates
each crate independently, so braid's opaque `tacenta_erasure.Encoder` and
erasure's own translated `Encoder` are unrelated Lean symbols with the same
name; bridging them would be its own separate project, not a shortcut.

Both are in the same trust category as `Tacenta.T3`'s `HmacAgrees`/
`HkdfAgrees`: an accepted external-primitive boundary, not something this
file tries to reprove. Braid gets its own KDF agreement assumptions below
too, distinct from `Tacenta.T3`'s, per the counting trap `BraidT1.lean`
already documents: Aeneas gives this crate its own copy of `hkdf_sha256`/
`hmac_sha256`, and one proof does not discharge another crate's copy.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.BraidT3

open tacenta_braid

/-! ## Byte conversions, braid's own copy -/

abbrev Bytes := List UInt8

def u8 (b : Std.U8) : UInt8 := UInt8.ofNat b.val
def keyOf {n : Usize} (a : Array Std.U8 n) : List UInt8 := a.val.map u8
def sliceOf (s : Slice Std.U8) : List UInt8 := s.val.map u8
def vecOf (v : alloc.vec.Vec Std.U8) : List UInt8 := v.val.map u8

theorem u8_injective {x y : Std.U8} (h : u8 x = u8 y) : x = y := by
  simp only [u8] at h
  have hx : x.val < 256 := by scalar_tac
  have hy : y.val < 256 := by scalar_tac
  have := congrArg UInt8.toNat h
  simp at this
  scalar_tac

/-! ## The KDF boundary: braid's own copy of `HmacAgrees`/`HkdfAgrees`

Same shape as `Tacenta.T3`'s, but a separate declaration: Aeneas gives this
crate its own `tacenta_kdf.hkdf_sha256`/`hmac_sha256` axioms (the counting
trap `BraidT1.lean` already documents for their totality-only versions), so
one proof of the ratchet's agreement does not discharge braid's. Argument
order matches how `Auth.update`/`Auth.mac_hdr`/`Auth.mac_ct`/`kdf_ok` call
them and how `Model.Kdf.hkdf salt ikm info len`/`Model.Kdf.hmac key data`
are written, with no relabelling to match. `.total` derives `BraidT1.lean`'s
existing totality constants back out, so that file needs no edits. -/

def BraidHkdfAgrees : Prop :=
  ∀ (N : Usize) (salt ikm info : Slice Std.U8),
    ∃ r, tacenta_kdf.hkdf_sha256 N salt ikm info = ok r ∧
      keyOf r = Model.Kdf.hkdf (sliceOf salt) (sliceOf ikm) (sliceOf info) N.val

def BraidHmacAgrees : Prop :=
  ∀ (key data : Slice Std.U8),
    ∃ r, tacenta_kdf.hmac_sha256 key data = ok r ∧
      keyOf r = Model.Kdf.hmac (sliceOf key) (sliceOf data)

theorem BraidHkdfAgrees.total (h : BraidHkdfAgrees) : Tacenta.BraidT1.HkdfSha256Total :=
  fun N a b c => let ⟨r, hr, _⟩ := h N a b c; ⟨r, hr⟩

theorem BraidHmacAgrees.total (h : BraidHmacAgrees) : Tacenta.BraidT1.HmacSha256Total :=
  fun a b => let ⟨r, hr, _⟩ := h a b; ⟨r, hr⟩

/-! ## The derivation labels and protocol constants agree

Checked directly against `Model.Braid`'s literals, not assumed: if either
side drifted the refinement below would be false, and a label that differs
between the two sides changes every MAC and every epoch key. -/

theorem protocolInfo_agrees :
    sliceOf PROTOCOL_INFO = Model.Braid.protocolInfo := by
  simp [sliceOf, PROTOCOL_INFO, Model.Braid.protocolInfo]; rfl

theorem authUpdate_agrees :
    sliceOf AUTH_UPDATE = Model.Braid.authUpdateLabel := by
  simp [sliceOf, AUTH_UPDATE, Model.Braid.authUpdateLabel]; rfl

theorem sckaKey_agrees :
    sliceOf SCKA_KEY = Model.Braid.sckaKeyLabel := by
  simp [sliceOf, SCKA_KEY, Model.Braid.sckaKeyLabel]; rfl

theorem ekHeader_agrees :
    sliceOf EK_HEADER = Model.Braid.ekHeaderLabel := by
  simp [sliceOf, EK_HEADER, Model.Braid.ekHeaderLabel]; rfl

theorem ciphertext_agrees :
    sliceOf CIPHERTEXT = Model.Braid.ciphertextLabel := by
  simp [sliceOf, CIPHERTEXT, Model.Braid.ciphertextLabel]; rfl

theorem macLen_agrees : MAC_LEN.val = Model.Braid.macSize := by
  simp [MAC_LEN, Model.Braid.macSize]

/-- `tacenta_kem::HEADER_LEN`/`EK_VECTOR_LEN`/`CT1_LEN`/`CT2_LEN` are opaque
axioms (`tacenta_kem` is translated as an interface, not a body, same as
`IncrementalKeyPair`/`EncapsState`), so nothing here can compute what they
return the way `macLen_agrees` computes through a real literal. `headerSize`
is a fixed `Model.Braid` constant regardless of which `Kem` witness `K` is,
but `ekSize`/`ct1Size`/`ct2Size` are themselves uninterpreted `Kem` fields, so
even the *shape* of agreement has to be parametrized by `K`, the same
boundary and trust category as `KemAgreesFor`. -/
def KemLenAgrees (K : Model.Braid.Kem) : Prop :=
  (∃ v, tacenta_kem.HEADER_LEN = ok v ∧ v.val = Model.Braid.headerSize) ∧
  (∃ v, tacenta_kem.EK_VECTOR_LEN = ok v ∧ v.val = K.ekSize) ∧
  (∃ v, tacenta_kem.CT1_LEN = ok v ∧ v.val = K.ct1Size) ∧
  (∃ v, tacenta_kem.CT2_LEN = ok v ∧ v.val = K.ct2Size)

/-- The `i`-th big-endian byte of a 64-bit value, as a `setWidth`/shift rather
than the raw recursive `toLEBytes` definition. The recursive form unfolds
into an unreadable nested tower of `setWidth`/`>>>` that neither `simp` nor
`scalar_tac` closes; this closed form is what both sides can actually be
compared against. -/
private theorem beByte_eq (v : BitVec 64) (i : Nat) (hi : i < 8) :
    v.toBEBytes[i]! = (v >>> (8 * (7 - i))).setWidth 8 := by
  rw [BitVec.eq_iff]
  intro j hj
  have hlen : v.toLEBytes.length = 8 := by simp [BitVec.toLEBytes_length]
  have hib : i < v.toBEBytes.length := by simp [BitVec.toBEBytes_length]; omega
  have hb : 7 - i < v.toLEBytes.length := by omega
  have hrw : v.toBEBytes[i]! = v.toLEBytes[7 - i]! := by
    rw [← List.Inhabited_getElem_eq_getElem! v.toBEBytes i hib]
    unfold BitVec.toBEBytes
    rw [List.getElem_reverse]
    simp only [hlen]
    exact List.Inhabited_getElem_eq_getElem! v.toLEBytes (7 - i) hb
  have hbit := BitVec.toLEBytes_getElem!_testBit v (7 - i) j hj
  simp only [Byte.testBit, BitVec.getElem!_eq_testBit_toNat] at hbit
  rw [hrw, BitVec.getElem!_setWidth 8 _ j hj, BitVec.getElem!_eq_testBit_toNat,
    BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ushiftRight, hbit, Nat.testBit_shiftRight]

/-- `toNat_setWidth`-shaped, but derived the same testBit-extensionality way as
`beByte_eq` rather than trusted by name: this closes the fact directly,
without depending on a generic Mathlib/core lemma of this shape firing by
simp. -/
private theorem setWidth8_toNat (x : BitVec 64) : (x.setWidth 8).toNat = x.toNat % 2 ^ 8 := by
  rw [BitVec.toNat_setWidth]

/-! ## The KEM boundary: one bundled existential

`dk` never appears in the real API (`IncrementalKeyPair` exposes only
`.header`, `.ek_vector`, `.decapsulate`). It stands for the hidden
decapsulation key exactly the way `BraidState`'s own `dk : Vec U8` field
never leaves the state machine except as an argument to `decapsulate`
itself. `generate`'s randomness source isn't threaded through to `K.keyGen`:
`Kem.Correct` is a property of `encaps`/`decaps` agreeing, not of what
`generate` returns for a given seed, so nothing here needs to relate the
real RNG to the model's `Nat` seed.

Each clause follows `Tacenta.T3`'s `HmacAgrees` shape exactly: the real call's
own arguments stay universally quantified as their real types, and only the
*output* gets converted to `Bytes` for comparison. Nothing here is ever
built by converting a `Bytes` value back into a real `Slice`/`Array`. -/

/-- Parametrized by a specific witness `K`, rather than existentially binding
one, since almost everything downstream (`StateRefines`, `KeyPairRefines`,
...) already takes `K` as a free variable: a caller destructures `KemAgrees`
once, at the top, and threads the one resulting `K` through everything else
via `KemAgreesFor`. -/
def KemAgreesFor (K : Model.Braid.Kem) : Prop :=
  K.Correct ∧
    (∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (rng : R),
      ∃ kp rng' rand,
        tacenta_kem.IncrementalKeyPair.generate rc crc rng =
          ok (core.result.Result.Ok kp, rng') ∧
        (∃ h, tacenta_kem.IncrementalKeyPair.header kp = ok h ∧
          vecOf h = (K.keyGen rand).2.1 ++ K.hashEk (K.keyGen rand).2.1 (K.keyGen rand).2.2) ∧
        (∃ v, tacenta_kem.IncrementalKeyPair.ek_vector kp = ok v ∧
          vecOf v = (K.keyGen rand).2.2) ∧
        (∀ ct1 ct2 : Slice Std.U8, ct1.length = K.ct1Size → ct2.length = K.ct2Size →
          ∃ raw : Array Std.U8 32#usize,
            tacenta_kem.IncrementalKeyPair.decapsulate kp ct1 ct2 =
              ok (core.result.Result.Ok raw) ∧
            keyOf raw = K.decaps (K.keyGen rand).1 (sliceOf ct1) (sliceOf ct2))) ∧
    (∀ (kp : tacenta_kem.IncrementalKeyPair),
      ∃ dk ekSeed ekVector : Bytes,
        (∃ h, tacenta_kem.IncrementalKeyPair.header kp = ok h ∧
          vecOf h = ekSeed ++ K.hashEk ekSeed ekVector) ∧
        (∃ v, tacenta_kem.IncrementalKeyPair.ek_vector kp = ok v ∧ vecOf v = ekVector) ∧
        (∀ ct1 ct2 : Slice Std.U8, ct1.length = K.ct1Size → ct2.length = K.ct2Size →
          ∃ raw : Array Std.U8 32#usize,
            tacenta_kem.IncrementalKeyPair.decapsulate kp ct1 ct2 =
              ok (core.result.Result.Ok raw) ∧
            keyOf raw = K.decaps dk (sliceOf ct1) (sliceOf ct2))) ∧
    (∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
        (header : Slice Std.U8) (rng : R), header.length = Model.Braid.headerSize →
      ∃ es ct1raw ssraw rng',
        tacenta_kem.encapsulate1 rc crc header rng =
          ok (core.result.Result.Ok (es, ct1raw, ssraw), rng') ∧
        (∀ ekSeed hek : Bytes, ekSeed.length = 32 → sliceOf header = ekSeed ++ hek →
          (K.encaps1 ekSeed hek).2.1 = vecOf ct1raw ∧
          (K.encaps1 ekSeed hek).2.2 = keyOf ssraw ∧
          (∀ ekVector : Slice Std.U8, ekVector.length = K.ekSize →
            ∃ ct2raw,
              tacenta_kem.encapsulate2 es ekVector = ok (core.result.Result.Ok ct2raw) ∧
              vecOf ct2raw =
                K.encaps2 (K.encaps1 ekSeed hek).1 ekSeed (sliceOf ekVector))))

def KemAgrees : Prop := ∃ K, KemAgreesFor K

/-- `tacenta_kem::validate_ek` checks a received `ekVector` against the
`ekSeed`/`hek` split of a stored header, the receive-side counterpart to
`KemAgreesFor`'s `hashEk` clause. It's opaque like everything else at this
boundary, so its *result* (not just that it returns) has to be assumed: on a
header of the real layout (a 32-byte seed followed by a 32-byte hash) and a
vector of the real size, the real check accepts iff the model's `hashEk`
recomputation matches the stored `hek`, which is exactly the guard
`Model.Braid.receive`'s `ct1Sampled`/`ct1Acknowledged` branches use
(`K.hashEk ekSeed ekVector != hek`).

The three length premises are the guards the crate applies before it hashes
anything: libcrux's `validate_pk_bytes` returns `Err` (so `validate_ek`
returns `false`) on a header or vector of the wrong length. Stated for every
`hek` and `ekVector`, the clause would demand `true` of `validate_ek header
[]` whenever `hek = K.hashEk ekSeed []`, where the crate answers `false`, and
no `K` would satisfy it. The lengths are available at every use:
`StateRefines` carries `ekSeedM.length = 32`, `hekM.length = 32` and
`ekDecM.size = K.ekSize` for the header-holding states, and the decoded
vector's length is `Model.Braid.Decoder.message_length`. -/
def ValidateEkAgrees (K : Model.Braid.Kem) : Prop :=
  ∀ (header ekVector : Slice Std.U8) (ekSeed hek : Bytes),
    ekSeed.length = 32 → hek.length = 32 → ekVector.length = K.ekSize →
    sliceOf header = ekSeed ++ hek →
    ∃ r, tacenta_kem.validate_ek header ekVector = ok r ∧
      (r = true ↔ K.hashEk ekSeed (sliceOf ekVector) = hek)

/-- `State.clone` clones the `IncrementalKeyPair`/`EncapsState` it holds, and
nothing above says what a *clone* behaves like. `KemAgrees` only says every
key pair, cloned or not, has *some* witness, not that a clone shares its
original's witness. This is what closes that gap: a clone answers `header`/
`ek_vector`/`decapsulate`/`encapsulate2` exactly as the original did, which
is what "clone" means for any of this crate's own operations to still care
about it afterward. -/
def KemCloneAgrees : Prop :=
  (∀ kp kp' : tacenta_kem.IncrementalKeyPair,
    tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp = ok kp' →
    (∀ h, tacenta_kem.IncrementalKeyPair.header kp = ok h →
      tacenta_kem.IncrementalKeyPair.header kp' = ok h) ∧
    (∀ v, tacenta_kem.IncrementalKeyPair.ek_vector kp = ok v →
      tacenta_kem.IncrementalKeyPair.ek_vector kp' = ok v) ∧
    (∀ (ct1 ct2 : Slice Std.U8) raw,
      tacenta_kem.IncrementalKeyPair.decapsulate kp ct1 ct2 =
        ok (core.result.Result.Ok raw) →
      tacenta_kem.IncrementalKeyPair.decapsulate kp' ct1 ct2 =
        ok (core.result.Result.Ok raw))) ∧
  (∀ es es' : tacenta_kem.EncapsState,
    tacenta_kem.EncapsState.Insts.CoreCloneClone.clone es = ok es' →
    ∀ (ekVector : Slice Std.U8) ct2, tacenta_kem.encapsulate2 es ekVector =
      ok (core.result.Result.Ok ct2) →
      tacenta_kem.encapsulate2 es' ekVector = ok (core.result.Result.Ok ct2))

/-! ## The erasure boundary: a simulation relation, not a value equality

`Encoder`/`Decoder` are stateful (`new`/`next_chunk`/`add_chunk` thread state
across calls), so this can't be a single equation the way `KemAgrees`'s
pieces are. `EncoderSim n`/`DecoderSim m n` say the real and model state
agree for the next `n` operations.

Two aspects of the relation are stated more carefully than a first reading
might expect; `Satisfiability.lean` refutes the stronger alternatives:

- *Fuel is bounded.* A real chunk index is a `u16`, so no real encoder can
  satisfy `EncoderSim n` for every `n`. `EncoderRefines` demands it only
  while the model's own position leaves room (`model.next + n ≤ 65536`), and
  taking a step requires the encoder to be *live* (`model.next < 65536`), a
  precondition `step_send_refines` states through `EncodersLive`. That is
  the crate's real liveness limit -- an epoch whose peer never replies
  exhausts its encoder after 65,536 codewords -- put where it belongs, in
  the theorem's hypotheses, rather than assumed away.
- *A decoder's chunks belong to a message.* Model chunks carry the message
  they encode (`source`), so a relation quantifying over every model chunk
  sharing the real chunk's index would demand two different answers of one
  total real `message`. `DecoderSim m` is parameterised by the message `m`
  the decoder is collecting: it speaks only about real chunks that are
  codewords of `m`
  (`CodewordOf`, defined through the real encoder itself), and relates them
  to the model chunk `⟨m, index⟩`. `DecoderRefines` quantifies `m` over the
  messages the model decoder could still be collecting -- any `size`-byte
  message while it is empty, the one its chunks already carry otherwise --
  which is exactly the contract of an erasure code: fed codewords of one
  message of the right length, it reconstructs that message and nothing
  else.

The price is a precondition. Refinement of `step_receive` assumes the
incoming chunk is a codeword of the message the model says it
carries, of the right length, and that the decoder it lands in holds nothing
from another message (`HonestChunk`). That is a statement about the *input
relation*, and it excludes exactly one thing: a chunk spliced in from a
different encoding, which the real decoder turns into a wrong reconstruction
the MAC then rejects (`Failed`), while the model -- whose decoder returns
nothing for mixed sources -- keeps waiting. The two genuinely differ there,
so no relation can make that step refine; `LIMITATIONS.md` records it. In
this protocol a Braid message travels inside the ratchet's authenticated
channel, so splicing needs the channel's own key, not the network.

`EncoderSim` requires `next_chunk` to actually produce a chunk (`some`, not
`none`): `step_send`'s branches call `next_chunk` and need to know it
succeeds, and under the liveness bound that is asserting something true.
`add_chunk` rejecting a chunk (a duplicate, or an already-complete decoder)
stays a real possibility `DecoderSim` doesn't rule out. -/

def EncoderSim : Nat → tacenta_erasure.Encoder → Model.Braid.Encoder → Prop
  | 0, _, _ => True
  | n + 1, real, model =>
    ∃ chunk real', tacenta_erasure.Encoder.next_chunk real = ok (some chunk, real') ∧
      chunk.index.val = model.nextChunk.1.index ∧
        EncoderSim n real' model.nextChunk.2

/-- `chunk` is what `enc` emits after `i` further steps. -/
def NthChunk : Nat → tacenta_erasure.Encoder → tacenta_erasure.Chunk → Prop
  | 0, enc, chunk => ∃ enc', tacenta_erasure.Encoder.next_chunk enc = ok (some chunk, enc')
  | i + 1, enc, chunk =>
    ∃ c enc', tacenta_erasure.Encoder.next_chunk enc = ok (some c, enc') ∧ NthChunk i enc' chunk

/-- `real` is `enc0` advanced `k` steps. -/
def Stepped : Nat → tacenta_erasure.Encoder → tacenta_erasure.Encoder → Prop
  | 0, enc0, real => real = enc0
  | k + 1, enc0, real =>
    ∃ c enc', tacenta_erasure.Encoder.next_chunk enc0 = ok (some c, enc') ∧ Stepped k enc' real

/-- `chunk` is a codeword of `m`: the real encoder of a slice reading `m`
emits it, at the index it carries. Defined through the opaque encoder rather
than through any arithmetic, since the code is a boundary here. -/
def CodewordOf (m : Bytes) (chunk : tacenta_erasure.Chunk) : Prop :=
  ∃ (s : Slice Std.U8) (enc0 : tacenta_erasure.Encoder), sliceOf s = m ∧
    tacenta_erasure.Encoder.new s = ok enc0 ∧ NthChunk chunk.index.val enc0 chunk

def DecoderSim (m : Bytes) : Nat → tacenta_erasure.Decoder → Model.Braid.Decoder → Prop
  | 0, _, _ => True
  | n + 1, real, model =>
    (∀ (chunk : tacenta_erasure.Chunk) (advanced : Bool) (real' : tacenta_erasure.Decoder),
      CodewordOf m chunk →
      tacenta_erasure.Decoder.add_chunk real chunk = ok (advanced, real') →
      DecoderSim m n real' (model.addChunk ⟨m, chunk.index.val⟩)) ∧
    (∀ msg, tacenta_erasure.Decoder.message real = ok msg →
      msg.map vecOf = model.message)

/-- The real encoder is the model encoder's own: made from a slice reading the
model's `source`, advanced as many times as the model has emitted, and
agreeing with it for as many further steps as a `u16` index allows. -/
def EncoderRefines (real : tacenta_erasure.Encoder) (model : Model.Braid.Encoder) : Prop :=
  (∃ (s : Slice Std.U8) (enc0 : tacenta_erasure.Encoder), sliceOf s = model.source ∧
      tacenta_erasure.Encoder.new s = ok enc0 ∧ Stepped model.next enc0 real) ∧
  ∀ n, model.next + n ≤ 65536 → EncoderSim n real model

/-- The real decoder simulates the model decoder for every message the model
decoder could still be collecting. -/
def DecoderRefines (real : tacenta_erasure.Decoder) (model : Model.Braid.Decoder) : Prop :=
  ∀ m : Bytes, m.length = model.size → (∀ c ∈ model.chunks, c.source = m) →
    ∀ n, DecoderSim m n real model

def ErasureAgrees : Prop :=
  (∀ (s : Slice Std.U8), ∃ real, tacenta_erasure.Encoder.new s = ok real ∧
    EncoderRefines real (Model.Braid.encode (sliceOf s))) ∧
  (∀ (n : Usize), ∃ real, tacenta_erasure.Decoder.new n = ok real ∧
    DecoderRefines real (Model.Braid.Decoder.new n.val))

/-- A clone of an opaque erasure value *is* that value. Stated as equality
rather than as "simulates whatever the original did", because
`EncoderRefines` records where an encoder came from, which a behavioural
clause cannot transfer; and equality is what cloning a plain struct with no
interior mutability means. -/
def ErasureCloneAgrees : Prop :=
  (∀ (real real' : tacenta_erasure.Encoder),
    tacenta_erasure.Encoder.Insts.CoreCloneClone.clone real = ok real' → real' = real) ∧
  (∀ (real real' : tacenta_erasure.Decoder),
    tacenta_erasure.Decoder.Insts.CoreCloneClone.clone real = ok real' → real' = real)

/-- A completed decode is exactly as long as the decoder was sized for.
Named as a proposition for uniformity with the other boundary statements,
but it is a theorem, not a hypothesis (see below): the model's
`Decoder.message` checks the length, which is what the real decoder does.
Without that check it would hold only of a *size-coherent* `Kem`, one whose
operations produce outputs of its declared sizes (`toyKem` and ML-KEM are;
an arbitrary `Model.Braid.Kem` need not be). -/
def DecoderMessageLenAgrees : Prop :=
  ∀ (d : Model.Braid.Decoder) (bytes : Bytes), d.message = some bytes → bytes.length = d.size

/-- **Not a hypothesis.** The statement is `Model.Braid.Decoder.message_length`,
proved, and taken by nothing as an assumption; this theorem is its
discharge. -/
theorem decoderMessageLenAgrees : DecoderMessageLenAgrees :=
  fun d bytes h => Model.Braid.Decoder.message_length d bytes h

theorem epochBytes_agrees (epoch : Std.U64) :
    sliceOf (Array.to_slice (core.num.U64.to_be_bytes epoch)) =
      Model.Braid.epochBytes epoch.val := by
  apply List.ext_getElem
  · simp [sliceOf, Array.to_slice, core.num.U64.to_be_bytes, Model.Braid.epochBytes]
  · intro i h1 h2
    have hi : i < 8 := by
      simp only [Model.Braid.epochBytes, List.length_map, List.length_range] at h2; omega
    simp only [sliceOf, Array.to_slice, List.getElem_map, Model.Braid.epochBytes,
      List.getElem_range]
    have hib8 : i < epoch.bv.toBEBytes.length := by simp [BitVec.toBEBytes_length]; omega
    simp only [u8, core.num.U64.to_be_bytes, List.getElem_map]
    rw [← getElem!_pos _ i hib8, beByte_eq epoch.bv i hi]
    apply UInt8.toNat.inj
    simp only [UInt8.toNat_ofNat', UScalar.val, setWidth8_toNat,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_mod _ _

/-! ## The abstraction: real `State`/`Auth` to `Model.Braid`'s

`Auth` is a direct field-for-field correspondence. `State` needs more: the
real machine's 12 constructors line up one-for-one with the model's, but
several real fields are *opaque* (`IncrementalKeyPair`, `EncapsState`,
`Encoder`, `Decoder`) where the model tracks plain `Bytes` or its own
`Encoder`/`Decoder`. Three small relations carry that weight, each used
across whichever constructors hold that piece:

- `KeyPairRefines K ikp dk`: this key pair decapsulates like `K.decaps dk`.
  Every state past `KeysUnsampled` that still holds an `IncrementalKeyPair`
  needs exactly this and nothing more. `header`/`ek_vector` are only
  relevant once, right when the key pair is fresh.
- `FreshKeyPairRefines K ikp dk ekVector` adds that one-time `header`/
  `ek_vector` correspondence, for `KeysSampled` alone.
- `EncapsRefines K es ekSeed encapsSecret`: this encapsulation state
  finishes like `K.encaps2 encapsSecret ekSeed`.

Two bytes fields the real states are seen to drop along the way have no
real-side counterpart in those later constructors: `ekSeed`, once a header
is sent (folded into the encoder's queued bytes), and `hek`, once
`encapsulate1` runs (folded into the opaque `EncapsState`). They stay bound in the
model side of the relevant clause with no corresponding real witness, which
is exactly the shape `KemAgrees`'s own per-key-pair existential already has. -/

def AuthOf (a : Auth) : Model.Braid.Auth := ⟨keyOf a.root_key, keyOf a.mac_key⟩

def KeyPairRefines (K : Model.Braid.Kem) (ikp : tacenta_kem.IncrementalKeyPair)
    (dk : Bytes) : Prop :=
  ∀ ct1 ct2 : Slice Std.U8, ct1.length = K.ct1Size → ct2.length = K.ct2Size →
    ∃ raw, tacenta_kem.IncrementalKeyPair.decapsulate ikp ct1 ct2 =
      ok (core.result.Result.Ok raw) ∧ keyOf raw = K.decaps dk (sliceOf ct1) (sliceOf ct2)

def FreshKeyPairRefines (K : Model.Braid.Kem) (ikp : tacenta_kem.IncrementalKeyPair)
    (dk ekVector : Bytes) : Prop :=
  KeyPairRefines K ikp dk ∧
  (∃ v, tacenta_kem.IncrementalKeyPair.ek_vector ikp = ok v ∧ vecOf v = ekVector) ∧
  (∃ h ekSeed, tacenta_kem.IncrementalKeyPair.header ikp = ok h ∧
    vecOf h = ekSeed ++ K.hashEk ekSeed ekVector)

def EncapsRefines (K : Model.Braid.Kem) (es : tacenta_kem.EncapsState)
    (ekSeed encapsSecret : Bytes) : Prop :=
  ∀ ekVector : Slice Std.U8, ekVector.length = K.ekSize →
    ∃ ct2raw, tacenta_kem.encapsulate2 es ekVector = ok (core.result.Result.Ok ct2raw) ∧
      vecOf ct2raw = K.encaps2 encapsSecret ekSeed (sliceOf ekVector)

theorem Stepped.succ {k : Nat} {enc0 real real' : tacenta_erasure.Encoder}
    {c : tacenta_erasure.Chunk} (hs : Stepped k enc0 real)
    (h : tacenta_erasure.Encoder.next_chunk real = ok (some c, real')) :
    Stepped (k + 1) enc0 real' := by
  induction k generalizing enc0 with
  | zero => subst hs; exact ⟨c, real', h, rfl⟩
  | succ k ih =>
    obtain ⟨c0, e1, h0, hs'⟩ := hs
    exact ⟨c0, e1, h0, ih hs'⟩

theorem Stepped.nthChunk {k : Nat} {enc0 real real' : tacenta_erasure.Encoder}
    {c : tacenta_erasure.Chunk} (hs : Stepped k enc0 real)
    (h : tacenta_erasure.Encoder.next_chunk real = ok (some c, real')) :
    NthChunk k enc0 c := by
  induction k generalizing enc0 with
  | zero => subst hs; exact ⟨real', h⟩
  | succ k ih =>
    obtain ⟨c0, e1, h0, hs'⟩ := hs
    exact ⟨c0, e1, h0, ih hs'⟩

/-- Unfolds `EncoderRefines` by one `next_chunk` call, which needs the encoder
live. Yields the index correspondence, that the chunk is a codeword of the
model's source, and the relation one step on. `next_chunk` is a pure function
of `real`, so whichever `n` a use of `EncoderRefines` picks to learn *this*
call's outcome, the outcome itself doesn't depend on `n`. -/
theorem EncoderRefines.step {real : tacenta_erasure.Encoder} {model : Model.Braid.Encoder}
    (hr : EncoderRefines real model) (hlive : model.next < 65536)
    {chunk : tacenta_erasure.Chunk} {real' : tacenta_erasure.Encoder}
    (h : tacenta_erasure.Encoder.next_chunk real = ok (some chunk, real')) :
    chunk.index.val = model.nextChunk.1.index ∧ CodewordOf model.source chunk ∧
      EncoderRefines real' model.nextChunk.2 := by
  obtain ⟨⟨s, enc0, hs, hnew, hstep⟩, hsim⟩ := hr
  have key : ∀ n, model.next + (n + 1) ≤ 65536 →
      chunk.index.val = model.nextChunk.1.index ∧ EncoderSim n real' model.nextChunk.2 := by
    intro n hn
    obtain ⟨chunk1, real1, hchunk1, hidx1, hsim1⟩ := hsim (n + 1) hn
    rw [h] at hchunk1
    simp only [ok.injEq, Prod.mk.injEq, Option.some.injEq] at hchunk1
    obtain ⟨hc, hr1⟩ := hchunk1
    subst hc; subst hr1
    exact ⟨hidx1, hsim1⟩
  have hidx := (key 0 (by omega)).1
  refine ⟨hidx, ⟨s, enc0, hs, hnew, ?_⟩,
    ⟨s, enc0, hs, hnew, Stepped.succ hstep h⟩,
    fun n hn => (key n (by simp only [Model.Braid.Encoder.nextChunk] at hn; omega)).2⟩
  have hidx' : chunk.index.val = model.next := by
    simpa [Model.Braid.Encoder.nextChunk] using hidx
  rw [hidx']
  exact Stepped.nthChunk hstep h

theorem Model.Braid.Decoder.addChunk_size (d : Model.Braid.Decoder) (c : Model.Braid.Chunk) :
    (d.addChunk c).size = d.size := by
  unfold Model.Braid.Decoder.addChunk; split <;> rfl

theorem Model.Braid.Decoder.addChunk_sources (d : Model.Braid.Decoder) (c : Model.Braid.Chunk)
    (m : Bytes) (hd : ∀ x ∈ d.chunks, x.source = m) (hc : c.source = m) :
    ∀ x ∈ (d.addChunk c).chunks, x.source = m := by
  unfold Model.Braid.Decoder.addChunk; split
  · exact hd
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hc
    · exact hd x hx

theorem Model.Braid.Decoder.addChunk_chunks_ne_nil (d : Model.Braid.Decoder)
    (c : Model.Braid.Chunk) : (d.addChunk c).chunks ≠ [] := by
  unfold Model.Braid.Decoder.addChunk; split
  · rename_i h; intro hnil; rw [hnil] at h; simp at h
  · simp

/-- Feeding a decoder one honest chunk carries the relation over to the model
decoder holding the model chunk. `DecoderRefines.add_message` adds what the
real decoder then says. -/
theorem DecoderRefines.add {real real' : tacenta_erasure.Decoder}
    {model : Model.Braid.Decoder} (hr : DecoderRefines real model)
    {chunk : tacenta_erasure.Chunk} {advanced : Bool} {mc : Model.Braid.Chunk}
    (hsame : ∀ c ∈ model.chunks, c.source = mc.source)
    (hcw : CodewordOf mc.source chunk) (hidx : chunk.index.val = mc.index)
    (hadd : tacenta_erasure.Decoder.add_chunk real chunk = ok (advanced, real')) :
    DecoderRefines real' (model.addChunk mc) := by
  have hmc : (⟨mc.source, chunk.index.val⟩ : Model.Braid.Chunk) = mc := by
    cases mc; simp_all
  intro m hm hall n
  have hne := Model.Braid.Decoder.addChunk_chunks_ne_nil model mc
  have hmeq : m = mc.source := by
    have hsrc := Model.Braid.Decoder.addChunk_sources model mc mc.source hsame rfl
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
    rw [← hall x hx, hsrc x hx]
  subst hmeq
  -- The size fit is the post-state's own: `addChunk` keeps the size.
  have hfit : mc.source.length = model.size := by
    rw [← Model.Braid.Decoder.addChunk_size model mc]; exact hm
  have := (hr mc.source hfit hsame (n + 1)).1 chunk advanced real' hcw hadd
  rwa [hmc] at this

/-- Feeding a decoder one honest chunk: the relation carries over to the model
decoder holding the model chunk, and what the real decoder then says its
message is agrees with the model's. The message the real chunk encodes is
the message the model chunk names (`hcw`), of the decoder's size (`hfit`),
and nothing from another message is already in the decoder (`hsame`) --
`HonestChunk`, at the theorem level. -/
theorem DecoderRefines.add_message {real real' : tacenta_erasure.Decoder}
    {model : Model.Braid.Decoder} (hr : DecoderRefines real model)
    {chunk : tacenta_erasure.Chunk} {advanced : Bool} {mc : Model.Braid.Chunk}
    (hfit : mc.source.length = model.size)
    (hsame : ∀ c ∈ model.chunks, c.source = mc.source)
    (hcw : CodewordOf mc.source chunk) (hidx : chunk.index.val = mc.index)
    (hadd : tacenta_erasure.Decoder.add_chunk real chunk = ok (advanced, real'))
    {omsg : Option (alloc.vec.Vec Std.U8)}
    (hmsg : tacenta_erasure.Decoder.message real' = ok omsg) :
    DecoderRefines real' (model.addChunk mc) ∧ omsg.map vecOf = (model.addChunk mc).message := by
  have hr' := DecoderRefines.add hr hsame hcw hidx hadd
  refine ⟨hr', (hr' mc.source ?_ ?_ 1).2 omsg hmsg⟩
  · rw [Model.Braid.Decoder.addChunk_size]; exact hfit
  · exact Model.Braid.Decoder.addChunk_sources model mc mc.source hsame rfl

/-- `State.clone` clones every opaque field it holds; these four lemmas are
what let `State.clone_refines` carry each field's `*Refines` fact across its
own clone, given the four `*CloneAgrees` assumptions above. -/
theorem KeyPairRefines.clone (hcl : KemCloneAgrees) {K : Model.Braid.Kem}
    {ikp ikp' : tacenta_kem.IncrementalKeyPair} {dk : Bytes}
    (h : tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone ikp = ok ikp')
    (hr : KeyPairRefines K ikp dk) : KeyPairRefines K ikp' dk := by
  intro ct1 ct2 h1 h2
  obtain ⟨raw, hraw, hval⟩ := hr ct1 ct2 h1 h2
  exact ⟨raw, (hcl.1 ikp ikp' h).2.2 ct1 ct2 raw hraw, hval⟩

theorem FreshKeyPairRefines.clone (hcl : KemCloneAgrees) {K : Model.Braid.Kem}
    {ikp ikp' : tacenta_kem.IncrementalKeyPair} {dk ekVector : Bytes}
    (h : tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone ikp = ok ikp')
    (hr : FreshKeyPairRefines K ikp dk ekVector) :
    FreshKeyPairRefines K ikp' dk ekVector := by
  obtain ⟨hkp, ⟨v, hv, hveq⟩, ⟨hd, ekSeed, hhd, hheq⟩⟩ := hr
  have hclkp := hcl.1 ikp ikp' h
  exact ⟨KeyPairRefines.clone hcl h hkp, ⟨v, hclkp.2.1 v hv, hveq⟩,
    ⟨hd, ekSeed, hclkp.1 hd hhd, hheq⟩⟩

theorem EncapsRefines.clone (hcl : KemCloneAgrees) {K : Model.Braid.Kem}
    {es es' : tacenta_kem.EncapsState} {ekSeed encapsSecret : Bytes}
    (h : tacenta_kem.EncapsState.Insts.CoreCloneClone.clone es = ok es')
    (hr : EncapsRefines K es ekSeed encapsSecret) :
    EncapsRefines K es' ekSeed encapsSecret := by
  intro ekVector hlen
  obtain ⟨ct2raw, hct2, hval⟩ := hr ekVector hlen
  exact ⟨ct2raw, hcl.2 es es' h ekVector ct2raw hct2, hval⟩

theorem EncoderRefines.clone (hcl : ErasureCloneAgrees) {real real' : tacenta_erasure.Encoder}
    {model : Model.Braid.Encoder}
    (h : tacenta_erasure.Encoder.Insts.CoreCloneClone.clone real = ok real')
    (hr : EncoderRefines real model) : EncoderRefines real' model := by
  rw [hcl.1 real real' h]; exact hr

theorem DecoderRefines.clone (hcl : ErasureCloneAgrees) {real real' : tacenta_erasure.Decoder}
    {model : Model.Braid.Decoder}
    (h : tacenta_erasure.Decoder.Insts.CoreCloneClone.clone real = ok real')
    (hr : DecoderRefines real model) : DecoderRefines real' model := by
  rw [hcl.2 real real' h]; exact hr

theorem Auth.clone_refines (self : Auth) :
    Auth.Insts.CoreCloneClone.clone self ⦃ fun r => AuthOf r = AuthOf self ⦄ := by
  unfold Auth.Insts.CoreCloneClone.clone
  step*
  simp_all [AuthOf]

def StateRefines (K : Model.Braid.Kem) : State → Model.Braid.BraidState → Prop
  | .KeysUnsampled epoch auth, .keysUnsampled e a =>
    epoch.val = e ∧ AuthOf auth = a
  | .KeysSampled epoch auth ikp enc, .keysSampled e a dk ekVector hdrEnc =>
    epoch.val = e ∧ AuthOf auth = a ∧
    FreshKeyPairRefines K ikp dk ekVector ∧ EncoderRefines enc hdrEnc
  | .HeaderSent epoch auth ikp ct1Dec enc, .headerSent e a dk ct1DecM ekEncM =>
    epoch.val = e ∧ AuthOf auth = a ∧ KeyPairRefines K ikp dk ∧
    DecoderRefines ct1Dec ct1DecM ∧ ct1DecM.size = K.ct1Size ∧ EncoderRefines enc ekEncM
  | .Ct1Received epoch auth ikp ct1 enc, .ct1Received e a dk ct1M ekEncM =>
    epoch.val = e ∧ AuthOf auth = a ∧ KeyPairRefines K ikp dk ∧
    vecOf ct1 = ct1M ∧ ct1M.length = K.ct1Size ∧ EncoderRefines enc ekEncM
  | .EkSentCt1Received epoch auth ikp ct1 dec, .ekSentCt1Received e a dk ct1M ct2DecM =>
    epoch.val = e ∧ AuthOf auth = a ∧ KeyPairRefines K ikp dk ∧
    vecOf ct1 = ct1M ∧ ct1M.length = K.ct1Size ∧ DecoderRefines dec ct2DecM ∧
    ct2DecM.size = K.ct2Size + Model.Braid.macSize
  | .NoHeaderReceived epoch auth dec, .noHeaderReceived e a hdrDecM =>
    epoch.val = e ∧ AuthOf auth = a ∧ DecoderRefines dec hdrDecM ∧
    hdrDecM.size = Model.Braid.headerSize + Model.Braid.macSize
  | .HeaderReceived epoch auth hdr dec, .headerReceived e a ekSeedM hekM ekDecM =>
    epoch.val = e ∧ AuthOf auth = a ∧ vecOf hdr = ekSeedM ++ hekM ∧ ekSeedM.length = 32 ∧
    hekM.length = 32 ∧ DecoderRefines dec ekDecM ∧ ekDecM.size = K.ekSize
  | .Ct1Sampled epoch auth header es ct1 enc dec,
      .ct1Sampled e a ekSeedM hekM encapsSecretM ct1M ct1EncM ekDecM =>
    epoch.val = e ∧ AuthOf auth = a ∧ vecOf header = ekSeedM ++ hekM ∧ ekSeedM.length = 32 ∧
    hekM.length = 32 ∧ EncapsRefines K es ekSeedM encapsSecretM ∧ vecOf ct1 = ct1M ∧
    EncoderRefines enc ct1EncM ∧ DecoderRefines dec ekDecM ∧ ekDecM.size = K.ekSize
  | .EkReceivedCt1Sampled epoch auth es ct1 ekVector enc,
      .ekReceivedCt1Sampled e a encapsSecretM ct1M ekSeedM ekVectorM ct1EncM =>
    epoch.val = e ∧ AuthOf auth = a ∧
    EncapsRefines K es ekSeedM encapsSecretM ∧
    vecOf ct1 = ct1M ∧ vecOf ekVector = ekVectorM ∧ ekVectorM.length = K.ekSize ∧
    EncoderRefines enc ct1EncM
  | .Ct1Acknowledged epoch auth header es ct1 dec,
      .ct1Acknowledged e a ekSeedM hekM encapsSecretM ct1M ekDecM =>
    epoch.val = e ∧ AuthOf auth = a ∧ vecOf header = ekSeedM ++ hekM ∧ ekSeedM.length = 32 ∧
    hekM.length = 32 ∧ EncapsRefines K es ekSeedM encapsSecretM ∧ vecOf ct1 = ct1M ∧
    DecoderRefines dec ekDecM ∧ ekDecM.size = K.ekSize
  | .Ct2Sampled epoch auth enc, .ct2Sampled e a ct2EncM =>
    epoch.val = e ∧ AuthOf auth = a ∧ EncoderRefines enc ct2EncM
  | .Failed, .failed => True
  | _, _ => False

/-- The encoder a model state is emitting from, if any. -/
def EncoderOf : Model.Braid.BraidState → Option Model.Braid.Encoder
  | .keysSampled _ _ _ _ e => some e
  | .headerSent _ _ _ _ e => some e
  | .ct1Received _ _ _ _ e => some e
  | .ct1Sampled _ _ _ _ _ _ e _ => some e
  | .ekReceivedCt1Sampled _ _ _ _ _ _ e => some e
  | .ct2Sampled _ _ e => some e
  | _ => none

/-- The state's encoder, if it has one, has codewords left to emit: the
crate's liveness limit (a `u16` index), stated as a precondition of sending
rather than assumed of every encoder (see the erasure boundary above). -/
def EncodersLive (model : Model.Braid.BraidState) : Prop :=
  ∀ e, EncoderOf model = some e → e.next < 65536

/-- A chunk fits a decoder: its source is a message of the decoder's size,
and the decoder holds nothing from another message. -/
def ChunkFits (d : Model.Braid.Decoder) (mc : Model.Braid.Chunk) : Prop :=
  mc.source.length = d.size ∧ ∀ c ∈ d.chunks, c.source = mc.source

/-- The incoming chunk is honest for the decoder it will be fed to, if any.
`Model.Braid.receive` feeds a chunk to a decoder in exactly six
state/message-type pairs, and only when the epochs match; this assumes
nothing anywhere else, so a stale or wrong-type chunk the model ignores
(a retransmitted header at `headerReceived`, a previous epoch's `ct2`)
costs the theorem nothing; assuming a fit for every data-bearing message
would leave the theorem inapplicable to those benign, reachable steps.
Whether the chunk is a codeword of
its source is `MsgRefines`'s business; the two states that build a fresh
decoder for the very chunk they receive (`keysSampled` on `ct1`,
`ct1Received` on `ct2`) need nothing here, since an empty decoder fits any
message and `DecoderRefines.add` derives the size from the model. -/
def HonestChunk (model : Model.Braid.BraidState) (modelMsg : Model.Braid.Msg) : Prop :=
  ∀ mc, modelMsg.data = some mc → modelMsg.epoch = model.epoch →
    match model, modelMsg.type with
    | .headerSent _ _ _ d _, .ct1 => ChunkFits d mc
    | .ekSentCt1Received _ _ _ _ d, .ct2 => ChunkFits d mc
    | .noHeaderReceived _ _ d, .hdr => ChunkFits d mc
    | .ct1Sampled _ _ _ _ _ _ _ d, .ek => ChunkFits d mc
    | .ct1Sampled _ _ _ _ _ _ _ d, .ekCt1Ack => ChunkFits d mc
    | .ct1Acknowledged _ _ _ _ _ _ d, .ekCt1Ack => ChunkFits d mc
    | _, _ => True

/-- A `Vec`'s slice view has the length of its bytes. -/
theorem deref_length (v : alloc.vec.Vec Std.U8) : v.deref.length = (vecOf v).length := by
  simp [vecOf, alloc.vec.Vec.deref]

/-! ## `info`, `Auth`, and `kdf_ok` refine their model counterparts -/

theorem protocolInfo_length : Model.Braid.protocolInfo.length = 25 := by
  simp [← protocolInfo_agrees, sliceOf, global_simps]

theorem authUpdateLabel_length : Model.Braid.authUpdateLabel.length = 21 := by
  simp [← authUpdate_agrees, sliceOf, global_simps]

theorem ekHeaderLabel_length : Model.Braid.ekHeaderLabel.length = 9 := by
  simp [← ekHeader_agrees, sliceOf, global_simps]

theorem ciphertextLabel_length : Model.Braid.ciphertextLabel.length = 11 := by
  simp [← ciphertext_agrees, sliceOf, global_simps]

theorem sckaKeyLabel_length : Model.Braid.sckaKeyLabel.length = 9 := by
  simp [← sckaKey_agrees, sliceOf, global_simps]

theorem epochBytes_length (epoch : Nat) : (Model.Braid.epochBytes epoch).length = 8 := by
  simp [Model.Braid.epochBytes]

theorem info_refines (label : Slice Std.U8) (labelBytes : Bytes)
    (hlabel : sliceOf label = labelBytes) (epoch : Std.U64)
    (hlen : label.length + 64 ≤ Usize.max) :
    info label epoch ⦃ fun r =>
      vecOf r = Model.Braid.protocolInfo ++ labelBytes ++ Model.Braid.epochBytes epoch.val ⦄ := by
  have hpi : (PROTOCOL_INFO : Slice Std.U8).length = 25 := by
    simp only [global_simps, Array.length_to_slice]; scalar_tac
  have hcap : ∀ (i : Usize), (alloc.vec.Vec.with_capacity Std.U8 i).val = [] := by
    intro i
    simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
  have e3 : List.map u8 (List.map UScalar.mk epoch.bv.toBEBytes) = Model.Braid.epochBytes epoch.val := by
    have := epochBytes_agrees epoch
    simpa [sliceOf, Array.to_slice, core.num.U64.to_be_bytes, u8] using this
  have e1 : List.map u8 (PROTOCOL_INFO : Slice Std.U8).val = Model.Braid.protocolInfo := by
    have := protocolInfo_agrees; simpa [sliceOf] using this
  have e2 : List.map u8 label.val = labelBytes := by
    have := hlabel; simpa [sliceOf] using this
  unfold info
  step*
  all_goals (try simp_all)
  all_goals (try (simp only [vecOf, r_post, List.map_append, List.map_map, e1, e2, e3]))

theorem Auth.update_refines (hkdf : BraidHkdfAgrees) (hz : Tacenta.BraidT1.ZeroizingArrayRoundTrip)
    (self : Auth) (epoch : Std.U64) (key : Slice Std.U8) :
    Auth.update self epoch key ⦃ fun r =>
      AuthOf r = Model.Braid.Auth.update (AuthOf self) epoch.val (sliceOf key) ⦄ := by
  have hau : (AUTH_UPDATE : Slice Std.U8).length = 21 := by
    simp only [global_simps, Array.length_to_slice]; scalar_tac
  unfold Auth.update
  step*
  step with info_refines AUTH_UPDATE Model.Braid.authUpdateLabel authUpdate_agrees epoch (by simp [hau]; scalar_tac)
  obtain ⟨okm, hokm, hokmval⟩ := hkdf 64#usize s key v.deref
  simp only [hokm]
  -- The 64-byte output passes through the `Zeroizing` wrapper and straight
  -- back out (`ZeroizingArrayRoundTrip`) before the two key slots are copied.
  step with Tacenta.BraidT1.zeroizing_new_spec hz
  step*
  step with Tacenta.BraidT1.zeroizing_deref_spec ‹_›
  step*
  simp_all [AuthOf, Model.Braid.Auth.update, vecOf, keyOf, sliceOf, alloc.vec.Vec.deref]

theorem Auth.mac_hdr_refines (hmac : BraidHmacAgrees) (self : Auth) (epoch : Std.U64)
    (hdr : Slice Std.U8) (hdrBytes : Bytes) (hhdr : sliceOf hdr = hdrBytes)
    (hlen : hdr.length + 64 ≤ Usize.max) :
    Auth.mac_hdr self epoch hdr ⦃ fun r =>
      keyOf r = Model.Braid.Auth.macHdr (AuthOf self) epoch.val hdrBytes ⦄ := by
  have heh : (EK_HEADER : Slice Std.U8).length = 9 := by
    simp only [global_simps, Array.length_to_slice]; scalar_tac
  unfold Auth.mac_hdr
  step*
  step with info_refines EK_HEADER Model.Braid.ekHeaderLabel ekHeader_agrees epoch (by simp [heh]; scalar_tac)
  all_goals (try step*)
  all_goals (try (have hdl := congrArg List.length data_post; simp [vecOf, List.length_map, protocolInfo_length, ekHeaderLabel_length, epochBytes_length] at hdl; scalar_tac))
  all_goals (try (obtain ⟨out, hout, houtval⟩ := hmac s data1.deref; simp only [hout]))
  all_goals (try step*)
  all_goals (try simp_all [AuthOf, Model.Braid.Auth.macHdr, vecOf, keyOf, sliceOf, alloc.vec.Vec.deref])

theorem Auth.mac_ct_refines (hmac : BraidHmacAgrees) (self : Auth) (epoch : Std.U64)
    (ct1 ct2 : Slice Std.U8) (ct1Bytes ct2Bytes : Bytes) (hct1 : sliceOf ct1 = ct1Bytes)
    (hct2 : sliceOf ct2 = ct2Bytes) (hlen : ct1.length + ct2.length + 96 ≤ Usize.max) :
    Auth.mac_ct self epoch ct1 ct2 ⦃ fun r =>
      keyOf r = Model.Braid.Auth.macCt (AuthOf self) epoch.val (ct1Bytes ++ ct2Bytes) ⦄ := by
  have hct : (CIPHERTEXT : Slice Std.U8).length = 11 := by
    simp only [global_simps, Array.length_to_slice]; scalar_tac
  unfold Auth.mac_ct
  step*
  step with info_refines CIPHERTEXT Model.Braid.ciphertextLabel ciphertext_agrees epoch (by simp [hct]; scalar_tac)
  all_goals (try step*)
  all_goals (try (have hdl := congrArg List.length data_post; simp [vecOf, List.length_map, protocolInfo_length, ciphertextLabel_length, epochBytes_length] at hdl; scalar_tac))
  all_goals (try (have hd := congrArg List.length data_post; have hd1 := congrArg List.length data1_post; simp [vecOf, List.length_map, protocolInfo_length, ciphertextLabel_length, epochBytes_length] at hd hd1; scalar_tac))
  all_goals (try (obtain ⟨out, hout, houtval⟩ := hmac s data2.deref; simp only [hout]))
  all_goals (try step*)
  all_goals (try simp_all [AuthOf, Model.Braid.Auth.macCt, vecOf, keyOf, sliceOf, alloc.vec.Vec.deref])

theorem kdf_ok_refines (hkdf : BraidHkdfAgrees) (shared_secret : Slice Std.U8)
    (ssBytes : Bytes) (hss : sliceOf shared_secret = ssBytes) (epoch : Std.U64) :
    kdf_ok shared_secret epoch ⦃ fun r =>
      keyOf r = Model.Braid.kdfOk ssBytes epoch.val ⦄ := by
  have hsk : (SCKA_KEY : Slice Std.U8).length = 9 := by
    simp only [global_simps, Array.length_to_slice]; scalar_tac
  unfold kdf_ok
  step*
  step with info_refines SCKA_KEY Model.Braid.sckaKeyLabel sckaKey_agrees epoch (by simp [hsk]; scalar_tac)
  all_goals (try (obtain ⟨out, hout, houtval⟩ := hkdf 32#usize s shared_secret v.deref; simp only [hout]))
  all_goals (try step*)
  all_goals (try simp_all [Model.Braid.kdfOk, vecOf, keyOf, sliceOf, u8, alloc.vec.Vec.deref])

/-- `Auth.update` only ever reads `self.root_key` (`Model.Braid.Auth.update`
does the same, ignoring `a.macKey`), so the all-zero `mac_key` this starts
with need not match the model's all-zero `[]` for `Auth.init` to refine. -/
theorem Auth.init_refines (hkdf : BraidHkdfAgrees) (hz : Tacenta.BraidT1.ZeroizingArrayRoundTrip)
    (epoch : Std.U64) (secret : Slice Std.U8) :
    Auth.init epoch secret ⦃ fun r =>
      AuthOf r = Model.Braid.Auth.init epoch.val (sliceOf secret) ⦄ := by
  unfold Auth.init Model.Braid.Auth.init
  step with Auth.update_refines hkdf hz ⟨Array.repeat 32#usize 0#u8, Array.repeat 32#usize 0#u8⟩ epoch secret
  simp_all [AuthOf, keyOf, Array.repeat, Model.Braid.Auth.update, u8, List.replicate]

theorem State.epoch_refines (K : Model.Braid.Kem) (self : State) (model : Model.Braid.BraidState)
    (hrel : StateRefines K self model) :
    State.epoch self ⦃ fun r => r.val = model.epoch ⦄ := by
  unfold State.epoch
  cases self <;> cases model <;> simp_all [StateRefines, Model.Braid.BraidState.epoch]

theorem State.clone_refines (hkcl : KemCloneAgrees) (hecl : ErasureCloneAgrees)
    (henc : Tacenta.BraidT1.EncoderCloneTotal) (hdec : Tacenta.BraidT1.DecoderCloneTotal)
    (hkp : Tacenta.BraidT1.KeyPairCloneTotal) (hes : Tacenta.BraidT1.EncapsStateCloneTotal)
    {K : Model.Braid.Kem} {self : State} {model : Model.Braid.BraidState}
    (hrel : StateRefines K self model) :
    State.Insts.CoreCloneClone.clone self ⦃ fun r => StateRefines K r model ⦄ := by
  rcases self with _|_|_|_|_|_|_|_|_|_|_|_ <;> cases model <;>
    simp only [StateRefines] at hrel <;>
    try exact hrel.elim
  case KeysUnsampled.keysUnsampled =>
    obtain ⟨he, ha⟩ := hrel
    simp only [State.Insts.CoreCloneClone.clone, lift]
    step*
    step with Auth.clone_refines
    simp_all [StateRefines]
  case KeysSampled.keysSampled =>
    obtain ⟨he, ha, hfkp, hencr⟩ := hrel
    simp only [State.Insts.CoreCloneClone.clone, lift]
    step*
    step with Auth.clone_refines
    obtain ⟨ikp', hikp'⟩ := hkp ‹_›
    simp only [hikp']
    obtain ⟨enc', henc'⟩ := henc ‹_›
    simp only [henc']
    have := FreshKeyPairRefines.clone hkcl hikp' hfkp
    have := EncoderRefines.clone hecl henc' hencr
    simp_all [StateRefines]
  case HeaderSent.headerSent =>
    obtain ⟨he, ha, hkpr, hdr, hct1size, her⟩ := hrel
    simp only [State.Insts.CoreCloneClone.clone, lift]
    step*
    step with Auth.clone_refines
    obtain ⟨ikp', hikp'⟩ := hkp ‹_›
    simp only [hikp']
    obtain ⟨dec', hdec'⟩ := hdec ‹_›
    simp only [hdec']
    obtain ⟨enc', henc'⟩ := henc ‹_›
    simp only [henc']
    have := KeyPairRefines.clone hkcl hikp' hkpr
    have := DecoderRefines.clone hecl hdec' hdr
    have := EncoderRefines.clone hecl henc' her
    simp_all [StateRefines]
  case Ct1Received.ct1Received =>
    obtain ⟨he, ha, hkpr, hct1, hct1len, her⟩ := hrel
    simp only [State.Insts.CoreCloneClone.clone, lift]
    step*
    step with Auth.clone_refines
    obtain ⟨ikp', hikp'⟩ := hkp ‹_›
    simp only [hikp']
    step with Tacenta.BraidT1.vecU8_clone_no_panic
    obtain ⟨enc', henc'⟩ := henc ‹_›
    simp only [henc']
    have := KeyPairRefines.clone hkcl hikp' hkpr
    have := EncoderRefines.clone hecl henc' her
    simp_all [StateRefines]
  case EkSentCt1Received.ekSentCt1Received =>
    obtain ⟨he, ha, hkpr, hct1, hct1len, hdr, hdsize⟩ := hrel
    simp only [State.Insts.CoreCloneClone.clone, lift]
    step*
    step with Auth.clone_refines
    obtain ⟨ikp', hikp'⟩ := hkp ‹_›
    simp only [hikp']
    step with Tacenta.BraidT1.vecU8_clone_no_panic
    obtain ⟨dec', hdec'⟩ := hdec ‹_›
    simp only [hdec']
    have := KeyPairRefines.clone hkcl hikp' hkpr
    have := DecoderRefines.clone hecl hdec' hdr
    simp_all [StateRefines]
  case NoHeaderReceived.noHeaderReceived =>
    obtain ⟨he, ha, hdr, hdsize⟩ := hrel
    simp only [State.Insts.CoreCloneClone.clone, lift]
    step*
    step with Auth.clone_refines
    obtain ⟨dec', hdec'⟩ := hdec ‹_›
    simp only [hdec']
    have := DecoderRefines.clone hecl hdec' hdr
    simp_all [StateRefines]
  case HeaderReceived.headerReceived =>
    obtain ⟨he, ha, hhdr, hlen32, hhek32, hdr, heksize⟩ := hrel
    simp only [State.Insts.CoreCloneClone.clone, lift]
    step*
    step with Auth.clone_refines
    step with Tacenta.BraidT1.vecU8_clone_no_panic
    obtain ⟨dec', hdec'⟩ := hdec ‹_›
    simp only [hdec']
    have := DecoderRefines.clone hecl hdec' hdr
    simp_all [StateRefines]
  case Ct1Sampled.ct1Sampled =>
    obtain ⟨he, ha, hekSeed, hlen32, hhek32, hencaps, hct1, henr, hdr, heksize⟩ := hrel
    simp only [State.Insts.CoreCloneClone.clone, lift]
    step*
    step with Auth.clone_refines
    step with Tacenta.BraidT1.vecU8_clone_no_panic
    obtain ⟨es', hes'⟩ := hes ‹_›
    simp only [hes']
    step with Tacenta.BraidT1.vecU8_clone_no_panic
    obtain ⟨enc', henc'⟩ := henc ‹_›
    simp only [henc']
    obtain ⟨dec', hdec'⟩ := hdec ‹_›
    simp only [hdec']
    have := EncapsRefines.clone hkcl hes' hencaps
    have := EncoderRefines.clone hecl henc' henr
    have := DecoderRefines.clone hecl hdec' hdr
    simp_all [StateRefines]
  case EkReceivedCt1Sampled.ekReceivedCt1Sampled =>
    obtain ⟨he, ha, hencaps, hct1, hekVector, hekvlen, henr⟩ := hrel
    simp only [State.Insts.CoreCloneClone.clone, lift]
    step*
    step with Auth.clone_refines
    obtain ⟨es', hes'⟩ := hes ‹_›
    simp only [hes']
    step with Tacenta.BraidT1.vecU8_clone_no_panic
    step with Tacenta.BraidT1.vecU8_clone_no_panic
    obtain ⟨enc', henc'⟩ := henc ‹_›
    simp only [henc']
    have := EncapsRefines.clone hkcl hes' hencaps
    have := EncoderRefines.clone hecl henc' henr
    simp_all [StateRefines]
  case Ct1Acknowledged.ct1Acknowledged =>
    obtain ⟨he, ha, hekSeed, hlen32, hhek32, hencaps, hct1, hdr, heksize⟩ := hrel
    simp only [State.Insts.CoreCloneClone.clone, lift]
    step*
    step with Auth.clone_refines
    step with Tacenta.BraidT1.vecU8_clone_no_panic
    obtain ⟨es', hes'⟩ := hes ‹_›
    simp only [hes']
    step with Tacenta.BraidT1.vecU8_clone_no_panic
    obtain ⟨dec', hdec'⟩ := hdec ‹_›
    simp only [hdec']
    have := EncapsRefines.clone hkcl hes' hencaps
    have := DecoderRefines.clone hecl hdec' hdr
    simp_all [StateRefines]
  case Ct2Sampled.ct2Sampled =>
    obtain ⟨he, ha, her⟩ := hrel
    simp only [State.Insts.CoreCloneClone.clone, lift]
    step*
    step with Auth.clone_refines
    obtain ⟨enc', henc'⟩ := henc ‹_›
    simp only [henc']
    have := EncoderRefines.clone hecl henc' her
    simp_all [StateRefines]
  case Failed.failed =>
    simp only [State.Insts.CoreCloneClone.clone]
    simp [StateRefines]

/-! ## `Braid`'s thin wrappers -/

theorem Braid.epoch_refines (K : Model.Braid.Kem) (self : Braid) (model : Model.Braid.BraidState)
    (hrel : StateRefines K self.state model) :
    Braid.epoch self ⦃ fun r => r.val = model.epoch ⦄ := by
  unfold Braid.epoch
  step with State.epoch_refines K self.state model hrel
  exact r_post

theorem Braid.clone_refines (hkcl : KemCloneAgrees) (hecl : ErasureCloneAgrees)
    (henc : Tacenta.BraidT1.EncoderCloneTotal) (hdec : Tacenta.BraidT1.DecoderCloneTotal)
    (hkp : Tacenta.BraidT1.KeyPairCloneTotal) (hes : Tacenta.BraidT1.EncapsStateCloneTotal)
    {K : Model.Braid.Kem} (self : Braid) (model : Model.Braid.BraidState)
    (hrel : StateRefines K self.state model) :
    Braid.Insts.CoreCloneClone.clone self ⦃ fun r => StateRefines K r.state model ⦄ := by
  unfold Braid.Insts.CoreCloneClone.clone
  step with State.clone_refines hkcl hecl henc hdec hkp hes hrel
  exact s_post

theorem Braid.reported_refines (K : Model.Braid.Kem) (self : Braid)
    (model : Model.Braid.BraidState) (hrel : StateRefines K self.state model) :
    Braid.reported self ⦃ fun r => r.val = model.epoch - 1 ⦄ := by
  unfold Braid.reported
  step with State.epoch_refines K self.state model hrel
  simp only [core.num.U64.saturating_sub, UScalar.saturating_sub, UScalar.val,
    BitVec.toNat_ofNat, UScalarTy.U64_numBits_eq] at i_post ⊢
  have hi : i.bv.toNat < 2 ^ 64 := i.bv.isLt
  have h1 : (1#u64 : U64).bv.toNat = 1 := by decide
  omega

/-- Whenever `Model.Braid.receive` emits an output, the epoch it just
finished (`Model.Braid.receive_output_epoch`'s `o.keyEpoch = st.epoch`) is
exactly the epoch the resulting state reports one below: the same "receive
advances the epoch by exactly one, precisely when it emits a key" fact
`Model.Braid.receive_epoch_le`'s inequality doesn't pin down on its own. -/
theorem Model.Braid.receive_output_next_epoch (K : Model.Braid.Kem)
    (st : Model.Braid.BraidState) (msg : Model.Braid.Msg) (o : Model.Braid.Output) :
    (Model.Braid.receive K st msg).2.1 = some o →
    o.keyEpoch = (Model.Braid.receive K st msg).2.2.epoch - 1 := by
  cases st <;> simp only [Model.Braid.receive] <;> repeat' split
  all_goals (simp [Model.Braid.BraidState.epoch]; try omega)
  all_goals (rintro rfl; rfl)

/-! ## `mac_eq` refines byte equality

Unlike `validate_ek`, `mac_eq` is fully translated Rust (a constant-time
XOR-fold loop), not an opaque boundary call, so, like `BraidT1.lean`'s own
`mac_eq_no_panic`, this is *proved*, not assumed. `U8.xor_eq_zero_iff`/
`U8.or_eq_zero_iff` (Aeneas' `BvTac` lemma set) turn the fold into exactly
the invariant "the accumulator is zero iff every byte seen so far agreed". -/

private theorem mac_eq_loop_agrees (a b : Slice Std.U8) (diff : Std.U8) (i : Usize)
    (hlen : a.length ≤ b.length) (hi : i.val ≤ a.length)
    (hinv : diff = 0#u8 ↔ List.map u8 (a.val.take i.val) = List.map u8 (b.val.take i.val)) :
    mac_eq_loop a b diff i ⦃ fun r =>
      r = 0#u8 ↔ List.map u8 (a.val.take a.length) = List.map u8 (b.val.take a.length) ⦄ := by
  unfold mac_eq_loop
  apply loop.spec_decr_nat
    (measure := fun p => a.length - p.2.val)
    (inv := fun p => p.2.val ≤ a.length ∧
      (p.1 = 0#u8 ↔ List.map u8 (a.val.take p.2.val) = List.map u8 (b.val.take p.2.val)))
  · rintro ⟨diffA, iA⟩ ⟨hiA, hinvA⟩
    simp only [mac_eq_loop.body]
    split
    · rename_i hlt
      step*
      refine ⟨?_, ?_, ?_⟩
      · scalar_tac
      · have hdiff1 : diff1 = diffA ||| i4 := by scalar_tac
        have hi4 : i4 = i2 ^^^ i3 := by scalar_tac
        rw [i5_post, hdiff1, hi4, U8.or_eq_zero_iff, U8.xor_eq_zero_iff]
        have htakeA : a.val.take (iA.val + 1) = a.val.take iA.val ++ [a.val[iA.val]'(by scalar_tac)] := by
          rw [List.take_add_one]; simp [List.getElem?_eq_getElem (by scalar_tac : iA.val < a.val.length)]
        have htakeB : b.val.take (iA.val + 1) = b.val.take iA.val ++ [b.val[iA.val]'(by scalar_tac)] := by
          rw [List.take_add_one]; simp [List.getElem?_eq_getElem (by scalar_tac : iA.val < b.val.length)]
        simp only [htakeA, htakeB, List.map_append, List.map_cons, List.map_nil]
        constructor
        · rintro ⟨hd, hab⟩; rw [hinvA] at hd
          rw [i2_post, i3_post] at hab
          rw [hd, hab]
        · intro heq
          have hlens : (List.map u8 (a.val.take iA.val)).length =
              (List.map u8 (b.val.take iA.val)).length := by
            simp; scalar_tac
          obtain ⟨heq1, heq2⟩ := List.append_inj heq (by simpa using hlens)
          refine ⟨hinvA.mpr heq1, u8_injective ?_⟩
          rw [i2_post, i3_post]
          simpa using heq2
      · scalar_tac
    · rename_i hge
      have hEq : iA.val = a.length := by scalar_tac
      rw [hEq] at hinvA
      exact hinvA
  · exact ⟨hi, hinv⟩

theorem mac_eq_agrees (a b : Slice Std.U8) :
    mac_eq a b ⦃ fun r => r = true ↔ sliceOf a = sliceOf b ⦄ := by
  unfold mac_eq
  simp only []
  split
  · rename_i hne
    have hne' : a.length ≠ b.length := by scalar_tac
    have : ¬ sliceOf a = sliceOf b := by
      intro heq
      apply hne'
      have hl := congrArg List.length heq
      simpa [sliceOf] using hl
    simp [this]
  · rename_i hlen
    have hlen' : a.length ≤ b.length := by scalar_tac
    step with mac_eq_loop_agrees a b 0#u8 0#usize hlen' (by scalar_tac) (by simp)
    have haT : a.val.take a.length = a.val := by simp
    have hbT : b.val.take a.length = b.val := by
      have : a.length = b.length := by scalar_tac
      simp [this]
    rw [haT, hbT] at diff_post
    simp only [sliceOf, decide_eq_true_eq]
    exact diff_post

/-! ## `Msg`/`Output` refine their model counterparts

`Msg.data`'s `Chunk` follows `ErasureAgrees`'s own rule: only the index has
to correspond, never the bytes. `Output.key` is different: it is the actual
derived key a caller consumes, not wire-format opaque bytes, so it needs
full value agreement, not just an index. -/

def MsgTypeRefines : tacenta_braid.MsgType → Model.Braid.MsgType → Prop
  | .None, .none => True
  | .Hdr, .hdr => True
  | .Ek, .ek => True
  | .EkCt1Ack, .ekCt1Ack => True
  | .Ct1, .ct1 => True
  | .Ct2, .ct2 => True
  | _, _ => False

/-- `MsgType`'s `eq` is fully translated (a `read_discriminant` compare, not an
opaque boundary call), so this is proved outright, the same way
`TripleError.eq_no_panic` proves its own enum's `eq` total: the addition
here is the *value*, not just that it returns. Stated against two already-
`MsgTypeRefines`-related pairs so every `step_receive` call site (which always
compares a real `msg.ty` against a real literal, both already known to refine
some model constructor) gets exactly the fact it needs in one step. -/
theorem MsgTypeRefines.eq_agrees {a : tacenta_braid.MsgType} {ma : Model.Braid.MsgType}
    (ha : MsgTypeRefines a ma) {b : tacenta_braid.MsgType} {mb : Model.Braid.MsgType}
    (hb : MsgTypeRefines b mb) :
    MsgType.Insts.CoreCmpPartialEqMsgType.eq a b ⦃ fun r => r = true ↔ ma = mb ⦄ := by
  unfold MsgType.Insts.CoreCmpPartialEqMsgType.eq
  cases a <;> cases ma <;> cases b <;> cases mb <;>
    simp_all [MsgTypeRefines, MsgType.read_discriminant]

def MsgRefines (real : tacenta_braid.Msg) (model : Model.Braid.Msg) : Prop :=
  real.epoch.val = model.epoch ∧ MsgTypeRefines real.ty model.type ∧
  (match real.data, model.data with
   | none, none => True
   | some c, some mc => c.index.val = mc.index ∧ CodewordOf mc.source c
   | _, _ => False)

def OutputRefines (real : tacenta_braid.Output) (model : Model.Braid.Output) : Prop :=
  real.key_epoch.val = model.keyEpoch ∧ keyOf real.key = model.key

def OptionOutputRefines :
    Option tacenta_braid.Output → Option Model.Braid.Output → Prop
  | none, none => True
  | some o, some mo => OutputRefines o mo
  | _, _ => False

/-! ## `step_send` refines `Model.Braid.send`

`rand` is existentially bound in the conclusion, not universally: the real
crate's actual randomness is whatever its RNG produced, not a value this
proof controls, so all this can say is that *some* `rand` makes the model
agree, exactly the same shape `KemAgreesFor`'s own per-key-pair existential
already uses for the same reason. For the ten branches that don't call
`generate`, the existential is trivially satisfied (`rand` is unused there),
so it costs nothing where it isn't needed. -/

set_option maxHeartbeats 1000000 in
theorem step_send_refines (hka : KemAgreesFor K) (hea : ErasureAgrees)
    (hmac : BraidHmacAgrees) (hkdf : BraidHkdfAgrees)
    (hhdr : Tacenta.BraidT1.KeyPairHeaderTotal) (hekv : Tacenta.BraidT1.KeyPairEkVectorTotal)
    (hct1len : Tacenta.BraidT1.Ct1LenTotal) (hct2len : Tacenta.BraidT1.Ct2LenTotal)
    (hz : Tacenta.BraidT1.ZeroizingArrayRoundTrip) (hzz : Tacenta.BraidT1.ArrayZeroizeTotal)
    (hrf : Tacenta.BraidT1.RangeFullIndexTotal)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : Braid) (state : State) (rng : R)
    {model : Model.Braid.BraidState} (hrel : StateRefines K state model)
    (hlive : EncodersLive model) :
    Braid.step_send rc crc self state rng ⦃ fun ((msg, out, next), _) =>
      ∃ rand, (∀ modelMsg, (Model.Braid.send K rand model).1 = some modelMsg →
          MsgRefines msg modelMsg) ∧
        OptionOutputRefines out (Model.Braid.send K rand model).2.2.1 ∧
        StateRefines K next (Model.Braid.send K rand model).2.2.2 ⦄ := by
  obtain ⟨hKcorrect, hgen, hkp, hencaps⟩ := hka
  rcases state with _|_|_|_|_|_|_|_|_|_|_|_ <;> cases model <;>
    simp only [StateRefines] at hrel <;>
    try exact hrel.elim
  case KeysUnsampled.keysUnsampled =>
    rename_i epoch auth epoch' auth'
    obtain ⟨he, ha⟩ := hrel
    obtain ⟨kp, rng', rand, hgenkp, ⟨h, hh, hhval⟩, ⟨v, hv, hvval⟩, hdecap⟩ := hgen rc crc rng
    obtain ⟨h', hh', hh'len⟩ := hhdr kp
    rw [hh] at hh'; injection hh' with hh'; subst hh'
    unfold Braid.step_send
    simp only [hgenkp]
    step*
    simp only [hh]
    step*
    have hsliceh : sliceOf h.deref = (K.keyGen rand).2.1 ++ K.hashEk (K.keyGen rand).2.1 (K.keyGen rand).2.2 := by
      simp [sliceOf, alloc.vec.Vec.deref, vecOf] at hhval ⊢; exact hhval
    step with Auth.mac_hdr_refines hmac auth epoch h.deref _ hsliceh (by simp [alloc.vec.Vec.deref]; scalar_tac)
    step*
    obtain ⟨hdr_enc, hdr_enc_eq, hdr_enc_sim⟩ := hea.1 header1.deref
    simp only [hdr_enc_eq]
    have hencR : EncoderRefines hdr_enc
        (Model.Braid.encode (sliceOf header1.deref)) := hdr_enc_sim
    have hlt : (Model.Braid.encode (sliceOf header1.deref)).next < 65536 := by
      simp [Model.Braid.encode]
    obtain ⟨chunk0, hdr_enc1_0, hnc_eq, hidx0, hsimtail⟩ := hencR.2 1 (by omega)
    have hstep0 := EncoderRefines.step hencR hlt hnc_eq
    step*
    simp only [hnc_eq]
    unfold Msg.with
    step*
    have hheader1val : sliceOf header1.deref =
        ((K.keyGen rand).2.1 ++ K.hashEk (K.keyGen rand).2.1 (K.keyGen rand).2.2) ++
          (AuthOf auth).macHdr epoch.val
            ((K.keyGen rand).2.1 ++ K.hashEk (K.keyGen rand).2.1 (K.keyGen rand).2.2) := by
      simp only [sliceOf, alloc.vec.Vec.deref] at header1_post ⊢
      simp only [header1_post, s1_post, List.map_append]
      simp only [sliceOf, alloc.vec.Vec.deref] at hsliceh
      rw [hsliceh]
      congr 1
    rw [he, ha] at hheader1val
    rw [hheader1val] at hencR
    have hmsg_ex : (Model.Braid.send K rand
        (Model.Braid.BraidState.keysUnsampled epoch' auth')).1 =
        some ⟨epoch', Model.Braid.MsgType.hdr,
          some (Model.Braid.encode (sliceOf header1.deref)).nextChunk.1⟩ := by
      unfold Model.Braid.send
      simp only []
      rw [← hheader1val]
    refine ⟨rand, ?_, ?_, ?_⟩
    · intro modelMsg hm; rw [hmsg_ex] at hm; injection hm with hm; subst hm
      exact ⟨he, trivial, hidx0, hstep0.2.1⟩
    · trivial
    · exact ⟨he, ha, ⟨hdecap, ⟨v, hv, hvval⟩, ⟨h, _, hh, hhval⟩⟩,
        (EncoderRefines.step hencR hlt hnc_eq).2.2⟩
  case KeysSampled.keysSampled =>
    rename_i epoch auth kp hdr_enc epoch' auth' dk ekVector hdr_encM
    obtain ⟨he, ha, hfkp, hencr⟩ := hrel
    have hlt := hlive _ rfl
    obtain ⟨chunk0, hdr_enc1_0, hnc_eq, hidx0, _⟩ := hencr.2 1 (by omega)
    unfold Braid.step_send
    step*
    simp only [hnc_eq]
    unfold Msg.with
    step*
    have hmsg_ex : (Model.Braid.send K 0
        (Model.Braid.BraidState.keysSampled epoch' auth' dk ekVector hdr_encM)).1 =
        some ⟨epoch', Model.Braid.MsgType.hdr, some hdr_encM.nextChunk.1⟩ := by
      unfold Model.Braid.send; rfl
    refine ⟨0, ?_, ?_, ?_⟩
    · intro modelMsg hm; rw [hmsg_ex] at hm; injection hm with hm; subst hm
      exact ⟨he, trivial, hidx0, (EncoderRefines.step hencr hlt hnc_eq).2.1⟩
    · trivial
    · exact ⟨he, ha, hfkp, (EncoderRefines.step hencr hlt hnc_eq).2.2⟩
  case HeaderSent.headerSent =>
    rename_i epoch auth kp ct1_dec ek_enc epoch' auth' dk ct1DecM ekEncM
    obtain ⟨he, ha, hkpr, hdr, hct1size, her⟩ := hrel
    have hlt := hlive _ rfl
    obtain ⟨chunk0, enc1_0, hnc_eq, hidx0, _⟩ := her.2 1 (by omega)
    unfold Braid.step_send
    step*
    simp only [hnc_eq]
    unfold Msg.with
    step*
    have hmsg_ex : (Model.Braid.send K 0
        (Model.Braid.BraidState.headerSent epoch' auth' dk ct1DecM ekEncM)).1 =
        some ⟨epoch', Model.Braid.MsgType.ek, some ekEncM.nextChunk.1⟩ := by
      unfold Model.Braid.send; rfl
    refine ⟨0, ?_, ?_, ?_⟩
    · intro modelMsg hm; rw [hmsg_ex] at hm; injection hm with hm; subst hm
      exact ⟨he, trivial, hidx0, (EncoderRefines.step her hlt hnc_eq).2.1⟩
    · trivial
    · exact ⟨he, ha, hkpr, hdr, hct1size, (EncoderRefines.step her hlt hnc_eq).2.2⟩
  case Ct1Received.ct1Received =>
    rename_i epoch auth kp ct1 ek_enc epoch' auth' dk ct1M ekEncM
    obtain ⟨he, ha, hkpr, hct1, hct1len, her⟩ := hrel
    have hlt := hlive _ rfl
    obtain ⟨chunk0, enc1_0, hnc_eq, hidx0, _⟩ := her.2 1 (by omega)
    unfold Braid.step_send
    step*
    simp only [hnc_eq]
    unfold Msg.with
    step*
    have hmsg_ex : (Model.Braid.send K 0
        (Model.Braid.BraidState.ct1Received epoch' auth' dk ct1M ekEncM)).1 =
        some ⟨epoch', Model.Braid.MsgType.ekCt1Ack, some ekEncM.nextChunk.1⟩ := by
      unfold Model.Braid.send; rfl
    refine ⟨0, ?_, ?_, ?_⟩
    · intro modelMsg hm; rw [hmsg_ex] at hm; injection hm with hm; subst hm
      exact ⟨he, trivial, hidx0, (EncoderRefines.step her hlt hnc_eq).2.1⟩
    · trivial
    · exact ⟨he, ha, hkpr, hct1, hct1len, (EncoderRefines.step her hlt hnc_eq).2.2⟩
  case EkSentCt1Received.ekSentCt1Received =>
    rename_i epoch auth kp ct1 dec epoch' auth' dk ct1M ct2DecM
    obtain ⟨he, ha, hkpr, hct1, hct1len, hdr, hdsize⟩ := hrel
    unfold Braid.step_send
    unfold state_back
    step*
    unfold Msg.empty
    step*
    have hmsg_ex : (Model.Braid.send K 0
        (Model.Braid.BraidState.ekSentCt1Received epoch' auth' dk ct1M ct2DecM)).1 =
        some ⟨epoch', Model.Braid.MsgType.none, none⟩ := by
      unfold Model.Braid.send; rfl
    refine ⟨0, ?_, ?_, ?_⟩
    · intro modelMsg hm; rw [hmsg_ex] at hm; injection hm with hm; subst hm
      exact ⟨he, trivial, trivial⟩
    · trivial
    · exact ⟨he, ha, hkpr, hct1, hct1len, hdr, hdsize⟩
  case NoHeaderReceived.noHeaderReceived =>
    rename_i epoch auth dec epoch' auth' hdrDecM
    obtain ⟨he, ha, hdr, hdsize⟩ := hrel
    unfold Braid.step_send
    unfold state_back
    step*
    unfold Msg.empty
    step*
    have hmsg_ex : (Model.Braid.send K 0
        (Model.Braid.BraidState.noHeaderReceived epoch' auth' hdrDecM)).1 =
        some ⟨epoch', Model.Braid.MsgType.none, none⟩ := by
      unfold Model.Braid.send; rfl
    refine ⟨0, ?_, ?_, ?_⟩
    · intro modelMsg hm; rw [hmsg_ex] at hm; injection hm with hm; subst hm
      exact ⟨he, trivial, trivial⟩
    · trivial
    · exact ⟨he, ha, hdr, hdsize⟩
  case HeaderReceived.headerReceived =>
    rename_i epoch auth header ek_dec epoch' auth' ekSeedM hekM ekDecM
    obtain ⟨he, ha, hhdreq, hlen32, hhek32, hdecr, heksize⟩ := hrel
    have hslicehdr : sliceOf header.deref = ekSeedM ++ hekM := by
      simp [sliceOf, alloc.vec.Vec.deref, vecOf] at hhdreq ⊢; exact hhdreq
    obtain ⟨es, ct1raw, ssraw, rng'', hep1, hep1'⟩ := hencaps rc crc header.deref rng
      (by rw [deref_length, hhdreq]; simp [hlen32, hhek32, Model.Braid.headerSize])
    obtain ⟨hct1eq, hsseq, hencaps2⟩ := hep1' ekSeedM hekM hlen32 hslicehdr
    unfold Braid.step_send
    simp only [hep1]
    step*
    have hs1eq : sliceOf s1 = keyOf ssraw := by
      simp only [sliceOf, Array.to_slice, keyOf] at s1_post ⊢
      rw [s1_post]
    step with kdf_ok_refines hkdf s1 (keyOf ssraw) hs1eq epoch
    -- The epoch key is wrapped, the raw secret wiped, and the key read back
    -- through `key[..]`: three opaque calls, each by assumption the identity
    -- on the value (or, for the wipe, discarded).
    step with Tacenta.BraidT1.zeroizing_new_spec hz
    step with Tacenta.BraidT1.array_zeroize_spec hzz
    step with Tacenta.BraidT1.zeroizing_deref_spec ‹_›
    step with Tacenta.BraidT1.index_full_spec hrf
    have hs2eq : sliceOf s2 = keyOf a := by
      rw [a1_post] at s2_post
      simp only [sliceOf, Array.to_slice, keyOf] at s2_post ⊢
      rw [s2_post]
    step with Auth.update_refines hkdf hz auth epoch s2
    obtain ⟨ct1_enc0, hct1_enc_eq, hct1_enc_sim⟩ := hea.1 ct1raw.deref
    simp only [hct1_enc_eq]
    have hencR : EncoderRefines ct1_enc0 (Model.Braid.encode (sliceOf ct1raw.deref)) :=
      hct1_enc_sim
    have hlt : (Model.Braid.encode (sliceOf ct1raw.deref)).next < 65536 := by
      simp [Model.Braid.encode]
    obtain ⟨chunk0, ct1_enc1_0, hnc_eq, hidx0, hsimtail⟩ := hencR.2 1 (by omega)
    have hstep0 := EncoderRefines.step hencR hlt hnc_eq
    step*
    simp only [hnc_eq]
    unfold Msg.with
    step*
    have hkeyeq0 : keyOf a = Model.Braid.kdfOk (keyOf ssraw) epoch.val := a_post
    have hkeyeq : keyOf a = Model.Braid.kdfOk ((K.encaps1 ekSeedM hekM).2.2) epoch.val := by
      rw [← hsseq] at hkeyeq0; exact hkeyeq0
    have hauth1eq0 : AuthOf auth1 =
        Model.Braid.Auth.update (AuthOf auth) epoch.val (Model.Braid.kdfOk (keyOf ssraw) epoch.val) := by
      rw [hs2eq, hkeyeq0] at auth1_post; exact auth1_post
    have hauth1eq : AuthOf auth1 =
        Model.Braid.Auth.update auth' epoch.val
          (Model.Braid.kdfOk ((K.encaps1 ekSeedM hekM).2.2) epoch.val) := by
      rw [hsseq, ← ha]; exact hauth1eq0
    have hct1sliceeq : sliceOf ct1raw.deref = vecOf ct1raw := by
      simp [sliceOf, alloc.vec.Vec.deref, vecOf]
    have hmsg_ex : (Model.Braid.send K 0
        (Model.Braid.BraidState.headerReceived epoch' auth' ekSeedM hekM ekDecM)).1 =
        some ⟨epoch', Model.Braid.MsgType.ct1,
          some (Model.Braid.encode (sliceOf ct1raw.deref)).nextChunk.1⟩ := by
      unfold Model.Braid.send
      simp only []
      rw [hct1sliceeq, ← hct1eq]
    rw [hct1sliceeq, ← hct1eq] at hencR
    refine ⟨0, ?_, ?_, ?_⟩
    · intro modelMsg hm; rw [hmsg_ex] at hm; injection hm with hm; subst hm
      exact ⟨he, trivial, hidx0, hstep0.2.1⟩
    · refine ⟨he, ?_⟩; rw [a1_post, ← he]; exact hkeyeq
    · refine ⟨he, ?_, hhdreq, hlen32, hhek32, hencaps2, hct1eq.symm,
        (EncoderRefines.step hencR hlt hnc_eq).2.2, hdecr, heksize⟩
      rw [← he]; exact hauth1eq
  case Ct1Sampled.ct1Sampled =>
    rename_i epoch auth header encaps ct1 ct1_enc ek_dec epoch' auth' ekSeedM hekM
      encapsSecretM ct1M ct1EncM ekDecM
    obtain ⟨he, ha, hekSeed, hlen32, hhek32, hencaps, hct1, henr, hdr, heksize⟩ := hrel
    have hlt := hlive _ rfl
    obtain ⟨chunk0, enc1_0, hnc_eq, hidx0, _⟩ := henr.2 1 (by omega)
    unfold Braid.step_send
    step*
    simp only [hnc_eq]
    unfold Msg.with
    step*
    have hmsg_ex : (Model.Braid.send K 0
        (Model.Braid.BraidState.ct1Sampled epoch' auth' ekSeedM hekM encapsSecretM ct1M
          ct1EncM ekDecM)).1 =
        some ⟨epoch', Model.Braid.MsgType.ct1, some ct1EncM.nextChunk.1⟩ := by
      unfold Model.Braid.send; rfl
    refine ⟨0, ?_, ?_, ?_⟩
    · intro modelMsg hm; rw [hmsg_ex] at hm; injection hm with hm; subst hm
      exact ⟨he, trivial, hidx0, (EncoderRefines.step henr hlt hnc_eq).2.1⟩
    · trivial
    · exact ⟨he, ha, hekSeed, hlen32, hhek32, hencaps, hct1, (EncoderRefines.step henr hlt hnc_eq).2.2, hdr, heksize⟩
  case EkReceivedCt1Sampled.ekReceivedCt1Sampled =>
    rename_i epoch auth es ct1 ekVector ct1_enc epoch' auth' encapsSecretM ct1M ekSeedM
      ekVectorM ct1EncM
    obtain ⟨he, ha, hencaps, hct1, hekVector, hekvlen, henr⟩ := hrel
    have hlt := hlive _ rfl
    obtain ⟨chunk0, enc1_0, hnc_eq, hidx0, _⟩ := henr.2 1 (by omega)
    unfold Braid.step_send
    step*
    simp only [hnc_eq]
    unfold Msg.with
    step*
    have hmsg_ex : (Model.Braid.send K 0
        (Model.Braid.BraidState.ekReceivedCt1Sampled epoch' auth' encapsSecretM ct1M ekSeedM
          ekVectorM ct1EncM)).1 =
        some ⟨epoch', Model.Braid.MsgType.ct1, some ct1EncM.nextChunk.1⟩ := by
      unfold Model.Braid.send; rfl
    refine ⟨0, ?_, ?_, ?_⟩
    · intro modelMsg hm; rw [hmsg_ex] at hm; injection hm with hm; subst hm
      exact ⟨he, trivial, hidx0, (EncoderRefines.step henr hlt hnc_eq).2.1⟩
    · trivial
    · exact ⟨he, ha, hencaps, hct1, hekVector, hekvlen, (EncoderRefines.step henr hlt hnc_eq).2.2⟩
  case Ct1Acknowledged.ct1Acknowledged =>
    rename_i epoch auth ekSeed es ct1 dec epoch' auth' ekSeedM hekM encapsSecretM ct1M ekDecM
    obtain ⟨he, ha, hekSeed, hlen32, hhek32, hencaps, hct1, hdr, heksize⟩ := hrel
    unfold Braid.step_send
    unfold state_back
    step*
    unfold Msg.empty
    step*
    have hmsg_ex : (Model.Braid.send K 0
        (Model.Braid.BraidState.ct1Acknowledged epoch' auth' ekSeedM hekM encapsSecretM ct1M
          ekDecM)).1 = some ⟨epoch', Model.Braid.MsgType.none, none⟩ := by
      unfold Model.Braid.send; rfl
    refine ⟨0, ?_, ?_, ?_⟩
    · intro modelMsg hm; rw [hmsg_ex] at hm; injection hm with hm; subst hm
      exact ⟨he, trivial, trivial⟩
    · trivial
    · exact ⟨he, ha, hekSeed, hlen32, hhek32, hencaps, hct1, hdr, heksize⟩
  case Ct2Sampled.ct2Sampled =>
    rename_i epoch auth ct2_enc epoch' auth' ct2EncM
    obtain ⟨he, ha, her⟩ := hrel
    have hlt := hlive _ rfl
    obtain ⟨chunk0, enc1_0, hnc_eq, hidx0, _⟩ := her.2 1 (by omega)
    unfold Braid.step_send
    step*
    simp only [hnc_eq]
    unfold Msg.with
    step*
    have hmsg_ex : (Model.Braid.send K 0
        (Model.Braid.BraidState.ct2Sampled epoch' auth' ct2EncM)).1 =
        some ⟨epoch', Model.Braid.MsgType.ct2, some ct2EncM.nextChunk.1⟩ := by
      unfold Model.Braid.send; rfl
    refine ⟨0, ?_, ?_, ?_⟩
    · intro modelMsg hm; rw [hmsg_ex] at hm; injection hm with hm; subst hm
      exact ⟨he, trivial, hidx0, (EncoderRefines.step her hlt hnc_eq).2.1⟩
    · trivial
    · exact ⟨he, ha, (EncoderRefines.step her hlt hnc_eq).2.2⟩
  case Failed.failed =>
    unfold Braid.step_send
    unfold Msg.empty
    step*
    refine ⟨0, ?_, ?_, ?_⟩
    · intro modelMsg hm; simp [Model.Braid.send] at hm
    · trivial
    · trivial

/-- `Braid.send` clones the state first (so the original is left untouched on
the caller's side, matching what `Braid.clone_refines` already established),
then runs `step_send` on the clone, then reports the epoch via
`Braid.reported`. This just composes the three pieces already proven above. -/
theorem Braid.send_refines (hka : KemAgreesFor K) (hea : ErasureAgrees)
    (hmac : BraidHmacAgrees) (hkdf : BraidHkdfAgrees)
    (hhdr : Tacenta.BraidT1.KeyPairHeaderTotal) (hekv : Tacenta.BraidT1.KeyPairEkVectorTotal)
    (hct1len : Tacenta.BraidT1.Ct1LenTotal) (hct2len : Tacenta.BraidT1.Ct2LenTotal)
    (hkcl : KemCloneAgrees) (hecl : ErasureCloneAgrees)
    (henc : Tacenta.BraidT1.EncoderCloneTotal) (hdec : Tacenta.BraidT1.DecoderCloneTotal)
    (hkp : Tacenta.BraidT1.KeyPairCloneTotal) (hes : Tacenta.BraidT1.EncapsStateCloneTotal)
    (hz : Tacenta.BraidT1.ZeroizingArrayRoundTrip) (hzz : Tacenta.BraidT1.ArrayZeroizeTotal)
    (hrf : Tacenta.BraidT1.RangeFullIndexTotal)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : Braid) (rng : R)
    {model : Model.Braid.BraidState} (hrel : StateRefines K self.state model)
    (hlive : EncodersLive model) :
    Braid.send rc crc self rng ⦃ fun ((msg, i, out, next), _) =>
      ∃ rand, (∀ modelMsg, (Model.Braid.send K rand model).1 = some modelMsg →
          MsgRefines msg modelMsg) ∧
        i.val = (Model.Braid.send K rand model).2.2.2.epoch - 1 ∧
        OptionOutputRefines out (Model.Braid.send K rand model).2.2.1 ∧
        StateRefines K next.state (Model.Braid.send K rand model).2.2.2 ⦄ := by
  unfold Braid.send
  step with State.clone_refines hkcl hecl henc hdec hkp hes hrel
  step with step_send_refines hka hea hmac hkdf hhdr hekv hct1len hct2len hz hzz hrf rc crc self s rng s_post hlive
  obtain ⟨rand, hmsg, hout, hnext⟩ := ‹_›
  step with Braid.reported_refines K { state := next } (Model.Braid.send K rand model).2.2.2 hnext
  exact ⟨rand, hmsg, i_post, hout, hnext⟩

/-! ## `step_receive` refines `Model.Braid.receive` -/

/-- Three real states (`Ct1Sampled`/`EkReceivedCt1Sampled`/`Ct1Acknowledged`)
finish an encapsulation identically, matching `Model.Braid.finishEncaps`'s own
role as the shared tail of transitions (9), (11), (12). `encapsulate2`'s
success (not just totality) comes from `EncapsRefines`, which is exactly
"encapsulate2 succeeds and agrees with `K.encaps2`," so the real `Err` arm
never fires and needs no separate case. -/
theorem finish_encaps_refines (hmac : BraidHmacAgrees) (hea : ErasureAgrees)
    {K : Model.Braid.Kem} (epoch : Std.U64) (auth : Auth) (encaps : tacenta_kem.EncapsState)
    (ct1 ek_vector : Slice Std.U8) {a : Model.Braid.Auth} {es ekSeed ct1M : Bytes}
    (ha : AuthOf auth = a) (hct1 : sliceOf ct1 = ct1M)
    (hencapsRel : EncapsRefines K encaps ekSeed es) (hekv : ek_vector.length = K.ekSize)
    (hlen : ct1.length + (K.encaps2 es ekSeed (sliceOf ek_vector)).length + 96 ≤ Usize.max) :
    finish_encaps epoch auth encaps ct1 ek_vector ⦃ fun r =>
      StateRefines K r (Model.Braid.BraidState.ct2Sampled epoch.val a
        (Model.Braid.encode (K.encaps2 es ekSeed (sliceOf ek_vector) ++
          a.macCt epoch.val (ct1M ++ K.encaps2 es ekSeed (sliceOf ek_vector))))) ⦄ := by
  unfold finish_encaps
  obtain ⟨ct2raw, hct2raw, hct2rawval⟩ := hencapsRel ek_vector hekv
  simp only [hct2raw]
  have hs : sliceOf ct2raw.deref = K.encaps2 es ekSeed (sliceOf ek_vector) := by
    simp only [sliceOf, alloc.vec.Vec.deref, vecOf] at hct2rawval ⊢
    exact hct2rawval
  have hll : ct2raw.deref.length = (K.encaps2 es ekSeed (sliceOf ek_vector)).length := by
    have := congrArg List.length hs
    simpa [sliceOf, alloc.vec.Vec.deref] using this
  step with Auth.mac_ct_refines hmac auth epoch ct1 ct2raw.deref ct1M
    (K.encaps2 es ekSeed (sliceOf ek_vector)) hct1 hs (by scalar_tac)
  step*
  have hlen2 : ct2raw.length + s1.length ≤ Usize.max := by
    have : ct2raw.length = ct2raw.deref.length := by simp [alloc.vec.Vec.deref]
    rw [this, hll]
    have hs1len : s1.length = 32 := by simp [s1_post, Array.to_slice]
    rw [hs1len]
    scalar_tac
  step*
  have hc1 : vecOf c1 = vecOf ct2raw ++ keyOf r := by
    have hs1 : sliceOf s1 = keyOf r := by
      simp only [sliceOf, Array.to_slice, keyOf] at s1_post ⊢
      rw [s1_post]
    simp only [vecOf] at c1_post hs1 ⊢
    rw [c1_post, List.map_append]
    congr 1
  have hs2 : sliceOf c1.deref =
      K.encaps2 es ekSeed (sliceOf ek_vector) ++
        a.macCt epoch.val (ct1M ++ K.encaps2 es ekSeed (sliceOf ek_vector)) := by
    have hsd : sliceOf c1.deref = vecOf c1 := by
      simp [sliceOf, alloc.vec.Vec.deref, vecOf]
    have hmaceq : keyOf r = a.macCt epoch.val (ct1M ++ K.encaps2 es ekSeed (sliceOf ek_vector)) := by
      rw [r_post, ha]
    rw [hsd, hc1, hct2rawval, hmaceq]
  obtain ⟨enc, hnewcall, hnewsim⟩ := hea.1 c1.deref
  simp only [hnewcall]
  refine ⟨rfl, ha, ?_⟩
  rw [hs2] at hnewsim
  exact hnewsim

/-- `hdr_decoder` builds a fresh decoder sized `HEADER_LEN + MAC_LEN`, matching
`Model.Braid.Decoder.new (headerSize + macSize)`, the one place a brand-new
header decoder gets constructed mid-protocol (transition (5)'s epoch swap). -/
theorem hdr_decoder_refines (hea : ErasureAgrees)
    (hheaderlen : ∃ v : Usize, tacenta_kem.HEADER_LEN = ok v ∧ v.val = Model.Braid.headerSize) :
    hdr_decoder ⦃ fun r =>
      DecoderRefines r (Model.Braid.Decoder.new (Model.Braid.headerSize + Model.Braid.macSize)) ⦄ := by
  unfold hdr_decoder
  obtain ⟨v, hv, hvb⟩ := hheaderlen
  simp only [hv]
  step*
  · simp only [hvb, macLen_agrees, Model.Braid.headerSize, Model.Braid.macSize]; scalar_tac
  · obtain ⟨dec, hdec, hdecsim⟩ := hea.2 i1
    simp only [hdec]
    have hi1 : i1.val = Model.Braid.headerSize + Model.Braid.macSize := by
      rw [i1_post, hvb, macLen_agrees]
    rw [hi1] at hdecsim
    exact hdecsim

set_option maxHeartbeats 1000000 in
/-- `step_receive` refines `Model.Braid.receive`. `self` is unused by the real
function (it operates purely on the passed `state`), same as `step_send`. -/
theorem step_receive_refines (hka : KemAgreesFor K) (hea : ErasureAgrees)
    (hmac : BraidHmacAgrees) (hkdf : BraidHkdfAgrees)
    (hlens : KemLenAgrees K) (hvalek : ValidateEkAgrees K)
    (hencaps2len : Tacenta.BraidT1.Encapsulate2Total)
    (hdadd : Tacenta.BraidT1.DecoderAddChunkTotal)
    (hdmsg : Tacenta.BraidT1.DecoderMessageTotal)
    (hct1lenB : Tacenta.BraidT1.Ct1LenTotal) (hct2lenB : Tacenta.BraidT1.Ct2LenTotal)
    (hheaderlenB : Tacenta.BraidT1.HeaderLenTotal)
    (hz : Tacenta.BraidT1.ZeroizingArrayRoundTrip) (hzz : Tacenta.BraidT1.ArrayZeroizeTotal)
    (hrf : Tacenta.BraidT1.RangeFullIndexTotal)
    (self : Braid) (state : State) (msg : tacenta_braid.Msg)
    (hct1b : Tacenta.BraidT1.State.ct1_bounded state)
    (hepoch : (Tacenta.BraidT1.State.epoch_val state).val < Std.U64.max)
    {model : Model.Braid.BraidState} {modelMsg : Model.Braid.Msg}
    (hrel : StateRefines K state model) (hmsg : MsgRefines msg modelMsg)
    (hhonest : HonestChunk model modelMsg) :
    Braid.step_receive self state msg ⦃ fun (out, next) =>
      OptionOutputRefines out (Model.Braid.receive K model modelMsg).2.1 ∧
      StateRefines K next (Model.Braid.receive K model modelMsg).2.2 ⦄ := by
  obtain ⟨hKcorrect, hgen, hkp, hencaps⟩ := hka
  obtain ⟨hheaderlen, hekveclen, hct1len, hct2len⟩ := hlens
  rcases state with _|_|_|_|_|_|_|_|_|_|_|_ <;> cases model <;>
    simp only [StateRefines] at hrel <;>
    try exact hrel.elim
  case KeysUnsampled.keysUnsampled =>
    rename_i epoch auth epoch' auth'
    obtain ⟨he, ha⟩ := hrel
    unfold Braid.step_receive
    step*
    unfold Model.Braid.receive
    exact ⟨trivial, he, ha⟩
  case HeaderReceived.headerReceived =>
    rename_i epoch auth header ek_dec epoch' auth' ekSeedM hekM ekDecM
    obtain ⟨he, ha, hhdreq, hlen32, hhek32, hdecr, heksize⟩ := hrel
    unfold Braid.step_receive
    step*
    unfold Model.Braid.receive
    exact ⟨trivial, he, ha, hhdreq, hlen32, hhek32, hdecr, heksize⟩
  case KeysSampled.keysSampled =>
    rename_i epoch1 auth kp enc epoch' auth' dk ekVector hdrEnc
    have he := hrel.1
    obtain ⟨_, ha, hfkp, henc⟩ := hrel
    have hepiff : msg.epoch = epoch1 ↔ modelMsg.epoch = epoch' := by
      have h1 := hmsg.1
      constructor
      · intro h; rw [h, he] at h1; exact h1.symm
      · intro h; rw [h] at h1; rw [← he] at h1; scalar_tac
    have hct1triv : MsgTypeRefines MsgType.Ct1 Model.Braid.MsgType.ct1 := trivial
    unfold Braid.step_receive
    unfold State.epoch
    simp only [bind_tc_ok]
    by_cases hep : msg.epoch = epoch1
    · have hepM : modelMsg.epoch = epoch' := hepiff.mp hep
      rw [if_pos hep]
      step with MsgTypeRefines.eq_agrees hmsg.2.1 hct1triv
      by_cases hty : b = true
      · have htyM : modelMsg.type = Model.Braid.MsgType.ct1 := b_post.mp hty
        rw [if_pos hty]
        rcases hdm2 : msg.data with _ | c
        · have hdm : modelMsg.data = none := by
            have hdd := hmsg.2.2
            rcases hx : modelMsg.data with _ | mc
            · rfl
            · exfalso; rw [hdm2, hx] at hdd; exact hdd
          simp only []
          step*
          unfold Model.Braid.receive
          simp only [hepM, htyM, hdm]
          split <;> exact ⟨trivial, he, ha, hfkp, henc⟩
        · obtain ⟨mc, hdm, hidx, hcw⟩ : ∃ mc, modelMsg.data = some mc ∧ c.index.val = mc.index ∧ CodewordOf mc.source c := by
            have hdd := hmsg.2.2
            rcases hx : modelMsg.data with _ | mc
            · exfalso; rw [hdm2, hx] at hdd; exact hdd
            · exact ⟨mc, rfl, by rw [hdm2, hx] at hdd; exact hdd⟩
          simp only []
          obtain ⟨lv, hlv, hlveq⟩ := hct1len
          simp only [hlv]
          step*
          obtain ⟨ct1_dec0, hnewd, hnewdsim⟩ := hea.2 lv
          simp only [hnewd]
          step*
          obtain ⟨⟨advanced, ct1_dec1⟩, hadd⟩ := hdadd ct1_dec0 c
          simp only [hadd]
          step*
          obtain ⟨ekv, hekv, hekveq⟩ := hfkp.2.1
          simp only [hekv]
          step*
          obtain ⟨ek_enc0, hnewe, hnewesim⟩ := hea.1 ekv.deref
          simp only [hnewe]
          step*
          have hct1decr : DecoderRefines ct1_dec1
              ((Model.Braid.Decoder.new K.ct1Size).addChunk mc) := by
            rw [← hlveq]
            exact DecoderRefines.add hnewdsim (by simp [Model.Braid.Decoder.new]) hcw hidx hadd
          have hekencr : EncoderRefines ek_enc0 (Model.Braid.encode ekVector) := by
            have hslice : sliceOf ekv.deref = ekVector := by
              simp only [sliceOf, alloc.vec.Vec.deref, vecOf] at hekveq ⊢
              exact hekveq
            rw [← hslice]
            exact hnewesim
          unfold Model.Braid.receive
          simp only [hepM, htyM, hdm]
          split
          · exact ⟨trivial, he, ha, hfkp.1, hct1decr, by rw [Model.Braid.Decoder.addChunk_size]; rfl, hekencr⟩
          · exfalso; simp_all
      · have htyM : ¬ modelMsg.type = Model.Braid.MsgType.ct1 := fun h => hty (b_post.mpr h)
        rw [if_neg hty]
        unfold Model.Braid.receive
        simp only [hepM]
        split
        · exfalso; simp_all
        · exact ⟨trivial, he, ha, hfkp, henc⟩
    · have hepM : ¬ modelMsg.epoch = epoch' := fun h => hep (hepiff.mpr h)
      rw [if_neg hep]
      unfold Model.Braid.receive
      simp only
      split
      · exfalso; simp_all
      · exact ⟨trivial, he, ha, hfkp, henc⟩
  case HeaderSent.headerSent =>
    rename_i epoch1 auth kp ct1_dec ek_enc epoch' auth' dk ct1DecM ekEncM
    have he := hrel.1
    obtain ⟨_, ha, hkpr, hdcr, hct1size, hencr⟩ := hrel
    have hepiff : msg.epoch = epoch1 ↔ modelMsg.epoch = epoch' := by
      have h1 := hmsg.1
      constructor
      · intro h; rw [h, he] at h1; exact h1.symm
      · intro h; rw [h] at h1; rw [← he] at h1; scalar_tac
    have hct1triv : MsgTypeRefines MsgType.Ct1 Model.Braid.MsgType.ct1 := trivial
    unfold Braid.step_receive
    unfold State.epoch
    simp only [bind_tc_ok]
    by_cases hep : msg.epoch = epoch1
    · have hepM : modelMsg.epoch = epoch' := hepiff.mp hep
      rw [if_pos hep]
      step with MsgTypeRefines.eq_agrees hmsg.2.1 hct1triv
      by_cases hty : b = true
      · have htyM : modelMsg.type = Model.Braid.MsgType.ct1 := b_post.mp hty
        rw [if_pos hty]
        rcases hdm2 : msg.data with _ | c
        · have hdm : modelMsg.data = none := by
            have hdd := hmsg.2.2
            rcases hx : modelMsg.data with _ | mc
            · rfl
            · exfalso; rw [hdm2, hx] at hdd; exact hdd
          simp only []
          step*
          unfold Model.Braid.receive
          simp only [hepM, htyM, hdm]
          split <;> exact ⟨trivial, he, ha, hkpr, hdcr, hct1size, hencr⟩
        · obtain ⟨mc, hdm, hidx, hcw⟩ : ∃ mc, modelMsg.data = some mc ∧ c.index.val = mc.index ∧ CodewordOf mc.source c := by
            have hdd := hmsg.2.2
            rcases hx : modelMsg.data with _ | mc
            · exfalso; rw [hdm2, hx] at hdd; exact hdd
            · exact ⟨mc, rfl, by rw [hdm2, hx] at hdd; exact hdd⟩
          simp only []
          obtain ⟨⟨advanced, ct1_dec1⟩, hadd⟩ := hdadd ct1_dec c
          simp only [hadd]
          step*
          obtain ⟨hfit, hsame⟩ : ChunkFits _ mc := by
            have h := hhonest mc hdm hepM
            rw [htyM] at h
            exact h
          obtain ⟨omsg, homsg⟩ := hdmsg ct1_dec1
          obtain ⟨hct1decr, hmsgeq⟩ := DecoderRefines.add_message hdcr hfit hsame hcw hidx hadd homsg
          simp only [homsg]
          rcases hom : omsg with _ | ct1raw
          · have hMnone : (ct1DecM.addChunk mc).message = none := by
              rw [hom] at hmsgeq; simpa using hmsgeq.symm
            simp only [bind_tc_ok]
            unfold Model.Braid.receive
            simp only [hepM, htyM, hdm]
            split
            · simp only [hMnone]
              exact ⟨trivial, he, ha, hkpr, hct1decr,
                by rw [Model.Braid.Decoder.addChunk_size]; exact hct1size, hencr⟩
            · rename_i hcond; exact absurd (by simp) hcond
          · obtain ⟨ct1M, hMsome⟩ : ∃ ct1M, (ct1DecM.addChunk mc).message = some ct1M := by
              rw [hom] at hmsgeq
              rcases hy : (ct1DecM.addChunk mc).message with _ | ct1M
              · rw [hy] at hmsgeq; simp at hmsgeq
              · exact ⟨ct1M, rfl⟩
            have hct1eq : vecOf ct1raw = ct1M := by
              rw [hom, hMsome] at hmsgeq; simpa using hmsgeq
            simp only [bind_tc_ok]
            unfold Model.Braid.receive
            simp only [hepM, htyM, hdm]
            split
            · simp only [hMsome]
              exact ⟨trivial, he, ha, hkpr, hct1eq,
                by rw [Model.Braid.Decoder.message_length _ _ hMsome,
                  Model.Braid.Decoder.addChunk_size]; exact hct1size, hencr⟩
            · rename_i hcond; exact absurd (by simp) hcond
      · have htyM : ¬ modelMsg.type = Model.Braid.MsgType.ct1 := fun h => hty (b_post.mpr h)
        rw [if_neg hty]
        unfold Model.Braid.receive
        simp only [hepM]
        split
        · rename_i hcond; exact absurd hcond (by simp [htyM])
        · exact ⟨trivial, he, ha, hkpr, hdcr, hct1size, hencr⟩
    · have hepM : ¬ modelMsg.epoch = epoch' := fun h => hep (hepiff.mpr h)
      rw [if_neg hep]
      unfold Model.Braid.receive
      simp only
      split
      · rename_i hcond; exact absurd hcond (by simp [hepM])
      · exact ⟨trivial, he, ha, hkpr, hdcr, hct1size, hencr⟩
  case Ct1Received.ct1Received =>
    rename_i epoch1 auth kp ct1 enc epoch' auth' dk ct1M ekEncM
    have he := hrel.1
    obtain ⟨_, ha, hkpr, hct1, hct1len, hencr⟩ := hrel
    have hepiff : msg.epoch = epoch1 ↔ modelMsg.epoch = epoch' := by
      have h1 := hmsg.1
      constructor
      · intro h; rw [h, he] at h1; exact h1.symm
      · intro h; rw [h] at h1; rw [← he] at h1; scalar_tac
    have hct2triv : MsgTypeRefines MsgType.Ct2 Model.Braid.MsgType.ct2 := trivial
    unfold Braid.step_receive
    unfold State.epoch
    simp only [bind_tc_ok]
    by_cases hep : msg.epoch = epoch1
    · have hepM : modelMsg.epoch = epoch' := hepiff.mp hep
      rw [if_pos hep]
      step with MsgTypeRefines.eq_agrees hmsg.2.1 hct2triv
      by_cases hty : b = true
      · have htyM : modelMsg.type = Model.Braid.MsgType.ct2 := b_post.mp hty
        rw [if_pos hty]
        rcases hdm2 : msg.data with _ | c
        · have hdm : modelMsg.data = none := by
            have hdd := hmsg.2.2
            rcases hx : modelMsg.data with _ | mc
            · rfl
            · exfalso; rw [hdm2, hx] at hdd; exact hdd
          simp only []
          step*
          unfold Model.Braid.receive
          simp only [hepM, htyM, hdm]
          split <;> exact ⟨trivial, he, ha, hkpr, hct1, hct1len, hencr⟩
        · obtain ⟨mc, hdm, hidx, hcw⟩ : ∃ mc, modelMsg.data = some mc ∧ c.index.val = mc.index ∧ CodewordOf mc.source c := by
            have hdd := hmsg.2.2
            rcases hx : modelMsg.data with _ | mc
            · exfalso; rw [hdm2, hx] at hdd; exact hdd
            · exact ⟨mc, rfl, by rw [hdm2, hx] at hdd; exact hdd⟩
          simp only []
          obtain ⟨lv, hlv, hlveq⟩ := hct2len
          obtain ⟨lv2, hlv2, hlv2bound⟩ := hct2lenB
          rw [hlv] at hlv2; injection hlv2 with hlv2; subst hlv2
          simp only [hlv]
          step with Usize.add_spec (by simp only [MAC_LEN]; scalar_tac :
            lv.val + MAC_LEN.val ≤ Usize.max)
          have hlv1eq : i.val = K.ct2Size + Model.Braid.macSize := by
            rw [i_post, ← hlveq, ← macLen_agrees]
          obtain ⟨ct2_dec0, hnewd, hnewdsim⟩ := hea.2 i
          simp only [hnewd]
          step*
          obtain ⟨⟨advanced, ct2_dec1⟩, hadd⟩ := hdadd ct2_dec0 c
          simp only [hadd]
          step*
          have hct2decr : DecoderRefines ct2_dec1
              ((Model.Braid.Decoder.new (K.ct2Size + Model.Braid.macSize)).addChunk mc) := by
            rw [← hlv1eq]
            exact DecoderRefines.add hnewdsim (by simp [Model.Braid.Decoder.new]) hcw hidx hadd
          have hct2decsize : ((Model.Braid.Decoder.new (K.ct2Size + Model.Braid.macSize)).addChunk mc).size
              = K.ct2Size + Model.Braid.macSize := by
            simp [Model.Braid.Decoder.addChunk, Model.Braid.Decoder.new]
          unfold Model.Braid.receive
          simp only [hepM, htyM, hdm]
          split
          · exact ⟨trivial, he, ha, hkpr, hct1, hct1len, hct2decr, hct2decsize⟩
          · rename_i hcond; exact absurd hcond (by simp)
      · have htyM : ¬ modelMsg.type = Model.Braid.MsgType.ct2 := fun h => hty (b_post.mpr h)
        rw [if_neg hty]
        unfold Model.Braid.receive
        simp only [hepM]
        split
        · rename_i hcond; exact absurd hcond (by simp [htyM])
        · exact ⟨trivial, he, ha, hkpr, hct1, hct1len, hencr⟩
    · have hepM : ¬ modelMsg.epoch = epoch' := fun h => hep (hepiff.mpr h)
      rw [if_neg hep]
      unfold Model.Braid.receive
      simp only
      split
      · rename_i hcond; exact absurd hcond (by simp [hepM])
      · exact ⟨trivial, he, ha, hkpr, hct1, hct1len, hencr⟩
  case Ct2Sampled.ct2Sampled =>
    rename_i epoch1 auth ct2_enc epoch' auth' ct2EncM
    obtain ⟨he, ha, hencr⟩ := hrel
    have hepoch1 : epoch1.val < Std.U64.max := by
      simpa [Tacenta.BraidT1.State.epoch_val] using hepoch
    unfold Braid.step_receive
    unfold State.epoch
    simp only [bind_tc_ok]
    -- Transition 13 advances the epoch with `checked_add`. Below the ceiling
    -- (`hepoch`) it is `some`, and the model's `epoch + 1` is its value; at the
    -- ceiling the real code answers `Failed` where the model's `Nat` keeps
    -- counting, which is why the refinement keeps `hepoch`.
    have hcs := Std.U64.checked_add_bv_spec epoch1 1#u64
    rcases hchk : Std.U64.checked_add epoch1 1#u64 with _ | i
    · rw [hchk] at hcs; simp at hcs; scalar_tac
    rw [hchk] at hcs
    obtain ⟨-, i_post, -⟩ := hcs
    simp only [lift, bind_tc_ok]
    have h1 := hmsg.1
    by_cases hep : msg.epoch = i
    · have hepM : modelMsg.epoch = epoch' + 1 := by
        rw [hep] at h1; scalar_tac
      rw [if_pos hep]
      unfold Model.Braid.receive
      simp only [hepM]
      split
      · refine ⟨trivial, ?_, ha⟩
        scalar_tac
      · rename_i hcond; exact absurd hcond (by simp)
    · have hepM : ¬ modelMsg.epoch = epoch' + 1 := by
        intro h
        apply hep
        scalar_tac
      rw [if_neg hep]
      unfold Model.Braid.receive
      simp only
      split
      · rename_i hcond; exact absurd hcond (by simp [hepM])
      · exact ⟨trivial, he, ha, hencr⟩
  case Failed.failed =>
    unfold Braid.step_receive
    step*
    unfold Model.Braid.receive
    exact ⟨trivial, trivial⟩
  case EkReceivedCt1Sampled.ekReceivedCt1Sampled =>
    rename_i epoch1 auth es ct1 ekVector enc epoch' auth' encapsSecretM ct1M ekSeedM
      ekVectorM ct1EncM
    have he := hrel.1
    obtain ⟨_, ha, hencaps, hct1, hekVector, hekvlen, hencr⟩ := hrel
    have hepiff : msg.epoch = epoch1 ↔ modelMsg.epoch = epoch' := by
      have h1 := hmsg.1
      constructor
      · intro h; rw [h, he] at h1; exact h1.symm
      · intro h; rw [h] at h1; rw [← he] at h1; scalar_tac
    have hcktriv : MsgTypeRefines MsgType.EkCt1Ack Model.Braid.MsgType.ekCt1Ack := trivial
    unfold Braid.step_receive
    unfold State.epoch
    simp only [bind_tc_ok]
    by_cases hep : msg.epoch = epoch1
    · have hepM : modelMsg.epoch = epoch' := hepiff.mp hep
      rw [if_pos hep]
      step with MsgTypeRefines.eq_agrees hmsg.2.1 hcktriv
      by_cases hty : b = true
      · have htyM : modelMsg.type = Model.Braid.MsgType.ekCt1Ack := b_post.mp hty
        rw [if_pos hty]
        have hct1slice : sliceOf ct1.deref = ct1M := by
          simp only [sliceOf, alloc.vec.Vec.deref, vecOf] at hct1 ⊢; exact hct1
        have hekvL : ekVector.deref.length = K.ekSize := by
          rw [deref_length, hekVector]; exact hekvlen
        have hlen : ct1.length +
            (K.encaps2 encapsSecretM ekSeedM (sliceOf ekVector.deref)).length + 96
            ≤ Usize.max := by
          obtain ⟨ct2raw, hct2raw, hct2rawval⟩ := hencaps ekVector.deref hekvL
          obtain ⟨r, hr, hrbound⟩ := hencaps2len es ekVector.deref
          rw [hct2raw] at hr
          injection hr with hr
          have hb := hrbound ct2raw hr.symm
          have hlen2 :
              (K.encaps2 encapsSecretM ekSeedM (sliceOf ekVector.deref)).length = ct2raw.length := by
            rw [← hct2rawval]
            simp [vecOf]
          rw [hlen2]
          have hct1bound : ct1.length ≤ 4096 := by
            simpa [Tacenta.BraidT1.State.ct1_bounded] using hct1b
          scalar_tac
        step with finish_encaps_refines hmac hea epoch1 auth es ct1.deref ekVector.deref
          ha hct1slice hencaps hekvL hlen
        unfold Model.Braid.receive
        simp only [hepM, htyM]
        split
        · have hekVectorSlice : sliceOf ekVector.deref = ekVectorM := by
            simp only [sliceOf, alloc.vec.Vec.deref, vecOf] at hekVector ⊢; exact hekVector
          rw [he, hekVectorSlice] at s2_post
          exact ⟨trivial, s2_post⟩
        · rename_i hcond; exact absurd hcond (by simp)
      · have htyM : ¬ modelMsg.type = Model.Braid.MsgType.ekCt1Ack :=
          fun h => hty (b_post.mpr h)
        rw [if_neg hty]
        unfold Model.Braid.receive
        simp only [hepM]
        split
        · rename_i hcond; exact absurd hcond (by simp [htyM])
        · exact ⟨trivial, he, ha, hencaps, hct1, hekVector, hekvlen, hencr⟩
    · have hepM : ¬ modelMsg.epoch = epoch' := fun h => hep (hepiff.mpr h)
      rw [if_neg hep]
      unfold Model.Braid.receive
      simp only
      split
      · rename_i hcond; exact absurd hcond (by simp [hepM])
      · exact ⟨trivial, he, ha, hencaps, hct1, hekVector, hekvlen, hencr⟩
  case Ct1Sampled.ct1Sampled =>
    rename_i epoch1 auth header encaps ct1 ct1_enc ek_dec epoch' auth' ekSeedM hekM
      encapsSecretM ct1M ct1EncM ekDecM
    have he := hrel.1
    obtain ⟨_, ha, hhdr, hlen32, hhek32, hencapsr, hct1, hencr, hdecr, heksize⟩ := hrel
    have hepiff : msg.epoch = epoch1 ↔ modelMsg.epoch = epoch' := by
      have h1 := hmsg.1
      constructor
      · intro h; rw [h, he] at h1; exact h1.symm
      · intro h; rw [h] at h1; rw [← he] at h1; scalar_tac
    have hektriv : MsgTypeRefines MsgType.Ek Model.Braid.MsgType.ek := trivial
    have hcktriv : MsgTypeRefines MsgType.EkCt1Ack Model.Braid.MsgType.ekCt1Ack := trivial
    have hhdrslice : sliceOf header.deref = ekSeedM ++ hekM := by
      simp only [sliceOf, alloc.vec.Vec.deref, vecOf] at hhdr ⊢; exact hhdr
    unfold Braid.step_receive
    unfold State.epoch
    simp only [bind_tc_ok]
    by_cases hep : msg.epoch = epoch1
    · have hepM : modelMsg.epoch = epoch' := hepiff.mp hep
      rw [if_pos hep]
      step with MsgTypeRefines.eq_agrees hmsg.2.1 hektriv
      by_cases hb1 : relevant = true
      · have htyM : modelMsg.type = Model.Braid.MsgType.ek := relevant_post.mp hb1
        rw [if_pos hb1]
        step*
        · rename_i hdm2
          have hdm : modelMsg.data = none := by
            have hdd := hmsg.2.2
            rcases hx : modelMsg.data with _ | mc
            · rfl
            · exfalso; rw [hdm2, hx] at hdd; exact hdd
          unfold Model.Braid.receive
          simp only [hepM, htyM, hdm]
          split
          · exact ⟨trivial, he, ha, hhdr, hlen32, hhek32, hencapsr, hct1, hencr, hdecr, heksize⟩
          · rename_i hcond; exact absurd hcond (by simp)
        · rename_i hdm2
          obtain ⟨mc, hdm, hidx, hcw⟩ : ∃ mc, modelMsg.data = some mc ∧ c.index.val = mc.index ∧ CodewordOf mc.source c := by
            have hdd := hmsg.2.2
            rcases hx : modelMsg.data with _ | mc
            · exfalso; rw [hdm2, hx] at hdd; exact hdd
            · exact ⟨mc, rfl, by rw [hdm2, hx] at hdd; exact hdd⟩
          step with MsgTypeRefines.eq_agrees hmsg.2.1 hcktriv
          obtain ⟨advanced, ek_dec1, hadd⟩ :
              ∃ advanced ek_dec1, ek_dec.add_chunk c = ok (advanced, ek_dec1) := by
            obtain ⟨⟨a1, a2⟩, ha12⟩ := hdadd ek_dec c; exact ⟨a1, a2, ha12⟩
          simp only [hadd]
          step*
          obtain ⟨hfit, hsame⟩ : ChunkFits _ mc := by
            have h := hhonest mc hdm hepM
            rw [htyM] at h
            exact h
          obtain ⟨omsg, homsg⟩ := hdmsg ek_dec1
          obtain ⟨hekdecr, hmsgeq⟩ := DecoderRefines.add_message hdecr hfit hsame hcw hidx hadd homsg
          simp only [homsg]
          have hackedFalse : acked = false := by
            rw [← Bool.not_eq_true]
            intro h
            exact absurd (acked_post.mp h) (by simp [htyM])
          rcases hom : omsg with _ | ekVecRaw
          · have hMnone : (ekDecM.addChunk mc).message = none := by
              rw [hom] at hmsgeq; simpa using hmsgeq.symm
            simp only [bind_tc_ok, hackedFalse, Bool.false_eq_true, if_false]
            unfold Model.Braid.receive
            simp only [hepM, htyM, hdm, hMnone]
            split
            · exact ⟨trivial, he, ha, hhdr, hlen32, hhek32, hencapsr, hct1, hencr, hekdecr,
                by rw [Model.Braid.Decoder.addChunk_size]; exact heksize⟩
            · rename_i hcond
              first
                | exact absurd hcond (by simp)
                | exact absurd (by simp [hepM, htyM]) hcond
          · obtain ⟨ekVectorM, hMsome⟩ :
                ∃ ekVectorM, (ekDecM.addChunk mc).message = some ekVectorM := by
              rw [hom] at hmsgeq
              rcases hy : (ekDecM.addChunk mc).message with _ | ekVectorM
              · rw [hy] at hmsgeq; simp at hmsgeq
              · exact ⟨ekVectorM, rfl⟩
            have hekVecEq : vecOf ekVecRaw = ekVectorM := by
              rw [hom, hMsome] at hmsgeq; simpa using hmsgeq
            have hekVecSlice : sliceOf ekVecRaw.deref = ekVectorM := by
              simp only [sliceOf, alloc.vec.Vec.deref, vecOf] at hekVecEq ⊢; exact hekVecEq
            simp only [bind_tc_ok]
            have hekvL : ekVecRaw.deref.length = K.ekSize := by
              rw [deref_length, hekVecEq, Model.Braid.Decoder.message_length _ _ hMsome,
                Model.Braid.Decoder.addChunk_size]; exact heksize
            obtain ⟨rb, hrb, hrbiff⟩ :=
              hvalek header.deref ekVecRaw.deref ekSeedM hekM hlen32 hhek32 hekvL hhdrslice
            simp only [hrb, bind_tc_ok]
            by_cases hrbval : rb = true
            · simp only [if_pos hrbval, hackedFalse, Bool.false_eq_true, if_false]
              have hhashEq : K.hashEk ekSeedM ekVectorM = hekM := by
                rw [← hekVecSlice]; exact hrbiff.mp hrbval
              unfold Model.Braid.receive
              simp only [hepM, htyM, hdm, hMsome]
              split
              · split
                · rename_i hcond
                  first
                    | exact absurd hcond (by simp [hhashEq])
                    | exact absurd (by simp [hhashEq]) hcond
                · exact ⟨trivial, he, ha, hencapsr, hct1, hekVecSlice,
                    by rw [Model.Braid.Decoder.message_length _ _ hMsome,
                      Model.Braid.Decoder.addChunk_size]; exact heksize, hencr⟩
              · rename_i hcond
                first
                  | exact absurd hcond (by simp)
                  | exact absurd (by simp [hepM, htyM]) hcond
            · rw [if_neg hrbval]
              have hhashNeq : K.hashEk ekSeedM ekVectorM ≠ hekM := by
                rw [← hekVecSlice]; exact fun h => hrbval (hrbiff.mpr h)
              unfold Model.Braid.receive
              simp only [hepM, htyM, hdm, hMsome]
              split
              · split
                · trivial
                · rename_i hcond
                  first
                    | exact absurd hcond (by simp [hhashNeq])
                    | exact absurd (by simp [hhashNeq]) hcond
              · rename_i hcond
                first
                  | exact absurd hcond (by simp)
                  | exact absurd (by simp [hepM, htyM]) hcond
      · have htyM : ¬ modelMsg.type = Model.Braid.MsgType.ek := fun h => hb1 (relevant_post.mpr h)
        rw [if_neg hb1]
        step with MsgTypeRefines.eq_agrees hmsg.2.1 hcktriv
        by_cases hb2 : relevant = true
        · have htyM2 : modelMsg.type = Model.Braid.MsgType.ekCt1Ack := relevant_post.mp hb2
          rw [if_pos hb2]
          step*
          · rename_i hdm2
            have hdm : modelMsg.data = none := by
              have hdd := hmsg.2.2
              rcases hx : modelMsg.data with _ | mc
              · rfl
              · exfalso; rw [hdm2, hx] at hdd; exact hdd
            unfold Model.Braid.receive
            simp only [hepM, htyM2, hdm]
            split
            · exact ⟨trivial, he, ha, hhdr, hlen32, hhek32, hencapsr, hct1, hencr, hdecr, heksize⟩
            · rename_i hcond
              first
                | exact absurd hcond (by simp)
                | exact absurd (by simp [hepM, htyM2]) hcond
          · rename_i hdm2
            obtain ⟨mc, hdm, hidx, hcw⟩ : ∃ mc, modelMsg.data = some mc ∧ c.index.val = mc.index ∧ CodewordOf mc.source c := by
              have hdd := hmsg.2.2
              rcases hx : modelMsg.data with _ | mc
              · exfalso; rw [hdm2, hx] at hdd; exact hdd
              · exact ⟨mc, rfl, by rw [hdm2, hx] at hdd; exact hdd⟩
            step with MsgTypeRefines.eq_agrees hmsg.2.1 hcktriv
            have hackedTrue : acked = true := acked_post.mpr htyM2
            obtain ⟨advanced, ek_dec1, hadd⟩ :
                ∃ advanced ek_dec1, ek_dec.add_chunk c = ok (advanced, ek_dec1) := by
              obtain ⟨⟨a1, a2⟩, ha12⟩ := hdadd ek_dec c; exact ⟨a1, a2, ha12⟩
            simp only [hadd]
            step*
            obtain ⟨hfit, hsame⟩ : ChunkFits _ mc := by
              have h := hhonest mc hdm hepM
              rw [htyM2] at h
              exact h
            obtain ⟨omsg, homsg⟩ := hdmsg ek_dec1
            obtain ⟨hekdecr, hmsgeq⟩ := DecoderRefines.add_message hdecr hfit hsame hcw hidx hadd homsg
            simp only [homsg]
            rcases hom : omsg with _ | ekVecRaw
            · have hMnone : (ekDecM.addChunk mc).message = none := by
                rw [hom] at hmsgeq; simpa using hmsgeq.symm
              simp only [bind_tc_ok, hackedTrue, if_true]
              unfold Model.Braid.receive
              simp only [hepM, htyM2, hdm, hMnone]
              split
              · exact ⟨trivial, he, ha, hhdr, hlen32, hhek32, hencapsr, hct1, hekdecr,
                by rw [Model.Braid.Decoder.addChunk_size]; exact heksize⟩
              · rename_i hcond
                first
                  | exact absurd hcond (by simp)
                  | exact absurd (by simp [hepM, htyM2]) hcond
            · obtain ⟨ekVectorM, hMsome⟩ :
                  ∃ ekVectorM, (ekDecM.addChunk mc).message = some ekVectorM := by
                rw [hom] at hmsgeq
                rcases hy : (ekDecM.addChunk mc).message with _ | ekVectorM
                · rw [hy] at hmsgeq; simp at hmsgeq
                · exact ⟨ekVectorM, rfl⟩
              have hekVecEq : vecOf ekVecRaw = ekVectorM := by
                rw [hom, hMsome] at hmsgeq; simpa using hmsgeq
              have hekVecSlice : sliceOf ekVecRaw.deref = ekVectorM := by
                simp only [sliceOf, alloc.vec.Vec.deref, vecOf] at hekVecEq ⊢; exact hekVecEq
              simp only [bind_tc_ok]
              have hekvL : ekVecRaw.deref.length = K.ekSize := by
                rw [deref_length, hekVecEq, Model.Braid.Decoder.message_length _ _ hMsome,
                  Model.Braid.Decoder.addChunk_size]; exact heksize
              obtain ⟨rb, hrb, hrbiff⟩ :=
                hvalek header.deref ekVecRaw.deref ekSeedM hekM hlen32 hhek32 hekvL hhdrslice
              simp only [hrb, bind_tc_ok]
              by_cases hrbval : rb = true
              · simp only [if_pos hrbval, hackedTrue, if_true]
                have hhashEq : K.hashEk ekSeedM ekVectorM = hekM := by
                  rw [← hekVecSlice]; exact hrbiff.mp hrbval
                have hct1slice : sliceOf ct1.deref = ct1M := by
                  simp only [sliceOf, alloc.vec.Vec.deref, vecOf] at hct1 ⊢; exact hct1
                have hlen : ct1.length +
                    (K.encaps2 encapsSecretM ekSeedM (sliceOf ekVecRaw.deref)).length + 96
                    ≤ Usize.max := by
                  obtain ⟨ct2raw, hct2raw, hct2rawval⟩ := hencapsr ekVecRaw.deref hekvL
                  obtain ⟨r, hr, hrbound⟩ := hencaps2len encaps ekVecRaw.deref
                  rw [hct2raw] at hr
                  injection hr with hr
                  have hb := hrbound ct2raw hr.symm
                  have hlen2 : (K.encaps2 encapsSecretM ekSeedM (sliceOf ekVecRaw.deref)).length
                      = ct2raw.length := by
                    rw [← hct2rawval]; simp [vecOf]
                  rw [hlen2]
                  have hct1bound : ct1.length ≤ 4096 := by
                    simpa [Tacenta.BraidT1.State.ct1_bounded] using hct1b
                  scalar_tac
                step with finish_encaps_refines hmac hea epoch1 auth encaps ct1.deref
                  ekVecRaw.deref ha hct1slice hencapsr hekvL hlen
                unfold Model.Braid.receive
                simp only [hepM, htyM2, hdm, hMsome]
                split
                · split
                  · rename_i hcond
                    first
                      | exact absurd hcond (by simp [hhashEq])
                      | exact absurd (by simp [hhashEq]) hcond
                  · rw [he, hekVecSlice] at s4_post
                    exact ⟨trivial, s4_post⟩
                · rename_i hcond
                  first
                    | exact absurd hcond (by simp)
                    | exact absurd (by simp [hepM, htyM2]) hcond
              · rw [if_neg hrbval]
                have hhashNeq : K.hashEk ekSeedM ekVectorM ≠ hekM := by
                  rw [← hekVecSlice]; exact fun h => hrbval (hrbiff.mpr h)
                unfold Model.Braid.receive
                simp only [hepM, htyM2, hdm, hMsome]
                split
                · split
                  · trivial
                  · rename_i hcond
                    first
                      | exact absurd hcond (by simp [hhashNeq])
                      | exact absurd (by simp [hhashNeq]) hcond
                · rename_i hcond
                  first
                    | exact absurd hcond (by simp)
                    | exact absurd (by simp [hepM, htyM2]) hcond
        · have htyM2 : ¬ modelMsg.type = Model.Braid.MsgType.ekCt1Ack :=
            fun h => hb2 (relevant_post.mpr h)
          rw [if_neg hb2]
          unfold Model.Braid.receive
          simp only [hepM]
          split
          · rename_i hcond
            first
              | exact absurd hcond (by simp [htyM, htyM2])
              | exact absurd (by simp [htyM, htyM2]) hcond
          · exact ⟨trivial, he, ha, hhdr, hlen32, hhek32, hencapsr, hct1, hencr, hdecr, heksize⟩
    · have hepM : ¬ modelMsg.epoch = epoch' := fun h => hep (hepiff.mpr h)
      rw [if_neg hep]
      simp only [bind_tc_ok, Bool.false_eq_true, if_false]
      unfold Model.Braid.receive
      simp only
      split
      · exfalso; simp_all
      · exact ⟨trivial, he, ha, hhdr, hlen32, hhek32, hencapsr, hct1, hencr, hdecr, heksize⟩
  case Ct1Acknowledged.ct1Acknowledged =>
    rename_i epoch1 auth header encaps ct1 ek_dec epoch' auth' ekSeedM hekM encapsSecretM ct1M
      ekDecM
    have he := hrel.1
    obtain ⟨_, ha, hhdr, hlen32, hhek32, hencapsr, hct1, hdecr, heksize⟩ := hrel
    have hepiff : msg.epoch = epoch1 ↔ modelMsg.epoch = epoch' := by
      have h1 := hmsg.1
      constructor
      · intro h; rw [h, he] at h1; exact h1.symm
      · intro h; rw [h] at h1; rw [← he] at h1; scalar_tac
    have hcktriv : MsgTypeRefines MsgType.EkCt1Ack Model.Braid.MsgType.ekCt1Ack := trivial
    have hhdrslice : sliceOf header.deref = ekSeedM ++ hekM := by
      simp only [sliceOf, alloc.vec.Vec.deref, vecOf] at hhdr ⊢; exact hhdr
    unfold Braid.step_receive
    unfold State.epoch
    simp only [bind_tc_ok]
    by_cases hep : msg.epoch = epoch1
    · have hepM : modelMsg.epoch = epoch' := hepiff.mp hep
      rw [if_pos hep]
      step with MsgTypeRefines.eq_agrees hmsg.2.1 hcktriv
      by_cases hty : b = true
      · have htyM : modelMsg.type = Model.Braid.MsgType.ekCt1Ack := b_post.mp hty
        rw [if_pos hty]
        step*
        · rename_i hdm2
          have hdm : modelMsg.data = none := by
            have hdd := hmsg.2.2
            rcases hx : modelMsg.data with _ | mc
            · rfl
            · exfalso; rw [hdm2, hx] at hdd; exact hdd
          unfold Model.Braid.receive
          simp only [hepM, htyM, hdm]
          split
          · exact ⟨trivial, he, ha, hhdr, hlen32, hhek32, hencapsr, hct1, hdecr, heksize⟩
          · rename_i hcond; exact absurd hcond (by simp)
        · rename_i hdm2
          obtain ⟨mc, hdm, hidx, hcw⟩ : ∃ mc, modelMsg.data = some mc ∧ c.index.val = mc.index ∧ CodewordOf mc.source c := by
            have hdd := hmsg.2.2
            rcases hx : modelMsg.data with _ | mc
            · exfalso; rw [hdm2, hx] at hdd; exact hdd
            · exact ⟨mc, rfl, by rw [hdm2, hx] at hdd; exact hdd⟩
          obtain ⟨advanced, ek_dec1, hadd⟩ :
              ∃ advanced ek_dec1, ek_dec.add_chunk c = ok (advanced, ek_dec1) := by
            obtain ⟨⟨a1, a2⟩, ha12⟩ := hdadd ek_dec c; exact ⟨a1, a2, ha12⟩
          simp only [hadd]
          step*
          obtain ⟨hfit, hsame⟩ : ChunkFits _ mc := by
            have h := hhonest mc hdm hepM
            rw [htyM] at h
            exact h
          obtain ⟨omsg, homsg⟩ := hdmsg ek_dec1
          obtain ⟨hekdecr, hmsgeq⟩ := DecoderRefines.add_message hdecr hfit hsame hcw hidx hadd homsg
          simp only [homsg]
          rcases hom : omsg with _ | ekVecRaw
          · have hMnone : (ekDecM.addChunk mc).message = none := by
              rw [hom] at hmsgeq; simpa using hmsgeq.symm
            simp only [bind_tc_ok]
            unfold Model.Braid.receive
            simp only [hepM, htyM, hdm, hMnone]
            split
            · exact ⟨trivial, he, ha, hhdr, hlen32, hhek32, hencapsr, hct1, hekdecr,
                by rw [Model.Braid.Decoder.addChunk_size]; exact heksize⟩
            · rename_i hcond; exact absurd hcond (by simp)
          · obtain ⟨ekVectorM, hMsome⟩ :
                ∃ ekVectorM, (ekDecM.addChunk mc).message = some ekVectorM := by
              rw [hom] at hmsgeq
              rcases hy : (ekDecM.addChunk mc).message with _ | ekVectorM
              · rw [hy] at hmsgeq; simp at hmsgeq
              · exact ⟨ekVectorM, rfl⟩
            have hekVecEq : vecOf ekVecRaw = ekVectorM := by
              rw [hom, hMsome] at hmsgeq; simpa using hmsgeq
            have hekVecSlice : sliceOf ekVecRaw.deref = ekVectorM := by
              simp only [sliceOf, alloc.vec.Vec.deref, vecOf] at hekVecEq ⊢; exact hekVecEq
            simp only [bind_tc_ok]
            have hekvL : ekVecRaw.deref.length = K.ekSize := by
              rw [deref_length, hekVecEq, Model.Braid.Decoder.message_length _ _ hMsome,
                Model.Braid.Decoder.addChunk_size]; exact heksize
            obtain ⟨rb, hrb, hrbiff⟩ :=
              hvalek header.deref ekVecRaw.deref ekSeedM hekM hlen32 hhek32 hekvL hhdrslice
            simp only [hrb, bind_tc_ok]
            by_cases hrbval : rb = true
            · simp only [if_pos hrbval]
              have hhashEq : K.hashEk ekSeedM ekVectorM = hekM := by
                rw [← hekVecSlice]; exact hrbiff.mp hrbval
              have hct1slice : sliceOf ct1.deref = ct1M := by
                simp only [sliceOf, alloc.vec.Vec.deref, vecOf] at hct1 ⊢; exact hct1
              have hlen : ct1.length +
                  (K.encaps2 encapsSecretM ekSeedM (sliceOf ekVecRaw.deref)).length + 96
                  ≤ Usize.max := by
                obtain ⟨ct2raw, hct2raw, hct2rawval⟩ := hencapsr ekVecRaw.deref hekvL
                obtain ⟨r, hr, hrbound⟩ := hencaps2len encaps ekVecRaw.deref
                rw [hct2raw] at hr
                injection hr with hr
                have hb := hrbound ct2raw hr.symm
                have hlen2 : (K.encaps2 encapsSecretM ekSeedM (sliceOf ekVecRaw.deref)).length
                    = ct2raw.length := by
                  rw [← hct2rawval]; simp [vecOf]
                rw [hlen2]
                have hct1bound : ct1.length ≤ 4096 := by
                  simpa [Tacenta.BraidT1.State.ct1_bounded] using hct1b
                scalar_tac
              step with finish_encaps_refines hmac hea epoch1 auth encaps ct1.deref
                ekVecRaw.deref ha hct1slice hencapsr hekvL hlen
              unfold Model.Braid.receive
              simp only [hepM, htyM, hdm, hMsome]
              split
              · split
                · rename_i hcond
                  first
                    | exact absurd hcond (by simp [hhashEq])
                    | exact absurd (by simp [hhashEq]) hcond
                · rw [he, hekVecSlice] at s4_post
                  exact ⟨trivial, s4_post⟩
              · rename_i hcond
                first
                  | exact absurd hcond (by simp)
                  | exact absurd (by simp [hepM, htyM]) hcond
            · rw [if_neg hrbval]
              have hhashNeq : K.hashEk ekSeedM ekVectorM ≠ hekM := by
                rw [← hekVecSlice]; exact fun h => hrbval (hrbiff.mpr h)
              unfold Model.Braid.receive
              simp only [hepM, htyM, hdm, hMsome]
              split
              · split
                · trivial
                · rename_i hcond
                  first
                    | exact absurd hcond (by simp [hhashNeq])
                    | exact absurd (by simp [hhashNeq]) hcond
              · rename_i hcond
                first
                  | exact absurd hcond (by simp)
                  | exact absurd (by simp [hepM, htyM]) hcond
      · have htyM : ¬ modelMsg.type = Model.Braid.MsgType.ekCt1Ack := fun h => hty (b_post.mpr h)
        rw [if_neg hty]
        unfold Model.Braid.receive
        simp only [hepM]
        split
        · exfalso; simp_all
        · exact ⟨trivial, he, ha, hhdr, hlen32, hhek32, hencapsr, hct1, hdecr, heksize⟩
    · have hepM : ¬ modelMsg.epoch = epoch' := fun h => hep (hepiff.mpr h)
      rw [if_neg hep]
      unfold Model.Braid.receive
      simp only
      split
      · exfalso; simp_all
      · exact ⟨trivial, he, ha, hhdr, hlen32, hhek32, hencapsr, hct1, hdecr, heksize⟩
  case EkSentCt1Received.ekSentCt1Received =>
    rename_i epoch1 auth kp ct1 ct2_dec epoch' auth' dk ct1M ct2DecM
    have he := hrel.1
    obtain ⟨_, ha, hkpr, hct1, hct1len, hdecr, hdsize⟩ := hrel
    have hepiff : msg.epoch = epoch1 ↔ modelMsg.epoch = epoch' := by
      have h1 := hmsg.1
      constructor
      · intro h; rw [h, he] at h1; exact h1.symm
      · intro h; rw [h] at h1; rw [← he] at h1; scalar_tac
    have hct2triv : MsgTypeRefines MsgType.Ct2 Model.Braid.MsgType.ct2 := trivial
    unfold Braid.step_receive
    unfold State.epoch
    simp only [bind_tc_ok]
    by_cases hep : msg.epoch = epoch1
    · have hepM : modelMsg.epoch = epoch' := hepiff.mp hep
      rw [if_pos hep]
      step with MsgTypeRefines.eq_agrees hmsg.2.1 hct2triv
      by_cases hty : b = true
      · have htyM : modelMsg.type = Model.Braid.MsgType.ct2 := b_post.mp hty
        rw [if_pos hty]
        step*
        · rename_i hdm2
          have hdm : modelMsg.data = none := by
            have hdd := hmsg.2.2
            rcases hx : modelMsg.data with _ | mc
            · rfl
            · exfalso; rw [hdm2, hx] at hdd; exact hdd
          unfold Model.Braid.receive
          simp only [hepM, htyM, hdm]
          split
          · exact ⟨trivial, he, ha, hkpr, hct1, hct1len, hdecr, hdsize⟩
          · rename_i hcond; exact absurd hcond (by simp)
        · rename_i hdm2
          obtain ⟨mc, hdm, hidx, hcw⟩ : ∃ mc, modelMsg.data = some mc ∧ c.index.val = mc.index ∧ CodewordOf mc.source c := by
            have hdd := hmsg.2.2
            rcases hx : modelMsg.data with _ | mc
            · exfalso; rw [hdm2, hx] at hdd; exact hdd
            · exact ⟨mc, rfl, by rw [hdm2, hx] at hdd; exact hdd⟩
          obtain ⟨advanced, ct2_dec1, hadd⟩ :
              ∃ advanced ct2_dec1, ct2_dec.add_chunk c = ok (advanced, ct2_dec1) := by
            obtain ⟨⟨a1, a2⟩, ha12⟩ := hdadd ct2_dec c; exact ⟨a1, a2, ha12⟩
          simp only [hadd]
          step*
          obtain ⟨hfit, hsame⟩ : ChunkFits _ mc := by
            have h := hhonest mc hdm hepM
            rw [htyM] at h
            exact h
          have haddSize : (ct2DecM.addChunk mc).size = K.ct2Size + Model.Braid.macSize := by
            unfold Model.Braid.Decoder.addChunk; split <;> simp [hdsize]
          obtain ⟨omsg, homsg⟩ := hdmsg ct2_dec1
          obtain ⟨hct2decr, hmsgeq⟩ := DecoderRefines.add_message hdecr hfit hsame hcw hidx hadd homsg
          simp only [homsg]
          rcases hom : omsg with _ | framedRaw
          · have hMnone : (ct2DecM.addChunk mc).message = none := by
              rw [hom] at hmsgeq; simpa using hmsgeq.symm
            simp only [bind_tc_ok]
            unfold Model.Braid.receive
            simp only [hepM, htyM, hdm, hMnone]
            split
            · exact ⟨trivial, he, ha, hkpr, hct1, hct1len, hct2decr, haddSize⟩
            · rename_i hcond; exact absurd hcond (by simp)
          · obtain ⟨framedM, hMsome⟩ :
                ∃ framedM, (ct2DecM.addChunk mc).message = some framedM := by
              rw [hom] at hmsgeq
              rcases hy : (ct2DecM.addChunk mc).message with _ | framedM
              · rw [hy] at hmsgeq; simp at hmsgeq
              · exact ⟨framedM, rfl⟩
            have hframedEq : vecOf framedRaw = framedM := by
              rw [hom, hMsome] at hmsgeq; simpa using hmsgeq
            have hframedLen : framedM.length = K.ct2Size + Model.Braid.macSize :=
              (Model.Braid.Decoder.message_length _ _ hMsome).trans haddSize
            have hframedRawLen : framedRaw.length = K.ct2Size + Model.Braid.macSize := by
              have hl : framedRaw.length = framedM.length := by
                have := congrArg List.length hframedEq
                simpa [vecOf] using this
              rw [hl, hframedLen]
            simp only [bind_tc_ok]
            obtain ⟨lv, hlv, hlveq⟩ := hct2len
            obtain ⟨lv2, hlv2, hlv2bound⟩ := hct2lenB
            rw [hlv] at hlv2; injection hlv2 with hlv2; subst hlv2
            simp only [hlv]
            step*
            · simp only [MAC_LEN]; scalar_tac
            · rename_i hcond
              exfalso
              have hi2eq : i2.val = K.ct2Size + Model.Braid.macSize := by
                rw [i2_post, ← hlveq, ← macLen_agrees]
              have hlenval : framedRaw.len.val = framedRaw.length := by
                simp [global_simps]
              simp only [bne_iff_ne, ne_eq] at hcond
              exact hcond (by scalar_tac)
            · -- Transition 5's `checked_add` came back `none`: unreachable below
              -- the ceiling `hepoch` keeps the state under.
              rename_i ho1
              exfalso
              rw [ho1] at o1_post
              simp only [Tacenta.BraidT1.State.epoch_val] at hepoch
              simp at o1_post
              scalar_tac
            · simp only [alloc.vec.Vec.deref, Slice.length]
              have hi2eq : i2.val = K.ct2Size + Model.Braid.macSize := by
                rw [i2_post, ← hlveq, ← macLen_agrees]
              scalar_tac
            · rename_i ho1
              have hne : next_epoch.val = epoch1.val + 1 := by
                have h := o1_post
                rw [ho1] at h
                exact h.2.1
              have hct1slice : sliceOf ct1.deref = ct1M := by
                simp only [sliceOf, alloc.vec.Vec.deref, vecOf] at hct1 ⊢; exact hct1
              have hframedslice : sliceOf framedRaw.deref = framedM := by
                simp only [sliceOf, alloc.vec.Vec.deref, vecOf] at hframedEq ⊢; exact hframedEq
              have hct2slice : sliceOf ct2 = framedM.take K.ct2Size := by
                have h : sliceOf ct2 = List.take lv.val (sliceOf framedRaw.deref) := by
                  simp only [sliceOf, ct2_post3, List.map_take]
                rw [h, hframedslice, hlveq]
              have hmacslice : sliceOf mac = framedM.drop K.ct2Size := by
                have h : sliceOf mac = List.drop lv.val (sliceOf framedRaw.deref) := by
                  simp only [sliceOf, ct2_post4, List.map_drop]
                rw [h, hframedslice, hlveq]
              obtain ⟨raw, hrawcall, hrawval⟩ := hkpr ct1.deref ct2
                (by rw [deref_length, hct1]; exact hct1len)
                (by
                  have h := congrArg List.length hct2slice
                  simp only [sliceOf, List.length_map, List.length_take, hframedLen,
                    Model.Braid.macSize] at h
                  simp only [Slice.length]; omega)
              simp only [hrawcall]
              step*
              have hs2 : sliceOf s2 = keyOf raw := by
                simp only [sliceOf, Array.to_slice, keyOf] at s2_post ⊢
                rw [s2_post]
              step with kdf_ok_refines hkdf s2 (keyOf raw) hs2 epoch1
              -- Wrap the epoch key, wipe the raw secret, read the key back
              -- through `key[..]`: the same three assumptions transition 7 uses.
              step with Tacenta.BraidT1.zeroizing_new_spec hz
              step with Tacenta.BraidT1.array_zeroize_spec hzz
              step with Tacenta.BraidT1.zeroizing_deref_spec ‹_›
              step with Tacenta.BraidT1.index_full_spec hrf
              have hs3 : sliceOf s3 = keyOf a := by
                rw [a1_post] at s3_post
                simp only [sliceOf, Array.to_slice, keyOf] at s3_post ⊢
                rw [s3_post]
              step with Auth.update_refines hkdf hz auth epoch1 s3
              step with Auth.mac_ct_refines hmac auth1 epoch1 ct1.deref ct2 ct1M
                (framedM.take K.ct2Size) hct1slice hct2slice (by
                  have hct1bound : ct1.length ≤ 4096 := by
                    simpa [Tacenta.BraidT1.State.ct1_bounded] using hct1b
                  have hct2bound : ct2.length ≤ 4096 := by rw [ct2_post1]; scalar_tac
                  simp only [alloc.vec.Vec.deref]
                  scalar_tac)
              step
              have hs5 : sliceOf s5 = keyOf a2 := by
                simp only [sliceOf, Array.to_slice, keyOf] at s5_post ⊢
                rw [s5_post]
              step with mac_eq_agrees s5 mac
              have hkeyeq : keyOf a = Model.Braid.kdfOk
                  (K.decaps dk ct1M (framedM.take K.ct2Size)) epoch1.val := by
                rw [a_post, hrawval, hct1slice, hct2slice]
              have hauth1eq : AuthOf auth1 = Model.Braid.Auth.update auth' epoch1.val
                  (Model.Braid.kdfOk (K.decaps dk ct1M (framedM.take K.ct2Size)) epoch1.val) := by
                rw [auth1_post, hs3, hkeyeq, ha]
              have haeq : keyOf a2 = Model.Braid.Auth.macCt (AuthOf auth1) epoch1.val
                  (ct1M ++ framedM.take K.ct2Size) := a2_post
              by_cases hb1 : b1 = true
              · rw [if_pos hb1]
                have hmaceq : Model.Braid.Auth.macCt (AuthOf auth1) epoch1.val
                    (ct1M ++ framedM.take K.ct2Size) = framedM.drop K.ct2Size := by
                  rw [← haeq]
                  have := b1_post.mp hb1
                  rw [hs5, hmacslice] at this
                  exact this
                step with hdr_decoder_refines hea hheaderlen
                have hdsize2 : (Model.Braid.Decoder.new
                    (Model.Braid.headerSize + Model.Braid.macSize)).size
                    = Model.Braid.headerSize + Model.Braid.macSize := rfl
                unfold Model.Braid.receive
                simp only [hepM, htyM, hdm, hMsome]
                split
                · split
                  · refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
                    · exact he
                    · rw [a1_post, hkeyeq, he]
                    · rw [hne, he]
                    · rw [hauth1eq, he]
                    · exact d_post
                    · exact hdsize2
                  · rename_i hcond
                    exact absurd hcond (by rw [← he, ← hauth1eq]; simp [hmaceq])
                · rename_i hcond; exact absurd hcond (by simp)
              · rw [if_neg hb1]
                have hmacneq : Model.Braid.Auth.macCt (AuthOf auth1) epoch1.val
                    (ct1M ++ framedM.take K.ct2Size) ≠ framedM.drop K.ct2Size := by
                  rw [← haeq]
                  intro heqv
                  apply hb1
                  apply b1_post.mpr
                  rw [hs5, hmacslice]
                  exact heqv
                unfold Model.Braid.receive
                simp only [hepM, htyM, hdm, hMsome]
                split
                · split
                  · rename_i hcond
                    exact absurd hcond (by rw [← he, ← hauth1eq]; simp [hmacneq])
                  · trivial
                · rename_i hcond; exact absurd hcond (by simp)
      · have htyM : ¬ modelMsg.type = Model.Braid.MsgType.ct2 := fun h => hty (b_post.mpr h)
        rw [if_neg hty]
        unfold Model.Braid.receive
        simp only [hepM]
        split
        · exfalso; simp_all
        · exact ⟨trivial, he, ha, hkpr, hct1, hct1len, hdecr, hdsize⟩
    · have hepM : ¬ modelMsg.epoch = epoch' := fun h => hep (hepiff.mpr h)
      rw [if_neg hep]
      unfold Model.Braid.receive
      simp only
      split
      · exfalso; simp_all
      · exact ⟨trivial, he, ha, hkpr, hct1, hct1len, hdecr, hdsize⟩
  case NoHeaderReceived.noHeaderReceived =>
    rename_i epoch1 auth hdr_dec epoch' auth' hdrDecM
    have he := hrel.1
    obtain ⟨_, ha, hdecr, hdsize⟩ := hrel
    have hepiff : msg.epoch = epoch1 ↔ modelMsg.epoch = epoch' := by
      have h1 := hmsg.1
      constructor
      · intro h; rw [h, he] at h1; exact h1.symm
      · intro h; rw [h] at h1; rw [← he] at h1; scalar_tac
    have hhdrtriv : MsgTypeRefines MsgType.Hdr Model.Braid.MsgType.hdr := trivial
    unfold Braid.step_receive
    unfold State.epoch
    simp only [bind_tc_ok]
    by_cases hep : msg.epoch = epoch1
    · have hepM : modelMsg.epoch = epoch' := hepiff.mp hep
      rw [if_pos hep]
      step with MsgTypeRefines.eq_agrees hmsg.2.1 hhdrtriv
      by_cases hty : b = true
      · have htyM : modelMsg.type = Model.Braid.MsgType.hdr := b_post.mp hty
        rw [if_pos hty]
        step*
        · rename_i hdm2
          have hdm : modelMsg.data = none := by
            have hdd := hmsg.2.2
            rcases hx : modelMsg.data with _ | mc
            · rfl
            · exfalso; rw [hdm2, hx] at hdd; exact hdd
          unfold Model.Braid.receive
          simp only [hepM, htyM, hdm]
          split
          · exact ⟨trivial, he, ha, hdecr, hdsize⟩
          · rename_i hcond; exact absurd hcond (by simp)
        · rename_i hdm2
          obtain ⟨mc, hdm, hidx, hcw⟩ : ∃ mc, modelMsg.data = some mc ∧ c.index.val = mc.index ∧ CodewordOf mc.source c := by
            have hdd := hmsg.2.2
            rcases hx : modelMsg.data with _ | mc
            · exfalso; rw [hdm2, hx] at hdd; exact hdd
            · exact ⟨mc, rfl, by rw [hdm2, hx] at hdd; exact hdd⟩
          obtain ⟨advanced, hdr_dec1, hadd⟩ :
              ∃ advanced hdr_dec1, hdr_dec.add_chunk c = ok (advanced, hdr_dec1) := by
            obtain ⟨⟨a1, a2⟩, ha12⟩ := hdadd hdr_dec c; exact ⟨a1, a2, ha12⟩
          simp only [hadd]
          step*
          obtain ⟨hfit, hsame⟩ : ChunkFits _ mc := by
            have h := hhonest mc hdm hepM
            rw [htyM] at h
            exact h
          have haddSize : (hdrDecM.addChunk mc).size = Model.Braid.headerSize + Model.Braid.macSize := by
            unfold Model.Braid.Decoder.addChunk; split <;> simp [hdsize]
          obtain ⟨omsg, homsg⟩ := hdmsg hdr_dec1
          obtain ⟨hhdrdecr, hmsgeq⟩ := DecoderRefines.add_message hdecr hfit hsame hcw hidx hadd homsg
          simp only [homsg]
          rcases hom : omsg with _ | framedRaw
          · have hMnone : (hdrDecM.addChunk mc).message = none := by
              rw [hom] at hmsgeq; simpa using hmsgeq.symm
            simp only [bind_tc_ok]
            unfold Model.Braid.receive
            simp only [hepM, htyM, hdm, hMnone]
            split
            · exact ⟨trivial, he, ha, hhdrdecr, haddSize⟩
            · rename_i hcond; exact absurd hcond (by simp)
          · obtain ⟨framedM, hMsome⟩ :
                ∃ framedM, (hdrDecM.addChunk mc).message = some framedM := by
              rw [hom] at hmsgeq
              rcases hy : (hdrDecM.addChunk mc).message with _ | framedM
              · rw [hy] at hmsgeq; simp at hmsgeq
              · exact ⟨framedM, rfl⟩
            have hframedEq : vecOf framedRaw = framedM := by
              rw [hom, hMsome] at hmsgeq; simpa using hmsgeq
            have hframedLen : framedM.length = Model.Braid.headerSize + Model.Braid.macSize :=
              (Model.Braid.Decoder.message_length _ _ hMsome).trans haddSize
            have hframedRawLen : framedRaw.length = Model.Braid.headerSize + Model.Braid.macSize := by
              have hl : framedRaw.length = framedM.length := by
                have := congrArg List.length hframedEq
                simpa [vecOf] using this
              rw [hl, hframedLen]
            simp only [bind_tc_ok]
            obtain ⟨hv, hhv, hhveq⟩ := hheaderlen
            obtain ⟨hv2, hhv2, hhv2bound⟩ := hheaderlenB
            rw [hhv] at hhv2; injection hhv2 with hhv2; subst hhv2
            simp only [hhv]
            step*
            · simp only [global_simps]; scalar_tac
            · rename_i hcond
              exfalso
              have hi2eq : i2.val = Model.Braid.headerSize + Model.Braid.macSize := by
                rw [i2_post, ← hhveq, ← macLen_agrees]
              have hlenval : framedRaw.len.val = framedRaw.length := by
                simp [global_simps]
              simp only [bne_iff_ne, ne_eq] at hcond
              exact hcond (by scalar_tac)
            · simp only [alloc.vec.Vec.deref, Slice.length]
              scalar_tac
            · have hframedslice : sliceOf framedRaw.deref = framedM := by
                simp only [sliceOf, alloc.vec.Vec.deref, vecOf] at hframedEq ⊢; exact hframedEq
              have hheaderslice : sliceOf header = framedM.take Model.Braid.headerSize := by
                have h : sliceOf header = List.take hv.val (sliceOf framedRaw.deref) := by
                  simp only [sliceOf, header_post3, List.map_take]
                rw [h, hframedslice, hhveq]
              have hmacslice : sliceOf mac = framedM.drop Model.Braid.headerSize := by
                have h : sliceOf mac = List.drop hv.val (sliceOf framedRaw.deref) := by
                  simp only [sliceOf, header_post4, List.map_drop]
                rw [h, hframedslice, hhveq]
              have hheaderbound : header.length ≤ 4096 := by rw [header_post1]; scalar_tac
              step with Auth.mac_hdr_refines hmac auth epoch1 header
                (framedM.take Model.Braid.headerSize) hheaderslice (by scalar_tac)
              step
              have hs1 : sliceOf s1 = keyOf a := by
                simp only [sliceOf, Array.to_slice, keyOf] at s1_post ⊢
                rw [s1_post]
              step with mac_eq_agrees s1 mac
              have hkeyeq : keyOf a = Model.Braid.Auth.macHdr auth' epoch1.val
                  (framedM.take Model.Braid.headerSize) := by
                rw [a_post, ha]
              obtain ⟨ekv, hekv, hekveq⟩ := hekveclen
              simp only [hekv]
              step*
              · obtain ⟨ek_dec0, hnewd, hnewdsim⟩ := hea.2 ekv
                simp only [hnewd]
                rename_i hb1
                have hmaceq : Model.Braid.Auth.macHdr auth' epoch1.val
                    (framedM.take Model.Braid.headerSize) = framedM.drop Model.Braid.headerSize := by
                  rw [← hkeyeq]
                  have hthis := b1_post.mp hb1
                  rw [hs1] at hthis
                  rw [hmacslice] at hthis
                  exact hthis
                unfold Model.Braid.receive
                simp only [hepM, htyM, hdm, hMsome]
                split
                · split
                  · refine ⟨trivial, he, ha, ?_, ?_, ?_, ?_, ?_⟩
                    · have hveq : vecOf v = sliceOf header := by simp [vecOf, sliceOf, v_post]
                      rw [hveq, hheaderslice]
                      exact (List.take_append_drop 32 _).symm
                    · simp only [List.length_take, hframedLen, Model.Braid.headerSize,
                        Model.Braid.macSize]
                      omega
                    · simp only [List.length_drop, List.length_take, hframedLen,
                        Model.Braid.headerSize, Model.Braid.macSize]
                      omega
                    · rw [← hekveq]; exact hnewdsim
                    · simp [Model.Braid.Decoder.new]
                  · rename_i hcond
                    exact absurd hcond (by rw [← he]; simp [hmaceq])
                · rename_i hcond; exact absurd hcond (by simp)
              · rename_i hb1
                have hmacneq : Model.Braid.Auth.macHdr auth' epoch1.val
                    (framedM.take Model.Braid.headerSize) ≠ framedM.drop Model.Braid.headerSize := by
                  rw [← hkeyeq]
                  intro heqv
                  apply hb1; apply b1_post.mpr
                  rw [hs1, hmacslice]; exact heqv
                unfold Model.Braid.receive
                simp only [hepM, htyM, hdm, hMsome]
                split
                · split
                  · rename_i hcond
                    exact absurd hcond (by rw [← he]; simp [hmacneq])
                  · trivial
                · rename_i hcond; exact absurd hcond (by simp)
      · have htyM : ¬ modelMsg.type = Model.Braid.MsgType.hdr := fun h => hty (b_post.mpr h)
        rw [if_neg hty]
        unfold Model.Braid.receive
        simp only [hepM]
        split
        · exfalso; simp_all
        · exact ⟨trivial, he, ha, hdecr, hdsize⟩
    · have hepM : ¬ modelMsg.epoch = epoch' := fun h => hep (hepiff.mpr h)
      rw [if_neg hep]
      unfold Model.Braid.receive
      simp only
      split
      · exfalso; simp_all
      · exact ⟨trivial, he, ha, hdecr, hdsize⟩

/-- `step_receive` needs `ct1_bounded`/`epoch_val` for the *clone* it actually
runs on, not the original `self.state`. But a clone only ever holds a value
already pinned to the same `model` the original does (`State.clone_refines`),
so whichever constructor `self.state` and its clone share, they carry the
same `ct1` bytes and the same epoch, and the bound/value transfers across. -/
theorem State.clone_bounds_refines {K : Model.Braid.Kem} {self s : State}
    {model : Model.Braid.BraidState}
    (hrel : StateRefines K self model) (hrelS : StateRefines K s model) :
    (Tacenta.BraidT1.State.epoch_val s).val = (Tacenta.BraidT1.State.epoch_val self).val ∧
    (Tacenta.BraidT1.State.ct1_bounded self → Tacenta.BraidT1.State.ct1_bounded s) := by
  have hlen : ∀ {a b : alloc.vec.Vec Std.U8} {c : Model.Braid.Bytes},
      vecOf a = c → vecOf b = c → a.length = b.length := by
    intro a b c ha hb
    have := congrArg List.length (ha.trans hb.symm)
    simpa [vecOf] using this
  rcases self with _|_|_|_|_|_|_|_|_|_|_|_ <;> cases model <;>
    simp only [StateRefines] at hrel <;> try exact hrel.elim
  case KeysUnsampled.keysUnsampled =>
    cases s <;> simp_all [StateRefines, Tacenta.BraidT1.State.epoch_val,
      Tacenta.BraidT1.State.ct1_bounded]
  case KeysSampled.keysSampled =>
    cases s <;> simp_all [StateRefines, Tacenta.BraidT1.State.epoch_val,
      Tacenta.BraidT1.State.ct1_bounded]
  case HeaderSent.headerSent =>
    cases s <;> simp_all [StateRefines, Tacenta.BraidT1.State.epoch_val,
      Tacenta.BraidT1.State.ct1_bounded]
  case Ct1Received.ct1Received =>
    cases s <;> simp only [StateRefines] at hrelS <;> try exact hrelS.elim
    obtain ⟨he, -, -, hveq, -⟩ := hrel
    obtain ⟨heS, -, -, hveqS, -⟩ := hrelS
    refine ⟨by simp [Tacenta.BraidT1.State.epoch_val, he, heS], ?_⟩
    simp only [Tacenta.BraidT1.State.ct1_bounded]
    intro h
    exact (hlen hveq hveqS) ▸ h
  case EkSentCt1Received.ekSentCt1Received =>
    cases s <;> simp only [StateRefines] at hrelS <;> try exact hrelS.elim
    obtain ⟨he, -, -, hveq, -, -, -⟩ := hrel
    obtain ⟨heS, -, -, hveqS, -, -, -⟩ := hrelS
    refine ⟨by simp [Tacenta.BraidT1.State.epoch_val, he, heS], ?_⟩
    simp only [Tacenta.BraidT1.State.ct1_bounded]
    intro h
    exact (hlen hveq hveqS) ▸ h
  case NoHeaderReceived.noHeaderReceived =>
    cases s <;> simp_all [StateRefines, Tacenta.BraidT1.State.epoch_val,
      Tacenta.BraidT1.State.ct1_bounded]
  case HeaderReceived.headerReceived =>
    cases s <;> simp_all [StateRefines, Tacenta.BraidT1.State.epoch_val,
      Tacenta.BraidT1.State.ct1_bounded]
  case Ct1Sampled.ct1Sampled =>
    cases s <;> simp only [StateRefines] at hrelS <;> try exact hrelS.elim
    obtain ⟨he, -, -, -, -, -, hveq, -, -, -⟩ := hrel
    obtain ⟨heS, -, -, -, -, -, hveqS, -, -, -⟩ := hrelS
    refine ⟨by simp [Tacenta.BraidT1.State.epoch_val, he, heS], ?_⟩
    simp only [Tacenta.BraidT1.State.ct1_bounded]
    intro h
    exact (hlen hveq hveqS) ▸ h
  case EkReceivedCt1Sampled.ekReceivedCt1Sampled =>
    cases s <;> simp only [StateRefines] at hrelS <;> try exact hrelS.elim
    obtain ⟨he, -, -, hveq, -, -, -⟩ := hrel
    obtain ⟨heS, -, -, hveqS, -, -, -⟩ := hrelS
    refine ⟨by simp [Tacenta.BraidT1.State.epoch_val, he, heS], ?_⟩
    simp only [Tacenta.BraidT1.State.ct1_bounded]
    intro h
    exact (hlen hveq hveqS) ▸ h
  case Ct1Acknowledged.ct1Acknowledged =>
    cases s <;> simp only [StateRefines] at hrelS <;> try exact hrelS.elim
    obtain ⟨he, -, -, -, -, -, hveq, -, -⟩ := hrel
    obtain ⟨heS, -, -, -, -, -, hveqS, -, -⟩ := hrelS
    refine ⟨by simp [Tacenta.BraidT1.State.epoch_val, he, heS], ?_⟩
    simp only [Tacenta.BraidT1.State.ct1_bounded]
    intro h
    exact (hlen hveq hveqS) ▸ h
  case Ct2Sampled.ct2Sampled =>
    cases s <;> simp_all [StateRefines, Tacenta.BraidT1.State.epoch_val,
      Tacenta.BraidT1.State.ct1_bounded]
  case Failed.failed =>
    cases s <;> simp_all [StateRefines, Tacenta.BraidT1.State.epoch_val,
      Tacenta.BraidT1.State.ct1_bounded]

/-- `Braid.receive` clones the state first (leaving the caller's copy
untouched, per `State.clone_refines`), runs `step_receive` on the clone, then
reports the epoch via `Braid.reported` when the step produced no output:
`step_receive`'s own `OptionOutputRefines` already forces the model's output
to be `none` in that case, matching `stay`'s `(epoch - 1, none, state)`
shape. When the step *did* produce an output, the real code reports that
output's own `key_epoch` directly instead of calling `Braid.reported`, and
every model transition that emits `some output` sets its own leading `Nat`
to exactly that output's `keyEpoch`, so `OutputRefines`'s first component is
already the fact needed here, no separate epoch computation to prove. -/
theorem Braid.receive_refines (hka : KemAgreesFor K) (hea : ErasureAgrees)
    (hmac : BraidHmacAgrees) (hkdf : BraidHkdfAgrees)
    (hlens : KemLenAgrees K) (hvalek : ValidateEkAgrees K)
    (hencaps2len : Tacenta.BraidT1.Encapsulate2Total)
    (hdadd : Tacenta.BraidT1.DecoderAddChunkTotal)
    (hdmsg : Tacenta.BraidT1.DecoderMessageTotal)
    (hct1lenB : Tacenta.BraidT1.Ct1LenTotal) (hct2lenB : Tacenta.BraidT1.Ct2LenTotal)
    (hheaderlenB : Tacenta.BraidT1.HeaderLenTotal)
    (hkcl : KemCloneAgrees) (hecl : ErasureCloneAgrees)
    (henc : Tacenta.BraidT1.EncoderCloneTotal) (hdec : Tacenta.BraidT1.DecoderCloneTotal)
    (hkp : Tacenta.BraidT1.KeyPairCloneTotal) (hes : Tacenta.BraidT1.EncapsStateCloneTotal)
    (hopt : Tacenta.BraidT1.OptionCloneTotal)
    (hz : Tacenta.BraidT1.ZeroizingArrayRoundTrip) (hzz : Tacenta.BraidT1.ArrayZeroizeTotal)
    (hrf : Tacenta.BraidT1.RangeFullIndexTotal)
    (self : Braid) (msg : tacenta_braid.Msg)
    (hct1b : Tacenta.BraidT1.State.ct1_bounded self.state)
    (hepoch : (Tacenta.BraidT1.State.epoch_val self.state).val < Std.U64.max)
    {model : Model.Braid.BraidState} {modelMsg : Model.Braid.Msg}
    (hrel : StateRefines K self.state model) (hmsg : MsgRefines msg modelMsg)
    (hhonest : HonestChunk model modelMsg) :
    Braid.receive self msg ⦃ fun (i, out, next) =>
      i.val = (Model.Braid.receive K model modelMsg).2.2.epoch - 1 ∧
      OptionOutputRefines out (Model.Braid.receive K model modelMsg).2.1 ∧
      StateRefines K next.state (Model.Braid.receive K model modelMsg).2.2 ⦄ := by
  unfold Braid.receive
  step with State.clone_refines hkcl hecl henc hdec hkp hes hrel
  obtain ⟨hepocheq, hct1bimp⟩ := State.clone_bounds_refines hrel s_post
  step with step_receive_refines hka hea hmac hkdf hlens hvalek hencaps2len hdadd hdmsg
    hct1lenB hct2lenB hheaderlenB hz hzz hrf self s msg (hct1bimp hct1b) (by rw [hepocheq]; exact hepoch)
    s_post hmsg hhonest
  obtain ⟨hout, hnext⟩ := ‹_›
  rcases hom : out with _ | o
  · have hMnone : (Model.Braid.receive K model modelMsg).2.1 = none := by
      rw [hom] at hout; cases hM : (Model.Braid.receive K model modelMsg).2.1 with
      | none => rfl
      | some mo => rw [hM] at hout; exact hout.elim
    step with Braid.reported_refines K { state := next } (Model.Braid.receive K model modelMsg).2.2 hnext
    rw [hMnone]
    rename_i hi
    exact ⟨hi, trivial, hnext⟩
  · obtain ⟨mo, hMsome⟩ : ∃ mo, (Model.Braid.receive K model modelMsg).2.1 = some mo := by
      rw [hom] at hout
      cases hM : (Model.Braid.receive K model modelMsg).2.1 with
      | none => rw [hM] at hout; exact hout.elim
      | some mo => exact ⟨mo, rfl⟩
    rw [hom] at hout
    rw [hMsome] at hout
    step with hopt Output.Insts.CoreCloneClone (some o) (fun x _ => Tacenta.BraidT1.Output.clone_no_panic x)
    have hkeyepoch : o.key_epoch.val = (Model.Braid.receive K model modelMsg).2.2.epoch - 1 := by
      rw [hout.1, Model.Braid.receive_output_next_epoch K model modelMsg mo hMsome]
    refine ⟨hkeyepoch, ?_, hnext⟩
    rename_i ho1
    rw [ho1, hMsome]
    exact hout

end Tacenta.BraidT3
