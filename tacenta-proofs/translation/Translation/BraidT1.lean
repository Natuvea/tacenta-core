import Translation.TacentaBraid
import Translation.SessionT1

/-!
# T1 for the ML-KEM Braid: totality on what a peer sends

This crate is on the session's send and receive path. The agreement runs on every
message, driven by chunks a peer chose, so a panic here is a remote denial of
service reachable by anyone who can deliver one.

## Why this is smaller than it looks

The braid is an eleven-state machine over erasure-coded chunks, and only **one**
loop survives translation into this crate: the constant-time MAC comparison. The
erasure coding it rests on lives in `tacenta-erasure`, which is a verified zone
already with T1 complete, and the state machine itself branches rather than
loops. So the loop obligations here are one, not eleven.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.BraidT1

open tacenta_braid

/-- Comparing two authenticators cannot fail, **given that they are the same
length**, which is the condition `mac_eq` checks before entering the loop.

The precondition is the interesting part. The loop bounds itself on `a` and then
indexes **both** `a` and `b` at that index, so nothing inside it keeps the second
index in range. If a caller ever reached this loop with a shorter `b`, the
comparison would be an out-of-bounds read on attacker-supplied bytes. The check
is in the source; this is what makes it load-bearing rather than incidental. -/
theorem mac_eq_loop_no_panic (a b : Slice U8) (diff : U8) (i : Usize)
    (hlen : a.length ≤ b.length) :
    mac_eq_loop a b diff i ⦃ fun _ => True ⦄ := by
  unfold mac_eq_loop
  apply loop.spec_decr_nat
    (measure := fun p => a.length - p.2.val)
    (inv := fun _ => True)
  · rintro ⟨diffA, iA⟩ -
    simp only [mac_eq_loop.body]
    split
    · step*
    · simp
  · trivial

/-- And `mac_eq` itself, which refuses unequal lengths before it starts. -/
@[step]
theorem mac_eq_no_panic (a b : Slice U8) : mac_eq a b ⦃ fun _ => True ⦄ := by
  unfold mac_eq
  simp only []
  split
  · simp
  · step with mac_eq_loop_no_panic a b _ _ (by scalar_tac)

/-! ## The opaque surface: erasure coding, the KEM, and two KDF calls

`tacenta-braid` does not loop beyond `mac_eq`, but it calls out to two other
verified-adjacent crates and a KDF crate, none of which Aeneas can see inside.
Each opaque operation gets its own totality assumption below, per this
project's established rule: one axiom per crate that touches it, not one per
name, since Aeneas gives each crate its own copy even of an operation another
crate also assumes. -/

/-- The encoder never fails to start, and never fails to hand back its next
chunk (which may itself be `none`, meaning the source has nothing left to
send -- that is a value, not a failure). -/
def EncoderNewTotal : Prop :=
  ∀ (s : Slice U8), ∃ r, tacenta_erasure.Encoder.new s = ok r

def EncoderNextChunkTotal : Prop :=
  ∀ (e : tacenta_erasure.Encoder), ∃ r, tacenta_erasure.Encoder.next_chunk e = ok r

def EncoderCloneTotal : Prop :=
  ∀ (e : tacenta_erasure.Encoder),
    ∃ r, tacenta_erasure.Encoder.Insts.CoreCloneClone.clone e = ok r

/-- The decoder: constructing it, feeding it a chunk (whether or not that
chunk completes the message), and asking for the message so far (which is
`none` until enough chunks have arrived -- again a value, not a failure). -/
def DecoderNewTotal : Prop :=
  ∀ (n : Usize), ∃ r, tacenta_erasure.Decoder.new n = ok r

def DecoderAddChunkTotal : Prop :=
  ∀ (d : tacenta_erasure.Decoder) (c : tacenta_erasure.Chunk),
    ∃ r, tacenta_erasure.Decoder.add_chunk d c = ok r

def DecoderMessageTotal : Prop :=
  ∀ (d : tacenta_erasure.Decoder), ∃ r, tacenta_erasure.Decoder.message d = ok r

def DecoderCloneTotal : Prop :=
  ∀ (d : tacenta_erasure.Decoder),
    ∃ r, tacenta_erasure.Decoder.Insts.CoreCloneClone.clone d = ok r

/-- The KEM's four fixed-size-output constants, the same shape as the erasure
coder's `CHUNK_BYTES` and for the same reason. Each carries a concrete size
cap alongside its totality, not just headroom below `Usize.max`: a header,
encapsulation-key vector, or ciphertext genuinely is a few kilobytes at most
for any real ML-KEM parameter set, and more than one of these bounded values
gets summed at a single call site (`finish_encaps` sums a ciphertext against
another opaque bound), so two facts each individually "under `Usize.max`"
would not compose -- two concrete small caps do. -/
def HeaderLenTotal : Prop := ∃ v : Usize, tacenta_kem.HEADER_LEN = ok v ∧ v.val ≤ 4096
def EkVectorLenTotal : Prop := ∃ v : Usize, tacenta_kem.EK_VECTOR_LEN = ok v ∧ v.val ≤ 4096
def Ct1LenTotal : Prop := ∃ v : Usize, tacenta_kem.CT1_LEN = ok v ∧ v.val ≤ 4096
def Ct2LenTotal : Prop := ∃ v : Usize, tacenta_kem.CT2_LEN = ok v ∧ v.val ≤ 4096

/-- A randomness source that answers. Key-pair generation and the first
encapsulation each draw their randomness from the caller's `RngCore` through
`fill_bytes` (`tacenta-core/kem/src/lib.rs`), so their totality is the RNG's:
a `fill_bytes` that panics propagates through them, and a hypothesis that
said they return for *every* RNG would be stronger than the crate. This names
the condition, and the two totals below and `BraidT3.lean`'s `KemAgreesFor`
carry it as a premise; `step_send_no_panic`, `send_no_panic` and the send
refinements take it for the RNG they are handed. -/
def RngTotal {R : Type} (rc : rand_core_1.RngCore R) : Prop :=
  ∀ (rng : R) (buf : Slice U8), ∃ r, rc.fill_bytes rng buf = ok r

/-- The incremental key pair: generating one (the *outer* `Result` is what
this states is total, given an RNG that answers; the *inner*
`core.result.Result _ KemError` it returns is a real value the source
already branches on, `Ok` or `Err` both handled), reading its header or
encapsulation-key vector back out, and decapsulating against a peer's
ciphertext (same inner/outer split). -/
def KeyPairGenerateTotal : Prop :=
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (rng : R),
    RngTotal rc → ∃ r, tacenta_kem.IncrementalKeyPair.generate rc crc rng = ok r

-- Both carry the same concrete size cap as the fixed-size KEM constants
-- above, and for the same composing-sums reason: each is appended to (a MAC,
-- in `step_send`/`step_receive`), and a bare "this returns some vector"
-- leaves that append's own overflow check unprovable.
def KeyPairHeaderTotal : Prop :=
  ∀ (kp : tacenta_kem.IncrementalKeyPair),
    ∃ r : alloc.vec.Vec U8, tacenta_kem.IncrementalKeyPair.header kp = ok r ∧
      r.length ≤ 4096

def KeyPairEkVectorTotal : Prop :=
  ∀ (kp : tacenta_kem.IncrementalKeyPair),
    ∃ r : alloc.vec.Vec U8, tacenta_kem.IncrementalKeyPair.ek_vector kp = ok r ∧
      r.length ≤ 4096

def KeyPairDecapsulateTotal : Prop :=
  ∀ (kp : tacenta_kem.IncrementalKeyPair) (a b : Slice U8),
    ∃ r, tacenta_kem.IncrementalKeyPair.decapsulate kp a b = ok r

def KeyPairCloneTotal : Prop :=
  ∀ (kp : tacenta_kem.IncrementalKeyPair),
    ∃ r, tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone kp = ok r

/-- The two-step encapsulation state: sampling it (same inner/outer split as
key-pair generation, and the same `RngTotal` premise, since this is the
other call that draws randomness), finishing it against a peer's
encapsulation-key vector, and cloning it while it is held across a state
transition. -/
-- Both carry the same concrete size cap on the ciphertext vector they hand
-- back on success, for the same reason `KeyPairHeaderTotal` does:
-- `finish_encaps` sums one of these against another opaque bound before
-- appending a MAC, and two "under `Usize.max`" facts do not compose the way
-- two concrete caps do.
def Encapsulate1Total : Prop :=
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (s : Slice U8) (rng : R), RngTotal rc →
    ∃ r, tacenta_kem.encapsulate1 rc crc s rng = ok r ∧
      ∀ es (ct1 : alloc.vec.Vec U8) raw,
        r.1 = core.result.Result.Ok (es, ct1, raw) → ct1.length ≤ 4096

def Encapsulate2Total : Prop :=
  ∀ (es : tacenta_kem.EncapsState) (s : Slice U8),
    ∃ r, tacenta_kem.encapsulate2 es s = ok r ∧
      ∀ c : alloc.vec.Vec U8, r = core.result.Result.Ok c → c.length ≤ 4096

def EncapsStateCloneTotal : Prop :=
  ∀ (es : tacenta_kem.EncapsState),
    ∃ r, tacenta_kem.EncapsState.Insts.CoreCloneClone.clone es = ok r

/-- Checking a received encapsulation-key vector against the header that
committed to it. Refusing is a real, attacker-reachable outcome (`ok false`);
this states only that the check itself completes. -/
def ValidateEkTotal : Prop :=
  ∀ (a b : Slice U8), ∃ r, tacenta_kem.validate_ek a b = ok r

/-- The two KDF calls, braid's own copies distinct from the sparse ratchet's
`KdfCkTotal`/`KdfRkTotal` and the classical ratchet's, per the counting trap:
each translated crate gets its own opaque `hkdf_sha256`, and one proof does
not discharge another crate's copy. The HKDF premise is RFC 5869's output
bound of 8160 bytes, which the crate's own `expect` enforces, so the
hypothesis is stated exactly where the real operation returns
(`T1.HkdfTotal` says why); this crate asks for 32 or 64 bytes. -/
def HkdfSha256Total : Prop :=
  ∀ (N : Usize) (a b c : Slice U8), N.val ≤ 8160 →
    ∃ r, tacenta_kdf.hkdf_sha256 N a b c = ok r

def HmacSha256Total : Prop :=
  ∀ (a b : Slice U8), ∃ r, tacenta_kdf.hmac_sha256 a b = ok r

/-- Braid's own copy of the generic `Option::clone` axiom, which `SpqrT1.lean`
assumes too, for the same reason it needs one: cloning an
`Option` a caller reports back out (`receive`'s returned `Output`) is not
known total by the library, and this crate's copy of the axiom is a distinct
constant from its. -/
def OptionCloneTotal : Prop :=
  ∀ {T : Type} (inst : core.clone.Clone T) (o : Option T),
    (∀ x, o = some x → inst.clone x ⦃ fun y => y = x ⦄) →
    core.option.Option.Insts.CoreCloneClone.clone inst o ⦃ fun o' => o' = o ⦄

/-- The `zeroize` crate's touches, braid's own copies (the ratchet's and the
session's `Zeroizing` are distinct constants again, per the counting rule).
Wrapping a fixed-size byte array in `Zeroizing` and reading it straight back
through `Deref` returns the array: the wrapper changes what happens on drop,
not the value. Stated as one round trip rather than two bare totalities
because the two calls only ever appear together in this crate (`Auth.update`'s
64-byte HKDF output, and the 32-byte epoch key in transitions 5 and 7), and
the refinement needs the value, not just the return. -/
def ZeroizingArrayRoundTrip : Prop :=
  ∀ (N : Usize) (inst : zeroize.Zeroize (Array U8 N)) (a : Array U8 N),
    ∃ z, zeroize.Zeroizing.new inst a = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst z = ok a

/-- Wiping a fixed-size byte array in place -- the raw KEM secret, once the
epoch key has been derived from it -- returns. The source discards what it
leaves behind, so nothing about the value is assumed. -/
def ArrayZeroizeTotal : Prop :=
  ∀ (N : Usize) (inst : zeroize.Zeroize U8) (a : Array U8 N),
    ∃ r, Array.Insts.ZeroizeZeroize.zeroize (N := N) inst a = ok r

/-- Indexing a slice by the full range `..` returns the slice. The Aeneas
library models the bounded range shapes but not `RangeFull`, so the
translation declares this crate's copy of that index as an axiom; the value
is what `key[..]` means. -/
def RangeFullIndexTotal : Prop :=
  ∀ (s : Slice U8),
    core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index () s = ok s

/-- The three assumptions above, at the instances the translation actually
passes, in the shape the stepping tactic consumes. Wrapping carries the
read-back as its postcondition, so the `deref` a few lines later is a
rewrite rather than a second call to the assumption. -/
theorem zeroizing_new_spec (hz : ZeroizingArrayRoundTrip) {N : Usize} (a : Array U8 N) :
    zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize N
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a ⦃ fun z =>
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref (Array.Insts.ZeroizeZeroize N
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) z = ok a ⦄ := by
  obtain ⟨z, hz1, hz2⟩ := hz N (Array.Insts.ZeroizeZeroize N
    (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a
  rw [hz1]
  simp [hz2]

/-- Reading the wrapper back, from the fact the wrap left behind. -/
theorem zeroizing_deref_spec {N : Usize} {z : zeroize.Zeroizing (Array U8 N)} {a : Array U8 N}
    (h : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref (Array.Insts.ZeroizeZeroize N
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) z = ok a) :
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref (Array.Insts.ZeroizeZeroize N
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) z ⦃ fun r => r = a ⦄ := by
  rw [h]; simp

theorem array_zeroize_spec (hzz : ArrayZeroizeTotal) {N : Usize} (a : Array U8 N) :
    Array.Insts.ZeroizeZeroize.zeroize (N := N)
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a ⦃ fun _ => True ⦄ := by
  obtain ⟨r, hr⟩ := hzz N (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a
  rw [hr]; simp

theorem index_full_spec (hrf : RangeFullIndexTotal) {N : Usize} (a : Array U8 N) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice U8)) a ()
      ⦃ fun s => s = Array.to_slice a ⦄ := by
  have h : core.array.Array.index (core.ops.index.IndexSlice
      (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice U8)) a ()
      = ok (Array.to_slice a) := hrf (Array.to_slice a)
  rw [h]
  simp

/-- Concatenating the fixed protocol prefix, a label, and an epoch's eight
big-endian bytes cannot overflow a vector's length for any label this crate
actually passes (all four named labels are under 32 bytes), stated with
headroom rather than the exact bound so this does not need updating if a
label changes. The exact output length is carried too, not just totality:
every caller appends its own data afterwards, and needs to know how much
room that append has left before `Usize.max`. -/
theorem info_no_panic (label : Slice U8) (epoch : U64)
    (hlen : label.length + 64 ≤ Usize.max) :
    info label epoch ⦃ fun r => r.length = label.length + 33 ⦄ := by
  have hpi : (PROTOCOL_INFO : Slice U8).length = 25 := by
    simp only [global_simps, Array.length_to_slice]; scalar_tac
  have hcap : ∀ (i : Usize), (alloc.vec.Vec.with_capacity U8 i).length = 0 := by
    intro i
    simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, alloc.vec.Vec.length]
  unfold info
  step*
  all_goals (try simp_all)
  all_goals (try scalar_tac)

/-- Ratcheting the authenticator's two 32-byte keys forward from an epoch's
shared secret. The HKDF call is total by assumption, and so is the
`Zeroizing` wrapper its 64-byte output now passes through on the way to the
two key slots; everything else is fixed-size array/slice bookkeeping the
Aeneas library already has specs for. -/
theorem Auth.update_no_panic (hkdf : HkdfSha256Total) (hz : ZeroizingArrayRoundTrip)
    (self : Auth) (epoch : U64) (key : Slice U8) :
    Auth.update self epoch key ⦃ fun _ => True ⦄ := by
  have hau : (AUTH_UPDATE : Slice U8).length = 21 := by
    simp only [global_simps, Array.length_to_slice]; scalar_tac
  unfold Auth.update
  step*
  all_goals (try (step with info_no_panic AUTH_UPDATE epoch (by simp [hau]; scalar_tac)))
  all_goals (try (obtain ⟨okm, hokm⟩ := hkdf 64#usize s key v.deref (by scalar_tac); simp only [hokm]))
  all_goals (try (step with zeroizing_new_spec hz))
  all_goals (try step*)
  all_goals (try (step with zeroizing_deref_spec ‹_›))
  all_goals (try step*)

/-- Computing a header's authenticator: the length precondition gives the
append past `info`'s output room to spare, and the HMAC call is total by
assumption. -/
theorem Auth.mac_hdr_no_panic (hmac : HmacSha256Total) (self : Auth) (epoch : U64)
    (hdr : Slice U8) (hlen : hdr.length + 64 ≤ Usize.max) :
    Auth.mac_hdr self epoch hdr ⦃ fun _ => True ⦄ := by
  have heh : (EK_HEADER : Slice U8).length = 9 := by
    simp only [global_simps, Array.length_to_slice]; scalar_tac
  unfold Auth.mac_hdr
  step*
  all_goals (try (step with info_no_panic EK_HEADER epoch (by simp [heh]; scalar_tac)))
  all_goals (try step*)
  all_goals (try (obtain ⟨out, hout⟩ := hmac s data1.deref; simp only [hout]))
  all_goals (try step*)

/-- Computing a ciphertext authenticator: the same shape as `mac_hdr`, with
two appends (`ct1` then `ct2`) instead of one. -/
theorem Auth.mac_ct_no_panic (hmac : HmacSha256Total) (self : Auth) (epoch : U64)
    (ct1 ct2 : Slice U8) (hlen : ct1.length + ct2.length + 96 ≤ Usize.max) :
    Auth.mac_ct self epoch ct1 ct2 ⦃ fun _ => True ⦄ := by
  have hct : (CIPHERTEXT : Slice U8).length = 11 := by
    simp only [global_simps, Array.length_to_slice]; scalar_tac
  unfold Auth.mac_ct
  step*
  all_goals (try (step with info_no_panic CIPHERTEXT epoch (by simp [hct]; scalar_tac)))
  all_goals (try step*)
  all_goals (try (obtain ⟨out, hout⟩ := hmac s data2.deref; simp only [hout]))
  all_goals (try step*)

/-- Deriving the ML-KEM Braid's shared-channel key from an epoch's shared
secret: `info` is called on a fixed all-zero 32-byte array, so there is no
caller-supplied length to bound, and the HKDF call is total by assumption. -/
theorem kdf_ok_no_panic (hkdf : HkdfSha256Total) (shared_secret : Slice U8) (epoch : U64) :
    kdf_ok shared_secret epoch ⦃ fun _ => True ⦄ := by
  have hsk : (SCKA_KEY : Slice U8).length = 9 := by
    simp only [global_simps, Array.length_to_slice]; scalar_tac
  unfold kdf_ok
  step*
  all_goals (try (step with info_no_panic SCKA_KEY epoch (by simp [hsk]; scalar_tac)))
  all_goals (try (obtain ⟨out, hout⟩ := hkdf 32#usize s shared_secret v.deref (by scalar_tac); simp only [hout]))
  all_goals (try step*)

/-- `init` is `update` from an all-zero starting authenticator, so it inherits
`update`'s totality outright. -/
theorem Auth.init_no_panic (hkdf : HkdfSha256Total) (hz : ZeroizingArrayRoundTrip)
    (epoch : U64) (secret : Slice U8) :
    Auth.init epoch secret ⦃ fun _ => True ⦄ := by
  unfold Auth.init
  exact Auth.update_no_panic hkdf hz _ epoch secret

/-- Cloning the authenticator: two fixed 32-byte array clones, both the
identity for `u8`, both already specified in the Aeneas library. -/
theorem Auth.clone_no_panic (self : Auth) :
    Auth.Insts.CoreCloneClone.clone self ⦃ fun r => r = self ⦄ := by
  unfold Auth.Insts.CoreCloneClone.clone
  step with core.array.CloneArray.clone_spec core.clone.CloneU8 self.root_key
    (fun x _ => by simp)
  step with core.array.CloneArray.clone_spec core.clone.CloneU8 self.mac_key
    (fun x _ => by simp)
  simp only [← a_post, ← a1_post]

/-- A `Vec U8` clones as the identity: `u8`'s own clone is, and the library
models `Vec::clone` as a slice clone rather than an axiom (the same fact
`extend_from_slice`'s own spec above rests on). -/
theorem vecU8_clone_no_panic (v : alloc.vec.Vec U8) :
    alloc.vec.CloneVec.clone core.clone.CloneU8 v ⦃ fun v' => v = v' ⦄ := by
  unfold alloc.vec.CloneVec.clone
  have h : ∀ x ∈ v.val, (core.clone.CloneU8.clone) x = ok x := by
    intro x _
    rfl
  exact Slice.clone_spec h

/-! ## The eleven-state machine's own bookkeeping

Every function below either matches on the state without touching what is
inside its variants, or clones it whole. Nothing here loops and nothing here
computes; the only way any of it fails is through the clones, whose totality
already stands above and below. -/

theorem State.epoch_no_panic (self : State) : State.epoch self ⦃ fun _ => True ⦄ := by
  unfold State.epoch
  rcases self with _|_|_|_|_|_|_|_|_|_|_|_ <;> simp

/-- An invariant `step_send` maintains but this file does not prove (that
would be a T3-shaped claim about the whole state machine, not a T1 one about
a single function): the `ct1` field held across the encapsulation exchange is
the KEM ciphertext `encapsulate1` produced, concrete-capped the same way
`Encapsulate1Total` caps it fresh. Received exactly as sent, it carries the
same bound forward through every state that still holds it. -/
def State.ct1_bounded : State → Prop
  | .Ct1Received _ _ _ ct1 _ => ct1.length ≤ 4096
  | .EkSentCt1Received _ _ _ ct1 _ => ct1.length ≤ 4096
  | .Ct1Sampled _ _ _ _ ct1 _ _ => ct1.length ≤ 4096
  | .EkReceivedCt1Sampled _ _ _ ct1 _ _ => ct1.length ≤ 4096
  | .Ct1Acknowledged _ _ _ _ ct1 _ => ct1.length ≤ 4096
  | _ => True

/-- The epoch every state constructor carries, as a plain value rather than
wrapped in `Result` the way `State.epoch` is -- needed to state a bound on it
directly, since `EkSentCt1Received` and `Ct2Sampled` each advance it by one on
a real message. -/
def State.epoch_val : State → U64
  | .KeysUnsampled epoch _ => epoch
  | .KeysSampled epoch _ _ _ => epoch
  | .HeaderSent epoch _ _ _ _ => epoch
  | .Ct1Received epoch _ _ _ _ => epoch
  | .EkSentCt1Received epoch _ _ _ _ => epoch
  | .NoHeaderReceived epoch _ _ => epoch
  | .HeaderReceived epoch _ _ _ => epoch
  | .Ct1Sampled epoch _ _ _ _ _ _ => epoch
  | .EkReceivedCt1Sampled epoch _ _ _ _ _ => epoch
  | .Ct1Acknowledged epoch _ _ _ _ _ => epoch
  | .Ct2Sampled epoch _ _ => epoch
  | .Failed => 0#u64

/-- Cloning a state: an eleven-way match, one clone call per field, each
already total -- the encoder, decoder, key-pair and encapsulation-state
clones by assumption, everything else by the lemmas just above. -/
theorem State.clone_no_panic (henc : EncoderCloneTotal) (hdec : DecoderCloneTotal)
    (hkp : KeyPairCloneTotal) (hes : EncapsStateCloneTotal) (self : State) :
    -- Strengthened past bare totality: `receive` clones the state before
    -- stepping it, and needs to know the clone carries forward the two facts
    -- `step_receive` depends on, even though the opaque Encoder/Decoder/
    -- KeyPair/EncapsState clones are not known to be the identity.
    State.Insts.CoreCloneClone.clone self
      ⦃ fun r => State.epoch_val r = State.epoch_val self ∧
                 (State.ct1_bounded self → State.ct1_bounded r) ⦄ := by
  unfold State.Insts.CoreCloneClone.clone
  rcases self with _|_|_|_|_|_|_|_|_|_|_|_ <;>
    first
    | (simp [State.epoch_val, State.ct1_bounded]; done)
    | (all_goals (try simp only [lift])
       all_goals (try step*)
       all_goals (try (obtain ⟨r, hr⟩ := henc ‹_›; simp only [hr]))
       all_goals (try (obtain ⟨r, hr⟩ := hdec ‹_›; simp only [hr]))
       all_goals (try (obtain ⟨r, hr⟩ := hkp ‹_›; simp only [hr]))
       all_goals (try (obtain ⟨r, hr⟩ := hes ‹_›; simp only [hr]))
       all_goals (try (step with Auth.clone_no_panic))
       all_goals (try (step with vecU8_clone_no_panic))
       all_goals (try step*)
       all_goals (try (step with vecU8_clone_no_panic))
       all_goals (try (simp_all [State.epoch_val, State.ct1_bounded])))

theorem Braid.clone_no_panic (henc : EncoderCloneTotal) (hdec : DecoderCloneTotal)
    (hkp : KeyPairCloneTotal) (hes : EncapsStateCloneTotal) (self : Braid) :
    Braid.Insts.CoreCloneClone.clone self ⦃ fun _ => True ⦄ := by
  unfold Braid.Insts.CoreCloneClone.clone
  step with State.clone_no_panic henc hdec hkp hes

theorem hdr_decoder_no_panic (hdec : DecoderNewTotal) (hhl : HeaderLenTotal) :
    hdr_decoder ⦃ fun _ => True ⦄ := by
  unfold hdr_decoder
  obtain ⟨v, hv, hvbound⟩ := hhl
  simp only [hv]
  step*
  all_goals (try (simp only [global_simps]; scalar_tac))
  all_goals (try (obtain ⟨r, hr⟩ := hdec i1; simp only [hr]))
  all_goals (try simp)

theorem Braid.initiator_no_panic (hkdf : HkdfSha256Total) (hz : ZeroizingArrayRoundTrip)
    (secret : Slice U8) :
    Braid.initiator secret ⦃ fun _ => True ⦄ := by
  unfold Braid.initiator
  step with Auth.init_no_panic hkdf hz 1#u64 secret

theorem Braid.responder_no_panic (hkdf : HkdfSha256Total) (hz : ZeroizingArrayRoundTrip)
    (hdec : DecoderNewTotal) (hhl : HeaderLenTotal) (secret : Slice U8) :
    Braid.responder secret ⦃ fun _ => True ⦄ := by
  unfold Braid.responder
  step with Auth.init_no_panic hkdf hz 1#u64 secret
  step with hdr_decoder_no_panic hdec hhl

theorem Braid.epoch_no_panic (self : Braid) : Braid.epoch self ⦃ fun _ => True ⦄ := by
  unfold Braid.epoch; exact State.epoch_no_panic self.state

theorem Braid.failed_no_panic (self : Braid) : Braid.failed self ⦃ fun _ => True ⦄ := by
  unfold Braid.failed
  rcases self.state with _|_|_|_|_|_|_|_|_|_|_|_ <;> simp

theorem Braid.state_tag_no_panic (self : Braid) : Braid.state_tag self ⦃ fun _ => True ⦄ := by
  unfold Braid.state_tag
  rcases self.state with _|_|_|_|_|_|_|_|_|_|_|_ <;> simp

theorem Braid.reported_no_panic (self : Braid) : Braid.reported self ⦃ fun _ => True ⦄ := by
  unfold Braid.reported
  step with State.epoch_no_panic self.state

theorem state_back_no_panic (state : State) : state_back state ⦃ fun _ => True ⦄ := by
  unfold state_back; simp

theorem Braid.commit_no_panic (self next : Braid) : Braid.commit self next ⦃ fun _ => True ⦄ := by
  unfold Braid.commit; simp

/-- An empty message (no chunk, `MsgType.None`) is always constructible. -/
theorem Msg.empty_no_panic (epoch : U64) : Msg.empty epoch ⦃ fun _ => True ⦄ := by
  unfold Msg.empty; simp

/-- Wrapping a chunk into a message, or falling back to empty when there is
none: both arms are a bare `ok`. -/
theorem Msg.with_no_panic (epoch : U64) (ty : MsgType) (chunk : Option tacenta_erasure.Chunk) :
    Msg.with epoch ty chunk ⦃ fun _ => True ⦄ := by
  unfold Msg.with
  rcases chunk with _|_ <;> simp [Msg.empty]

/-- The sending half of the eleven-state machine. Six of the eleven branches
share one shape (advance an encoder, wrap its next chunk in a message); three
more share another (leave the state alone, send an empty message); `Failed`
is the same shape as those three with no state to leave alone; and two
(`KeysUnsampled`, `HeaderReceived`) sample fresh key material and branch on
whether the KEM call succeeded, the only real branching this function does. -/
theorem Braid.step_send_no_panic {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (hrng : RngTotal rc) (hgen : KeyPairGenerateTotal)
    (hhdr : KeyPairHeaderTotal) (hmac : HmacSha256Total) (henew : EncoderNewTotal)
    (henext : EncoderNextChunkTotal) (hkdf : HkdfSha256Total)
    (hencaps1 : Encapsulate1Total) (hz : ZeroizingArrayRoundTrip) (hzz : ArrayZeroizeTotal)
    (hrf : RangeFullIndexTotal) (self : Braid) (state : State) (rng : R) :
    Braid.step_send rc crc self state rng ⦃ fun _ => True ⦄ := by
  unfold Braid.step_send
  rcases state with
    ⟨epoch, auth⟩ | ⟨epoch, auth, kp, hdr_enc⟩ | ⟨epoch, auth, kp, ct1_dec, ek_enc⟩
    | ⟨epoch, auth, kp, ct1, ek_enc⟩ | ⟨epoch, auth, kp, ct1, ct2_dec⟩
    | ⟨epoch, auth, hdr_dec⟩ | ⟨epoch, auth, header, ek_dec⟩
    | ⟨epoch, auth, header, encaps, ct1, ct1_enc, ek_dec⟩
    | ⟨epoch, auth, encaps, ct1, ek_vector, ct1_enc⟩
    | ⟨epoch, auth, header, encaps, ct1, ek_dec⟩ | ⟨epoch, auth, ct2_enc⟩ | -
  · -- KeysUnsampled: sample a key pair, MAC its header, start an encoder.
    obtain ⟨⟨rval, rng1⟩, hr⟩ := hgen rc crc rng hrng
    simp only [hr]
    rcases rval with kp | e
    all_goals (try step*)
    all_goals (try (obtain ⟨header, hheader, hhlen⟩ := hhdr kp; simp only [hheader]))
    all_goals (try step*)
    all_goals (try (step with Auth.mac_hdr_no_panic hmac auth epoch header.deref (by simp only [alloc.vec.Vec.deref, Slice.length]; scalar_tac)))
    all_goals (try step*)
    all_goals (try (obtain ⟨henc_r, hhenc⟩ := henew header1.deref; simp only [hhenc]))
    all_goals (try step*)
    all_goals (try (obtain ⟨⟨chunk, hdr_enc1⟩, hchunk⟩ := henext henc_r; simp only [hchunk]))
    all_goals (try step*)
    all_goals (try (step with Msg.with_no_panic))
    all_goals (try (step with Msg.empty_no_panic))
  · -- KeysSampled
    step*
    all_goals (try (obtain ⟨⟨chunk, enc1⟩, hr⟩ := henext ‹_›; simp only [hr]))
    all_goals (try step*)
    all_goals (try (step with Msg.with_no_panic))
  · -- HeaderSent
    step*
    all_goals (try (obtain ⟨⟨chunk, enc1⟩, hr⟩ := henext ‹_›; simp only [hr]))
    all_goals (try step*)
    all_goals (try (step with Msg.with_no_panic))
  · -- Ct1Received
    step*
    all_goals (try (obtain ⟨⟨chunk, enc1⟩, hr⟩ := henext ‹_›; simp only [hr]))
    all_goals (try step*)
    all_goals (try (step with Msg.with_no_panic))
  · -- EkSentCt1Received: leaves the state alone.
    step*
    all_goals (try (step with state_back_no_panic))
    all_goals (try (step with Msg.empty_no_panic))
  · -- NoHeaderReceived: leaves the state alone.
    step*
    all_goals (try (step with state_back_no_panic))
    all_goals (try (step with Msg.empty_no_panic))
  · -- HeaderReceived: sample an encapsulation, derive the shared key.
    obtain ⟨⟨rval, rng1⟩, hr, hrbound⟩ := hencaps1 rc crc header.deref rng hrng
    simp only [hr]
    rcases rval with ⟨encaps, ct1, raw1⟩ | e
    all_goals (try step*)
    all_goals (try (step with kdf_ok_no_panic hkdf))
    all_goals (try (step with zeroizing_new_spec hz))
    all_goals (try (step with array_zeroize_spec hzz))
    all_goals (try (step with zeroizing_deref_spec ‹_›))
    all_goals (try (step with index_full_spec hrf))
    all_goals (try (step with Auth.update_no_panic hkdf hz))
    all_goals (try (obtain ⟨henc_r, hhenc⟩ := henew ct1.deref; simp only [hhenc]))
    all_goals (try step*)
    all_goals (try (obtain ⟨⟨chunk, ct1_enc1⟩, hchunk⟩ := henext henc_r; simp only [hchunk]))
    all_goals (try step*)
    all_goals (try (step with Msg.with_no_panic))
    all_goals (try (step with Msg.empty_no_panic))
  · -- Ct1Sampled
    step*
    all_goals (try (obtain ⟨⟨chunk, enc1⟩, hr⟩ := henext ‹_›; simp only [hr]))
    all_goals (try step*)
    all_goals (try (step with Msg.with_no_panic))
  · -- EkReceivedCt1Sampled
    step*
    all_goals (try (obtain ⟨⟨chunk, enc1⟩, hr⟩ := henext ‹_›; simp only [hr]))
    all_goals (try step*)
    all_goals (try (step with Msg.with_no_panic))
  · -- Ct1Acknowledged: leaves the state alone.
    step*
    all_goals (try (step with state_back_no_panic))
    all_goals (try (step with Msg.empty_no_panic))
  · -- Ct2Sampled
    step*
    all_goals (try (obtain ⟨⟨chunk, enc1⟩, hr⟩ := henext ‹_›; simp only [hr]))
    all_goals (try step*)
    all_goals (try (step with Msg.with_no_panic))
  · -- Failed
    step with Msg.empty_no_panic

/-- `send`: clone the current state, step it, and read back the reportable
epoch. All three are already total. -/
theorem Braid.send_no_panic {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (hrng : RngTotal rc)
    (henc : EncoderCloneTotal) (hdec : DecoderCloneTotal)
    (hkp : KeyPairCloneTotal) (hes : EncapsStateCloneTotal) (hgen : KeyPairGenerateTotal)
    (hhdr : KeyPairHeaderTotal) (hmac : HmacSha256Total) (henew : EncoderNewTotal)
    (henext : EncoderNextChunkTotal) (hkdf : HkdfSha256Total) (hencaps1 : Encapsulate1Total)
    (hz : ZeroizingArrayRoundTrip) (hzz : ArrayZeroizeTotal) (hrf : RangeFullIndexTotal)
    (self : Braid) (rng : R) :
    Braid.send rc crc self rng ⦃ fun _ => True ⦄ := by
  unfold Braid.send
  step with State.clone_no_panic henc hdec hkp hes
  all_goals (try (step with Braid.step_send_no_panic rc crc hrng hgen hhdr hmac henew henext hkdf hencaps1 hz hzz hrf))
  all_goals (try (step with Braid.reported_no_panic))

/-- Finishing an encapsulation: sample the second ciphertext, MAC it together
with the first (both concrete-capped, so the sum stays in bounds), append the
MAC, and start an encoder over the result. -/
theorem finish_encaps_no_panic (hencaps2 : Encapsulate2Total) (hmac : HmacSha256Total)
    (henew : EncoderNewTotal) (epoch : U64) (auth : Auth) (encaps : tacenta_kem.EncapsState)
    (ct1 ek_vector : Slice U8) (hct1 : ct1.length ≤ 4096) :
    finish_encaps epoch auth encaps ct1 ek_vector ⦃ fun _ => True ⦄ := by
  unfold finish_encaps
  obtain ⟨r, hr, hrbound⟩ := hencaps2 encaps ek_vector
  simp only [hr]
  rcases r with c | e
  all_goals (try step*)
  all_goals (try (have hclen := hrbound c rfl))
  all_goals (try (step with Auth.mac_ct_no_panic hmac auth epoch ct1 c.deref (by simp only [alloc.vec.Vec.deref, Slice.length]; scalar_tac)))
  all_goals (try step*)
  all_goals (try (obtain ⟨henc_r, hhenc⟩ := henew c1.deref; simp only [hhenc]))
  all_goals (try step*)

/-- The receiving half of the eleven-state machine, and the one an attacker's
header, chunk data and claimed lengths drive directly. Three branches
(`KeysUnsampled`, `HeaderReceived`, `Failed`) are inert. The rest advance a
decoder by one chunk and, once a full message has arrived, check a claimed
length, MAC, or validation result before ever trusting the bytes -- each of
those checks is what turns an attacker-chosen framing into `Failed` rather
than a panic. -/
theorem Braid.step_receive_no_panic (hdnew : DecoderNewTotal) (hdadd : DecoderAddChunkTotal)
    (hdmsg : DecoderMessageTotal) (hct1len : Ct1LenTotal) (hct2len : Ct2LenTotal)
    (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal) (hekvec : KeyPairEkVectorTotal)
    (henew : EncoderNewTotal) (hdecap : KeyPairDecapsulateTotal) (hkdf : HkdfSha256Total)
    (hmac : HmacSha256Total) (hvalek : ValidateEkTotal) (hencaps2 : Encapsulate2Total)
    (hz : ZeroizingArrayRoundTrip) (hzz : ArrayZeroizeTotal) (hrf : RangeFullIndexTotal)
    (self : Braid) (state : State) (msg : Msg) (hct1b : State.ct1_bounded state) :
    Braid.step_receive self state msg ⦃ fun _ => True ⦄ := by
  unfold Braid.step_receive
  rcases state with
    ⟨epoch1, auth⟩ | ⟨epoch1, auth, kp, hdr_enc⟩ | ⟨epoch1, auth, kp, ct1_dec, ek_enc⟩
    | ⟨epoch1, auth, kp, ct1, ek_enc⟩ | ⟨epoch1, auth, kp, ct1, ct2_dec⟩
    | ⟨epoch1, auth, hdr_dec⟩ | ⟨epoch1, auth, header, ek_dec⟩
    | ⟨epoch1, auth, header, encaps, ct1, ct1_enc, ek_dec⟩
    | ⟨epoch1, auth, encaps, ct1, ek_vector, ct1_enc⟩
    | ⟨epoch1, auth, header, encaps, ct1, ek_dec⟩ | ⟨epoch1, auth, ct2_enc⟩ | -
  case KeysUnsampled =>
    simp [State.epoch]
  case KeysSampled =>
    simp only [State.epoch, MsgType.Insts.CoreCmpPartialEqMsgType.eq]
    step*
    all_goals (try (obtain ⟨v, hv, hvb⟩ := hct1len; simp only [hv]))
    all_goals (try step*)
    all_goals (try (obtain ⟨r, hr⟩ := hdnew v; simp only [hr]))
    all_goals (try step*)
    all_goals (try (obtain ⟨⟨b, ct1_dec1⟩, hr⟩ := hdadd r ‹_›; simp only [hr]))
    all_goals (try step*)
    all_goals (try (obtain ⟨v2, hv2, hv2b⟩ := hekvec kp; simp only [hv2]))
    all_goals (try step*)
    all_goals (try (obtain ⟨enc, henc⟩ := henew v2.deref; simp only [henc]))
    all_goals (try step*)
  case HeaderSent =>
    simp only [State.epoch, MsgType.Insts.CoreCmpPartialEqMsgType.eq]
    step*
    all_goals (try (obtain ⟨⟨b, ct1_dec1⟩, hr⟩ := hdadd ct1_dec ‹_›; simp only [hr]))
    all_goals (try step*)
    all_goals (try (obtain ⟨o, ho⟩ := hdmsg ct1_dec1; simp only [ho]))
    all_goals (try step*)
  case Ct1Received =>
    simp only [State.epoch, MsgType.Insts.CoreCmpPartialEqMsgType.eq]
    step*
    all_goals (try (obtain ⟨v, hv, hvb⟩ := hct2len; simp only [hv]))
    all_goals (try step*)
    all_goals (try (simp only [global_simps]; scalar_tac))
    all_goals (try (obtain ⟨r, hr⟩ := hdnew ‹_›; simp only [hr]))
    all_goals (try step*)
    all_goals (try (obtain ⟨⟨b, ct2_dec1⟩, hr⟩ := hdadd r ‹_›; simp only [hr]))
    all_goals (try step*)
  case EkSentCt1Received =>
    simp only [State.ct1_bounded] at hct1b
    simp only [State.epoch, MsgType.Insts.CoreCmpPartialEqMsgType.eq]
    step*
    all_goals (try (obtain ⟨⟨b, ct2_dec1⟩, hr⟩ := hdadd ct2_dec ‹_›; simp only [hr]))
    all_goals (try step*)
    all_goals (try (obtain ⟨o, ho⟩ := hdmsg ct2_dec1; simp only [ho]))
    all_goals (try step*)
    all_goals (try (obtain ⟨v, hv, hvb⟩ := hct2len; simp only [hv]))
    all_goals (try step*)
    all_goals (try (simp only [global_simps]; scalar_tac))
    all_goals (try (simp only [alloc.vec.Vec.deref, Slice.length]; scalar_tac))
    all_goals (try (obtain ⟨r2, hr2⟩ := hdecap kp ct1.deref ct2; simp only [hr2]))
    all_goals (try step*)
    all_goals (try (rcases r2 with ss | e))
    all_goals (try step*)
    all_goals (try (step with kdf_ok_no_panic hkdf))
    all_goals (try (step with zeroizing_new_spec hz))
    all_goals (try (step with array_zeroize_spec hzz))
    all_goals (try (step with zeroizing_deref_spec ‹_›))
    all_goals (try (step with index_full_spec hrf))
    all_goals (try (step with Auth.update_no_panic hkdf hz))
    all_goals (try (step with Auth.mac_ct_no_panic hmac auth1 epoch1 ct1.deref ct2 (by simp only [alloc.vec.Vec.deref, Slice.length]; scalar_tac)))
    all_goals (try step*)
    all_goals (try (step with hdr_decoder_no_panic hdnew hhdrlen))
  case NoHeaderReceived =>
    simp only [State.epoch, MsgType.Insts.CoreCmpPartialEqMsgType.eq]
    step*
    all_goals (try (obtain ⟨⟨b, hdr_dec1⟩, hr⟩ := hdadd hdr_dec ‹_›; simp only [hr]))
    all_goals (try step*)
    all_goals (try (obtain ⟨o, ho⟩ := hdmsg hdr_dec1; simp only [ho]))
    all_goals (try step*)
    all_goals (try (obtain ⟨v, hv, hvb⟩ := hhdrlen; simp only [hv]))
    all_goals (try step*)
    all_goals (try (simp only [global_simps]; scalar_tac))
    all_goals (try (simp only [alloc.vec.Vec.deref, Slice.length]; scalar_tac))
    all_goals (try (step with Auth.mac_hdr_no_panic hmac auth epoch1 header (by scalar_tac)))
    all_goals (try step*)
    all_goals (try (obtain ⟨v2, hv2, hv2b⟩ := hekveclen; simp only [hv2]))
    all_goals (try step*)
    all_goals (try (obtain ⟨r, hr⟩ := hdnew v2; simp only [hr]))
    all_goals (try step*)
  case HeaderReceived =>
    simp [State.epoch]
  case Ct1Sampled =>
    simp only [State.ct1_bounded] at hct1b
    simp only [State.epoch, MsgType.Insts.CoreCmpPartialEqMsgType.eq]
    step*
    split_ifs
    all_goals (try step*)
    all_goals (try (obtain ⟨⟨b, ek_dec1⟩, hr⟩ := hdadd ek_dec ‹_›; simp only [hr]))
    all_goals (try step*)
    all_goals (try (obtain ⟨o, ho⟩ := hdmsg ek_dec1; simp only [ho]))
    all_goals (try step*)
    all_goals (try (obtain ⟨b2, hb2⟩ := hvalek header.deref ek_vector.deref; simp only [hb2]))
    all_goals (try step*)
    all_goals (try (step with finish_encaps_no_panic hencaps2 hmac henew epoch1 auth encaps ct1.deref ek_vector.deref (by simp only [alloc.vec.Vec.deref, Slice.length]; scalar_tac)))
  case EkReceivedCt1Sampled =>
    simp only [State.ct1_bounded] at hct1b
    simp only [State.epoch, MsgType.Insts.CoreCmpPartialEqMsgType.eq]
    step*
    all_goals (try (step with finish_encaps_no_panic hencaps2 hmac henew epoch1 auth encaps ct1.deref ek_vector.deref (by simp only [alloc.vec.Vec.deref, Slice.length]; scalar_tac)))
  case Ct1Acknowledged =>
    simp only [State.ct1_bounded] at hct1b
    simp only [State.epoch, MsgType.Insts.CoreCmpPartialEqMsgType.eq]
    step*
    all_goals (try (obtain ⟨⟨b, ek_dec1⟩, hr⟩ := hdadd ek_dec ‹_›; simp only [hr]))
    all_goals (try step*)
    all_goals (try (obtain ⟨o, ho⟩ := hdmsg ek_dec1; simp only [ho]))
    all_goals (try step*)
    all_goals (try (obtain ⟨b1, hb1⟩ := hvalek header.deref ek_vector.deref; simp only [hb1]))
    all_goals (try step*)
    all_goals (try (step with finish_encaps_no_panic hencaps2 hmac henew epoch1 auth encaps ct1.deref ek_vector.deref (by simp only [alloc.vec.Vec.deref, Slice.length]; scalar_tac)))
  case Ct2Sampled =>
    simp only [State.epoch]
    step*
  case Failed =>
    simp [State.epoch]

/-- Cloning an `Output`: a `U64` and a fixed 32-byte array, both already
specified in the Aeneas library the same way `Auth`'s clone is. -/
theorem Output.clone_no_panic (self : Output) :
    Output.Insts.CoreCloneClone.clone self ⦃ fun r => r = self ⦄ := by
  unfold Output.Insts.CoreCloneClone.clone
  simp only [lift]
  step with core.array.CloneArray.clone_spec core.clone.CloneU8 self.key
    (fun x _ => by simp)
  simp [← i_post]

/-- `receive`: clone the state (carrying the two facts `step_receive` needs
forward, per `State.clone_no_panic`'s strengthened conclusion), step it, and
clone the reported `Output` back out if there is one. -/
theorem Braid.receive_no_panic (hdnew : DecoderNewTotal) (hdadd : DecoderAddChunkTotal)
    (hdmsg : DecoderMessageTotal) (hct1len : Ct1LenTotal) (hct2len : Ct2LenTotal)
    (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal) (hekvec : KeyPairEkVectorTotal)
    (henew : EncoderNewTotal) (hdecap : KeyPairDecapsulateTotal) (hkdf : HkdfSha256Total)
    (hmac : HmacSha256Total) (hvalek : ValidateEkTotal) (hencaps2 : Encapsulate2Total)
    (henc : EncoderCloneTotal) (hdec : DecoderCloneTotal) (hkp : KeyPairCloneTotal)
    (hes : EncapsStateCloneTotal) (hopt : OptionCloneTotal)
    (hz : ZeroizingArrayRoundTrip) (hzz : ArrayZeroizeTotal) (hrf : RangeFullIndexTotal)
    (self : Braid) (msg : Msg) (hct1b : State.ct1_bounded self.state) :
    Braid.receive self msg ⦃ fun _ => True ⦄ := by
  unfold Braid.receive
  step with State.clone_no_panic henc hdec hkp hes
  all_goals (try (step with Braid.step_receive_no_panic hdnew hdadd hdmsg hct1len hct2len hhdrlen hekveclen hekvec henew hdecap hkdf hmac hvalek hencaps2 hz hzz hrf self ‹_› msg (by simp_all)))
  all_goals (try step*)
  all_goals (try (step with Braid.reported_no_panic))
  all_goals (try (step with hopt Output.Insts.CoreCloneClone (some o) (fun x _ => Output.clone_no_panic x)))

/-! ## What this covers, and what it does not

**Proved:** the crate's one loop (`mac_eq`), every helper the state machine
calls (`info`, `Auth.update`/`mac_hdr`/`mac_ct`/`init`,
`kdf_ok`, `finish_encaps`), the state machine's own bookkeeping (`State`'s and
`Braid`'s clone, `epoch`, `failed`, `state_tag`, `reported`, `state_back`,
`hdr_decoder`, `initiator`, `responder`), and now the two functions that were
this file's actual point: `step_send` and `step_receive`, the eleven-state
machine's send and receive halves, and their entry points `send`, `receive`,
and `commit`. `step_receive` is the one an attacker's header, chunk data, and
claimed lengths drive directly, so this is what stands between a malformed
message and a remote denial of service, for this leaf crate.

One real precondition travels with `step_receive` and `receive`, not a
formality: `State.ct1_bounded`, a size cap on the KEM ciphertext carried
across the encapsulation exchange that `step_send` maintains but this file
does not prove (that would be a T3 claim about the whole state machine, not a
T1 one about a single function). The epoch bound this file used to carry as
well (`State.epoch_val _ < U64.max`, the same shape of counter bound the
classical ratchet and the sparse ratchet each need) is gone: the two
transitions that advance the epoch (5 and 13) now use `checked_add`, and at
the ceiling they answer `Failed` instead of overflowing, an outcome this file
proves as a value rather than assumes away.

## Twenty-six assumptions, not one or four

Every opaque operation this crate calls out to -- the erasure coder, the KEM,
the two KDF calls, `Option::clone`, and the `zeroize` crate's wrapper, wipe
and full-range index -- gets its own totality assumption, per this project's
established counting rule: one axiom per crate that touches an unmodelled
operation, not one per name. That comes to twenty-six named constants in
this file. Several carry a concrete size cap (`≤ 4096`) rather than mere
headroom below `Usize.max`, because more than one capped value gets summed at
a single call site (`finish_encaps` sums a ciphertext against another opaque
bound before appending a MAC), and two facts each individually "under
`Usize.max`" do not compose the way two concrete small caps do -- the same
lesson `SessionT1.lean`'s appends and `SpqrT1.lean`'s counting trap describe
from their own crates.

The three `zeroize` assumptions are new with the epoch key's `Zeroizing`
wrapper: `Auth.update` now passes its 64-byte HKDF output through the wrapper
on the way to the two key slots, and transitions 5 and 7 wrap the 32-byte
epoch key the same way, wipe the raw KEM secret in place once the key is
derived, and read the key back through `key[..]`, a `RangeFull` index the
Aeneas library does not model. Each is a distinct constant from the ratchet's
and the session's copies. The crate's `zeroize_or_on_drop` axiom is still not
needed by anything proved here: no explicit `drop` call appears in
`step_send`, `step_receive`, or anything they call. -/

-- The axiom audit for the two entry points, enforced rather than asserted: the
-- kernel's three axioms and the crate's opaque boundary (erasure coder, KEM, KDF,
-- `zeroize`, and the library types and operations Aeneas does not model), and
-- nothing else. No `native_decide` reaches either. A proof that starts
-- trusting something new fails here.

/--
info: 'Tacenta.BraidT1.Braid.send_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_erasure.Encoder.new,
 tacenta_erasure.Encoder.next_chunk,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_erasure.Decoder.Insts.CoreCloneClone.clone,
 tacenta_erasure.Encoder.Insts.CoreCloneClone.clone,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.BraidT1.Braid.send_no_panic

/--
info: 'Tacenta.BraidT1.Braid.receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_erasure.Decoder,
 tacenta_erasure.Encoder,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 tacenta_erasure.Decoder.add_chunk,
 tacenta_erasure.Decoder.message,
 tacenta_erasure.Decoder.new,
 tacenta_erasure.Encoder.new,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_erasure.Decoder.Insts.CoreCloneClone.clone,
 tacenta_erasure.Encoder.Insts.CoreCloneClone.clone,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.BraidT1.Braid.receive_no_panic

end Tacenta.BraidT1
