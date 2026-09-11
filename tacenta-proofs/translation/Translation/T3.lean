import Translation.TacentaRatchet
import Model.Ratchet
import Translation.T1

/-!
# T3: refinement of the verified zone against the model

T1 says the translated ratchet cannot fail. T2 says the model has the properties
the specification asks for. Neither says the two compute the same thing, and
that is what this file is for: a relation between the translated state and the
model's state, and theorems saying each operation carries one to the other.

The two sides are deliberately different shapes. The translation carries what
Rust carries, which is fixed-width arrays, `u32` counters and a `Vec` of
records; the model carries what is convenient to reason about, which is byte
lists, `Nat` counters and a list of triples. The relation is where that
difference is absorbed, so it has to be stated once and stated honestly.

## What this tier does not close

The key-derivation primitives are opaque to the translation, by the same
deliberate choice that made T1 tractable. A refinement proof needs them to
*agree* with the model's derivations, and an axiom cannot be shown to agree with
anything. So agreement is a stated hypothesis (`HmacAgrees`, `HkdfAgrees`), and
what this file proves is refinement **modulo that agreement** rather than
refinement outright. Discharging it means translating the key-derivation crate
and proving its SHA-256 equal to `Model.Sha256`, which is separate work and is
not attempted here.

That is a real limit rather than a formality. If the Rust HMAC and the model's
HMAC disagreed, every theorem below would still hold and the implementation
would still be wrong. What keeps it honest is that the two are also checked
against each other by the model-generated vectors, which are bytes, outside
Lean.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.T3

open tacenta_ratchet

-- The `zeroize` model at the derived-keys vector is T1's; only the name is
-- brought in, so every other T1 assumption stays spelled out where it is used.
open Tacenta.T1 (DerivedKeysModel)

/-! ## Carrying bytes across

Aeneas's `U8` is a bounded scalar and the model's byte is Lean's `UInt8`. Every
comparison below goes through this one conversion. -/

/-- One translated byte as a model byte. -/
def u8 (b : Std.U8) : UInt8 := UInt8.ofNat b.val

/-- A translated byte array as a model key. -/
def keyOf {n : Usize} (a : Array Std.U8 n) : Model.State.Key := a.val.map u8

/-- A translated slice as a model byte string. -/
def sliceOf (s : Slice Std.U8) : List UInt8 := s.val.map u8

/-! ## Array equality, with its value

T1 registered a rule saying the comparison returns, which is all panic-freedom
needed. Refinement needs to know *what* it returned: a branch that only knows
some opaque `Bool` was true cannot decide anything about the states. This is the
same gap the key-derivation primitives had, in a place that is not a trusted
boundary at all, so it is closed by proof rather than by assumption. -/

private theorem allM_pure_val {α : Type} (g : α → Bool) (l : List α) :
    List.allM (fun x => (ok (g x) : Result Bool)) l = ok (l.all g) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    by_cases hg : g hd
    · simp only [List.allM, hg, List.all_cons, Bool.true_and]
      simpa using ih
    · have hg' : g hd = false := by simpa using hg
      simp only [List.allM, hg', List.all_cons, Bool.false_and]
      rfl

private theorem zip_all_eq {α : Type} [DecidableEq α] (l1 l2 : List α)
    (hlen : l1.length = l2.length) :
    ((l1.zip l2).all fun p => decide (p.1 = p.2)) = true ↔ l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons a t ih =>
    cases l2 with
    | nil => simp at hlen
    | cons b u =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq, List.cons.injEq]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [ih u hlen]

-- T1's rule for this says only that the comparison returned, which is what
-- panic-freedom needed and is useless here, so it comes out of the stepping set.
attribute [-step] Tacenta.T1.array_eq_total

@[step]
theorem array_eq_val {N : Usize} (a b : Array Std.U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b ⦃ fun r =>
      r = true ↔ a = b ⦄ := by
  have hlen : a.val.length = b.val.length := by rw [a.property, b.property]
  have hf : (fun (x : Std.U8 × Std.U8) => do
        let bb ← liftFun2 core.cmp.impls.PartialEqU8.ne x.1 x.2
        (ok (decide ¬bb = true) : Result Bool))
      = fun x => ok (decide (x.1 = x.2)) := by
    funext x
    simp [liftFun2, core.cmp.impls.PartialEqU8.ne]
    exact ⟨fun h => by scalar_tac, fun h => by rw [h]⟩
  simp only [core.array.equality.PartialEqArray.eq, if_pos hlen, hf,
    allM_pure_val]
  simp only [Std.WP.spec_ok]
  rw [zip_all_eq _ _ hlen]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩

-- The inequality test is the equality test negated, and T1's rule for it says
-- only that it returned. Same story, same fix.
attribute [-step] Tacenta.T1.array_ne_total

@[step]
theorem array_ne_val {N : Usize} (a b : Array Std.U8 N) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b ⦃ fun r =>
      r = true ↔ a ≠ b ⦄ := by
  obtain ⟨v, hv⟩ := (Tacenta.T1.noPanic_iff _).mp (Tacenta.T1.array_eq_total a b)
  have hval := array_eq_val a b
  rw [hv] at hval
  have hv2 : (v = true ↔ a = b) := hval
  unfold core.array.equality.PartialEqArray.ne
  rw [hv]
  step*

/-! ## The byte conversion is faithful

A refinement relation that identified two different states would prove nothing,
so the conversion has to be injective, and the place it bites is the negative
branch of a comparison: knowing two arrays differ has to give that their model
keys differ, and only injectivity does that. -/

theorem u8_inj {x y : Std.U8} (h : u8 x = u8 y) : x = y := by
  simp only [u8] at h
  have hx : x.val < 256 := by scalar_tac
  have hy : y.val < 256 := by scalar_tac
  have := congrArg UInt8.toNat h
  simp at this
  scalar_tac

theorem keyOf_inj {n : Usize} {a b : Array Std.U8 n} (h : keyOf a = keyOf b) :
    a = b := by
  have : a.val = b.val := by
    simp only [keyOf] at h
    exact List.map_injective_iff.mpr (fun _ _ => u8_inj) h
  cases a; cases b; simp_all

/-- The form the branch tests need: model keys agree exactly when the arrays
do. -/
@[simp]
theorem keyOf_eq_iff {n : Usize} (a b : Array Std.U8 n) :
    keyOf a = keyOf b ↔ a = b :=
  ⟨keyOf_inj, fun h => by rw [h]⟩

/-- The translated label set as the model's. -/
def labelsOf : LabelSet → Model.State.LabelSet
  | .Tacenta => .tacenta

/-! ## The derivation labels agree

The model chose its own `info` labels and the Rust holds its own copy of the
same bytes. Nothing but this check ties the two together, and if either drifted
the refinement would be false rather than merely unproven, so it is checked
here rather than assumed. -/

theorem rk_info_agrees (l : LabelSet) :
    sliceOf RK_INFO = (labelsOf l).rkInfo := by
  cases l
  simp [sliceOf, RK_INFO]
  rfl

theorem mk_info_agrees (l : LabelSet) :
    sliceOf MK_INFO = (labelsOf l).mkInfo := by
  cases l
  simp [sliceOf, MK_INFO]
  rfl

/-! ## The bounds agree -/

theorem max_skip_agrees : MAX_SKIP.val = Model.State.maxSkip := by
  simp [MAX_SKIP, Model.State.maxSkip]

theorem max_skipped_store_agrees :
    MAX_SKIPPED_STORE.val = Model.State.maxSkippedStore := by
  simp [MAX_SKIPPED_STORE, Model.State.maxSkippedStore]

/-! ## The trusted boundary, restated as agreement

T1 assumed these primitives cannot fail. Refinement needs more: that when they
return, they return what the model computes. Both are stated against the model's
own definitions, so there is no third description of the derivation to keep in
step. -/

/-- The opaque HMAC returns, and returns the model's HMAC. Stated as one
assumption rather than two because the real primitive does both, and because a
separate totality assumption would then have to be kept in step with T1's. -/
def HmacAgrees : Prop :=
  ∀ key data, ∃ r, tacenta_kdf.hmac_sha256 key data = ok r ∧
    keyOf r = Model.Kdf.hmac (sliceOf key) (sliceOf data)

/-- The opaque HKDF returns, and returns the model's HKDF, for every output
length within RFC 5869's bound of 8160 bytes -- the bound the crate's own
`expect` enforces, and so exactly where the real operation returns
(`T1.HkdfTotal` says why). Argument order follows the Rust: the first slice is
the salt and the second the input keying material, which is how `kdf_rk` calls
it and how `Model.State.kdfRk` is written. -/
def HkdfAgrees : Prop :=
  ∀ N key salt info, N.val ≤ 8160 → ∃ r, tacenta_kdf.hkdf_sha256 N key salt info = ok r ∧
    keyOf r = Model.Kdf.hkdf (sliceOf key) (sliceOf salt) (sliceOf info) N.val

/-- Agreement is strictly stronger than the totality T1 assumed, so a caller
holding it need not carry T1's hypothesis as well. -/
theorem HmacAgrees.total (h : HmacAgrees) : Tacenta.T1.HmacTotal :=
  fun key data => let ⟨r, hr, _⟩ := h key data; ⟨r, hr⟩

theorem HkdfAgrees.total (h : HkdfAgrees) : Tacenta.T1.HkdfTotal :=
  fun N key salt info hN => let ⟨r, hr, _⟩ := h N key salt info hN; ⟨r, hr⟩

/-! ## Stepping rules carrying the derivation values

The same shape T1 used, but the postconditions now say what the primitive
returned rather than merely that it returned. -/

@[simp]
theorem sliceOf_to_slice {n : Usize} (a : Array Std.U8 n) :
    sliceOf a.to_slice = keyOf a := rfl

/-- The generated code passes byte literals through `Array.make`, which the
model states as plain lists. -/
@[simp]
theorem map_u8_make {n : Usize} (l : List Std.U8) (h) :
    List.map u8 (Array.make n l h).val = l.map u8 := rfl

@[step]
theorem hmac_step (h : HmacAgrees) (key data : Slice Std.U8) :
    tacenta_kdf.hmac_sha256 key data ⦃ fun r =>
      keyOf r = Model.Kdf.hmac (sliceOf key) (sliceOf data) ⦄ := by
  obtain ⟨r, hr, hv⟩ := h key data; simp [hr, hv]

@[step]
theorem hkdf_step (h : HkdfAgrees) (N : Usize) (key salt info : Slice Std.U8)
    (hN : N.val ≤ 8160) :
    tacenta_kdf.hkdf_sha256 N key salt info ⦃ fun r =>
      keyOf r = Model.Kdf.hkdf (sliceOf key) (sliceOf salt) (sliceOf info) N.val ⦄ := by
  obtain ⟨r, hr, hv⟩ := h N key salt info hN; simp [hr, hv]

/-- The `zeroize` wrapper round-trips: reading back what was wrapped gives the
same value. T1 needed only that neither step can fail. Refinement needs the
value to survive the wrapper, because otherwise nothing connects the expansion's
output to the halves copied out of it, and the root-key step could not be
related to the model at all. It is true of the crate for the same reason the
totality was: a newtype constructor and its projection. -/
def ZeroizingRoundTrips : Prop :=
  ∀ inst : zeroize.Zeroize (Array Std.U8 64#usize),
    (∀ z, ∃ w, zeroize.Zeroizing.new inst z = ok w ∧
       zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst w = ok z) ∧
    (∀ w, ∃ z, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst w = ok z)

/-- The round trip subsumes what T1 assumed, so a caller holding it does not
carry both. The second conjunct is what makes that so: the round trip alone says
nothing about a wrapper the code did not construct, and T1's statement quantifies
over all of them. -/
theorem ZeroizingRoundTrips.total (h : ZeroizingRoundTrips) :
    Tacenta.T1.ZeroizingTotal := by
  intro inst
  exact ⟨fun z => let ⟨w, hw, _⟩ := (h inst).1 z; ⟨w, hw⟩, (h inst).2⟩

@[step]
theorem zeroizing_new_step (hz : ZeroizingRoundTrips)
    (inst : zeroize.Zeroize (Array Std.U8 64#usize)) (z : Array Std.U8 64#usize) :
    zeroize.Zeroizing.new inst z ⦃ fun w =>
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst w = ok z ⦄ := by
  obtain ⟨w, hw, hd⟩ := (hz inst).1 z; simp [hw, hd]

/-! ## The chain-key step refines the model's -/

-- From here on the value-carrying rules are the ones wanted, so T1's
-- returns-only rule for the chain-key step comes out of the stepping set. T1's
-- own proofs are already checked and are unaffected.
attribute [-step] Tacenta.T1.kdf_ck_step

@[step]
theorem kdf_ck_refines (h : HmacAgrees) (ck : Array Std.U8 32#usize) :
    kdf_ck ck ⦃ fun r =>
      (keyOf r.1, keyOf r.2) = Model.State.kdfCk (keyOf ck) ⦄ := by
  unfold kdf_ck
  step*
  simp_all [Model.State.kdfCk, keyOf, u8]

/-! ## The state relation

Field by field, with the shape difference absorbed here and nowhere else. -/

/-- A translated skipped-key entry as the model's tuple. -/
def skippedOf (s : SkippedKey) : Model.State.Key × Nat × Nat × Model.State.Key :=
  (keyOf s.dh, s.n.val, s.stored_at.val, keyOf s.key)

/-- The translated state refines the model state. -/
structure StateR (s : State) (m : Model.State.State) : Prop where
  dhs_pub : keyOf s.dhs_pub = m.dhsPub
  dhr_pub : s.dhr_pub.map keyOf = m.dhrPub
  rk      : keyOf s.rk = m.rk
  cks     : s.cks.map keyOf = m.cks
  ckr     : s.ckr.map keyOf = m.ckr
  ns      : s.ns.val = m.ns
  nr      : s.nr.val = m.nr
  pn      : s.pn.val = m.pn
  skipped : s.skipped.val.map skippedOf = m.skipped
  /-- The store's clock. The core counts received messages in `u32` and the
      model in the naturals, so they agree only below `u32`'s width; that is the
      same finite-width boundary the counters already carry, and the refinement
      of `receive` excludes the saturating case for the same reason. -/
  events  : s.events.val = m.events
  /-- The label set both sides derive under. Carried through the translation
      rather than assumed: the verified zone takes it as a parameter and stores
      it, so a second set later is a value the proofs already range over rather
      than a change they have to absorb. -/
  labels  : labelsOf s.labels = m.labels

/-- The translated header refines the model header. -/
structure HeaderR (h : Header) (mh : Model.State.Header) : Prop where
  dh : keyOf h.dh = mh.dh
  pn : h.pn.val = mh.pn
  n  : h.n.val = mh.n

/-! ## The root-key step refines the model's -/

-- T1 registered a stepping rule for the wrapper's projection whose
-- postcondition is only that it returned. Here that is too weak: it would
-- introduce the unwrapped value with nothing tying it to what was wrapped, and
-- the expansion's output would be lost. Removing it locally makes the tactic
-- stop at the projection so the round trip can be applied by hand.
section DerefByHand
attribute [-step] Tacenta.T1.zeroizing_deref_step

@[step]
theorem kdf_rk_refines (h : HkdfAgrees) (hz : ZeroizingRoundTrips)
    (rk dh_out : Array Std.U8 32#usize) (labels : LabelSet) :
    kdf_rk rk dh_out labels ⦃ fun r =>
      (keyOf r.1, keyOf r.2)
        = Model.State.kdfRk (keyOf rk) (keyOf dh_out) (labelsOf labels) ⦄ := by
  have hzt : Tacenta.T1.ZeroizingTotal := hz.total
  have hht : Tacenta.T1.HkdfTotal := h.total
  unfold kdf_rk
  step*
  simp only [out_post]
  step* <;> simp_all [Slice.length, Model.State.kdfRk, keyOf,
    rk_info_agrees labels, List.map_take, List.map_drop]

-- The removal is scoped to this section, so nothing outside this proof is
-- affected by it and the rule is back in force from here on.
end DerefByHand

/-! ## Message-key expansion refines the model's

The last derivation before the cipher. A message key is expanded by one HKDF
call into the AEAD key, the MAC key and the IV, and it is the one derivation a
label or split-order error would change every ciphertext key through while
every ratchet-level theorem stayed true, since nothing above it reads the
expansion back. So it is related to `Model.State.messageKeys` directly: the
same zero salt, the same `info`, the same eighty bytes split at the same two
offsets. -/

/-- The `zeroize` round trip at the eighty-byte width `message_keys` wraps its
expansion at. `ZeroizingRoundTrips` is stated at sixty-four bytes, the
root-key step's width, and deliberately no wider, so this is the same
assumption at the one other width the crate uses, kept separate so that no
existing theorem's hypothesis widens. -/
def ZeroizingRoundTrips80 : Prop :=
  ∀ inst : zeroize.Zeroize (Array Std.U8 80#usize),
    (∀ z, ∃ w, zeroize.Zeroizing.new inst z = ok w ∧
       zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst w = ok z) ∧
    (∀ w, ∃ z, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst w = ok z)

@[step]
theorem zeroizing_new_step80 (hz : ZeroizingRoundTrips80)
    (inst : zeroize.Zeroize (Array Std.U8 80#usize)) (z : Array Std.U8 80#usize) :
    zeroize.Zeroizing.new inst z ⦃ fun w =>
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst w = ok z ⦄ := by
  obtain ⟨w, hw, hd⟩ := (hz inst).1 z; simp [hw, hd]

/-- The translated zero byte is the model's zero byte. The stepping tactic
expands the all-zero salt into thirty-two translated literals, so this is what
lets the salt the code passes normalise to the salt the model writes. -/
theorem u8_zero : u8 0#u8 = 0 := rfl

theorem message_keys_refines (h : HkdfAgrees) (hz : ZeroizingRoundTrips80)
    (mk : Array Std.U8 32#usize) (labels : LabelSet) :
    message_keys mk labels ⦃ fun r =>
      (keyOf r.1, keyOf r.2.1, keyOf r.2.2)
        = Model.State.messageKeys (keyOf mk) (labelsOf labels) ⦄ := by
  have hht : Tacenta.T1.HkdfTotal := h.total
  unfold message_keys
  step*
  simp only [out_post]
  step* <;> simp_all [Slice.length, Model.State.messageKeys, keyOf,
    mk_info_agrees labels, u8_zero, List.slice, List.map_take, List.map_drop]

/-! ## Sending refines the model's send

The two disagree in one place, and it is worth naming rather than hiding. The
model counts messages in `Nat` and so can always send; the Rust counts in `u32`
and reports `ChainExhausted` when the counter would wrap. That case has no
model counterpart, so the statement below relates the two where they can be
related: a successful send agrees with the model, and the "no sending chain"
refusal agrees with the model's `none`. The exhaustion case is the finite-width
boundary showing through, not a defect, and it is left out of the correspondence
deliberately. -/

theorem send_refines (h : HmacAgrees) (s : State) (m : Model.State.State)
    (hR : StateR s m) :
    send s ⦃ fun r =>
      (∀ hdr mk, r.1 = core.result.Result.Ok (hdr, mk) →
        ∃ m' mh, Model.Ratchet.send m = some (m', mh, keyOf mk)
          ∧ StateR r.2 m' ∧ HeaderR hdr mh)
      ∧ (r.1 = core.result.Result.Err RatchetError.NoSendingChain →
          Model.Ratchet.send m = none) ⦄ := by
  obtain ⟨hdhs, hdhr, hrk, hcks, hckr, hns, hnr, hpn, hskip, hev, hlab⟩ := hR
  unfold send
  rcases hc : s.cks with _ | ck
  · simp_all [Model.Ratchet.send, ← hcks]
  · rcases hadd : s.ns.checked_add 1#u32 with _ | next_ns
    · simp_all [lift]
    · simp only [lift]
      step*
      have hm : m.cks = some (keyOf ck) := by rw [← hcks, hc]; simp
      have hspec := U32.checked_add_bv_spec s.ns 1#u32
      rw [hadd] at hspec
      simp_all [Model.Ratchet.send, Model.State.kdfCk]
      exact ⟨⟨hdhs, hdhr, hrk, by simp_all, hckr, by simp_all, hnr, hpn, hskip,
              hev, by simp_all⟩,
             ⟨hdhs, hpn, hns⟩⟩

/-! ## The DH ratchet step refines the model's

The one operation where the two definitions line up field for field, so it is
short. What it is really doing is carrying the relation across a whole-state
replacement rather than a single field update. -/

theorem dh_ratchet_refines (h : HkdfAgrees) (hz : ZeroizingRoundTrips)
    (s : State) (m : Model.State.State) (hR : StateR s m)
    (hdr : Header) (mh : Model.State.Header) (hH : HeaderR hdr mh)
    (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize) :
    dh_ratchet s hdr dh_out_recv dh_out_send new_dhs_pub ⦃ fun s' =>
      StateR s' (Model.Ratchet.dhRatchet m mh (keyOf dh_out_recv)
        (keyOf dh_out_send) (keyOf new_dhs_pub)) ⦄ := by
  obtain ⟨hdhs, hdhr, hrk, hcks, hckr, hns, hnr, hpn, hskip, hev, hlab⟩ := hR
  obtain ⟨hhdh, hhpn, hhn⟩ := hH
  unfold dh_ratchet
  step*
  simp_all [Model.Ratchet.dhRatchet, Model.State.kdfRk]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

/-! ## Chain derivation refines the model's

The first loop, and the shape of its proof is the one the remaining loops will
take. A loop cannot be related to a structural recursion one step at a time,
because the recursion consumes its argument from the front while the loop
accumulates from the back. What works instead is to say the model's prediction
made from the *current* loop state is the same prediction it made from the
state the loop started in. That is a constant, so it survives as an invariant,
and at the exit it is exactly what the loop returned. -/

/-- A produced key pair as the model records it. -/
def pairOf (p : Std.U32 × Array Std.U8 32#usize) : Nat × Model.State.Key :=
  (p.1.val, keyOf p.2)

/-- The accumulated keys as the model's list. -/
def keysOf (v : alloc.vec.Vec (Std.U32 × Array Std.U8 32#usize)) :
    List (Nat × Model.State.Key) := v.val.map pairOf

/-- What the model says this loop state will have produced once it finishes:
the keys already accumulated, followed by those the remaining iterations will
derive. -/
def predOf (start_n : Std.U32) (it : core.ops.range.Range Std.U32)
    (cur : Array Std.U8 32#usize)
    (ks : alloc.vec.Vec (Std.U32 × Array Std.U8 32#usize)) :
    Model.State.Key × List (Nat × Model.State.Key) :=
  let r := Model.State.deriveChain (keyOf cur) (start_n.val + it.start.val)
    (it.end.val - it.start.val)
  (r.1, keysOf ks ++ r.2)

theorem derive_chain_loop_refines (h : HmacAgrees) [DerivedKeysModel]
    (start_n : Std.U32)
    (target : Model.State.Key × List (Nat × Model.State.Key))
    (B : Nat) (hB : B ≤ Usize.max)
    (iter : core.ops.range.Range Std.U32) (cur : Array Std.U8 32#usize)
    (keys : zeroize.Zeroizing (alloc.vec.Vec (Std.U32 × Array Std.U8 32#usize)))
    (hb : (DerivedKeysModel.contents keys).val.length
          + (iter.end.val - iter.start.val) ≤ B)
    (hinv : predOf start_n iter cur (DerivedKeysModel.contents keys) = target) :
    derive_chain_loop iter start_n cur keys ⦃ fun r =>
      match r with
      | core.result.Result.Ok p =>
        (keyOf p.1, keysOf (DerivedKeysModel.contents p.2)) = target
        ∧ (DerivedKeysModel.contents p.2).val.length ≤ B
      | core.result.Result.Err _ => True ⦄ := by
  unfold derive_chain_loop
  apply loop.spec_decr_nat
    (measure := fun x => (Prod.fst x).end.val - (Prod.fst x).start.val)
    (inv := fun x =>
      predOf start_n (Prod.fst x) (Prod.fst (Prod.snd x))
          (DerivedKeysModel.contents (Prod.snd (Prod.snd x)))
          = target
      ∧ (DerivedKeysModel.contents (Prod.snd (Prod.snd x))).val.length
          + ((Prod.fst x).end.val - (Prod.fst x).start.val) ≤ B)
  · rintro ⟨it, c, ks⟩ ⟨hinv2, hlen⟩
    simp only at hinv2 hlen
    simp only [derive_chain_loop.body]
    by_cases hlt : it.start.val < it.end.val
    · -- One more iteration. The model's recursion has to be exposed at a
      -- successor before it will unfold, which is what `hk` is for; without it
      -- the hypothesis keeps the count opaque and the two sides never meet.
      obtain ⟨k, hk⟩ : ∃ k, it.end.val - it.start.val = k + 1 :=
        ⟨it.end.val - it.start.val - 1, by omega⟩
      have hk2 : it.end.val - (it.start.val + 1) = k := by omega
      simp only [predOf, hk, Model.State.deriveChain, Model.State.kdfCk] at hinv2
      step*
      all_goals
        simp_all [predOf, keysOf, pairOf, Model.State.kdfCk, Nat.add_assoc]
      all_goals omega
    · -- The range is spent, so the model derives nothing further and the
      -- invariant is already the answer.
      step*
      simp_all [predOf, keysOf, Model.State.deriveChain]
  · exact ⟨hinv, hb⟩

/-- The loop lifted to the whole function: what the Rust derives is what the
model derives, whenever it does not report exhaustion, and no more keys than it
was asked for.

Bounding against a free `B` rather than against `Usize.max` directly is what
makes this usable as a stepping rule. A count that is a `u32` is below
`Usize.max` on any target, so the bound discharges itself here and the rule
carries no hypothesis a caller has to supply. Demanding a *strict* bound instead
would not: on a 32-bit target `Usize.max` and `U32.max` coincide, so the strict
form is false of some `u32` and every caller would have to prove it away. The
strictness the vector push actually needs comes from there being an iteration
left to do, which the loop knows and a caller should not have to. -/
@[step]
theorem derive_chain_refines (h : HmacAgrees) [DerivedKeysModel]
    (ck : Array Std.U8 32#usize) (start_n count : Std.U32) :
    derive_chain ck start_n count ⦃ fun r =>
      match r with
      | core.result.Result.Ok p =>
        (keyOf p.1, keysOf (DerivedKeysModel.contents p.2))
          = Model.State.deriveChain (keyOf ck) start_n.val count.val
        ∧ (DerivedKeysModel.contents p.2).val.length ≤ count.val
      | core.result.Result.Err _ => True ⦄ := by
  unfold derive_chain
  simp only [lift, alloc.vec.Vec.with_capacity]
  step
  refine derive_chain_loop_refines h start_n _ count.val (by scalar_tac)
    _ ck _ ?_ ?_
  · simp_all
  · simp_all [predOf, keysOf]

/-! ## Storing skipped keys refines the model's

The second loop, and the same invariant shape: what the store will hold once the
iterator is spent, held equal to what it was going to hold at the start. -/

/-- A derived key as the model stores it, under the receiving ratchet key. -/
def storedOf (dhr : Array Std.U8 32#usize) (now : Std.U32)
    (p : Std.U32 × Array Std.U8 32#usize) :
    Model.State.Key × Nat × Nat × Model.State.Key :=
  (keyOf dhr, p.1.val, now.val, keyOf p.2)

/-- Stated at the value the arguments determine rather than at a free target,
which is what lets it serve as a stepping rule: a free target would have to be
guessed. The length bound stays a hypothesis, because the sum of two vector
lengths is not bounded in general; the caller discharges it from its own store
guard. The loop reads the wrapper by index, so what it appends is the part of
the wrapper's contents from the cursor on. -/
@[step]
theorem skip_message_keys_loop_refines [DerivedKeysModel]
    (dhr : Array Std.U8 32#usize) (v : alloc.vec.Vec SkippedKey) (now : Std.U32)
    (keys : zeroize.Zeroizing (alloc.vec.Vec (Std.U32 × Array Std.U8 32#usize)))
    (i : Usize)
    (hb : v.val.length + ((DerivedKeysModel.contents keys).val.length - i.val)
          ≤ Usize.max) :
    skip_message_keys_loop dhr v now keys i ⦃ fun r =>
      r.val.map skippedOf
        = v.val.map skippedOf
          ++ ((DerivedKeysModel.contents keys).val.drop i.val).map (storedOf dhr now) ⦄ := by
  set target := v.val.map skippedOf
    ++ ((DerivedKeysModel.contents keys).val.drop i.val).map (storedOf dhr now)
    with htarget
  have hinv : v.val.map skippedOf
    ++ ((DerivedKeysModel.contents keys).val.drop i.val).map (storedOf dhr now)
    = target := rfl
  unfold skip_message_keys_loop
  apply loop.spec_decr_nat
    (measure := fun x =>
      (DerivedKeysModel.contents keys).val.length - (Prod.snd x).val)
    (inv := fun x =>
      (Prod.fst x).val.map skippedOf
          ++ ((DerivedKeysModel.contents keys).val.drop (Prod.snd x).val).map
               (storedOf dhr now) = target
      ∧ (Prod.fst x).val.length
          + ((DerivedKeysModel.contents keys).val.length - (Prod.snd x).val)
          ≤ Usize.max)
  · rintro ⟨vv, j⟩ ⟨hinv2, hlen⟩
    simp only at hinv2 hlen
    simp only [skip_message_keys_loop.body]
    have hfits := (DerivedKeysModel.contents keys).property
    by_cases hlt : j.val < (DerivedKeysModel.contents keys).val.length
    · -- One more key: it moves from the head of what is left to read onto
      -- the end of the store, and the answer does not change.
      rw [List.drop_eq_getElem_cons hlt] at hinv2
      step*
      subst v1_post
      -- The two reads at the cursor are the two halves of the same entry.
      have h1 := congrArg Prod.fst i3_post
      have h2 := congrArg Prod.snd __post
      simp only at h1 h2
      refine ⟨?_, ?_, ?_⟩
      · -- Done by hand rather than by `simp_all`, which folds the exposed head
        -- back into the drop and loses the entry it was exposed for.
        rw [v2_post, i4_post, ← hinv2]
        simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          List.singleton_append, skippedOf, storedOf, h1, h2]
      · simp only [v2_post, List.length_append, List.length_singleton, i4_post]
        omega
      · rw [i4_post]
        omega
    · -- Nothing left to read, so the invariant is already the answer.
      have hge : (DerivedKeysModel.contents keys).val.length ≤ j.val := by omega
      rw [List.drop_eq_nil_of_le hge] at hinv2
      step*
      simp_all [alloc.vec.Vec.len]
  · exact ⟨hinv, hb⟩

/-! ## The skip step refines the model's

The two loops are related above. What is left is the guards, and the first of
them is not a calculation. The Rust bounds the per-chain skip with a saturating
`u32` addition where the model adds in `Nat`, so the values differ exactly when
the addition would overflow. Only one direction is needed, and it holds either
way: the saturated result never exceeds the true sum, so a message number the
Rust accepted is one the model accepts too. -/

theorem saturating_add_le (x y : Std.U32) :
    (core.num.U32.saturating_add x y).val ≤ x.val + y.val := by
  simp only [core.num.U32.saturating_add, UScalar.saturating_add]
  simp only [UScalar.val, BitVec.toNat_ofNat]
  simp [UScalarTy.numBits]
  omega

/-! ## The purge scan refines the model's filter

The scan removes at an index without advancing it, so the invariant cannot be
"the prefix is done" alone: the vector itself shrinks underneath. What holds is
that the entries before the index are settled and the rest are still to be
judged, so the answer is the settled prefix followed by the filtered tail. At
the exit the tail is empty and that is the answer. -/

/-- The model's side of the purge predicate: keep what the skip is not about to
replace. -/
def keepOutside (dhr : Model.State.Key) (from1 upto : Nat)
    (e : Model.State.Key × Nat × Nat × Model.State.Key) : Bool :=
  !(e.1 == dhr && decide (from1 ≤ e.2.1) && decide (e.2.1 < upto))

/-- Stepping past an entry the predicate keeps: it moves from the filtered tail
into the settled prefix, and the answer does not change. -/
theorem prefix_step_keep {α : Type} (L : List α) (p : α → Bool) (j : Nat)
    (hj : j < L.length) (hp : p L[j] = true) :
    L.take j ++ (L.drop j).filter p = L.take (j + 1) ++ (L.drop (j + 1)).filter p := by
  rw [List.drop_eq_getElem_cons hj, List.filter_cons_of_pos hp]
  have h : L.take (j + 1) = L.take j ++ [L[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; simp
  simp only [h, List.append_assoc, List.singleton_append]

/-- Removing an entry the predicate rejects: it leaves the filtered tail and
does not join the prefix, and the answer does not change. -/
theorem prefix_step_drop {α : Type} (L : List α) (p : α → Bool) (j : Nat)
    (hj : j < L.length) (hp : p L[j] = false) :
    L.take j ++ (L.drop j).filter p = L.take j ++ (L.drop (j + 1)).filter p := by
  rw [List.drop_eq_getElem_cons hj, List.filter_cons_of_neg (by simp [hp])]

/-- Mapping commutes with taking and dropping a prefix. The translated goals
arrive with the map on the inside and the list lemmas below want it on the
outside; this is the step between, and the scan's proof relies on `simp_all`
to apply it before those rewrites can land. -/
theorem map_take {α β : Type} (f : α → β) (l : List α) (n : Nat) :
    (l.take n).map f = (l.map f).take n := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih => cases n <;> simp [ih]

theorem map_drop {α β : Type} (f : α → β) (l : List α) (n : Nat) :
    (l.drop n).map f = (l.map f).drop n := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih => cases n <;> simp [ih]

/-- When at most one entry satisfies a predicate and the entry at `k` is that
one, filtering the satisfying entries out is the same as erasing that index.

This is what makes the skipped-key lookup relatable at all. The model deletes by
filtering every match and the core removes the first it finds, and those agree
exactly when there is no second one. The store is kept a map so that holds, but
it is a hypothesis here rather than a fact, because nothing in this function
establishes it. -/
theorem filter_not_eq_eraseIdx {α : Type} (p : α → Bool) (l : List α) (k : Nat)
    (hk : k < l.length) (hpk : p l[k] = true)
    (hone : (l.filter p).length ≤ 1) :
    l.filter (fun x => !p x) = l.eraseIdx k := by
  have hsplit : l = l.take k ++ l[k] :: l.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hfil : (l.filter p).length
      = ((l.take k).filter p).length + 1 + ((l.drop (k + 1)).filter p).length := by
    nth_rewrite 1 [hsplit]
    simp only [List.filter_append, List.filter_cons_of_pos hpk,
      List.length_append, List.length_cons]
    omega
  have hpre : (l.take k).filter p = [] := by
    have : ((l.take k).filter p).length = 0 := by omega
    exact List.length_eq_zero_iff.mp this
  have hpost : (l.drop (k + 1)).filter p = [] := by
    have : ((l.drop (k + 1)).filter p).length = 0 := by omega
    exact List.length_eq_zero_iff.mp this
  have hkeep : ∀ (m : List α), m.filter p = [] → m.filter (fun x => !p x) = m := by
    intro m hm
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [Bool.not_eq_true']
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    have : x ∈ m.filter p := List.mem_filter.mpr ⟨hx, hc⟩
    rw [hm] at this
    exact absurd this (List.not_mem_nil)
  rw [List.eraseIdx_eq_take_drop_succ]
  nth_rewrite 1 [hsplit]
  rw [List.filter_append, List.filter_cons_of_neg (by simp [hpk]),
    hkeep _ hpre, hkeep _ hpost]

/-- Mapping commutes with erasing at an index. -/
theorem map_eraseIdx {α β : Type} (f : α → β) (l : List α) (i : Nat) :
    (l.eraseIdx i).map f = (l.map f).eraseIdx i := by
  induction l generalizing i with
  | nil => simp
  | cons a t ih => cases i <;> simp [ih]

/-- Erasing the entry at the index leaves the answer alone, when the predicate
rejects it. This is `prefix_step_drop` stated the way the scan reaches it, with
the vector already shortened and the index standing still. -/
theorem prefix_step_erase {α : Type} (L : List α) (p : α → Bool) (j : Nat)
    (hj : j < L.length) (hp : p L[j] = false) :
    (L.eraseIdx j).take j ++ ((L.eraseIdx j).drop j).filter p
      = L.take j ++ (L.drop j).filter p := by
  have hlen : (L.take j).length = j := by simp; omega
  rw [List.eraseIdx_eq_take_drop_succ, List.take_left' hlen, List.drop_left' hlen]
  exact (prefix_step_drop L p j hj hp).symm

/-! ## Session initialisation refines the model's

Both are straight-line, so they are short. What they are worth is the endpoints:
every other theorem here relates one step to one step, and these say the two
sides start in states that already correspond, without which the steps compose
from nothing. -/

theorem init_receiver_refines (sk our_pub : Array Std.U8 32#usize)
    (labels : LabelSet) :
    init_receiver sk our_pub labels ⦃ fun s =>
      StateR s (Model.Ratchet.initReceiver (keyOf sk) (keyOf our_pub)
        (labelsOf labels)) ⦄ := by
  unfold init_receiver
  simp only [Model.Ratchet.initReceiver]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
  simp

theorem init_sender_refines (h : HkdfAgrees) (hz : ZeroizingRoundTrips)
    (sk our_pub peer_pub dh_out : Array Std.U8 32#usize) (labels : LabelSet) :
    init_sender sk our_pub peer_pub dh_out labels ⦃ fun s =>
      StateR s (Model.Ratchet.initSender (keyOf sk) (keyOf our_pub)
        (keyOf peer_pub) (keyOf dh_out) (labelsOf labels)) ⦄ := by
  unfold init_sender
  step*
  simp_all [Model.Ratchet.initSender, Model.State.kdfRk]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

theorem purge_chain_range_loop_refines (hrm : Tacenta.T1.VecRemoveTotal)
    (dhr : Array Std.U8 32#usize) (from1 upto : Std.U32)
    (target : List (Model.State.Key × Nat × Nat × Model.State.Key))
    (skipped : alloc.vec.Vec SkippedKey) (i : Usize)
    (hinv : (skipped.val.take i.val).map skippedOf
        ++ ((skipped.val.drop i.val).map skippedOf).filter
             (keepOutside (keyOf dhr) from1.val upto.val) = target) :
    purge_chain_range_loop skipped dhr from1 upto i ⦃ fun r =>
      r.val.map skippedOf = target ⦄ := by
  unfold purge_chain_range_loop
  apply loop.spec_decr_nat
    (measure := fun x => (Prod.fst x).val.length - (Prod.snd x).val)
    (inv := fun x =>
      ((Prod.fst x).val.take (Prod.snd x).val).map skippedOf
        ++ (((Prod.fst x).val.drop (Prod.snd x).val).map skippedOf).filter
             (keepOutside (keyOf dhr) from1.val upto.val) = target)
  · rintro ⟨v, j⟩ hinv2
    simp only at hinv2
    simp only [purge_chain_range_loop.body]
    simp only [map_take, map_drop] at hinv2
    -- The removal's hypothesis is available only under the guard the body
    -- checks first, so the case split comes before the removal is named.
    by_cases hlt : j.val < v.val.length
    · obtain ⟨⟨removed, v'⟩, hrm', hv⟩ := hrm Global v j hlt
      simp only [hrm']
      step*
      all_goals
        first
          -- The entry matches: it goes, and the index stays put.
          | (rw [hv]
             refine ⟨?_, by simp only [List.length_eraseIdx]; split <;> omega⟩
             simp only [map_take, map_drop, map_eraseIdx]
             rw [prefix_step_erase (List.map skippedOf v.val)
               (keepOutside (keyOf dhr) from1.val upto.val) j.val
               (by simpa using hlt)
               (by simp_all [keepOutside, skippedOf])]
             exact hinv2)
          -- The entry is kept and the scan steps past it.
          | (rw [i2_post]
             refine ⟨?_, by omega⟩
             simp only [map_take, map_drop]
             rw [← prefix_step_keep (List.map skippedOf v.val)
               (keepOutside (keyOf dhr) from1.val upto.val) j.val
               (by simpa using hlt)
               (by simp_all [keepOutside, skippedOf])]
             exact hinv2)
    · -- The scan is spent: nothing is left to judge, so the invariant is
      -- already the answer.
      step*
      have hge : (List.map skippedOf v.val).length ≤ j.val := by
        simp; omega
      rw [List.take_of_length_le hge, List.drop_eq_nil_of_le hge] at hinv2
      simpa using hinv2
  · exact hinv

/-- The scan lifted to the whole function: what it leaves in the store is what
the model's filter leaves. -/
@[step]
theorem purge_chain_range_refines (hrm : Tacenta.T1.VecRemoveTotal)
    (skipped : alloc.vec.Vec SkippedKey) (dhr : Array Std.U8 32#usize)
    (from1 upto : Std.U32) :
    purge_chain_range skipped dhr from1 upto ⦃ fun r =>
      r.val.map skippedOf
        = (skipped.val.map skippedOf).filter
            (keepOutside (keyOf dhr) from1.val upto.val) ⦄ := by
  unfold purge_chain_range
  refine purge_chain_range_loop_refines hrm dhr from1 upto _ skipped 0#usize ?_
  simp

/-! ## Expiry refines the model's

The same loop shape as the purge above: an index scan that removes what a
predicate rejects. The predicate is the only difference, and it lines up without
a side condition, because the core's subtraction saturates and the model's is
over the naturals, which truncates. -/

/-- The saturating subtraction is the naturals' subtraction on the values. This
is why expiry needs no invariant about `stored_at` being behind `now`: the two
sides agree even when it is not. -/
theorem saturating_sub_val (x y : Std.U32) :
    (core.num.U32.saturating_sub x y).val = x.val - y.val := by
  first
    | scalar_tac
    | (simp only [core.num.U32.saturating_sub, UScalar.saturating_sub]
       scalar_tac)
    | (simp only [core.num.U32.saturating_sub, UScalar.saturating_sub,
         UScalar.val, BitVec.toNat_ofNat, UScalarTy.numBits, Nat.zero_max]
       omega)

/-- The saturating addition at its value, which the counter's step needs
exactly rather than as the bound `saturating_add_le` gives. -/
theorem saturating_add_val (x y : Std.U32) :
    (core.num.U32.saturating_add x y).val = min U32.max (x.val + y.val) := by
  simp only [core.num.U32.saturating_add, UScalar.saturating_add, UScalar.val,
    BitVec.toNat_ofNat]
  have h : min (UScalar.max UScalarTy.U32) (x.val + y.val)
      < 2 ^ UScalarTy.U32.numBits := by
    have := Nat.min_le_left (UScalar.max UScalarTy.U32) (x.val + y.val)
    simp only [UScalar.max, UScalarTy.numBits] at *
    omega
  simpa [U32.max] using Nat.mod_eq_of_lt h

/-- The model's side of the expiry predicate: keep what has not outlived the
cap. -/
def keepFresh (now : Nat) (e : Model.State.Key × Nat × Nat × Model.State.Key) : Bool :=
  decide (now - e.2.2.1 < Model.State.maxSkippedAge)

/-- The model writes its predicate inline; this names it, the same move as
`matchesHeader_eta`, so the filter it builds rewrites into the loop's form.
Not a global `simp` lemma: its left-hand side is a lambda, which the
discrimination tree cannot index, so it is supplied by name where it is
needed. -/
theorem keepFresh_eta (now : Nat) :
    (fun e : Model.State.Key × Nat × Nat × Model.State.Key =>
      decide (now - e.2.2.1 < Model.State.maxSkippedAge)) = keepFresh now :=
  rfl

theorem age_store_loop_refines (hrm : Tacenta.T1.VecRemoveTotal)
    (now : Std.U32)
    (target : List (Model.State.Key × Nat × Nat × Model.State.Key))
    (skipped : alloc.vec.Vec SkippedKey) (i : Usize)
    (hinv : (skipped.val.take i.val).map skippedOf
        ++ ((skipped.val.drop i.val).map skippedOf).filter (keepFresh now.val)
      = target) :
    age_store_loop skipped now i ⦃ fun r => r.val.map skippedOf = target ⦄ := by
  unfold age_store_loop
  apply loop.spec_decr_nat
    (measure := fun x => (Prod.fst x).val.length - (Prod.snd x).val)
    (inv := fun x =>
      ((Prod.fst x).val.take (Prod.snd x).val).map skippedOf
        ++ (((Prod.fst x).val.drop (Prod.snd x).val).map skippedOf).filter
             (keepFresh now.val) = target)
  · rintro ⟨v, j⟩ hinv2
    simp only at hinv2
    simp only [age_store_loop.body, lift]
    simp only [map_take, map_drop] at hinv2
    -- The exit case is separated rather than left to a fallback branch: a
    -- `first` cannot back out of a failure raised inside a nested `by`, so a
    -- branch that half-applies here would take the goal with it. The removal
    -- is named only in the other case, under the guard its hypothesis needs.
    by_cases hlt : j.val < v.val.length
    case neg =>
      step*
      rw [List.drop_eq_nil_of_le (by simpa using hlt), List.filter_nil,
        List.append_nil, List.take_of_length_le (by simpa using hlt)] at hinv2
      exact hinv2
    obtain ⟨⟨removed, v'⟩, hrm', hv⟩ := hrm Global v j hlt
    simp only [hrm']
    step*
    all_goals
      first
        -- Expired: the entry goes, and the index stays put.
        | (rw [hv]
           refine ⟨?_, by simp only [List.length_eraseIdx]; split <;> omega⟩
           simp only [map_take, map_drop, map_eraseIdx]
           rw [prefix_step_erase (List.map skippedOf v.val)
             (keepFresh now.val) j.val
             (by simpa using hlt)
             (by simp_all [keepFresh, skippedOf, saturating_sub_val,
                   MAX_SKIPPED_AGE, Model.State.maxSkippedAge])]
           exact hinv2)
        -- Still fresh, so the scan steps past it.
        | (rw [i3_post]
           refine ⟨?_, by omega⟩
           simp only [map_take, map_drop]
           rw [← prefix_step_keep (List.map skippedOf v.val)
             (keepFresh now.val) j.val
             (by simpa using hlt)
             (by simp_all [keepFresh, skippedOf, saturating_sub_val,
                   MAX_SKIPPED_AGE, Model.State.maxSkippedAge])]
           exact hinv2)
  · simpa using hinv

/-- Ageing the store refines the model's, given the counter has room for the
step. The bound is the finite-width boundary, and the core now stops one short
of it: the saturating step is clamped to `MAX_EVENTS`, one below `u32::MAX`, so
that a state the crate exports still satisfies its own `invariant`'s
`events < u32::MAX` rather than being refused by its own decoder forever. The
model counts in the naturals and neither saturates nor clamps, so the two part
company at the clamp and not only at the ceiling: from `events = MAX_EVENTS` the
core's clock stands still while the model's moves on. The precondition therefore
asks room for the increment -- `events + 1 < U32.max`, which is
`events < MAX_EVENTS` -- and not merely for the value, and that is exactly the
region where the two agree. Below it the clamp never fires and `now` is the
saturating step itself. -/
theorem age_store_refines (hrm : Tacenta.T1.VecRemoveTotal)
    (s : State) (m : Model.State.State) (hR : StateR s m)
    (hroom : s.events.val + 1 < U32.max) :
    age_store s ⦃ fun s' => StateR s' (Model.State.ageStore m) ⦄ := by
  obtain ⟨hdhs, hdhr, hrk, hcks, hckr, hns, hnr, hpn, hskip, hev, hlab⟩ := hR
  unfold age_store
  simp only [lift]
  have hnow : (core.num.U32.saturating_add s.events 1#u32).val = m.events + 1 := by
    rw [saturating_add_val]
    scalar_tac
  -- The clamp is a branch on a value, not on a computation, so it is discharged
  -- before the stepping tactic reaches it. Under `hroom` the step lands strictly
  -- below the ceiling, so the branch is the `else` and `now` is the step itself.
  have hmax : (core.num.U32.MAX : U32).val = U32.max := by
    simp only [core.num.U32.MAX, UScalar.ofNat, UScalar.ofNatCore_val_eq, U32.rMax]
    scalar_tac
  have hne : ¬ (core.num.U32.saturating_add s.events 1#u32 = core.num.U32.MAX) := by
    intro hc
    have hval := congrArg UScalar.val hc
    rw [saturating_add_val, hmax] at hval
    scalar_tac
  simp only [bind_tc_ok, if_neg hne]
  have hl := age_store_loop_refines hrm (core.num.U32.saturating_add s.events 1#u32)
    _ s.skipped 0#usize rfl
  step*
  refine ⟨hdhs, hdhr, hrk, hcks, hckr, hns, hnr, hpn, ?_, ?_, hlab⟩
  · simp only [Model.State.ageStore]
    rw [← hskip]
    simp_all [keepFresh_eta]
  · simpa [Model.State.ageStore] using hnow

theorem skip_message_keys_refines (h : HmacAgrees)
    (hrm : Tacenta.T1.VecRemoveTotal) [DerivedKeysModel] (s : State)
    (m : Model.State.State) (hR : StateR s m) (upto : Std.U32)
    (hs : s.skipped.val.length + MAX_SKIP.val ≤ Usize.max) :
    skip_message_keys s upto ⦃ fun r =>
      r.1 = core.result.Result.Ok () →
        ∃ m', Model.State.skipMessageKeys m upto.val = some m'
          ∧ StateR r.2 m' ⦄ := by
  have hSR := hR
  have hht : Tacenta.T1.HmacTotal := h.total
  obtain ⟨hdhs, hdhr, hrk, hcks, hckr, hns, hnr, hpn, hskip, hev, hlab⟩ := hR
  unfold skip_message_keys
  rcases hck : s.ckr with _ | ck
  · have hm : m.ckr = none := by rw [← hckr, hck]; rfl
    simp [Model.State.skipMessageKeys, hm]
    exact hSR
  · rcases hdh : s.dhr_pub with _ | dhr
    · have hm : m.dhrPub = none := by rw [← hdhr, hdh]; rfl
      simp [Model.State.skipMessageKeys, hm]
      exact hSR
    · have hmck : m.ckr = some (keyOf ck) := by rw [← hckr, hck]; rfl
      have hmdh : m.dhrPub = some (keyOf dhr) := by rw [← hdhr, hdh]; rfl
      simp only [Model.State.skipMessageKeys, hmck, hmdh]
      by_cases hle : upto ≤ s.nr
      · have hleN : upto.val ≤ m.nr := by rw [← hnr]; scalar_tac
        simp [hle, hleN]
        exact hSR
      · have hgtN : ¬ (upto.val ≤ m.nr) := by rw [← hnr]; scalar_tac
        simp only [hle, hgtN, if_false, lift]
        -- The `MAX_SKIP` guard is split before stepping: under it the call is
        -- the `TooManySkipped` return and the postcondition is vacuous, and
        -- under its negation `skip_gap_le` bounds the gap the store grows by,
        -- which is what the store's overflow obligation now needs.
        by_cases hg : upto > core.num.U32.saturating_add s.nr MAX_SKIP
        · have hg' : (core.num.U32.saturating_add s.nr MAX_SKIP).val < upto.val := hg
          simp [hg']
        have hgap := Tacenta.T1.skip_gap_le s.nr upto hg
        step*
        obtain ⟨ck2, keys⟩ := v
        have hrOk : r = core.result.Result.Ok (ck2, keys) := by assumption
        rw [hrOk] at r_post
        obtain ⟨rp, rlen⟩ := r_post
        step*
        · -- The purge shrank the store, so the storing loop still fits.
          have hlen := congrArg List.length v1_post
          have hfil := List.length_filter_le
            (keepOutside (keyOf dhr) s.nr.val upto.val)
            (List.map skippedOf s.skipped.val)
          have hi2max : i2.val ≤ U32.max := by scalar_tac
          simp only [List.length_map] at hlen hfil
          simp only at rlen
          omega
        · intro _
          have hsatle := saturating_add_le s.nr MAX_SKIP
          have hg1 : ¬ (upto.val > m.nr + Model.State.maxSkip) := by
            rw [← hnr]
            simp only [MAX_SKIP, Model.State.maxSkip] at *
            scalar_tac
          have hg2 : ¬ (m.skipped.length + (upto.val - m.nr)
              > Model.State.maxSkippedStore) := by
            rw [← hnr, ← hskip]
            simp only [Model.State.maxSkippedStore, MAX_SKIPPED_STORE,
              alloc.vec.Vec.len] at *
            scalar_tac
          simp only [hg1, hg2, if_false]
          -- The derivation was indexed by the Rust's counters; restate it at
          -- the model's before matching, or the two never line up.
          have hi2 : i2.val = upto.val - m.nr := by rw [← hnr]; omega
          rw [hnr, hi2] at rp
          have rck := congrArg Prod.fst rp
          have rkeys := congrArg Prod.snd rp
          simp only at rck rkeys
          -- The store the loop built, restated as the list the model appends.
          have hstored : List.map (storedOf dhr s.events)
                ((DerivedKeysModel.contents keys).val.drop 0)
              = List.map (fun x => (keyOf dhr, x.1, m.events, x.2))
                  (Model.State.deriveChain (keyOf ck) m.nr (upto.val - m.nr)).2 := by
            rw [List.drop_zero, ← rkeys]
            simp [keysOf, List.map_map, storedOf, pairOf, hev]
          -- What the purge left, restated at the model's counter.
          have hkept : List.map skippedOf v1.val
              = (m.skipped.filter fun e =>
                  !(e.1 == keyOf dhr && decide (m.nr ≤ e.2.1)
                    && decide (e.2.1 < upto.val))) := by
            rw [v1_post, hskip, hnr]
            rfl
          refine ⟨_, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
            simp_all [keysOf]

/-! ## The skipped-key lookup refines the model's

The loop carries only the index: the store is fixed across it, because the
removal happens once and the loop exits. So the invariant is simply that nothing
before the index matches, and at a match `filter_not_eq_eraseIdx` turns the
model's delete-every-match into the core's erase-at-index.

The at-most-one hypothesis is discharged for real callers by
`Proofs.StateInvariants.skipMessageKeys_preserves_map`, which is in the
functional-property package next door: storing keeps the store a map, so a
header can match at most one entry. -/

/-- Nothing before the entry matches and the entry does, so the model's
first-match lookup finds exactly it. Stated on an explicit split rather than an
index, because rewriting a list under a dependent index breaks the motive. -/
theorem find?_eq_of_split {α : Type} (p : α → Bool) (pre : List α) (a : α)
    (post : List α) (hpre : pre.filter p = []) (hpa : p a = true) :
    (pre ++ a :: post).find? p = some a := by
  have hnone : pre.find? p = none := by
    rw [List.find?_eq_none]
    intro x hx hpx
    have : x ∈ pre.filter p := List.mem_filter.mpr ⟨hx, hpx⟩
    rw [hpre] at this
    exact absurd this List.not_mem_nil
  rw [List.find?_append, hnone]
  simp [List.find?_cons_of_pos hpa]

/-- Nothing before the index matches and the index is past the end, so nothing
matches at all. -/
theorem find?_eq_none_of_scanned {α : Type} (p : α → Bool) (L : List α) (j : Nat)
    (hge : L.length ≤ j) (hpre : (L.take j).filter p = []) :
    L.find? p = none := by
  rw [List.take_of_length_le hge] at hpre
  rw [List.find?_eq_none]
  intro x hx hpx
  have : x ∈ L.filter p := List.mem_filter.mpr ⟨hx, hpx⟩
  rw [hpre] at this
  exact absurd this List.not_mem_nil

/-- The model's lookup predicate, written the way the model writes it: a
pattern-match over the triple rather than projections. The two forms agree but
are not the same term, and the model's `find?` will not accept a conclusion
stated in the other one, so it is easier to match the model here than to align
them later. -/
def matchesHeader (mh : Model.State.Header)
    (e : Model.State.Key × Nat × Nat × Model.State.Key) : Bool :=
  match e with | (dh, n, _, _) => dh == mh.dh && n == mh.n

/-- The model writes its predicate inline; this names it, so the scan's
conclusions rewrite into the model's `match` scrutinee. Definitional, but `rw`
matches syntactically, so it has to be said. Not a global `simp` lemma, for
the same reason as `keepFresh_eta`. -/
theorem matchesHeader_eta (mh : Model.State.Header) :
    (fun (x : Model.State.Key × Nat × Nat × Model.State.Key) =>
      match x with | (dh, n, _, _) => dh == mh.dh && n == mh.n) = matchesHeader mh :=
  rfl

theorem try_skipped_loop_refines (hrm : Tacenta.T1.VecRemoveTotal)
    (s : State) (hdr : Header) (mh : Model.State.Header)
    (hH : HeaderR hdr mh) (i : Usize)
    (hone : ((s.skipped.val.map skippedOf).filter (matchesHeader mh)).length ≤ 1)
    (hpre : (((s.skipped.val.map skippedOf).take i.val).filter
              (matchesHeader mh)) = []) :
    try_skipped_loop s hdr i ⦃ fun r =>
      (∀ mk, r.1 = some mk →
        -- The entry's `stored_at` is existential: the scan returns the key it
        -- found, not when it was stored, and no caller needs the latter.
        (∃ at_, (s.skipped.val.map skippedOf).find? (matchesHeader mh)
            = some (mh.dh, mh.n, at_, keyOf mk))
        ∧ r.2.2.2.2.2.2.2.2.2.1.val.map skippedOf
            = (s.skipped.val.map skippedOf).filter
                (fun e => !matchesHeader mh e))
      ∧ (r.1 = none →
        (s.skipped.val.map skippedOf).find? (matchesHeader mh) = none
        ∧ r.2.2.2.2.2.2.2.2.2.1 = s.skipped) ⦄ := by
  obtain ⟨hhdh, hhpn, hhn⟩ := hH
  unfold try_skipped_loop
  apply loop.spec_decr_nat
    (measure := fun j => s.skipped.val.length - j.val)
    (inv := fun j => ((s.skipped.val.map skippedOf).take j.val).filter
      (matchesHeader mh) = [])
  · rintro j hinv2
    simp only [try_skipped_loop.body]
    -- The removal's hypothesis is available only under the guard the body
    -- checks first, so the case split comes before the removal is named.
    by_cases hlt : j.val < s.skipped.val.length
    · obtain ⟨⟨removed, v'⟩, hrm', hv⟩ := hrm Global s.skipped j hlt
      simp only [hrm']
      step*
      -- The entry matches: the lookup finds it, and deleting every match is
      -- erasing this index, which is what the store being a map buys.
      · have hjm : j.val < (s.skipped.val.map skippedOf).length := by simpa using hlt
        have hdheq : sk.dh = hdr.dh := b_post.mp (by assumption)
        have hneq : sk.n = hdr.n := by assumption
        have hpj : matchesHeader mh (s.skipped.val.map skippedOf)[j.val] = true := by
          rw [List.getElem_map, ← sk_post]
          simp only [matchesHeader, skippedOf, Bool.and_eq_true, beq_iff_eq]
          exact ⟨by rw [hdheq, hhdh], by rw [hneq, hhn]⟩
        refine ⟨?_, by simp⟩
        rintro mk hmk
        injection hmk with hmk
        subst hmk
        constructor
        · refine ⟨sk.stored_at.val, ?_⟩
          have hsp : (s.skipped.val.map skippedOf)
              = ((s.skipped.val.map skippedOf).take j.val)
                ++ (s.skipped.val.map skippedOf)[j.val]
                  :: (s.skipped.val.map skippedOf).drop (j.val + 1) := by
            rw [← List.drop_eq_getElem_cons hjm, List.take_append_drop]
          rw [hsp, find?_eq_of_split _ _ _ _ hinv2 hpj, List.getElem_map, ← sk_post]
          simp only [skippedOf]
          rw [hdheq, hhdh, hneq, hhn]
        · rw [hv, map_eraseIdx,
            filter_not_eq_eraseIdx (matchesHeader mh) _ j.val hjm hpj hone]
      -- The entry's message number differs, so the scan steps past it.
      · have hjm : j.val < (s.skipped.val.map skippedOf).length := by
          simpa using hlt
        rw [i2_post]
        refine ⟨?_, by omega⟩
        rw [List.take_add_one, List.getElem?_eq_getElem hjm, List.filter_append,
          hinv2]
        simp only [List.nil_append, List.getElem_map, ← sk_post]
        have hnm : matchesHeader mh (skippedOf sk) = false := by
          simp only [matchesHeader, skippedOf, Bool.and_eq_false_iff,
            beq_eq_false_iff_ne]
          right
          intro hc
          rw [← hhn] at hc
          exact (by assumption : ¬ sk.n = hdr.n) (by scalar_tac)
        simp [hnm]
      -- The entry's ratchet key differs, likewise.
      · have hjm : j.val < (s.skipped.val.map skippedOf).length := by
          simpa using hlt
        rw [i2_post]
        refine ⟨?_, by omega⟩
        rw [List.take_add_one, List.getElem?_eq_getElem hjm, List.filter_append,
          hinv2]
        simp only [List.nil_append, List.getElem_map, ← sk_post]
        have hnm : matchesHeader mh (skippedOf sk) = false := by
          simp only [matchesHeader, skippedOf, Bool.and_eq_false_iff,
            beq_eq_false_iff_ne]
          left
          intro hc
          rw [← hhdh] at hc
          exact (by assumption : ¬ b = true) (b_post.mpr (keyOf_inj hc))
        simp [hnm]
    -- The scan is spent, so nothing matched anywhere and the store is the one
    -- it started with.
    · step*
      refine ⟨by simp, fun _ => ?_⟩
      exact find?_eq_none_of_scanned _ _ j.val (by simpa using hlt) hinv2
  · exact hpre

/-- The scan returns every field but the store untouched, so the state the
wrapper rebuilds is the one it started from with the store replaced. Separate
from the refinement above because it is a different concern: that one is about
what the scan found, this is about what it left alone. -/
theorem try_skipped_loop_fields (hrm : Tacenta.T1.VecRemoveTotal)
    (s : State) (hdr : Header) (i : Usize) :
    try_skipped_loop s hdr i ⦃ fun r =>
      ({ dhs_pub := r.2.1, dhr_pub := r.2.2.1, rk := r.2.2.2.1,
         cks := r.2.2.2.2.1, ckr := r.2.2.2.2.2.1, ns := r.2.2.2.2.2.2.1,
         nr := r.2.2.2.2.2.2.2.1, pn := r.2.2.2.2.2.2.2.2.1,
         skipped := r.2.2.2.2.2.2.2.2.2.1, events := r.2.2.2.2.2.2.2.2.2.2.1,
         labels := r.2.2.2.2.2.2.2.2.2.2.2 } : State)
        = { s with skipped := r.2.2.2.2.2.2.2.2.2.1 } ⦄ := by
  unfold try_skipped_loop
  apply loop.spec_decr_nat
    (measure := fun j => s.skipped.val.length - j.val)
    (inv := fun _ => True)
  · rintro j -
    simp only [try_skipped_loop.body]
    by_cases hlt : j.val < s.skipped.val.length
    · obtain ⟨⟨removed, v'⟩, hrm', -⟩ := hrm Global s.skipped j hlt
      simp only [hrm']
      step*
    · step*
  · trivial

/-- The lookup, lifted to the whole function. On a hit it returns the key the
model's lookup returns and leaves the store the model leaves; on a miss the
model finds nothing either.

The at-most-one hypothesis is what the store being a map buys, and it is proven
rather than assumed: see `Proofs.StateInvariants.skipMessageKeys_preserves_map`
in the functional-property package. -/
theorem try_skipped_refines (hrm : Tacenta.T1.VecRemoveTotal)
    (s : State) (m : Model.State.State) (hR : StateR s m)
    (hdr : Header) (mh : Model.State.Header) (hH : HeaderR hdr mh)
    (hone : (m.skipped.filter (matchesHeader mh)).length ≤ 1) :
    try_skipped s hdr ⦃ fun r =>
      (∀ mk, r.1 = some mk →
        ∃ m', Model.Ratchet.trySkipped m mh = some (m', keyOf mk)
          ∧ StateR r.2 m')
      ∧ (r.1 = none → Model.Ratchet.trySkipped m mh = none ∧ StateR r.2 m) ⦄ := by
  have hSR := hR
  obtain ⟨hdhs, hdhr, hrk, hcks, hckr, hns, hnr, hpn, hskip, hev, hlab⟩ := hR
  unfold try_skipped
  have hloop := try_skipped_loop_refines hrm s hdr mh hH 0#usize
    (by rw [hskip]; exact hone) (by simp)
  obtain ⟨rr, hrr⟩ := (Tacenta.T1.noPanic_iff _).mp
    (Tacenta.T1.try_skipped_loop_no_panic hrm s hdr 0#usize)
  obtain ⟨o, a, o1, a1, o2, o3, ii, i1, i2, v, lbl⟩ := rr
  rw [hrr] at hloop ⊢
  have hfields := try_skipped_loop_fields hrm s hdr 0#usize
  rw [hrr] at hfields
  obtain ⟨hsome, hnone⟩ := hloop
  step*
  refine ⟨?_, ?_⟩
  · rintro mk hmk
    obtain ⟨⟨at_, hfind⟩, hfilt⟩ := hsome mk hmk
    rw [hfields]
    refine ⟨{ m with skipped :=
        m.skipped.filter (fun e => !matchesHeader mh e) },
      ?_, ⟨hdhs, hdhr, hrk, hcks, hckr, hns, hnr, hpn, ?_, hev, hlab⟩⟩
    · unfold Model.Ratchet.trySkipped
      rw [← hskip]
      simp only [matchesHeader_eta, hfind]
      rfl
    · rw [hfilt, hskip]
  · intro hn
    obtain ⟨hfind, hstore⟩ := hnone hn
    refine ⟨?_, ?_⟩
    · unfold Model.Ratchet.trySkipped
      rw [← hskip]
      simp only [matchesHeader_eta, hfind]
    · rw [hfields, hstore]
      exact hSR

-- T1's rule for `age_store` says only that the store did not grow, which is all
-- panic-freedom needed. Here that would walk past the call and lose what the
-- ageing produced, so it is removed and the refinement applied by hand; its
-- statement carries the model state, which a stepping rule cannot determine.
attribute [-step] Tacenta.T1.age_store_spec

/-- The suffix both of `receive`'s ratchet paths share: skip forward to the
message number, refuse a number the chain has already passed, then take the
chain-key step. Factoring it out is what keeps that proof from being written
three times.

The refusal (`OutOfOrder`, ratchet.md, Sending and receiving) is an `Err` on
the Rust side and a `none` on the model's, and the two agree on when it fires
because the skip leaves `nr` related: so a success here is never the refused
case, and the model's test is passed exactly when the Rust's is. -/
theorem receive_tail_refines (h : HmacAgrees) (hrm : Tacenta.T1.VecRemoveTotal)
    [DerivedKeysModel] (st : State) (mst : Model.State.State) (hR : StateR st mst) (n : Std.U32)
    (hs : st.skipped.val.length + MAX_SKIP.val ≤ Usize.max)
    (hroom : st.events.val + 1 < U32.max) :
    (do
      let (r1, state4) ← skip_message_keys st n
      match r1 with
      | core.result.Result.Ok _ =>
        if n < state4.nr
        then ok (core.result.Result.Err RatchetError.OutOfOrder, state4)
        else
          match state4.ckr with
          | none =>
            ok (core.result.Result.Err RatchetError.NoReceivingChain, state4)
          | some ck =>
            let o2 ← lift (U32.checked_add state4.nr 1#u32)
            match o2 with
            | none =>
              ok (core.result.Result.Err RatchetError.ChainExhausted, state4)
            | some next_nr =>
              let (ck2, mk) ← kdf_ck ck
              let state5 ← age_store { state4 with ckr := some ck2, nr := next_nr }
              ok (core.result.Result.Ok mk, state5)
      | core.result.Result.Err e => ok (core.result.Result.Err e, state4))
    ⦃ fun r => ∀ mk, r.1 = core.result.Result.Ok mk →
      ∃ m',
        (match Model.State.skipMessageKeys mst n.val with
         | none => none
         | some st2 =>
           if n.val < st2.nr then
             none
           else
             match st2.ckr with
             | none => none
             | some ck =>
               some (Model.State.ageStore
                       { st2 with
                         ckr := some (Model.State.kdfCk ck).fst,
                         nr := st2.nr + 1 },
                     (Model.State.kdfCk ck).snd))
          = some (m', keyOf mk)
        ∧ StateR r.2 m' ⦄ := by
  have hht : Tacenta.T1.HmacTotal := h.total
  obtain ⟨rk, hrk⟩ := (Tacenta.T1.noPanic_iff _).mp
    (Tacenta.T1.skip_message_keys_no_panic hht hrm st n hs)
  obtain ⟨r1, state4⟩ := rk
  have hsk := skip_message_keys_refines h hrm st mst hR n hs
  rw [hrk] at hsk ⊢
  rcases r1 with _ | e
  · obtain ⟨m2, hm2, hSR2⟩ := hsk rfl
    step*
    have hck : state4.ckr = some ck := by assumption
    have ho : o2 = some next_nr := by assumption
    simp only at hSR2
    have hmckr : m2.ckr = some (keyOf ck) := by
      have hc := hSR2.ckr
      rw [hck] at hc
      simpa using hc.symm
    -- Past the refusal on the Rust side, so past it on the model's: the skip
    -- left the two counters related.
    have hnlt : ¬ n.val < m2.nr := by
      intro hc
      have hn2 := hSR2.nr
      have hlt4 : n < state4.nr := by scalar_tac
      exact absurd hlt4 (by assumption)
    have hnr : next_nr.val = m2.nr + 1 := by
      rw [ho] at o2_post
      simp only at o2_post
      have hn2 := hSR2.nr
      omega
    -- The state before ageing already refines; ageing is then a step both sides
    -- take, and the counter has room because nothing between has moved it.
    have hpre : StateR { state4 with ckr := some ck2, nr := next_nr }
        { m2 with ckr := some (keyOf ck2), nr := m2.nr + 1 } :=
      ⟨hSR2.dhs_pub, hSR2.dhr_pub, hSR2.rk, hSR2.cks, by simp,
        hSR2.ns, by simpa using hnr, hSR2.pn, hSR2.skipped, hSR2.events,
        hSR2.labels⟩
    have hroom2 : (({ state4 with ckr := some ck2, nr := next_nr } : State)).events.val + 1
        < U32.max := by
      have he4 := hSR2.events
      have hmev := Model.State.skipMessageKeys_events mst n.val m2 hm2
      have hst := hR.events
      simp only at he4 hst ⊢
      omega
    obtain ⟨s5, hs5, hSR5⟩ :=
      Std.WP.spec_imp_exists (age_store_refines hrm _ _ hpre hroom2)
    rw [hs5]
    step*
    rintro mk1 hmk1
    injection hmk1 with hmk1
    subst hmk1
    refine ⟨Model.State.ageStore
      { m2 with ckr := some (keyOf ck2), nr := m2.nr + 1 }, ?_, hSR5⟩
    · rw [hm2]
      show (if n.val < m2.nr then none else
            match m2.ckr with
            | none => none
            | some ck' =>
              let p := Model.State.kdfCk ck'
              some (Model.State.ageStore
                      { m2 with ckr := some p.1, nr := m2.nr + 1 }, p.2)) = _
      rw [if_neg hnlt]
      simp only [hmckr]
      rw [← ck2_post]
  · simp

-- The sub-operations are applied by hand below: their refinement statements
-- carry the model state as a free parameter, which the stepping tactic has
-- nothing to determine from the call, so T1's weaker rules would win.
attribute [-step] Tacenta.T1.skip_message_keys_bound Tacenta.T1.dh_ratchet_spec

theorem receive_refines (h : HmacAgrees) (hk : HkdfAgrees)
    (hz : ZeroizingRoundTrips) (hrm : Tacenta.T1.VecRemoveTotal)
    [DerivedKeysModel] (s : State) (m : Model.State.State) (hR : StateR s m)
    (hdr : Header) (mh : Model.State.Header) (hH : HeaderR hdr mh)
    (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize)
    (hone : (m.skipped.filter (matchesHeader mh)).length ≤ 1)
    (hs : max s.skipped.val.length MAX_SKIPPED_STORE.val + MAX_SKIP.val
            ≤ Usize.max)
    (hroom : s.events.val + 1 < U32.max) :
    receive s hdr dh_out_recv dh_out_send new_dhs_pub ⦃ fun r =>
      ∀ mk, r.1 = core.result.Result.Ok mk →
        ∃ m', Model.Ratchet.receive m mh (keyOf dh_out_recv) (keyOf dh_out_send)
              (keyOf new_dhs_pub) = some (m', keyOf mk)
          ∧ StateR r.2 m' ⦄ := by
  have hht : Tacenta.T1.HmacTotal := h.total
  have hkt : Tacenta.T1.HkdfTotal := hk.total
  have hzt : Tacenta.T1.ZeroizingTotal := hz.total
  unfold receive
  obtain ⟨rr, hrr⟩ := (Tacenta.T1.noPanic_iff _).mp
    (Tacenta.T1.try_skipped_no_panic hrm s hdr)
  obtain ⟨o, state1⟩ := rr
  have hts := try_skipped_refines hrm s m hR hdr mh hH hone
  rw [hrr] at hts ⊢
  obtain ⟨hsome, hnone⟩ := hts
  rcases o with _ | mk0
  · obtain ⟨hmiss, hSR1⟩ := hnone rfl
    have hlen1 : state1.skipped.val.length = s.skipped.val.length := by
      have hh := congrArg List.length (hSR1.skipped.trans hR.skipped.symm)
      simpa using hh
    step*
    rcases hd : state1.dhr_pub with _ | dhr <;> (try simp only) <;> step*
    -- No receiving ratchet key held yet, so the first message ratchets.
    · have hnotsame : ¬ (m.dhrPub = some mh.dh) := by
        have hc := hSR1.dhr_pub
        rw [hd] at hc
        simp only [Option.map] at hc
        rw [← hc]
        simp
      rw [← hd]
      have hlen : state1.skipped.val.length + MAX_SKIP.val ≤ Usize.max := by
        simp only [MAX_SKIPPED_STORE] at *
        omega
      obtain ⟨r2, hr2⟩ := (Tacenta.T1.noPanic_iff _).mp
        (Tacenta.T1.skip_message_keys_no_panic hht hrm state1 hdr.pn hlen)
      obtain ⟨rres2, state2⟩ := r2
      have hsk := skip_message_keys_refines h hrm state1 m hSR1 hdr.pn hlen
      rw [hr2] at hsk ⊢
      rcases rres2 with _ | e2
      · obtain ⟨m2, hm2, hSR2⟩ := hsk rfl
        step*
        obtain ⟨r3, hr3, hdr3⟩ := Std.WP.spec_imp_exists
          (dh_ratchet_refines hk hz state2 m2 hSR2 hdr mh hH dh_out_recv
            dh_out_send new_dhs_pub)
        rw [hr3]
        have hlen3 : r3.skipped.val.length + MAX_SKIP.val ≤ Usize.max := by
          have hb := Tacenta.T1.skip_message_keys_bound hht hrm state1 hdr.pn hlen
          rw [hr2] at hb
          have hd3 := Tacenta.T1.dh_ratchet_spec hkt hzt state2 hdr dh_out_recv
            dh_out_send new_dhs_pub
          rw [hr3] at hd3
          have hb2 : state2.skipped.val.length
              ≤ max state1.skipped.val.length MAX_SKIPPED_STORE.val := hb
          have hd32 : r3.skipped.val.length = state2.skipped.val.length := hd3
          simp only [MAX_SKIPPED_STORE] at *
          omega
        -- Nothing between the entry and here moves the counter: skipping does
        -- not, and the ratchet step replaces every field but this one.
        have hroom3 : r3.events.val + 1 < U32.max := by
          have h1 := hdr3.events
          have h2 := Model.State.skipMessageKeys_events m hdr.pn.val m2 hm2
          have h3 := hR.events
          simp only [Model.Ratchet.dhRatchet] at h1
          omega
        refine Std.WP.spec_mono
          (receive_tail_refines h hrm r3 _ hdr3 hdr.n hlen3 hroom3) ?_
        rintro ⟨rres, rst⟩ hp mk hmk
        obtain ⟨m', hm', hSRm⟩ := hp mk hmk
        refine ⟨m', ?_, hSRm⟩
        rw [hH.n] at hm'
        rw [hH.pn] at hm2
        have hcond : ¬ ((m.dhrPub == some mh.dh) = true) := by simpa using hnotsame
        unfold Model.Ratchet.receive
        rw [hmiss, if_neg hcond, hm2]
        exact hm'
      · simp
    -- The peer moved to a ratchet key we do not hold, so the chain ratchets.
    · have hnotsame : ¬ (m.dhrPub = some mh.dh) := by
        have hxt : x = true := by assumption
        have hne : dhr ≠ hdr.dh := x_post.mp hxt
        have hc := hSR1.dhr_pub
        rw [hd] at hc
        simp only [Option.map] at hc
        rw [← hc]
        simp only [Option.some.injEq]
        intro heq
        rw [← hH.dh] at heq
        exact hne (keyOf_inj heq)
      rw [← hd]
      have hlen : state1.skipped.val.length + MAX_SKIP.val ≤ Usize.max := by
        simp only [MAX_SKIPPED_STORE] at *
        omega
      obtain ⟨r2, hr2⟩ := (Tacenta.T1.noPanic_iff _).mp
        (Tacenta.T1.skip_message_keys_no_panic hht hrm state1 hdr.pn hlen)
      obtain ⟨rres2, state2⟩ := r2
      have hsk := skip_message_keys_refines h hrm state1 m hSR1 hdr.pn hlen
      rw [hr2] at hsk ⊢
      rcases rres2 with _ | e2
      · obtain ⟨m2, hm2, hSR2⟩ := hsk rfl
        step*
        obtain ⟨r3, hr3, hdr3⟩ := Std.WP.spec_imp_exists
          (dh_ratchet_refines hk hz state2 m2 hSR2 hdr mh hH dh_out_recv
            dh_out_send new_dhs_pub)
        rw [hr3]
        have hlen3 : r3.skipped.val.length + MAX_SKIP.val ≤ Usize.max := by
          have hb := Tacenta.T1.skip_message_keys_bound hht hrm state1 hdr.pn hlen
          rw [hr2] at hb
          have hd3 := Tacenta.T1.dh_ratchet_spec hkt hzt state2 hdr dh_out_recv
            dh_out_send new_dhs_pub
          rw [hr3] at hd3
          have hb2 : state2.skipped.val.length
              ≤ max state1.skipped.val.length MAX_SKIPPED_STORE.val := hb
          have hd32 : r3.skipped.val.length = state2.skipped.val.length := hd3
          simp only [MAX_SKIPPED_STORE] at *
          omega
        -- Nothing between the entry and here moves the counter: skipping does
        -- not, and the ratchet step replaces every field but this one.
        have hroom3 : r3.events.val + 1 < U32.max := by
          have h1 := hdr3.events
          have h2 := Model.State.skipMessageKeys_events m hdr.pn.val m2 hm2
          have h3 := hR.events
          simp only [Model.Ratchet.dhRatchet] at h1
          omega
        refine Std.WP.spec_mono
          (receive_tail_refines h hrm r3 _ hdr3 hdr.n hlen3 hroom3) ?_
        rintro ⟨rres, rst⟩ hp mk hmk
        obtain ⟨m', hm', hSRm⟩ := hp mk hmk
        refine ⟨m', ?_, hSRm⟩
        rw [hH.n] at hm'
        rw [hH.pn] at hm2
        have hcond : ¬ ((m.dhrPub == some mh.dh) = true) := by simpa using hnotsame
        unfold Model.Ratchet.receive
        rw [hmiss, if_neg hcond, hm2]
        exact hm'
      · simp
    -- The peer stayed on the ratchet key we hold, so no ratchet step: the
    -- shared suffix applies directly.
    · rw [← hd]
      refine Std.WP.spec_mono
        (receive_tail_refines h hrm state1 m hSR1 hdr.n ?_ ?_) ?_
      · simp only [MAX_SKIPPED_STORE] at *
        omega
      · -- The lookup that missed left every field but the store alone.
        have hev1 := hSR1.events
        have hev3 := hR.events
        simp only at hev1 hev3 ⊢
        omega
      · rintro ⟨rres, rst⟩ hp mk hmk
        obtain ⟨m', hm', hSRm⟩ := hp mk hmk
        refine ⟨m', ?_, hSRm⟩
        have hxf : ¬x = true := by assumption
        have hdheq : dhr = hdr.dh := by
          by_contra hc
          exact hxf (x_post.mpr hc)
        have hmdhr : m.dhrPub = some mh.dh := by
          have hc := hSR1.dhr_pub
          rw [hd] at hc
          simp only [Option.map] at hc
          rw [← hc, hdheq, hH.dh]
        rw [hH.n] at hm'
        unfold Model.Ratchet.receive
        rw [hmiss]
        simp only [hmdhr, beq_self_eq_true, if_pos]
        exact hm'
  · obtain ⟨m', hm', hSR'⟩ := hsome mk0 rfl
    -- The store is aged on this path too: a message taken from the store is a
    -- received message, and both sides count it.
    have hroom1 : state1.events.val + 1 < U32.max := by
      have hev1 := hSR'.events
      have hevm := Model.Ratchet.trySkipped_events m mh (m', keyOf mk0) hm'
      have hev3 := hR.events
      simp only at hev1 hevm hev3 ⊢
      omega
    step*
    obtain ⟨s2, hs2, hSR2⟩ :=
      Std.WP.spec_imp_exists (age_store_refines hrm _ _ hSR' hroom1)
    rw [hs2]
    step*
    refine fun mk hmk => ?_
    injection hmk with hmk
    subst hmk
    exact ⟨Model.State.ageStore m',
      by unfold Model.Ratchet.receive; rw [hm'], hSR2⟩

/-
## What remains

**T3 covers every protocol operation the model defines.** Each is proved to
be refined by the translated Rust: both key-derivation steps, the message-key
expansion (`message_keys_refines`, the last derivation before the cipher),
both session-initialisation operations, `send`, `dh_ratchet`, chain
derivation, the whole skip step with its purge scan, the skipped-key lookup,
and `receive`, which composes the rest. There is no `sorry`. What it does not
cover is what the translation contains and the model does not define: the
persistence codecs (`from_bytes`, `to_bytes` and their helpers) and the small
accessors, which `CLAIMS.md` lists under "translated is not proved".

Two limits stand, and neither is a formality.

Refinement is **modulo agreement of the key-derivation primitives**. They are
opaque by the same choice that made T1 tractable, and an axiom cannot be shown
to agree with anything, so `HmacAgrees` and `HkdfAgrees` are assumptions. If the
Rust HMAC and the model's disagreed, every theorem here would still hold and the
implementation would still be wrong. The model-generated byte vectors are what
covers that, outside Lean. `ZeroizingRoundTrips`, T1's `DerivedKeysModel` and
`VecRemoveTotal` are the other three, the first two for an external crate --
the wrapper at the root-key step's width, and the wrapper the derived keys
travel in between the chain derivation and the store -- and the third for an
operation Aeneas does not model.

And the **finite-width boundary shows through** wherever the Rust counts in
`u32` and the model in `Nat`. Sending can report `ChainExhausted` where the
model simply continues; `receive` carries a store-size precondition, the store's
length plus `MAX_SKIP`, which holds at either platform width; and expiry means
`receive` also requires the store's clock to have room for the step, because the
core's counter stops and the model's does not. The stop is now one below the
ceiling rather than at it: `age_store` clamps the saturating step to
`MAX_EVENTS`, so that a state the crate exports still satisfies its own
`invariant`'s `events < u32::MAX` instead of being refused by its own decoder
for the rest of the session. That clamp is why `hroom` reads
`events + 1 < U32.max` and not `events < U32.max`: at `events = MAX_EVENTS` the
two sides genuinely disagree, the core holding its clock still while the model's
advances, and the refinement is stated where they agree. It also means the
crate's own `events < u32::MAX` is now *preserved* by `age_store` rather than
merely assumed by it -- true of the state afterwards for any state at all --
which is one clause of `invariant` that no longer has to be carried in by hand;
it is, however, one clause weaker than the refinement's `hroom`, so a caller
holding only `invariant` no longer holds `hroom`: `ImportInv`'s
`inv_gives_clock_room` reaches `events < u32::MAX` and stops one short of what
`receive_refines` now asks. Those cases are excluded from the correspondence
deliberately rather than papered over.

What expiry touches, for the next person adding a field to the state: the
store's element type carries an extra component and `StateR` an extra field, and
that alone reaches every lemma about the store. The work is not the purge loop,
which is the purge scan again with a different predicate; it is that a
projection into the state is written positionally, so widening the state moves
every one of them.

A note for the next proof here: when a rewrite will not go in, check first
whether the statement is written in a form the model does not use --
projections against a pattern-match, `do` against `match`, `let` against a
destructuring `let`. A `let` with a type ascription elaborates to an opaque
`have` that no rewrite can see through, which is why the model avoids the
form.

-/

/-! ## The axiom audit, enforced rather than asserted

The two headline theorems and the expansion, pinned so that a change which
made one of them rest on something new -- a `sorry`, a `native_decide`, an
assumption smuggled in through a lemma -- fails the build here rather than
being noticed by whoever next runs `#print axioms` by hand. Everything each
rests on beyond Lean's three standard axioms is an opaque external the
translation declares: the key-derivation primitives, the `zeroize` wrapper,
and `Vec::remove`. -/

/-- info: 'Tacenta.T3.send_refines' depends on axioms: [propext, Classical.choice, Quot.sound, tacenta_kdf.hmac_sha256] -/
#guard_msgs in
#print axioms Tacenta.T3.send_refines

/--
info: 'Tacenta.T3.receive_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.remove,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.T3.receive_refines

/--
info: 'Tacenta.T3.message_keys_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.T3.message_keys_refines

end Tacenta.T3
